/-
  FormalRV.System.DependencyGraph — a first-class CAUSAL-DEPENDENCY graph for
  parallel schedules: the (B) half of "max parallelism subject to invariants".

  John's insight (2026-06-02): the system invariants are about two things —
  (A) RESOURCE conflict-freedom and (B) CAUSAL dependencies — and (B) is just as
  essential.  (A) is captured by the `checkAll` resource invariants (capacity,
  exclusivity, throughput, decoder).  This file gives (B) the same first-class
  treatment: an explicit DEPENDENCY GRAPH over a schedule, a decidable check that
  the schedule RESPECTS it, and — crucially — a wrapping into the SAME extensible
  `SpaceTimeInvariant` framework, so causality is verified by the same mechanism
  as the resource constraints.  Then "two ops may run concurrently iff no
  resource conflict (A) AND no causal dependency (B)" is one uniform `checkAll`.

  The causal orderings (qianxu App. E, all class (B)): sub-circuits C_i are
  sequential; within each, teleport-in → compute → teleport-out; each Toffoli is
  a sequence of PPMs; measure → decode → feed-forward.  These are producer→
  consumer edges: the producer must FINISH before the consumer may START.

  No Mathlib.  Pure Bool / Nat + `decide`.  No `sorry`, no `axiom`.
-/
import FormalRV.System.InvariantFramework

namespace FormalRV.System.DependencyGraph

open FormalRV.Framework.Architecture FormalRV.Framework.InvariantFramework

/-! ## (1) The dependency graph -/

/-- A causal dependency edge: the operation at schedule index `before` must
    FINISH (its `end_us`) before the operation at index `after` may START (its
    `begin_us`).  This is a producer → consumer edge. -/
structure DepEdge where
  before : Nat
  after  : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A causal dependency graph over a schedule: a list of producer → consumer
    edges.  (The schedule it refers to is supplied separately, as a `List
    SysCall`; edges are indices into it.) -/
structure DepGraph where
  edges : List DepEdge
  deriving Repr, Inhabited

/-- A schedule RESPECTS a dependency graph iff every edge's producer finishes no
    later than its consumer starts.  A dangling edge (index out of range) marks a
    malformed program → rejected. -/
def respectsCausality (sched : List SysCall) (g : DepGraph) : Bool :=
  g.edges.all (fun e =>
    match sched[e.before]?, sched[e.after]? with
    | some u, some v => decide (u.end_us ≤ v.begin_us)
    | _, _           => false)

/-! ## (2) Causality as a first-class SpaceTimeInvariant

    The dependency graph is a parameter of the invariant instance (like
    `n_decoders` for a decoder-concurrency invariant); the check reads the
    context's schedule.  So (B) causal dependency plugs into `checkAll` exactly
    like the (A) resource invariants — one uniform, extensible mechanism. -/

def causalityInv (g : DepGraph) : SpaceTimeInvariant :=
  { name  := "causal dependency (producer finishes before consumer starts)",
    check := fun c => respectsCausality c.sched g }

/-! ## (3) Soundness of the dependency relation — acyclicity.

    A genuine causal order is acyclic.  The simplest witness: with positive
    operation durations, no operation can depend on itself — a self-edge `i → i`
    would force `end_i ≤ begin_i`, contradicting `begin_i < end_i`.  (Longer
    cycles are excluded the same way: a cycle forces a strict-time decrease.) -/
theorem no_self_dependency (sched : List SysCall) (g : DepGraph)
    (h : respectsCausality sched g = true)
    (e : DepEdge) (he : e ∈ g.edges) (heq : e.before = e.after)
    (u : SysCall) (hu : sched[e.before]? = some u) (hpos : u.begin_us < u.end_us) :
    False := by
  have h2 := (List.all_eq_true.mp h) e he
  have hv : sched[e.after]? = some u := heq ▸ hu
  rw [hu, hv] at h2
  have hle : u.end_us ≤ u.begin_us := by simpa using h2
  omega

/-! ## (4) Worked example — the per-Toffoli causal DAG (qianxu App. E, p. 20-21).

    teleport-in (PPM) → compute → teleport-out (PPM) → decode → feed-forward.
    Each edge forces the consumer to start no earlier than the producer ends. -/

def toffoliSched : List SysCall :=
  [ { kind := SysCallKind.Measure 0 0,        begin_us := 0,  end_us := 10 }   -- 0: teleport-in PPM
  , { kind := SysCallKind.Gate2q 0 1 0,       begin_us := 10, end_us := 20 }   -- 1: compute (processor)
  , { kind := SysCallKind.Measure 1 0,        begin_us := 20, end_us := 30 }   -- 2: teleport-out PPM
  , { kind := SysCallKind.DecodeSyndrome 0,   begin_us := 30, end_us := 35 }   -- 3: decode
  , { kind := SysCallKind.PauliFrameUpdate 0, begin_us := 35, end_us := 36 } ] -- 4: feed-forward

def toffoliDeps : DepGraph :=
  { edges :=
    [ { before := 0, after := 1 }    -- teleport-in BEFORE compute
    , { before := 1, after := 2 }    -- compute BEFORE teleport-out
    , { before := 2, after := 3 }    -- measurement BEFORE decode
    , { before := 3, after := 4 } ] }  -- decode BEFORE feed-forward

/-- The time-ordered schedule respects every causal edge. -/
example : respectsCausality toffoliSched toffoliDeps = true := by decide

/-- A schedule that puts the feed-forward (index 4) BEFORE the decode (index 3)
    violates the `3 → 4` edge — rejected.  No parallelism can let a correction
    precede the decode that produces it. -/
def badToffoliSched : List SysCall :=
  [ { kind := SysCallKind.Measure 0 0,        begin_us := 0,  end_us := 10 }
  , { kind := SysCallKind.Gate2q 0 1 0,       begin_us := 10, end_us := 20 }
  , { kind := SysCallKind.Measure 1 0,        begin_us := 20, end_us := 30 }
  , { kind := SysCallKind.DecodeSyndrome 0,   begin_us := 35, end_us := 40 }   -- decode LATE
  , { kind := SysCallKind.PauliFrameUpdate 0, begin_us := 30, end_us := 31 } ] -- feed-forward EARLY
example : respectsCausality badToffoliSched toffoliDeps = false := by decide

/-! ## (5) Unifying (A) and (B): resource + causal checked by ONE `checkAll`.

    Appending `causalityInv toffoliDeps` to the resource `baseInvariants` checks
    BOTH classes uniformly.  The valid schedule passes both; a causality-violating
    schedule fails ONLY the causal invariant (the resource invariants still hold —
    non-interference, the extensibility guarantee). -/

def toffoliCtx : SystemCtx :=
  { arch := demoArch, sched := toffoliSched, moves := [],
    window_us := 1000, max_per_window := 1, t_react_us := 10, distance_fn := demoDist }

/-- Resource (A) AND causal (B) together: the well-ordered Toffoli schedule
    passes the unified check. -/
example : checkAll (baseInvariants ++ [causalityInv toffoliDeps]) toffoliCtx = true := by decide

def badToffoliCtx : SystemCtx := { toffoliCtx with sched := badToffoliSched }

/-- The reordered schedule fails the unified check… -/
example : checkAll (baseInvariants ++ [causalityInv toffoliDeps]) badToffoliCtx = false := by decide

/-- …because it violates CAUSALITY (B) specifically — the RESOURCE invariants (A)
    still hold on it.  Adding causality did not disturb the resource checks. -/
example : checkAll baseInvariants badToffoliCtx = true := by decide
example : (causalityInv toffoliDeps).check badToffoliCtx = false := by decide

/-! ## (6) Causal depth = the runtime floor.

    The dependency DAG sets an irreducible runtime floor that no amount of
    parallelism (class A) can beat: along any dependency chain, the consumer
    cannot start before the producer ends.  This is the formal counterpart of
    qianxu's Toffoli-layer depth (≈ n–2n ripple-carry, ≈ 4·log n carry-lookahead
    layers, p. 6, p. 24) — the floor the `System/NaiveUpperBound.lean` sequential
    makespan rests on.  Transitivity along a 2-edge chain `i → j → k`: -/

theorem causal_chain_floor (sched : List SysCall) (g : DepGraph)
    (h : respectsCausality sched g = true)
    (e1 e2 : DepEdge) (h1 : e1 ∈ g.edges) (h2 : e2 ∈ g.edges)
    (hmid : e1.after = e2.before)
    (u v w : SysCall)
    (hu : sched[e1.before]? = some u) (hv : sched[e1.after]? = some v)
    (hw : sched[e2.after]? = some w)
    (hvpos : v.begin_us ≤ v.end_us) :
    u.end_us ≤ w.begin_us := by
  have hc1 := (List.all_eq_true.mp h) e1 h1
  rw [hu, hv] at hc1
  have hle1 : u.end_us ≤ v.begin_us := by simpa using hc1
  have hc2 := (List.all_eq_true.mp h) e2 h2
  have hv2 : sched[e2.before]? = some v := hmid ▸ hv
  rw [hv2, hw] at hc2
  have hle2 : v.end_us ≤ w.begin_us := by simpa using hc2
  omega

/-! ## (7) A CONDITIONAL critical-path runtime LOWER BOUND.

    CAREFUL ABOUT WHAT THIS IS (John, 2026-06-02).  An *unconditional* lower
    bound — "no algorithm/circuit/schedule whatsoever beats XX" — is a
    complexity-theoretic statement and is NOT verifiable here (it quantifies over
    all possible computations).  What IS verifiable is the *conditional*
    critical-path bound: fix the dependency DAG (the circuit's causal structure)
    and a per-operation MINIMUM duration `dmin` (a hardware fact, an axiom/input);
    then NO SCHEDULE — no assignment of begin/end times respecting the DAG with
    durations ≥ `dmin` — beats the weighted critical path.  This IS a genuine
    `∀`-schedules statement, because a dependency chain is intrinsically serial:
    you cannot parallelize it away.

    The two ASSUMPTIONS are the honest residue: a shallower DAG (a cleverer
    circuit) or a faster `dmin` (better hardware) lowers the floor.  So this
    floors THIS circuit's runtime on THIS hardware, not the problem's optimum.

    Total minimum duration along a chain of (op, dmin) pairs. -/
def chainMinTotal : List (SysCall × Nat) → Nat
  | []            => 0
  | (_, d) :: rest => d + chainMinTotal rest

/-- `end_us` of the last operation in a chain (0 on the empty chain). -/
def lastEnd : List (SysCall × Nat) → Nat
  | []            => 0
  | [(op, _)]     => op.end_us
  | _ :: rest     => lastEnd rest

/-- A chain is a valid execution iff each op runs at least its minimum duration
    (`begin + dmin ≤ end`) and consecutive ops are dependency-linked
    (`prev.end ≤ next.begin`).  This holds of ANY schedule of the chain — it is
    the `∀`-schedules hypothesis. -/
def MinChain : List (SysCall × Nat) → Prop
  | []                          => True
  | [(op, d)]                   => op.begin_us + d ≤ op.end_us
  | (op1, d1) :: (op2, d2) :: r =>
      op1.begin_us + d1 ≤ op1.end_us ∧ op1.end_us ≤ op2.begin_us
      ∧ MinChain ((op2, d2) :: r)

/-- THE CRITICAL-PATH LOWER BOUND.  For ANY schedule (any begin/end times) of a
    dependency chain `(op0, d0) :: rest` that respects the dependencies and runs
    each op for at least its minimum duration, the last operation cannot finish
    before `op0.begin + Σ dmin`.  Equivalently: the makespan from `op0`'s start
    to the chain's end is ≥ the sum of minimum durations — NO scheduling beats
    the critical path.  Proven by induction on the chain. -/
theorem critical_path_lower_bound :
    ∀ (op0 : SysCall) (d0 : Nat) (rest : List (SysCall × Nat)),
      MinChain ((op0, d0) :: rest) →
      op0.begin_us + chainMinTotal ((op0, d0) :: rest)
        ≤ lastEnd ((op0, d0) :: rest)
  | op0, d0, [], h => by
      simp only [MinChain] at h
      simp only [chainMinTotal, lastEnd]
      omega
  | op0, d0, (op1, d1) :: tl, h => by
      simp only [MinChain] at h
      obtain ⟨hm0, hdep, hrest⟩ := h
      have ih := critical_path_lower_bound op1 d1 tl hrest
      simp only [chainMinTotal, lastEnd] at ih ⊢
      omega

/-- The two-operation seed, for clarity: along a single dependency edge
    `op0 → op1`, every schedule has makespan ≥ `d0 + d1`.  (One `omega`; this is
    the base mechanism the induction iterates.) -/
theorem critical_path_two (op0 op1 : SysCall) (d0 d1 : Nat)
    (hmin0 : op0.begin_us + d0 ≤ op0.end_us)
    (hdep  : op0.end_us ≤ op1.begin_us)
    (hmin1 : op1.begin_us + d1 ≤ op1.end_us) :
    op0.begin_us + (d0 + d1) ≤ op1.end_us := by
  omega

/-! ## (8) SCALABILITY — the bound is PARAMETRIC, not a graph computation.

    Proving a critical-path lower bound for a billion-gate circuit by
    MATERIALIZING the dependency DAG and running a longest-path algorithm is
    infeasible in-kernel.  The scalable route is a PARAMETRIC closed-form bound
    proven by INDUCTION on the circuit's recursive structure — one proof `∀ n`,
    instantiated at any size INSTANTLY (no graph traversal).  This works whenever
    the circuit is structured enough that its critical path is identifiable from
    its recursion (e.g. the carry chain of a ripple-carry adder); the structured
    arithmetic circuits qianxu uses qualify.

    The model below abstracts a schedule as a START-TIME function `begin_ : Nat →
    Nat` (gate `i` starts at `begin_ i`), so the theorem quantifies over ALL
    schedules at once — no scheduling is fixed, only the chain dependency and the
    per-gate minimum duration `τ` (Q1: circuit + hardware, not system schedule). -/

/-- PARAMETRIC CRITICAL-PATH LOWER BOUND.  For a chain of gates where each gate
    runs at least `τ` and gate `i+1` cannot start before gate `i`'s minimum
    completion (`begin_ i + τ ≤ begin_ (i+1)`), gate `n` starts no earlier than
    `begin_ 0 + n·τ` — for ANY start-time schedule `begin_`.  Proven by induction
    on `n`: NO graph algorithm, scalable to any depth. -/
theorem serial_chain_depth (τ : Nat) (begin_ : Nat → Nat)
    (hdep : ∀ i, begin_ i + τ ≤ begin_ (i + 1)) (n : Nat) :
    begin_ 0 + n * τ ≤ begin_ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hk := hdep k
      rw [Nat.succ_mul]
      omega

/-- Instantiation at RSA-2048 scale is INSTANT — it is the `∀ n` theorem applied
    to a literal, NOT a graph traversal.  (n = 10⁹ would be equally immediate.)
    So a depth-`n` dependency chain forces makespan ≥ `n·τ` at any scale, with no
    per-instance graph computation. -/
example (τ : Nat) (b : Nat → Nat) (h : ∀ i, b i + τ ≤ b (i + 1)) :
    b 0 + 2048 * τ ≤ b 2048 :=
  serial_chain_depth τ b h 2048

/-! ## (9) Composing the floor through a circuit's STRUCTURE.

    A structured circuit's critical path is a chain threaded through its
    sub-structures, so its depth is a PRODUCT of structural coefficients — which
    is what makes the floor parametric (Q2-scalable) and circuit-derived (Q1:
    no scheduling).  For Shor's modular exponentiation:
      • the ripple-carry ADDER's carry chain has length = the adder width
        (carry `c_{i+1}` depends on `c_i`) ⇒ Toffoli-depth ≥ width;
        (the carry-lookahead variant cuts this to ≈ log width — a different,
        shallower DAG, hence a different floor: Q1's decomposition residue);
      • a MULTIPLICATION threads `adds_per_mult` additions on its critical path;
      • MODEXP threads `mults` modular multiplications (the accumulator chain).
    So the modexp critical-path Toffoli-DEPTH ≥ `mults · adds_per_mult ·
    adder_depth`, and the runtime floor ≥ that depth · `τ_Toff` cycles — for ANY
    schedule and ANY resource count.  The coefficients come from the SPECIFIC
    circuit (qianxu App. E/F); the corpus instantiation plugs them in. -/

/-- Modexp critical-path Toffoli-depth from its structural coefficients. -/
def modexpToffoliDepth (mults adds_per_mult adder_depth : Nat) : Nat :=
  mults * adds_per_mult * adder_depth

/-- Runtime floor in code-cycles = (critical-path Toffoli-depth) · (min cycles
    per Toffoli). -/
def runtimeFloorCycles (depth tau_toff_cycles : Nat) : Nat :=
  depth * tau_toff_cycles

/-- THE FLOOR IS A GENUINE `∀`-SCHEDULES LOWER BOUND.  A critical path of `depth`
    serially-dependent Toffolis, each taking at least `τ` cycles, takes at least
    `runtimeFloorCycles depth τ` cycles — no matter the schedule and no matter
    the resource provisioning (a specialisation of `serial_chain_depth`, with
    `begin_ i` the start cycle of the i-th critical-path Toffoli). -/
theorem runtimeFloor_is_lower_bound (τ : Nat) (begin_ : Nat → Nat)
    (hdep : ∀ i, begin_ i + τ ≤ begin_ (i + 1)) (depth : Nat) :
    begin_ 0 + runtimeFloorCycles depth τ ≤ begin_ depth := by
  unfold runtimeFloorCycles
  exact serial_chain_depth τ begin_ hdep depth

end FormalRV.System.DependencyGraph
