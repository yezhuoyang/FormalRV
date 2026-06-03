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

end FormalRV.System.DependencyGraph
