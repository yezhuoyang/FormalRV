/-
  FormalRV.System.Examples.ParallelismVerification — the system-level
  framework expresses parallelism and its limits.

  Parallelism in the Cain–Xu setting (App. B/E/F) splits into exactly TWO
  classes, and the framework expresses both:

    (A) RESOURCE-CAPACITY constraints — `demand ≤ capacity`.  What CAN'T overlap:
        two ops can run concurrently only if they don't exceed a shared resource.
        Captured by the extensible `checkAll` invariants, every one of which is
        ACTIVE-SET / OVERLAP based (genuinely concurrency-aware, not a sequential
        approximation):
          • exclusivity      — time-overlapping ops claim DISJOINT atoms;
          • capacity/cycle   — the active set's per-zone load ≤ zone capacity;
          • throughput       — factory production rate over any window;
          • decoder reaction — each decode finishes within the reaction budget;
          • + extensible: rigid AOD parallel moves, decoder CONCURRENCY (§D).

    (B) CAUSAL DEPENDENCIES — a partial order on operations.  What MUST be
        sequential: producer must finish before consumer starts.  Captured by
        `Architecture.semantically_correct` (measure → decode → feed-forward;
        teleport-in → compute → teleport-out; no double-measure).

  "Maximum parallelism subject to system invariants" is then PRECISELY: two
  operations may run concurrently iff they have no resource conflict (A) AND no
  causal dependency (B).  This is the standard dependency-DAG + resource-
  constraint model of correct parallel scheduling, and the framework decides it.

  §C certifies ONLY the disjointness precondition of the sequentializability
  argument (time-overlapping ops act on disjoint atoms, hence share no qubit);
  the commutation step and a "parallel ≡ sequential" theorem are NOT
  formalised here or elsewhere in the SysCall layer.

  EXTENSIBILITY: any future parallelism limit is ONE more `SpaceTimeInvariant`
  that ANDs in via `checkAll_snoc` without touching the others
  (`checkAll_mono`).  §D adds decoder-concurrency as a worked example.

  Residues (honest): the syscall layer is non-semantic by design (per-op
  semantics live at the PPM layer).  Adaptive/feed-forward branching is
  abstracted via reaction-time bounds, not modelled as data-dependent
  control flow.

  No Mathlib.  Pure Bool / Nat + `decide`.  No `sorry`, no `axiom`.
-/
import FormalRV.System.Invariants.InvariantFramework

set_option maxRecDepth 8000

namespace FormalRV.System.ParallelismVerification

open FormalRV.System.Architecture FormalRV.System.ScheduleInv
open FormalRV.System.InvariantFramework

/-! ## (A) RESOURCE-CAPACITY PARALLELISM — max concurrency passes the invariants.

    A maximally-parallel schedule: FIVE operations across FOUR zones, all running
    CONCURRENTLY in the window [0,10) — syndrome extraction on a Data atom, a
    surgery PPM on a Workspace atom, a factory magic-state request, a decoder
    call, and a fresh-ancilla request.  Each lands in its own zone / resource;
    the two atom-claiming ops use disjoint atoms.  This is the four-zone
    concurrent pipeline of qianxu (memory-QEC ∥ surgery ∥ factory ∥ decode). -/

def parallelSched : List SysCall :=
  [ { kind := SysCallKind.Measure 5 0,           begin_us := 0, end_us := 10 }   -- syndrome ext. (Data zone)
  , { kind := SysCallKind.Measure 15 0,          begin_us := 0, end_us := 10 }   -- surgery PPM (Workspace)
  , { kind := SysCallKind.RequestMagicState 2,   begin_us := 0, end_us := 10 }   -- factory (Resource)
  , { kind := SysCallKind.DecodeSyndrome 0,      begin_us := 0, end_us := 10 }   -- decoder (classical)
  , { kind := SysCallKind.RequestFreshAncilla 1, begin_us := 0, end_us := 10 } ] -- fresh ancilla

def parallelCtx : SystemCtx :=
  { arch := demoArch, sched := parallelSched, moves := [],
    window_us := 1000, max_per_window := 1, t_react_us := 10, distance_fn := demoDist }

/-- These five operations genuinely run CONCURRENTLY — every one occupies the
    same window [0,10).  This is not a sequential schedule. -/
example : ∀ s ∈ parallelSched, s.begin_us = 0 ∧ s.end_us = 10 := by decide

/-- MAX PARALLELISM IS VALID: the fully-concurrent four-zone schedule passes
    EVERY base invariant.  This is "maximum parallelism allowed as long as the
    system invariants hold", machine-checked. -/
example : checkAll baseInvariants parallelCtx = true := by decide

/-! ### Negative tests — each resource-capacity invariant independently rejects
    an over-parallel schedule (the parallelism limit is real, not advisory). -/

/-- ATOM CONFLICT: two concurrent measurements on the SAME atom 5.  Exclusivity
    rejects — you cannot run two ops on one qubit at once. -/
def conflictCtx : SystemCtx := { parallelCtx with sched :=
  [ { kind := SysCallKind.Measure 5 0, begin_us := 0, end_us := 10 }
  , { kind := SysCallKind.Measure 5 0, begin_us := 0, end_us := 10 } ] }
example : checkAll baseInvariants conflictCtx = false := by decide

/-- THROUGHPUT: two magic-state requests inside one factory window, with
    `max_per_window = 1`.  Window-throughput rejects — the factory cannot supply
    faster than its rate (qianxu: 12 cycles per |CCZ⟩). -/
def throughputViolCtx : SystemCtx := { parallelCtx with sched :=
  [ { kind := SysCallKind.RequestMagicState 2, begin_us := 0, end_us := 10 }
  , { kind := SysCallKind.RequestMagicState 2, begin_us := 5, end_us := 15 } ] }
example : checkAll baseInvariants throughputViolCtx = false := by decide

/-- DECODER REACTION: a decode that runs longer than the reaction budget
    (`t_react_us = 10`).  The decoder invariant rejects — real-time decoding must
    keep up with the cycle stream. -/
def slowDecodeCtx : SystemCtx := { parallelCtx with sched :=
  [ { kind := SysCallKind.DecodeSyndrome 0, begin_us := 0, end_us := 50 } ] }
example : checkAll baseInvariants slowDecodeCtx = false := by decide

/-! ## (B) CAUSAL DEPENDENCY — the orderings that FORBID parallelism.

    `Architecture.semantically_correct` enforces producer-before-consumer via
    timestamps.  The measure → decode → feed-forward chain (and qianxu's
    teleport-in → compute → teleport-out) is a hard causal order: no amount of
    parallelism can let a decode precede its syndrome. -/

/-- A measure → decode → feed-forward chain respects the causal order: every
    SysCall's precondition is met (decode sees a prior measurement; the frame
    update sees a prior decode). -/
def causalSched : Schedule :=
  [ { kind := SysCallKind.Measure 0 0,        begin_us := 0,  end_us := 10 }
  , { kind := SysCallKind.DecodeSyndrome 0,   begin_us := 10, end_us := 15 }
  , { kind := SysCallKind.PauliFrameUpdate 0, begin_us := 15, end_us := 16 } ]
example : semantically_correct [] neutral_atom_mini causalSched = true := by decide

/-- VIOLATION: decoding BEFORE any measurement.  The framework rejects it — the
    measure → decode dependency cannot be parallelised away. -/
def badCausalSched : Schedule :=
  [ { kind := SysCallKind.DecodeSyndrome 0, begin_us := 0,  end_us := 5  }
  , { kind := SysCallKind.Measure 0 0,      begin_us := 10, end_us := 20 } ]
example : semantically_correct [] neutral_atom_mini badCausalSched = false := by decide

/-! ## (C) THE DISJOINTNESS PRECONDITION for sequentializability.

    Exclusivity makes time-overlapping operations act on DISJOINT atoms
    (`atoms_disjoint`: no atom of one op's support appears in the other's),
    so their physical circuits share no qubit — the standard precondition
    for commuting them past each other and reducing the concurrent schedule
    to a sequential one whose per-operation actions are certified at the
    PPM layer.  This file certifies ONLY that precondition, via
    `exclusivity_ok`; the commutation step and the resulting "parallel ≡
    sequential" equivalence are NOT proven here or elsewhere in the SysCall
    layer. -/

/-- Every time-overlapping ordered pair in the parallel schedule acts on
    disjoint atoms — the certified disjointness precondition. -/
example : exclusivity_ok parallelSched = true := by decide

/-! ## (D) EXTENSIBILITY — a NEW parallelism invariant, added without breaking
    the others.  qianxu's decoder uses an ENSEMBLE of decoder instances; the
    number running CONCURRENTLY is a classical-compute capacity limit distinct
    from each decode's reaction time.  We add it as ONE `SpaceTimeInvariant`. -/

/-- Number of `DecodeSyndrome` calls active at time `t`. -/
def decodeDepthAt (sched : List SysCall) (t : Nat) : Nat :=
  (sched.filter (fun sc =>
    match sc.kind with
    | .DecodeSyndrome _ => decide (sc.begin_us ≤ t) && decide (t < sc.end_us)
    | _ => false)).length

/-- NEW invariant: at every begin-time, at most `n_decoders` decoders run
    concurrently (classical-compute parallelism limit — qianxu's decoder
    ensemble). -/
def decoderConcurrencyInv (n_decoders : Nat) : SpaceTimeInvariant :=
  { name := "decoder concurrency (≤ n parallel decodes)",
    check := fun c =>
      (c.sched.map (·.begin_us)).all (fun t => decide (decodeDepthAt c.sched t ≤ n_decoders)) }

/-- Adding it ANDs in its check WITHOUT affecting the base invariants
    (`checkAll_snoc` instantiated) — the extensibility guarantee. -/
example (c : SystemCtx) (n : Nat) :
    checkAll (baseInvariants ++ [decoderConcurrencyInv n]) c
      = (checkAll baseInvariants c && (decoderConcurrencyInv n).check c) :=
  checkAll_snoc baseInvariants (decoderConcurrencyInv n) c

/-- A context with TWO concurrent decodes; both run in [0,10). -/
def twoDecodeCtx : SystemCtx := { parallelCtx with sched :=
  [ { kind := SysCallKind.DecodeSyndrome 0, begin_us := 0, end_us := 10 }
  , { kind := SysCallKind.DecodeSyndrome 1, begin_us := 0, end_us := 10 } ] }

/-- With a 2-decoder budget the extended set passes (2 concurrent ≤ 2). -/
example : checkAll (baseInvariants ++ [decoderConcurrencyInv 2]) twoDecodeCtx = true := by decide

/-- With only a 1-decoder budget, the NEW invariant rejects the 2-concurrent-
    decode schedule… -/
example : checkAll (baseInvariants ++ [decoderConcurrencyInv 1]) twoDecodeCtx = false := by decide

/-- …while the BASE invariants still pass on it — adding the new constraint does
    not interfere with the existing guarantees (non-interference). -/
example : checkAll baseInvariants twoDecodeCtx = true := by decide

end FormalRV.System.ParallelismVerification
