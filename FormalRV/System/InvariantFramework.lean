/-
  FormalRV.Framework.InvariantFramework — EXTENSIBLE SPACE-TIME INVARIANT
  FRAMEWORK.

  The fixed resources are qubits/atoms (space), classical compute, and time; a
  schedule makes claims on them.  Every system invariant is a space-time
  PROPOSITION over these resources — a `SpaceTimeInvariant` (named decidable
  predicate on `SystemCtx`).  They live in an OPEN list checked uniformly by
  `checkAll`; `checkAll_snoc`/`checkAll_mono` prove that appending an invariant
  ANDs in its check WITHOUT affecting the others, so a future FT-OS author
  extends coverage by appending one instance — never editing existing
  invariants.  The standard scheduling rules (capacity = ancilla, exclusivity,
  latency/speed = routing, throughput = T-factory, decoder) are instances
  (`baseInvariants`); `latticeParallelMoveInv` shows the framework captures
  INSTRUCTION-LEVEL hardware limits too (neutral-atom rigid parallel movement —
  time-overlapping atom moves must share a displacement).
  FTSchedule.ft_ok is recoverable as `checkAll baseInvariants c &&
  distance_adequate`.

  No Mathlib.  Pure List / Bool / Nat + `decide`.  No `sorry`, no `axiom`,
  no `admit`.
-/
import FormalRV.System.ScheduleInvariantsExplicit

namespace FormalRV.Framework.InvariantFramework

open FormalRV.Framework.Architecture FormalRV.Framework.ScheduleInv

/-! ## (1) The fixed resources + the schedule context -/

/-- An atom-position resource usage: atom `id` moves from `fromPos` to `toPos`
    over [begin_us, end_us).  Positions are lattice coords (row, col). -/
structure AtomMove where
  id       : Nat
  fromPos  : Nat × Nat
  toPos    : Nat × Nat
  begin_us : Nat
  end_us   : Nat
deriving Repr, DecidableEq

/-- The fixed resources + schedule a system invariant is a proposition about:
    the zoned architecture (qubit/atom slots in space + timing params), the
    syscall schedule (resource claims in space-time), the atom-move schedule,
    and the throughput/decoder window parameters. -/
structure SystemCtx where
  arch           : ZonedArch
  sched          : List SysCall
  moves          : List AtomMove
  window_us      : Nat
  max_per_window : Nat
  t_react_us     : Nat
  distance_fn    : Nat → Nat

/-! ## (2) The space-time invariant abstraction + the uniform mechanical check -/

/-- A space-time proposition over the fixed resources: a named decidable
    predicate on the system context. -/
structure SpaceTimeInvariant where
  name  : String
  check : SystemCtx → Bool

/-- Mechanical uniform check: every invariant in the (open) list holds. -/
def checkAll (invs : List SpaceTimeInvariant) (c : SystemCtx) : Bool :=
  invs.all (fun inv => inv.check c)

/-! ## (3) Extensibility theorems — appending an invariant ANDs in its check
    WITHOUT affecting the others.  These three are the load-bearing
    "open framework" theorems. -/

theorem checkAll_append (a b : List SpaceTimeInvariant) (c : SystemCtx) :
    checkAll (a ++ b) c = (checkAll a c && checkAll b c) := by
  simp [checkAll, List.all_append]

theorem checkAll_snoc (invs : List SpaceTimeInvariant) (inv : SpaceTimeInvariant)
    (c : SystemCtx) :
    checkAll (invs ++ [inv]) c = (checkAll invs c && inv.check c) := by
  simp [checkAll, List.all_append]

/-- Monotonicity: extending the invariant set can only restrict — a schedule
    valid under more invariants is valid under fewer.  So adding invariants
    never breaks an existing guarantee. -/
theorem checkAll_mono (invs extra : List SpaceTimeInvariant) (c : SystemCtx)
    (h : checkAll (invs ++ extra) c = true) : checkAll invs c = true := by
  rw [checkAll_append] at h; exact (Bool.and_eq_true_iff.mp h).1

/-! ## (4) The existing invariants as instances (wrap the decidable checks) -/

def capacityInv : SpaceTimeInvariant :=
  { name := "capacity (ancilla/zone slots)",
    check := fun c => capacity_in_arch_ok c.arch c.sched
                      && capacity_per_cycle_ok c.arch c.sched }

def exclusivityInv : SpaceTimeInvariant :=
  { name := "exclusivity (no shared slot)", check := fun c => exclusivity_ok c.sched }

def latencyInv : SpaceTimeInvariant :=
  { name := "latency/speed (routing)",
    check := fun c => latency_speed_ok c.arch.t_cycle_us c.arch.v_max_um_per_us
                        c.distance_fn c.sched }

def throughputInv : SpaceTimeInvariant :=
  { name := "throughput (T-factory)",
    check := fun c => window_throughput_ok c.sched c.window_us c.max_per_window }

def decoderInv : SpaceTimeInvariant :=
  { name := "decoder reaction-time", check := fun c => decoder_react_ok c.t_react_us c.sched }

/-- The standard scheduling rules as a base set.  `checkAll baseInvariants c`
    is the schedulability core of `FTSchedule.ft_ok` minus distance adequacy. -/
def baseInvariants : List SpaceTimeInvariant :=
  [capacityInv, exclusivityInv, latencyInv, throughputInv, decoderInv]

/-! ## (5) THE NEW INSTANCE — neutral-atom instruction-level constraint

    Neutral-atom AOD/lattice movement: atoms are in a lattice and a parallel
    move shifts a whole row/column rigidly, so atoms moved in time-overlapping
    steps must share the SAME displacement ("same pace").  Modelled as a
    space-time proposition over the atom-move resource. -/

/-- Two moves overlap in time. -/
def movesOverlap (a b : AtomMove) : Bool :=
  decide (a.begin_us < b.end_us) && decide (b.begin_us < a.end_us)

/-- Equal displacement (Nat-safe via cross-addition, avoiding subtraction):
    (to-from) of a equals (to-from) of b in both coordinates. -/
def sameDisplacement (a b : AtomMove) : Bool :=
  decide (a.toPos.1 + b.fromPos.1 = b.toPos.1 + a.fromPos.1) &&
  decide (a.toPos.2 + b.fromPos.2 = b.toPos.2 + a.fromPos.2)

/-- Neutral-atom parallel-move constraint: any two time-overlapping atom moves
    must have the same displacement (rigid lattice translation — "same pace").
    An INSTRUCTION-LEVEL hardware limit, expressed as a space-time invariant. -/
def latticeParallelMoveInv : SpaceTimeInvariant :=
  { name := "neutral-atom rigid parallel move (same pace)",
    check := fun c => c.moves.all (fun a => c.moves.all (fun b =>
      ! movesOverlap a b || sameDisplacement a b)) }

/-! ## (6) WORKED INSTANCE + tests

    `demoCtx` reuses the EXACT `demoArch` / `demoSched` /
    (`window_us = 1000`, `max_per_window = 1`, `t_react_us = 10`, `demoDist`)
    that `System/FaultTolerantSchedule.lean` already proves passes
    `all_invariants_ok` + `decoder_react_ok`, so all five base invariants hold.
    The atom-move list is two coherent parallel moves (both displacement (0,+1),
    overlapping in [0,10)), so `latticeParallelMoveInv` also holds. -/

/-- Worked-instance architecture (mirror of `FTSchedule.demoArch`). -/
def demoArch : ZonedArch :=
  { zones :=
      [ { name := "Data",      atom_lo := 0,  atom_hi := 10 }
      , { name := "Workspace", atom_lo := 10, atom_hi := 20 }
      , { name := "Factory",   atom_lo := 20, atom_hi := 30 }
      , { name := "Routing",   atom_lo := 30, atom_hi := 40 } ]
    total_atoms := 40
    t_cycle_us  := 100
    v_max_um_per_us := 5 }

/-- Route distance function: every channel covers 30 µm (mirror of
    `FTSchedule.demoDist`). -/
def demoDist : Nat → Nat := fun _ => 30

/-- Worked-instance schedule (mirror of `FTSchedule.demoSched`). -/
def demoSched : List SysCall :=
  [ { kind := SysCallKind.RequestMagicState 2,   begin_us := 0,  end_us := 10 }
  , { kind := SysCallKind.RequestFreshAncilla 1, begin_us := 0,  end_us := 10 }
  , { kind := SysCallKind.TransitQubit 30 0,     begin_us := 10, end_us := 20 }
  , { kind := SysCallKind.DecodeSyndrome 0,      begin_us := 20, end_us := 25 }
  , { kind := SysCallKind.Measure 5 0,           begin_us := 30, end_us := 35 }
  , { kind := SysCallKind.Gate2q 1 2 0,          begin_us := 40, end_us := 45 } ]

/-- Two COHERENT parallel atom moves: both displace by (0,+1) (one lattice site
    rightward), both running over [0,10) — a legal rigid translation. -/
def demoMoves : List AtomMove :=
  [ { id := 0, fromPos := (0,0), toPos := (0,1), begin_us := 0, end_us := 10 }
  , { id := 1, fromPos := (1,0), toPos := (1,1), begin_us := 0, end_us := 10 } ]

/-- The worked system context. -/
def demoCtx : SystemCtx :=
  { arch := demoArch, sched := demoSched, moves := demoMoves,
    window_us := 1000, max_per_window := 1, t_react_us := 10, distance_fn := demoDist }

-- The base invariants hold (mechanical check of the standard scheduling rules):
example : checkAll baseInvariants demoCtx = true := by decide

-- Extending with the neutral-atom constraint: adding it ANDs in, base
-- unaffected (this is `checkAll_snoc` instantiated at the worked context):
example : checkAll (baseInvariants ++ [latticeParallelMoveInv]) demoCtx
        = (checkAll baseInvariants demoCtx && latticeParallelMoveInv.check demoCtx) :=
  checkAll_snoc baseInvariants latticeParallelMoveInv demoCtx

-- POSITIVE: two coherent parallel moves (same displacement, overlapping) pass:
example : latticeParallelMoveInv.check demoCtx = true := by decide

-- The full extended set still passes on the coherent context:
example : checkAll (baseInvariants ++ [latticeParallelMoveInv]) demoCtx = true := by decide

/-- NEGATIVE: two overlapping moves with DIFFERENT displacement.  Move 0
    displaces (0,+1); move 1 displaces (+1,0); both run over [0,10), so they
    overlap with unequal displacement — a non-rigid (illegal) parallel move. -/
def badMoveCtx : SystemCtx := { demoCtx with moves :=
  [ { id := 0, fromPos := (0,0), toPos := (0,1), begin_us := 0, end_us := 10 }
  , { id := 1, fromPos := (1,0), toPos := (2,0), begin_us := 0, end_us := 10 } ] }

-- The new invariant alone rejects the bad move set:
example : latticeParallelMoveInv.check badMoveCtx = false := by decide

-- Hence the extended set fails on the bad context:
example : checkAll (baseInvariants ++ [latticeParallelMoveInv]) badMoveCtx = false := by decide

-- ... and the base invariants STILL pass on badMoveCtx (only the new
-- constraint fails — invariants do not interfere with each other):
example : checkAll baseInvariants badMoveCtx = true := by decide

end FormalRV.Framework.InvariantFramework
