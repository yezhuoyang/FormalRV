/-
  FormalRV.Resource.SysCallCount — THE system-level (SysCall) resource
  counters.

  ## Contract (the folder's design principle, enforced here for L4)

  These are honest tree-walks over the concrete syntactic object
  `List SysCall` and NOTHING else: no architecture, no checkers, no
  proofs.  **Every verifier, certificate, or theorem that claims a
  system-level resource (time, op counts, qubit footprint, peak
  occupancy, syndrome volume) must call THESE functions — never redefine
  its own.**  A skeptic can `#eval` any of them on any schedule without
  reading a proof.

  Re-pointed consumers (single-source enforcement):
    * `ScheduleCombinators.scheduleWallclockUs`  → `wallclockUs`
    * `CompressedSchedule.resourceOfSysCalls`    → the per-kind counters
    * `FTSchedule.countKind`                     → `countWhere`
    * `GE2021PPMSysInv.count_*`                  → the per-kind counters
    * `QECScheduleToSystem.decodeIds/pfuCorrs`   → moved here

  The FTQ-VM computes the same quantities independently from the same
  DEVICE-PROGRAM files; `scripts/EmitResourceCounts.lean` +
  `ftq_vm/backend/tests/test_resource_counts.py` assert exact agreement.
-/
import FormalRV.System.Core.Architecture
import FormalRV.System.Core.CodedLayout
import FormalRV.Resource.Interface

namespace FormalRV.Resource.SysCallCount

open FormalRV.System.Architecture

/-! ## §1. Kind predicates (the counter's own, checker-independent) -/

def isGate1q   : SysCallKind → Bool | .Gate1q ..             => true | _ => false
def isGate2q   : SysCallKind → Bool | .Gate2q ..             => true | _ => false
def isMeasure  : SysCallKind → Bool | .Measure ..            => true | _ => false
def isTransit  : SysCallKind → Bool | .TransitQubit ..       => true | _ => false
def isFreshAnc : SysCallKind → Bool | .RequestFreshAncilla _ => true | _ => false
def isMagicReq : SysCallKind → Bool | .RequestMagicState _   => true | _ => false
def isDecode   : SysCallKind → Bool | .DecodeSyndrome _      => true | _ => false
def isFeedback : SysCallKind → Bool | .PauliFrameUpdate _    => true | _ => false

/-! ## §2. TIME: wallclock and busy time -/

/-- **Wallclock** (µs): the latest `end_us` (0 for the empty schedule). -/
def wallclockUs (xs : List SysCall) : Nat :=
  xs.foldl (fun acc sc => Nat.max acc sc.end_us) 0

/-- **Total busy time** (µs): the sum of all op durations (a lower bound
    on hardware-seconds; ≥ wallclock·(min parallelism)). -/
def totalBusyUs (xs : List SysCall) : Nat :=
  xs.foldl (fun acc sc => acc + (sc.end_us - sc.begin_us)) 0

/-! ## §3. TIME: operation counters -/

/-- Count SysCalls whose kind satisfies `p`. -/
def countWhere (p : SysCallKind → Bool) (xs : List SysCall) : Nat :=
  (xs.filter (fun sc => p sc.kind)).length

def countGate1q   (xs : List SysCall) : Nat := countWhere isGate1q xs
def countGate2q   (xs : List SysCall) : Nat := countWhere isGate2q xs
def countMeasure  (xs : List SysCall) : Nat := countWhere isMeasure xs
def countTransit  (xs : List SysCall) : Nat := countWhere isTransit xs
def countFreshAnc (xs : List SysCall) : Nat := countWhere isFreshAnc xs
def countMagicReq (xs : List SysCall) : Nat := countWhere isMagicReq xs
def countDecode   (xs : List SysCall) : Nat := countWhere isDecode xs
def countFeedback (xs : List SysCall) : Nat := countWhere isFeedback xs

/-- Total SysCall count (physical ops AND system calls). -/
def opCountS (xs : List SysCall) : Nat := xs.length

/-! ## §4. CLASSICAL-CHANNEL IDS -/

/-- The decode round ids, in emission order. -/
def decodeIds (xs : List SysCall) : List Nat :=
  xs.filterMap fun sc =>
    match sc.kind with
    | .DecodeSyndrome r => some r
    | _                 => none

/-- The frame-update correction ids, in emission order. -/
def pfuCorrs (xs : List SysCall) : List Nat :=
  xs.filterMap fun sc =>
    match sc.kind with
    | .PauliFrameUpdate c => some c
    | _                   => none

/-! ## §5. SPACE: qubit counting -/

/-- All sites the schedule ever touches (deduplicated; uses the IR's
    `syscall_acts_on` site map). -/
def sitesTouched (xs : List SysCall) : List Nat :=
  (xs.flatMap syscall_acts_on).dedup

/-- **Qubit footprint**: how many distinct sites the schedule uses. -/
def qubitFootprint (xs : List SysCall) : Nat :=
  (sitesTouched xs).length

/-- Sites occupied at instant `t` (half-open `[begin, end)` activity). -/
def sitesActiveAt (xs : List SysCall) (t : Nat) : List Nat :=
  ((xs.filter (fun sc => decide (sc.begin_us ≤ t) && decide (t < sc.end_us)))
    |>.flatMap syscall_acts_on).dedup

/-- **Peak site occupancy**: the maximum number of simultaneously
    occupied sites, sampled at op start times (sufficient: occupancy only
    increases when an op begins). -/
def peakSiteOccupancy (xs : List SysCall) : Nat :=
  (xs.map (fun sc => (sitesActiveAt xs sc.begin_us).length)).foldl Nat.max 0

/-! ## §6. SYNDROME VOLUME (feeds the I5 link contract) -/

/-- Total syndrome bits produced, at `bits` per measurement. -/
def syndromeBitsTotal (bits : Nat) (xs : List SysCall) : Nat :=
  bits * countMeasure xs

/-! ## §6.b Interface instance — the same cross-IR shape as `Gate`,
       `BaseUCom`, and `PhysCircuit` (TIME = cnot/gates, SPACE = qubits) -/

instance : FormalRV.Resource.HasResourceCount (List SysCall) where
  cnot   := countGate2q
  gates  := opCountS
  qubits := qubitFootprint

/-! ## §7. Counting algebra (append/cons — pure list facts) -/

@[simp] theorem countWhere_nil (p : SysCallKind → Bool) :
    countWhere p [] = 0 := rfl

theorem countWhere_append (p : SysCallKind → Bool) (xs ys : List SysCall) :
    countWhere p (xs ++ ys) = countWhere p xs + countWhere p ys := by
  simp [countWhere]

theorem decodeIds_append (xs ys : List SysCall) :
    decodeIds (xs ++ ys) = decodeIds xs ++ decodeIds ys :=
  List.filterMap_append

theorem pfuCorrs_append (xs ys : List SysCall) :
    pfuCorrs (xs ++ ys) = pfuCorrs xs ++ pfuCorrs ys :=
  List.filterMap_append

theorem countDecode_eq_decodeIds_length (xs : List SysCall) :
    countDecode xs = (decodeIds xs).length := by
  induction xs with
  | nil => rfl
  | cons sc rest ih =>
      cases h : sc.kind <;>
        simp_all [countDecode, countWhere, decodeIds, isDecode,
                  List.filter_cons, List.filterMap_cons, h]

end FormalRV.Resource.SysCallCount
