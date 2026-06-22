/-
  Concrete `native_decide` regressions on the n=1 adder block.

  Expanded strict bundle at n=10; symbolic acceptance and resource
  counts at n=1,000,000 (O(|body|), no expansion); seq2/seq3
  Obligation-A instances (96/144 SysCalls); feedback-after-decode at
  n=100; ancilla freshness at n=3 and n=10; plus the negative tests
  `feedback_bad_body_for_repeat` and `freshness_bad_body_for_repeat`
  showing the symbolic checker rejects bad bodies.  These ground the
  parametric chains; they are not load-bearing for them.
-/

import FormalRV.System.Artifacts.LayeredArtifactInterface
import FormalRV.System.Artifacts.CompressedRepeat.ShiftInvariance
import FormalRV.System.Artifacts.CompressedRepeat.FeedbackAfterDecode

namespace FormalRV.System.CompressedRepeatSoundness

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.AdderSystem
open FormalRV.System.LayeredArtifactInterface

/-! ## §7. Headline concrete instances

    Concrete `native_decide` groundings of the parametric
    chains proved in `SymbolicRepeatSoundness.lean`; the
    parametric theorems do not depend on these. -/

/-- `n=10` cross-check via expansion + `native_decide`.  This
    confirms that the strict bundle accepts the EXPANDED
    repeated schedule for a moderately large `n`, grounding
    the symbolic checker against the existing
    expansion-based check. -/
theorem adder_n1_repeated_10_expanded_strict_ok :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        adder_n1_system_models.arch
        adder_n1_system_models.opCap
        adder_n1_system_models.slotCap
        adder_n1_system_models.ancillaModel
        (CompressedSchedule.rep 10 (CompressedSchedule.atom adder_n1_syscalls)).expand
        adder_n1_system_models.t_react_us
        adder_n1_system_models.window_us
        adder_n1_system_models.max_per_window = true := by
  native_decide

/-- **Headline scalability regression**: `n=1_000_000` via
    `symbolic_rep_strict_ok`.  The symbolic check is
    reps-independent by design: it checks the body once
    (`O(|body|)`) and never materialises the 1,000,000 SysCall
    copies; soundness for the expanded n-fold schedule is
    established separately in `SymbolicRepeatSoundness.lean`. -/
theorem adder_n1_repeated_1000000_symbolic_ok :
    symbolic_rep_strict_ok
        adder_n1_system_models adder_n1_syscalls 1000000 = true := by
  native_decide

/-- Symbolic wallclock for `rep 1_000_000`: `1_000_000 × 48 =
    48_000_000` µs.  Computed by `CompressedResourceSummary.scale`. -/
theorem adder_n1_repeated_1000000_resource_wallclock :
    (CompressedSchedule.rep 1000000
        (CompressedSchedule.atom adder_n1_syscalls)).resource.wallclock_us
      = 48000000 := by
  native_decide

/-- Symbolic Gate2q count for `rep 1_000_000`: `1_000_000 × 18
    = 18_000_000`. -/
theorem adder_n1_repeated_1000000_resource_gate2q :
    (CompressedSchedule.rep 1000000
        (CompressedSchedule.atom adder_n1_syscalls)).resource.gate2q_count
      = 18000000 := by
  native_decide

/-- Symbolic SysCall count for `rep 1_000_000`: `1_000_000 ×
    48 = 48_000_000`. -/
theorem adder_n1_repeated_1000000_resource_syscall_count :
    (CompressedSchedule.rep 1000000
        (CompressedSchedule.atom adder_n1_syscalls)).resource.syscall_count
      = 48000000 := by
  native_decide

theorem adder_n1_scheduleWithinWallclock :
    scheduleWithinWallclock adder_n1_syscalls = true := by native_decide

/-! ### §9.e Concrete adder seq2 examples for all four
       pairwise / capacity invariants -/

/-- The composition `seqSchedules adder adder` is 96 SysCalls,
    96 µs wallclock. -/
private def adder_seq2 : List SysCall :=
  seqSchedules adder_n1_syscalls adder_n1_syscalls

theorem adder_seq2_length : adder_seq2.length = 96 := by native_decide

theorem adder_seq2_wallclock : scheduleWallclockUs adder_seq2 = 96 := by native_decide

theorem adder_seq2_exclusivity_ok :
    exclusivity_ok adder_seq2 = true := by native_decide

theorem adder_seq2_factory_exclusivity_ok :
    factory_exclusivity_ok adder_seq2 = true := by native_decide

theorem adder_seq2_operation_capacity_ok :
    operation_capacity_ok
        adder_n1_system_models.opCap adder_seq2 = true := by native_decide

theorem adder_seq2_slot_capacity_ok :
    slot_capacity_ok
        adder_n1_system_models.slotCap adder_seq2 = true := by native_decide

/-- **Combined Obligation-A status for adder seq2** (concrete
    instance, not parametric).  All four pairwise / capacity
    invariants hold on `seqSchedules adder adder`. -/
theorem adder_seq2_obligation_A_ok :
    exclusivity_ok adder_seq2 = true
    ∧ factory_exclusivity_ok adder_seq2 = true
    ∧ operation_capacity_ok adder_n1_system_models.opCap adder_seq2 = true
    ∧ slot_capacity_ok adder_n1_system_models.slotCap adder_seq2 = true :=
  ⟨ adder_seq2_exclusivity_ok
  , adder_seq2_factory_exclusivity_ok
  , adder_seq2_operation_capacity_ok
  , adder_seq2_slot_capacity_ok ⟩

/-! ### §9.f Concrete adder seq3 example (144 SysCalls) -/

private def adder_seq3 : List SysCall :=
  seqManySchedules
    [adder_n1_syscalls, adder_n1_syscalls, adder_n1_syscalls]

theorem adder_seq3_length : adder_seq3.length = 144 := by native_decide

theorem adder_seq3_wallclock : scheduleWallclockUs adder_seq3 = 144 := by native_decide

theorem adder_seq3_obligation_A_ok :
    exclusivity_ok adder_seq3 = true
    ∧ factory_exclusivity_ok adder_seq3 = true
    ∧ operation_capacity_ok adder_n1_system_models.opCap adder_seq3 = true
    ∧ slot_capacity_ok adder_n1_system_models.slotCap adder_seq3 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ### §10.i Concrete regression examples -/

/-- Direct check: `rep 100 adder` expanded passes the
    feedback-after-decode invariant. -/
theorem adder_repeated_100_feedback_after_decode_ok :
    feedback_after_decode_ok
        (CompressedSchedule.rep 100 (CompressedSchedule.atom adder_n1_syscalls)).expand
      = true :=
  feedback_after_decode_ok_repeated_atom_expand adder_n1_syscalls 100
    (by native_decide)

/-- A bad body: `PauliFrameUpdate 0` at `[0, 1)` BEFORE the
    matching `DecodeSyndrome 0` at `[10, 11)` (the review's
    counterexample, restated locally to avoid namespace
    cycles). -/
def feedback_bad_body_for_repeat : List SysCall :=
  [ { kind := SysCallKind.PauliFrameUpdate 0
      begin_us := 0, end_us := 1 }
  , { kind := SysCallKind.DecodeSyndrome 0
      begin_us := 10, end_us := 11 } ]

theorem feedback_bad_body_fails_feedback_check :
    feedback_after_decode_ok feedback_bad_body_for_repeat = false := by
  native_decide

theorem feedback_bad_body_repeat_symbolic_rejected :
    symbolic_rep_strict_ok
        adder_n1_system_models feedback_bad_body_for_repeat 10 = false := by
  native_decide

/-! ### §11.f–g Concrete ancilla-freshness regressions
       (Obligation C) -/

/-- Direct check: the EXPANDED `rep 3 adder` schedule (144
    SysCalls) passes the ancilla-freshness check.  Closed by
    `native_decide` on the expansion; the parametric chain
    (`symbolic_rep_implies_expanded_block_ancilla_freshness_ok`
    in `FreshnessSoundness.lean`) covers arbitrary `n`. -/
theorem adder_repeated_3_ancilla_freshness_ok :
    ancilla_freshness_ok
        adder_n1_system_models.ancillaModel
        (CompressedSchedule.rep 3 (CompressedSchedule.atom adder_n1_syscalls)).expand
      = true := by
  native_decide

/-- Direct check at `n = 10` (480 SysCalls). -/
theorem adder_repeated_10_ancilla_freshness_ok :
    ancilla_freshness_ok
        adder_n1_system_models.ancillaModel
        (CompressedSchedule.rep 10 (CompressedSchedule.atom adder_n1_syscalls)).expand
      = true := by
  native_decide

/-- A bad body: Gate2q on ancilla site 100 before any
    `RequestFreshAncilla` (the review's freshness violator
    shape).  Body fails ancilla-freshness ⇒ strict bundle
    fails ⇒ symbolic_rep_strict_ok rejects. -/
def freshness_bad_body_for_repeat : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 100 0, begin_us := 0, end_us := 1 } ]

theorem freshness_bad_body_fails_freshness_check :
    ancilla_freshness_ok
        adder_n1_system_models.ancillaModel freshness_bad_body_for_repeat = false := by
  native_decide

theorem freshness_bad_body_repeat_symbolic_rejected :
    symbolic_rep_strict_ok
        adder_n1_system_models freshness_bad_body_for_repeat 10 = false := by
  native_decide

end FormalRV.System.CompressedRepeatSoundness
