/-
  Obligation A, sampled-time checks (CLOSED): `operation_capacity_ok`
  and `slot_capacity_ok` under shift, `seqSchedules`, n-fold replicate,
  and expanded repeat.

  Built on `countActiveKindAt` / `activeSitesAt` /
  `activeSiteCountInZoneAt` helpers: append distribution, shift
  compensation, and out-of-window zero facts.  Sample times are
  partitioned at the first block's wallclock; each side's per-time
  check reduces to the corresponding block's own check.  No `sorry`,
  no custom `axiom`.
-/

import FormalRV.System.Artifacts.LayeredArtifactInterface
import FormalRV.System.Artifacts.CompressedRepeat.ShiftInvariance

namespace FormalRV.System.CompressedRepeatSoundness

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.AdderSystem
open FormalRV.System.LayeredArtifactInterface

/-! ### §13.a.15 `countActiveKindAt` helpers

    The sampled-time A-conjuncts (`operation_capacity_ok`,
    `slot_capacity_ok`) build on `countActiveKindAt`.  Three
    helpers are enough to handle sequential composition:

      * count distributes over `++`;
      * shifting the schedule shifts the active count's argument;
      * at times outside a block's wallclock window the count
        is zero. -/

theorem countActiveKindAt_append
    (pred : SysCallKind → Bool) (t : Nat) (xs ys : List SysCall) :
    countActiveKindAt pred t (xs ++ ys)
      = countActiveKindAt pred t xs + countActiveKindAt pred t ys := by
  unfold countActiveKindAt
  rw [List.filter_append, List.length_append]

theorem countActiveKindAt_shiftSchedule
    (pred : SysCallKind → Bool) (t dt : Nat) (xs : List SysCall) :
    countActiveKindAt pred (t + dt) (shiftSchedule dt xs)
      = countActiveKindAt pred t xs := by
  unfold countActiveKindAt shiftSchedule
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro sc _
  simp only [Function.comp]
  rw [shiftSysCall_kind]
  unfold syscallActiveAt
  rw [shiftSysCall_begin, shiftSysCall_end]
  have h1 : decide (sc.begin_us + dt ≤ t + dt) = decide (sc.begin_us ≤ t) := by
    have : (sc.begin_us + dt ≤ t + dt) ↔ (sc.begin_us ≤ t) := by omega
    simp [this]
  have h2 : decide (t + dt < sc.end_us + dt) = decide (t < sc.end_us) := by
    have : (t + dt < sc.end_us + dt) ↔ (t < sc.end_us) := by omega
    simp [this]
  rw [h1, h2]

theorem countActiveKindAt_eq_zero_of_within_wallclock_at_or_after
    (pred : SysCallKind → Bool) (t : Nat) (xs : List SysCall)
    (hwithin : scheduleWithinWallclock xs = true)
    (h : scheduleWallclockUs xs ≤ t) :
    countActiveKindAt pred t xs = 0 := by
  unfold countActiveKindAt
  rw [List.length_eq_zero_iff]
  rw [List.filter_eq_nil_iff]
  intro sc hsc
  have h_end_le : sc.end_us ≤ scheduleWallclockUs xs :=
    scheduleWithinWallclock_end_le xs sc hsc hwithin
  unfold syscallActiveAt
  have h_not : ¬ (t < sc.end_us) := by omega
  simp [h_not]

theorem countActiveKindAt_shiftSchedule_eq_zero_before_offset
    (pred : SysCallKind → Bool) (t dt : Nat) (ys : List SysCall)
    (h : t < dt) :
    countActiveKindAt pred t (shiftSchedule dt ys) = 0 := by
  unfold countActiveKindAt
  rw [List.length_eq_zero_iff]
  rw [List.filter_eq_nil_iff]
  intro sc hsc
  have h_begin : dt ≤ sc.begin_us := shifted_begin_ge_offset dt ys sc hsc
  unfold syscallActiveAt
  have h_not : ¬ (sc.begin_us ≤ t) := by omega
  simp [h_not]

/-! ### §13.a.16 Per-time operation-capacity check abstraction

    Bool function that runs the conjunction of all eight kind
    capacity checks at a single time `t` against schedule `L`.
    `operation_capacity_ok` is exactly this function `.all`-ed
    over the schedule's sample times. -/

private def op_cap_check_at (opCap : OperationCapacityModel)
    (L : List SysCall) (t : Nat) : Bool :=
  decide (countActiveKindAt kindIsGate1q t L ≤ opCap.max_gate1q_active)
  && decide (countActiveKindAt kindIsGate2q t L ≤ opCap.max_gate2q_active)
  && decide (countActiveKindAt kindIsMeasure t L ≤ opCap.max_measure_active)
  && decide (countActiveKindAt kindIsDecode t L ≤ opCap.max_decode_active)
  && decide (countActiveKindAt kindIsFeedback t L ≤ opCap.max_feedback_active)
  && decide (countActiveKindAt kindIsMagicReq t L ≤ opCap.max_magic_req_active)
  && decide (countActiveKindAt kindIsFreshAnc t L ≤ opCap.max_fresh_ancilla_active)
  && decide (countActiveKindAt kindIsTransit t L ≤ opCap.max_transit_active)

private theorem operation_capacity_ok_eq
    (opCap : OperationCapacityModel) (L : List SysCall) :
    operation_capacity_ok opCap L
      = (scheduleEventTimes L).all (op_cap_check_at opCap L) := rfl

/-- If every count in `L'` is ≤ the corresponding count in `L`,
    then `L'`'s per-time check passes whenever `L`'s does. -/
private theorem op_cap_check_at_mono
    (opCap : OperationCapacityModel) (L L' : List SysCall) (t : Nat)
    (h1 : countActiveKindAt kindIsGate1q t L' ≤ countActiveKindAt kindIsGate1q t L)
    (h2 : countActiveKindAt kindIsGate2q t L' ≤ countActiveKindAt kindIsGate2q t L)
    (h3 : countActiveKindAt kindIsMeasure t L' ≤ countActiveKindAt kindIsMeasure t L)
    (h4 : countActiveKindAt kindIsDecode t L' ≤ countActiveKindAt kindIsDecode t L)
    (h5 : countActiveKindAt kindIsFeedback t L' ≤ countActiveKindAt kindIsFeedback t L)
    (h6 : countActiveKindAt kindIsMagicReq t L' ≤ countActiveKindAt kindIsMagicReq t L)
    (h7 : countActiveKindAt kindIsFreshAnc t L' ≤ countActiveKindAt kindIsFreshAnc t L)
    (h8 : countActiveKindAt kindIsTransit t L' ≤ countActiveKindAt kindIsTransit t L)
    (hL : op_cap_check_at opCap L t = true) :
    op_cap_check_at opCap L' t = true := by
  unfold op_cap_check_at at hL ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hL ⊢
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
    first
      | exact Nat.le_trans h1 hL.1.1.1.1.1.1.1
      | exact Nat.le_trans h2 hL.1.1.1.1.1.1.2
      | exact Nat.le_trans h3 hL.1.1.1.1.1.2
      | exact Nat.le_trans h4 hL.1.1.1.1.2
      | exact Nat.le_trans h5 hL.1.1.1.2
      | exact Nat.le_trans h6 hL.1.1.2
      | exact Nat.le_trans h7 hL.1.2
      | exact Nat.le_trans h8 hL.2

/-! ### §13.a.17 Shift invariance of `op_cap_check_at`. -/

private theorem op_cap_check_at_shiftSchedule
    (opCap : OperationCapacityModel) (xs : List SysCall) (t dt : Nat) :
    op_cap_check_at opCap (shiftSchedule dt xs) (t + dt)
      = op_cap_check_at opCap xs t := by
  unfold op_cap_check_at
  rw [countActiveKindAt_shiftSchedule, countActiveKindAt_shiftSchedule,
      countActiveKindAt_shiftSchedule, countActiveKindAt_shiftSchedule,
      countActiveKindAt_shiftSchedule, countActiveKindAt_shiftSchedule,
      countActiveKindAt_shiftSchedule, countActiveKindAt_shiftSchedule]

/-! ### §13.a.18 `operation_capacity_ok_shiftSchedule_eq`. -/

theorem operation_capacity_ok_shiftSchedule_eq
    (opCap : OperationCapacityModel) (dt : Nat) (xs : List SysCall) :
    operation_capacity_ok opCap (shiftSchedule dt xs)
      = operation_capacity_ok opCap xs := by
  rw [operation_capacity_ok_eq, operation_capacity_ok_eq]
  show ((shiftSchedule dt xs).map (·.begin_us)).all _
      = (xs.map (·.begin_us)).all _
  -- shifted event times = xs.map (·.begin_us + dt)
  have h_evt :
      (shiftSchedule dt xs).map (·.begin_us)
        = xs.map (fun sc => sc.begin_us + dt) := by
    unfold shiftSchedule
    rw [List.map_map]
    rfl
  rw [h_evt]
  rw [List.all_map, List.all_map]
  congr 1
  funext sc
  show op_cap_check_at opCap (shiftSchedule dt xs) (sc.begin_us + dt)
      = op_cap_check_at opCap xs sc.begin_us
  exact op_cap_check_at_shiftSchedule opCap xs sc.begin_us dt

/-! ### §13.a.19 `operation_capacity_ok_seqSchedules`. -/

theorem operation_capacity_ok_seqSchedules
    (opCap : OperationCapacityModel) (xs ys : List SysCall)
    (hxs : operation_capacity_ok opCap xs = true)
    (hys : operation_capacity_ok opCap ys = true)
    (hwithin : scheduleWithinWallclock xs = true) :
    operation_capacity_ok opCap (seqSchedules xs ys) = true := by
  show operation_capacity_ok opCap (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  rw [operation_capacity_ok_eq]
  show (scheduleEventTimes (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)).all _ = true
  have h_evt :
      scheduleEventTimes (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
        = xs.map (·.begin_us)
          ++ ys.map (fun sc => sc.begin_us + scheduleWallclockUs xs) := by
    show ((xs ++ shiftSchedule (scheduleWallclockUs xs) ys).map _) = _
    rw [List.map_append]
    congr 1
    unfold shiftSchedule
    rw [List.map_map]
    rfl
  rw [h_evt, List.all_append, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- Pre-W sample times: each t = sc.begin_us for sc ∈ xs, so t < W.
    rw [List.all_map]
    rw [List.all_eq_true]
    intro sc hsc
    have h_end : sc.end_us ≤ scheduleWallclockUs xs :=
      scheduleWithinWallclock_end_le xs sc hsc hwithin
    have h_begin_lt : sc.begin_us < sc.end_us :=
      scheduleWithinWallclock_begin_lt_end xs sc hsc hwithin
    have h_t_lt_W : sc.begin_us < scheduleWallclockUs xs := by omega
    -- counts in (xs ++ shifted ys) at sc.begin_us = counts in xs (since shifted ys has none here)
    have h_count_zero_each :
        ∀ pred, countActiveKindAt pred sc.begin_us
                  (shiftSchedule (scheduleWallclockUs xs) ys) = 0 :=
      fun pred =>
        countActiveKindAt_shiftSchedule_eq_zero_before_offset pred sc.begin_us
          (scheduleWallclockUs xs) ys h_t_lt_W
    have h_count_eq :
        ∀ pred, countActiveKindAt pred sc.begin_us
                  (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
                = countActiveKindAt pred sc.begin_us xs := by
      intro pred
      rw [countActiveKindAt_append, h_count_zero_each pred, Nat.add_zero]
    -- extract the per-time check at sc.begin_us from hxs
    have hxs_at :
        op_cap_check_at opCap xs sc.begin_us = true := by
      have hmem : sc.begin_us ∈ scheduleEventTimes xs :=
        List.mem_map.mpr ⟨sc, hsc, rfl⟩
      exact (List.all_eq_true.mp hxs) sc.begin_us hmem
    simp only [Function.comp]
    unfold op_cap_check_at
    simp only [h_count_eq]
    unfold op_cap_check_at at hxs_at
    exact hxs_at
  · -- Post-W sample times: each t' = sc.begin_us + W for sc ∈ ys, so t' ≥ W.
    rw [List.all_map]
    rw [List.all_eq_true]
    intro sc hsc
    have h_t_ge_W : scheduleWallclockUs xs ≤ sc.begin_us + scheduleWallclockUs xs := by omega
    -- counts in (xs ++ shifted ys) at sc.begin_us + W = counts in shifted ys (since xs has none here)
    have h_count_zero_each_xs :
        ∀ pred, countActiveKindAt pred (sc.begin_us + scheduleWallclockUs xs) xs = 0 :=
      fun pred =>
        countActiveKindAt_eq_zero_of_within_wallclock_at_or_after pred
          (sc.begin_us + scheduleWallclockUs xs) xs hwithin h_t_ge_W
    have h_count_eq :
        ∀ pred, countActiveKindAt pred (sc.begin_us + scheduleWallclockUs xs)
                  (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
                = countActiveKindAt pred sc.begin_us ys := by
      intro pred
      rw [countActiveKindAt_append, h_count_zero_each_xs pred, Nat.zero_add]
      exact countActiveKindAt_shiftSchedule pred sc.begin_us (scheduleWallclockUs xs) ys
    -- extract the per-time check at sc.begin_us from hys
    have hys_at :
        op_cap_check_at opCap ys sc.begin_us = true := by
      have hmem : sc.begin_us ∈ scheduleEventTimes ys :=
        List.mem_map.mpr ⟨sc, hsc, rfl⟩
      exact (List.all_eq_true.mp hys) sc.begin_us hmem
    simp only [Function.comp]
    unfold op_cap_check_at
    simp only [h_count_eq]
    unfold op_cap_check_at at hys_at
    exact hys_at

/-! ### §13.a.20 Repeated-block operation capacity. -/

theorem operation_capacity_ok_seqMany_replicate_block
    (opCap : OperationCapacityModel) (block : List SysCall) (n : Nat)
    (hblock : operation_capacity_ok opCap block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    operation_capacity_ok opCap (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show operation_capacity_ok opCap
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact operation_capacity_ok_seqSchedules opCap block _ hblock ih hwithin

/-! ### §13.a.21 Expanded-form headline for `operation_capacity_ok`. -/

theorem operation_capacity_ok_repeated_block_expand
    (opCap : OperationCapacityModel) (block : List SysCall) (n : Nat)
    (hblock : operation_capacity_ok opCap block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    operation_capacity_ok opCap
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact operation_capacity_ok_seqMany_replicate_block opCap block n hblock hwithin

/-! ### §13.a.22 `activeSitesAt` helpers.

    The sampled-time `slot_capacity_ok` checker builds on
    `activeSitesAt t sched`, the list of site claims by SysCalls
    active at time `t`.  Same four helpers as `countActiveKindAt`:
    append distribution, shift compensation, and the two
    out-of-window zero-list facts. -/

theorem activeSitesAt_append (t : Nat) (xs ys : List SysCall) :
    activeSitesAt t (xs ++ ys)
      = activeSitesAt t xs ++ activeSitesAt t ys := by
  unfold activeSitesAt
  rw [List.filter_append, List.flatMap_append]

theorem activeSitesAt_shiftSchedule (t dt : Nat) (xs : List SysCall) :
    activeSitesAt (t + dt) (shiftSchedule dt xs) = activeSitesAt t xs := by
  unfold activeSitesAt shiftSchedule
  rw [List.filter_map, List.flatMap_map]
  congr 1
  apply List.filter_congr
  intro sc _
  simp only [Function.comp]
  unfold syscallActiveAt
  rw [shiftSysCall_begin, shiftSysCall_end]
  have h1 : decide (sc.begin_us + dt ≤ t + dt) = decide (sc.begin_us ≤ t) := by
    have : (sc.begin_us + dt ≤ t + dt) ↔ (sc.begin_us ≤ t) := by omega
    simp [this]
  have h2 : decide (t + dt < sc.end_us + dt) = decide (t < sc.end_us) := by
    have : (t + dt < sc.end_us + dt) ↔ (t < sc.end_us) := by omega
    simp [this]
  rw [h1, h2]

theorem activeSitesAt_eq_nil_of_within_wallclock_at_or_after
    (t : Nat) (xs : List SysCall)
    (hwithin : scheduleWithinWallclock xs = true)
    (h : scheduleWallclockUs xs ≤ t) :
    activeSitesAt t xs = [] := by
  unfold activeSitesAt
  have hfilter : xs.filter (syscallActiveAt t) = [] := by
    rw [List.filter_eq_nil_iff]
    intro sc hsc
    have h_end_le : sc.end_us ≤ scheduleWallclockUs xs :=
      scheduleWithinWallclock_end_le xs sc hsc hwithin
    unfold syscallActiveAt
    have h_not : ¬ (t < sc.end_us) := by omega
    simp [h_not]
  rw [hfilter]
  rfl

theorem activeSitesAt_shiftSchedule_eq_nil_before_offset
    (t dt : Nat) (ys : List SysCall) (h : t < dt) :
    activeSitesAt t (shiftSchedule dt ys) = [] := by
  unfold activeSitesAt
  have hfilter : (shiftSchedule dt ys).filter (syscallActiveAt t) = [] := by
    rw [List.filter_eq_nil_iff]
    intro sc hsc
    have h_begin : dt ≤ sc.begin_us := shifted_begin_ge_offset dt ys sc hsc
    unfold syscallActiveAt
    have h_not : ¬ (sc.begin_us ≤ t) := by omega
    simp [h_not]
  rw [hfilter]
  rfl

/-! ### §13.a.23 `activeSiteCountInZoneAt` helpers.

    Derived from the `activeSitesAt` helpers via `.filter
    (siteInZoneSpec · z) |>.length`. -/

theorem activeSiteCountInZoneAt_append
    (z : ZoneCapacitySpec) (t : Nat) (xs ys : List SysCall) :
    activeSiteCountInZoneAt z t (xs ++ ys)
      = activeSiteCountInZoneAt z t xs + activeSiteCountInZoneAt z t ys := by
  unfold activeSiteCountInZoneAt
  rw [activeSitesAt_append, List.filter_append, List.length_append]

theorem activeSiteCountInZoneAt_shiftSchedule
    (z : ZoneCapacitySpec) (t dt : Nat) (xs : List SysCall) :
    activeSiteCountInZoneAt z (t + dt) (shiftSchedule dt xs)
      = activeSiteCountInZoneAt z t xs := by
  unfold activeSiteCountInZoneAt
  rw [activeSitesAt_shiftSchedule]

theorem activeSiteCountInZoneAt_eq_zero_of_within_wallclock_at_or_after
    (z : ZoneCapacitySpec) (t : Nat) (xs : List SysCall)
    (hwithin : scheduleWithinWallclock xs = true)
    (h : scheduleWallclockUs xs ≤ t) :
    activeSiteCountInZoneAt z t xs = 0 := by
  unfold activeSiteCountInZoneAt
  rw [activeSitesAt_eq_nil_of_within_wallclock_at_or_after t xs hwithin h]
  rfl

theorem activeSiteCountInZoneAt_shiftSchedule_eq_zero_before_offset
    (z : ZoneCapacitySpec) (t dt : Nat) (ys : List SysCall)
    (h : t < dt) :
    activeSiteCountInZoneAt z t (shiftSchedule dt ys) = 0 := by
  unfold activeSiteCountInZoneAt
  rw [activeSitesAt_shiftSchedule_eq_nil_before_offset t dt ys h]
  rfl

/-! ### §13.a.24 Per-time slot-capacity check abstraction. -/

private def slot_cap_check_at (slotCap : SlotCapacityModel)
    (L : List SysCall) (t : Nat) : Bool :=
  slotCap.zones.all fun z =>
    decide (activeSiteCountInZoneAt z t L ≤ z.slot_capacity)

private theorem slot_capacity_ok_eq
    (slotCap : SlotCapacityModel) (L : List SysCall) :
    slot_capacity_ok slotCap L
      = (scheduleEventTimes L).all (slot_cap_check_at slotCap L) := rfl

/-! ### §13.a.25 Shift invariance of `slot_cap_check_at`. -/

private theorem slot_cap_check_at_shiftSchedule
    (slotCap : SlotCapacityModel) (xs : List SysCall) (t dt : Nat) :
    slot_cap_check_at slotCap (shiftSchedule dt xs) (t + dt)
      = slot_cap_check_at slotCap xs t := by
  unfold slot_cap_check_at
  refine List.all_congr rfl ?_
  intro z
  rw [activeSiteCountInZoneAt_shiftSchedule]

/-! ### §13.a.26 `slot_capacity_ok_shiftSchedule_eq`. -/

theorem slot_capacity_ok_shiftSchedule_eq
    (slotCap : SlotCapacityModel) (dt : Nat) (xs : List SysCall) :
    slot_capacity_ok slotCap (shiftSchedule dt xs)
      = slot_capacity_ok slotCap xs := by
  rw [slot_capacity_ok_eq, slot_capacity_ok_eq]
  show ((shiftSchedule dt xs).map (·.begin_us)).all _
      = (xs.map (·.begin_us)).all _
  have h_evt :
      (shiftSchedule dt xs).map (·.begin_us)
        = xs.map (fun sc => sc.begin_us + dt) := by
    unfold shiftSchedule
    rw [List.map_map]
    rfl
  rw [h_evt]
  rw [List.all_map, List.all_map]
  congr 1
  funext sc
  show slot_cap_check_at slotCap (shiftSchedule dt xs) (sc.begin_us + dt)
      = slot_cap_check_at slotCap xs sc.begin_us
  exact slot_cap_check_at_shiftSchedule slotCap xs sc.begin_us dt

/-! ### §13.a.27 `slot_capacity_ok_seqSchedules`. -/

theorem slot_capacity_ok_seqSchedules
    (slotCap : SlotCapacityModel) (xs ys : List SysCall)
    (hxs : slot_capacity_ok slotCap xs = true)
    (hys : slot_capacity_ok slotCap ys = true)
    (hwithin : scheduleWithinWallclock xs = true) :
    slot_capacity_ok slotCap (seqSchedules xs ys) = true := by
  show slot_capacity_ok slotCap (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  rw [slot_capacity_ok_eq]
  show (scheduleEventTimes (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)).all _ = true
  have h_evt :
      scheduleEventTimes (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
        = xs.map (·.begin_us)
          ++ ys.map (fun sc => sc.begin_us + scheduleWallclockUs xs) := by
    show ((xs ++ shiftSchedule (scheduleWallclockUs xs) ys).map _) = _
    rw [List.map_append]
    congr 1
    unfold shiftSchedule
    rw [List.map_map]
    rfl
  rw [h_evt, List.all_append, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- Pre-W sample times.
    rw [List.all_map]
    rw [List.all_eq_true]
    intro sc hsc
    have h_end : sc.end_us ≤ scheduleWallclockUs xs :=
      scheduleWithinWallclock_end_le xs sc hsc hwithin
    have h_begin_lt : sc.begin_us < sc.end_us :=
      scheduleWithinWallclock_begin_lt_end xs sc hsc hwithin
    have h_t_lt_W : sc.begin_us < scheduleWallclockUs xs := by omega
    have h_count_eq :
        ∀ z, activeSiteCountInZoneAt z sc.begin_us
                  (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
                = activeSiteCountInZoneAt z sc.begin_us xs := by
      intro z
      rw [activeSiteCountInZoneAt_append,
          activeSiteCountInZoneAt_shiftSchedule_eq_zero_before_offset z
            sc.begin_us (scheduleWallclockUs xs) ys h_t_lt_W,
          Nat.add_zero]
    have hxs_at : slot_cap_check_at slotCap xs sc.begin_us = true := by
      have hmem : sc.begin_us ∈ scheduleEventTimes xs :=
        List.mem_map.mpr ⟨sc, hsc, rfl⟩
      exact (List.all_eq_true.mp hxs) sc.begin_us hmem
    simp only [Function.comp]
    unfold slot_cap_check_at
    rw [List.all_eq_true]
    intro z hz
    rw [h_count_eq z]
    unfold slot_cap_check_at at hxs_at
    exact (List.all_eq_true.mp hxs_at) z hz
  · -- Post-W sample times.
    rw [List.all_map]
    rw [List.all_eq_true]
    intro sc hsc
    have h_t_ge_W :
        scheduleWallclockUs xs ≤ sc.begin_us + scheduleWallclockUs xs := by omega
    have h_count_eq :
        ∀ z, activeSiteCountInZoneAt z (sc.begin_us + scheduleWallclockUs xs)
                  (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
                = activeSiteCountInZoneAt z sc.begin_us ys := by
      intro z
      rw [activeSiteCountInZoneAt_append,
          activeSiteCountInZoneAt_eq_zero_of_within_wallclock_at_or_after z
            (sc.begin_us + scheduleWallclockUs xs) xs hwithin h_t_ge_W,
          Nat.zero_add]
      exact activeSiteCountInZoneAt_shiftSchedule z sc.begin_us
        (scheduleWallclockUs xs) ys
    have hys_at : slot_cap_check_at slotCap ys sc.begin_us = true := by
      have hmem : sc.begin_us ∈ scheduleEventTimes ys :=
        List.mem_map.mpr ⟨sc, hsc, rfl⟩
      exact (List.all_eq_true.mp hys) sc.begin_us hmem
    simp only [Function.comp]
    unfold slot_cap_check_at
    rw [List.all_eq_true]
    intro z hz
    rw [h_count_eq z]
    unfold slot_cap_check_at at hys_at
    exact (List.all_eq_true.mp hys_at) z hz

/-! ### §13.a.28 Repeated-block slot capacity. -/

theorem slot_capacity_ok_seqMany_replicate_block
    (slotCap : SlotCapacityModel) (block : List SysCall) (n : Nat)
    (hblock : slot_capacity_ok slotCap block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    slot_capacity_ok slotCap (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show slot_capacity_ok slotCap
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact slot_capacity_ok_seqSchedules slotCap block _ hblock ih hwithin

/-! ### §13.a.29 Expanded-form headline for `slot_capacity_ok`. -/

theorem slot_capacity_ok_repeated_block_expand
    (slotCap : SlotCapacityModel) (block : List SysCall) (n : Nat)
    (hblock : slot_capacity_ok slotCap block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    slot_capacity_ok slotCap
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact slot_capacity_ok_seqMany_replicate_block slotCap block n hblock hwithin

end FormalRV.System.CompressedRepeatSoundness
