/-
  seqSchedules / replicate / expanded-repeat chains for the remaining
  strict-bundle conjuncts: `capacity_in_arch_ok`,
  `feedback_latency_ok`, `decoder_react_ok` (per-syscall, immediate
  from the ShiftInvariance lemmas plus `List.all_append`);
  `window_throughput_ok` (vacuous on magic-free blocks, with the
  magic-count bookkeeping under append/shift/replicate); and the
  sampled-time `capacity_per_cycle_ok` (via the CapacitySeq
  `activeSitesAt` helpers).  No `sorry`, no custom `axiom`.
-/

import FormalRV.System.Artifacts.LayeredArtifactInterface
import FormalRV.System.Artifacts.CompressedRepeat.ShiftInvariance
import FormalRV.System.Artifacts.CompressedRepeat.CapacitySeq

namespace FormalRV.System.CompressedRepeatSoundness

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.AdderSystem
open FormalRV.System.LayeredArtifactInterface

/-! ### §13.a.30 `capacity_in_arch_ok` chain.

    Per-syscall predicate.  The shift-equality lemma in §2
    plus `List.all_append` give an immediate full chain. -/

theorem capacity_in_arch_ok_seqSchedules
    (arch : ZonedArch) (xs ys : List SysCall)
    (hxs : capacity_in_arch_ok arch xs = true)
    (hys : capacity_in_arch_ok arch ys = true) :
    capacity_in_arch_ok arch (seqSchedules xs ys) = true := by
  show capacity_in_arch_ok arch (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  unfold capacity_in_arch_ok
  rw [List.all_append]
  rw [show xs.all _ = capacity_in_arch_ok arch xs from rfl,
      show (shiftSchedule (scheduleWallclockUs xs) ys).all _
            = capacity_in_arch_ok arch (shiftSchedule (scheduleWallclockUs xs) ys) from rfl]
  rw [capacity_in_arch_ok_shiftSchedule]
  simp [hxs, hys]

theorem capacity_in_arch_ok_seqMany_replicate_block
    (arch : ZonedArch) (block : List SysCall) (n : Nat)
    (hblock : capacity_in_arch_ok arch block = true) :
    capacity_in_arch_ok arch
        (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show capacity_in_arch_ok arch
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact capacity_in_arch_ok_seqSchedules arch block _ hblock ih

theorem capacity_in_arch_ok_repeated_block_expand
    (arch : ZonedArch) (block : List SysCall) (n : Nat)
    (hblock : capacity_in_arch_ok arch block = true) :
    capacity_in_arch_ok arch
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact capacity_in_arch_ok_seqMany_replicate_block arch block n hblock

/-! ### §13.a.31 `feedback_latency_ok` chain.

    Per-syscall predicate; shift-equality in §3. -/

theorem feedback_latency_ok_seqSchedules
    (t_cycle_us : Nat) (xs ys : List SysCall)
    (hxs : feedback_latency_ok t_cycle_us xs = true)
    (hys : feedback_latency_ok t_cycle_us ys = true) :
    feedback_latency_ok t_cycle_us (seqSchedules xs ys) = true := by
  show feedback_latency_ok t_cycle_us
        (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  unfold feedback_latency_ok
  rw [List.all_append]
  rw [show xs.all _ = feedback_latency_ok t_cycle_us xs from rfl,
      show (shiftSchedule (scheduleWallclockUs xs) ys).all _
            = feedback_latency_ok t_cycle_us
                (shiftSchedule (scheduleWallclockUs xs) ys) from rfl]
  rw [feedback_latency_ok_shiftSchedule]
  simp [hxs, hys]

theorem feedback_latency_ok_seqMany_replicate_block
    (t_cycle_us : Nat) (block : List SysCall) (n : Nat)
    (hblock : feedback_latency_ok t_cycle_us block = true) :
    feedback_latency_ok t_cycle_us
        (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show feedback_latency_ok t_cycle_us
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact feedback_latency_ok_seqSchedules t_cycle_us block _ hblock ih

theorem feedback_latency_ok_repeated_block_expand
    (t_cycle_us : Nat) (block : List SysCall) (n : Nat)
    (hblock : feedback_latency_ok t_cycle_us block = true) :
    feedback_latency_ok t_cycle_us
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact feedback_latency_ok_seqMany_replicate_block t_cycle_us block n hblock

/-! ### §13.a.32 `decoder_react_ok` chain.

    Per-syscall predicate; shift-equality in §4. -/

theorem decoder_react_ok_seqSchedules
    (t_react_us : Nat) (xs ys : List SysCall)
    (hxs : decoder_react_ok t_react_us xs = true)
    (hys : decoder_react_ok t_react_us ys = true) :
    decoder_react_ok t_react_us (seqSchedules xs ys) = true := by
  show decoder_react_ok t_react_us
        (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  unfold decoder_react_ok
  rw [List.all_append]
  rw [show xs.all _ = decoder_react_ok t_react_us xs from rfl,
      show (shiftSchedule (scheduleWallclockUs xs) ys).all _
            = decoder_react_ok t_react_us
                (shiftSchedule (scheduleWallclockUs xs) ys) from rfl]
  rw [decoder_react_ok_shiftSchedule]
  simp [hxs, hys]

theorem decoder_react_ok_seqMany_replicate_block
    (t_react_us : Nat) (block : List SysCall) (n : Nat)
    (hblock : decoder_react_ok t_react_us block = true) :
    decoder_react_ok t_react_us
        (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show decoder_react_ok t_react_us
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact decoder_react_ok_seqSchedules t_react_us block _ hblock ih

theorem decoder_react_ok_repeated_block_expand
    (t_react_us : Nat) (block : List SysCall) (n : Nat)
    (hblock : decoder_react_ok t_react_us block = true) :
    decoder_react_ok t_react_us
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact decoder_react_ok_seqMany_replicate_block t_react_us block n hblock

/-! ### §13.a.33 `window_throughput_ok` chain — vacuous on
       magic-free bodies.

    `repeat_safe_block_ok` requires the body to contain NO
    `RequestMagicState` syscalls.  Append and shift both
    preserve "zero magic SysCalls", so the expanded block is
    also magic-free.  The `window_throughput_ok` filter then
    yields the empty list and `[].all _ = true`. -/

theorem magic_count_append (xs ys : List SysCall) :
    ((xs ++ ys).filter (fun sc => kindIsMagicReq sc.kind)).length
      = (xs.filter (fun sc => kindIsMagicReq sc.kind)).length
        + (ys.filter (fun sc => kindIsMagicReq sc.kind)).length := by
  rw [List.filter_append, List.length_append]

theorem magic_count_seqMany_replicate
    (block : List SysCall) (n : Nat)
    (h : (block.filter (fun sc => kindIsMagicReq sc.kind)).length = 0) :
    ((seqManySchedules (List.replicate n block)).filter
        (fun sc => kindIsMagicReq sc.kind)).length = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show ((seqSchedules block
              (seqManySchedules (List.replicate k block))).filter _).length = 0
      show ((block ++ shiftSchedule (scheduleWallclockUs block)
              (seqManySchedules (List.replicate k block))).filter _).length = 0
      rw [magic_count_append, magic_count_shiftSchedule, h, ih]

theorem magic_count_repeated_block_expand
    (block : List SysCall) (n : Nat)
    (h : (block.filter (fun sc => kindIsMagicReq sc.kind)).length = 0) :
    (((CompressedSchedule.rep n (CompressedSchedule.atom block)).expand).filter
        (fun sc => kindIsMagicReq sc.kind)).length = 0 := by
  rw [rep_atom_expand_eq]
  exact magic_count_seqMany_replicate block n h

theorem window_throughput_ok_of_no_magic
    (sched : List SysCall) (window_us max_per_window : Nat)
    (h : (sched.filter (fun sc => kindIsMagicReq sc.kind)).length = 0) :
    window_throughput_ok sched window_us max_per_window = true := by
  have hfilter :
      (sched.filter (fun sc =>
        match sc.kind with
        | .RequestMagicState _ => true
        | _                    => false)) = [] :=
    List.length_eq_zero_iff.mp h
  show ((sched.filter (fun sc =>
            match sc.kind with
            | .RequestMagicState _ => true
            | _                    => false)).map (·.begin_us)).all
          (fun t0 =>
            decide (magicReq_count_in_window sched t0 window_us ≤ max_per_window))
        = true
  rw [hfilter]
  rfl

/-! ### §13.a.34 `capacity_per_cycle_ok` chain.

    Sampled-time check with zone-load counts.  Same structure
    as `slot_capacity_ok` (uses `activeSitesAt` and a per-zone
    filter+count), but iterates over `arch.zones` (List
    ArchZone) with `z.contains_atom` and `z.capacity`. -/

private def cap_per_cycle_check_at
    (arch : ZonedArch) (L : List SysCall) (t : Nat) : Bool :=
  arch.zones.all (fun z =>
    decide (((activeSitesAt t L).filter z.contains_atom).length ≤ z.capacity))

private theorem capacity_per_cycle_ok_eq
    (arch : ZonedArch) (L : List SysCall) :
    capacity_per_cycle_ok arch L
      = (scheduleEventTimes L).all (cap_per_cycle_check_at arch L) := rfl

private theorem cap_per_cycle_check_at_shiftSchedule
    (arch : ZonedArch) (xs : List SysCall) (t dt : Nat) :
    cap_per_cycle_check_at arch (shiftSchedule dt xs) (t + dt)
      = cap_per_cycle_check_at arch xs t := by
  unfold cap_per_cycle_check_at
  refine List.all_congr rfl ?_
  intro z
  rw [activeSitesAt_shiftSchedule]

theorem capacity_per_cycle_ok_shiftSchedule_eq
    (arch : ZonedArch) (dt : Nat) (xs : List SysCall) :
    capacity_per_cycle_ok arch (shiftSchedule dt xs)
      = capacity_per_cycle_ok arch xs := by
  rw [capacity_per_cycle_ok_eq, capacity_per_cycle_ok_eq]
  show ((shiftSchedule dt xs).map (·.begin_us)).all _
      = (xs.map (·.begin_us)).all _
  have h_evt :
      (shiftSchedule dt xs).map (·.begin_us)
        = xs.map (fun sc => sc.begin_us + dt) := by
    unfold shiftSchedule
    rw [List.map_map]
    rfl
  rw [h_evt, List.all_map, List.all_map]
  congr 1
  funext sc
  show cap_per_cycle_check_at arch (shiftSchedule dt xs) (sc.begin_us + dt)
      = cap_per_cycle_check_at arch xs sc.begin_us
  exact cap_per_cycle_check_at_shiftSchedule arch xs sc.begin_us dt

theorem capacity_per_cycle_ok_seqSchedules
    (arch : ZonedArch) (xs ys : List SysCall)
    (hxs : capacity_per_cycle_ok arch xs = true)
    (hys : capacity_per_cycle_ok arch ys = true)
    (hwithin : scheduleWithinWallclock xs = true) :
    capacity_per_cycle_ok arch (seqSchedules xs ys) = true := by
  show capacity_per_cycle_ok arch
        (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  rw [capacity_per_cycle_ok_eq]
  show (scheduleEventTimes
          (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)).all _ = true
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
    have h_active_eq :
        activeSitesAt sc.begin_us
              (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
            = activeSitesAt sc.begin_us xs := by
      rw [activeSitesAt_append,
          activeSitesAt_shiftSchedule_eq_nil_before_offset sc.begin_us
            (scheduleWallclockUs xs) ys h_t_lt_W,
          List.append_nil]
    have hxs_at : cap_per_cycle_check_at arch xs sc.begin_us = true := by
      have hmem : sc.begin_us ∈ scheduleEventTimes xs :=
        List.mem_map.mpr ⟨sc, hsc, rfl⟩
      rw [capacity_per_cycle_ok_eq] at hxs
      exact (List.all_eq_true.mp hxs) sc.begin_us hmem
    simp only [Function.comp]
    unfold cap_per_cycle_check_at
    rw [List.all_eq_true]
    intro z hz
    rw [h_active_eq]
    unfold cap_per_cycle_check_at at hxs_at
    exact (List.all_eq_true.mp hxs_at) z hz
  · -- Post-W sample times.
    rw [List.all_map]
    rw [List.all_eq_true]
    intro sc hsc
    have h_t_ge_W :
        scheduleWallclockUs xs ≤ sc.begin_us + scheduleWallclockUs xs := by omega
    have h_active_eq :
        activeSitesAt (sc.begin_us + scheduleWallclockUs xs)
              (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
            = activeSitesAt sc.begin_us ys := by
      rw [activeSitesAt_append,
          activeSitesAt_eq_nil_of_within_wallclock_at_or_after
            (sc.begin_us + scheduleWallclockUs xs) xs hwithin h_t_ge_W,
          List.nil_append]
      exact activeSitesAt_shiftSchedule sc.begin_us
        (scheduleWallclockUs xs) ys
    have hys_at : cap_per_cycle_check_at arch ys sc.begin_us = true := by
      have hmem : sc.begin_us ∈ scheduleEventTimes ys :=
        List.mem_map.mpr ⟨sc, hsc, rfl⟩
      rw [capacity_per_cycle_ok_eq] at hys
      exact (List.all_eq_true.mp hys) sc.begin_us hmem
    simp only [Function.comp]
    unfold cap_per_cycle_check_at
    rw [List.all_eq_true]
    intro z hz
    rw [h_active_eq]
    unfold cap_per_cycle_check_at at hys_at
    exact (List.all_eq_true.mp hys_at) z hz

theorem capacity_per_cycle_ok_seqMany_replicate_block
    (arch : ZonedArch) (block : List SysCall) (n : Nat)
    (hblock : capacity_per_cycle_ok arch block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    capacity_per_cycle_ok arch
        (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show capacity_per_cycle_ok arch
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact capacity_per_cycle_ok_seqSchedules arch block _ hblock ih hwithin

theorem capacity_per_cycle_ok_repeated_block_expand
    (arch : ZonedArch) (block : List SysCall) (n : Nat)
    (hblock : capacity_per_cycle_ok arch block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    capacity_per_cycle_ok arch
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact capacity_per_cycle_ok_seqMany_replicate_block arch block n hblock hwithin

end FormalRV.System.CompressedRepeatSoundness
