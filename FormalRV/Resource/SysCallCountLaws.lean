/-
  FormalRV.Resource.SysCallCountLaws — the counting ALGEBRA: how the
  canonical L4 counters (`SysCallCount`) behave under the schedule
  combinators (`shiftSchedule` / `seqSchedules` / `parSchedules`).

  These laws are what lets a composite schedule's resources be computed
  from its parts' WITHOUT expansion — they back the
  `CompressedSchedule.resource = resourceOfSysCalls ∘ expand` correctness
  theorem (`System/Artifacts/CompressedRepeat/ResourceCorrectness.lean`).
-/
import FormalRV.Resource.SysCallCount
import FormalRV.System.Core.ScheduleCombinators

namespace FormalRV.Resource.SysCallCount

open FormalRV.System.Architecture
open FormalRV.System.LatticeSurgeryPPMContract

/-! ## §1. Counts: invariant under shift, additive under seq/par -/

theorem countWhere_shift (p : SysCallKind → Bool) (dt : Nat)
    (xs : List SysCall) :
    countWhere p (shiftSchedule dt xs) = countWhere p xs := by
  simp [countWhere, shiftSchedule, shiftSysCall, List.filter_map,
        Function.comp_def]

theorem countWhere_seqSchedules (p : SysCallKind → Bool)
    (xs ys : List SysCall) :
    countWhere p (seqSchedules xs ys) = countWhere p xs + countWhere p ys := by
  rw [seqSchedules, countWhere_append, countWhere_shift]

theorem countWhere_parSchedules (p : SysCallKind → Bool)
    (xs ys : List SysCall) :
    countWhere p (parSchedules xs ys) = countWhere p xs + countWhere p ys := by
  rw [parSchedules, countWhere_append]

theorem opCountS_shift (dt : Nat) (xs : List SysCall) :
    opCountS (shiftSchedule dt xs) = opCountS xs := by
  simp [opCountS, shiftSchedule]

theorem opCountS_seqSchedules (xs ys : List SysCall) :
    opCountS (seqSchedules xs ys) = opCountS xs + opCountS ys := by
  simp [opCountS, seqSchedules, shiftSchedule]

theorem opCountS_parSchedules (xs ys : List SysCall) :
    opCountS (parSchedules xs ys) = opCountS xs + opCountS ys := by
  simp [opCountS, parSchedules]

/-! ## §2. Wallclock: max under par, sum under seq -/

private theorem max_add (a b d : Nat) :
    Nat.max (a + d) (b + d) = Nat.max a b + d := by
  unfold Nat.max
  omega

private theorem foldl_max_init (xs : List SysCall) :
    ∀ a, xs.foldl (fun acc sc => Nat.max acc sc.end_us) a
      = Nat.max a (wallclockUs xs) := by
  induction xs with
  | nil => intro a; simp [wallclockUs]
  | cons x rest ih =>
      intro a
      show rest.foldl _ (Nat.max a x.end_us) = _
      rw [ih (Nat.max a x.end_us)]
      have hr : wallclockUs (x :: rest)
          = Nat.max x.end_us (wallclockUs rest) := by
        show rest.foldl _ (Nat.max 0 x.end_us) = _
        rw [ih (Nat.max 0 x.end_us)]
        unfold Nat.max
        omega
      rw [hr]
      unfold Nat.max
      omega

theorem wallclockUs_append (xs ys : List SysCall) :
    wallclockUs (xs ++ ys) = Nat.max (wallclockUs xs) (wallclockUs ys) := by
  rw [wallclockUs, List.foldl_append]
  exact foldl_max_init ys (wallclockUs xs)

theorem wallclockUs_parSchedules (xs ys : List SysCall) :
    wallclockUs (parSchedules xs ys)
      = Nat.max (wallclockUs xs) (wallclockUs ys) :=
  wallclockUs_append xs ys

private theorem foldl_max_shift (dt : Nat) (xs : List SysCall) :
    ∀ a, (shiftSchedule dt xs).foldl (fun acc sc => Nat.max acc sc.end_us) (a + dt)
      = xs.foldl (fun acc sc => Nat.max acc sc.end_us) a + dt := by
  induction xs with
  | nil => intro a; rfl
  | cons x rest ih =>
      intro a
      show (shiftSchedule dt rest).foldl _ (Nat.max (a + dt) (x.end_us + dt)) = _
      rw [max_add, ih (Nat.max a x.end_us)]
      rfl

/-- Shifting a NONEMPTY schedule shifts its wallclock. -/
theorem wallclockUs_shift_of_ne_nil (dt : Nat) (xs : List SysCall)
    (h : xs ≠ []) : wallclockUs (shiftSchedule dt xs) = dt + wallclockUs xs := by
  cases xs with
  | nil => exact absurd rfl h
  | cons x rest =>
      show (shiftSchedule dt rest).foldl _ (Nat.max 0 (x.end_us + dt)) = _
      have h0 : Nat.max 0 (x.end_us + dt) = Nat.max 0 x.end_us + dt := by
        unfold Nat.max
        omega
      rw [h0, foldl_max_shift dt rest (Nat.max 0 x.end_us)]
      exact Nat.add_comm _ _

/-- **Wallclock is additive under sequential composition** (the case
    split handles the empty tail, whose shift contributes nothing). -/
theorem wallclockUs_seqSchedules (xs ys : List SysCall) :
    wallclockUs (seqSchedules xs ys) = wallclockUs xs + wallclockUs ys := by
  rw [seqSchedules, wallclockUs_append]
  cases ys with
  | nil => simp [shiftSchedule, wallclockUs]
  | cons y rest =>
      rw [wallclockUs_shift_of_ne_nil _ _ (by simp)]
      simp only [scheduleWallclockUs]
      unfold Nat.max
      omega

end FormalRV.Resource.SysCallCount
