/-
  FormalRV.System.Core.ScheduleCombinators — pure combinators over
  `List SysCall` schedules: `scheduleWallclockUs` (foldl max end_us),
  `shiftSysCall` / `shiftSchedule` (time translation), `seqSchedules` /
  `parSchedules` and their n-ary forms `seqManySchedules` /
  `parManySchedules`, with length and derived-wallclock lemmas.

  Extracted verbatim from `Compile/LatticeSurgeryPPMContract.lean` §16.
  Declarations stay in `namespace FormalRV.System.LatticeSurgeryPPMContract`
  to preserve fully-qualified names.  Depends only on `Core.Architecture`
  (for `SysCall`).  No Mathlib.
-/

import FormalRV.System.Core.Architecture
import FormalRV.Resource.SysCallCount

namespace FormalRV.System.LatticeSurgeryPPMContract

open FormalRV.System.Architecture

/-! ## §16. Composition layer: pure schedule operations

    Reusable combinators for SysCall schedules.  These are pure
    functions over `List SysCall`; the validator in §17 re-runs
    the strengthened bundle on the merged stream. -/

/-- Wallclock of a schedule = max `end_us` across all SysCalls — an
    alias for THE canonical counter (`Resource/SysCallCount.wallclockUs`);
    resource claims must never redefine their own walk. -/
abbrev scheduleWallclockUs : List SysCall → Nat :=
  FormalRV.Resource.SysCallCount.wallclockUs

/-- Shift a single SysCall forward in time by `dt` µs. -/
def shiftSysCall (dt : Nat) (sc : SysCall) : SysCall :=
  { sc with begin_us := sc.begin_us + dt
            end_us   := sc.end_us + dt }

/-- Shift every SysCall in a schedule forward by `dt` µs. -/
def shiftSchedule (dt : Nat) (xs : List SysCall) : List SysCall :=
  xs.map (shiftSysCall dt)

/-- Sequential composition: `xs ` followed by `ys` shifted by
    `wallclock(xs)`.  After the merge, `ys`'s SysCalls all begin
    at or after `xs`'s wallclock. -/
def seqSchedules (xs ys : List SysCall) : List SysCall :=
  xs ++ shiftSchedule (scheduleWallclockUs xs) ys

/-- Parallel composition: `xs` and `ys` both starting at their
    original times.  No time shift is applied; the merged
    schedule's validity must be RECHECKED (e.g., for ancilla
    aliasing or factory-port conflicts). -/
def parSchedules (xs ys : List SysCall) : List SysCall :=
  xs ++ ys

/-! ### §16.a Basic derived-resource lemmas -/


theorem shiftSchedule_length (dt : Nat) (xs : List SysCall) :
    (shiftSchedule dt xs).length = xs.length := by
  unfold shiftSchedule
  rw [List.length_map]

theorem seqSchedules_length (xs ys : List SysCall) :
    (seqSchedules xs ys).length = xs.length + ys.length := by
  unfold seqSchedules
  rw [List.length_append, shiftSchedule_length]

theorem parSchedules_length (xs ys : List SysCall) :
    (parSchedules xs ys).length = xs.length + ys.length := by
  unfold parSchedules
  rw [List.length_append]

/-- **Anti-spreadsheet (`rfl`)**: the wallclock of `seqSchedules`
    IS the foldl over the merged list — not a closed-form sum. -/
theorem seqSchedules_wallclock_is_derived (xs ys : List SysCall) :
    scheduleWallclockUs (seqSchedules xs ys)
      = (seqSchedules xs ys).foldl (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

/-- **Anti-spreadsheet (`rfl`)**: same for `parSchedules`. -/
theorem parSchedules_wallclock_is_derived (xs ys : List SysCall) :
    scheduleWallclockUs (parSchedules xs ys)
      = (parSchedules xs ys).foldl (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

/-! ### §16.b List-level composition for many schedules -/

/-- Sequential composition of many schedules, recursively shifted. -/
def seqManySchedules : List (List SysCall) → List SysCall
  | []         => []
  | xs :: rest => seqSchedules xs (seqManySchedules rest)

/-- Parallel composition of many schedules, all starting at t=0. -/
def parManySchedules : List (List SysCall) → List SysCall
  | []         => []
  | xs :: rest => parSchedules xs (parManySchedules rest)


/-- Singleton case for `seqManySchedules`: equals the input
    (shifted by 0, since the empty tail has wallclock 0). -/
theorem seqManySchedules_singleton (xs : List SysCall) :
    seqManySchedules [xs] = xs := by
  unfold seqManySchedules seqManySchedules seqSchedules
         shiftSchedule scheduleWallclockUs
  simp

/-- Singleton case for `parManySchedules`: equals the input. -/
theorem parManySchedules_singleton (xs : List SysCall) :
    parManySchedules [xs] = xs := by
  unfold parManySchedules parManySchedules parSchedules
  simp

end FormalRV.System.LatticeSurgeryPPMContract
