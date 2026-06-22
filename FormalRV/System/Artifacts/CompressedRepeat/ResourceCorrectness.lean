/-
  FormalRV.System.Artifacts.CompressedRepeat.ResourceCorrectness —
  **the symbolic resource evaluator is CORRECT against the canonical
  counters on the expansion**, for EVERY CompressedSchedule (atoms, seq,
  par, rep — arbitrarily nested):

      cs.resource = resourceOfSysCalls cs.expand

  This closes the audited gap "no parametric count=expand theorem": the
  10⁹-op headline ("Lean re-derives the claimed numbers symbolically")
  now rests on a proof that the symbolic numbers equal THE canonical
  `Resource/SysCallCount` walks over the materialized schedule — for any
  n, any nesting — not on an n=3 spot check.
-/
import FormalRV.System.Artifacts.CompressedSchedule
import FormalRV.Resource.SysCallCountLaws

namespace FormalRV.System.CompressedScheduleResource

open FormalRV.System.Architecture
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.LayeredArtifactInterface
open FormalRV.Resource.SysCallCount
open FormalRV.System.LayeredArtifactInterface.CompressedResourceSummary

/-! ## §1. The summary is a homomorphism for seq/par composition -/

theorem resourceOfSysCalls_nil :
    resourceOfSysCalls [] = CompressedResourceSummary.zero := rfl

theorem resourceOfSysCalls_seqSchedules (xs ys : List SysCall) :
    resourceOfSysCalls (seqSchedules xs ys)
      = seqCombine (resourceOfSysCalls xs) (resourceOfSysCalls ys) := by
  unfold resourceOfSysCalls seqCombine
  simp only [CompressedResourceSummary.mk.injEq]
  exact ⟨wallclockUs_seqSchedules xs ys,
         opCountS_seqSchedules xs ys,
         countWhere_seqSchedules _ xs ys,
         countWhere_seqSchedules _ xs ys,
         countWhere_seqSchedules _ xs ys,
         countWhere_seqSchedules _ xs ys,
         countWhere_seqSchedules _ xs ys,
         countWhere_seqSchedules _ xs ys⟩

theorem resourceOfSysCalls_parSchedules (xs ys : List SysCall) :
    resourceOfSysCalls (parSchedules xs ys)
      = parCombine (resourceOfSysCalls xs) (resourceOfSysCalls ys) := by
  unfold resourceOfSysCalls parCombine
  simp only [CompressedResourceSummary.mk.injEq]
  exact ⟨wallclockUs_parSchedules xs ys,
         opCountS_parSchedules xs ys,
         countWhere_parSchedules _ xs ys,
         countWhere_parSchedules _ xs ys,
         countWhere_parSchedules _ xs ys,
         countWhere_parSchedules _ xs ys,
         countWhere_parSchedules _ xs ys,
         countWhere_parSchedules _ xs ys⟩

/-! ## §2. Fold forms for the n-ary combinators -/

theorem resourceOfSysCalls_seqMany (ls : List (List SysCall)) :
    resourceOfSysCalls (seqManySchedules ls)
      = (ls.map resourceOfSysCalls).foldr seqCombine zero := by
  induction ls with
  | nil => rfl
  | cons xs rest ih =>
      rw [seqManySchedules, resourceOfSysCalls_seqSchedules, ih]
      rfl

theorem resourceOfSysCalls_parMany (ls : List (List SysCall)) :
    resourceOfSysCalls (parManySchedules ls)
      = (ls.map resourceOfSysCalls).foldr parCombine zero := by
  induction ls with
  | nil => rfl
  | cons xs rest ih =>
      rw [parManySchedules, resourceOfSysCalls_parSchedules, ih]
      rfl

/-- `scale` is iterated `seqCombine` (field-wise `(n+1)·x = x + n·x`). -/
theorem scale_succ (n : Nat) (r : CompressedResourceSummary) :
    scale (n + 1) r = seqCombine r (scale n r) := by
  simp [scale, seqCombine, Nat.succ_mul, Nat.add_comm]

theorem foldr_seqCombine_replicate (n : Nat) (r : CompressedResourceSummary) :
    (List.replicate n r).foldr seqCombine zero = scale n r := by
  induction n with
  | zero => simp [scale, zero]
  | succ m ih => rw [List.replicate_succ, List.foldr_cons, ih, ← scale_succ]

/-! ## §3. THE correctness theorem -/

/-- **`CompressedSchedule.resource` = the canonical counters on the
    expansion** — for every schedule shape, every nesting, every `n`. -/
theorem resource_eq_expand :
    (cs : CompressedSchedule) →
      cs.resource = resourceOfSysCalls cs.expand
  | .atom xs => by
      rw [CompressedSchedule.resource, expand_atom]
  | .seq blocks => by
      rw [CompressedSchedule.resource, CompressedSchedule.expand,
          resourceOfSysCalls_seqMany, List.map_map]
      congr 1
      exact List.map_congr_left fun c _ => resource_eq_expand c
  | .par blocks => by
      rw [CompressedSchedule.resource, CompressedSchedule.expand,
          resourceOfSysCalls_parMany, List.map_map]
      congr 1
      exact List.map_congr_left fun c _ => resource_eq_expand c
  | .rep n body => by
      rw [CompressedSchedule.resource, CompressedSchedule.expand,
          resourceOfSysCalls_seqMany, List.map_replicate,
          foldr_seqCombine_replicate, resource_eq_expand body]

/-! ## §4. Headline corollaries in canonical-counter terms -/

theorem resource_wallclock_eq (cs : CompressedSchedule) :
    cs.resource.wallclock_us = wallclockUs cs.expand := by
  rw [resource_eq_expand]; rfl

theorem resource_syscall_count_eq (cs : CompressedSchedule) :
    cs.resource.syscall_count = opCountS cs.expand := by
  rw [resource_eq_expand]; rfl

theorem resource_gate2q_eq (cs : CompressedSchedule) :
    cs.resource.gate2q_count = countGate2q cs.expand := by
  rw [resource_eq_expand]; rfl

theorem resource_magic_req_eq (cs : CompressedSchedule) :
    cs.resource.magic_req_count = countMagicReq cs.expand := by
  rw [resource_eq_expand]; rfl

end FormalRV.System.CompressedScheduleResource
