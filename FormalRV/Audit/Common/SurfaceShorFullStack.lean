/-
  FormalRV.Audit.Common.SurfaceShorFullStack — the SCHEDULE-LEVEL capstone of Path A:
  a multi-PPM surface-code schedule of VERIFIED logical measurements, proven to
  reduce to its sequence of surgery merges, AND resource-counted.

  This upgrades `SurfaceShorPPMEndToEnd` (which realised ONE logical PPM on the
  surface code) to an ARBITRARY-LENGTH schedule, using the whole-schedule
  reduction `SurgerySchedule.schedule_runs_as_surgeries`.  It then attaches the
  post-verification resource count (`SurfaceShorResourceCount`): the schedule's
  TIME is the sum of the per-merge `tau_s` (`scheduleTotalRounds`, = n·tau_s for
  n PPMs), and its SPACE is the (reused) per-merge physical footprint.

  ## The L1→L4 stack, assembled
  * L1 (algorithm)  `shor_succeeds_with_ppm_realized_modmult`  — order finding
                    succeeds, modular-multiplier oracle observed correctly.
  * L2→L3 (PPM)     each logical operation is a Pauli-product measurement; a
                    schedule of them is `scheduleProgramX`.
  * L3→L4 (surgery) `schedule_runs_as_surgeries` — the schedule's PPM program runs
                    EXACTLY as the sequence of surface-code surgery merges, each
                    `surface3_x_surgery` structurally verified and measuring X̄.
  * resource        `scheduleTotalRounds` (time) + `surgeryPhysQubits` (space),
                    counted on the VERIFIED objects.

  ## Honesty boundary (unchanged from `SurfaceShorPPMEndToEnd`)
  `demoSchedule` is a CONCRETE length-3 schedule of verified logical-X̄ merges; it
  stands in for a prefix of Shor's actual PPM sequence (the reduction is
  gadget-general, so it applies once that sequence is enumerated — and the
  enumeration of every Shor PPM, with `teleportCCX` magic injection, remains the
  deferred contract).  Merged-code distance / FT and Gottesman–Knill
  Hilbert-space faithfulness also remain delimited there.

  No `sorry`, no new `axiom`.
-/

import FormalRV.Audit.Common.SurfaceShorResourceCount
import FormalRV.LatticeSurgery.SurgerySchedule

namespace FormalRV.Audit.Common.SurfaceShorFullStack

open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgerySchedule
open FormalRV.Framework.ZX
open FormalRV.Framework.PPMOp
open FormalRV.Audit.Common.SurgeryDemoSurface
open FormalRV.Audit.Common.SurfaceShorResourceCount

/-- A concrete surface-code SCHEDULE: a length-3 fragment of logical-X̄ PPMs on
    the verified [[13,1,3]] code.  Stands for a prefix of Shor's PPM sequence;
    the reduction below is gadget-general. -/
def demoSchedule : Schedule := List.replicate 3 surface3_x_surgery

/-- Every gadget in the schedule passes the structural verifier. -/
theorem demoSchedule_verified :
    demoSchedule.all (fun g => SurgeryGadget.verify_surgery_gadget g) = true := by decide

/-- **The whole schedule reduces to its surgery merges** (the multi-PPM
    enumeration, instantiated on the concrete schedule). -/
theorem demoSchedule_reduces (s : StabilizerState) :
    zxRun (scheduleProgramX demoSchedule) s = runScheduleX demoSchedule s :=
  schedule_runs_as_surgeries demoSchedule s

/-! ## Parametric resource law: time scales linearly in the number of PPMs -/

private theorem foldl_add_replicate (n acc c : Nat) :
    (List.replicate n c).foldl (· + ·) acc = acc + n * c := by
  induction n generalizing acc with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.foldl_cons, ih, Nat.add_mul, Nat.one_mul]; omega

/-- **Schedule time law.**  A schedule of `n` identical logical-PPM merges runs
    for `n · tau_s` syndrome rounds — the per-merge verified `tau_s` scaled by the
    number of PPMs. -/
theorem schedule_rounds_replicate (n : Nat) (g : SurgeryGadget) :
    scheduleTotalRounds (List.replicate n g) = n * g.tau_s := by
  unfold scheduleTotalRounds
  rw [List.map_replicate, foldl_add_replicate]
  simp

/-- The demo schedule's TIME: 3 PPMs × 2 rounds = 6 syndrome rounds. -/
theorem demoSchedule_total_rounds : scheduleTotalRounds demoSchedule = 6 := by decide

/-- The demo schedule's SPACE: the per-merge physical footprint, 28 qubits — the
    same patches are REUSED across the schedule (space is the max, not the sum;
    only time accumulates). -/
theorem demoSchedule_space : surgeryPhysQubits surface3_x_surgery = 28 :=
  surface3_phys_qubits

/-- **SCHEDULE-LEVEL CAPSTONE.**  A multi-PPM surface-code schedule of VERIFIED
    logical measurements (i) is structurally verified gadget-by-gadget, (ii)
    reduces operationally to its sequence of surgery merges, and (iii) is
    resource-counted — time `= n · tau_s = 6` rounds, space `= 28` (reused)
    physical qubits.  Composes with `shor_succeeds_with_ppm_realized_modmult`
    (L1) and `surface_shor_ppm_physically_realized` (per-surgery L3→L4) for the
    full stack. -/
theorem surface_schedule_full_stack (s : StabilizerState) :
    demoSchedule.all (fun g => SurgeryGadget.verify_surgery_gadget g) = true
    ∧ zxRun (scheduleProgramX demoSchedule) s = runScheduleX demoSchedule s
    ∧ scheduleTotalRounds demoSchedule = 6
    ∧ surgeryPhysQubits surface3_x_surgery = 28 :=
  ⟨demoSchedule_verified, demoSchedule_reduces s,
   demoSchedule_total_rounds, demoSchedule_space⟩

end FormalRV.Audit.Common.SurfaceShorFullStack
