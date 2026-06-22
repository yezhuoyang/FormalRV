/-
  FormalRV.Framework.SurgerySchedule — from ONE surgery to a WHOLE SCHEDULE.

  `SurgeryReduction` / `ZXStabilizer` proved that a SINGLE logical Pauli-product
  measurement, expressed in the ZX IR, runs as one surgery merge
  (`mergeZX_X_runs_as_surgery`).  A full fault-tolerant computation — e.g. Shor's
  modular exponentiation — is a SEQUENCE of such logical PPMs.  This module lifts
  the single-merge reduction to an arbitrary SCHEDULE (a list of surgery
  gadgets), proving that the composed ZX/PPM program of the whole schedule runs
  EXACTLY as the sequence of surgery merges on the stabilizer state:

      zxRun (scheduleProgramX sched) s = runScheduleX sched s.

  This is the operational core of the capstone's deferred contract "enumerate all
  of Shor's PPMs into one composed surface schedule" (`SurfaceShorPPMEndToEnd`),
  discharged at the stabilizer-state level for an arbitrary-length schedule.

  The proof rests on one new structural fact — `zxRun` distributes over diagram
  concatenation (`zxRun_append`) — plus the per-merge reduction, by induction on
  the schedule.  Both bases (X and Z) are covered.

  No Mathlib.  No `sorry`, no `axiom`.
-/

import FormalRV.PPM.Rules.ZXStabilizer

namespace FormalRV.Framework.SurgerySchedule

open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.Framework.SurgeryReadout
open FormalRV.Framework.SurgeryReduction
open FormalRV.Framework.StabProgram
open FormalRV.Framework.PPMOp
open FormalRV.Framework.ZX

/-! ## `zxRun` as a fold, and its distribution over concatenation -/

/-- The all-`+1` ZX run is the left fold of `apply_PPM_pos` over the measured
    Paulis — the same fold `measureChecks` uses. -/
theorem zxRun_eq_foldl (d : ZXDiagram) (s : StabilizerState) :
    zxRun d s = (d.map ZXSpider.toPauli).foldl (fun st P => apply_PPM_pos st P) s := by
  unfold zxRun zxToPPM
  have : d.map ZXSpider.toStabOp = (d.map ZXSpider.toPauli).map StabOp.meas := by
    rw [List.map_map]; rfl
  rw [this]
  exact runProgram_map_meas_nil _ s

/-- **`zxRun` distributes over diagram concatenation.**  Running `d₁ ++ d₂` is
    running `d₂` on the state produced by running `d₁` — sequential composition
    of PPM programs. -/
theorem zxRun_append (d1 d2 : ZXDiagram) (s : StabilizerState) :
    zxRun (d1 ++ d2) s = zxRun d2 (zxRun d1 s) := by
  rw [zxRun_eq_foldl, zxRun_eq_foldl, zxRun_eq_foldl, List.map_append, List.foldl_append]

/-! ## Surface-code schedules -/

/-- A surface-code lattice-surgery SCHEDULE: a list of surgery gadgets executed
    in order (each one logical Pauli-product measurement). -/
abbrev Schedule := List SurgeryGadget

/-- The whole schedule's composed ZX/PPM program: concatenate each gadget's
    X-merge diagram. -/
def scheduleProgramX (sched : Schedule) : ZXDiagram :=
  sched.flatMap mergeToZX_X

/-- The schedule's intended state map: apply each gadget's surgery merge
    (`measureChecks`) in order. -/
def runScheduleX (sched : Schedule) (s : StabilizerState) : StabilizerState :=
  sched.foldl (fun st g => measureChecks (merged_stabilizers_X g) st) s

/-- **WHOLE-SCHEDULE REDUCTION (X-type).**  The composed ZX/PPM program of an
    arbitrary-length surface-code schedule runs exactly as the sequence of
    surgery merges — many logical PPMs enumerated into one composed surface
    schedule, verified at the stabilizer-state level.  Axiom-free. -/
theorem schedule_runs_as_surgeries (sched : Schedule) (s : StabilizerState) :
    zxRun (scheduleProgramX sched) s = runScheduleX sched s := by
  induction sched generalizing s with
  | nil => rfl
  | cons g gs ih =>
    unfold scheduleProgramX runScheduleX
    rw [List.flatMap_cons, List.foldl_cons]
    rw [zxRun_append, mergeZX_X_runs_as_surgery]
    exact ih (measureChecks (merged_stabilizers_X g) s)

/-! ## Z-type dual -/

/-- The whole schedule's composed Z-merge program. -/
def scheduleProgramZ (sched : Schedule) : ZXDiagram :=
  sched.flatMap mergeToZX_Z

/-- The schedule's Z-merge state map. -/
def runScheduleZ (sched : Schedule) (s : StabilizerState) : StabilizerState :=
  sched.foldl (fun st g => measureChecks (merged_stabilizers_Z g) st) s

/-- **WHOLE-SCHEDULE REDUCTION (Z-type).** -/
theorem schedule_runs_as_surgeries_Z (sched : Schedule) (s : StabilizerState) :
    zxRun (scheduleProgramZ sched) s = runScheduleZ sched s := by
  induction sched generalizing s with
  | nil => rfl
  | cons g gs ih =>
    unfold scheduleProgramZ runScheduleZ
    rw [List.flatMap_cons, List.foldl_cons]
    rw [zxRun_append, mergeZX_Z_runs_as_surgery]
    exact ih (measureChecks (merged_stabilizers_Z g) s)

/-! ## Schedule resource aggregate (verified-schedule → total syndrome rounds)

    Tied to `SurfaceShorResourceCount`: the total number of syndrome rounds the
    whole VERIFIED schedule runs is the sum of the per-gadget `tau_s`. -/

/-- Total syndrome rounds of the schedule (sum of each merge's verified `tau_s`). -/
def scheduleTotalRounds (sched : Schedule) : Nat :=
  (sched.map (fun g => g.tau_s)).foldl (· + ·) 0

/-- A two-surgery schedule's rounds add: smoke that the aggregate composes. -/
example (g h : SurgeryGadget) :
    scheduleTotalRounds [g, h] = g.tau_s + h.tau_s := by
  simp [scheduleTotalRounds]

end FormalRV.Framework.SurgerySchedule
