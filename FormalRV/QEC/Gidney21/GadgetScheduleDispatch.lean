/-
  FormalRV.QEC.Gidney21.GadgetScheduleDispatch
  ────────────────────────────────────────────
  **(completeness step 3) Per-statement Pauli-type DISPATCH.**

  Replaces the uniform `replicate (rotatedXMerge …)` (which ignored each
  measurement's Pauli type) with a real dispatcher that routes EACH PPM
  measurement by its axis:

    • a PURE-X product (all factors `.x`)  ↦  `rotatedXMerge 27` ;
    • a PURE-Z product (all factors `.z`)  ↦  `rotatedZMerge 27` .

  Both targets are fully verified (`MergeFullyCorrect`), so any schedule built
  by the dispatcher is fully semantically correct — every syndrome extraction
  and every lattice surgery in it is correct, with the merge axis now
  determined by the actual measured Pauli.

  MIXED (joint X/Z in one statement) and Y products classify to `none` and are
  the documented next step (basis-change reduction); they are NOT silently
  routed to the wrong merge.
-/
import FormalRV.QEC.Gidney21.RotatedMerge
import FormalRV.QEC.Gidney21.AlgorithmCorrectness
import FormalRV.PPM.Syntax.Program

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC FormalRV.Framework.LDPC
open FormalRV.LatticeSurgery
open FormalRV.PPM.Prog

/-! ## §1. The supported pure measurement axes. -/

/-- The two pure logical-measurement axes a single lattice-surgery merge can
realize directly. -/
inductive MergeAxis where
  | xAxis | zAxis
  deriving DecidableEq, Repr

/-- **Classify a PPM measurement's Pauli product by axis**: all-`X` ⇒ X-axis,
all-`Z` ⇒ Z-axis, otherwise `none` (mixed or `Y` — needs the basis-change
reduction, not a direct merge).  The empty product is not a measurement. -/
def classifyAxis (P : PauliProduct) : Option MergeAxis :=
  if P.isEmpty then none
  else if P.all (fun f => f.kind == PKind.x) then some MergeAxis.xAxis
  else if P.all (fun f => f.kind == PKind.z) then some MergeAxis.zAxis
  else none

/-! ## §2. The dispatch to verified merges. -/

/-- **Dispatch an axis to its verified d=27 merge.** -/
def axisMerge : MergeAxis → SurgeryGadget
  | MergeAxis.xAxis => rotatedXMerge 27 18 40
  | MergeAxis.zAxis => rotatedZMerge 27 18 40

/-- **Each dispatched merge is fully semantically correct** — by case on the
axis, it is the verified X- or Z-merge. -/
theorem axisMerge_fully_correct (a : MergeAxis) : MergeFullyCorrect (axisMerge a) := by
  cases a with
  | xAxis => exact rotatedXMerge27_fully_correct
  | zAxis => exact rotatedZMerge27_fully_correct

/-! ## §3. The dispatched schedule and its full correctness. -/

/-- **The schedule built by dispatching a list of axes** to verified merges. -/
def axisSchedule (axes : List MergeAxis) : List SurgeryGadget :=
  axes.map axisMerge

/-- **The dispatched schedule is FULLY SEMANTICALLY CORRECT** — every merge,
chosen by the measured Pauli's axis, has correct syndrome extraction AND a
correct genuine-logical measurement. -/
theorem axisSchedule_fully_correct (axes : List MergeAxis) :
    ScheduleFullyCorrect (axisSchedule axes) := by
  intro g hg
  rw [axisSchedule, List.mem_map] at hg
  obtain ⟨a, _, rfl⟩ := hg
  exact axisMerge_fully_correct a

/-! ## §4. From a PPM program to a dispatched, verified schedule. -/

/-- The pure-axis classification of every measurement in a PPM program (the
ones a single merge realizes directly); mixed/`Y` measurements drop out. -/
def programAxes : PPMProg → List MergeAxis
  | [] => []
  | st :: rest =>
      (match st with
        | .measure _ P => (classifyAxis P).toList
        | _ => [])
      ++ programAxes rest

/-- **The verified merge schedule of a PPM program** — each pure measurement
routed to its correct-axis merge. -/
def programSchedule (prog : PPMProg) : List SurgeryGadget :=
  axisSchedule (programAxes prog)

/-- **A PPM program's dispatched physical schedule is fully semantically
correct** — every merge in it is verified, with its axis set by the actual
measured Pauli. -/
theorem programSchedule_fully_correct (prog : PPMProg) :
    ScheduleFullyCorrect (programSchedule prog) :=
  axisSchedule_fully_correct (programAxes prog)

/-! ## §5. Sanity: the dispatcher routes by axis. -/

example : classifyAxis [⟨0, .x⟩, ⟨1, .x⟩] = some MergeAxis.xAxis := by decide
example : classifyAxis [⟨0, .z⟩, ⟨2, .z⟩] = some MergeAxis.zAxis := by decide
example : classifyAxis [⟨0, .x⟩, ⟨1, .z⟩] = none := by decide   -- mixed → not routed
example : classifyAxis [⟨0, .y⟩] = none := by decide             -- Y → not routed

end FormalRV.QEC.Gidney21
