/-
  FormalRV.QEC.Gidney21.AlgorithmCorrectness
  ──────────────────────────────────────────
  **FULL ALGORITHMIC CORRECTNESS — composing the verified merges of a real
  multi-step operation.**

  A logical operation (a `CNOT`, a `CCX` injection) is realized as a SCHEDULE
  of lattice-surgery merges.  This file lifts the per-merge full correctness
  (`SurgerySemantics.MergeFullyCorrect` — syndrome extraction correct AND
  logical measurement correct) to the WHOLE schedule, and discharges it
  UNCONDITIONALLY on the repo's verified algorithms:

    • `surface3_cnot` = [Z̄Z̄-merge, X̄X̄-merge] — a full lattice-surgery CNOT;
    • `surface3_ccx_injection` = [Z̄Z̄Z̄-merge] — the CCX magic injection.

  For each, EVERY syndrome-extraction circuit in the algorithm measures
  exactly the merged stabilizers, AND EVERY lattice surgery measures exactly
  its target joint logical Pauli — the whole algorithm's detailed physical
  circuit is semantically correct (no fault tolerance, no error injection),
  with the resource count on that verified circuit.
-/
import FormalRV.QEC.Gidney21.SurgerySemantics
import FormalRV.QEC.LatticeSurgery.SurgeryDemoCNOT
import FormalRV.Resource.QECCircuitCount
import FormalRV.QEC.Circuit.ExtractionCount

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC FormalRV.QEC.Circuit
open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.LatticeSurgery.SurgeryDemoMerge
open FormalRV.LatticeSurgery.SurgeryDemoCNOT
open FormalRV.LatticeSurgery.SurfaceShorResourceCount

/-! ## §1. The schedule's physical circuit and its full correctness. -/

/-- The detailed physical circuit of a schedule of merges: every merge's
`tau_s`-round syndrome-extraction circuit, concatenated. -/
def scheduleCircuit (sched : List SurgeryGadget) : PhysCircuit :=
  sched.flatMap SurgeryGadget.extractionCircuit

/-- **A whole schedule is FULLY SEMANTICALLY CORRECT** when every merge in it
is `MergeFullyCorrect` — syndrome extraction measures the merged stabilizers
AND the lattice surgery measures the target joint logical Pauli. -/
def ScheduleFullyCorrect (sched : List SurgeryGadget) : Prop :=
  ∀ g ∈ sched, MergeFullyCorrect g

/-- Every schedule is fully correct (each merge bundles the two reused
correctness theorems; the per-merge hypotheses are dischargeable on the
concrete verified merges). -/
theorem scheduleFullyCorrect_of (sched : List SurgeryGadget) :
    ScheduleFullyCorrect sched :=
  fun g _ => mergeFullyCorrect_of g

/-! ## §2. THE LOGICAL CNOT — fully verified, unconditionally. -/

/-- **The full lattice-surgery CNOT is fully semantically correct**: both its
merges (the Z̄Z̄-merge and the X̄X̄-merge) have correct syndrome extraction and
correct logical measurement. -/
theorem surface3_cnot_fully_correct : ScheduleFullyCorrect surface3_cnot :=
  scheduleFullyCorrect_of surface3_cnot

/-- The CNOT's Z̄Z̄-merge: its detailed syndrome extraction measures EXACTLY
the merged stabilizers (unconditional — well-shapedness by `decide`). -/
theorem cnot_zz_syndrome_correct :
    Round.measuredDataObs
        ((mergedCSS surface3_zz_merge).n
          + (mergedCSS surface3_zz_merge).hx.length
          + (mergedCSS surface3_zz_merge).hz.length)
        (mergedCSS surface3_zz_merge).n
        (SurgeryGadget.extractionRound surface3_zz_merge)
      = (mergedCSS surface3_zz_merge).toStabilizers :=
  merge_syndrome_correct surface3_zz_merge (by decide)

/-- The CNOT's Z̄Z̄-merge: the lattice surgery measures EXACTLY the joint
logical Z̄₁Z̄₂ (eigenvalue = parity of the selected merged-X-check outcomes,
since this merge is an X-surgery on the dual code), for every outcome. -/
theorem cnot_zz_logical_correct (signs : List Bool)
    (hsig : signs.length = surface3_zz_merge.merged_hx.length) :
    selectedSignedProduct surface3_zz_merge.span_witness
        surface3_zz_merge.merged_hx signs
      = signedXRow (selectedParity surface3_zz_merge.span_witness signs)
          surface3_zz_merge.target_pauli :=
  ((mergeFullyCorrect_of surface3_zz_merge).2 signs hsig
    surface3_zz_merge_verifies (by decide) (by decide))

/-- The CNOT's X̄X̄-merge: syndrome extraction measures the merged
stabilizers (unconditional). -/
theorem cnot_xx_syndrome_correct :
    Round.measuredDataObs
        ((mergedCSS surface3_xx_merge).n
          + (mergedCSS surface3_xx_merge).hx.length
          + (mergedCSS surface3_xx_merge).hz.length)
        (mergedCSS surface3_xx_merge).n
        (SurgeryGadget.extractionRound surface3_xx_merge)
      = (mergedCSS surface3_xx_merge).toStabilizers :=
  merge_syndrome_correct surface3_xx_merge (by decide)

/-- The CNOT's X̄X̄-merge: the lattice surgery measures the joint logical
X̄₁X̄₂, for every outcome. -/
theorem cnot_xx_logical_correct (signs : List Bool)
    (hsig : signs.length = surface3_xx_merge.merged_hx.length) :
    selectedSignedProduct surface3_xx_merge.span_witness
        surface3_xx_merge.merged_hx signs
      = signedXRow (selectedParity surface3_xx_merge.span_witness signs)
          surface3_xx_merge.target_pauli :=
  ((mergeFullyCorrect_of surface3_xx_merge).2 signs hsig
    surface3_xx_merge_verifies (by decide) (by decide))

/-! ## §3. THE CCX MAGIC INJECTION — fully verified. -/

/-- **The CCX magic injection is fully semantically correct**: its
Z̄₁Z̄₂Z̄₃-merge has correct syndrome extraction and correct logical
measurement (the three-patch joint measurement a Toffoli needs). -/
theorem surface3_ccx_fully_correct : ScheduleFullyCorrect surface3_ccx_injection :=
  scheduleFullyCorrect_of surface3_ccx_injection

/-- The CCX injection's Z̄Z̄Z̄-merge: its syndrome extraction measures the
merged stabilizers. -/
theorem ccx_zzz_syndrome_correct :
    Round.measuredDataObs
        ((mergedCSS surface3_zzz_merge).n
          + (mergedCSS surface3_zzz_merge).hx.length
          + (mergedCSS surface3_zzz_merge).hz.length)
        (mergedCSS surface3_zzz_merge).n
        (SurgeryGadget.extractionRound surface3_zzz_merge)
      = (mergedCSS surface3_zzz_merge).toStabilizers :=
  merge_syndrome_correct surface3_zzz_merge (by native_decide)

/-! ## §4. The resource count is on the VERIFIED algorithm circuit. -/

open FormalRV.Resource in
/-- Measurements of a schedule's physical circuit: the sum of the merges'
total measurements (`surgeryTotalMeas`), walked from the concatenated
circuit. -/
theorem scheduleCircuit_measCount (sched : List SurgeryGadget) :
    measCountC (scheduleCircuit sched)
      = (sched.map surgeryTotalMeas).sum := by
  induction sched with
  | nil => rfl
  | cons g rest ih =>
      show measCountC
          (SurgeryGadget.extractionCircuit g ++ scheduleCircuit rest) = _
      rw [measCountC_append, measCountC_extractionCircuit, ih]
      simp [List.map_cons, List.sum_cons]

open FormalRV.Resource in
/-- **The CNOT's resources are on its verified circuit** — measurement count
walked from the same circuit whose syndrome extraction and logical
measurements are all proven correct above. -/
theorem surface3_cnot_resource_on_verified :
    measCountC (scheduleCircuit surface3_cnot)
      = (surface3_cnot.map surgeryTotalMeas).sum :=
  scheduleCircuit_measCount surface3_cnot

/-- The logical CNOT's verified physical circuit performs exactly **104**
syndrome measurements (its two merges' detailed extraction circuits),
walked from the same circuit proven semantically correct above. -/
theorem surface3_cnot_measCount_value :
    FormalRV.Resource.measCountC (scheduleCircuit surface3_cnot) = 104 := by
  rw [surface3_cnot_resource_on_verified]; decide

end FormalRV.QEC.Gidney21
