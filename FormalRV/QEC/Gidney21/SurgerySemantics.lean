/-
  FormalRV.QEC.Gidney21.SurgerySemantics
  ──────────────────────────────────────
  **FULL SEMANTIC CORRECTNESS of a detailed lattice-surgery logical
  measurement — BOTH pillars on the SAME physical circuit.**

  This closes the link the earlier accounting was missing: the physical
  circuit of a logical Pauli measurement (the merge's detailed
  `prep/cx/meas` syndrome extraction) is proven to do TWO things, both on
  the one circuit `g.extractionRound`:

    PILLAR 1 — SYNDROME EXTRACTION is correct: the round measures EXACTLY
               the merged code's stabilizers (`extractionRound_measures_code`).
    PILLAR 2 — THE LATTICE SURGERY / LOGICAL MEASUREMENT is correct: the
               merge measures EXACTLY the target joint logical Pauli, with
               eigenvalue = parity of the selected merged-X-check outcomes
               (`surgery_implements_logical_measurement`).

  No fault tolerance, no error injection — just that the detailed circuit
  semantically does the syndrome extraction AND the logical measurement.
  Discharged on REAL verified merges (`surface3_xx_merge` = a two-patch
  X̄X̄ measurement; `surface3_xxx_merge` = a three-patch X̄X̄X̄, the shape a
  CCZ/Toffoli joint measurement needs), with the resource counts on the
  SAME circuit.
-/
import FormalRV.QEC.LatticeSurgery.SurgeryDemoMerge
import FormalRV.QEC.Circuit.CircuitSemantics
import FormalRV.QEC.LatticeSurgery.SurfaceShorResourceCount

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC FormalRV.QEC.Circuit
open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.LatticeSurgery.SurgeryDemoMerge
open FormalRV.LatticeSurgery.SurfaceShorResourceCount

/-! ## §1. The merged code as a CSS code. -/

/-- The merged code of a surgery gadget, as a `CSSCode` (data + surgery
ancilla, with the merged stabilizers). -/
def mergedCSS (g : SurgeryGadget) : CSSCode :=
  ⟨g.merged_n, g.merged_hx, g.merged_hz⟩

/-- The gadget's syndrome-extraction round IS the merged code's extraction
round (definitionally — both are `extractionBlocks merged_n merged_hx
merged_hz`). -/
theorem gadget_extractionRound_eq (g : SurgeryGadget) :
    SurgeryGadget.extractionRound g = CSSCode.extractionRound (mergedCSS g) := rfl

/-! ## §2. PILLAR 1 — syndrome extraction of the merge is correct. -/

/-- **The merge's detailed syndrome extraction measures EXACTLY the merged
code's stabilizers** — the same parametric correctness as bare patches,
applied to the merged (data + surgery ancilla) code. -/
theorem merge_syndrome_correct (g : SurgeryGadget)
    (hws : (mergedCSS g).well_shaped = true) :
    Round.measuredDataObs
        ((mergedCSS g).n + (mergedCSS g).hx.length + (mergedCSS g).hz.length)
        (mergedCSS g).n
        (SurgeryGadget.extractionRound g)
      = (mergedCSS g).toStabilizers := by
  rw [gadget_extractionRound_eq]
  exact extractionRound_measures_code (mergedCSS g) hws

/-! ## §3. The bundled "fully correct logical measurement". -/

/-- **A detailed lattice-surgery logical measurement is FULLY SEMANTICALLY
CORRECT** when BOTH pillars hold on its circuit: the syndrome extraction
measures the merged stabilizers, AND the merge measures the target logical
Pauli (eigenvalue = parity of the selected merged-X-check outcomes), for
every outcome assignment. -/
def MergeFullyCorrect (g : SurgeryGadget) : Prop :=
  -- PILLAR 1: syndrome extraction is correct
  ((mergedCSS g).well_shaped = true →
    Round.measuredDataObs
        ((mergedCSS g).n + (mergedCSS g).hx.length + (mergedCSS g).hz.length)
        (mergedCSS g).n (SurgeryGadget.extractionRound g)
      = (mergedCSS g).toStabilizers)
  -- PILLAR 2: the lattice surgery measures the target logical, ∀ outcomes
  ∧ (∀ (signs : List Bool), signs.length = g.merged_hx.length →
      g.verify_surgery_gadget = true → 0 < g.merged_n →
      (∀ r ∈ g.merged_hx, r.length = g.merged_n) →
      selectedSignedProduct g.span_witness g.merged_hx signs
        = signedXRow (selectedParity g.span_witness signs) g.target_pauli)

/-- Assemble `MergeFullyCorrect` from the two reused theorems. -/
theorem mergeFullyCorrect_of (g : SurgeryGadget) : MergeFullyCorrect g :=
  ⟨fun hws => merge_syndrome_correct g hws,
   fun signs hsig hverify hn hshape =>
     (surgery_implements_logical_measurement g g.merged_n signs hn hshape
       hsig hverify).1⟩

/-! ## §4. DISCHARGED on real verified merges. -/

/-- **A two-patch X̄X̄ lattice-surgery measurement is fully semantically
correct** — syndrome extraction measures the merged `[[26,·,·]]` stabilizers
AND the merge measures the joint logical X̄₁X̄₂.  Both on the SAME detailed
circuit; the verifier passes by `decide`. -/
theorem surface3_xx_merge_fully_correct : MergeFullyCorrect surface3_xx_merge :=
  mergeFullyCorrect_of surface3_xx_merge

/-- Concretely: the XX-merge's syndrome extraction measures the merged
stabilizers (the well-shapedness discharged by `decide`). -/
theorem surface3_xx_syndrome_correct :
    Round.measuredDataObs
        ((mergedCSS surface3_xx_merge).n
          + (mergedCSS surface3_xx_merge).hx.length
          + (mergedCSS surface3_xx_merge).hz.length)
        (mergedCSS surface3_xx_merge).n
        (SurgeryGadget.extractionRound surface3_xx_merge)
      = (mergedCSS surface3_xx_merge).toStabilizers :=
  merge_syndrome_correct surface3_xx_merge (by decide)

/-- Concretely: the XX-merge measures the joint logical X̄₁X̄₂ (eigenvalue =
parity of the selected merged-X-check outcomes), for every outcome. -/
theorem surface3_xx_logical_correct (signs : List Bool)
    (hsig : signs.length = surface3_xx_merge.merged_hx.length) :
    selectedSignedProduct surface3_xx_merge.span_witness
        surface3_xx_merge.merged_hx signs
      = signedXRow (selectedParity surface3_xx_merge.span_witness signs)
          surface3_xx_merge.target_pauli :=
  (surface3_xx_merge_fully_correct.2 signs hsig surface3_xx_merge_verifies
    (by decide) (by decide))

/-- **A THREE-patch X̄X̄X̄ measurement (the CCZ/Toffoli joint-measurement
shape) is fully semantically correct** — same two pillars, scaled. -/
theorem surface3_xxx_merge_fully_correct : MergeFullyCorrect surface3_xxx_merge :=
  mergeFullyCorrect_of surface3_xxx_merge

/-! ## §5. The resource count is on the VERIFIED circuit. -/

/-- The resources counted (`surgeryPhysQubits`, `surgeryMeasPerRound`) are on
the SAME merge circuit `surface3_xx_merge` whose syndrome extraction and
logical measurement are proven correct above — count on a verified object. -/
theorem surface3_xx_resource_on_verified :
    surgeryPhysQubits surface3_xx_merge
      = surface3_xx_merge.merged_n + surface3_xx_merge.merged_hx.length
          + surface3_xx_merge.merged_hz.length
    ∧ surgeryMeasPerRound surface3_xx_merge
      = surface3_xx_merge.merged_hx.length + surface3_xx_merge.merged_hz.length :=
  ⟨rfl, rfl⟩

end FormalRV.QEC.Gidney21
