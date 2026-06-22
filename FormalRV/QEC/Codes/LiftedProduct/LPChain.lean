/-
  FormalRV.QEC.Codes.LiftedProduct.LPChain — the lifted-product family's
  END-TO-END test case (see `../README.md` for the pipeline charter).

  The code: `lpTiny = liftedProduct 3 [[[0],[1]]] 1 2` — [[15, 3, d]]
  (3 logical qubits COMPUTED; d asserted 3, consumed only by the
  `3·τ_s ≥ 2d` bound with τ_s = 2).

  The paper-scale LP corpus (lp16/lp20/lp24, 2610–5278 columns) stays in
  `QEC/Instances.lean`: `well_shaped` is closed parametrically
  (`LPInstancesValid`, via `liftedProduct_well_shaped`), the `css_condition`
  at that scale is the documented open `LPCssCondition` programme.  This
  folder demonstrates the FULL chain on the family's kernel-checkable member.

  No Mathlib.  No `sorry`; no project axioms (kernel `decide` throughout).
-/

import FormalRV.QEC.LatticeSurgery.XSurgeryBuilder
import FormalRV.QEC.Circuit.CircuitSemantics
import FormalRV.QEC.Circuit.ExtractionCount
import FormalRV.QEC.LogicalFinder
import FormalRV.QEC.StabilizerCode
import FormalRV.QEC.LPInstancesValid

set_option maxRecDepth 16384

namespace FormalRV.QEC.Codes.LP

open FormalRV.QEC FormalRV.QEC.Circuit FormalRV.QEC.LogicalFinder
open FormalRV.QEC.Algebraic
open FormalRV.Framework FormalRV.Framework.LDPC FormalRV.Framework.PPMOp
open FormalRV.LatticeSurgery.SurfaceShorResourceCount

/-! ## 1. The code -/

theorem lpTiny_n : lpTiny.n = 15 := by decide
theorem lpTiny_well_shaped : lpTiny.well_shaped = true := by decide
theorem lpTiny_css : lpTiny.css_condition = true := by decide

theorem lpTiny_stabilizer_valid : lpTiny.toStabilizerCode.valid = true :=
  CSSCode.toStabilizerCode_valid lpTiny lpTiny_well_shaped lpTiny_css

/-- The paper-scale corpus: well-shapedness closed parametrically
    (re-exposed from `LPInstancesValid`). -/
theorem lp_corpus_well_shaped :
    FormalRV.QEC.Instances.lp16.well_shaped = true
    ∧ FormalRV.QEC.Instances.lp20.well_shaped = true
    ∧ FormalRV.QEC.Instances.lp24.well_shaped = true :=
  FormalRV.QEC.LPInstancesValid.lp_codes_well_shaped

/-! ## 2. Logical operators, COMPUTED -/

theorem lpTiny_k : numLogicals lpTiny = 3 := by decide
theorem lpTiny_lx_genuine : logicalX_genuine lpTiny = true := by decide
theorem lpTiny_lz_genuine : logicalZ_genuine lpTiny = true := by decide

/-- The first computed X-type logical (support `{2,3}`). -/
def lpTiny_lx : BoolVec := (logicalX lpTiny).getD 0 []

/-! ## 3. The logical operation: measure X̄ by lattice surgery -/

def lpTinyXSurgery : SurgeryGadget :=
  canonicalXSurgery (lpTiny.toQECCode 3 3) lpTiny_lx 2 8

theorem lpTinyXSurgery_verifies :
    SurgeryGadget.verify_surgery_gadget lpTinyXSurgery = true := by decide


/-- Per-vector certification of the EXACT logical the gadget consumes
    (legacy `logicalX_genuine` pattern, applied to the `getD 0` vector). -/
theorem lpTiny_lx_certified :
    (lpTiny.hz.all (fun r => ! gf2dot r lpTiny_lx)
      && ! inRowspace lpTiny.hx lpTiny_lx) = true := by decide

/-- The merged code as a `CSSCode` — the L5 leg mirroring
    `surface3_merged_syndrome_circuit_implements`: the merged checks form a
    VALID stabilizer code via the legacy `syndrome_circuit_implements_code`. -/
def lpTinyXSurgery_merged_css : FormalRV.QEC.CSSCode :=
  ⟨lpTinyXSurgery.merged_n, lpTinyXSurgery.merged_hx, lpTinyXSurgery.merged_hz⟩

theorem lpTinyXSurgery_merged_syndrome_valid :
    StabilizerState.valid lpTinyXSurgery_merged_css.toStabilizers lpTinyXSurgery_merged_css.n = true :=
  (FormalRV.QEC.CSSCode.syndrome_circuit_implements_code
    lpTinyXSurgery_merged_css (by decide)).mpr (by decide)

/-! ## 4. The compiled physical circuit and its semantics -/

theorem lpTiny_circuit_measures_merged :
    Round.measuredDataObs
        (lpTinyXSurgery.merged_n + lpTinyXSurgery.merged_hx.length
          + lpTinyXSurgery.merged_hz.length)
        lpTinyXSurgery.merged_n (SurgeryGadget.extractionRound lpTinyXSurgery)
      = FormalRV.Framework.SurgeryReadout.merged_stabilizers_X lpTinyXSurgery
        ++ FormalRV.Framework.SurgeryCorrect.merged_stabilizers_Z lpTinyXSurgery :=
  extractionRound_measures_merged lpTinyXSurgery (by decide) (by decide)

theorem lpTiny_circuit_readout (signs : List Bool)
    (hsig : signs.length = lpTinyXSurgery.merged_hx.length) :
    ((Round.measuredDataObs
        (lpTinyXSurgery.merged_n + lpTinyXSurgery.merged_hx.length
          + lpTinyXSurgery.merged_hz.length)
        lpTinyXSurgery.merged_n
        (SurgeryGadget.extractionRound lpTinyXSurgery)).take
          lpTinyXSurgery.merged_hx.length
      = FormalRV.Framework.SurgeryReadout.merged_stabilizers_X lpTinyXSurgery)
    ∧ FormalRV.Framework.SurgeryCorrect.selectedSignedProduct
        lpTinyXSurgery.span_witness lpTinyXSurgery.merged_hx signs
      = FormalRV.Framework.SurgeryCorrect.signedXRow
          (FormalRV.Framework.SurgeryCorrect.selectedParity
            lpTinyXSurgery.span_witness signs)
          lpTinyXSurgery.target_pauli :=
  extraction_measures_readout lpTinyXSurgery (by decide) signs
    (by decide) (by decide) hsig (by decide)

/-! ## 5. Independent resource counts — via the PARAMETRIC theorems -/

theorem lpTiny_circuit_width :
    FormalRV.Resource.widthC
        (Round.ops (SurgeryGadget.extractionRound lpTinyXSurgery)) = 30 := by
  rw [widthC_extractionRound lpTinyXSurgery (by decide) (by decide) (by decide)]
  decide

theorem lpTiny_circuit_cnots :
    FormalRV.Resource.cxCountC
        (Round.ops (SurgeryGadget.extractionRound lpTinyXSurgery)) = 40 := by
  rw [cxCountC_extractionRound]
  decide

theorem lpTiny_circuit_meas :
    FormalRV.Resource.measCountC
        (Round.ops (SurgeryGadget.extractionRound lpTinyXSurgery)) = 14 := by
  rw [measCountC_extractionRound]
  decide

/-! ## 6. Logical-cycle schedule -/

open FormalRV.QEC.Time

/-- Two parallel X̄-measurements on disjoint lpTiny blocks: 2 cycles, vs 4
    sequentially. -/
def lpTwoPPMpar : CycleSchedule :=
  .par (.op (.ppmVia lpTinyXSurgery 0)) (.op (.ppmVia lpTinyXSurgery 30))

theorem lp_par_wellFormed : lpTwoPPMpar.wellFormed = true := by decide
theorem lp_par_duration : lpTwoPPMpar.duration = 2 := by decide

end FormalRV.QEC.Codes.LP
