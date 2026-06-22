/-
  FormalRV.QEC.Codes.BivariateBicycle.BBChain — the bivariate-bicycle
  family's END-TO-END test case (see `../README.md` for the pipeline charter).

  The code: `bbSmall = bivariateBicycle 3 3 [(1,0),(0,1)] [(1,0),(0,2)]` —
  [[18, 2, d]] (2 logical qubits COMPUTED; d asserted 6, believed (family-level
  heuristic; instance distance unverified, and 3·τ_s ≥ 2d is TIGHT here), consumed only by the `3·τ_s ≥ 2d` bound with τ_s = 4).

  Cross-check: this gadget's 39 physical qubits is the figure the Audit layer
  states independently (`Audit/CainXu2026/SystemZones.lean`,
  `lpGadget_footprint = 39`) for its hand-built `bb_x_surgery` — here the
  gadget is built GENERICALLY from the computed logical support.

  No Mathlib.  No `sorry`; no project axioms (kernel `decide` throughout).
-/

import FormalRV.QEC.LatticeSurgery.XSurgeryBuilder
import FormalRV.QEC.Circuit.CircuitSemantics
import FormalRV.QEC.Circuit.ExtractionCount
import FormalRV.QEC.LogicalFinder
import FormalRV.QEC.StabilizerCode
import FormalRV.QEC.SmallCodeValidity

set_option maxRecDepth 16384

namespace FormalRV.QEC.Codes.BB

open FormalRV.QEC FormalRV.QEC.Circuit FormalRV.QEC.LogicalFinder
open FormalRV.Framework FormalRV.Framework.LDPC FormalRV.Framework.PPMOp
open FormalRV.LatticeSurgery.SurfaceShorResourceCount

/-! ## 1. The code -/

theorem bbSmall_n : bbSmall.n = 18 := by decide
theorem bbSmall_well_shaped : bbSmall.well_shaped = true := by decide
theorem bbSmall_css : bbSmall.css_condition = true :=
  FormalRV.QEC.bbSmall_is_CSS

theorem bbSmall_stabilizer_valid : bbSmall.toStabilizerCode.valid = true :=
  CSSCode.toStabilizerCode_valid bbSmall bbSmall_well_shaped bbSmall_css

/-! ## 2. Logical operators, COMPUTED — REUSED from `LogicalFinder`
    (no re-proof: these are the existing corpus theorems, cited) -/

theorem bbSmall_k : numLogicals bbSmall = 2 :=
  FormalRV.QEC.LogicalFinder.bbSmall_2_logical_qubits

theorem bbSmall_lx_genuine : logicalX_genuine bbSmall = true :=
  FormalRV.QEC.LogicalFinder.bbSmall_logicalX_genuine

theorem bbSmall_lz_genuine : logicalZ_genuine bbSmall = true :=
  FormalRV.QEC.LogicalFinder.bbSmall_logicalZ_genuine

/-- The first computed X-type logical (support `{1,5,6}`). -/
def bbSmall_lx : BoolVec := (logicalX bbSmall).getD 0 []

/-! ## 3. The logical operation: measure X̄ by lattice surgery -/

/-- X̄-measurement surgery on `bbSmall`, generic builder on the computed
    logical (d := 6 asserted ⇒ τ_s = 4 meets `3·τ ≥ 2d`). -/
def bbSmallXSurgery : SurgeryGadget :=
  canonicalXSurgery (bbSmall.toQECCode 2 6) bbSmall_lx 4 8

theorem bbSmallXSurgery_verifies :
    SurgeryGadget.verify_surgery_gadget bbSmallXSurgery = true := by decide


/-- Per-vector certification of the EXACT logical the gadget consumes
    (legacy `logicalX_genuine` pattern, applied to the `getD 0` vector). -/
theorem bbSmall_lx_certified :
    (bbSmall.hz.all (fun r => ! gf2dot r bbSmall_lx)
      && ! inRowspace bbSmall.hx bbSmall_lx) = true := by decide

/-- The merged code as a `CSSCode` — the L5 leg mirroring
    `surface3_merged_syndrome_circuit_implements`: the merged checks form a
    VALID stabilizer code via the legacy `syndrome_circuit_implements_code`. -/
def bbSmallXSurgery_merged_css : FormalRV.QEC.CSSCode :=
  ⟨bbSmallXSurgery.merged_n, bbSmallXSurgery.merged_hx, bbSmallXSurgery.merged_hz⟩

theorem bbSmallXSurgery_merged_syndrome_valid :
    StabilizerState.valid bbSmallXSurgery_merged_css.toStabilizers bbSmallXSurgery_merged_css.n = true :=
  (FormalRV.QEC.CSSCode.syndrome_circuit_implements_code
    bbSmallXSurgery_merged_css (by decide)).mpr (by decide)

/-! ## 4. The compiled physical circuit and its semantics -/

theorem bbSmall_circuit_measures_merged :
    Round.measuredDataObs
        (bbSmallXSurgery.merged_n + bbSmallXSurgery.merged_hx.length
          + bbSmallXSurgery.merged_hz.length)
        bbSmallXSurgery.merged_n (SurgeryGadget.extractionRound bbSmallXSurgery)
      = FormalRV.Framework.SurgeryReadout.merged_stabilizers_X bbSmallXSurgery
        ++ FormalRV.Framework.SurgeryCorrect.merged_stabilizers_Z bbSmallXSurgery :=
  extractionRound_measures_merged bbSmallXSurgery (by decide) (by decide)

theorem bbSmall_circuit_readout (signs : List Bool)
    (hsig : signs.length = bbSmallXSurgery.merged_hx.length) :
    ((Round.measuredDataObs
        (bbSmallXSurgery.merged_n + bbSmallXSurgery.merged_hx.length
          + bbSmallXSurgery.merged_hz.length)
        bbSmallXSurgery.merged_n
        (SurgeryGadget.extractionRound bbSmallXSurgery)).take
          bbSmallXSurgery.merged_hx.length
      = FormalRV.Framework.SurgeryReadout.merged_stabilizers_X bbSmallXSurgery)
    ∧ FormalRV.Framework.SurgeryCorrect.selectedSignedProduct
        bbSmallXSurgery.span_witness bbSmallXSurgery.merged_hx signs
      = FormalRV.Framework.SurgeryCorrect.signedXRow
          (FormalRV.Framework.SurgeryCorrect.selectedParity
            bbSmallXSurgery.span_witness signs)
          bbSmallXSurgery.target_pauli :=
  extraction_measures_readout bbSmallXSurgery (by decide) signs
    (by decide) (by decide) hsig (by decide)

/-! ## 5. Independent resource counts — via the PARAMETRIC theorems -/

theorem bbSmall_circuit_width :
    FormalRV.Resource.widthC
        (Round.ops (SurgeryGadget.extractionRound bbSmallXSurgery)) = 39 := by
  rw [widthC_extractionRound bbSmallXSurgery (by decide) (by decide) (by decide)]
  decide

theorem bbSmall_circuit_cnots :
    FormalRV.Resource.cxCountC
        (Round.ops (SurgeryGadget.extractionRound bbSmallXSurgery)) = 77 := by
  rw [cxCountC_extractionRound]
  decide

theorem bbSmall_circuit_meas :
    FormalRV.Resource.measCountC
        (Round.ops (SurgeryGadget.extractionRound bbSmallXSurgery)) = 20 := by
  rw [measCountC_extractionRound]
  decide

/-! ## 6. Logical-cycle schedule -/

open FormalRV.QEC.Time

/-- Two parallel X̄-measurements on disjoint bbSmall blocks: 4 cycles
    (τ_s = 4), vs 8 sequentially. -/
def bbTwoPPMpar : CycleSchedule :=
  .par (.op (.ppmVia bbSmallXSurgery 0)) (.op (.ppmVia bbSmallXSurgery 39))

theorem bb_par_wellFormed : bbTwoPPMpar.wellFormed = true := by decide
theorem bb_par_duration : bbTwoPPMpar.duration = 4 := by decide

end FormalRV.QEC.Codes.BB
