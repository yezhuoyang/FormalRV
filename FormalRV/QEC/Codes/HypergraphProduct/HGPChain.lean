/-
  FormalRV.QEC.Codes.HypergraphProduct.HGPChain — the hypergraph-product
  family's END-TO-END test case (see `../README.md` for the pipeline charter).

  The code: `hgp73 = HGP(Hamming [7,4], rep 3)` — a genuinely NON-SQUARE,
  non-surface hypergraph product, [[27, 4, d]] (4 logical qubits COMPUTED
  from the matrices; d asserted 3 = min of the factors' distances).

  Every step below is the same pipeline as the other family folders:
  validity → computed logicals → verified X̄-surgery on a computed logical →
  compiled circuit semantics → independent counts → cycle schedule.

  No Mathlib.  No `sorry`; no project axioms (kernel `decide` throughout
  unless noted).
-/

import FormalRV.QEC.LatticeSurgery.XSurgeryBuilder
import FormalRV.QEC.Circuit.CircuitSemantics
import FormalRV.QEC.Circuit.ExtractionCount
import FormalRV.QEC.LogicalFinder
import FormalRV.QEC.StabilizerCode

-- The HGP matrices are built through `kron`; kernel `decide` on them needs
-- more recursion headroom than the default (still kernel-checked, no
-- native_decide).
set_option maxRecDepth 16384

namespace FormalRV.QEC.Codes.HGP

open FormalRV.QEC FormalRV.QEC.Circuit FormalRV.QEC.LogicalFinder
open FormalRV.Framework FormalRV.Framework.LDPC FormalRV.Framework.PPMOp
open FormalRV.LatticeSurgery.SurfaceShorResourceCount

/-! ## 1. The code -/

/-- HGP of the Hamming [7,4] check (= the Steane matrix) with the distance-3
    repetition check: `[[7·3 + 3·2, 4, 3]] = [[27, 4, 3]]`. -/
def hgp73 : FormalRV.QEC.CSSCode :=
  FormalRV.QEC.Algebraic.hypergraphProduct
    FormalRV.Framework.LDPC.steaneH (FormalRV.QEC.Algebraic.repCode 3) 3 7 2 3

theorem hgp73_n : hgp73.n = 27 := by decide
theorem hgp73_well_shaped : hgp73.well_shaped = true := by decide
theorem hgp73_css : hgp73.css_condition = true := by decide

/-- The lowered check set is a valid stabilizer code (the general-code
    embedding). -/
theorem hgp73_stabilizer_valid : hgp73.toStabilizerCode.valid = true :=
  CSSCode.toStabilizerCode_valid hgp73 hgp73_well_shaped hgp73_css

/-! ## 2. Logical operators, COMPUTED from the matrices -/

theorem hgp73_k : numLogicals hgp73 = 4 := by decide
theorem hgp73_logicalX_genuine : logicalX_genuine hgp73 = true := by decide
theorem hgp73_logicalZ_genuine : logicalZ_genuine hgp73 = true := by decide

/-- The first computed X-type logical (support `{0,1,2}` — a repetition
    string across the first row block). -/
def hgp73_lx : BoolVec := (logicalX hgp73).getD 0 []

/-! ## 3. The logical operation: measure X̄ by lattice surgery -/

/-- X̄-measurement surgery on `hgp73`, built by the GENERIC builder on the
    COMPUTED logical support (d := 3 asserted ⇒ τ_s = 2 meets `3·τ ≥ 2d`). -/
def hgp73XSurgery : SurgeryGadget :=
  canonicalXSurgery (hgp73.toQECCode 4 3) hgp73_lx 2 8

theorem hgp73XSurgery_verifies :
    SurgeryGadget.verify_surgery_gadget hgp73XSurgery = true := by decide


/-- Per-vector certification of the EXACT logical the gadget consumes
    (legacy `logicalX_genuine` pattern, applied to the `getD 0` vector). -/
theorem hgp73_lx_certified :
    (hgp73.hz.all (fun r => ! gf2dot r hgp73_lx)
      && ! inRowspace hgp73.hx hgp73_lx) = true := by decide

/-- The merged code as a `CSSCode` — the L5 leg mirroring
    `surface3_merged_syndrome_circuit_implements`: the merged checks form a
    VALID stabilizer code via the legacy `syndrome_circuit_implements_code`. -/
def hgp73XSurgery_merged_css : FormalRV.QEC.CSSCode :=
  ⟨hgp73XSurgery.merged_n, hgp73XSurgery.merged_hx, hgp73XSurgery.merged_hz⟩

theorem hgp73XSurgery_merged_syndrome_valid :
    StabilizerState.valid hgp73XSurgery_merged_css.toStabilizers hgp73XSurgery_merged_css.n = true :=
  (FormalRV.QEC.CSSCode.syndrome_circuit_implements_code
    hgp73XSurgery_merged_css (by decide)).mpr (by decide)

/-! ## 4. The compiled physical circuit and its semantics -/

/-- The compiled merged-code extraction circuit measures EXACTLY the merged
    stabilizers — the parametric `extractionRound_measures_merged` with
    `decide`-discharged layout hypotheses. -/
theorem hgp73_circuit_measures_merged :
    Round.measuredDataObs
        (hgp73XSurgery.merged_n + hgp73XSurgery.merged_hx.length
          + hgp73XSurgery.merged_hz.length)
        hgp73XSurgery.merged_n (SurgeryGadget.extractionRound hgp73XSurgery)
      = FormalRV.Framework.SurgeryReadout.merged_stabilizers_X hgp73XSurgery
        ++ FormalRV.Framework.SurgeryCorrect.merged_stabilizers_Z hgp73XSurgery :=
  extractionRound_measures_merged hgp73XSurgery (by decide) (by decide)

/-- Composed (R): the circuit's X-prefix is the merged X-checks, and their
    span-witness-selected signed product reads the target X̄. -/
theorem hgp73_circuit_readout (signs : List Bool)
    (hsig : signs.length = hgp73XSurgery.merged_hx.length) :
    ((Round.measuredDataObs
        (hgp73XSurgery.merged_n + hgp73XSurgery.merged_hx.length
          + hgp73XSurgery.merged_hz.length)
        hgp73XSurgery.merged_n
        (SurgeryGadget.extractionRound hgp73XSurgery)).take
          hgp73XSurgery.merged_hx.length
      = FormalRV.Framework.SurgeryReadout.merged_stabilizers_X hgp73XSurgery)
    ∧ FormalRV.Framework.SurgeryCorrect.selectedSignedProduct
        hgp73XSurgery.span_witness hgp73XSurgery.merged_hx signs
      = FormalRV.Framework.SurgeryCorrect.signedXRow
          (FormalRV.Framework.SurgeryCorrect.selectedParity
            hgp73XSurgery.span_witness signs)
          hgp73XSurgery.target_pauli :=
  extraction_measures_readout hgp73XSurgery (by decide) signs
    (by decide) (by decide) hsig (by decide)

/-! ## 5. Independent resource counts — via the PARAMETRIC theorems -/

set_option maxRecDepth 16384 in
theorem hgp73_circuit_width :
    FormalRV.Resource.widthC
        (Round.ops (SurgeryGadget.extractionRound hgp73XSurgery)) = 53 := by
  rw [widthC_extractionRound hgp73XSurgery (by decide) (by decide) (by decide)]
  decide

set_option maxRecDepth 16384 in
theorem hgp73_circuit_cnots :
    FormalRV.Resource.cxCountC
        (Round.ops (SurgeryGadget.extractionRound hgp73XSurgery)) = 105 := by
  rw [cxCountC_extractionRound]
  decide

theorem hgp73_circuit_meas :
    FormalRV.Resource.measCountC
        (Round.ops (SurgeryGadget.extractionRound hgp73XSurgery)) = 25 := by
  rw [measCountC_extractionRound]
  decide

/-! ## 6. Logical-cycle schedule -/

open FormalRV.QEC.Time

/-- Two parallel X̄-measurements on disjoint hgp73 blocks: 2 cycles, vs 4
    sequentially — the family's parallel-PPM demand exemplar. -/
def hgp73TwoPPMpar : CycleSchedule :=
  .par (.op (.ppmVia hgp73XSurgery 0)) (.op (.ppmVia hgp73XSurgery 53))

theorem hgp73_par_wellFormed : hgp73TwoPPMpar.wellFormed = true := by decide
theorem hgp73_par_duration : hgp73TwoPPMpar.duration = 2 := by decide

end FormalRV.QEC.Codes.HGP
