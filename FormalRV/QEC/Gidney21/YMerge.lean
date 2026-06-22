/-
  FormalRV.QEC.Gidney21.YMerge
  ----------------------------
  (completeness) The single-patch logical-Y measurement, via the Litinski
  S-gadget: a Zbar-tensor-Zbar merge with a supplied |Y>-eigenstate ancilla.

  Ybar = Xbar . Zbar on ONE patch is irreducibly mixed-type, so NO single
  direct X- or Z-surgery measures it (a patch is primal OR dual, not both;
  Ybar anticommutes with both Xbar and Zbar, so no representative is one type).
  The standard fault-tolerant realization (Litinski, "A game of surface
  codes") measures Ybar_a by:
    (1) supplying a fresh |Y>-eigenstate ancilla patch y (a CLIFFORD magic
        state -- no factory at this level, exactly as |T> / |CCZ> are);
    (2) a joint Zbar_a-tensor-Zbar_y lattice-surgery measurement (a Z-merge);
    (3) reading the ancilla.

  The PHYSICAL CIRCUIT is therefore exactly a verified two-patch Z-merge --
  fully MergeFullyCorrect (syndrome extraction + the Zbar-tensor-Zbar
  measurement).  The step from "measures Zbar_a Zbar_y" to "measures Ybar_a"
  is supplied by the |Y> ancilla state -- the SAME supplied-Clifford-state
  residue already accepted for the magic states.  We verify the circuit; we
  do not re-derive the state evolution.
-/
import FormalRV.QEC.Gidney21.MixedMerge

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC FormalRV.QEC.Circuit
open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.LatticeSurgery

/-! ## §1. The Y-measurement S-gadget circuit (a two-patch Z-merge). -/

/-- The two oriented axes of the Y-gadget: the data/magic patch and the
|Ȳ⟩-ancilla patch are BOTH joined on their Z̄ boundary. -/
def yGadgetAxes : List MergeAxis := [MergeAxis.zAxis, MergeAxis.zAxis]

/-- **The Ȳ-measurement gadget circuit**: the joint `Z̄ ⊗ Z̄` lattice-surgery
merge between the data/magic patch and the supplied |Ȳ⟩-eigenstate ancilla
patch — the physical realization of `measure Y[a]`. -/
def yMeasurementMerge (d tau bound : Nat) : SurgeryGadget :=
  mixedMerge yGadgetAxes d tau bound

/-! ## §2. d = 3 — the gadget circuit is fully verified. -/

/-- The Y-gadget's Z̄⊗Z̄ merge passes the structural verifier (d=3). -/
theorem yMerge3_verifies :
    SurgeryGadget.verify_surgery_gadget (yMeasurementMerge 3 2 30) = true := by
  decide

/-- **The Y-measurement gadget's PHYSICAL CIRCUIT is fully semantically
correct** — its detailed syndrome extraction of the merged composite AND its
joint Z̄⊗Z̄ measurement are both correct.  (The Ȳ semantics then follows from
the supplied |Ȳ⟩ ancilla — the magic-state residue.) -/
theorem yMerge3_fully_correct : MergeFullyCorrect (yMeasurementMerge 3 2 30) :=
  mergeFullyCorrect_of (yMeasurementMerge 3 2 30)

/-- The Y-gadget's syndrome extraction measures the merged stabilizers. -/
theorem yMerge3_syndrome_correct :
    Round.measuredDataObs
        ((mergedCSS (yMeasurementMerge 3 2 30)).n
          + (mergedCSS (yMeasurementMerge 3 2 30)).hx.length
          + (mergedCSS (yMeasurementMerge 3 2 30)).hz.length)
        (mergedCSS (yMeasurementMerge 3 2 30)).n
        (SurgeryGadget.extractionRound (yMeasurementMerge 3 2 30))
      = (mergedCSS (yMeasurementMerge 3 2 30)).toStabilizers :=
  merge_syndrome_correct (yMeasurementMerge 3 2 30) (by decide)

/-- The Y-gadget's merge measures its target joint Z-logical, for every
outcome (the Z̄_a Z̄_y readout the S-gadget consumes). -/
theorem yMerge3_logical_correct (signs : List Bool)
    (hsig : signs.length = (yMeasurementMerge 3 2 30).merged_hx.length) :
    selectedSignedProduct (yMeasurementMerge 3 2 30).span_witness
        (yMeasurementMerge 3 2 30).merged_hx signs
      = signedXRow (selectedParity (yMeasurementMerge 3 2 30).span_witness signs)
          (yMeasurementMerge 3 2 30).target_pauli :=
  ((yMerge3_fully_correct).2 signs hsig yMerge3_verifies (by decide) (by decide))

/-! ## §3. d = 27 — the Y-gadget circuit at GE2021 scale. -/

/-- **The Y-measurement gadget's circuit verifies at d = 27.** -/
theorem yMerge27_verifies :
    SurgeryGadget.verify_surgery_gadget (yMeasurementMerge 27 18 60) = true := by
  native_decide

/-- **The d=27 Y-measurement gadget's physical circuit is fully semantically
correct** — the verified S-gadget Z̄⊗Z̄ merge at GE2021 scale. -/
theorem yMerge27_fully_correct : MergeFullyCorrect (yMeasurementMerge 27 18 60) :=
  mergeFullyCorrect_of (yMeasurementMerge 27 18 60)

end FormalRV.QEC.Gidney21
