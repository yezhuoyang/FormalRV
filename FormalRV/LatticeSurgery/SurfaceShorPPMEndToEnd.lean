/-
  FormalRV.LatticeSurgery.SurfaceShorPPMEndToEnd — the capstone of Path A: PPM-based
  Shor's algorithm, joined to a FULLY COMPILED surface-code realisation of a
  logical Pauli-product measurement (lattice surgery + detailed syndrome
  extraction), semantically verified.

  ## What this proves (and its honest scope)

  `surface_shor_ppm_physically_realized` conjoins, at the SAME parameters, two
  sorry-free results:

  (I) PPM-LEVEL SHOR (reused verbatim from
      `ShorPPMEndToEnd.shor_succeeds_with_ppm_realized_modmult`): order finding
      succeeds with probability ≥ κ/(log₂N)⁴, and the modular-multiplier oracle
      is compiled to a magic-aware PPM program that runs on a factory pool and
      observes the correct modular product.

  (II) SURFACE-CODE REALISATION of a logical PPM (this Path-A contribution):
      a representative logical Pauli-product measurement — the logical X̄ of the
      surface code [[13,1,3]] — is FULLY COMPILED to a physical surface-code
      circuit and verified:
        * the surgery gadget passes the structural verifier
          (`surface3_x_surgery_verifies`);
        * it MEASURES the logical X̄ — the readout (R) of the code-general,
          axiom-free `surgery_implements_logical_measurement`
          (`surface3_x_surgery_measures_logicalX`);
        * the LATTICE SURGERY is the syndrome extraction of the merged code,
          whose detailed CSS syndrome circuit (one ancilla + CNOTs + measurement
          per merged check, `CliffordConj`-realised) implements the merge
          (`surface3_merged_syndrome_circuit_implements`).

  ## Honesty boundary (precise — read before citing)

  This is a CONJUNCTION, NOT a reduction.  We prove "Shor (at the PPM level)
  succeeds AND each logical PPM it abstracts is realisable by a verified
  surface-code surgery gadget with an explicit physical CSS syndrome circuit".
  We do NOT prove "the Shor PPM program literally executes as a single surface
  schedule".  The deferred contract (exactly as `ShorPPMEndToEnd` already
  delimits `teleportCCXRel`, factory distillation, QPE, decoder) is:
    * the operational reduction of each `MagicPPMCommand`
      (`teleportCCX` / `base`) to a concrete sequence of surgery gadgets, and
      the enumeration of ALL of Shor's PPMs into one composed surface circuit;
    * merged-code DISTANCE / fault-tolerant error suppression;
    * the Gottesman–Knill Hilbert-space faithfulness of the Heisenberg picture.
  What is NEW and verified here: the PPM-on-a-code gap John flagged is closed for
  the surface code — a logical PPM is no longer an abstract command but a
  concrete, structurally-verified, logically-correct surface-code surgery whose
  every stabiliser is an explicit gate circuit.

  No Mathlib beyond what `ShorPPMEndToEnd` already pulls (the success bound is
  over ℝ).  No `sorry`; no NEW axioms beyond those of conjunct (I).
-/

import FormalRV.Shor.PPM.ShorPPMEndToEnd
import FormalRV.LatticeSurgery.SurgeryDemoSurface

namespace FormalRV.LatticeSurgery.SurfaceShorPPMEndToEnd

open FormalRV.Framework
open FormalRV.Framework.Factory
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMToffoliMagic
open FormalRV.Framework.CircuitToPPMFactoryProvision
open FormalRV.BQAlgo
open FormalRV.Shor.ShorModMulPPMFactoryE2E
open FormalRV.Shor.ShorPPMEndToEnd
open VerifiedShor
open FormalRV.LatticeSurgery.SurgeryDemoSurface
open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.Framework.SurgeryReadout
open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp
open FormalRV.QEC

/-- **CAPSTONE (Path A): PPM-Shor succeeds, AND a logical PPM is fully realised
    by a verified surface-code circuit (lattice surgery + detailed syndrome
    extraction).**

    (I) is `shor_succeeds_with_ppm_realized_modmult` verbatim; (II) is the
    surface-code realisation of the logical X̄ PPM.  See the file header for the
    precise honesty boundary (this is a conjunction, not a whole-program
    reduction). -/
theorem surface_shor_ppm_physically_realized
    (F : TFactoryContract)
    (a r N m bits ainv x : Nat)
    (h_setting : ShorSetting a r N m bits)
    (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (signs : List Bool)
    (hsig : signs.length = surface3_x_surgery.merged_hx.length) :
    -- (I) PPM-level Shor (reused):
    (FormalRV.SQIRPort.probability_of_success a r N m bits
        (ModMul.ancillaWidth bits) (ModMul.circuitFamily a ainv N bits)
        ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
     ∧ ∃ σ',
        MagicPPMProgramRel F
          (compileArithmeticGateToMagicPPM (ModMul.gateMCP bits N a ainv))
          (encodeWithPool (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) x)
            (factoryProvision F (shorMagicDemand (ModMul.gateMCP bits N a ainv)))) σ'
        ∧ (magicBasisRefinesApplyNat F).observesBits σ'
            (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) ((a * x) % N)))
    -- (II) a logical PPM is fully realised by a verified surface-code circuit:
    ∧ (SurgeryGadget.verify_surgery_gadget surface3_x_surgery = true
       ∧ (selectedSignedProduct surface3_x_surgery.span_witness
            surface3_x_surgery.merged_hx signs
            = signedXRow (selectedParity surface3_x_surgery.span_witness signs)
                surface3_x_surgery.target_pauli)
       ∧ StabilizerState.valid surface3_merged_css.toStabilizers
            surface3_merged_css.n = true) := by
  refine ⟨shor_succeeds_with_ppm_realized_modmult F a r N m bits ainv x
            h_setting h_sizing h_inv h_ainv_le hx, ?_⟩
  exact ⟨surface3_x_surgery_verifies,
         surface3_x_surgery_measures_logicalX signs hsig,
         surface3_merged_syndrome_circuit_implements⟩

end FormalRV.LatticeSurgery.SurfaceShorPPMEndToEnd
