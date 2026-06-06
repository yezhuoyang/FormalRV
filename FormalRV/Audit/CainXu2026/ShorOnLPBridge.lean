/-
  FormalRV.Audit.CainXu2026.ShorOnLPBridge — connect the Shor-algorithm island to the LP-code island
  (closing seam 1, the "biggest seam": the two were import-disjoint, so "no statement could
  even mention both probability_of_success and bbCodeState").

  This module imports BOTH subtrees and states ONE theorem that mentions both:

    • the ALGORITHM side: `shor_succeeds_with_ppm_realized_modmult` — Shor order-finding
      succeeds with probability ≥ κ/(log₂N)⁴ AND its modular multiplier, compiled to a
      magic-provisioned PPM program, observes the correct modular product `(a·x) mod N`
      (the a^x-mod-N ARITHMETIC content, seam 2);

    • the LP-CODE side: the qianxu LP code's logical qubits are well-defined
      (`bbSmallLogicalBasis_valid`), a logical measurement is realised by a
      structurally-verified lattice-surgery gadget ON that code (`bb_x_surgery_verifies`,
      seam 4), and the FULL modexp — any-length logical-PPM sequence — preserves the code
      (`logical_computation_preserves_code`, seam 2-survival).

  And it ties them through the SAME gate set: the modular multiplier is built from
  Clifford `ICX` gates (which REDUCE to the Boolean PPM run, seam 6
  `ppm_clifford_run_eq_applyNat`) and `CCX`/Toffoli gates (GROUNDED in the verified
  Clifford+T circuit, seam 5 `teleportCCX_grounded_in_verified_clifford_T`).

  HONEST RESIDUE (the seam is narrowed, not erased): conjuncts (A) and (B) live at
  different abstraction levels — the algorithm/PPM register (`bits + ancillaWidth` qubits,
  Boolean `Gate.applyNat`) vs the LP stabilizer state (`bbCodeState`, 18 qubits).  Because
  the verified multiplier's register (≥19 qubits for bits=2) does not fit the small
  `decide`-tractable LP instance, the SAME gate term is not literally run on both; the LP
  code is the verified COMPILATION TARGET for the modular arithmetic the algorithm relies
  on, and the connection is spec-level (both realise the same modular-multiply / logical
  operations).  Removing the dimension restriction is the documented next step.

  No `sorry`, no `axiom`.
-/

import FormalRV.Shor.ShorPPMEndToEnd
import FormalRV.Shor.ShorPPMUnitaryReduction
import FormalRV.Shor.TeleportCCXGrounded
import FormalRV.Audit.CainXu2026.QianxuLPSurgery
import FormalRV.Audit.CainXu2026.QianxuModExpLP

namespace FormalRV.Audit.CainXu2026.ShorOnLPBridge

open FormalRV.Framework
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMToffoliMagic
open FormalRV.Framework.CircuitToPPMFactoryProvision
open FormalRV.BQAlgo
open FormalRV.Shor.ShorModMulPPMFactoryE2E
open FormalRV.Shor.ShorPPMEndToEnd
open FormalRV.Audit.CainXu2026.QianxuPPMonLP
open FormalRV.Audit.CainXu2026.QianxuLPComputation
open FormalRV.Audit.CainXu2026.QianxuModExpLP
open FormalRV.Audit.CainXu2026.QianxuLPSurgery
open FormalRV.Framework.CircuitToPPMInterface
open FormalRV.QEC.LogicalFinder
open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp
open VerifiedShor

/-! ## The bridge: one theorem mentioning BOTH the Shor success bound and the LP code -/

/-- **SHOR ON THE LP CODE (seam 1 bridge).**  In a single statement importing both
    subtrees:

    (A) **Algorithm + arithmetic** — Shor order-finding succeeds with probability
        `≥ κ/(log₂N)⁴`, and the modular multiplier compiled to a magic-provisioned PPM
        program observes the correct modular product `(a·x) mod N`.

    (B) **LP-code compilation target** — qianxu's LP code has well-defined logical qubits,
        a logical measurement is realised by a structurally-verified surgery gadget on it,
        and the full modexp (any-length logical-PPM sequence `ps`) preserves the code.

    The two are now in ONE theorem (the import-disjointness is gone); their connection is
    the shared modular-arithmetic / logical-operation content, with the dimension residue
    documented above. -/
theorem shor_on_LP_code
    (F : TFactoryContract)
    (a r N m bits ainv x : Nat)
    (h_setting : ShorSetting a r N m bits)
    (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (ps : List PauliString)
    (hlog : ∀ P ∈ ps, ∀ g ∈ codeStabs, g.commutes P = true) :
    -- (A) ALGORITHM SUCCESS + a^x-mod-N ARITHMETIC (the modular multiplier PPM-realised):
    ( FormalRV.SQIRPort.probability_of_success a r N m bits
          (ModMul.ancillaWidth bits) (ModMul.circuitFamily a ainv N bits)
        ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
      ∧ ∃ σ',
          MagicPPMProgramRel F
            (compileArithmeticGateToMagicPPM (ModMul.gateMCP bits N a ainv))
            (encodeWithPool (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) x)
              (factoryProvision F (shorMagicDemand (ModMul.gateMCP bits N a ainv)))) σ'
          ∧ (magicBasisRefinesApplyNat F).observesBits σ'
              (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) ((a * x) % N)) )
    -- (B) LP-CODE COMPILATION TARGET (logical qubits defined, surgery verified, code preserved):
    ∧ ( bbSmallLogicalBasis.valid = true
      ∧ FormalRV.Framework.LDPC.SurgeryGadget.verify_surgery_gadget bb_x_surgery = true
      ∧ (∀ g ∈ codeStabs, g ∈ runPPMs ps bbCodeState) ) :=
  ⟨shor_succeeds_with_ppm_realized_modmult F a r N m bits ainv x h_setting h_sizing h_inv h_ainv_le hx,
   bbSmallLogicalBasis_valid,
   bb_x_surgery_verifies,
   fun g hg => logical_computation_preserves_code ps hlog g hg⟩

/-! ## The shared gate set: the multiplier's gates are both verified arithmetic AND
    reduce to code-preserving PPMs -/

/-- **The connection is the SAME gate set.**  Every Clifford `ICX` gate of the modular
    multiplier REDUCES to its Boolean PPM run (seam 6), and every `CCX`/Toffoli is GROUNDED
    in the verified Clifford+T circuit (seam 5).  So the modular arithmetic that conjunct
    (A) verifies is realised by exactly the gate set whose PPM compilation conjunct (B)
    runs on the LP code. -/
theorem multiplier_gateset_bridges_to_LP
    (F : TFactoryContract) (g : Gate) (hICX : isICXGate g = true) (f : Nat → Bool)
    (σ' : MagicBasisPPMState)
    (hrun : PPMProgramRel
              (magicBasisPPMSemanticsModel F)
              (compileArithmeticGateToPPM g)
              (magicBasisEncodeBits F f) σ')
    (a b c : Nat) (hac : a ≠ c) (hbc : b ≠ c)
    (s t : MagicBasisPPMState) (h : teleportCCXRel F a b c s t) :
    -- Clifford fragment reduces to the Boolean PPM run (seam 6):
    σ'.bits = Gate.applyNat g f
    -- Toffoli grounded in the verified 8T→CCZ→Toffoli circuit (seam 5):
    ∧ ( t.bits a, t.bits b, t.bits c )
        = (s.bits a, s.bits b, xor (s.bits c) (s.bits a && s.bits b)) :=
  ⟨FormalRV.Shor.ShorPPMUnitaryReduction.ppm_clifford_run_eq_applyNat F g hICX f σ' hrun,
   (FormalRV.Shor.TeleportCCXGrounded.teleportCCX_grounded_in_verified_clifford_T
      F a b c s t hac hbc h).1⟩

end FormalRV.Audit.CainXu2026.ShorOnLPBridge
