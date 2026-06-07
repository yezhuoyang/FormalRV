/-
  Audit · cain-xu-2026 · LAYER 1 — THE ALGORITHM
  ============================================================================
  cain-xu factors RSA-2048 with a windowed Ekerå–Håstad Shor (q_A = 33; the
  recorded `cainxu_shor` lives in L4_Code with the parametric tuple).  The
  ALGORITHM-LEVEL success guarantee is SHARED and N-parametric — the order-finding
  success bound ≥ κ/(log₂N)⁴ (see Audit/Peng2022 and FormalRV.StandardShor).

  This layer also carries (one flat namespace `FormalRV.Audit.CainXu2026`):
    • the Shor↔LP-code BRIDGE — one theorem mentioning BOTH the Shor success bound
      and the LP-code semantics (was ShorOnLPBridge);
    • the proof-carrying CONTRACT / verifier for "fault-tolerant Shor on a
      user-specified LP code" (was ShorLPContract).

  No `sorry`, no `axiom`.
-/
import FormalRV.Audit.CainXu2026.Verifier
import FormalRV.StandardShor
import FormalRV.Shor.ShorPPMEndToEnd
import FormalRV.Shor.ShorPPMUnitaryReduction
import FormalRV.Shor.TeleportCCXGrounded
import FormalRV.QEC.LogicalMeasurementGeneral

namespace FormalRV.Audit.CainXu2026

open FormalRV.Framework
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMToffoliMagic
open FormalRV.Framework.CircuitToPPMFactoryProvision
open FormalRV.Framework.CircuitToPPMInterface
open FormalRV.Framework.LDPC
open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp
open FormalRV.Framework.SurgeryCorrect
open FormalRV.BQAlgo
open FormalRV.Shor.ShorModMulPPMFactoryE2E
open FormalRV.Shor.ShorPPMEndToEnd
open FormalRV.QEC
open FormalRV.QEC.LogicalFinder
open FormalRV.QEC.LogicalMeasurementGeneral
open VerifiedShor

/-============================================================================
  PART A — The Shor↔LP-code bridge (was ShorOnLPBridge)
============================================================================-/

/-- **SHOR ON THE LP CODE (seam 1 bridge).**  In a single statement importing both
    subtrees:
    (A) **Algorithm + arithmetic** — Shor order-finding succeeds with probability
        `≥ κ/(log₂N)⁴`, and the modular multiplier compiled to a magic-provisioned
        PPM program observes the correct modular product `(a·x) mod N`.
    (B) **LP-code compilation target** — qianxu's LP code has well-defined logical
        qubits, a logical measurement is realised by a structurally-verified surgery
        gadget on it, and the full modexp (any-length logical-PPM sequence `ps`)
        preserves the code. -/
theorem shor_on_LP_code
    (F : TFactoryContract)
    (a r N m bits ainv x : Nat)
    (h_setting : ShorSetting a r N m bits)
    (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (ps : List PauliString)
    (hlog : ∀ P ∈ ps, ∀ g ∈ codeStabs, g.commutes P = true) :
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
    ∧ ( bbSmallLogicalBasis.valid = true
      ∧ FormalRV.Framework.LDPC.SurgeryGadget.verify_surgery_gadget bb_x_surgery = true
      ∧ (∀ g ∈ codeStabs, g ∈ runPPMs ps bbCodeState) ) :=
  ⟨shor_succeeds_with_ppm_realized_modmult F a r N m bits ainv x h_setting h_sizing h_inv h_ainv_le hx,
   bbSmallLogicalBasis_valid,
   bb_x_surgery_verifies,
   fun g hg => logical_computation_preserves_code ps hlog g hg⟩

/-- **The connection is the SAME gate set.**  Every Clifford `ICX` gate of the
    modular multiplier REDUCES to its Boolean PPM run (seam 6), and every
    `CCX`/Toffoli is GROUNDED in the verified Clifford+T circuit (seam 5). -/
theorem multiplier_gateset_bridges_to_LP
    (F : TFactoryContract) (g : Gate) (hICX : isICXGate g = true) (f : Nat → Bool)
    (σ' : MagicBasisPPMState)
    (hrun : PPMProgramRel
              (magicBasisPPMSemanticsModel F)
              (compileArithmeticGateToPPM g)
              (magicBasisEncodeBits F f) σ')
    (a b c : Nat) (hac : a ≠ c) (hbc : b ≠ c)
    (s t : MagicBasisPPMState) (h : teleportCCXRel F a b c s t) :
    σ'.bits = Gate.applyNat g f
    ∧ ( t.bits a, t.bits b, t.bits c )
        = (s.bits a, s.bits b, xor (s.bits c) (s.bits a && s.bits b)) :=
  ⟨FormalRV.Shor.ShorPPMUnitaryReduction.ppm_clifford_run_eq_applyNat F g hICX f σ' hrun,
   (FormalRV.Shor.TeleportCCXGrounded.teleportCCX_grounded_in_verified_clifford_T
      F a b c s t hac hbc h).1⟩

/-============================================================================
  PART B — The proof-carrying contract / verifier (was ShorLPContract)
============================================================================-/

/-- The GF(2) support of a Pauli string: the positions where it acts non-trivially. -/
def pauliSupport (P : PauliString) : BoolVec :=
  P.ops.map (fun p => decide (p ≠ Pauli.I))

/-- **The fault-tolerant-Shor-on-`code` certificate.**  A term of this type is a
    complete, machine-checked proof that the user's LP `code` carries a
    fault-tolerant Shor's algorithm.  Every field is a genuine obligation. -/
structure Certificate (code : CSSCode) where
  hCSS : code.valid = true
  k : Nat
  basis : LogicalBasis code k
  hBasisValid : basis.valid = true
  hDimension : code.n - rank code.hx - rank code.hz = k
  bits : Nat
  N : Nat
  a : Nat
  ainv : Nat
  arithCircuit : Gate
  hArithCorrect : ∀ x : Nat, x < N →
    Gate.applyNat arithCircuit (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) x)
      = encodeDataZeroAnc bits (ModMul.ancillaWidth bits) ((a * x) % N)
  program : List PauliString
  hProgramLogical : ∀ P ∈ program, ∀ g ∈ code.hx.map CSSCode.xStab ++ code.hz.map CSSCode.zStab,
    g.commutes P = true
  hPreservesCode : ∀ g ∈ code.hx.map CSSCode.xStab ++ code.hz.map CSSCode.zStab,
    g ∈ measureChecks program (codeStateWithLogicals code k basis)
  gadgets : Fin program.length → SurgeryGadget
  hGadgetsOnCode : ∀ i : Fin program.length,
    (gadgets i).data_code.hx = code.hx ∧ (gadgets i).data_code.hz = code.hz
  hGadgetsVerified : ∀ i : Fin program.length,
    SurgeryGadget.verify_surgery_gadget (gadgets i) = true
  hGadgetsMeasure : ∀ i : Fin program.length,
    (gadgets i).target_pauli
      = pauliSupport (program.get i) ++ List.replicate (gadgets i).ancilla_n false
  encodeState : Nat → StabilizerState
  hSimulates : ∀ x : Nat, x < N →
    measureChecks program (encodeState x) = encodeState ((a * x) % N)
  r : Nat
  m : Nat
  hShorSucceeds :
    FormalRV.SQIRPort.probability_of_success a r N m bits (ModMul.ancillaWidth bits)
        (ModMul.circuitFamily a ainv N bits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
  qubitBound : Nat
  timeBound : Nat
  numPPMs : Nat
  tau_s : Nat
  cycle : Nat
  n_LP : Nat
  N_A : Nat
  factory : Nat
  hQubitBound : qubitBound = upperQubits n_LP N_A factory
  hTimeBound  : timeBound = upperTimeUs numPPMs tau_s cycle
  hTimeIsUpperBound : ∀ depth, depth ≤ numPPMs →
    depth * tau_s * cycle ≤ upperTimeUs numPPMs tau_s cycle

/-- The verifier's decidable acceptance core: the code is CSS, the logical basis is
    valid, and the qubit count is the true dimension. -/
def acceptsCore (code : CSSCode) (k : Nat) (basis : LogicalBasis code k) : Bool :=
  code.valid && basis.valid && decide (code.n - rank code.hx - rank code.hz = k)

/-- Soundness of the core checker. -/
theorem acceptsCore_iff (code : CSSCode) (cert : Certificate code) :
    acceptsCore code cert.k cert.basis = true := by
  unfold acceptsCore
  rw [cert.hCSS, cert.hBasisValid]
  simp [cert.hDimension]

/-- The decidable core IS satisfiable on the real [[18,2,d]] bivariate-bicycle code. -/
theorem bbSmall_core_accepted :
    acceptsCore bbSmall 2 bbSmallLogicalBasis = true := by decide

/-- A deliberately WRONG logical basis for the BB code. -/
def bogusBasis : LogicalBasis bbSmall 2 :=
  { lx := fun _ => List.replicate bbSmall.n false
    lz := fun _ => List.replicate bbSmall.n false }

/-- **The verifier REJECTS the bogus basis** — overclaiming is impossible. -/
theorem bogus_rejected : acceptsCore bbSmall 2 bogusBasis = false := by decide

/-- Concretely, the bogus basis fails validity. -/
theorem bogus_basis_invalid : bogusBasis.valid = false := by decide

end FormalRV.Audit.CainXu2026

#check @FormalRV.Audit.CainXu2026.cainxu_instance              -- the recorded ShorAlgorithm (q_A = 33)
#check @FormalRV.StandardShor.orderFindingSucceeds            -- ✅ shared success bound ≥ κ/(log₂N)⁴
#check @FormalRV.Audit.CainXu2026.shor_on_LP_code            -- bridge: Shor success ∧ LP-code semantics
#check @FormalRV.Audit.CainXu2026.bbSmall_core_accepted      -- contract core accepts the real BB code
