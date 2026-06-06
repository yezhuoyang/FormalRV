/-
  FormalRV.Audit.Common.ShorPPMEndToEnd — the end-to-end composition:
  Shor's algorithm succeeds with its verified bound AND its
  resource-dominant arithmetic oracle (the modular multiplier — where
  *all* the Toffoli / magic-state content lives) is realised by a
  factory-provisioned PPM program that provably computes the correct
  modular product.

  ## What this connects

  Two sorry-free results existed but were UNCONNECTED:

  * `VerifiedShor.correct_general_via_interface` — Shor order-finding
    succeeds with probability `≥ κ / (log₂ N)⁴`, using the verified
    modular multiplier `ModMul.circuitFamily` (= the compiled
    `ModMul.gateMCP`) as the oracle.  This is at the SQIR / unitary
    (state-vector) semantic level.

  * `…ShorModMulPPMFactoryE2E.shorModMul_compiles_to_PPM_with_factory`
    — the *same* modular multiplier `ModMul.gateMCP`, compiled to the
    magic-aware PPM program (every Toffoli → certified-T teleportation),
    runs on a factory-provisioned token pool and observes the correct
    Boolean output `encodeDataZeroAnc … ((a·x) mod N)`.

  `shor_succeeds_with_ppm_realized_modmult` packages them: the verified
  Shor success bound holds, AND the modular multiplier feeding it is a
  provisioned PPM program with proven Boolean correctness.

  ## Honesty boundary (precise)

  This is "Shor succeeds + its modular-exponentiation **oracle** is
  PPM-realised", NOT "the entire Shor circuit including QPE is compiled
  to PPM".  Specifically:

  * The **modular multiplier / modular exponentiation** — the
    resource-dominant, Toffoli-rich, magic-consuming part — IS compiled
    to a PPM program and proven correct (Boolean basis-state level) +
    factory-provisioned.
  * The **QPE wrapper** (Hadamards + inverse-QFT phase rotations +
    final measurement) stays at the SQIR / unitary level inside
    `VerifiedShor.correct*`.  Those Clifford+rotation layers are not
    re-expressed as PPM programs here.
  * The PPM correctness of the multiplier is the **success-branch**
    Boolean action (via the `teleportCCXRel` contract, discharged
    quantum-mechanically by `ToffoliScheme`); the per-request factory
    failure probability is accounted in `successProbLB_ppm`, not folded
    into the run.

  So: the headline is honest about scope — Shor's *guarantee* is proved,
  and its *arithmetic oracle* is a verified, provisioned PPM program.
-/
import FormalRV.Audit.Common.ShorModMulPPMFactoryE2E

namespace FormalRV.Audit.Common.ShorPPMEndToEnd

open FormalRV.Framework
open FormalRV.Framework.Factory
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMToffoliMagic
open FormalRV.Framework.CircuitToPPMFactoryProvision
open FormalRV.BQAlgo
open FormalRV.Audit.Common.ShorModMulPPMFactoryE2E
open VerifiedShor

/-- **End-to-end: Shor succeeds, with its modular multiplier realised by
    a provisioned PPM program.**

    Conjunction of two sorry-free facts at the same `(a, N, bits, ainv)`:

    1. **Algorithmic success** — order finding succeeds with probability
       `≥ κ / (log₂ N)⁴` using `ModMul.circuitFamily` as the oracle
       (`VerifiedShor.correct_general_via_interface`).
    2. **PPM realisation of the oracle** — the modular multiplier
       `ModMul.gateMCP bits N a ainv`, compiled to the magic-aware PPM
       program and provisioned with `shorMagicDemand` certified-T tokens
       from `F`, runs to completion and observes the correct modular
       product `encodeDataZeroAnc bits (ancillaWidth bits) ((a·x) % N)`. -/
theorem shor_succeeds_with_ppm_realized_modmult
    (F : TFactoryContract)
    (a r N m bits ainv x : Nat)
    (h_setting : ShorSetting a r N m bits)
    (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1)
    (h_ainv_le : ainv ≤ N) (hx : x < N) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
        (ModMul.ancillaWidth bits) (ModMul.circuitFamily a ainv N bits)
        ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
    ∧ ∃ σ',
        MagicPPMProgramRel F
          (compileArithmeticGateToMagicPPM (ModMul.gateMCP bits N a ainv))
          (encodeWithPool (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) x)
            (factoryProvision F (shorMagicDemand (ModMul.gateMCP bits N a ainv)))) σ'
        ∧ (magicBasisRefinesApplyNat F).observesBits σ'
            (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) ((a * x) % N)) := by
  refine ⟨correct_general_via_interface a r N m bits ainv h_setting h_sizing h_inv, ?_⟩
  have h_a_pos : 0 < a := h_setting.1.1
  have h_a_lt : a < N := h_setting.1.2
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  exact shorModMul_compiles_to_PPM_with_factory F bits N a ainv x
    h_sizing.1 hN_pos h_sizing.2.1 h_sizing.2.2 h_ainv_le hx h_inv

end FormalRV.Audit.Common.ShorPPMEndToEnd
