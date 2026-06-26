/-
  FormalRV.Shor.GidneyInPlace — UMBRELLA / public interface of the Gidney in-place
  coset-multiplier Shor success proof.
  ════════════════════════════════════════════════════════════════════════════

  This file is the single public entry point for the modularised proof.  Importing
  it pulls the headline theorem together with every reusable component contract, and
  acts as the full build gate for the folder (all 102 live files build through here).

      THE HEADLINE THEOREM
        `FormalRV.Shor.GidneyInPlace.E2RunwayShorCapstone.gidney_inplace_coset_shor_succeeds_hybrid`
        — the oblivious-runway in-place coset multiplier realises Shor's algorithm with
          success deviation bounded by `2·m·√(8·numWin/2^cm)`.
        Axiom-clean: {propext, Classical.choice, Quot.sound}.

  COMPONENT MAP (each folder = an independent, reusable component split Def / Spec / Proof):

      Primitives/   coset-arithmetic primitives, states, approx-op interface, orbit fold,
                    phase-register marginal.
      Gate/         the reversible-gate ↔ permutation ↔ Cuccaro layout bridge.
      Adder/        two-register product-add wrapper + its modular-arithmetic spec.
      ReducedLookup/ the reduced-lookup coset gate (value, shift, step action).
      OutOfPlaceCoset/ the OUT-of-place coset multiplier (table sum, fold, deviation E).
      QPE/          the oracle-abstract QPE stage decomposition + well-typedness.
      Ideal/        the ideal runway multiplier, coset-eigenstate intertwining trajectory,
                    and the E₂ actual-side state/probability objects (Def/E2CosetSuccess).
      Embedding/    the two-register canonical-residue embedding + marginal isometry.
      InPlace/      the IN-place coset multiplier: gate Def, frontier Spec, and the
                    three-leg Proof (Legs / Branch / Mass / Input).
      Deviation/    the generic ℓ² (pmDist) telescoping Engine + the E₂ deviation Proof.
      Capstone/     the headline theorem (root) + the G0/physical-realisation glue (Proof).

  Legacy/ holds the superseded EmbedAgreeOff orbit-fold route; it is archived, not part
  of this interface, and is intentionally NOT imported here (see Legacy/ for why the route
  is non-inhabitable for the physical gate).
-/

-- ── THE headline theorem (transitively builds the live proof closure) ─────────────
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorCapstone
-- ── The coset bound against the EXPLICIT Shor floor κ/(log₂N)⁴ (Shor_correct_var weld) ──
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorUnconditional
-- ── A concrete exact ModMulImpl multiplier at the coset dimension (w ≥ 2) ──
import FormalRV.Shor.GidneyInPlace.Capstone.IdealResidueOracle
-- ── Route B′: the residue↔runway intertwining from canonical-only data (weakened hf_residue) ──
import FormalRV.Shor.GidneyInPlace.Capstone.E2ResidueEmbedCanonical
-- ── Route B′: the coset κ-floor capstone from canonical-only residue data ──
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorCanonical
-- ── Route B′ step 2: idealResidueFamily discharges the canonical capstone's hf_res_can ──
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorClosure
-- ── Route B′ step 2d: coset-machine final state is sub-unit (discharges hnormP/hnormI) ──
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorNorms
-- ── Route B′ ideal-runway-oracle effort: a verified reversible divide-by-N (E2RunwayDivider) + exact
--    mod-mult (E2RunwayResidueMul) compose into the clean-ancilla guarded-shift gate (E2RunwayGuardedShift);
--    E2RunwayReduction reduces the UNCONDITIONAL bound to one obligation (a gate with gateToPerm = idealPerm)
--    + the route-S column-identity reduction. ──
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayReduction
-- ── GENERIC reversible-permutation synthesis (the route that realizes the ideal runway oracle): clean
--    multi-controlled-X (E2RunwaySynthMCX) → transposition gate (E2RunwaySynthSwap) → permGate σ via
--    Mathlib's swap factorization (E2RunwaySynthPerm) → the runway gate = permGate of resShiftPerm on the
--    a-block + its route-S column identity (E2RunwaySynthRunwayGate). ──
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthRunwayGate
-- ── ★ THE FULLY-UNCONDITIONAL coset/runway Shor bound: physRunwayOracle ≥ κ/(log₂N)⁴ − 2m√(8·numWin/2^cm),
--    NO abstract oracle hypothesis, NO cm≤2w-3 constraint — only standard parameters (w ≥ 2) + a·ainv0 ≡ 1. ──
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorFinal
-- ── The runway INPUT is a genuine state-prep CIRCUIT: uc_eval(E2runwayInitPrep, a concrete X+interior-npar_H circuit)
--    · |0…0⟩ = E2runwayInit (no abstract input). Chain: RunwayPrepCore → SubBlock → Full → Close → Done. ──
import FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepDone

-- ── Public component contracts (the Spec layer) ──────────────────────────────────
import FormalRV.Shor.GidneyInPlace.Gate.Spec.UCEvalBridge
import FormalRV.Shor.GidneyInPlace.Gate.Spec.GateAddConstBridge
import FormalRV.Shor.GidneyInPlace.Adder.Spec.ProductAddArith
import FormalRV.Shor.GidneyInPlace.ReducedLookup.Spec.ReducedLookupCosetShift
import FormalRV.Shor.GidneyInPlace.ReducedLookup.Spec.ReducedLookupCosetValue
import FormalRV.Shor.GidneyInPlace.OutOfPlaceCoset.Spec.CosetMul
import FormalRV.Shor.GidneyInPlace.OutOfPlaceCoset.Spec.CosetTableSum
import FormalRV.Shor.GidneyInPlace.QPE.Spec.QpeStageWellTyped
import FormalRV.Shor.GidneyInPlace.Ideal.Spec.RunwayCosetEigenstate
import FormalRV.Shor.GidneyInPlace.Ideal.Spec.RunwayIntertwine
import FormalRV.Shor.GidneyInPlace.InPlace.Spec.InPlaceCoset
import FormalRV.Shor.GidneyInPlace.InPlace.Spec.InPlaceCosetSpec
import FormalRV.Shor.GidneyInPlace.InPlace.Spec.InPlaceCosetDeviation

-- The public actual-side success objects (`probability_of_success_E2coset`,
-- `Shor_final_state_E2coset`, `E2runwayInit`) — foundational defs, hence in Ideal/Def.
import FormalRV.Shor.GidneyInPlace.Ideal.Def.E2CosetSuccess

-- ── Reusable components off the capstone critical path (full-build coverage) ──────
-- The Cuccaro literal-gate ↔ coset-shift layout bridge: a complete, verified component
-- that the E₂ hybrid route does not route through, kept for reuse and audit.
import FormalRV.Shor.GidneyInPlace.Primitives.Def.CosetLayout
import FormalRV.Shor.GidneyInPlace.Adder.Def.ProductAddLayout
import FormalRV.Shor.GidneyInPlace.Gate.Proof.CosetLayoutTransport
import FormalRV.Shor.GidneyInPlace.Gate.Proof.CuccaroLayoutAdapter
import FormalRV.Shor.GidneyInPlace.Ideal.Proof.CosetRunwayStep
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceCosetForward
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceCosetClearing
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Mass.InPlaceCosetNormBound

-- ── Auxiliary probes (proven, unwired; structural results from the discharge log) ──
import FormalRV.Shor.GidneyInPlace.InPlace.Def.InPlaceBasisBridge
import FormalRV.Shor.GidneyInPlace.Embedding.Proof.InPlaceContractInput
import FormalRV.Shor.GidneyInPlace.Embedding.Proof.InPlaceTwoRegEmbedIsometry
