/-
  FormalRV.Shor.CosetEigenstate.InPlaceCosetSpec — THE SOLE REMAINING CONCRETE FRONTIER:
  the in-place reduced-lookup coset multiplier interface.
  ════════════════════════════════════════════════════════════════════════════

  MILESTONE FREEZE (2026-06-15).  The Route-2 reduced-lookup coset-Shor result is now
  proven CONDITIONAL on exactly one named concrete construction — an in-place coset
  multiplier oracle with off-bad `cosetState`-shift correctness on the Shor work register.
  Everything else is verified, axiom-clean scaffold.

  ── WHAT IS VERIFIED (axiom-clean `[propext, Classical.choice, Quot.sound]`) ─────────────
    * The reduced-lookup OUT-OF-PLACE coset multiplier + its value/cosetState-shift
      correctness off `numWin/2^m` (`ReducedLookupCosetGate/Value/StepAction/Egate/CosetShift`,
      tag `coset-multiplier-local-complete`).
    * The abstract Shor/QPE EmbedAgree scaffold: the QPE stage-decomposition
      (`QPEStageDecomp.shor_final_eq_orbitState`), the embedding `E_phys = I_phase ⊗ E_data`
      + phase-commute + per-branch marginal isometry (`CosetEphys`), the embedded-init
      coset Shor making `hdecomp_a`/`hinit` definitional (`CosetEmbeddedInit`).
    * The controlled-oracle layout bridge (`ControlStageBridge.qpeStage_oracle_jointIdx`).
    * The `hc_local` + `hintertwine` lifting framework over an ABSTRACT work oracle
      (`ControlOracleLift`), feeding the live engine `embedAgreeOff_oracle_step`.

  ── WHAT IS OPEN (this file's spec) ──────────────────────────────────────────────────────
    A concrete in-place coset multiplier oracle `g : BaseUCom (n+anc)` satisfying the
    work-oracle hypotheses `controlled_shifted_oracle_{hc_local,hintertwine}` consume.  The
    repo's verified coset multiplier is OUT-OF-PLACE (`cosetInput 0 → accumulator`, on
    `cosetDim`); the QPE oracle is IN-PLACE (`|z⟩ → |a·z mod N⟩` on `Fin (2^(n+anc))`).  The
    out-of-place result does NOT directly give the in-place action — see
    `COSET_MULTIPLIER_DESIGN.md §9` for why (no in-place coset gate exists; `InPlaceCoset`'s
    swap/uncompute legs are open hypotheses; register/form/bad-set mismatches).

  ── THE NEXT PHASE (4 checkpoints, do NOT start lemma-5 glue before this lands) ───────────
    1. Gate: `inplaceCosetGate := mulFwd ; swap ; mulInv(a⁻¹)` from the verified out-of-place
       reduced-lookup multiplier (`n = bits`, `anc` = the multiplier scratch budget).
    2. Forward leg: reuse `reducedLookupWindowedMul_cosetState_shift`.
    3. Swap + reverse/uncompute: the two-register coset-state transformation + the inverse
       multiplier action (the HARDEST — discharges `InPlaceCoset`'s `hfwd`/`hrev`).
    4. Work-register extraction: convert the two-register out-of-place result into the
       in-place ROW-action `workMat` form (`workMat_c ∘ E_data = E_data ∘ workMat_i` off bad)
       + good-set preservation, with the explicit `B ↔ badY` bad-set correspondence.

  This file states ONLY the target interface (`Prop`, no `sorry`, no axiom) — the type-checked
  contract the next phase proves and then feeds into the (deferred) lemma-5 glue.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.ReducedLookupCosetShift

namespace FormalRV.Shor.CosetEigenstate.InPlaceCosetSpec

open FormalRV.SQIRPort
open FormalRV.Shor.CosetEigenstate.ApproxOp (cosetState)
open FormalRV.Shor.CosetBornWeight (bornWeightOn)

/-- **THE IN-PLACE REDUCED-LOOKUP COSET MULTIPLIER INTERFACE** (the sole remaining concrete
    frontier).  An in-place work oracle `g : BaseUCom (n+anc)` realizes the coset modular
    multiply by `a` mod `N` on the Shor WORK register `Fin (2^(n+anc))` (the data factor of
    `jointIdx (shorDvd …)`, the register `E_data`/`cosetEmbedMat` live on):

      `uc_eval g · cosetState z  =  cosetState ((a·z) mod N)`   for canonical residues `z < N`,

    EXACTLY off a bad set `B` (the runway-wrap boundary) whose Born mass is `≤ numWin/2^cm`.
    `B` lives on the work-register space (NOT the multiplier's `cosetDim` accumulator) —
    phase-independent, as `CosetWrapAccumulation` requires.

    Once provided (next phase, 4 checkpoints above), this discharges the work-oracle
    hypotheses of `ControlOracleLift.controlled_shifted_oracle_{hc_local,hintertwine}` (after
    the `Fin (2^bits) ≅ Fin (2^(n+anc))` register identification), which feed
    `embedAgreeOff_oracle_step` → `orbit_final_embedAgree` → the embedded-init
    `coset_route2_success_conditional` → the reduced-lookup coset-Shor success bound. -/
def inplaceReducedLookupCosetMul_shift
    (n anc N cm a numWin : Nat) (g : FormalRV.Framework.BaseUCom (n + anc)) : Prop :=
  ∃ B : Finset (Fin (2 ^ (n + anc))),
    -- off the wrap boundary `B`, the in-place oracle realizes the coset shift exactly:
    (∀ z : Nat, z < N → ∀ i : Fin (2 ^ (n + anc)), i ∉ B →
        uc_eval g (cosetState (2 ^ (n + anc)) N cm z) i 0
          = cosetState (2 ^ (n + anc)) N cm ((a * z) % N) i 0)
    -- and the wrap boundary carries Born mass `≤ numWin/2^cm` on each canonical input coset:
    ∧ (∀ z : Nat, z < N →
        bornWeightOn (cosetState (2 ^ (n + anc)) N cm z) B ≤ (numWin : ℝ) / 2 ^ cm)

end FormalRV.Shor.CosetEigenstate.InPlaceCosetSpec
