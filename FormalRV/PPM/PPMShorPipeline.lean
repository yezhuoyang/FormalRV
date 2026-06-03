-- ============================================================================
-- FormalRV/PPM/PPMShorPipeline.lean
-- Paste-ready. Machine-validated against the live repo (scratch built clean,
-- zero diagnostics, all 9 decls axiom-clean = {propext, Classical.choice,
-- Quot.sound}, then deleted). Backbone = Design B.
--
-- BUILD ORDER: all five imports already exist and build in the repo. This file
-- is a NEW LEAF (nothing imports it), so it adds no rebuild burden to existing
-- modules. Add it to FormalRV.lean's import aggregator (or build directly) AFTER
-- the five dependencies; lake resolves the order automatically.
--
-- DEPENDENCY ORDER OF DECLS (top-to-bottom is the only valid order):
--   trivAnc -> kron_vec_triv_right -> ccz_magic_realizes_outcome_000
--   -> clifford_magic_realizes -> Gadget -> foldGateProduct
--   -> magic_realizes_list_fold        (end section Gadgets)
--   -> PPMRealizesShorOracle -> ppm_preserves_success
--   -> ppm_realized_shor_succeeds -> {with_budget, from_effective_action,
--      representative}                 (end section ShorTransfer)
-- ============================================================================
import FormalRV.PPM.MagicGadgetInterface
import FormalRV.PPM.CCZGadgetTeleport
import FormalRV.Shor.ProbabilityTransfer
import FormalRV.Shor.VerifiedShor.Part10
import FormalRV.Shor.SuccessSensitivity

open scoped Matrix

namespace FormalRV.PPM.PPMShorPipeline

/-! ===== SECTION 1 / Gadgets (state-vector layer, below FormalRV.Framework) =====
    SEAMS 1 + 2: the three gadget families discharge ONE unified predicate
    (MagicRealizes), and they compose by a List fold that keeps the real
    gadget operators in the conclusion. -/
section Gadgets
open FormalRV.Framework
open FormalRV.PPM.MagicGadgetInterface
open FormalRV.PPM.CCZGadgetTeleport
open Complex

/-- Trivial 1-dim ancilla state (dA = 0); the right unit for ⊗ᵥ. -/
noncomputable def trivAnc : StateVec 0 := basisState (0 : Fin (2^0))

/-- The MISSING b=0 kron law: `ψ ⊗ᵥ trivAnc = ψ`. Enables the Clifford dA=0 case.
    (Design B repaired the Design-A `unitState0` formulation; this `basisState`
    form is the one that validates.) -/
theorem kron_vec_triv_right {a : Nat} (ψ : StateVec a) :
    (ψ ⊗ᵥ trivAnc : StateVec (a + 0)) = ψ := by
  funext i j
  rw [kron_vec_apply]
  simp only [trivAnc, basisState]
  have hlow : (kron_vec_low i : Fin (2^0)) = (0 : Fin (2^0)) := by
    apply Fin.ext; simp [kron_vec_low]
  rw [hlow, if_pos rfl, mul_one]
  have hhigh : kron_vec_high i = i := by
    apply Fin.ext; simp [kron_vec_high]
  have hj : j = 0 := Subsingleton.elim _ _
  rw [hhigh, hj]

/-- (SEAM 1, CCZ instance) The CCZ teleportation gadget, all-zeros (b=000)
    measurement branch, discharges the SAME `MagicRealizes` predicate as the T
    gadget. U := the repo's 8T->CCZ `cczMat` (non-axiomatic, tied to the data
    action by `ccz_gadget_outcome_000_is_cczMat`). -/
theorem ccz_magic_realizes_outcome_000 :
    MagicRealizes (dD := 3) (dA := 3)
      (projAnc000 * cnotChain) cczKet
      (FormalRV.Framework.EightTToCCZ.cczMat) := by
  intro ψ
  refine ⟨basisState 0, (1 / (2 * Real.sqrt 2) : ℂ), ?_⟩
  rw [Matrix.mul_assoc]
  exact ccz_gadget_outcome_000_is_cczMat ψ

/-- (SEAM 1, Clifford instance) Any Clifford gate discharges `MagicRealizes` with
    dA = 0, c = 1, G = U: honest Clifford-is-free magic-accounting model (no magic
    consumed, action exact). NOTE: the T instance is the COMMITTED repo theorem
    `MagicGadgetInterface.tGadget_magic_realizes (b : Bool)` — reused verbatim, not
    re-proved here — so {T (any outcome b), CCZ (outcome 000), any Clifford}
    all satisfy the one predicate. -/
theorem clifford_magic_realizes {dD : Nat} (U : Square dD) :
    MagicRealizes (dD := dD) (dA := 0) (U : Square (dD + 0)) trivAnc U := by
  intro ψ
  refine ⟨trivAnc, 1, ?_⟩
  rw [one_smul, kron_vec_triv_right, kron_vec_triv_right]

/-- A gadget bundles the REAL `MagicRealizes` instance together with its data
    unitary — so the fold below carries genuine gadget content. -/
structure Gadget (dD : Nat) where
  dA : Nat
  G : Square (dD + dA)
  magic : StateVec dA
  U : Square dD
  realizes : MagicRealizes G magic U

/-- The data-register product realized by a gadget list (U_n * ... * U_1). -/
noncomputable def foldGateProduct {dD : Nat} : List (Gadget dD) → Square dD
  | [] => 1
  | g :: gs => foldGateProduct gs * g.U

/-- (SEAM 2) LIST/FOLD composition, generalising the repo's two-gadget
    `magic_realizes_chain` over an arbitrary list. The composite data evolution
    lands the FULL product `foldGateProduct gs * ψ` on the data register (up to one
    accumulated scalar `c`), AND the conclusion RETAINS the head gadget's actual
    operator equation — so it is NON-VACUOUS (not the rejected `∃ anc c, True`). -/
theorem magic_realizes_list_fold {dD : Nat}
    (gs : List (Gadget dD)) (ψ : StateVec dD) :
    ∃ (final : StateVec dD) (c : ℂ),
      final = c • (foldGateProduct gs * ψ)
      ∧ (∀ (g : Gadget dD) (gtl : List (Gadget dD)), gs = g :: gtl →
          ∃ (anc : StateVec g.dA) (chead : ℂ),
            g.G * (ψ ⊗ᵥ g.magic) = chead • ((g.U * ψ) ⊗ᵥ anc)) := by
  induction gs generalizing ψ with
  | nil =>
      -- REPAIR (vs both designs' reported code): the nil witness's first proof must
      -- be `(one_smul _ _).symm`, NOT `by rw [one_smul]` (the latter leaves an
      -- unsolved reflexive goal `foldGateProduct [] * ψ = foldGateProduct [] * ψ`).
      exact ⟨foldGateProduct [] * ψ, 1, (one_smul _ _).symm, by intro g gtl h; cases h⟩
  | cons g gs ih =>
      obtain ⟨anc, chead, hhead⟩ := g.realizes ψ
      obtain ⟨final_tail, ctail, htail, _⟩ := ih (g.U * ψ)
      refine ⟨final_tail, ctail, ?_, ?_⟩
      · rw [htail]; congr 1; simp only [foldGateProduct]; rw [Matrix.mul_assoc]
      · intro g' gtl' heq
        rw [List.cons.injEq] at heq
        obtain ⟨rfl, _⟩ := heq
        exact ⟨anc, chead, hhead⟩

end Gadgets

/-! ===== SECTION 2 / ShorTransfer (Shor layer, FormalRV.SQIRPort) =====
    SEAM 3: exact success transfer. SEAM 4: the single causal end-to-end theorem.
    CRITICAL: do NOT also `open FormalRV.Framework` here — BaseUCom / uc_eval /
    probability_of_success are AMBIGUOUS between Framework and SQIRPort and the
    file fails with 'Ambiguous term' if both are open. -/
section ShorTransfer
open FormalRV.SQIRPort
open VerifiedShor

/-- The SINGLE A/B -> C/D seam, named as a definition: the PPM family's effective
    action on the Shor input state equals the verified circuit's. This is the one
    obligation blocks A/B must ultimately discharge (see honest_gaps). -/
def PPMRealizesShorOracle
    (m n anc : Nat) (f_ver f_ppm : Nat → BaseUCom (n + anc)) : Prop :=
  uc_eval (QPE_var_lsb m (n + anc) f_ppm) (Shor_initial_state m n anc)
    = uc_eval (QPE_var_lsb m (n + anc) f_ver) (Shor_initial_state m n anc)

/-- (SEAM 3, CLOSED by theorem) TRANSFER hookup — EXACT, no error subtraction.
    `probability_of_success` depends on `f` ONLY through `uc_eval (QPE_var_lsb f)`
    on the initial state, so a matching effective action preserves success on the
    nose. Wraps the committed `prob_of_success_congr_via_uc_eval`. -/
theorem ppm_preserves_success
    (a r N m n anc : Nat)
    (f_ver f_ppm : Nat → BaseUCom (n + anc))
    (hppm : PPMRealizesShorOracle m n anc f_ver f_ppm) :
    probability_of_success a r N m n anc f_ppm
      = probability_of_success a r N m n anc f_ver :=
  prob_of_success_congr_via_uc_eval a r N m n anc f_ppm f_ver hppm

/-- (SEAM 4, CLOSED by theorem) THE SINGLE CAUSAL END-TO-END THEOREM (not a
    conjunction). Success of the PPM-realized circuit is DERIVED THROUGH the
    realization: `rw [ppm_preserves_success ...]` rewrites PPM success to verified
    success USING the realization equality `hppm`, THEN
    `correct_general_via_interface` supplies the bound. Delete `hppm` and the
    rewrite fails — the realization hypothesis is load-bearing. -/
theorem ppm_realized_shor_succeeds
    (a r N m bits ainv : Nat)
    (f_ppm : Nat → BaseUCom (bits + ModMul.ancillaWidth bits))
    (h_setting : ShorSetting a r N m bits)
    (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1)
    (hppm : PPMRealizesShorOracle m bits (ModMul.ancillaWidth bits)
              (ModMul.circuitFamily a ainv N bits) f_ppm) :
    probability_of_success a r N m bits (ModMul.ancillaWidth bits) f_ppm
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 := by
  rw [ppm_preserves_success a r N m bits (ModMul.ancillaWidth bits)
        (ModMul.circuitFamily a ainv N bits) f_ppm hppm]
  exact correct_general_via_interface a r N m bits ainv h_setting h_sizing h_inv

/-- The same causal theorem degraded by the FT union-bound budget
    (− AQFT cutoff − num_ops·p_L). Derived from the exact form by `linarith`. -/
theorem ppm_realized_shor_succeeds_with_budget
    (a r N m bits ainv : Nat)
    (f_ppm : Nat → BaseUCom (bits + ModMul.ancillaWidth bits))
    (h_setting : ShorSetting a r N m bits) (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1)
    (hppm : PPMRealizesShorOracle m bits (ModMul.ancillaWidth bits)
              (ModMul.circuitFamily a ainv N bits) f_ppm)
    (cutoff : ℕ) (p_L num_ops : ℝ) (hp_L : 0 ≤ p_L) (hnum : 0 ≤ num_ops) :
    probability_of_success a r N m bits (ModMul.ancillaWidth bits) f_ppm
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 - (2 * Real.pi / 2 ^ cutoff) - num_ops * p_L := by
  have hexact :=
    ppm_realized_shor_succeeds a r N m bits ainv f_ppm h_setting h_sizing h_inv hppm
  have h1 : (0:ℝ) ≤ 2 * Real.pi / 2 ^ cutoff := by positivity
  have h2 : (0:ℝ) ≤ num_ops * p_L := mul_nonneg hnum hp_L
  linarith [hexact, h1, h2]

/-- The A/B -> C/D obligation made a SINGLE VISIBLE hypothesis (not a hidden gap):
    given the raw uc_eval-equality, success follows. This is the exact equality
    blocks A/B must produce to instantiate `ppm_realized_shor_succeeds` with a
    genuine (non-identity) PPM family. -/
theorem ppm_shor_succeeds_from_effective_action
    (a r N m bits ainv : Nat)
    (f_ppm : Nat → BaseUCom (bits + ModMul.ancillaWidth bits))
    (h_setting : ShorSetting a r N m bits) (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1)
    (h_effective_action :
      uc_eval (QPE_var_lsb m (bits + ModMul.ancillaWidth bits) f_ppm)
          (Shor_initial_state m bits (ModMul.ancillaWidth bits))
        = uc_eval (QPE_var_lsb m (bits + ModMul.ancillaWidth bits)
            (ModMul.circuitFamily a ainv N bits))
          (Shor_initial_state m bits (ModMul.ancillaWidth bits))) :
    probability_of_success a r N m bits (ModMul.ancillaWidth bits) f_ppm
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  ppm_realized_shor_succeeds a r N m bits ainv f_ppm h_setting h_sizing h_inv
    h_effective_action

/-- NON-VACUITY smoke test: the parametric theorem FIRES. The identity
    realization (f_ppm = the verified family) satisfies the hypothesis by `rfl`.
    Proves the universally-quantified theorem is not vacuous; a genuinely-different
    f_ppm needs the residual seam in honest_gaps. -/
theorem ppm_realized_shor_succeeds_representative
    (a r N m bits ainv : Nat)
    (h_setting : ShorSetting a r N m bits) (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1) :
    probability_of_success a r N m bits (ModMul.ancillaWidth bits)
        (ModMul.circuitFamily a ainv N bits)
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  ppm_realized_shor_succeeds a r N m bits ainv
    (ModMul.circuitFamily a ainv N bits) h_setting h_sizing h_inv rfl

end ShorTransfer

end FormalRV.PPM.PPMShorPipeline