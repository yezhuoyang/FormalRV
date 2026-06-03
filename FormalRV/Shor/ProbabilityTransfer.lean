/-
  FormalRV.Shor.ProbabilityTransfer — the success-probability TRANSFER lemma.

  `probability_of_success` is DEFINED as
    `∑ x, r_found x · prob_partial_meas (basis_vector x) (Shor_final_state f)`,
  and `Shor_final_state f = QState.cast (uc_eval (QPE_var_lsb … f) · initial)`.
  So it depends on the oracle family `f` ONLY through the post-circuit STATE — i.e.
  only through the unitary `uc_eval (QPE_var_lsb … f)`.

  Hence "same denotation ⇒ same final state ⇒ (Born rule, `prob_partial_meas`,
  already in the repo) ⇒ same success probability" is a CONGRUENCE on the
  definition, not a deep gap.  These lemmas make that precise, and turn the
  conditional `success_transfer` in `PPMCompilerCorrectness` into an unconditional
  fact at the Shor layer: any compilation that preserves `uc_eval` (exactly)
  inherits the success bound — for ANY oracle family / Shor variant.

  Kernel-clean; no sorry, no new axiom.
-/
import FormalRV.Shor.Shor.Part1

namespace FormalRV.SQIRPort

/-- **Transfer lemma (state level).**  `probability_of_success` depends on the
    oracle family `f` only through the post-circuit state `Shor_final_state`, so
    equal final states ⇒ equal success probabilities. -/
theorem prob_of_success_congr
    (a r N m n anc : Nat)
    (f₁ f₂ : Nat → BaseUCom (n + anc))
    (h : Shor_final_state m n anc f₁ = Shor_final_state m n anc f₂) :
    probability_of_success a r N m n anc f₁
      = probability_of_success a r N m n anc f₂ := by
  simp only [probability_of_success, h]

/-- **Transfer lemma (operator / `uc_eval` level).**  If two oracle families
    produce the same circuit semantics under `QPE_var_lsb` on the Shor input
    state, their success probabilities agree.  Equality of the unitary action ⇒
    equality of the final state ⇒ equality of the success probability.

    This is exactly the "semantic correctness + Born rule ⇒ same success
    probability" transfer: a PPM compilation whose denotation equals `uc_eval`
    (on the nose) of the verified circuit inherits its success bound. -/
theorem prob_of_success_congr_via_uc_eval
    (a r N m n anc : Nat)
    (f₁ f₂ : Nat → BaseUCom (n + anc))
    (h : uc_eval (QPE_var_lsb m (n + anc) f₁) (Shor_initial_state m n anc)
       = uc_eval (QPE_var_lsb m (n + anc) f₂) (Shor_initial_state m n anc)) :
    probability_of_success a r N m n anc f₁
      = probability_of_success a r N m n anc f₂ := by
  apply prob_of_success_congr
  unfold Shor_final_state
  rw [h]

end FormalRV.SQIRPort
