/-
  FormalRV.Shor.Approx.SuccessStable — Phase C, lift the per-outcome bridge to the
  whole success quantity.

  `probability_of_success` is `∑_{x<2^m} r_found(x)·prob_partial_meas(|x⟩, final)`.
  Since `r_found ∈ {0,1}` (it never amplifies) and each measurement probability is
  `2`-Lipschitz in the final state (`GracefulDegradation`), two oracle families whose
  final states are `δ`-close in ℓ² have success probabilities within `2^m · 2δ`.
  This is the "graceful degradation of the success probability" the roadmap names
  for the approximate (coset) oracle.

  Kernel-clean; additive.
-/
import FormalRV.Shor.Approx.GracefulDegradation

namespace FormalRV.Shor.Approx

open scoped BigOperators
open FormalRV.SQIRPort

/-- `2^m` divides the full Shor register `2^m · 2^n · 2^anc`. -/
lemma shor_dvd (m n anc : Nat) : (2 ^ m) ∣ (2 ^ m * 2 ^ n * 2 ^ anc) :=
  ⟨2 ^ n * 2 ^ anc, by ring⟩

/-- **Success-probability stability.**  If the approximate family `f` and the ideal
    family `g` produce final states within ℓ²-distance `δ` (both normalized), then
    their success probabilities differ by at most `2^m · 2δ`. -/
theorem probability_of_success_stable (a r N m n anc : Nat)
    (f g : Nat → BaseUCom (n + anc)) (δ : ℝ)
    (hf : pmNorm (Shor_final_state m n anc f) ≤ 1)
    (hg : pmNorm (Shor_final_state m n anc g) ≤ 1)
    (hclose : pmDist (Shor_final_state m n anc f) (Shor_final_state m n anc g) ≤ δ) :
    |probability_of_success a r N m n anc f - probability_of_success a r N m n anc g|
      ≤ (2 ^ m : ℝ) * (2 * δ) := by
  unfold probability_of_success
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hbound : ∀ x ∈ Finset.range (2 ^ m),
      |r_found x m r a N
          * prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc f)
        - r_found x m r a N
          * prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc g)|
        ≤ 2 * δ := by
    intro x hx
    have hx' : x < 2 ^ m := Finset.mem_range.mp hx
    have hrf0 : 0 ≤ r_found x m r a N := by unfold r_found; split_ifs <;> norm_num
    have hrf1 : r_found x m r a N ≤ 1 := by unfold r_found; split_ifs <;> norm_num
    set pf := prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc f) with hpf
    set pg := prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc g) with hpg
    rw [← mul_sub, abs_mul, abs_of_nonneg hrf0]
    have hbridge := prob_partial_meas_diff_le_two_dist
      (m_dim := 2 ^ m) (full_dim := 2 ^ m * 2 ^ n * 2 ^ anc)
      x hx' (shor_dvd m n anc)
      (Shor_final_state m n anc f) (Shor_final_state m n anc g) hf hg
    have hpm : |pf - pg| ≤ 2 * δ := hbridge.trans (by linarith)
    calc r_found x m r a N * |pf - pg|
        ≤ 1 * (2 * δ) := mul_le_mul hrf1 hpm (abs_nonneg _) (by norm_num)
      _ = 2 * δ := by ring
  refine (Finset.sum_le_sum hbound).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **Phase C headline (proved).**  If the ideal oracle family `g` achieves a
    success bound `B`, and the approximate family `f` produces a final state within
    ℓ²-distance `δ` of `g`'s (both normalized), then `f` still succeeds with
    probability `≥ B − 2^m · 2δ`.  The exact-oracle path is the `δ = 0` special
    case (no degradation); the coset/approximate path pays the `2^m · 2δ` toll,
    where `δ` is supplied by the named coset obligations (`CosetObligations`). -/
theorem shor_success_approx (a r N m n anc : Nat) (f g : Nat → BaseUCom (n + anc))
    (B δ : ℝ)
    (hf : pmNorm (Shor_final_state m n anc f) ≤ 1)
    (hg : pmNorm (Shor_final_state m n anc g) ≤ 1)
    (h_ideal : B ≤ probability_of_success a r N m n anc g)
    (hclose : pmDist (Shor_final_state m n anc f) (Shor_final_state m n anc g) ≤ δ) :
    B - (2 ^ m : ℝ) * (2 * δ) ≤ probability_of_success a r N m n anc f := by
  have hstab := probability_of_success_stable a r N m n anc f g δ hf hg hclose
  have h := (abs_le.mp hstab).1
  linarith

end FormalRV.Shor.Approx
