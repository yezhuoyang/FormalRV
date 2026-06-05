/-
  FormalRV.Shor.Approx.GracefulDegradation — Phase C linchpin.

  The exact-oracle Shor headline uses `MultiplyCircuitProperty` = EXACT basis-state
  equality.  Gidney–Ekerå's algorithm instead uses the Zalka *coset representation*
  with an *approximate* (non-modular) adder.  To let that plug into the verified
  framework we need a "graceful degradation" bridge: if the final state produced by
  an approximate oracle is close (in ℓ²) to the ideal final state, then the
  measurement / success probabilities are close.

  This file proves the elementary linchpin (no Shor-specific machinery beyond
  `prob_partial_meas_basis_vector`): for a basis-vector first-register outcome,
  `prob_partial_meas` is Lipschitz in the joint state, with constant `2` on
  normalized states.  The proof is `prob_partial_meas (|s⟩) φ = ‖P_s φ‖²`
  (a block-slice of `|φ|²`), then `| ‖a‖² − ‖b‖² | ≤ ‖a−b‖·(‖a‖+‖b‖)` and
  Cauchy–Schwarz over the block.

  Kernel-clean; additive (does not touch the verified headline).
-/
import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement

namespace FormalRV.Shor.Approx

open scoped BigOperators
open FormalRV.SQIRPort

/-- Local ℓ²-norm of a column-vector state `φ : QState d`. -/
noncomputable def pmNorm {d : Nat} (φ : QState d) : ℝ :=
  Real.sqrt (∑ i, Complex.normSq (φ i 0))

/-- Local ℓ²-distance between two states (pointwise; avoids needing a `Sub`
    instance on the `def`-wrapped `QState`). -/
noncomputable def pmDist {d : Nat} (φ ψ : QState d) : ℝ :=
  Real.sqrt (∑ i, Complex.normSq (φ i 0 - ψ i 0))

lemma pmNorm_nonneg {d : Nat} (φ : QState d) : 0 ≤ pmNorm φ := Real.sqrt_nonneg _

lemma pmDist_nonneg {d : Nat} (φ ψ : QState d) : 0 ≤ pmDist φ ψ := Real.sqrt_nonneg _

lemma pmNorm_sq {d : Nat} (φ : QState d) :
    (pmNorm φ) ^ 2 = ∑ i, Complex.normSq (φ i 0) := by
  unfold pmNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)]

lemma pmDist_sq {d : Nat} (φ ψ : QState d) :
    (pmDist φ ψ) ^ 2 = ∑ i, Complex.normSq (φ i 0 - ψ i 0) := by
  unfold pmDist
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)]

/-- The selected-slice index map is injective in the second-register index. -/
lemma partial_meas_index_inj {m_dim full_dim : Nat} (h_dvd : m_dim ∣ full_dim)
    (s : Fin m_dim) : Function.Injective (partial_meas_index h_dvd s) := by
  intro y₁ y₂ h
  have hval : s.val * (full_dim / m_dim) + y₁.val
            = s.val * (full_dim / m_dim) + y₂.val := by
    have := congrArg Fin.val h
    simpa [partial_meas_index, Fin.coe_cast] using this
  exact Fin.ext (by omega)

/-- **Projector is norm-nonincreasing**: summing a nonneg function over the
    selected slice is `≤` summing over the whole register. -/
lemma block_sum_le {m_dim full_dim : Nat} (s : Nat) (h_s_lt : s < m_dim)
    (h_dvd : m_dim ∣ full_dim) (g : Fin full_dim → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ∑ y : Fin (full_dim / m_dim), g (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y)
      ≤ ∑ i, g i := by
  rw [← Finset.sum_image (g := partial_meas_index h_dvd ⟨s, h_s_lt⟩) (f := g)
        ((partial_meas_index_inj h_dvd ⟨s, h_s_lt⟩).injOn)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hg i)

/-- Pointwise: `|‖a‖² − ‖b‖²| ≤ ‖a−b‖·(‖a‖+‖b‖)` for complex amplitudes. -/
lemma normSq_sub_le (a b : ℂ) :
    |Complex.normSq a - Complex.normSq b| ≤ ‖a - b‖ * (‖a‖ + ‖b‖) := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      show ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by ring, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖a‖ + ‖b‖)]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le a b) (by positivity)

/-- **Graceful-degradation linchpin.**  For a basis-vector first-register outcome
    `|s⟩`, the partial-measurement probability is `2`-Lipschitz in the joint state
    over normalized states:
      `|P(s | φ) − P(s | ψ)| ≤ 2 · ‖φ − ψ‖`.
    Hence an approximate oracle whose final state is `δ`-close to the ideal one
    changes each measurement probability by at most `2δ`. -/
theorem prob_partial_meas_diff_le_two_dist {m_dim full_dim : Nat} (s : Nat)
    (h_s_lt : s < m_dim) (h_dvd : m_dim ∣ full_dim) (φ ψ : QState full_dim)
    (hφ : pmNorm φ ≤ 1) (hψ : pmNorm ψ ≤ 1) :
    |prob_partial_meas (basis_vector m_dim s) φ
        - prob_partial_meas (basis_vector m_dim s) ψ|
      ≤ 2 * pmDist φ ψ := by
  rw [prob_partial_meas_basis_vector s h_s_lt h_dvd φ,
      prob_partial_meas_basis_vector s h_s_lt h_dvd ψ, ← Finset.sum_sub_distrib]
  -- f y = ‖Δ at slice y‖,  G y = ‖φ slice‖ + ‖ψ slice‖
  set f : Fin (full_dim / m_dim) → ℝ :=
    fun y => ‖φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0
              - ψ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0‖ with hf
  set G : Fin (full_dim / m_dim) → ℝ :=
    fun y => ‖φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0‖
           + ‖ψ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0‖ with hG
  -- Step 1: |Σ Δ| ≤ Σ |Δ| ≤ Σ f·G
  have step1 :
      |∑ y, (Complex.normSq (φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0)
              - Complex.normSq (ψ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0))|
        ≤ ∑ y, f y * G y := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    simp only [hf, hG]
    exact normSq_sub_le _ _
  -- Step 2: Cauchy–Schwarz  (Σ f·G)² ≤ (Σ f²)(Σ G²)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f G
  -- Σ f² ≤ pmDist²
  have hf2 : ∑ y, (f y) ^ 2 ≤ (pmDist φ ψ) ^ 2 := by
    rw [pmDist_sq]
    have hrw : ∀ y, (f y) ^ 2
        = Complex.normSq (φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0
                          - ψ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0) := by
      intro y; simp only [hf]; rw [Complex.normSq_eq_norm_sq]
    rw [Finset.sum_congr rfl (fun y _ => hrw y)]
    exact block_sum_le s h_s_lt h_dvd (fun i => Complex.normSq (φ i 0 - ψ i 0))
      (fun _ => Complex.normSq_nonneg _)
  -- Σ G² ≤ 4  (each block sum ≤ pmNorm² ≤ 1)
  have hG2 : ∑ y, (G y) ^ 2 ≤ 4 := by
    have hpt : ∀ y, (G y) ^ 2
        ≤ 2 * Complex.normSq (φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0)
        + 2 * Complex.normSq (ψ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0) := by
      intro y
      simp only [hG]
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0),
                 norm_nonneg (ψ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0),
                 sq_nonneg (‖φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0‖
                          - ‖ψ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0‖)]
    refine (Finset.sum_le_sum fun y _ => hpt y).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hbφ : ∑ y, Complex.normSq (φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0) ≤ 1 := by
      refine le_trans (block_sum_le s h_s_lt h_dvd (fun i => Complex.normSq (φ i 0))
        (fun _ => Complex.normSq_nonneg _)) ?_
      rw [← pmNorm_sq]; nlinarith [pmNorm_nonneg φ]
    have hbψ : ∑ y, Complex.normSq (ψ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0) ≤ 1 := by
      refine le_trans (block_sum_le s h_s_lt h_dvd (fun i => Complex.normSq (ψ i 0))
        (fun _ => Complex.normSq_nonneg _)) ?_
      rw [← pmNorm_sq]; nlinarith [pmNorm_nonneg ψ]
    linarith
  -- Combine via Cauchy–Schwarz and √-monotonicity
  have hsum_nn : 0 ≤ ∑ y, f y * G y :=
    Finset.sum_nonneg fun y _ => mul_nonneg (norm_nonneg _) (by positivity)
  have hprod : (∑ y, f y * G y) ^ 2 ≤ (2 * pmDist φ ψ) ^ 2 := by
    refine hcs.trans ?_
    calc (∑ y, (f y) ^ 2) * (∑ y, (G y) ^ 2)
        ≤ (pmDist φ ψ) ^ 2 * 4 :=
          mul_le_mul hf2 hG2 (Finset.sum_nonneg fun y _ => sq_nonneg _) (sq_nonneg _)
      _ = (2 * pmDist φ ψ) ^ 2 := by ring
  have hfinal : ∑ y, f y * G y ≤ 2 * pmDist φ ψ := by
    have := Real.sqrt_le_sqrt hprod
    rwa [Real.sqrt_sq hsum_nn,
         Real.sqrt_sq (by have := pmDist_nonneg φ ψ; linarith : (0:ℝ) ≤ 2 * pmDist φ ψ)] at this
  exact step1.trans hfinal

end FormalRV.Shor.Approx
