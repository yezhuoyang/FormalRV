import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement.PartialMeasurementBasis

namespace FormalRV.SQIRPort

/-- **Orthogonal-superposition partial-measurement formula**: for an
orthonormal family `β : Fin r → QState (2^q)` (the eigenstates of the
unmeasured register) and any family `α : Fin r → QState (2^p)` of
"phase register" outputs, the partial-measurement probability of a
basis outcome on the linear combination

      Ψ = ∑ j : Fin r, kron_vec (α j) (β j)

equals the orthogonality-collapsed sum

      ∑ j : Fin r, ‖α_j ⟨s, _⟩ 0‖².

The cross-terms `α_j · α_j'` (for `j ≠ j'`) vanish by orthonormality
of `β`. Proof: combines `prob_partial_meas_basis_vector` with
`Framework.normSq_sum_apply_orth` (Parseval) and the identification
`partial_meas_index = kron_vec_combine`. -/
theorem prob_partial_meas_basis_sum_kron_orth
    {p q r : Nat} (s : Nat) (h_s_lt : s < 2^p)
    (α : Fin r → QState (2^p)) (β : Fin r → QState (2^q))
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0) :
    prob_partial_meas (basis_vector (2^p) s)
        ((∑ j : Fin r, FormalRV.Framework.kron_vec (α j) (β j) :
           Matrix (Fin (2^(p+q))) (Fin 1) ℂ))
      = ∑ j : Fin r, Complex.normSq ((α j) ⟨s, h_s_lt⟩ 0) := by
  have h_dvd : (2^p : ℕ) ∣ (2^(p+q) : ℕ) := pow_dvd_pow 2 (Nat.le_add_right p q)
  have h_div : (2^(p+q)) / (2^p) = 2^q := by
    rw [pow_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos p)]
  rw [prob_partial_meas_basis_vector s h_s_lt h_dvd]
  -- Step 1: identify partial_meas_index with kron_vec_combine (same as kron_vec lemma).
  have h_idx_eq : ∀ y : Fin ((2^(p+q))/(2^p)),
      partial_meas_index h_dvd ⟨s, h_s_lt⟩ y
        = FormalRV.Framework.kron_vec_combine ⟨s, h_s_lt⟩ (Fin.cast h_div y) := by
    intro y
    apply Fin.ext
    show s * ((2^(p+q))/(2^p)) + y.val = s * 2^q + y.val
    have : s * ((2^(p+q))/(2^p)) = s * 2^q := by rw [h_div]
    omega
  -- Step 2: distribute sum into kron_vec_apply_combine.
  rw [show (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq ((∑ j : Fin r,
              FormalRV.Framework.kron_vec (α j) (β j) :
              Matrix (Fin (2^(p+q))) (Fin 1) ℂ)
              (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0))
        = (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq (∑ j : Fin r,
              (α j) ⟨s, h_s_lt⟩ 0 * (β j) (Fin.cast h_div y) 0)) by
      refine Finset.sum_congr rfl ?_
      intro y _
      congr 1
      simp only [Matrix.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_idx_eq y]
      exact FormalRV.Framework.kron_vec_apply_combine (α j) (β j) ⟨s, h_s_lt⟩ _]
  -- Step 3: reindex sum from Fin ((2^(p+q))/(2^p)) to Fin (2^q).
  rw [show (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq (∑ j : Fin r,
              (α j) ⟨s, h_s_lt⟩ 0 * (β j) (Fin.cast h_div y) 0))
        = (∑ y : Fin (2^q),
            Complex.normSq (∑ j : Fin r,
              (α j) ⟨s, h_s_lt⟩ 0 * (β j) y 0)) from by
      exact Equiv.sum_comp (Fin.castOrderIso h_div).toEquiv
        (fun y => Complex.normSq (∑ j : Fin r,
          (α j) ⟨s, h_s_lt⟩ 0 * (β j) y 0))]
  -- Step 4: apply Parseval.
  exact FormalRV.Framework.normSq_sum_apply_orth β h_orth
    (fun j => (α j) ⟨s, h_s_lt⟩ 0)

/-- **Scalar scaling for partial measurement** (Born-rule homogeneity):
scaling the joint state by `c ∈ ℂ` (applied pointwise as `fun i j =>
c * φ i j`) scales the partial-measurement probability by `‖c‖²`.

      prob_partial_meas ψ (c · φ)  =  ‖c‖² · prob_partial_meas ψ φ

The scaled state is written as `fun i j => c * φ i j` rather than
`c • φ` to avoid the `SMul ℂ (QState dim)` typeclass-synthesis issue
(`QState` is a `def` alias for `Matrix (Fin dim) (Fin 1) ℂ`, so the
Matrix SMul instance doesn't automatically lift). For callers using
`c • φ`, applying `Matrix.smul_apply` recovers the equivalence.

Proof: in the divisibility branch, push the scalar through the inner
sum (via `Finset.mul_sum` + `ring`), then use `Complex.normSq_mul`
to factor `‖c‖²` out of each `normSq` term, then `Finset.mul_sum` to
pull it out of the outer sum. The else-0 branch is trivial (`ring`). -/
theorem prob_partial_meas_smul_right
    {m_dim full_dim : Nat}
    (ψ : QState m_dim) (φ : QState full_dim) (c : ℂ) :
    prob_partial_meas ψ (fun i j => c * φ i j)
      = Complex.normSq c * prob_partial_meas ψ φ := by
  unfold prob_partial_meas
  by_cases h_dvd : m_dim ∣ full_dim
  · rw [dif_pos h_dvd, dif_pos h_dvd]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [show (∑ x : Fin m_dim, starRingEnd ℂ (ψ x 0) *
              (c * φ (Fin.cast (Nat.mul_div_cancel' h_dvd) _) 0))
          = c * ∑ x : Fin m_dim, starRingEnd ℂ (ψ x 0) *
              φ (Fin.cast (Nat.mul_div_cancel' h_dvd) _) 0 from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intros; ring]
    rw [Complex.normSq_mul]
  · rw [dif_neg h_dvd, dif_neg h_dvd]
    ring

/-- **`normSq` of `1/√r`** as a real cast: `‖1/√r‖² = 1/r`. Used to
turn the `(1/√r)`-scaling factor (from the standard orbit-state
normalization `|1⟩_n = (1/√r) · Σ_k |ψ_k⟩`) into the `(1/r)` weight
in the QPE peak-bound chain. -/
theorem normSq_one_div_sqrt (r : Nat) (h_r_pos : 0 < r) :
    Complex.normSq ((1 / (Real.sqrt r : ℂ))) = 1 / (r : ℝ) := by
  have h_r_R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h_r_pos
  rw [show (1 / (Real.sqrt r : ℂ)) = ((1 / Real.sqrt r : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.normSq_ofReal]
  field_simp
  rw [Real.sq_sqrt h_r_R.le]

/-- **QPE orthogonal-sum bridge with `1/r` factor**: the headline
combination of the scalar lemma + orthogonal-superposition formula +
QPE phase-state evaluation. Given:
* a family `k : Fin r → ℝ` of "true phases" (one per eigenstate),
* an orthonormal family `β : Fin r → QState (2^q)` of unmeasured-
  register eigenstates,

the partial-measurement probability of basis outcome `s` on the
normalized orbit-state-style superposition
`(1/√r) · ∑_j (qpe_phase_state p (k_j)) ⊗ |β_j⟩` equals the
average ideal QPE probability:

      (1/r) · ∑_j, qpe_prob p s (k_j).

Combined with `qpe_prob_peak_bound`, this gives the standard
`(1/r) · 4/π²` per-correctly-aligned-eigenstate lower bound — exactly
the per-outcome contribution at the heart of `QPE_MMI_correct`. -/
theorem prob_partial_meas_qpe_orth_sum
    {p q r : Nat} (s : Nat) (h_s_lt : s < 2^p) (h_r_pos : 0 < r)
    (k : Fin r → ℝ)
    (β : Fin r → QState (2^q))
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0) :
    prob_partial_meas (basis_vector (2^p) s)
        (fun i j => (1 / (Real.sqrt r : ℂ)) *
          ((∑ j_idx : Fin r,
             FormalRV.Framework.kron_vec
               (FormalRV.Framework.qpe_phase_state p (k j_idx)) (β j_idx) :
             Matrix (Fin (2^(p+q))) (Fin 1) ℂ) i j))
      = (1 / (r : ℝ)) * ∑ j_idx : Fin r,
          FormalRV.Framework.qpe_prob p s (k j_idx) := by
  -- Step 1: factor out the (1/√r) scalar via prob_partial_meas_smul_right.
  rw [prob_partial_meas_smul_right]
  -- Step 2: apply the orthogonal-superposition partial-meas formula.
  rw [prob_partial_meas_basis_sum_kron_orth s h_s_lt
        (fun j => FormalRV.Framework.qpe_phase_state p (k j)) β h_orth]
  -- Step 3: ‖qpe_phase_state at index‖² = qpe_prob.
  simp_rw [FormalRV.Framework.normSq_qpe_phase_state_apply]
  -- Step 4: ‖1/√r‖² = 1/r.
  rw [normSq_one_div_sqrt r h_r_pos]

end FormalRV.SQIRPort
