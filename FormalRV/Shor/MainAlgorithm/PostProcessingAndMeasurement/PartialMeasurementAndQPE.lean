import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement.RFoundRecoveryGeneric

namespace FormalRV.SQIRPort

/-! ## Partial-measurement API (basis-vector first register)

API lemmas for `prob_partial_meas` when the first register is a
computational basis state `|s⟩`. These reduce the inner-product sum to
a single non-zero contribution (at `x.val = s`), giving a clean closed
form: the partial-measurement probability is the sum of squared
amplitudes over the "selected slice" of the joint state. -/

/-- **Selected-slice index** for partial measurement: maps a "first
register" outcome `s : Fin m_dim` and "second register" basis index
`y : Fin (full_dim / m_dim)` to the joint-register basis index
`s · (full_dim / m_dim) + y` in `Fin full_dim`. The cast through
`Fin (m_dim * (full_dim / m_dim))` uses the divisibility hypothesis. -/
noncomputable def partial_meas_index {m_dim full_dim : Nat}
    (h_dvd : m_dim ∣ full_dim) (s : Fin m_dim)
    (y : Fin (full_dim / m_dim)) : Fin full_dim :=
  Fin.cast (Nat.mul_div_cancel' h_dvd) ⟨s.val * (full_dim / m_dim) + y.val, by
    have hx : s.val < m_dim := s.isLt
    have hy : y.val < full_dim / m_dim := y.isLt
    calc s.val * (full_dim / m_dim) + y.val
        < s.val * (full_dim / m_dim) + (full_dim / m_dim) := by omega
      _ = (s.val + 1) * (full_dim / m_dim) := by ring
      _ ≤ m_dim * (full_dim / m_dim) := Nat.mul_le_mul_right _ hx⟩

/-- **Partial-measurement formula for a basis-vector outcome**: when
the first-register outcome is `basis_vector m_dim s` with `s < m_dim`,
the inner-product sum collapses to a single term (the contribution
at `x.val = s`), and the partial-measurement probability becomes a
sum of squared amplitudes along the selected slice of the joint state.

      prob_partial_meas (basis_vector m_dim s) φ
        = ∑ y : Fin (full_dim / m_dim),
            ‖φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y)‖²
-/
theorem prob_partial_meas_basis_vector
    {m_dim full_dim : Nat} (s : Nat) (h_s_lt : s < m_dim)
    (h_dvd : m_dim ∣ full_dim) (φ : QState full_dim) :
    prob_partial_meas (basis_vector m_dim s) φ
      = ∑ y : Fin (full_dim / m_dim),
          Complex.normSq (φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0) := by
  unfold prob_partial_meas
  rw [dif_pos h_dvd]
  refine Finset.sum_congr rfl ?_
  intro y _
  congr 1
  -- ∑ x : Fin m_dim, conj(basis x 0) · φ(...) = φ(...) at x = s.
  rw [Finset.sum_eq_single (⟨s, h_s_lt⟩ : Fin m_dim)]
  · -- main case: x = ⟨s, h_s_lt⟩, basis_vector at s is 1.
    show starRingEnd ℂ ((basis_vector m_dim s) ⟨s, h_s_lt⟩ 0) *
          φ (Fin.cast (Nat.mul_div_cancel' h_dvd) _) 0
        = φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0
    show starRingEnd ℂ (if (⟨s, h_s_lt⟩ : Fin m_dim).val = s then (1 : ℂ) else 0)
          * φ _ 0 = _
    simp [partial_meas_index]
  · -- other cases: x ≠ ⟨s, h_s_lt⟩, so x.val ≠ s, basis is 0.
    intro x _ h_ne
    show starRingEnd ℂ ((basis_vector m_dim s) x 0) * φ _ 0 = 0
    show starRingEnd ℂ (if x.val = s then (1 : ℂ) else 0) * φ _ 0 = 0
    have h_x_ne : x.val ≠ s := fun heq => h_ne (Fin.ext heq)
    simp [h_x_ne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Partial-measurement of basis-vector on a tensor-product state**:
when the joint state factors as `kron_vec a b`, the partial-measurement
probability at a first-register basis-vector outcome reduces to the
single squared amplitude of `a` at that outcome, multiplied by the
total `‖b‖²` of the second-register state:

      prob_partial_meas (basis_vector (2^p) s) (kron_vec a b)
        = ‖a_s‖² · ∑ y : Fin (2^q), ‖b_y‖²

For a normalized second-register state (`Pure_State_Vector b`), the
sum is `1` and the partial-meas reduces to just `‖a_s‖²` — exactly the
"distribution on the first register, ignoring the second" reading of
partial measurement. Proof: combines `prob_partial_meas_basis_vector`
with the index identity `partial_meas_index = kron_vec_combine` and
`Equiv.sum_comp` for the dimensional reindex. -/
theorem prob_partial_meas_basis_kron_vec
    {p q : Nat} (s : Nat) (h_s_lt : s < 2^p)
    (a : QState (2^p)) (b : QState (2^q)) :
    prob_partial_meas (basis_vector (2^p) s)
        (FormalRV.Framework.kron_vec a b)
      = Complex.normSq (a ⟨s, h_s_lt⟩ 0) *
        ∑ y : Fin (2^q), Complex.normSq (b y 0) := by
  have h_dvd : (2^p : ℕ) ∣ (2^(p+q) : ℕ) := pow_dvd_pow 2 (Nat.le_add_right p q)
  have h_div : (2^(p+q)) / (2^p) = 2^q := by
    rw [pow_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos p)]
  rw [prob_partial_meas_basis_vector s h_s_lt h_dvd]
  -- Step 1: identify partial_meas_index with kron_vec_combine.
  have h_idx_eq : ∀ y : Fin ((2^(p+q))/(2^p)),
      partial_meas_index h_dvd ⟨s, h_s_lt⟩ y
        = FormalRV.Framework.kron_vec_combine ⟨s, h_s_lt⟩ (Fin.cast h_div y) := by
    intro y
    apply Fin.ext
    show s * ((2^(p+q))/(2^p)) + y.val = s * 2^q + y.val
    have : s * ((2^(p+q))/(2^p)) = s * 2^q := by rw [h_div]
    omega
  -- Step 2: apply kron_vec_normSq_apply_combine pointwise.
  rw [show (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq ((FormalRV.Framework.kron_vec a b)
                              (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0))
        = (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq (a ⟨s, h_s_lt⟩ 0) *
            Complex.normSq (b (Fin.cast h_div y) 0)) by
      refine Finset.sum_congr rfl ?_
      intro y _
      rw [h_idx_eq y]
      exact FormalRV.Framework.kron_vec_normSq_apply_combine a b ⟨s, h_s_lt⟩ _]
  -- Step 3: factor out normSq(a_s) and reindex via Fin.castOrderIso h_div.
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Fin.castOrderIso h_div).toEquiv
    (fun y => Complex.normSq (b y 0))

/-- **Partial-measurement of `qpe_phase_state ⊗ eigen` gives the ideal
analytic probability**: when the QPE-output state is the tensor product
of the ideal QPE phase register `qpe_phase_state m θ` and any
data-register state `ψ_eigen`, the partial-measurement probability at
the phase-register outcome `y` is exactly the ideal `qpe_prob m y θ`,
scaled by the total squared amplitude of `ψ_eigen` (which is `1` when
`ψ_eigen` is `Pure_State_Vector`).

      prob_partial_meas (basis_vector (2^m) y)
          (kron_vec (qpe_phase_state m θ) ψ_eigen)
        = qpe_prob m y θ · ∑ z, ‖ψ_eigen_z‖²

This is the kernel-clean connection between the actual
partial-measurement probability (left side, lives in the Shor port) and
the abstract analytic QPE probability (right side, lives in
`Framework.QPEAmplitude`). For normalized `ψ_eigen`, this reduces to
`qpe_prob m y θ`. -/
theorem prob_partial_meas_qpe_phase_state_kron
    {m anc : Nat} (y : Nat) (h_y_lt : y < 2^m) (θ : ℝ)
    (ψ_eigen : QState (2^anc)) :
    prob_partial_meas (basis_vector (2^m) y)
        (FormalRV.Framework.kron_vec
          (FormalRV.Framework.qpe_phase_state m θ) ψ_eigen)
      = FormalRV.Framework.qpe_prob m y θ *
        ∑ z : Fin (2^anc), Complex.normSq (ψ_eigen z 0) := by
  rw [prob_partial_meas_basis_kron_vec y h_y_lt
        (FormalRV.Framework.qpe_phase_state m θ) ψ_eigen]
  rw [FormalRV.Framework.normSq_qpe_phase_state_apply]

/-- **Corollary: normalized eigenstate case**. When `ψ_eigen` is a
`Pure_State_Vector` (`∑ ‖ψ_eigen_z‖² = 1`), the partial-measurement
probability is exactly the ideal analytic `qpe_prob m y θ`. -/
theorem prob_partial_meas_qpe_phase_state_kron_pure
    {m anc : Nat} (y : Nat) (h_y_lt : y < 2^m) (θ : ℝ)
    (ψ_eigen : QState (2^anc))
    (h_pure : FormalRV.Framework.Pure_State_Vector ψ_eigen) :
    prob_partial_meas (basis_vector (2^m) y)
        (FormalRV.Framework.kron_vec
          (FormalRV.Framework.qpe_phase_state m θ) ψ_eigen)
      = FormalRV.Framework.qpe_prob m y θ := by
  rw [prob_partial_meas_qpe_phase_state_kron y h_y_lt θ ψ_eigen]
  unfold FormalRV.Framework.Pure_State_Vector at h_pure
  rw [h_pure, mul_one]

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

/-- **`QPE_MMI_correct_from_orbit`** (added 2026-05-24): state-
factorization conditional form of `QPE_MMI_correct`. Given an
orthonormal eigenstate family `β j` (for the unmeasured register) and
the orbit-state superposition shape

  `(1/√r) · ∑ j_idx : Fin r,
     (qpe_phase_state m (j_idx/r)) ⊗ (β j_idx)`

for the joint output state, the QPE peak bound `≥ 4/(π²·r)` at outcome
`s_closest m k r` follows. Closes the analytic half of the
`QPE_MMI_correct` axiom; the remaining (semantic / circuit) half is
showing that `Shor_final_state m n anc f` actually has this form,
which requires the circuit semantics of `QPE_var` plus the modular
multiplier's eigenstate spectrum (deferred to Phase 4).

Kernel-clean: depends on `prob_partial_meas_qpe_orth_sum` (the
`(1/r)`-factored partial-meas bridge), `qpe_prob_at_s_closest_ge`
(the analytic `4/π²` peak bound at the matching `k/r` term), and
basic real arithmetic. -/
theorem QPE_MMI_correct_from_orbit
    {m q r : Nat} (k : Nat) (h_k_lt : k < r) (h_r_pos : 0 < r)
    (h_s_lt : s_closest m k r < 2^m)
    (β : Fin r → Matrix (Fin (2^q)) (Fin 1) ℂ)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (fun i j => (1 / (Real.sqrt r : ℂ)) *
          ((∑ j_idx : Fin r,
             FormalRV.Framework.kron_vec
               (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
               (β j_idx) :
             Matrix (Fin (2^(m + q))) (Fin 1) ℂ) i j))
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  rw [prob_partial_meas_qpe_orth_sum (s_closest m k r) h_s_lt h_r_pos
        (fun j_idx => ((j_idx.val : ℝ) / r)) β h_orth]
  have h_r_pos_R : (0 : ℝ) < r := by exact_mod_cast h_r_pos
  have h_simp : (1 / (r : ℝ)) * (4 / Real.pi^2) = 4 / (Real.pi^2 * r) := by
    field_simp
  -- Sum is bounded below by the j_idx = ⟨k, h_k_lt⟩ term, which is ≥ 4/π².
  have h_sum_ge : (4 / Real.pi^2 : ℝ)
      ≤ ∑ j_idx : Fin r,
          FormalRV.Framework.qpe_prob m (s_closest m k r)
                                        ((j_idx.val : ℝ) / r) := by
    have h_term : (4 / Real.pi^2 : ℝ)
        ≤ FormalRV.Framework.qpe_prob m (s_closest m k r) ((k : ℝ) / r) :=
      qpe_prob_at_s_closest_ge m k r h_r_pos
    set g : Fin r → ℝ := fun j_idx =>
        FormalRV.Framework.qpe_prob m (s_closest m k r) ((j_idx.val : ℝ) / r) with hg
    have h_g_nonneg : ∀ j_idx ∈ Finset.univ, 0 ≤ g j_idx :=
      fun _ _ => FormalRV.Framework.qpe_prob_nonneg _ _ _
    have h_single : g ⟨k, h_k_lt⟩ ≤ ∑ j_idx, g j_idx :=
      Finset.single_le_sum h_g_nonneg (Finset.mem_univ _)
    have h_g_k : g ⟨k, h_k_lt⟩ = FormalRV.Framework.qpe_prob m (s_closest m k r) ((k : ℝ) / r) := rfl
    rw [h_g_k] at h_single
    linarith
  have h_lhs_ge : (1 / (r : ℝ)) * (4 / Real.pi^2)
                ≤ (1 / (r : ℝ)) * ∑ j_idx : Fin r,
                    FormalRV.Framework.qpe_prob m (s_closest m k r)
                                                  ((j_idx.val : ℝ) / r) :=
    mul_le_mul_of_nonneg_left h_sum_ge (by positivity)
  linarith

/-- **`QPE_MMI_correct_from_orbit_state_eq`** (added 2026-05-24):
the state-equality form of `QPE_MMI_correct_from_orbit`. Given an
`actual_state` at the natural `Matrix (Fin (2^(m+q))) (Fin 1) ℂ`
type and an equality hypothesis showing that this state is exactly
the orbit-superposition form, the QPE peak bound follows.

This is the cleanest "factor the QPE_MMI_correct axiom through a
state-equality hypothesis" theorem. To recover the public
`QPE_MMI_correct` shape, the remaining work is a separate equality
theorem:

  `Shor_final_state m n anc f = (orbit-superposition state)`

(possibly with a `QState.cast` for the dimension `2^m · 2^n · 2^anc`
vs `2^(m + (n + anc))` mismatch). That equality is the genuine
SQIR/`QPEGeneral.v` semantic obligation; this conditional theorem
closes everything downstream of it. -/
theorem QPE_MMI_correct_from_orbit_state_eq
    {m q r : Nat} (k : Nat) (h_k_lt : k < r) (h_r_pos : 0 < r)
    (h_s_lt : s_closest m k r < 2^m)
    (β : Fin r → Matrix (Fin (2^q)) (Fin 1) ℂ)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0)
    (actual_state : Matrix (Fin (2^(m + q))) (Fin 1) ℂ)
    (h_state : actual_state =
      fun i j => (1 / (Real.sqrt r : ℂ)) *
        ((∑ j_idx : Fin r,
           FormalRV.Framework.kron_vec
             (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
             (β j_idx) :
           Matrix (Fin (2^(m + q))) (Fin 1) ℂ) i j)) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r)) actual_state
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  rw [h_state]
  exact QPE_MMI_correct_from_orbit k h_k_lt h_r_pos h_s_lt β h_orth

/-- **`QPE_MMI_correct_from_Shor_orbit_state`** (added 2026-05-24):
the Shor-shaped wrapper around `QPE_MMI_correct_from_orbit_state_eq`.
Takes the Shor-specific parameters and `BasicSetting`/`ModMulImpl`/
well-typed hypotheses (mirroring `QPE_MMI_correct`'s signature), plus
an explicit state-equality hypothesis showing the joint output state
is the orbit superposition. Derives `0 < r` from `BasicSetting`'s
`Order` field and `s_closest m k r < 2^m` from the existing
`s_closest_ub` helper, then dispatches to
`QPE_MMI_correct_from_orbit_state_eq`.

The conclusion is stated on `actual_state` (not directly on
`Shor_final_state`) to avoid the `QState (2^m * 2^n * 2^anc)` vs
`Matrix (Fin (2^(m + (n + anc))))` dimensional cast — a future tick
can bridge `actual_state` and `Shor_final_state` via `QState.cast` in
a separate equality theorem. The current theorem isolates the QPE-
bound content from that cast bookkeeping.

The `_h_mmi` / `_h_wt` arguments are unused in the proof but kept in
the signature to mirror the public `QPE_MMI_correct`'s shape exactly,
making the final substitution into the full Shor chain mechanical
once the state-factorization equality lands. -/
theorem QPE_MMI_correct_from_Shor_orbit_state
    (a r N m n anc k : Nat)
    (f : Nat → BaseUCom (n + anc))
    (β : Fin r → Matrix (Fin (2^(n + anc))) (Fin 1) ℂ)
    (h_basic : BasicSetting a r N m n)
    (_h_mmi : ModMulImpl a N n anc f)
    (_h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^(n + anc)), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0)
    (actual_state : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ)
    (h_state : actual_state =
      fun i j => (1 / (Real.sqrt r : ℂ)) *
        ((∑ j_idx : Fin r,
           FormalRV.Framework.kron_vec
             (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
             (β j_idx) :
           Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ) i j)) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r)) actual_state
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  have h_r_pos : 0 < r := h_basic.2.1.1
  have h_s_lt : s_closest m k r < 2^m :=
    s_closest_ub a r N m n k h_basic h_k_lt
  exact QPE_MMI_correct_from_orbit_state_eq k h_k_lt h_r_pos h_s_lt
    β h_orth actual_state h_state

/-- **`QPE_MMI_correct_assuming_orbit_factorization`** (added
2026-05-24): the maximal closure of the QPE_MMI_correct axiom that
this codebase currently supports.

Replaces the entire QPE semantic chain with a SINGLE existential
hypothesis `h_orbit_exists`: "there exist orthonormal eigenstates β
and an orbit-form state whose partial-measurement probability matches
`Shor_final_state`'s." Given this hypothesis, the QPE peak bound
follows from the kernel-clean conditional chain
(`QPE_MMI_correct_from_Shor_orbit_state` ∘
`QPE_MMI_correct_from_orbit_state_eq` ∘
`QPE_MMI_correct_from_orbit` ∘ `prob_partial_meas_qpe_orth_sum` ∘
`qpe_prob_peak_bound`) — no axiom is needed downstream of the
existential.

**This theorem cannot replace the `QPE_MMI_correct` axiom directly**
because the existential `h_orbit_exists` is genuinely deep: it
unfolds into the modular-multiplier eigenstate construction +
`QPE_var` circuit semantics, both Phase-4 obligations needing
multi-file infrastructure that does not yet exist in
`Framework.QuantumLib` (linearity of `uc_eval` over arbitrary state
sums, partial-trace machinery, the spectral theorem for unitary
matrices applied to the modular multiplier, etc.).

What this theorem DOES accomplish:
- It witnesses that the analytic / counting / averaging content of
  `QPE_MMI_correct` is fully Lean-proved.
- It pinpoints the EXACT remaining semantic obligation in a single
  named existential hypothesis.
- Replacing this single existential with a theorem-form derivation
  (the Phase-4 work) is sufficient to close the entire QPE chain.

Kernel-clean: `[propext, Classical.choice, Quot.sound]` only. -/
theorem QPE_MMI_correct_assuming_orbit_factorization
    (a r N m n anc k : Nat) (f : Nat → BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_mmi : ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_orbit_exists :
        ∃ (β : Fin r → Matrix (Fin (2^(n + anc))) (Fin 1) ℂ)
          (actual_state : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ),
          ((∀ j j' : Fin r,
             ∑ y : Fin (2^(n + anc)),
                  starRingEnd ℂ ((β j') y 0) * (β j) y 0
             = if j = j' then (1 : ℂ) else 0)
          ∧ (actual_state = fun i j => (1 / (Real.sqrt r : ℂ)) *
              ((∑ j_idx : Fin r,
                 FormalRV.Framework.kron_vec
                   (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
                   (β j_idx) :
                 Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ) i j))
          ∧ (prob_partial_meas (basis_vector (2^m) (s_closest m k r))
                (Shor_final_state m n anc f)
              = prob_partial_meas (basis_vector (2^m) (s_closest m k r))
                                  actual_state))) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  obtain ⟨β, actual_state, h_orth, h_state, h_prob_eq⟩ := h_orbit_exists
  rw [h_prob_eq]
  exact QPE_MMI_correct_from_Shor_orbit_state a r N m n anc k f β
    h_basic h_mmi h_wt h_k_lt h_orth actual_state h_state

end FormalRV.SQIRPort
