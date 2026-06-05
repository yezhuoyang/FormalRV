import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement.RFoundGenericAndAssembly


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

end FormalRV.SQIRPort
