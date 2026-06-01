/-
  FormalRV.Framework.QPEAmplitude — pure-math QPE amplitude/probability.

  Standalone analytic development of the ideal Quantum Phase Estimation
  amplitude/probability expressions. No circuit semantics, no SQIR, no
  Hilbert-space tensor infrastructure — just the Dirichlet-kernel
  arithmetic the QPE Born-rule analysis ultimately reduces to.

  The single ideal amplitude at output `y` for phase `θ` on an
  `m`-bit precision register is

      qpe_amp m y θ
        = (1 / 2^m) · ∑_{x : Fin (2^m)} exp(2πi · x · (θ - y/2^m))

  and the Born probability of outcome `y` is

      qpe_prob m y θ  =  ‖qpe_amp m y θ‖².

  This file establishes the basic definitions and the easy
  "exact-phase" lemma (`θ = y/2^m → qpe_amp = 1`). The geometric-
  series closed form and the 4/π² Dirichlet peak bound are future
  ticks; this is the foundation they will build on.

  Standalone in scope: imports only Mathlib, exports a namespaced
  collection of defs/lemmas. No dependency on `FormalRV.SQIRPort.Shor`
  or `FormalRV.Framework.QPE` (the circuit-level file).
-/

import Mathlib

namespace FormalRV.Framework

/-- **Ideal QPE amplitude** at measurement outcome `y` on an `m`-bit
precision register for true phase `θ ∈ [0, 1)`:

  `qpe_amp m y θ = (1 / 2^m) · ∑_{x : Fin (2^m)} exp(2πi · x · (θ - y/2^m))`.

This is the amplitude that would arise from the textbook QPE circuit
applied to a single eigenstate with eigenvalue `exp(2πi · θ)` (after
the inverse-QFT step on the precision register). The full Born-rule
analysis of `QPE_MMI_correct` ultimately bounds `‖qpe_amp m y θ‖²`
below by `4/π²` for the closest output `y` and `|θ - y/2^m| ≤ 1/2^(m+1)`. -/
noncomputable def qpe_amp (m y : Nat) (θ : ℝ) : ℂ :=
  (1 / (2^m : ℂ)) * ∑ x : Fin (2^m),
    Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) *
                 ((θ : ℂ) - (y : ℂ) / (2^m : ℂ)))

/-- **Ideal QPE outcome probability** `‖qpe_amp m y θ‖²`. -/
noncomputable def qpe_prob (m y : Nat) (θ : ℝ) : ℝ :=
  Complex.normSq (qpe_amp m y θ)

/-- The QPE outcome probability is non-negative — trivial since it
is the squared norm of a complex number. -/
theorem qpe_prob_nonneg (m y : Nat) (θ : ℝ) : 0 ≤ qpe_prob m y θ :=
  Complex.normSq_nonneg _

/-- **Exact-phase amplitude is 1**: if `θ = y/2^m` exactly (the
measurement outcome `y` corresponds to the true phase exactly), every
exponent in the sum is zero, so the sum is `2^m` complex `1`s and
the prefactor gives `1`. -/
theorem qpe_amp_eq_one_of_exact (m y : Nat) (θ : ℝ)
    (h : θ = (y : ℝ) / (2^m : ℝ)) :
    qpe_amp m y θ = 1 := by
  unfold qpe_amp
  have h_cast : ((θ : ℂ) - (y : ℂ) / (2^m : ℂ)) = 0 := by
    have h1 : (θ : ℂ) = ((y : ℝ) / (2^m : ℝ) : ℝ) := by exact_mod_cast h
    rw [h1]; push_cast; ring
  simp [h_cast]

/-- **Exact-phase probability is 1**: direct corollary of the
amplitude lemma. -/
theorem qpe_prob_eq_one_of_exact (m y : Nat) (θ : ℝ)
    (h : θ = (y : ℝ) / (2^m : ℝ)) :
    qpe_prob m y θ = 1 := by
  unfold qpe_prob
  rw [qpe_amp_eq_one_of_exact m y θ h]
  exact Complex.normSq_one

/-- **The QPE sum is the inner sum factor (no prefactor)**. Convenient
form for the geometric-series closed form (future work). -/
noncomputable def qpe_sum (m y : Nat) (θ : ℝ) : ℂ :=
  ∑ x : Fin (2^m),
    Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) *
                 ((θ : ℂ) - (y : ℂ) / (2^m : ℂ)))

/-- Relation between `qpe_amp` and the prefactor-stripped `qpe_sum`. -/
theorem qpe_amp_eq_inv_pow_two_mul_sum (m y : Nat) (θ : ℝ) :
    qpe_amp m y θ = (1 / (2^m : ℂ)) * qpe_sum m y θ := rfl

/-- **Phase-difference encapsulation**: the natural variable of the
ideal QPE expression is `φ = 2^m · θ - y` (the un-normalised phase
discrepancy). Each summand exponent factors as `2πi · x · φ / 2^m`. -/
theorem qpe_sum_eq_sum_phase_diff (m y : Nat) (θ : ℝ) :
    qpe_sum m y θ
      = ∑ x : Fin (2^m),
          Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) *
                       (((2^m : ℝ) * θ - (y : ℝ)) / (2^m : ℝ) : ℂ)) := by
  unfold qpe_sum
  refine Finset.sum_congr rfl ?_
  intro x _
  congr 1
  have h2m : ((2^m : ℝ) : ℂ) ≠ 0 := by
    have h_pos : (0 : ℝ) < (2^m : ℝ) := by positivity
    exact_mod_cast h_pos.ne'
  push_cast
  field_simp

/-! ## Geometric-series closed form

Each summand `exp(2πi · x · (θ - y/2^m))` is `z^x` where
`z = exp(2πi · (θ - y/2^m))` (via `Complex.exp_nat_mul`). The sum is
then the standard finite geometric series

      ∑_{x=0}^{2^m - 1} z^x  =  (z^(2^m) - 1) / (z - 1)   if z ≠ 1,
                              =  2^m                       if z = 1.

These two cases together close the qpe_sum closed form. -/

/-- **The qpe_sum summand factored as `z^x.val`**: rewrites each
exponential `exp(2πi · x · (θ - y/2^m))` as `z^x.val` where
`z = exp(2πi · (θ - y/2^m))`. Foundational step for the geometric-
series closed form. -/
theorem qpe_sum_summand_eq_pow (m y : Nat) (θ : ℝ) (x : Fin (2^m)) :
    Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) *
                 ((θ : ℂ) - (y : ℂ) / (2^m : ℂ)))
      = (Complex.exp (2 * Real.pi * Complex.I *
                      ((θ : ℂ) - (y : ℂ) / (2^m : ℂ))))^x.val := by
  have h_rearr :
      (2 * Real.pi * Complex.I * (x.val : ℂ) *
        ((θ : ℂ) - (y : ℂ) / (2^m : ℂ)))
        = (x.val : ℂ) * (2 * Real.pi * Complex.I *
                          ((θ : ℂ) - (y : ℂ) / (2^m : ℂ))) := by ring
  rw [h_rearr, Complex.exp_nat_mul]

/-- **qpe_sum as a sum of powers**: combines `qpe_sum_summand_eq_pow`
over all `x : Fin (2^m)` and converts `Fin`-indexed sum to
`Finset.range`-indexed sum. Convenient form to apply mathlib's
`geom_sum_eq` / "sum of 1's" lemmas. -/
theorem qpe_sum_eq_sum_pow (m y : Nat) (θ : ℝ) :
    qpe_sum m y θ
      = ∑ k ∈ Finset.range (2^m),
          (Complex.exp (2 * Real.pi * Complex.I *
                        ((θ : ℂ) - (y : ℂ) / (2^m : ℂ))))^k := by
  unfold qpe_sum
  simp_rw [qpe_sum_summand_eq_pow]
  exact Fin.sum_univ_eq_sum_range _ _

/-- **Geometric-series closed form for qpe_sum (non-degenerate case)**:
when the per-step phase factor `z = exp(2πi · (θ - y/2^m))` is not 1,
the qpe_sum equals `(z^(2^m) - 1)/(z - 1)` — the standard finite
geometric series. -/
theorem qpe_sum_geom_eq (m y : Nat) (θ : ℝ)
    (hz : Complex.exp (2 * Real.pi * Complex.I *
                       ((θ : ℂ) - (y : ℂ) / (2^m : ℂ))) ≠ 1) :
    qpe_sum m y θ
      = ((Complex.exp (2 * Real.pi * Complex.I *
                       ((θ : ℂ) - (y : ℂ) / (2^m : ℂ))))^(2^m) - 1) /
        ((Complex.exp (2 * Real.pi * Complex.I *
                       ((θ : ℂ) - (y : ℂ) / (2^m : ℂ)))) - 1) := by
  rw [qpe_sum_eq_sum_pow]
  exact geom_sum_eq hz (2^m)

/-- **qpe_sum in the degenerate `z = 1` case**: when every summand is
`1`, the sum is simply `2^m`. -/
theorem qpe_sum_eq_card_of_exp_eq_one (m y : Nat) (θ : ℝ)
    (hz : Complex.exp (2 * Real.pi * Complex.I *
                       ((θ : ℂ) - (y : ℂ) / (2^m : ℂ))) = 1) :
    qpe_sum m y θ = (2^m : ℂ) := by
  rw [qpe_sum_eq_sum_pow]
  simp_rw [hz, one_pow]
  rw [Finset.sum_const, Finset.card_range]
  simp

/-! ## Modulus / sine formula for qpe_sum

For `z = exp(2πi · (θ - y/2^m))`, the standard identity
`|exp(I · t) - 1| = 2 |sin(t/2)|` (mathlib's
`Complex.norm_exp_I_mul_ofReal_sub_one`) lets us compute both the
numerator `|z^(2^m) - 1|` and denominator `|z - 1|` of the geometric
closed form in terms of sines. Their ratio collapses to

      |qpe_sum m y θ| = |sin(π · φ)| / |sin(π · φ / 2^m)|,

where `φ = 2^m · θ - y` is the natural phase-discrepancy variable. -/

/-- **Phase discrepancy**: the natural variable for the QPE peak bound.
For exact phase (`θ = y/2^m`), `φ = 0` and the QPE outcome is
deterministic; for `|φ| ≤ 1/2`, the analytic peak bound gives
`qpe_prob ≥ 4/π²`. -/
noncomputable def qpe_phase_discrepancy (m y : Nat) (θ : ℝ) : ℝ :=
  (2^m : ℝ) * θ - (y : ℝ)

/-- **Modulus of the denominator** `|z - 1|`, where
`z = exp(2πi · (θ - y/2^m))`: equals `2 |sin(π · (θ - y/2^m))|`.

Equivalently `= 2 |sin(π · φ / 2^m)|` (see
`qpe_denom_norm_eq_sin_phase_diff`). -/
theorem qpe_denom_norm (m y : Nat) (θ : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I *
                   ((θ : ℂ) - (y : ℂ) / (2^m : ℂ))) - 1‖
      = 2 * |Real.sin (Real.pi * (θ - (y : ℝ) / (2^m : ℝ)))| := by
  rw [show (2 * Real.pi * Complex.I * ((θ : ℂ) - (y : ℂ) / (2^m : ℂ)))
        = Complex.I * ((2 * Real.pi * (θ - (y : ℝ) / (2^m : ℝ)) : ℝ) : ℂ) by
      push_cast; ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * (θ - (y : ℝ) / (2^m : ℝ))) / 2
        = Real.pi * (θ - (y : ℝ) / (2^m : ℝ)) by ring]
  rw [Real.norm_eq_abs, abs_mul]
  simp

/-- **Modulus of the numerator** `|z^(2^m) - 1|`, where
`z = exp(2πi · (θ - y/2^m))`: equals `2 |sin(π · φ)|` with
`φ = 2^m · θ - y`. Via `Complex.exp_nat_mul` to absorb the power into
the exponent, then the same identity used in `qpe_denom_norm`. -/
theorem qpe_num_norm (m y : Nat) (θ : ℝ) :
    ‖(Complex.exp (2 * Real.pi * Complex.I *
                    ((θ : ℂ) - (y : ℂ) / (2^m : ℂ))))^(2^m) - 1‖
      = 2 * |Real.sin (Real.pi * qpe_phase_discrepancy m y θ)| := by
  unfold qpe_phase_discrepancy
  rw [← Complex.exp_nat_mul]
  rw [show ((2^m : ℕ) : ℂ) * (2 * Real.pi * Complex.I *
                                ((θ : ℂ) - (y : ℂ) / (2^m : ℂ)))
        = Complex.I * ((2 * Real.pi * ((2^m : ℝ) * θ - (y : ℝ)) : ℝ) : ℂ) by
      have h2m : ((2^m : ℕ) : ℂ) ≠ 0 := by
        have : (0 : ℝ) < (2^m : ℕ) := by exact_mod_cast Nat.two_pow_pos m
        exact_mod_cast this.ne'
      push_cast; field_simp]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * ((2^m : ℝ) * θ - (y : ℝ))) / 2
        = Real.pi * ((2^m : ℝ) * θ - (y : ℝ)) by ring]
  rw [Real.norm_eq_abs, abs_mul]
  simp

/-- **Denominator modulus in phase-discrepancy form**: the same value
expressed via `φ / 2^m` instead of `θ - y/2^m`. Useful for the
`|qpe_sum| = |sin(πφ)| / |sin(πφ/2^m)|` rewrite. -/
theorem qpe_denom_norm_eq_sin_phase_diff (m y : Nat) (θ : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I *
                   ((θ : ℂ) - (y : ℂ) / (2^m : ℂ))) - 1‖
      = 2 * |Real.sin (Real.pi * qpe_phase_discrepancy m y θ / (2^m : ℝ))| := by
  rw [qpe_denom_norm]
  congr 2
  unfold qpe_phase_discrepancy
  have h2m : (2 : ℝ)^m ≠ 0 := by positivity
  field_simp

/-- **Modulus / sine formula for `qpe_sum`**: the headline result of
this section. In the non-degenerate case `z ≠ 1`, the geometric
closed form `qpe_sum = (z^(2^m) - 1)/(z - 1)` has modulus

      |qpe_sum m y θ| = |sin(π · φ)| / |sin(π · φ / 2^m)|.

This is the entry point to the standard QPE peak-bound argument: when
`|φ| ≤ 1/2`, the right-hand side is bounded below by `2 · 2^m / π`
(via `|sin x| ≥ 2|x|/π` for `|x| ≤ π/2` in the numerator combined
with `|sin x| ≤ |x|` in the denominator), which after dividing by
the prefactor `1/2^m` and squaring gives `qpe_prob ≥ 4/π²`. -/
theorem qpe_sum_norm (m y : Nat) (θ : ℝ)
    (hz : Complex.exp (2 * Real.pi * Complex.I *
                       ((θ : ℂ) - (y : ℂ) / (2^m : ℂ))) ≠ 1) :
    ‖qpe_sum m y θ‖
      = |Real.sin (Real.pi * qpe_phase_discrepancy m y θ)| /
        |Real.sin (Real.pi * qpe_phase_discrepancy m y θ / (2^m : ℝ))| := by
  rw [qpe_sum_geom_eq m y θ hz, norm_div]
  rw [qpe_num_norm, qpe_denom_norm_eq_sin_phase_diff]
  -- (2 |sin a|) / (2 |sin b|) = |sin a| / |sin b|
  field_simp

/-! ## QPE peak bound

For phase discrepancy `|φ| ≤ 1/2`, the Born-rule probability of the
"closest" outcome satisfies `qpe_prob m y θ ≥ 4 / π²`. This is the
standard QPE accuracy bound — the probability that the measurement
lands on the right precision peak.

Proof outline:
* `φ = 0`: exact phase, `qpe_prob = 1 ≥ 4/π²` (using `π² ≥ 4`).
* `φ ≠ 0`: by `qpe_sum_norm`, `|qpe_sum| = |sin(πφ)| / |sin(πφ/2^m)|`.
  Combined with `qpe_amp = (1/2^m) · qpe_sum`, the squared probability is
  `(1/4^m) · sin²(πφ) / sin²(πφ/2^m)`. Bound via
  `|sin(πφ)| ≥ 2|φ|` (mathlib `Real.mul_abs_le_abs_sin`) and
  `|sin(πφ/2^m)| ≤ π|φ|/2^m` (mathlib `Real.abs_sin_le_abs`). -/

/-- **QPE peak bound** (the headline analytic result of this module):
when the phase discrepancy `φ = 2^m · θ - y` satisfies `|φ| ≤ 1/2`,
the QPE outcome probability at `y` is at least `4/π²`. -/
theorem qpe_prob_peak_bound
    (m y : Nat) (θ : ℝ)
    (hφ : |qpe_phase_discrepancy m y θ| ≤ 1 / 2) :
    qpe_prob m y θ ≥ 4 / Real.pi^2 := by
  set φ : ℝ := qpe_phase_discrepancy m y θ with hφ_def
  -- ─── Standard positivities ─────────────────────────────
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_pi_sq_pos : (0 : ℝ) < Real.pi^2 := pow_pos h_pi_pos 2
  have h_2m_pos : (0 : ℝ) < (2 : ℝ)^m := pow_pos two_pos m
  have h_2m_ne : ((2 : ℝ)^m) ≠ 0 := h_2m_pos.ne'
  have h_2m_ge_one : (1 : ℝ) ≤ (2 : ℝ)^m :=
    one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  -- ─── Trivial bound 4/π² ≤ 1 ───────────────────────────
  have h_bound_le_one : 4 / Real.pi^2 ≤ 1 := by
    rw [div_le_one h_pi_sq_pos]
    nlinarith [Real.pi_gt_three]
  -- ─── Case split on φ = 0 ──────────────────────────────
  by_cases hφ0 : φ = 0
  · -- Exact phase: qpe_prob = 1.
    have hθ_eq : θ = (y : ℝ) / (2^m : ℝ) := by
      have h_φ_eq : (2 : ℝ)^m * θ - (y : ℝ) = 0 := by
        unfold qpe_phase_discrepancy at hφ_def
        exact hφ_def ▸ hφ0
      field_simp
      linarith
    rw [qpe_prob_eq_one_of_exact m y θ hθ_eq]
    exact h_bound_le_one
  · -- ─── φ ≠ 0 ───────────────────────────────────────
    have hφ_abs_pos : 0 < |φ| := abs_pos.mpr hφ0
    -- Lower bound: |sin(πφ)| ≥ 2|φ|.
    have h_πφ_abs : |Real.pi * φ| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos h_pi_pos]; nlinarith
    have h_sin1 : 2 * |φ| ≤ |Real.sin (Real.pi * φ)| := by
      have h := Real.mul_abs_le_abs_sin h_πφ_abs
      rw [abs_mul, abs_of_pos h_pi_pos] at h
      have h_eq : (2 / Real.pi) * (Real.pi * |φ|) = 2 * |φ| := by field_simp
      linarith
    -- Upper bound: |sin(πφ/2^m)| ≤ π|φ|/2^m.
    have h_sin2 : |Real.sin (Real.pi * φ / (2 : ℝ)^m)|
                  ≤ Real.pi * |φ| / (2 : ℝ)^m := by
      have h := Real.abs_sin_le_abs (x := Real.pi * φ / (2 : ℝ)^m)
      rw [show |Real.pi * φ / (2 : ℝ)^m| = Real.pi * |φ| / (2 : ℝ)^m by
          rw [abs_div, abs_mul, abs_of_pos h_pi_pos, abs_of_pos h_2m_pos]] at h
      exact h
    -- sin(πφ/2^m) ≠ 0: needed to apply qpe_sum_norm (after the z ≠ 1 bridge).
    have h_sin2_ne : Real.sin (Real.pi * φ / (2 : ℝ)^m) ≠ 0 := by
      set x := Real.pi * φ / (2 : ℝ)^m
      have h_x_abs : |x| ≤ Real.pi / 2 := by
        show |Real.pi * φ / (2 : ℝ)^m| ≤ Real.pi / 2
        rw [abs_div, abs_mul, abs_of_pos h_pi_pos, abs_of_pos h_2m_pos]
        rw [div_le_iff₀ h_2m_pos]
        nlinarith
      have h_x_ne : x ≠ 0 :=
        div_ne_zero (mul_ne_zero h_pi_pos.ne' hφ0) h_2m_ne
      intro h_sin
      apply h_x_ne
      apply (Real.sin_eq_zero_iff_of_lt_of_lt _ _).mp h_sin
      · linarith [neg_abs_le x]
      · linarith [le_abs_self x]
    have h_sin2_abs_pos : 0 < |Real.sin (Real.pi * φ / (2 : ℝ)^m)| :=
      abs_pos.mpr h_sin2_ne
    -- z ≠ 1, via the denominator-norm bridge.
    have h_z_ne : Complex.exp (2 * Real.pi * Complex.I *
                  ((θ : ℂ) - (y : ℂ) / ((2 : ℂ)^m))) ≠ 1 := by
      intro h_eq
      have h_zero : Complex.exp (2 * Real.pi * Complex.I *
                ((θ : ℂ) - (y : ℂ) / ((2 : ℂ)^m))) - 1 = 0 := by
        rw [h_eq]; ring
      have h_norm_zero : ‖Complex.exp (2 * Real.pi * Complex.I *
                ((θ : ℂ) - (y : ℂ) / ((2 : ℂ)^m))) - 1‖ = 0 := by
        rw [h_zero, norm_zero]
      rw [qpe_denom_norm] at h_norm_zero
      have h_arg_eq : θ - (y : ℝ) / (2 : ℝ)^m = φ / (2 : ℝ)^m := by
        unfold qpe_phase_discrepancy at hφ_def
        rw [hφ_def]; field_simp
      rw [h_arg_eq] at h_norm_zero
      have h_abs_zero : |Real.sin (Real.pi * (φ / (2 : ℝ)^m))| = 0 := by linarith
      have h_sin_zero : Real.sin (Real.pi * (φ / (2 : ℝ)^m)) = 0 :=
        abs_eq_zero.mp h_abs_zero
      apply h_sin2_ne
      have h_rearr : Real.pi * φ / (2 : ℝ)^m = Real.pi * (φ / (2 : ℝ)^m) := by ring
      rw [h_rearr]; exact h_sin_zero
    -- Modulus formula for ‖qpe_sum‖.
    have h_qpe_sum_norm : ‖qpe_sum m y θ‖
        = |Real.sin (Real.pi * φ)| /
          |Real.sin (Real.pi * φ / (2 : ℝ)^m)| := qpe_sum_norm m y θ h_z_ne
    -- qpe_prob = (1/((2:ℝ)^m)^2) · ‖qpe_sum‖².
    have h_qpe_prob_form : qpe_prob m y θ
        = (1 / ((2 : ℝ)^m)^2) * ‖qpe_sum m y θ‖^2 := by
      unfold qpe_prob
      rw [qpe_amp_eq_inv_pow_two_mul_sum]
      rw [Complex.normSq_eq_norm_sq, norm_mul]
      rw [show ‖((1:ℂ) / (2:ℂ)^m)‖ = 1 / (2 : ℝ)^m by
        rw [norm_div, norm_one, norm_pow, Complex.norm_two]]
      rw [mul_pow]
      congr 1
      rw [div_pow, one_pow]
    -- Final assembly: qpe_prob = (1/(2^m)²) · sin²(πφ) / sin²(πφ/2^m).
    rw [h_qpe_prob_form, h_qpe_sum_norm]
    rw [div_pow, sq_abs, sq_abs]
    -- Goal: (1/(2^m)²) · sin²(πφ) / sin²(πφ/2^m) ≥ 4/π²
    -- Bounds: sin²(πφ) ≥ 4φ²; sin²(πφ/2^m) ≤ π²φ²/(2^m)².
    have h_sin1_sq : (Real.sin (Real.pi * φ))^2 ≥ 4 * φ^2 := by
      have h_rhs_nn : 0 ≤ 2 * |φ| := by positivity
      have h_sq : (2 * |φ|)^2 ≤ (|Real.sin (Real.pi * φ)|)^2 :=
        pow_le_pow_left₀ h_rhs_nn h_sin1 2
      rw [sq_abs] at h_sq
      have h_eq : (2 * |φ|)^2 = 4 * φ^2 := by
        rw [mul_pow, sq_abs]; ring
      linarith
    have h_sin2_sq : (Real.sin (Real.pi * φ / (2 : ℝ)^m))^2
                    ≤ Real.pi^2 * φ^2 / ((2 : ℝ)^m)^2 := by
      have h_lhs_nn : 0 ≤ |Real.sin (Real.pi * φ / (2 : ℝ)^m)| := abs_nonneg _
      have h_rhs_nn : 0 ≤ Real.pi * |φ| / (2 : ℝ)^m := by positivity
      have h_sq : (|Real.sin (Real.pi * φ / (2 : ℝ)^m)|)^2
                 ≤ (Real.pi * |φ| / (2 : ℝ)^m)^2 :=
        pow_le_pow_left₀ h_lhs_nn h_sin2 2
      rw [sq_abs] at h_sq
      have h_expand : (Real.pi * |φ| / (2 : ℝ)^m)^2
                    = Real.pi^2 * φ^2 / ((2 : ℝ)^m)^2 := by
        rw [div_pow, mul_pow, sq_abs]
      linarith [h_expand ▸ h_sq]
    -- Positive sin² in denominator
    have h_sin2_sq_pos : 0 < (Real.sin (Real.pi * φ / (2 : ℝ)^m))^2 := by
      have : Real.sin (Real.pi * φ / (2 : ℝ)^m) ^ 2
            = |Real.sin (Real.pi * φ / (2 : ℝ)^m)| ^ 2 := (sq_abs _).symm
      rw [this]; positivity
    have h_2m_sq_pos : 0 < ((2 : ℝ)^m)^2 := pow_pos h_2m_pos 2
    have h_φ_sq_pos : 0 < φ^2 := by positivity
    -- Combine.
    rw [ge_iff_le, div_le_iff₀ h_pi_sq_pos]
    rw [show (1 / ((2 : ℝ)^m)^2) * ((Real.sin (Real.pi * φ))^2 /
            (Real.sin (Real.pi * φ / (2 : ℝ)^m))^2)
          = (Real.sin (Real.pi * φ))^2
              / (((2 : ℝ)^m)^2 * (Real.sin (Real.pi * φ / (2 : ℝ)^m))^2) by
        field_simp]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    -- Goal: 4 * (((2:ℝ)^m)^2 * sin²(πφ/2^m)) ≤ sin²(πφ) * π²
    have h_lhs_le : 4 * (((2 : ℝ)^m)^2 * (Real.sin (Real.pi * φ / (2 : ℝ)^m))^2)
                  ≤ 4 * Real.pi^2 * φ^2 := by
      have h1 : ((2 : ℝ)^m)^2 * (Real.sin (Real.pi * φ / (2 : ℝ)^m))^2
              ≤ ((2 : ℝ)^m)^2 * (Real.pi^2 * φ^2 / ((2 : ℝ)^m)^2) :=
        mul_le_mul_of_nonneg_left h_sin2_sq h_2m_sq_pos.le
      have h2 : ((2 : ℝ)^m)^2 * (Real.pi^2 * φ^2 / ((2 : ℝ)^m)^2)
              = Real.pi^2 * φ^2 := by field_simp
      linarith
    have h_rhs_ge : 4 * Real.pi^2 * φ^2 ≤ (Real.sin (Real.pi * φ))^2 * Real.pi^2 := by
      have : Real.pi^2 * (4 * φ^2) ≤ Real.pi^2 * (Real.sin (Real.pi * φ))^2 :=
        mul_le_mul_of_nonneg_left h_sin1_sq h_pi_sq_pos.le
      linarith
    linarith

/-! ## Ideal QPE phase-register state

The state on the `m`-qubit precision register that QPE would output if
applied to a single eigenstate at phase `θ`. Its `y`-th amplitude is
exactly the ideal QPE amplitude `qpe_amp m y θ`, so that the
Born-rule probability of measuring outcome `y` matches `qpe_prob m y θ`.

This isolates the "phase register" half of QPE's output from the data
register. The combined output on a single eigenstate `|ψ⟩` is then
`kron_vec (qpe_phase_state m θ) |ψ⟩`, and a partial measurement on
the phase register gives `qpe_prob m y θ · ‖|ψ⟩‖²` (the analytic
QPE peak probability times the trivial unit-norm factor of `|ψ⟩`). -/

/-- **Ideal QPE phase-register output state**: the `y`-th amplitude is
the ideal QPE amplitude `qpe_amp m y θ`. -/
noncomputable def qpe_phase_state (m : Nat) (θ : ℝ) :
    Matrix (Fin (2^m)) (Fin 1) ℂ :=
  fun y _ => qpe_amp m y.val θ

/-- Per-index evaluation of `qpe_phase_state`. -/
@[simp]
theorem qpe_phase_state_apply (m : Nat) (θ : ℝ) (y : Fin (2^m)) :
    qpe_phase_state m θ y 0 = qpe_amp m y.val θ := rfl

/-- The squared amplitude of `qpe_phase_state m θ` at index `y` is
the ideal QPE outcome probability `qpe_prob m y θ`. Direct consequence
of the definition: `‖qpe_amp m y θ‖² = Complex.normSq (qpe_amp m y θ)
= qpe_prob m y θ`. -/
theorem normSq_qpe_phase_state_apply (m : Nat) (θ : ℝ) (y : Fin (2^m)) :
    Complex.normSq (qpe_phase_state m θ y 0) = qpe_prob m y.val θ := by
  rfl

/-! ## Parseval identity for orthonormal vector families

For an orthonormal family `β : Fin r → Matrix (Fin n) (Fin 1) ℂ` and
any scalar family `a : Fin r → ℂ`, the squared L²-norm of the linear
combination `Σ_j a_j · β_j` equals `Σ_j ‖a_j‖²`. The standard Parseval
identity, specialized to finite-dimensional orthonormal families. -/

/-- **Parseval identity for finite orthonormal families**:

      Σ_y ‖Σ_j a_j (β_j)_y‖²  =  Σ_j ‖a_j‖²

when the `β_j` are orthonormal (i.e., `⟨β_j' | β_j⟩ = δ_{j,j'}`).

Used downstream to compute the partial-measurement probability of a
linear combination of eigenstate-tensor terms: cross-terms vanish by
orthonormality, leaving only the diagonal `‖a_j‖²` contribution per
eigenstate. -/
theorem normSq_sum_apply_orth {n r : Nat}
    (β : Fin r → Matrix (Fin n) (Fin 1) ℂ)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin n, starRingEnd ℂ (β j' y 0) * β j y 0
       = if j = j' then (1 : ℂ) else 0)
    (a : Fin r → ℂ) :
    ∑ y : Fin n, Complex.normSq (∑ j : Fin r, a j * β j y 0)
      = ∑ j : Fin r, Complex.normSq (a j) := by
  -- Restate orth with `star` notation to match downstream rewriting.
  have h_orth' : ∀ j j' : Fin r,
      ∑ y : Fin n, star (β j' y 0) * β j y 0 = if j = j' then (1 : ℂ) else 0 := h_orth
  -- Push to ℂ, use Complex.mul_conj.
  have h_cast : ((∑ y : Fin n, Complex.normSq (∑ j : Fin r, a j * β j y 0) : ℝ) : ℂ)
              = ((∑ j : Fin r, Complex.normSq (a j) : ℝ) : ℂ) := by
    push_cast
    simp_rw [← Complex.mul_conj, map_sum, starRingEnd_apply,
             Finset.sum_mul, Finset.mul_sum, star_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_comm]
    conv_lhs =>
      enter [2, j', 2, y]
      rw [show a j * β j y 0 * (star (β j' y 0) * star (a j'))
            = a j * star (a j') * (star (β j' y 0) * β j y 0) from by ring]
    conv_lhs =>
      enter [2, j']
      rw [← Finset.mul_sum]
    simp_rw [h_orth']
    rw [Finset.sum_eq_single j]
    · simp
    · intros j' _ hne
      rw [if_neg (Ne.symm hne), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact_mod_cast h_cast

end FormalRV.Framework
