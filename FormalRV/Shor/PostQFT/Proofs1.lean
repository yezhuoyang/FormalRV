import FormalRV.Shor.PhaseKickback
import FormalRV.Shor.QPEAmplitude
import FormalRV.Shor.PostQFT.Defs

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-- Pointwise: the Fourier-weighted superposition evaluated at index `k`
gives the single non-zero term `(1/√2^m) · exp(2πi · k · θ)`. -/
lemma fourier_weighted_state_apply (m : Nat) (θ : ℝ) (k : Fin (2^m)) :
    (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
        ∑ x : Fin (2^m),
          Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
            FormalRV.Framework.basis_vector (2^m) x.val) k 0
    = ((1 : ℂ) / Real.sqrt (2^m : ℝ)) *
        Complex.exp (2 * Real.pi * Complex.I * (k.val : ℂ) * (θ : ℂ)) := by
  rw [Matrix.smul_apply, Matrix.sum_apply]
  rw [Finset.sum_eq_single k]
  · rw [Matrix.smul_apply, basis_vector_apply]
    simp [smul_eq_mul]
  · intro x _ hx
    rw [Matrix.smul_apply, basis_vector_apply]
    simp [smul_eq_mul]
    intro h_eq
    exact (hx (Fin.ext h_eq.symm)).elim
  · simp

/-- `(1/√2^m)² = 1/2^m` in ℂ. -/
lemma inv_sqrt_two_pow_sq (m : Nat) :
    ((1 : ℂ) / Real.sqrt (2^m : ℝ)) * ((1 : ℂ) / Real.sqrt (2^m : ℝ))
      = 1 / (2^m : ℂ) := by
  have h_pos : (0 : ℝ) < 2^m := by positivity
  have h_sqrt_sq_real : Real.sqrt (2^m : ℝ) * Real.sqrt (2^m : ℝ) = (2^m : ℝ) :=
    Real.mul_self_sqrt (le_of_lt h_pos)
  rw [show ((1 : ℂ) / Real.sqrt (2^m : ℝ)) * ((1 : ℂ) / Real.sqrt (2^m : ℝ))
        = 1 / ((Real.sqrt (2^m : ℝ) : ℂ) * Real.sqrt (2^m : ℝ)) from by ring]
  rw [show ((Real.sqrt (2^m : ℝ) : ℂ) * Real.sqrt (2^m : ℝ))
        = ((Real.sqrt (2^m : ℝ) * Real.sqrt (2^m : ℝ) : ℝ) : ℂ) from by push_cast; ring]
  rw [h_sqrt_sq_real]
  push_cast
  rfl

/-- **HEADLINE MATH THEOREM.** The ideal inverse-QFT matrix maps the
Fourier-weighted superposition `(1/√2^m) · ∑_x exp(+2πi · x · θ) · |x⟩`
to `qpe_phase_state m θ`. This is a pure linear-algebra fact,
independent of any specific circuit realization. -/
theorem IQFT_matrix_on_fourier_weighted_state
    (m : Nat) (θ : ℝ) :
    IQFT_matrix m *
      (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
        ∑ x : Fin (2^m),
          Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
            FormalRV.Framework.basis_vector (2^m) x.val)
    = qpe_phase_state m θ := by
  ext y j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  rw [Matrix.mul_apply]
  rw [show ∑ x : Fin (2^m), IQFT_matrix m y x *
            (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
              ∑ x' : Fin (2^m),
                Complex.exp (2 * Real.pi * Complex.I * (x'.val : ℂ) * (θ : ℂ)) •
                  FormalRV.Framework.basis_vector (2^m) x'.val) x 0
        = ∑ x : Fin (2^m), IQFT_matrix m y x *
            (((1 : ℂ) / Real.sqrt (2^m : ℝ)) *
              Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ))) from by
    apply Finset.sum_congr rfl
    intro x _
    rw [fourier_weighted_state_apply m θ x]]
  unfold IQFT_matrix qpe_phase_state qpe_amp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [show ((1 : ℂ) / Real.sqrt (2^m : ℝ)) *
            Complex.exp (-(2 * Real.pi * Complex.I) * (x.val : ℂ) * (y.val : ℂ) / (2^m : ℂ)) *
            (((1 : ℂ) / Real.sqrt (2^m : ℝ)) *
              Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)))
        = (((1 : ℂ) / Real.sqrt (2^m : ℝ)) * ((1 : ℂ) / Real.sqrt (2^m : ℝ))) *
          (Complex.exp (-(2 * Real.pi * Complex.I) * (x.val : ℂ) * (y.val : ℂ) / (2^m : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ))) from by ring]
  rw [← Complex.exp_add]
  rw [inv_sqrt_two_pow_sq m]
  congr 1
  ring

/-- The real 1-qubit inverse QFT is `H 0`. -/
theorem real_QFTinv_on_one : real_QFTinv_on 1 = (H 0 : BaseUCom 1) := rfl

/-- The real 0-qubit inverse QFT is `SKIP`. -/
theorem real_QFTinv_on_zero : real_QFTinv_on 0 = (SKIP : BaseUCom 0) := rfl

/-- **At `n = 2`, the recursive layer matches the hand-written candidate.**

Both circuits evaluate to `H 0 · CR(-π/2) · H 1 · SWAP` as a 4×4 matrix.
The recursive layer has a trailing `SKIP`, which collapses via
`uc_eval_ID_eq_one`. -/
theorem real_QFTinv_layer_two_eq_candidate :
    FormalRV.Framework.uc_eval (real_QFTinv_layer 2)
      = FormalRV.Framework.uc_eval real_QFTinv2_candidate := by
  show FormalRV.Framework.uc_eval (UCom.seq (bit_reversal_swaps 2)
        (real_QFTinv_layer.countdown 2 2))
      = FormalRV.Framework.uc_eval real_QFTinv2_candidate
  unfold bit_reversal_swaps real_QFTinv2_candidate
  simp [real_QFTinv_layer.countdown, bit_reversal_swaps.loop,
        inverse_qft_phase_ladder, inverse_qft_phase_ladder.loop,
        show (SKIP : FormalRV.Framework.BaseUCom 2) = ID 0 from rfl,
        uc_eval_ID_eq_one (show (0 : Nat) < 2 from by omega)]
  rw [Matrix.mul_assoc, Matrix.mul_assoc]

/-! ## §3. 1-qubit circuit correctness

The 1-qubit inverse QFT collapses to a Hadamard. We prove
`uc_eval (real_QFTinv_on 1) = IQFT_matrix 1` directly by entry-wise
comparison. This is the base case for the eventual recursive
correctness theorem. -/

/-- Helper: `√2 / 2 = (√2)⁻¹` over ℂ. -/
lemma sqrt_two_div_two_eq_inv :
    (Real.sqrt 2 : ℂ) / 2 = (Real.sqrt 2 : ℂ)⁻¹ := by
  have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast h_sqrt2_pos.ne'
  field_simp
  rw [show ((Real.sqrt 2 : ℂ))^2 = ((Real.sqrt 2)^2 : ℝ) from by push_cast; ring]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  push_cast; ring

/-- **m=1 circuit correctness.** The 1-qubit `real_QFTinv_on 1 = H 0`
has unitary evaluation matrix equal to `IQFT_matrix 1`. Proof: case
analysis on the 2×2 entries, with normalization `√2/2 = (√2)⁻¹` and
`exp(-π·I) = -1`. -/
theorem uc_eval_real_QFTinv_eq_IQFT_matrix_one :
    FormalRV.Framework.uc_eval (real_QFTinv_on 1 : BaseUCom 1)
      = IQFT_matrix 1 := by
  rw [real_QFTinv_on_one]
  rw [show FormalRV.Framework.uc_eval (H 0 : BaseUCom 1)
        = pad_u 1 0 hMatrix from by
    unfold H FormalRV.Framework.uc_eval ueval_r
    show pad_u 1 0 (rotation (Real.pi / 2) 0 Real.pi) = pad_u 1 0 hMatrix
    rw [rotation_H]]
  ext i j
  fin_cases i <;> fin_cases j <;>
  · unfold IQFT_matrix
    rw [pad_u_one_zero_eq hMatrix]
    simp [hMatrix]
    try exact sqrt_two_div_two_eq_inv
    try
      (rw [show -(2 * ↑Real.pi * Complex.I) / 2 = -((Real.pi : ℂ) * Complex.I) from by ring,
          Complex.exp_neg, Complex.exp_pi_mul_I]
       have h := sqrt_two_div_two_eq_inv
       linear_combination -h)

/-- **1-qubit semantic theorem.** The real 1-qubit inverse QFT applied
to the Fourier-weighted superposition `(1/√2) · ∑_x exp(2πi · x · θ) |x⟩`
yields `qpe_phase_state 1 θ`. Combines the circuit-correctness
theorem with the matrix-level `IQFT_matrix_on_fourier_weighted_state`. -/
theorem real_QFTinv_one_on_fourier_state (θ : ℝ) :
    FormalRV.Framework.uc_eval (real_QFTinv_on 1 : BaseUCom 1) *
      (((1 : ℂ) / Real.sqrt (2^1 : ℝ)) •
        ∑ x : Fin (2^1),
          Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
            FormalRV.Framework.basis_vector (2^1) x.val)
    = qpe_phase_state 1 θ := by
  rw [uc_eval_real_QFTinv_eq_IQFT_matrix_one]
  exact IQFT_matrix_on_fourier_weighted_state 1 θ

/-! ## §4. Building blocks for the 2-qubit matrix-equality theorem

The headline theorem `uc_eval real_QFTinv2_candidate = IQFT_matrix 2`
is established via `matrix_eq_of_basis_action` (Framework/PadAction):
suffices to show both matrices act identically on each of the four
basis vectors `basis_vector 4 k` for `k ∈ {0, 1, 2, 3}`.

This section lands:
- `H_one_eq_minus`: the `|1⟩` counterpart to `H_zero_eq_plus`.
- Two `uc_eval (H q : BaseUCom 2)` simplification lemmas (in terms of
  `pad_u 2 q hMatrix`).
- The four `IQFT_matrix_two_on_basis_*` lemmas giving the explicit
  exponential form of `IQFT_matrix 2 * basis_vector 4 k` for each k.

The remaining work for the next pass is: prove the analogous
explicit form of `uc_eval real_QFTinv2_candidate * basis_vector 4 k`
for each k by chaining SWAP → H 1 → controlled_Rz → H 0 actions, then
compose via `matrix_eq_of_basis_action`. -/

/-- **`H |1⟩ = (√2/2) · (|0⟩ − |1⟩)`** — the `|1⟩` counterpart to
`H_zero_eq_plus`. Direct 2×2 computation. -/
theorem H_one_eq_minus :
    FormalRV.Framework.uc_eval
        (FormalRV.Framework.BaseUCom.H 0 : FormalRV.Framework.BaseUCom 1) *
        FormalRV.Framework.basis_vector 2 1
      = ((Real.sqrt 2 / 2 : ℂ)) •
        (FormalRV.Framework.basis_vector 2 0 -
          FormalRV.Framework.basis_vector 2 1) := by
  show pad_u 1 0 (FormalRV.Framework.rotation (Real.pi / 2) 0 Real.pi) *
        FormalRV.Framework.basis_vector 2 1 = _
  rw [FormalRV.Framework.rotation_H]
  rw [pad_u_one_zero_eq]
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  fin_cases r
  · simp [Matrix.mul_apply, FormalRV.Framework.basis_vector, hMatrix,
          Matrix.sub_apply, smul_eq_mul, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, FormalRV.Framework.basis_vector, hMatrix,
          Matrix.sub_apply, smul_eq_mul, Fin.sum_univ_two]

/-- `uc_eval (H 0) = pad_u 2 0 hMatrix` at dim = 2. -/
theorem uc_eval_H_zero_two_eq_pad_u :
    FormalRV.Framework.uc_eval (BaseUCom.H 0 : FormalRV.Framework.BaseUCom 2)
      = pad_u 2 0 hMatrix := by
  unfold BaseUCom.H FormalRV.Framework.uc_eval ueval_r
  show pad_u 2 0 (rotation (Real.pi / 2) 0 Real.pi) = pad_u 2 0 hMatrix
  rw [rotation_H]

/-- `uc_eval (H 1) = pad_u 2 1 hMatrix` at dim = 2. -/
theorem uc_eval_H_one_two_eq_pad_u :
    FormalRV.Framework.uc_eval (BaseUCom.H 1 : FormalRV.Framework.BaseUCom 2)
      = pad_u 2 1 hMatrix := by
  unfold BaseUCom.H FormalRV.Framework.uc_eval ueval_r
  show pad_u 2 1 (rotation (Real.pi / 2) 0 Real.pi) = pad_u 2 1 hMatrix
  rw [rotation_H]

/-- **`IQFT_matrix 2` on `|0⟩`**: produces the uniform superposition
`(1/2) · (|0⟩ + |1⟩ + |2⟩ + |3⟩)`. All phases are 1 because
`exp(0) = 1`. -/
theorem IQFT_matrix_two_on_basis_zero :
    IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 0
      = ((1 : ℂ) / Real.sqrt (2^2 : ℝ)) •
        (FormalRV.Framework.basis_vector 4 0 +
         FormalRV.Framework.basis_vector 4 1 +
         FormalRV.Framework.basis_vector 4 2 +
         FormalRV.Framework.basis_vector 4 3) := by
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  fin_cases i <;>
    simp [Matrix.mul_apply, IQFT_matrix, FormalRV.Framework.basis_vector,
          Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- **`IQFT_matrix 2` on `|1⟩`**: `(1/2) · (|0⟩ + e^(-iπ/2)|1⟩ +
e^(-iπ)|2⟩ + e^(-i3π/2)|3⟩)`. -/
theorem IQFT_matrix_two_on_basis_one :
    IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 1
      = ((1 : ℂ) / Real.sqrt (2^2 : ℝ)) •
        (FormalRV.Framework.basis_vector 4 0
         + Complex.exp (-(Real.pi / 2) * Complex.I) • FormalRV.Framework.basis_vector 4 1
         + Complex.exp (-Real.pi * Complex.I) • FormalRV.Framework.basis_vector 4 2
         + Complex.exp (-(3 * Real.pi / 2) * Complex.I) • FormalRV.Framework.basis_vector 4 3) := by
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  fin_cases i <;>
    simp [Matrix.mul_apply, IQFT_matrix, FormalRV.Framework.basis_vector,
          Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  all_goals ring_nf

/-- **`IQFT_matrix 2` on `|2⟩`**: phases are `1, e^(-iπ), e^(-i2π),
e^(-i3π)` which collapse to `1, -1, 1, -1`. -/
theorem IQFT_matrix_two_on_basis_two :
    IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 2
      = ((1 : ℂ) / Real.sqrt (2^2 : ℝ)) •
        (FormalRV.Framework.basis_vector 4 0
         + Complex.exp (-Real.pi * Complex.I) • FormalRV.Framework.basis_vector 4 1
         + Complex.exp (-2 * Real.pi * Complex.I) • FormalRV.Framework.basis_vector 4 2
         + Complex.exp (-3 * Real.pi * Complex.I) • FormalRV.Framework.basis_vector 4 3) := by
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  fin_cases i <;>
    simp [Matrix.mul_apply, IQFT_matrix, FormalRV.Framework.basis_vector,
          Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  all_goals ring_nf

/-- **`IQFT_matrix 2` on `|3⟩`**: phases form the conjugate
`{1, -i, -1, i}` of the `|1⟩` column. -/
theorem IQFT_matrix_two_on_basis_three :
    IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 3
      = ((1 : ℂ) / Real.sqrt (2^2 : ℝ)) •
        (FormalRV.Framework.basis_vector 4 0
         + Complex.exp (-(3 * Real.pi / 2) * Complex.I) • FormalRV.Framework.basis_vector 4 1
         + Complex.exp (-3 * Real.pi * Complex.I) • FormalRV.Framework.basis_vector 4 2
         + Complex.exp (-(9 * Real.pi / 2) * Complex.I) • FormalRV.Framework.basis_vector 4 3) := by
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  fin_cases i <;>
    simp [Matrix.mul_apply, IQFT_matrix, FormalRV.Framework.basis_vector,
          Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  all_goals ring_nf

/-! ## §5. LHS circuit-action columns

For each k ∈ {0,1,2,3}, we prove
`uc_eval real_QFTinv2_candidate * basis_vector 4 k = IQFT_matrix 2 * basis_vector 4 k`
by chaining the gate-action lemmas (SWAP → H 1 → controlled_Rz → H 0)
and matching the resulting sum of basis vectors against the RHS
column lemmas from §4. -/

/-- `f_to_vec 2 f` in terms of `basis_vector 4` and the values of `f`
at bits 0 and 1. Recall that bit 0 is MSB (weight 2), bit 1 is LSB
(weight 1) in the framework's `funbool_to_nat` convention. -/
lemma f_to_vec_two_eq (f : Nat → Bool) :
    f_to_vec 2 f = FormalRV.Framework.basis_vector 4
      ((if f 0 then 2 else 0) + (if f 1 then 1 else 0)) := by
  unfold f_to_vec
  congr 1
  by_cases h0 : f 0 = true <;> by_cases h1 : f 1 = true <;>
    simp [funbool_to_nat, h0, h1]

/-- `(√2/2)² = 1/2` over `ℂ`. -/
lemma sqrt_two_half_sq :
    (Real.sqrt 2 / 2 : ℂ) * (Real.sqrt 2 / 2 : ℂ) = (1/2 : ℂ) := by
  rw [show (Real.sqrt 2 / 2 : ℂ) * (Real.sqrt 2 / 2 : ℂ) =
       ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) / 4 from by ring]
  rw [show (Real.sqrt 2 : ℂ) * Real.sqrt 2 =
       ((Real.sqrt 2 * Real.sqrt 2 : ℝ) : ℂ) from by push_cast; ring]
  rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  push_cast; norm_num

/-- `exp(-(π·I)) = -1`. -/
lemma exp_neg_pi_I : Complex.exp (-((Real.pi : ℂ) * Complex.I)) = -1 := by
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- `exp(-(2π·I)) = 1`. -/
lemma exp_neg_two_pi_I : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
  rw [show -(2 * (Real.pi : ℂ) * Complex.I)
        = -((Real.pi : ℂ) * Complex.I) + (-((Real.pi : ℂ) * Complex.I)) from by ring]
  rw [Complex.exp_add, exp_neg_pi_I]
  norm_num

/-- `exp(-(3π·I)) = -1`. -/
lemma exp_neg_three_pi_I : Complex.exp (-(3 * (Real.pi : ℂ) * Complex.I)) = -1 := by
  rw [show -(3 * (Real.pi : ℂ) * Complex.I)
        = -((Real.pi : ℂ) * Complex.I) + (-(2 * (Real.pi : ℂ) * Complex.I)) from by ring]
  rw [Complex.exp_add, exp_neg_pi_I, exp_neg_two_pi_I]
  norm_num

/-- `exp(-(3π/2 · I)) = -exp(-(π/2 · I))`. -/
lemma exp_neg_three_pi_half_I :
    Complex.exp (-(3 * (Real.pi : ℂ) / 2 * Complex.I))
      = -Complex.exp (-((Real.pi : ℂ) / 2 * Complex.I)) := by
  rw [show -(3 * (Real.pi : ℂ) / 2 * Complex.I)
        = -((Real.pi : ℂ) / 2 * Complex.I) + (-((Real.pi : ℂ) * Complex.I)) from by ring]
  rw [Complex.exp_add, exp_neg_pi_I]
  ring

/-- `exp(-(9π/2 · I)) = exp(-(π/2 · I))` — since `-9π/2 = -π/2 - 4π` and
`exp(-4π·I) = 1`. -/
lemma exp_neg_nine_pi_half_I :
    Complex.exp (-(9 * (Real.pi : ℂ) / 2 * Complex.I))
      = Complex.exp (-((Real.pi : ℂ) / 2 * Complex.I)) := by
  rw [show -(9 * (Real.pi : ℂ) / 2 * Complex.I)
        = -((Real.pi : ℂ) / 2 * Complex.I) + (-(2 * (Real.pi : ℂ) * Complex.I))
          + (-(2 * (Real.pi : ℂ) * Complex.I))
       from by ring]
  rw [Complex.exp_add, Complex.exp_add, exp_neg_two_pi_I]
  ring

/-- `(√2 : ℂ)² = 2`. -/
lemma sqrt_two_sq_complex : ((Real.sqrt 2 : ℂ))^2 = (2 : ℂ) := by
  rw [show ((Real.sqrt 2 : ℂ))^2 = ((Real.sqrt 2)^2 : ℝ) from by push_cast; ring]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  push_cast; ring

/-- Consolidate `(√2/2) * (e * (√2/2))` into `(1/2) * e`. -/
lemma sqrt_two_half_smul_sandwich (e : ℂ) :
    (Real.sqrt 2 / 2 : ℂ) * (e * (Real.sqrt 2 / 2 : ℂ)) = (1/2 : ℂ) * e := by
  rw [show (Real.sqrt 2 / 2 : ℂ) * (e * (Real.sqrt 2 / 2 : ℂ))
        = ((Real.sqrt 2 / 2 : ℂ) * (Real.sqrt 2 / 2 : ℂ)) * e from by ring]
  rw [sqrt_two_half_sq]

/-- **Column 0: candidate on `|0⟩`.** Direct chain via `f_to_vec_SWAP`,
`f_to_vec_H_uc_eval`, `controlled_Rz_acts_on_basis_correct`. -/
theorem real_QFTinv2_candidate_on_basis_zero :
    FormalRV.Framework.uc_eval real_QFTinv2_candidate *
        FormalRV.Framework.basis_vector 4 0
      = IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 0 := by
  rw [IQFT_matrix_two_on_basis_zero]
  unfold real_QFTinv2_candidate
  rw [uc_eval_seq_mul, uc_eval_seq_mul, uc_eval_seq_mul]
  conv_lhs =>
    rw [show (FormalRV.Framework.basis_vector 4 0 : Matrix (Fin 4) (Fin 1) ℂ)
          = FormalRV.Framework.basis_vector (2^2) 0 from rfl]
    rw [basis_vector_eq_f_to_vec_nat 2 0 (by omega)]
  rw [show (BaseUCom.SWAP 0 1 : FormalRV.Framework.BaseUCom 2)
        = UCom.seq (BaseUCom.CNOT 0 1) (UCom.seq (BaseUCom.CNOT 1 0) (BaseUCom.CNOT 0 1))
        from rfl]
  rw [f_to_vec_SWAP 2 0 1 (by omega) (by omega) (by decide)]
  rw [f_to_vec_H_uc_eval 2 1 (by omega)]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [Matrix.mul_add]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq]
  simp only [update,
             show (nat_to_funbool 2 0 0) = false from by decide,
             show (nat_to_funbool 2 0 1) = false from by decide]
  simp
  rw [smul_smul, smul_smul, smul_smul, smul_smul, sqrt_two_half_sq]
  rw [show ((1 : ℂ) / 2) = 2⁻¹ from by ring]
  module

/-- **Column 1: candidate on `|1⟩`.** -/
theorem real_QFTinv2_candidate_on_basis_one :
    FormalRV.Framework.uc_eval real_QFTinv2_candidate *
        FormalRV.Framework.basis_vector 4 1
      = IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 1 := by
  rw [IQFT_matrix_two_on_basis_one]
  unfold real_QFTinv2_candidate
  rw [uc_eval_seq_mul, uc_eval_seq_mul, uc_eval_seq_mul]
  conv_lhs =>
    rw [show (FormalRV.Framework.basis_vector 4 1 : Matrix (Fin 4) (Fin 1) ℂ)
          = FormalRV.Framework.basis_vector (2^2) 1 from rfl]
    rw [basis_vector_eq_f_to_vec_nat 2 1 (by omega)]
  rw [show (BaseUCom.SWAP 0 1 : FormalRV.Framework.BaseUCom 2)
        = UCom.seq (BaseUCom.CNOT 0 1) (UCom.seq (BaseUCom.CNOT 1 0) (BaseUCom.CNOT 0 1))
        from rfl]
  rw [f_to_vec_SWAP 2 0 1 (by omega) (by omega) (by decide)]
  rw [f_to_vec_H_uc_eval 2 1 (by omega)]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [Matrix.mul_add]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq]
  simp only [update,
             show (nat_to_funbool 2 1 0) = false from by decide,
             show (nat_to_funbool 2 1 1) = true from by decide]
  simp
  rw [exp_neg_pi_I, exp_neg_three_pi_half_I]
  simp only [smul_smul, sqrt_two_half_sq, sqrt_two_half_smul_sandwich]
  rw [show ((1 : ℂ) / 2) = 2⁻¹ from by ring]
  module

/-- **Column 2: candidate on `|2⟩`.** -/
theorem real_QFTinv2_candidate_on_basis_two :
    FormalRV.Framework.uc_eval real_QFTinv2_candidate *
        FormalRV.Framework.basis_vector 4 2
      = IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 2 := by
  rw [IQFT_matrix_two_on_basis_two]
  unfold real_QFTinv2_candidate
  rw [uc_eval_seq_mul, uc_eval_seq_mul, uc_eval_seq_mul]
  conv_lhs =>
    rw [show (FormalRV.Framework.basis_vector 4 2 : Matrix (Fin 4) (Fin 1) ℂ)
          = FormalRV.Framework.basis_vector (2^2) 2 from rfl]
    rw [basis_vector_eq_f_to_vec_nat 2 2 (by omega)]
  rw [show (BaseUCom.SWAP 0 1 : FormalRV.Framework.BaseUCom 2)
        = UCom.seq (BaseUCom.CNOT 0 1) (UCom.seq (BaseUCom.CNOT 1 0) (BaseUCom.CNOT 0 1))
        from rfl]
  rw [f_to_vec_SWAP 2 0 1 (by omega) (by omega) (by decide)]
  rw [f_to_vec_H_uc_eval 2 1 (by omega)]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [Matrix.mul_add]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq]
  simp only [update,
             show (nat_to_funbool 2 2 0) = true from by decide,
             show (nat_to_funbool 2 2 1) = false from by decide]
  simp
  rw [exp_neg_pi_I, exp_neg_two_pi_I, exp_neg_three_pi_I]
  rw [smul_smul, smul_smul, smul_smul, smul_smul, sqrt_two_half_sq]
  rw [show ((1 : ℂ) / 2) = 2⁻¹ from by ring]
  module

/-- **Column 3: candidate on `|3⟩`.** -/
theorem real_QFTinv2_candidate_on_basis_three :
    FormalRV.Framework.uc_eval real_QFTinv2_candidate *
        FormalRV.Framework.basis_vector 4 3
      = IQFT_matrix 2 * FormalRV.Framework.basis_vector 4 3 := by
  rw [IQFT_matrix_two_on_basis_three]
  unfold real_QFTinv2_candidate
  rw [uc_eval_seq_mul, uc_eval_seq_mul, uc_eval_seq_mul]
  conv_lhs =>
    rw [show (FormalRV.Framework.basis_vector 4 3 : Matrix (Fin 4) (Fin 1) ℂ)
          = FormalRV.Framework.basis_vector (2^2) 3 from rfl]
    rw [basis_vector_eq_f_to_vec_nat 2 3 (by omega)]
  rw [show (BaseUCom.SWAP 0 1 : FormalRV.Framework.BaseUCom 2)
        = UCom.seq (BaseUCom.CNOT 0 1) (UCom.seq (BaseUCom.CNOT 1 0) (BaseUCom.CNOT 0 1))
        from rfl]
  rw [f_to_vec_SWAP 2 0 1 (by omega) (by omega) (by decide)]
  rw [f_to_vec_H_uc_eval 2 1 (by omega)]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [controlled_Rz_acts_on_basis_correct 2 1 0 (by omega) (by omega) (by decide) (-(Real.pi / 2))]
  rw [Matrix.mul_add]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_H_uc_eval 2 0 (by omega)]
  rw [f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq, f_to_vec_two_eq]
  simp only [update,
             show (nat_to_funbool 2 3 0) = true from by decide,
             show (nat_to_funbool 2 3 1) = true from by decide]
  simp
  rw [exp_neg_three_pi_half_I, exp_neg_three_pi_I, exp_neg_nine_pi_half_I]
  simp only [smul_smul, sqrt_two_half_sq, sqrt_two_half_smul_sandwich]
  rw [show ((1 : ℂ) / 2) = 2⁻¹ from by ring]
  module

/-- **HEADLINE: 2-qubit IQFT matrix equality.** Lifts the four column
lemmas to matrix equality via `matrix_eq_of_basis_action`. -/
theorem uc_eval_real_QFTinv2_candidate_eq_IQFT_matrix :
    FormalRV.Framework.uc_eval real_QFTinv2_candidate = IQFT_matrix 2 := by
  apply matrix_eq_of_basis_action
  intro k
  fin_cases k
  · exact real_QFTinv2_candidate_on_basis_zero
  · exact real_QFTinv2_candidate_on_basis_one
  · exact real_QFTinv2_candidate_on_basis_two
  · exact real_QFTinv2_candidate_on_basis_three

/-- The `n = 2` case of `real_QFTinv_on` is syntactically equal to
`real_QFTinv2_candidate`. -/
theorem real_QFTinv_on_two : real_QFTinv_on 2 = real_QFTinv2_candidate := rfl

/-- **m=2 circuit correctness.** `uc_eval (real_QFTinv_on 2) = IQFT_matrix 2`,
the 2-qubit counterpart to `uc_eval_real_QFTinv_eq_IQFT_matrix_one`. -/
theorem uc_eval_real_QFTinv_eq_IQFT_matrix_two :
    FormalRV.Framework.uc_eval (real_QFTinv_on 2 : BaseUCom 2) = IQFT_matrix 2 := by
  rw [real_QFTinv_on_two]
  exact uc_eval_real_QFTinv2_candidate_eq_IQFT_matrix

/-- **2-qubit semantic theorem.** Mirrors `real_QFTinv_one_on_fourier_state`:
the real 2-qubit inverse QFT applied to the Fourier-weighted superposition
yields `qpe_phase_state 2 θ`. -/
theorem real_QFTinv_two_on_fourier_state (θ : ℝ) :
    FormalRV.Framework.uc_eval (real_QFTinv_on 2 : BaseUCom 2) *
      (((1 : ℂ) / Real.sqrt (2^2 : ℝ)) •
        ∑ x : Fin (2^2),
          Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
            FormalRV.Framework.basis_vector (2^2) x.val)
    = qpe_phase_state 2 θ := by
  rw [uc_eval_real_QFTinv_eq_IQFT_matrix_two]
  exact IQFT_matrix_on_fourier_weighted_state 2 θ

/-- **Lifted IQFT acts on the control factor.** Given `h_IQFT`, the
`real_QFTinv_on m` lifted to `m + anc` qubits acts on `kron_vec ψc ψd`
by applying `IQFT_matrix m` to the control factor `ψc`. -/
theorem real_QFTinv_lifted_on_kron
    {m anc : Nat}
    (ψc : Matrix (Fin (2^m)) (Fin 1) ℂ)
    (ψd : Matrix (Fin (2^anc)) (Fin 1) ℂ)
    (h_wt : UCom.WellTyped m (real_QFTinv_on m))
    (h_IQFT : FormalRV.Framework.uc_eval (real_QFTinv_on m : BaseUCom m)
                = IQFT_matrix m) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => q) (real_QFTinv_on m) : BaseUCom (m + anc))
      * kron_vec ψc ψd
    = kron_vec (IQFT_matrix m * ψc) ψd := by
  rw [uc_eval_control_register_circuit_kron_vec (real_QFTinv_on m) h_wt ψc ψd]
  rw [h_IQFT]

/-- **Distribute `kron_vec` into a Fourier-weighted sum.** Algebraic helper
exposing the `kron_vec ψc ψ` factorization of the Fourier-weighted
superposition. -/
theorem fourier_weighted_kron_sum_eq_kron_vec_fourier_state
    {m anc : Nat} (θ : ℝ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
      ∑ x : Fin (2^m),
        Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
    = kron_vec
        (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
          ∑ x : Fin (2^m),
            Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
              FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  rw [kron_vec_smul_left]
  congr 1
  rw [kron_vec_sum_left]
  apply Finset.sum_congr rfl
  intro x _
  rw [kron_vec_smul_left]

/-- **Post-QFT theorem from IQFT correctness.** Given `h_IQFT`, the
lifted `real_QFTinv_on m` applied to the Fourier-weighted kron
superposition yields `kron_vec (qpe_phase_state m θ) ψ`. -/
theorem real_QFTinv_on_fourier_weighted_kron_state_from_matrix_correct
    {m anc : Nat}
    (θ : ℝ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ)
    (h_wt : UCom.WellTyped m (real_QFTinv_on m))
    (h_IQFT : FormalRV.Framework.uc_eval (real_QFTinv_on m : BaseUCom m)
                = IQFT_matrix m) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => q) (real_QFTinv_on m) : BaseUCom (m + anc))
      *
    (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
      ∑ x : Fin (2^m),
        Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) * (θ : ℂ)) •
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
    = kron_vec (qpe_phase_state m θ) ψ := by
  rw [fourier_weighted_kron_sum_eq_kron_vec_fourier_state]
  rw [real_QFTinv_lifted_on_kron _ ψ h_wt h_IQFT]
  rw [IQFT_matrix_on_fourier_weighted_state m θ]

/-! ### Recursive-layer-level building blocks for arbitrary-n IQFT correctness

These lemmas are the layer-level interface used by the arbitrary-n
correctness proof (deferred to a later pass). The matrix-level
decomposition `IQFT_matrix_succ_decomp` is the central recursion;
the circuit-level decomposition uses `real_QFTinv_layer` together
with the per-target `inverse_qft_phase_ladder` ladders. -/

/-- **Named entry formula for `IQFT_matrix`.** Definitional unfolding,
exposed as a reusable theorem for the recursive correctness proof. -/
theorem IQFT_matrix_apply (m : Nat) (y x : Fin (2^m)) :
    IQFT_matrix m y x
      = ((1 : ℂ) / Real.sqrt (2^m : ℝ)) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (x.val : ℂ) * (y.val : ℂ)
                     / (2^m : ℂ)) := rfl

/-- **At `n = 2`, the recursive `real_QFTinv_layer` produces `IQFT_matrix 2`.**
This is the first nontrivial inductive-base instance of the
arbitrary-n correctness `uc_eval_real_QFTinv_layer_eq_IQFT_matrix`,
proved by chaining `real_QFTinv_layer_two_eq_candidate` with
`uc_eval_real_QFTinv2_candidate_eq_IQFT_matrix`. -/
theorem uc_eval_real_QFTinv_layer_eq_IQFT_matrix_two :
    FormalRV.Framework.uc_eval (real_QFTinv_layer 2 : BaseUCom 2)
      = IQFT_matrix 2 := by
  rw [real_QFTinv_layer_two_eq_candidate]
  exact uc_eval_real_QFTinv2_candidate_eq_IQFT_matrix

/-- **Matrix-arithmetic index decomposition.** Pure scalar identity
underlying the recursive `IQFT_matrix` decomposition: when an index
splits into a high bit + low part (`z = 2^n · z_h + z_l`), the
product `xy / 2^(n+1)` decomposes into three additive terms:
- `2^(n-1) · x_h · y_h` — integer for `n ≥ 1`, contributes `exp(±2πi·N) = 1`.
- `(x_h · y_l + x_l · y_h) / 2` — half-integer offsets (the inter-bit phases).
- `x_l · y_l / 2^(n+1)` — the lower-block phase. Note the denominator
  is `2^(n+1)`, not `2^n`; the recursive lower block exponent is
  `exp(-π · I · x_l y_l / 2^n)`, which is half the `IQFT_matrix n`
  argument. This means the natural matrix-level recursion is not
  `IQFT_matrix (n+1) y x = ... · IQFT_matrix n y_l x_l` — the
  textbook QFT recursion uses a different decomposition involving
  controlled-phase corrections at every recursion level. -/
theorem IQFT_index_split (n : Nat) (_hn : 1 ≤ n) (xh yh xl yl : Nat) :
    ((2^n * xh + xl : ℂ) * (2^n * yh + yl) / 2^(n+1) : ℂ)
    = (2^(n-1) * xh * yh : ℂ)
      + ((xh * yl + xl * yh : ℂ)) / 2
      + ((xl * yl : ℂ) / 2^(n+1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  push_cast
  field_simp
  ring

/-- **Index reconstruction from MSB + low.** `x.val = x_h · 2^n + x_l`. -/
theorem iqft_index_reconstruct (n : Nat) (x : Fin (2^(n+1))) :
    x.val = (iqftHighBit n x).val * 2^n + (iqftLowBits n x).val := by
  show x.val = x.val / 2^n * 2^n + x.val % 2^n
  rw [Nat.div_add_mod' x.val (2^n)]

/-- **`exp(-2πi · k) = 1` for natural `k`.** Consequence of
`Complex.exp_int_mul_two_pi_mul_I`. -/
theorem exp_neg_two_pi_I_mul_nat (k : Nat) :
    Complex.exp ((-2 * Real.pi * (k : ℝ) : ℂ) * Complex.I) = 1 := by
  have h := Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ))
  push_cast at h
  rw [show ((-2 * Real.pi * (k : ℝ) : ℂ) * Complex.I)
        = -(k : ℂ) * (2 * Real.pi * Complex.I) from by push_cast; ring]
  exact h

/-- **`exp(-π · I · k) = (-1)^k` for natural `k`.** Drives the
half-integer cross-term phase in the IQFT decomposition. -/
theorem exp_neg_pi_I_mul_nat (k : Nat) :
    Complex.exp (((-Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) = (-1 : ℂ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (((-Real.pi * ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)
          = (((-Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) + (-((Real.pi : ℂ) * Complex.I))
       from by push_cast; ring]
    rw [Complex.exp_add, ih]
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]
    rw [pow_succ]
    ring

/-- **Scalar normalization for the IQFT recursion.** Factors the
inverse square-root: `1/√(2^(n+1)) = (1/√2) · (1/√(2^n))`. -/
theorem inv_sqrt_pow_two_succ_factor (n : Nat) :
    (1 : ℂ) / Real.sqrt (2^(n+1) : ℝ)
      = ((1 : ℂ) / Real.sqrt 2) * ((1 : ℂ) / Real.sqrt (2^n : ℝ)) := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h_sqrt_mul : Real.sqrt (2^(n+1) : ℝ) = Real.sqrt 2 * Real.sqrt (2^n : ℝ) := by
    rw [show ((2 : ℝ)^(n+1)) = 2 * 2^n from by ring]
    rw [Real.sqrt_mul (le_of_lt h2_pos)]
  rw [h_sqrt_mul]
  push_cast
  field_simp

/-! ### Countdown circuit + structural decomposition of `real_QFTinv_layer`

`real_QFTinv_layer n` consists of `bit_reversal_swaps n` followed by
`real_QFTinv_layer.countdown n`. The countdown applies inverse-QFT
phase ladders for target = n-1 down to 0 in that order. This section
exposes the countdown structure for reusable theorems. -/

/-- Unfolding: `countdown n 0 = SKIP`. -/
theorem countdown_zero (n : Nat) :
    real_QFTinv_layer.countdown n 0 = (SKIP : FormalRV.Framework.BaseUCom n) := by
  conv_lhs => unfold real_QFTinv_layer.countdown

/-- Unfolding: `countdown n (k+1) = ladder n k ; countdown n k`.

By the seq semantics, applying `countdown n (k+1)` to a state `v` first
applies the ladder for target `k`, then `countdown n k` (which processes
targets `k-1, k-2, ..., 0`). -/
theorem countdown_succ (n k : Nat) :
    real_QFTinv_layer.countdown n (k+1)
      = UCom.seq (inverse_qft_phase_ladder n k) (real_QFTinv_layer.countdown n k) := by
  conv_lhs => unfold real_QFTinv_layer.countdown

/-- **Structural decomposition of `real_QFTinv_layer`.** -/
theorem real_QFTinv_layer_decomp (n : Nat) :
    (real_QFTinv_layer n : FormalRV.Framework.BaseUCom n)
      = UCom.seq (bit_reversal_swaps n) (real_QFTinv_layer.countdown n n) := by
  unfold real_QFTinv_layer
  rfl

/-- **State-level decomposition**: applying `real_QFTinv_layer n` to a state
equals applying `bit_reversal_swaps n` first, then `countdown n n`. -/
theorem real_QFTinv_layer_acts (n : Nat) (v : Matrix (Fin (2^n)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval (real_QFTinv_layer n : FormalRV.Framework.BaseUCom n) * v
    = FormalRV.Framework.uc_eval
        (real_QFTinv_layer.countdown n n : FormalRV.Framework.BaseUCom n)
      * (FormalRV.Framework.uc_eval
          (bit_reversal_swaps n : FormalRV.Framework.BaseUCom n) * v) := by
  rw [real_QFTinv_layer_decomp]
  rw [uc_eval_seq_mul]

/-- **Countdown 0 acts as identity** (for positive `n`). -/
theorem countdown_zero_acts (n : Nat) (hn : 0 < n) (v : Matrix (Fin (2^n)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (real_QFTinv_layer.countdown n 0 : FormalRV.Framework.BaseUCom n) * v = v := by
  rw [countdown_zero]
  rw [show (SKIP : FormalRV.Framework.BaseUCom n) = ID 0 from rfl]
  rw [uc_eval_ID_eq_one hn]
  exact Matrix.one_mul _

/-- **Structural recursion for `countdown` action**: `countdown (k+1)` applied
to `v` equals `countdown k` applied to (`ladder k` applied to `v`). -/
theorem countdown_succ_acts (n k : Nat) (v : Matrix (Fin (2^n)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (real_QFTinv_layer.countdown n (k+1) : FormalRV.Framework.BaseUCom n) * v
    = FormalRV.Framework.uc_eval
        (real_QFTinv_layer.countdown n k : FormalRV.Framework.BaseUCom n)
      * (FormalRV.Framework.uc_eval
          (inverse_qft_phase_ladder n k : FormalRV.Framework.BaseUCom n) * v) := by
  rw [countdown_succ]
  rw [uc_eval_seq_mul]

/-- **SWAP gate action on `f_to_vec`.** Direct wrapper around
`f_to_vec_SWAP` using the framework's CNOT-CNOT-CNOT unfolding of `SWAP`. -/
theorem uc_eval_SWAP_on_f_to_vec {n : Nat} (a b : Nat)
    (ha : a < n) (hb : b < n) (hab : a ≠ b) (f : Nat → Bool) :
    FormalRV.Framework.uc_eval
        (FormalRV.Framework.BaseUCom.SWAP a b : FormalRV.Framework.BaseUCom n)
      * f_to_vec n f
    = f_to_vec n (swapBits f a b) := by
  rw [show (FormalRV.Framework.BaseUCom.SWAP a b : FormalRV.Framework.BaseUCom n)
        = UCom.seq (FormalRV.Framework.BaseUCom.CNOT a b)
            (UCom.seq (FormalRV.Framework.BaseUCom.CNOT b a)
              (FormalRV.Framework.BaseUCom.CNOT a b)) from rfl]
  rw [f_to_vec_SWAP n a b ha hb hab f]
  congr 1
  funext i
  unfold swapBits update
  by_cases hia : i = a
  · subst hia; simp [hab]
  · by_cases hib : i = b
    · subst hib; simp [Ne.symm hab]
    · simp [hia, hib]

theorem bit_reversal_loop_step (n i : Nat) (hi : i + i + 1 < n) :
    bit_reversal_swaps.loop n i
      = UCom.seq (FormalRV.Framework.BaseUCom.SWAP i (n - 1 - i))
          (bit_reversal_swaps.loop n (i + 1)) := by
  conv_lhs => unfold bit_reversal_swaps.loop
  rw [if_pos hi]

theorem bit_reversal_loop_base (n i : Nat) (hi : ¬ i + i + 1 < n) :
    bit_reversal_swaps.loop n i = (SKIP : FormalRV.Framework.BaseUCom n) := by
  conv_lhs => unfold bit_reversal_swaps.loop
  rw [if_neg hi]

theorem applySwapsFrom_step (n k : Nat) (f : Nat → Bool) (hk : 2 * k + 1 < n) :
    applySwapsFrom n k f = applySwapsFrom n (k+1) (swapBits f k (n-1-k)) := by
  conv_lhs => unfold applySwapsFrom
  rw [dif_pos hk]

theorem applySwapsFrom_base (n k : Nat) (f : Nat → Bool) (hk : ¬ 2 * k + 1 < n) :
    applySwapsFrom n k f = f := by
  conv_lhs => unfold applySwapsFrom
  rw [dif_neg hk]

/-- **Auxiliary recursion.** Action of the inner `bit_reversal_swaps.loop n k`
on `f_to_vec n f` equals `f_to_vec n (applySwapsFrom n k f)`. Proved by
strong induction on `n - 2*k`. -/
theorem bit_reversal_loop_acts_on_f_to_vec_aux
    (n : Nat) (hn : 0 < n) : ∀ (m : Nat), ∀ (k : Nat), ∀ (f : Nat → Bool),
    n - 2 * k = m →
    FormalRV.Framework.uc_eval
        (bit_reversal_swaps.loop n k : FormalRV.Framework.BaseUCom n)
      * f_to_vec n f
    = f_to_vec n (applySwapsFrom n k f) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k f hm
    by_cases hk_lt : 2 * k + 1 < n
    · have hk_lt2 : k + k + 1 < n := by omega
      have hkn : k < n := by omega
      have h_n_1_k : n - 1 - k < n := by omega
      have h_ne : k ≠ n - 1 - k := by omega
      rw [bit_reversal_loop_step n k hk_lt2]
      rw [uc_eval_seq_mul]
      rw [uc_eval_SWAP_on_f_to_vec k (n-1-k) hkn h_n_1_k h_ne f]
      rw [ih (n - 2 * (k+1)) (by omega) (k+1) (swapBits f k (n-1-k)) rfl]
      rw [← applySwapsFrom_step n k f hk_lt]
    · have hk_done2 : ¬ k + k + 1 < n := by omega
      rw [bit_reversal_loop_base n k hk_done2]
      rw [applySwapsFrom_base n k f hk_lt]
      rw [show (SKIP : FormalRV.Framework.BaseUCom n) = ID 0 from rfl]
      rw [uc_eval_ID_eq_one hn]
      exact Matrix.one_mul _

/-- **HEADLINE: Bit-reversal SWAPs basis action.** The full bit-reversal
cascade maps `f_to_vec n f` to `f_to_vec n (applySwapsFrom n 0 f)`. -/
theorem bit_reversal_swaps_acts_on_f_to_vec (n : Nat) (hn : 0 < n) (f : Nat → Bool) :
    FormalRV.Framework.uc_eval (bit_reversal_swaps n : FormalRV.Framework.BaseUCom n)
      * f_to_vec n f
    = f_to_vec n (applySwapsFrom n 0 f) := by
  rw [show (bit_reversal_swaps n : FormalRV.Framework.BaseUCom n)
        = bit_reversal_swaps.loop n 0 from by unfold bit_reversal_swaps; rfl]
  exact bit_reversal_loop_acts_on_f_to_vec_aux n hn (n - 0) 0 f rfl

/-- Recursive step for `inverse_qft_ladder_phase_from`. -/
theorem inverse_qft_ladder_phase_from_succ (n target : Nat) (f : Nat → Bool) (k : Nat)
    (hk : k < n) :
    inverse_qft_ladder_phase_from n target f k
    = (if f k ∧ f target then
         Complex.exp ((((-(Real.pi / 2 ^ (k - target))) : ℝ)) * Complex.I)
       else 1)
      * inverse_qft_ladder_phase_from n target f (k+1) := by
  unfold inverse_qft_ladder_phase_from
  rw [← Finset.insert_Ico_add_one_left_eq_Ico hk]
  rw [Finset.prod_insert]
  · intro h
    rw [Finset.mem_Ico] at h
    omega

/-- Base case for `inverse_qft_ladder_phase_from` at `k = n`. -/
theorem inverse_qft_ladder_phase_from_at_top (n target : Nat) (f : Nat → Bool) :
    inverse_qft_ladder_phase_from n target f n = 1 := by
  unfold inverse_qft_ladder_phase_from
  rw [show Finset.Ico n n = (∅ : Finset Nat) from Finset.Ico_self n]
  simp

/-- Step unfolding for `inverse_qft_phase_ladder.loop` at `j < n`. -/
theorem ladder_loop_step (n target j : Nat) (hj : j < n) :
    inverse_qft_phase_ladder.loop n target j
      = UCom.seq (controlled_Rz j target (-(Real.pi / (2 ^ (j - target) : ℝ))))
                 (inverse_qft_phase_ladder.loop n target (j + 1)) := by
  conv_lhs => unfold inverse_qft_phase_ladder.loop
  rw [if_pos hj]

/-- Base case unfolding: `inverse_qft_phase_ladder.loop n target n = H target`. -/
theorem ladder_loop_base (n target j : Nat) (hj : ¬ j < n) :
    inverse_qft_phase_ladder.loop n target j
      = (FormalRV.Framework.BaseUCom.H target : FormalRV.Framework.BaseUCom n) := by
  conv_lhs => unfold inverse_qft_phase_ladder.loop
  rw [if_neg hj]

/-- **Auxiliary recursion**: action of the inner `loop k` on `f_to_vec`.
For `target < k ≤ n`, applying `loop k` to a basis-state vector
produces a scalar `inverse_qft_ladder_phase_from n target f k` times
the H-applied state. -/
theorem ladder_loop_acts_on_f_to_vec_aux
    (n_arg : Nat) (target : Nat) (h_target : target < n_arg)
    (f : Nat → Bool) :
    ∀ m k, k ≤ n_arg → n_arg - k = m → target < k →
      FormalRV.Framework.uc_eval
          (inverse_qft_phase_ladder.loop n_arg target k :
            FormalRV.Framework.BaseUCom n_arg)
        * f_to_vec n_arg f
      = inverse_qft_ladder_phase_from n_arg target f k
        • (FormalRV.Framework.uc_eval
            (FormalRV.Framework.BaseUCom.H target : FormalRV.Framework.BaseUCom n_arg)
            * f_to_vec n_arg f) := by
  intro m
  induction m with
  | zero =>
    intro k hk hm htarget
    have hkn : k = n_arg := by omega
    subst hkn
    rw [ladder_loop_base k target k (by omega)]
    rw [inverse_qft_ladder_phase_from_at_top]
    rw [one_smul]
  | succ m ih =>
    intro k hk hm htarget
    have hk_lt : k < n_arg := by omega
    rw [ladder_loop_step n_arg target k hk_lt]
    rw [uc_eval_seq_mul]
    rw [controlled_Rz_acts_on_basis_correct n_arg k target hk_lt h_target (by omega) _ f]
    rw [Matrix.mul_smul]
    rw [ih (k+1) (by omega) (by omega) (by omega)]
    rw [smul_smul]
    rw [← inverse_qft_ladder_phase_from_succ n_arg target f k hk_lt]

/-- **HEADLINE: Ladder action on basis state.** The full
`inverse_qft_phase_ladder n target` applied to a basis state
`f_to_vec n f` equals `(ladder phase) • (H_target · f_to_vec n f)`,
where the ladder phase is the product of controlled-Rz contributions
from each control bit `j ∈ [target+1, n)`. -/
theorem inverse_qft_phase_ladder_acts_on_f_to_vec
    (n target : Nat) (h_target : target < n)
    (f : Nat → Bool) :
    FormalRV.Framework.uc_eval
        (inverse_qft_phase_ladder n target : FormalRV.Framework.BaseUCom n)
      * f_to_vec n f
    = inverse_qft_ladder_phase n target f
      • (FormalRV.Framework.uc_eval
          (FormalRV.Framework.BaseUCom.H target : FormalRV.Framework.BaseUCom n)
          * f_to_vec n f) := by
  show FormalRV.Framework.uc_eval
        (inverse_qft_phase_ladder.loop n target (target + 1) :
          FormalRV.Framework.BaseUCom n)
      * f_to_vec n f = _
  exact ladder_loop_acts_on_f_to_vec_aux n target h_target f
    (n - (target + 1)) (target + 1) (by omega) rfl (by omega)

/-- **HEADLINE: Successor entry decomposition for `IQFT_matrix`.**

For `n ≥ 1`, the `(y, x)` entry of `IQFT_matrix (n+1)` decomposes as

    (1/√(2^(n+1))) · (-1)^(x_h · y_l + x_l · y_h) · exp(-π · I · x_l · y_l / 2^n)

where `(x_h, x_l)` and `(y_h, y_l)` are the MSB/lower-bit splits of `x` and `y`.

This is the matrix-arithmetic foundation for the recursive IQFT
correctness proof.

**Note on the inner exponent**: it is `exp(-π · I · x_l y_l / 2^n)`,
which is **half** the `IQFT_matrix n y_l x_l` exponent
`exp(-2π · I · x_l y_l / 2^n)`. This means the natural IQFT recursion
is not a direct factoring `IQFT_(n+1) y x = ... · IQFT_n y_l x_l`.
The textbook QFT recursion accounts for this discrepancy via the
controlled-phase ladder that conjugates the inner IQFT_n on the
control register (not yet formalized here). -/
theorem IQFT_matrix_succ_entry_decomp
    (n : Nat) (hn : 1 ≤ n)
    (y x : Fin (2^(n+1))) :
    IQFT_matrix (n+1) y x
      = ((1 : ℂ) / Real.sqrt (2^(n+1) : ℝ))
        * ((-1 : ℂ) ^
            ((iqftHighBit n x).val * (iqftLowBits n y).val
              + (iqftLowBits n x).val * (iqftHighBit n y).val))
        * Complex.exp (-(Real.pi : ℂ) * Complex.I
            * (iqftLowBits n x).val * (iqftLowBits n y).val / (2^n : ℂ)) := by
  unfold IQFT_matrix iqftHighBit iqftLowBits
  set xH : ℕ := x.val / 2^n
  set xL : ℕ := x.val % 2^n
  set yH : ℕ := y.val / 2^n
  set yL : ℕ := y.val % 2^n
  have hx_split : (x.val : ℂ) = (xH : ℂ) * 2^n + (xL : ℂ) := by
    have h := Nat.div_add_mod' x.val (2^n)
    push_cast
    rw [show ((x.val / 2^n : Nat) : ℂ) * (2^n : ℂ) + ((x.val % 2^n : Nat) : ℂ)
          = ((x.val / 2^n * 2^n + x.val % 2^n : Nat) : ℂ) from by push_cast; ring]
    congr 1
    exact_mod_cast h.symm
  have hy_split : (y.val : ℂ) = (yH : ℂ) * 2^n + (yL : ℂ) := by
    have h := Nat.div_add_mod' y.val (2^n)
    push_cast
    rw [show ((y.val / 2^n : Nat) : ℂ) * (2^n : ℂ) + ((y.val % 2^n : Nat) : ℂ)
          = ((y.val / 2^n * 2^n + y.val % 2^n : Nat) : ℂ) from by push_cast; ring]
    congr 1
    exact_mod_cast h.symm
  rw [hx_split, hy_split]
  have hsplit := IQFT_index_split n hn xH yH xL yL
  rw [show -(2 * Real.pi * Complex.I) * ((xH : ℂ) * 2^n + xL) * ((yH : ℂ) * 2^n + yL) /
          (2^(n+1) : ℂ)
        = -(2 * Real.pi * Complex.I) *
            ((2^n * (xH : ℂ) + xL) * (2^n * (yH : ℂ) + yL) / (2^(n+1) : ℂ)) from by ring]
  rw [hsplit]
  rw [show -(2 * Real.pi * Complex.I) *
        ((2^(n-1) * (xH : ℂ) * (yH : ℂ))
          + ((xH : ℂ) * (yL : ℂ) + (xL : ℂ) * (yH : ℂ)) / 2
          + ((xL : ℂ) * (yL : ℂ)) / (2^(n+1) : ℂ))
      = (-2 * Real.pi * ((xH * yH * 2^(n-1) : Nat) : ℝ) : ℂ) * Complex.I
        + ((-Real.pi * ((xH * yL + xL * yH : Nat) : ℝ) : ℝ) : ℂ) * Complex.I
        + (-((Real.pi : ℂ) * Complex.I) * (xL : ℂ) * (yL : ℂ) / (2^n : ℂ))
       from by
       push_cast
       rw [show ((2 : ℂ)^(n+1)) = 2 * 2^n from by ring]
       field_simp
       ring]
  rw [Complex.exp_add, Complex.exp_add]
  rw [exp_neg_two_pi_I_mul_nat]
  rw [exp_neg_pi_I_mul_nat]
  conv_rhs => rw [show ((-1 : ℂ) ^ (xH * yL + xL * yH))
                  = (-1 : ℂ) ^ (xH * yL) * (-1 : ℂ) ^ (xL * yH) from pow_add _ _ _]
  -- LHS and RHS differ only by associativity of multiplication
  -- inside Complex.exp and outside.
  have h_exp_eq : Complex.exp (-((Real.pi : ℂ) * Complex.I) * (xL : ℂ) * (yL : ℂ) / (2^n : ℂ))
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * ((⟨xL, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ : Fin (2^n)).val : ℂ)
            * ((⟨yL, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ : Fin (2^n)).val : ℂ) / (2^n : ℂ)) := by
    congr 1
    ring
  rw [h_exp_eq]
  ring

/-- **HEADLINE: Full real-QPE eigenstate theorem assuming IQFT correctness.**
Given `h_IQFT : uc_eval (real_QFTinv_on m) = IQFT_matrix m`, the
real-QPE circuit applied to `|0^m⟩ ⊗ ψ` (where `ψ` is a QPE eigenstate
with phase θ) yields `kron_vec (qpe_phase_state m θ) ψ`. This is the
exact form needed to drive `QPE_MMI_correct`; the only remaining
obligation is proving `h_IQFT` for arbitrary `m`. -/
theorem real_QPE_on_eigenstate_from_IQFT_correct
    {m anc : Nat} (hmanc : 0 < m + anc) (hm : 0 < m)
    (f : Nat → BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ)
    (θ : ℝ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (h_eig_data : ∀ i, i < m →
      FormalRV.Framework.uc_eval (f i) * ψ =
        qpeEigenvalue m i θ • ψ)
    (h_wt_IQFT : UCom.WellTyped m (real_QFTinv_on m))
    (h_IQFT : FormalRV.Framework.uc_eval (real_QFTinv_on m : BaseUCom m)
                = IQFT_matrix m) :
    FormalRV.Framework.uc_eval (real_QPE m anc f)
      * kron_vec (FormalRV.Framework.kron_zeros m) ψ
    = kron_vec (qpe_phase_state m θ) ψ := by
  unfold real_QPE
  rw [uc_eval_seq_mul, uc_eval_seq_mul]
  rw [QPE_pre_QFT_on_eigenstate_fourier_form hmanc hm f ψ θ h_wt_all h_eig_data]
  exact real_QFTinv_on_fourier_weighted_kron_state_from_matrix_correct
    θ ψ h_wt_IQFT h_IQFT

/-! ### Recursive countdown output + composition with bit reversal

The countdown circuit produces an exponentially-growing superposition
(one Hadamard branch per target). Rather than expanding this into a
single sum, we define the expected output recursively, matching the
state-action recurrence `countdown_succ_acts`, and prove the action
theorem against that recursive form. -/

/-- **Explicit two-branch ladder action.** Combines
`inverse_qft_phase_ladder_acts_on_f_to_vec` with `f_to_vec_H_uc_eval`
to expose the Hadamard expansion as a sum of two `f_to_vec` terms. -/
theorem inverse_qft_phase_ladder_explicit_on_f_to_vec
    (n target : Nat) (h_target : target < n)
    (f : Nat → Bool) :
    FormalRV.Framework.uc_eval
        (inverse_qft_phase_ladder n target : FormalRV.Framework.BaseUCom n)
      * f_to_vec n f
    = inverse_qft_ladder_phase n target f •
      (((Real.sqrt 2 / 2 : ℂ) • f_to_vec n (update f target false))
        + ((if f target then -(Real.sqrt 2 / 2 : ℂ) else (Real.sqrt 2 / 2 : ℂ))
            • f_to_vec n (update f target true))) := by
  rw [inverse_qft_phase_ladder_acts_on_f_to_vec n target h_target f]
  rw [f_to_vec_H_uc_eval n target h_target]
  congr 1
  by_cases h : f target
  · rw [if_pos h, if_pos h]; simp
  · rw [if_neg h, if_neg h]; simp

theorem countdown_output_zero (n : Nat) (f : Nat → Bool) :
    countdown_output n 0 f = f_to_vec n f := rfl

theorem countdown_output_succ (n k : Nat) (f : Nat → Bool) :
    countdown_output n (k+1) f
      = inverse_qft_ladder_phase n k f •
          (((Real.sqrt 2 / 2 : ℂ) • countdown_output n k (update f k false))
            + ((if f k then -(Real.sqrt 2 / 2 : ℂ) else (Real.sqrt 2 / 2 : ℂ))
                • countdown_output n k (update f k true))) := rfl

/-- **HEADLINE: Countdown action on `f_to_vec`.** Applying `countdown n k`
to a basis vector `f_to_vec n f` produces `countdown_output n k f`,
the recursively-defined expected output. Proof by induction on k,
using `countdown_succ_acts` and the explicit ladder action. -/
theorem countdown_acts_on_f_to_vec (n : Nat) (hn : 0 < n) :
    ∀ k, k ≤ n → ∀ (f : Nat → Bool),
      FormalRV.Framework.uc_eval
          (real_QFTinv_layer.countdown n k : FormalRV.Framework.BaseUCom n)
        * f_to_vec n f
      = countdown_output n k f := by
  intro k
  induction k with
  | zero => intro hk f; rw [countdown_zero_acts n hn]; rfl
  | succ k ih =>
    intro hk f
    have hk_lt : k < n := by omega
    have hk_le : k ≤ n := by omega
    rw [countdown_succ_acts]
    rw [inverse_qft_phase_ladder_explicit_on_f_to_vec n k hk_lt f]
    rw [Matrix.mul_smul, Matrix.mul_add]
    rw [Matrix.mul_smul, Matrix.mul_smul]
    rw [ih hk_le (update f k false)]
    rw [ih hk_le (update f k true)]
    rfl

/-- **Full `real_QFTinv_layer` action on `f_to_vec`.** Combines bit-reversal
and countdown: the layer applied to `f_to_vec n f` equals
`countdown_output n n (applySwapsFrom n 0 f)`. -/
theorem real_QFTinv_layer_output_on_f_to_vec
    (n : Nat) (hn : 0 < n) (f : Nat → Bool) :
    FormalRV.Framework.uc_eval (real_QFTinv_layer n : FormalRV.Framework.BaseUCom n)
      * f_to_vec n f
    = countdown_output n n (applySwapsFrom n 0 f) := by
  rw [real_QFTinv_layer_acts]
  rw [bit_reversal_swaps_acts_on_f_to_vec n hn f]
  exact countdown_acts_on_f_to_vec n hn n (le_refl n) _

/-- **`n = 1`: recursive layer matches `IQFT_matrix 1`.** Trivial since
`bit_reversal_swaps 1 = SKIP`, `countdown 1 = H 0 ; SKIP`, and the
matrix theorem for `H 0` is already in place. -/
theorem uc_eval_real_QFTinv_layer_eq_IQFT_matrix_one :
    FormalRV.Framework.uc_eval (real_QFTinv_layer 1 : FormalRV.Framework.BaseUCom 1)
      = IQFT_matrix 1 := by
  rw [real_QFTinv_layer_decomp]
  show FormalRV.Framework.uc_eval
        (UCom.seq (bit_reversal_swaps 1) (real_QFTinv_layer.countdown 1 1)) = IQFT_matrix 1
  rw [show (bit_reversal_swaps 1 : FormalRV.Framework.BaseUCom 1) = SKIP from by
    unfold bit_reversal_swaps
    rw [bit_reversal_loop_base 1 0 (by omega)]]
  rw [countdown_succ]
  rw [show real_QFTinv_layer.countdown 1 0 = (SKIP : FormalRV.Framework.BaseUCom 1)
       from countdown_zero 1]
  rw [show (inverse_qft_phase_ladder 1 0 : FormalRV.Framework.BaseUCom 1)
        = FormalRV.Framework.BaseUCom.H 0 from by
    unfold inverse_qft_phase_ladder
    rw [ladder_loop_base 1 0 1 (by omega)]]
  show FormalRV.Framework.uc_eval (UCom.seq (SKIP : FormalRV.Framework.BaseUCom 1)
        (UCom.seq (FormalRV.Framework.BaseUCom.H 0) (SKIP))) = IQFT_matrix 1
  rw [show (SKIP : FormalRV.Framework.BaseUCom 1) = ID 0 from rfl]
  show FormalRV.Framework.uc_eval (UCom.seq (ID 0) (UCom.seq (BaseUCom.H 0) (ID 0)))
      = IQFT_matrix 1
  rw [show FormalRV.Framework.uc_eval (UCom.seq (ID 0)
        (UCom.seq (BaseUCom.H 0) (ID 0)) : FormalRV.Framework.BaseUCom 1)
        = FormalRV.Framework.uc_eval (UCom.seq (BaseUCom.H 0) (ID 0))
          * FormalRV.Framework.uc_eval (ID 0) from rfl]
  rw [uc_eval_ID_eq_one (show (0:Nat) < 1 from by omega), Matrix.mul_one]
  rw [show FormalRV.Framework.uc_eval (UCom.seq (BaseUCom.H 0) (ID 0) :
        FormalRV.Framework.BaseUCom 1)
        = FormalRV.Framework.uc_eval (ID 0)
          * FormalRV.Framework.uc_eval (BaseUCom.H 0) from rfl]
  rw [uc_eval_ID_eq_one (show (0:Nat) < 1 from by omega), Matrix.one_mul]
  exact uc_eval_real_QFTinv_eq_IQFT_matrix_one

/-! ### Matching countdown_output to IQFT_matrix column

The final semantic bridge: `countdown_output n n (applySwapsFrom n 0 ...)`
should equal `IQFT_matrix n · basis_vector x`. This section closes
small cases (n=1, n=2) and provides the entry-formula API for the
arbitrary-n induction. -/

/-- **Entry formula for IQFT_matrix · basis_vector.** Picks out the
`(y, x)` entry of `IQFT_matrix`. -/
theorem IQFT_matrix_mul_basis_apply (n : Nat) (x y : Fin (2^n)) :
    (IQFT_matrix n * FormalRV.Framework.basis_vector (2^n) x.val) y 0
    = IQFT_matrix n y x := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single x]
  · rw [show (FormalRV.Framework.basis_vector (2^n) x.val) x 0 = 1 from by
      rw [basis_vector_apply]; simp]
    ring
  · intro i _ hix
    rw [show (FormalRV.Framework.basis_vector (2^n) x.val) i 0 = 0 from by
      rw [basis_vector_apply]
      have : i.val ≠ x.val := fun h => hix (Fin.ext h)
      simp [this]]
    ring
  · simp

/-- **`n = 1` column equality**: derived from the n=1 layer matrix
correctness via the `real_QFTinv_layer_output_on_f_to_vec` bridge. -/
theorem countdown_output_eq_IQFT_column_one (x : Fin (2^1)) :
    countdown_output 1 1 (applySwapsFrom 1 0 (nat_to_funbool 1 x.val))
    = IQFT_matrix 1 * FormalRV.Framework.basis_vector (2^1) x.val := by
  rw [← real_QFTinv_layer_output_on_f_to_vec 1 (by omega) _]
  rw [uc_eval_real_QFTinv_layer_eq_IQFT_matrix_one]
  rw [show f_to_vec 1 (nat_to_funbool 1 x.val)
        = FormalRV.Framework.basis_vector (2^1) x.val from
      (basis_vector_eq_f_to_vec_nat_to_funbool 1 x).symm]

/-- **`n = 2` column equality**: derived from the n=2 layer matrix
correctness. -/
theorem countdown_output_eq_IQFT_column_two (x : Fin (2^2)) :
    countdown_output 2 2 (applySwapsFrom 2 0 (nat_to_funbool 2 x.val))
    = IQFT_matrix 2 * FormalRV.Framework.basis_vector (2^2) x.val := by
  rw [← real_QFTinv_layer_output_on_f_to_vec 2 (by omega) _]
  rw [uc_eval_real_QFTinv_layer_eq_IQFT_matrix_two]
  rw [show f_to_vec 2 (nat_to_funbool 2 x.val)
        = FormalRV.Framework.basis_vector (2^2) x.val from
      (basis_vector_eq_f_to_vec_nat_to_funbool 2 x).symm]

/-- **`n = 1` column equality** in `countdownColumn` form. -/
theorem countdownColumn_eq_IQFT_column_one (x : Fin (2^1)) :
    countdownColumn 1 x = IQFT_matrix 1 * FormalRV.Framework.basis_vector (2^1) x.val := by
  unfold countdownColumn bitReversedBasisFun basisFunOfIndex
  exact countdown_output_eq_IQFT_column_one x

/-- **`n = 2` column equality** in `countdownColumn` form. -/
theorem countdownColumn_eq_IQFT_column_two (x : Fin (2^2)) :
    countdownColumn 2 x = IQFT_matrix 2 * FormalRV.Framework.basis_vector (2^2) x.val := by
  unfold countdownColumn bitReversedBasisFun basisFunOfIndex
  exact countdown_output_eq_IQFT_column_two x

/-! ### Dimension-split lemmas: (n+1)-qubit ↔ n-qubit + extra qubit

**Convention** (established by inspecting `countdown_output` /
`inverse_qft_phase_ladder`):

- Qubit `n` (the LSB in MSB-first convention) is the "untouched" extra
  qubit when going from `(n+1)`-qubit to `n`-qubit systems.
- For `k ≤ n`, `countdown_output (n+1) k f` processes ladders for
  targets `0..k-1`. Qubit `n` is never a target (never Hadamard'd),
  but is a CONTROL for every target `< n`, contributing extra phase
  factors.
- The split is therefore NOT a clean tensor product — there's an
  extra phase from qubit `n`'s controlling role. -/

/-- **`f_to_vec` dimension split.** `f_to_vec (n+1) f` factors as the
kron product of `f_to_vec n f` (using the lower n bits) and a
1-qubit basis vector encoding `f n`. -/
theorem f_to_vec_dim_split (n : Nat) (f : Nat → Bool) :
    f_to_vec (n+1) f
    = kron_vec (f_to_vec n f)
        (FormalRV.Framework.basis_vector 2 (if f n then 1 else 0)) := by
  unfold f_to_vec
  have h_fb_ne_pow : funbool_to_nat n f < 2^n := funbool_to_nat_lt n f
  have h_bit_lt : (if f n then 1 else 0) < 2 := by split_ifs <;> omega
  rw [show (FormalRV.Framework.basis_vector (2^n) (funbool_to_nat n f)
        : Matrix (Fin (2^n)) (Fin 1) ℂ)
        = FormalRV.Framework.basis_vector (2^n)
            (⟨funbool_to_nat n f, h_fb_ne_pow⟩ : Fin (2^n)).val from rfl]
  rw [show (FormalRV.Framework.basis_vector 2 (if f n then 1 else 0)
        : Matrix (Fin 2) (Fin 1) ℂ)
        = FormalRV.Framework.basis_vector (2^1)
            (⟨if f n then 1 else 0, h_bit_lt⟩ : Fin (2^1)).val from by simp]
  rw [kron_vec_basis_eq_basis_combine n 1
        ⟨funbool_to_nat n f, h_fb_ne_pow⟩ ⟨if f n then 1 else 0, h_bit_lt⟩]
  unfold kron_vec_combine
  congr 1
  show funbool_to_nat (n+1) f = funbool_to_nat n f * 2^1 + (if f n then 1 else 0)
  rw [show funbool_to_nat (n+1) f
        = 2 * funbool_to_nat n f + (if f n then 1 else 0) from rfl]
  ring

/-- **Ladder phase dimension split.** For `target < n`, the
`(n+1)`-qubit ladder phase factors as `(extra factor from qubit n) ·
(n-qubit ladder phase)`. The extra factor is the controlled-Rz
contribution from the highest qubit `n` onto the target. -/
theorem inverse_qft_ladder_phase_dim_split
    (n target : Nat) (h_target : target < n)
    (f : Nat → Bool) :
    inverse_qft_ladder_phase (n+1) target f
    = (if f n ∧ f target then
         Complex.exp ((((-(Real.pi / 2 ^ (n - target))) : ℝ)) * Complex.I)
       else 1)
      * inverse_qft_ladder_phase n target f := by
  unfold inverse_qft_ladder_phase inverse_qft_ladder_phase_from
  rw [Nat.Ico_succ_right_eq_insert_Ico (by omega : target + 1 ≤ n)]
  rw [Finset.prod_insert]
  · intro h
    rw [Finset.mem_Ico] at h
    omega

/-- `embedWithExtraBit` commutes with scalar multiplication. -/
theorem embedWithExtraBit_smul (n : Nat) (extra : Bool) (c : ℂ)
    (v : Matrix (Fin (2^n)) (Fin 1) ℂ) :
    embedWithExtraBit n extra (c • v) = c • embedWithExtraBit n extra v := by
  unfold embedWithExtraBit; rw [kron_vec_smul_left]

/-- `embedWithExtraBit` commutes with addition. -/
theorem embedWithExtraBit_add (n : Nat) (extra : Bool)
    (v w : Matrix (Fin (2^n)) (Fin 1) ℂ) :
    embedWithExtraBit n extra (v + w)
    = embedWithExtraBit n extra v + embedWithExtraBit n extra w := by
  unfold embedWithExtraBit; rw [kron_vec_add_left]

theorem cumulative_extra_phase_zero (n : Nat) (f : Nat → Bool) :
    cumulative_extra_phase n 0 f = 1 := by
  unfold cumulative_extra_phase; simp

theorem cumulative_extra_phase_succ (n k : Nat) (f : Nat → Bool) :
    cumulative_extra_phase n (k+1) f
    = cumulative_extra_phase n k f *
      (if f n ∧ f k then
        Complex.exp ((((-(Real.pi / 2 ^ (n - k))) : ℝ)) * Complex.I)
      else 1) := by
  unfold cumulative_extra_phase
  rw [Finset.prod_range_succ]

/-- **Extra-bit update lemma**: updating position `k < n` doesn't change
the value at position `n`. -/
theorem extra_bit_update_lt (n k : Nat) (hk : k < n) (f : Nat → Bool) (b : Bool) :
    update f k b n = f n := by
  unfold update; rw [if_neg (by omega)]

/-- **Cumulative extra phase update-branch lemma**: updating position
`k < n` doesn't change the cumulative extra phase product over targets
`t ∈ [0, k)`. -/
theorem cumulative_extra_phase_update_branch
    (n k : Nat) (hk : k < n) (f : Nat → Bool) (b : Bool) :
    cumulative_extra_phase n k (update f k b)
    = cumulative_extra_phase n k f := by
  unfold cumulative_extra_phase
  apply Finset.prod_congr rfl
  intro t ht
  rw [Finset.mem_range] at ht
  have htk : t ≠ k := by omega
  rw [extra_bit_update_lt n k hk f b]
  rw [show update f k b t = f t from by unfold update; rw [if_neg htk]]

/-- **HEADLINE: Countdown output dimension split.** For `k ≤ n`, the
`(n+1)`-qubit countdown output factors as a cumulative-extra-phase
scalar times the n-qubit countdown output embedded with the
extra-bit `f n`. Proof by induction on k: base via
`f_to_vec_dim_split`; successor via `inverse_qft_ladder_phase_dim_split`
+ the update lemmas + bilinearity of `embedWithExtraBit`, closed by
`module`. -/
theorem countdown_output_dim_split (n : Nat) :
    ∀ k, k ≤ n → ∀ (f : Nat → Bool),
      countdown_output (n+1) k f
      = cumulative_extra_phase n k f •
        embedWithExtraBit n (f n) (countdown_output n k f) := by
  intro k
  induction k with
  | zero =>
    intro hk f
    rw [countdown_output_zero, countdown_output_zero]
    rw [cumulative_extra_phase_zero, one_smul]
    unfold embedWithExtraBit
    exact f_to_vec_dim_split n f
  | succ k ih =>
    intro hk f
    have hk_lt : k < n := by omega
    have hk_le : k ≤ n := by omega
    rw [countdown_output_succ, countdown_output_succ]
    rw [ih hk_le (update f k false), ih hk_le (update f k true)]
    rw [extra_bit_update_lt n k hk_lt f false, extra_bit_update_lt n k hk_lt f true]
    rw [cumulative_extra_phase_update_branch n k hk_lt f false]
    rw [cumulative_extra_phase_update_branch n k hk_lt f true]
    rw [inverse_qft_ladder_phase_dim_split n k hk_lt f]
    rw [cumulative_extra_phase_succ n k f]
    rw [embedWithExtraBit_smul, embedWithExtraBit_add,
        embedWithExtraBit_smul, embedWithExtraBit_smul]
    module

/-- **Full-k specialization** of `countdown_output_dim_split`: at `k = n`,
the (n+1)-qubit countdown output factors through the full n-qubit
countdown. -/
theorem countdown_output_dim_split_full (n : Nat) (f : Nat → Bool) :
    countdown_output (n+1) n f
    = cumulative_extra_phase n n f •
      embedWithExtraBit n (f n) (countdown_output n n f) :=
  countdown_output_dim_split n n (le_refl n) f

/-- **Index reconstruction**: `y.val = high_n.val · 2 + lsb.val`. -/
theorem iqft_index_reconstruct_highN_low1 (n : Nat) (y : Fin (2^(n+1))) :
    y.val = (iqftHighBitsN n y).val * 2 + (iqftLowBitLSB n y).val := by
  show y.val = (y.val / 2) * 2 + y.val % 2
  rw [Nat.div_add_mod' y.val 2]

/-! ### Bit-reversal action formula and successor split

The bit-reversal cascade `applySwapsFrom n 0 f` maps position `i` to
the value at position `n-1-i` of the original `f`, for `i < n`. This
unlocks the bit-reversal successor split lemmas that bridge the
(n+1)-qubit and n-qubit countdown columns. -/

/-- `swapBits f a b a = f b`. -/
theorem swapBits_left (f : Nat → Bool) (a b : Nat) :
    swapBits f a b a = f b := by unfold swapBits; simp

/-- `swapBits f a b b = f a` (when `a ≠ b`). -/
theorem swapBits_right (f : Nat → Bool) (a b : Nat) (hab : a ≠ b) :
    swapBits f a b b = f a := by
  unfold swapBits; rw [if_neg (Ne.symm hab), if_pos rfl]

/-- `swapBits f a b i = f i` when `i ∉ {a, b}`. -/
theorem swapBits_other (f : Nat → Bool) (a b i : Nat) (hia : i ≠ a) (hib : i ≠ b) :
    swapBits f a b i = f i := by
  unfold swapBits; rw [if_neg hia, if_neg hib]

/-- **Partial-reversal invariant.** Starting from index `k`,
`applySwapsFrom n k f` reverses positions in `[k, n-1-k]` (and leaves
positions outside this range unchanged). Proof by strong induction
on `n - 2*k`. -/
theorem applySwapsFrom_apply_region (n : Nat) :
    ∀ (m k : Nat), n - 2 * k = m → ∀ (f : Nat → Bool) (i : Nat),
      applySwapsFrom n k f i =
        if k ≤ i ∧ i ≤ n - 1 - k then f (n - 1 - i) else f i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hm f i
    by_cases hk_lt : 2 * k + 1 < n
    · rw [applySwapsFrom_step n k f hk_lt]
      rw [ih (n - 2 * (k+1)) (by omega) (k+1) rfl (swapBits f k (n-1-k)) i]
      by_cases hi_eq_k : i = k
      · rw [hi_eq_k, if_neg (by omega : ¬(k + 1 ≤ k ∧ k ≤ n - 1 - (k+1))),
            swapBits_left, if_pos (by omega : k ≤ k ∧ k ≤ n - 1 - k)]
      · by_cases hi_eq_nk : i = n - 1 - k
        · rw [hi_eq_nk, if_neg (by omega : ¬(k + 1 ≤ n - 1 - k ∧ n - 1 - k ≤ n - 1 - (k+1)))]
          rw [swapBits_right f k (n-1-k) (by omega : k ≠ n - 1 - k)]
          rw [if_pos (by omega : k ≤ n - 1 - k ∧ n - 1 - k ≤ n - 1 - k)]
          rw [show n - 1 - (n - 1 - k) = k from by omega]
        · by_cases hi_inner : k + 1 ≤ i ∧ i ≤ n - 1 - (k+1)
          · rw [if_pos hi_inner]
            rw [swapBits_other f k (n-1-k) (n-1-i) (by omega) (by omega)]
            rw [if_pos (by omega : k ≤ i ∧ i ≤ n - 1 - k)]
          · rw [if_neg hi_inner, swapBits_other f k (n-1-k) i hi_eq_k hi_eq_nk]
            rw [if_neg (by omega : ¬(k ≤ i ∧ i ≤ n - 1 - k))]
    · rw [applySwapsFrom_base n k f hk_lt]
      by_cases h_then : k ≤ i ∧ i ≤ n - 1 - k
      · rw [if_pos h_then, ← (show i = n - 1 - i from by omega)]
      · rw [if_neg h_then]

end FormalRV.SQIRPort
