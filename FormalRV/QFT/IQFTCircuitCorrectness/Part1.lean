/- IQFTCircuitCorrectness — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.QPE.PhaseKickback
import FormalRV.QPE.QPEAmplitude
import FormalRV.QFT.IQFTDefinitions

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


end FormalRV.SQIRPort
