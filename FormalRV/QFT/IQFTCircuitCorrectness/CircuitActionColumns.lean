/- IQFTCircuitCorrectness — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.QFT.IQFTCircuitCorrectness.OneAndTwoQubitCorrectness

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom

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


end FormalRV.SQIRPort
