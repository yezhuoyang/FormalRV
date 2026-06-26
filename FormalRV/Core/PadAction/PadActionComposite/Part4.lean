/- PadActionComposite — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Core.PadAction.PadActionComposite.Part3

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker

/-! ## Algebraic infrastructure for the 7-T phase cancellation

    Identities involving `Complex.exp (i·π/4)` that the CCX_PHASE_CANCEL
    step will need. Each is independent of the circuit machinery. -/

/-- exp(iπ/4) · exp(-iπ/4) = 1. -/
theorem exp_pi4_mul_exp_neg_pi4 :
    Complex.exp (Complex.I * (Real.pi / 4))
      * Complex.exp (-(Complex.I * (Real.pi / 4))) = 1 := by
  rw [← Complex.exp_add]
  rw [show Complex.I * (Real.pi / 4) + -(Complex.I * (Real.pi / 4)) = 0 from by ring]
  exact Complex.exp_zero

/-- exp(-iπ/4) · exp(iπ/4) = 1. -/
theorem exp_neg_pi4_mul_exp_pi4 :
    Complex.exp (-(Complex.I * (Real.pi / 4)))
      * Complex.exp (Complex.I * (Real.pi / 4)) = 1 := by
  rw [mul_comm]; exact exp_pi4_mul_exp_neg_pi4

/-- exp(iπ/4)^2 · exp(-iπ/4)^2 = 1. -/
theorem exp_pi4_sq_mul_exp_neg_pi4_sq :
    (Complex.exp (Complex.I * (Real.pi / 4)))^2
      * (Complex.exp (-(Complex.I * (Real.pi / 4))))^2 = 1 := by
  rw [show (Complex.exp (Complex.I * (Real.pi / 4)))^2
        * (Complex.exp (-(Complex.I * (Real.pi / 4))))^2
        = (Complex.exp (Complex.I * (Real.pi / 4))
           * Complex.exp (-(Complex.I * (Real.pi / 4))))^2 from by ring]
  rw [exp_pi4_mul_exp_neg_pi4]
  ring

/-- exp(iπ/4)^4 = exp(iπ) = -1. -/
theorem exp_pi4_pow_four :
    (Complex.exp (Complex.I * (Real.pi / 4)))^4 = -1 := by
  rw [show (Complex.exp (Complex.I * (Real.pi / 4)))^4
        = Complex.exp (Complex.I * (Real.pi / 4) * 4) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show Complex.I * (Real.pi / 4) * 4 = (Real.pi : ℂ) * Complex.I from by ring]
  exact Complex.exp_pi_mul_I

/-- exp(-iπ/4)^4 = exp(-iπ) = -1. Dagger version of `exp_pi4_pow_four`. -/
theorem exp_neg_pi4_pow_four :
    (Complex.exp (-(Complex.I * (Real.pi / 4))))^4 = -1 := by
  rw [show (Complex.exp (-(Complex.I * (Real.pi / 4))))^4
        = Complex.exp (-(Complex.I * (Real.pi / 4)) * 4) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show -(Complex.I * (Real.pi / 4)) * 4 = -((Real.pi : ℂ) * Complex.I) from by ring]
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]
  ring

/-- exp(iπ/4)^2 = exp(iπ/2) = i. The basic π/4 → π/2 squaring identity.
    Useful for further reducing 2-factor exp products inside the CCX
    phase-cancellation cases. -/
theorem exp_pi4_pow_two_eq_I :
    (Complex.exp (Complex.I * (Real.pi / 4)))^2 = Complex.I := by
  rw [show (Complex.exp (Complex.I * (Real.pi / 4)))^2
        = Complex.exp (Complex.I * (Real.pi / 4) * 2) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show Complex.I * (Real.pi / 4) * 2 = (Real.pi / 2 : ℂ) * Complex.I from by ring]
  exact Complex.exp_pi_div_two_mul_I

/-- exp(-iπ/4)^2 = exp(-iπ/2) = -i. Dagger version. -/
theorem exp_neg_pi4_pow_two_eq_neg_I :
    (Complex.exp (-(Complex.I * (Real.pi / 4))))^2 = -Complex.I := by
  rw [show (Complex.exp (-(Complex.I * (Real.pi / 4))))^2
        = Complex.exp (-(Complex.I * (Real.pi / 4)) * 2) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show -(Complex.I * (Real.pi / 4)) * 2 = -((Real.pi / 2 : ℂ) * Complex.I) from by ring]
  rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I]
  simp [Complex.inv_I]

/-- 4-factor alternating pattern: `e * e⁻¹ * e * e⁻¹ = 1` where
    `e = exp(iπ/4)`. This product appears in CCX_PHASE_CANCEL α₁
    expressions for cases where (f a, f b) = (F, F). 1-line proof
    via repeated `exp_pi4_mul_exp_neg_pi4` after associativity. -/
theorem exp_pi4_alt_four :
    Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (-(Complex.I * (Real.pi / 4)))
    * Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (-(Complex.I * (Real.pi / 4))) = 1 := by
  rw [show Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
     = (Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4))))
       * (Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))) from by ring]
  rw [exp_pi4_mul_exp_neg_pi4]
  ring

/-- 4-factor consecutive-grouping pattern: `e * e * e⁻¹ * e⁻¹ = 1` where
    `e = exp(iπ/4)`. Appears in CCX_PHASE_CANCEL α₁ for (F,T,*) and
    (T,F,*) cases (2 positive π/4 factors then 2 negative). -/
theorem exp_pi4_consec_four :
    Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (-(Complex.I * (Real.pi / 4)))
    * Complex.exp (-(Complex.I * (Real.pi / 4))) = 1 := by
  rw [show Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
     = (Complex.exp (Complex.I * (Real.pi / 4)))^2
       * (Complex.exp (-(Complex.I * (Real.pi / 4))))^2 from by ring]
  exact exp_pi4_sq_mul_exp_neg_pi4_sq

/-- 4-factor palindrome pattern: `e * e⁻¹ * e⁻¹ * e = 1` where
    `e = exp(iπ/4)`. Appears in CCX_PHASE_CANCEL α₀ for (T,F,*) cases. -/
theorem exp_pi4_palindrome_four :
    Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (-(Complex.I * (Real.pi / 4)))
    * Complex.exp (-(Complex.I * (Real.pi / 4)))
    * Complex.exp (Complex.I * (Real.pi / 4)) = 1 := by
  rw [show Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (Complex.I * (Real.pi / 4))
     = (Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4))))
       * (Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (Complex.I * (Real.pi / 4))) from by ring]
  rw [exp_pi4_mul_exp_neg_pi4, exp_neg_pi4_mul_exp_pi4]
  ring

/-- 4-factor uniform-product pattern: `e * e * e * e = -1` where
    `e = exp(iπ/4)`. Appears in CCX_PHASE_CANCEL α₁ for (T,T,*) cases.
    Equivalent to `exp_pi4_pow_four` but in mul-of-mul form. -/
theorem exp_pi4_mul_four_eq_neg_one :
    Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (Complex.I * (Real.pi / 4)) = -1 := by
  rw [show Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (Complex.I * (Real.pi / 4))
     = (Complex.exp (Complex.I * (Real.pi / 4)))^4 from by ring]
  exact exp_pi4_pow_four

/-- (√2/2)² = 1/2 in ℂ. -/
theorem sqrt2_div2_sq : ((Real.sqrt 2 : ℂ) / 2) * ((Real.sqrt 2 : ℂ) / 2) = 1/2 := by
  have h : ((Real.sqrt 2 : ℂ))^2 = 2 := by
    have hreal : ((Real.sqrt 2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    exact_mod_cast hreal
  field_simp
  linear_combination h

/-- Hadamard sandwich: `H X H = Z`. -/
theorem hMatrix_σx_hMatrix : hMatrix * σx * hMatrix = σz := by
  unfold hMatrix σx σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try linear_combination 2 * sqrt2_div2_sq) <;>
    (try linear_combination -2 * sqrt2_div2_sq)

/-- Hadamard sandwich: `H Z H = X`. Dual of `hMatrix_σx_hMatrix`. -/
theorem hMatrix_σz_hMatrix : hMatrix * σz * hMatrix = σx := by
  unfold hMatrix σz σx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try linear_combination 2 * sqrt2_div2_sq) <;>
    (try linear_combination -2 * sqrt2_div2_sq)

/-- Hadamard sandwich: `H Y H = -Y`. The Y axis flips under Hadamard
    conjugation (Y is anti-symmetric under the X↔Z basis swap). -/
theorem hMatrix_σy_hMatrix : hMatrix * σy * hMatrix = -σy := by
  unfold hMatrix σy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply] <;>
    (try linear_combination 2 * Complex.I * sqrt2_div2_sq) <;>
    (try linear_combination -(2 * Complex.I) * sqrt2_div2_sq)

/-- S sandwich: `S X S† = Y`. The S gate maps X to Y under conjugation
    (a 90° rotation in the X-Y plane). -/
theorem sMatrix_σx_sdagMatrix : sMatrix * σx * sdagMatrix = σy := by
  unfold sMatrix σx sdagMatrix σy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- S sandwich: `S Y S† = -X`. -/
theorem sMatrix_σy_sdagMatrix : sMatrix * σy * sdagMatrix = -σx := by
  unfold sMatrix σy sdagMatrix σx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- S sandwich: `S Z S† = Z`. The Z axis is fixed by S (since both are
    Z-axis rotations and commute). -/
theorem sMatrix_σz_sdagMatrix : sMatrix * σz * sdagMatrix = σz := by
  unfold sMatrix σz sdagMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Dual S†-sandwich: `S† X S = -Y`. Inverse rotation of `S X S† = Y`. -/
theorem sdagMatrix_σx_sMatrix : sdagMatrix * σx * sMatrix = -σy := by
  unfold sdagMatrix σx sMatrix σy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Dual S†-sandwich: `S† Y S = X`. -/
theorem sdagMatrix_σy_sMatrix : sdagMatrix * σy * sMatrix = σx := by
  unfold sdagMatrix σy sMatrix σx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Dual S†-sandwich: `S† Z S = Z`. -/
theorem sdagMatrix_σz_sMatrix : sdagMatrix * σz * sMatrix = σz := by
  unfold sdagMatrix σz sMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- T-sandwich: `T Z T† = Z`. T is a Z-axis rotation (by π/4) so it
    commutes with σz; the sandwich therefore acts trivially. -/
theorem tMatrix_σz_tdagMatrix : tMatrix * σz * tdagMatrix = σz := by
  unfold tMatrix σz tdagMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
          ← Complex.exp_add, Complex.exp_zero]

/-- T†-sandwich: `T† Z T = Z`. Dual of `tMatrix_σz_tdagMatrix`. -/
theorem tdagMatrix_σz_tMatrix : tdagMatrix * σz * tMatrix = σz := by
  unfold tdagMatrix σz tMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
          ← Complex.exp_add, Complex.exp_zero]

/-- Circuit equivalence: `H q ; X q ; H q ≡ Z q`. This is the
    canonical Hadamard sandwich identity at the circuit level — lifts
    the matrix identity `hMatrix * σx * hMatrix = σz` (theorem
    `hMatrix_σx_hMatrix`) through `pad_u_mul_pad_u`. -/
theorem H_X_H_eq_Z {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.X n))
                       (BaseUCom.H n))
      = uc_eval (BaseUCom.Z n : BaseUCom dim) := by
  show pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
        * (pad_u dim n (rotation Real.pi 0 Real.pi)
            * pad_u dim n (rotation (Real.pi/2) 0 Real.pi))
      = pad_u dim n (rotation 0 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_H, rotation_X, rotation_Z, hMatrix_σx_hMatrix]

/-- Circuit equivalence: `H q ; Z q ; H q ≡ X q`. Dual sandwich. -/
theorem H_Z_H_eq_X {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.Z n))
                       (BaseUCom.H n))
      = uc_eval (BaseUCom.X n : BaseUCom dim) := by
  show pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
        * (pad_u dim n (rotation 0 0 Real.pi)
            * pad_u dim n (rotation (Real.pi/2) 0 Real.pi))
      = pad_u dim n (rotation Real.pi 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_H, rotation_Z, rotation_X, hMatrix_σz_hMatrix]


end FormalRV.Framework
