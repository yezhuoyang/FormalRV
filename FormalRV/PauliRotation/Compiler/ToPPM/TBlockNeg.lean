/-
  FormalRV.PauliRotation.Compiler.ToPPM.TBlockNeg
  ──────────────────────────────────────
  **THE NEGATIVE π/8 TELEPORT-BLOCK IDENTITIES** (the `|T†⟩` chirality).

  Same measurement statements as the forward block, ancilla prepared as
  `|T†⟩` (amplitudes `(1, e^{−iπ/4})`); the data ends in `e^{+iπ/8 P}ψ` =
  `rotOf(−π/8)` on every branch.  THE NUMERICS-CAUGHT DIFFERENCE: the
  Pauli correction fires on the XOR parity `c_a ^^ c_b` (not on `c_b`
  alone) — hence `lowerRot`'s `correct (if r.neg then [c, c+1] else
  [c+1])`.

      (0,0): ½·e^{−iπ/8} • (e^{+iπ/8P}ψ)   ⊗ (1, 1)
      (0,1): ½·e^{−iπ/8} • (P·e^{+iπ/8P}ψ) ⊗ (1, −1)
      (1,0): −½·e^{+iπ/8} • (P·e^{+iπ/8P}ψ) ⊗ (1, i)
      (1,1): ½·e^{+iπ/8} • (e^{+iπ/8P}ψ)   ⊗ (1, −i)
-/
import FormalRV.PauliRotation.Compiler.ToPPM.Embed

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-- **Neg-block branch (a=0, b=0)**: no correction (parity 0). -/
theorem tBlockNeg_branch_00 (n : Nat) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (hk : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ψ : Fin (2 ^ n) → ℂ) :
    (projHalf (axisMat (n + 1) [(⟨n, .x⟩ : PFactor)]) false).mulVec
      ((projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) false).mulVec
        (tensorHigh n 1 (phaseC (-(Real.pi / 4))) ψ))
      = ((2⁻¹ : ℂ) * phaseC (-(Real.pi / 8)))
          • tensorHigh n 1 1
              ((rotOf (-(Real.pi / 8)) (axisMat n P)).mulVec ψ) := by
  have h1 : (projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) false).mulVec
      (tensorHigh n 1 (phaseC (-(Real.pi / 4))) ψ)
      = (2⁻¹ : ℂ) • (tensorHigh n 1 (phaseC (-(Real.pi / 4))) ψ
          + tensorHigh n 1 (-(phaseC (-(Real.pi / 4))))
              ((axisMat n P).mulVec ψ)) := by
    rw [projHalf_mulVec, mulVec_joint_tensorHigh n P hs hw hk]
    simp
  rw [h1, projHalf_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add,
      mulVec_xn_tensorHigh, mulVec_xn_tensorHigh, rotOf,
      Matrix.sub_mulVec, smul_mulVec, smul_mulVec, Matrix.one_mulVec]
  funext m
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Bool.false_eq_true,
    if_false, one_smul, Pi.sub_apply, tensorHigh]
  rw [phaseC_eq, phaseC_eq, Real.cos_neg, Real.sin_neg, Real.cos_neg,
      Real.sin_neg, show Real.pi / 4 = 2 * (Real.pi / 8) from by ring,
      Real.cos_two_mul, Real.sin_two_mul]
  have hpy : Complex.sin ((Real.pi : ℂ) * (1 / 8)) ^ 2
      = 1 - Complex.cos ((Real.pi : ℂ) * (1 / 8)) ^ 2 := by
    linear_combination Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * (1 / 8))
  have hI3 : (Complex.I : ℂ) ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  by_cases h : (m : Nat).testBit n <;>
    simp only [h, if_true] <;>
    push_cast <;>
    ring_nf <;>
    simp only [Complex.I_sq, hpy] <;>
    ring

/-- **Neg-block branch (a=0, b=1)**: correction `P` (parity 1). -/
theorem tBlockNeg_branch_01 (n : Nat) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (hk : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ψ : Fin (2 ^ n) → ℂ) :
    (projHalf (axisMat (n + 1) [(⟨n, .x⟩ : PFactor)]) true).mulVec
      ((projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) false).mulVec
        (tensorHigh n 1 (phaseC (-(Real.pi / 4))) ψ))
      = ((2⁻¹ : ℂ) * phaseC (-(Real.pi / 8)))
          • tensorHigh n 1 (-1)
              ((axisMat n P).mulVec
                ((rotOf (-(Real.pi / 8)) (axisMat n P)).mulVec ψ)) := by
  have h1 : (projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) false).mulVec
      (tensorHigh n 1 (phaseC (-(Real.pi / 4))) ψ)
      = (2⁻¹ : ℂ) • (tensorHigh n 1 (phaseC (-(Real.pi / 4))) ψ
          + tensorHigh n 1 (-(phaseC (-(Real.pi / 4))))
              ((axisMat n P).mulVec ψ)) := by
    rw [projHalf_mulVec, mulVec_joint_tensorHigh n P hs hw hk]
    simp
  rw [h1, projHalf_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add,
      mulVec_xn_tensorHigh, mulVec_xn_tensorHigh, rotOf,
      Matrix.sub_mulVec, smul_mulVec, smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, axisMat_mul_self, Matrix.one_mulVec]
  funext m
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Pi.sub_apply, tensorHigh]
  rw [phaseC_eq, phaseC_eq, Real.cos_neg, Real.sin_neg, Real.cos_neg,
      Real.sin_neg, show Real.pi / 4 = 2 * (Real.pi / 8) from by ring,
      Real.cos_two_mul, Real.sin_two_mul]
  have hpy : Complex.sin ((Real.pi : ℂ) * (1 / 8)) ^ 2
      = 1 - Complex.cos ((Real.pi : ℂ) * (1 / 8)) ^ 2 := by
    linear_combination Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * (1 / 8))
  have hI3 : (Complex.I : ℂ) ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  by_cases h : (m : Nat).testBit n <;>
    simp only [h, if_true] <;>
    push_cast <;>
    ring_nf <;>
    simp only [Complex.I_sq, hpy] <;>
    ring

/-- **Neg-block branch (a=1, c=0)**: correction `P` (parity 1). -/
theorem tBlockNeg_branch_10 (n : Nat) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (hk : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ψ : Fin (2 ^ n) → ℂ) :
    (projHalf (axisMat (n + 1) [(⟨n, .y⟩ : PFactor)]) false).mulVec
      ((projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) true).mulVec
        (tensorHigh n 1 (phaseC (-(Real.pi / 4))) ψ))
      = (-(2⁻¹ : ℂ) * phaseC (Real.pi / 8))
          • tensorHigh n 1 Complex.I
              ((axisMat n P).mulVec
                ((rotOf (-(Real.pi / 8)) (axisMat n P)).mulVec ψ)) := by
  have h1 : (projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) true).mulVec
      (tensorHigh n 1 (phaseC (-(Real.pi / 4))) ψ)
      = (2⁻¹ : ℂ) • (tensorHigh n 1 (phaseC (-(Real.pi / 4))) ψ
          - tensorHigh n 1 (-(phaseC (-(Real.pi / 4))))
              ((axisMat n P).mulVec ψ)) := by
    rw [projHalf_mulVec, mulVec_joint_tensorHigh n P hs hw hk]
    simp [sub_eq_add_neg]
  rw [h1, projHalf_mulVec, Matrix.mulVec_smul, Matrix.mulVec_sub,
      mulVec_yn_tensorHigh, mulVec_yn_tensorHigh, rotOf,
      Matrix.sub_mulVec, smul_mulVec, smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, axisMat_mul_self, Matrix.one_mulVec]
  funext m
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Bool.false_eq_true,
    if_false, one_smul, Pi.sub_apply, tensorHigh]
  rw [phaseC_eq, phaseC_eq, Real.cos_neg, Real.sin_neg, Real.cos_neg,
      Real.sin_neg, show Real.pi / 4 = 2 * (Real.pi / 8) from by ring,
      Real.cos_two_mul, Real.sin_two_mul]
  have hpy : Complex.sin ((Real.pi : ℂ) * (1 / 8)) ^ 2
      = 1 - Complex.cos ((Real.pi : ℂ) * (1 / 8)) ^ 2 := by
    linear_combination Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * (1 / 8))
  have hI3 : (Complex.I : ℂ) ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  have h45 : Complex.cos ((Real.pi : ℂ) * (1 / 8))
        * Complex.sin ((Real.pi : ℂ) * (1 / 8))
      = Complex.cos ((Real.pi : ℂ) * (1 / 8)) ^ 2 - 1 / 2 := by
    have h1' := Real.sin_two_mul (Real.pi / 8)
    have h2 := Real.cos_two_mul (Real.pi / 8)
    have h3 : (2 : Real) * (Real.pi / 8) = Real.pi / 4 := by ring
    rw [h3] at h1' h2
    have h4 : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hr2 : 2 * (Real.cos (Real.pi / 8) * Real.sin (Real.pi / 8))
        = 2 * Real.cos (Real.pi / 8) ^ 2 - 1 := by nlinarith [h1', h2, h4]
    have harg : ((Real.pi : ℂ) * (1 / 8)) = ((Real.pi / 8 : Real) : ℂ) := by
      push_cast
      ring
    have hC2 : 2 * (Complex.cos ((Real.pi : ℂ) * (1 / 8))
          * Complex.sin ((Real.pi : ℂ) * (1 / 8)))
        = 2 * Complex.cos ((Real.pi : ℂ) * (1 / 8)) ^ 2 - 1 := by
      rw [harg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      exact_mod_cast hr2
    linear_combination hC2 / 2
  by_cases h : (m : Nat).testBit n
  · simp only [h, if_true]
    push_cast
    ring_nf
    simp only [Complex.I_sq, hI3, hpy, h45]
    ring
  · simp only [h]
    push_cast
    ring_nf
    simp only [Complex.I_sq, hpy]
    first
      | linear_combination ((Complex.I + 1)
          * (ψ (lowBits n m) + ((axisMat n P).mulVec ψ) (lowBits n m)) / 2) * h45
      | linear_combination (-(Complex.I + 1)
          * (ψ (lowBits n m) + ((axisMat n P).mulVec ψ) (lowBits n m)) / 2) * h45
      | linear_combination ((Complex.I - 1)
          * (ψ (lowBits n m) + ((axisMat n P).mulVec ψ) (lowBits n m)) / 2) * h45

/-- **Neg-block branch (a=1, c=1)**: no correction (parity 0). -/
theorem tBlockNeg_branch_11 (n : Nat) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (hk : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ψ : Fin (2 ^ n) → ℂ) :
    (projHalf (axisMat (n + 1) [(⟨n, .y⟩ : PFactor)]) true).mulVec
      ((projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) true).mulVec
        (tensorHigh n 1 (phaseC (-(Real.pi / 4))) ψ))
      = ((2⁻¹ : ℂ) * phaseC (Real.pi / 8))
          • tensorHigh n 1 (-Complex.I)
              ((rotOf (-(Real.pi / 8)) (axisMat n P)).mulVec ψ) := by
  have h1 : (projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) true).mulVec
      (tensorHigh n 1 (phaseC (-(Real.pi / 4))) ψ)
      = (2⁻¹ : ℂ) • (tensorHigh n 1 (phaseC (-(Real.pi / 4))) ψ
          - tensorHigh n 1 (-(phaseC (-(Real.pi / 4))))
              ((axisMat n P).mulVec ψ)) := by
    rw [projHalf_mulVec, mulVec_joint_tensorHigh n P hs hw hk]
    simp [sub_eq_add_neg]
  rw [h1, projHalf_mulVec, Matrix.mulVec_smul, Matrix.mulVec_sub,
      mulVec_yn_tensorHigh, mulVec_yn_tensorHigh, rotOf,
      Matrix.sub_mulVec, smul_mulVec, smul_mulVec, Matrix.one_mulVec]
  funext m
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Pi.sub_apply, tensorHigh]
  rw [phaseC_eq, phaseC_eq, Real.cos_neg, Real.sin_neg, Real.cos_neg,
      Real.sin_neg, show Real.pi / 4 = 2 * (Real.pi / 8) from by ring,
      Real.cos_two_mul, Real.sin_two_mul]
  have hpy : Complex.sin ((Real.pi : ℂ) * (1 / 8)) ^ 2
      = 1 - Complex.cos ((Real.pi : ℂ) * (1 / 8)) ^ 2 := by
    linear_combination Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * (1 / 8))
  have hI3 : (Complex.I : ℂ) ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  have h45 : Complex.cos ((Real.pi : ℂ) * (1 / 8))
        * Complex.sin ((Real.pi : ℂ) * (1 / 8))
      = Complex.cos ((Real.pi : ℂ) * (1 / 8)) ^ 2 - 1 / 2 := by
    have h1' := Real.sin_two_mul (Real.pi / 8)
    have h2 := Real.cos_two_mul (Real.pi / 8)
    have h3 : (2 : Real) * (Real.pi / 8) = Real.pi / 4 := by ring
    rw [h3] at h1' h2
    have h4 : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hr2 : 2 * (Real.cos (Real.pi / 8) * Real.sin (Real.pi / 8))
        = 2 * Real.cos (Real.pi / 8) ^ 2 - 1 := by nlinarith [h1', h2, h4]
    have harg : ((Real.pi : ℂ) * (1 / 8)) = ((Real.pi / 8 : Real) : ℂ) := by
      push_cast
      ring
    have hC2 : 2 * (Complex.cos ((Real.pi : ℂ) * (1 / 8))
          * Complex.sin ((Real.pi : ℂ) * (1 / 8)))
        = 2 * Complex.cos ((Real.pi : ℂ) * (1 / 8)) ^ 2 - 1 := by
      rw [harg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      exact_mod_cast hr2
    linear_combination hC2 / 2
  by_cases h : (m : Nat).testBit n
  · simp only [h, if_true]
    push_cast
    ring_nf
    simp only [Complex.I_sq, hI3, hpy, h45]
    ring
  · simp only [h]
    push_cast
    ring_nf
    simp only [Complex.I_sq, hpy]
    first
      | linear_combination ((Complex.I + 1)
          * (ψ (lowBits n m) + ((axisMat n P).mulVec ψ) (lowBits n m)) / 2) * h45
      | linear_combination (-(Complex.I + 1)
          * (ψ (lowBits n m) + ((axisMat n P).mulVec ψ) (lowBits n m)) / 2) * h45
      | linear_combination ((Complex.I - 1)
          * (ψ (lowBits n m) + ((axisMat n P).mulVec ψ) (lowBits n m)) / 2) * h45
      | linear_combination ((1 - Complex.I)
          * (ψ (lowBits n m) + ((axisMat n P).mulVec ψ) (lowBits n m)) / 2) * h45

end FormalRV.PauliRotation
