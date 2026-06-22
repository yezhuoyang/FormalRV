/-
  FormalRV.PauliRotation.Compiler.ToPPM.SBlock
  ───────────────────────────────────
  **THE π/4 (CLIFFORD/S-LEVEL) TELEPORT-BLOCK IDENTITIES.**

  The lowering's S-block on data axis `P` with the `|Y⟩` ancilla at wire `n`
  (`|Y⟩ = (|0⟩ + i|1⟩)/√2` — a STABILIZER state, magic-free):

      c_a = Measure  P·Z[n]
      c_b = Measure  X[n]
      if c_a ^^ c_b == 1 then frame P

  Unlike the π/8 block, NO selective destruction is needed: the bad-branch
  correction of a π/4 rotation is `(−i)P` — Pauli with phase — so both
  measurements are FIXED and the correction fires on the XOR parity
  `c_a ^^ c_b`, exactly expressible by the ORIGINAL `correct` statement.

  The four branch identities (numerically pinned, then proven):

      (0,0): ½·e^{iπ/4}  • (e^{−iπ/4 P}ψ)   ⊗ |+⟩
      (0,1): ½·e^{iπ/4}  • (P·e^{−iπ/4 P}ψ) ⊗ |−⟩
      (1,0): −½·e^{−iπ/4} • (P·e^{−iπ/4 P}ψ) ⊗ |+⟩
      (1,1): ½·e^{−iπ/4} • (e^{−iπ/4 P}ψ)   ⊗ |−⟩
-/
import FormalRV.PauliRotation.Compiler.ToPPM.TBlock

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-- **S-block branch (a=0, b=0)**: no correction. -/
theorem sBlock_branch_00 (n : Nat) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (hk : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ψ : Fin (2 ^ n) → ℂ) :
    (projHalf (axisMat (n + 1) [(⟨n, .x⟩ : PFactor)]) false).mulVec
      ((projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) false).mulVec
        (tensorHigh n 1 Complex.I ψ))
      = ((2⁻¹ : ℂ) * phaseC (Real.pi / 4))
          • tensorHigh n 1 1 ((rotOf (Real.pi / 4) (axisMat n P)).mulVec ψ) := by
  have h1 : (projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) false).mulVec
      (tensorHigh n 1 Complex.I ψ)
      = (2⁻¹ : ℂ) • (tensorHigh n 1 Complex.I ψ
          + tensorHigh n 1 (-Complex.I) ((axisMat n P).mulVec ψ)) := by
    rw [projHalf_mulVec, mulVec_joint_tensorHigh n P hs hw hk]
    simp
  rw [h1, projHalf_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add,
      mulVec_xn_tensorHigh, mulVec_xn_tensorHigh, rotOf,
      Matrix.sub_mulVec, smul_mulVec, smul_mulVec, Matrix.one_mulVec]
  funext m
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Bool.false_eq_true,
    if_false, one_smul, Pi.sub_apply, tensorHigh]
  rw [phaseC_eq]
  have hd : Complex.sin ((Real.pi : ℂ) * (1 / 4))
      = Complex.cos ((Real.pi : ℂ) * (1 / 4)) := by
    have hr : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have harg : ((Real.pi : ℂ) * (1 / 4)) = ((Real.pi / 4 : Real) : ℂ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
    exact_mod_cast hr
  have hc2 : Complex.cos ((Real.pi : ℂ) * (1 / 4)) ^ 2 = 1 / 2 := by
    have hr2 : 2 * Real.cos (Real.pi / 4) ^ 2 = 1 := by
      rw [Real.cos_pi_div_four]
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
      norm_num
    have harg : ((Real.pi : ℂ) * (1 / 4)) = ((Real.pi / 4 : Real) : ℂ) := by
      push_cast
      ring
    have hC : 2 * Complex.cos ((Real.pi : ℂ) * (1 / 4)) ^ 2 = 1 := by
      rw [harg, ← Complex.ofReal_cos]
      exact_mod_cast hr2
    linear_combination hC / 2
  by_cases h : (m : Nat).testBit n <;>
    simp only [h, if_true] <;>
    push_cast <;>
    ring_nf <;>
    simp only [Complex.I_sq, hd] <;>
    linear_combination (-((ψ (lowBits n m) + ((axisMat n P).mulVec ψ) (lowBits n m))
      + Complex.I * (ψ (lowBits n m)
          - ((axisMat n P).mulVec ψ) (lowBits n m))) / 2) * hc2

/-- **S-block branch (a=0, b=1)**: correction `P` (parity 1). -/
theorem sBlock_branch_01 (n : Nat) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (hk : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ψ : Fin (2 ^ n) → ℂ) :
    (projHalf (axisMat (n + 1) [(⟨n, .x⟩ : PFactor)]) true).mulVec
      ((projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) false).mulVec
        (tensorHigh n 1 Complex.I ψ))
      = ((2⁻¹ : ℂ) * phaseC (Real.pi / 4))
          • tensorHigh n 1 (-1)
              ((axisMat n P).mulVec
                ((rotOf (Real.pi / 4) (axisMat n P)).mulVec ψ)) := by
  have h1 : (projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) false).mulVec
      (tensorHigh n 1 Complex.I ψ)
      = (2⁻¹ : ℂ) • (tensorHigh n 1 Complex.I ψ
          + tensorHigh n 1 (-Complex.I) ((axisMat n P).mulVec ψ)) := by
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
  rw [phaseC_eq]
  have hd : Complex.sin ((Real.pi : ℂ) * (1 / 4))
      = Complex.cos ((Real.pi : ℂ) * (1 / 4)) := by
    have hr : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have harg : ((Real.pi : ℂ) * (1 / 4)) = ((Real.pi / 4 : Real) : ℂ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
    exact_mod_cast hr
  have hc2 : Complex.cos ((Real.pi : ℂ) * (1 / 4)) ^ 2 = 1 / 2 := by
    have hr2 : 2 * Real.cos (Real.pi / 4) ^ 2 = 1 := by
      rw [Real.cos_pi_div_four]
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
      norm_num
    have harg : ((Real.pi : ℂ) * (1 / 4)) = ((Real.pi / 4 : Real) : ℂ) := by
      push_cast
      ring
    have hC : 2 * Complex.cos ((Real.pi : ℂ) * (1 / 4)) ^ 2 = 1 := by
      rw [harg, ← Complex.ofReal_cos]
      exact_mod_cast hr2
    linear_combination hC / 2
  by_cases h : (m : Nat).testBit n <;>
    simp only [h, if_true] <;>
    push_cast <;>
    ring_nf <;>
    simp only [Complex.I_sq, hd] <;>
    first
      | linear_combination (((ψ (lowBits n m) + ((axisMat n P).mulVec ψ) (lowBits n m))
          + Complex.I * (((axisMat n P).mulVec ψ) (lowBits n m)
              - ψ (lowBits n m))) / 2) * hc2
      | linear_combination (-(((ψ (lowBits n m) + ((axisMat n P).mulVec ψ) (lowBits n m))
          + Complex.I * (((axisMat n P).mulVec ψ) (lowBits n m)
              - ψ (lowBits n m))) / 2)) * hc2

/-- **S-block branch (a=1, b=0)**: correction `P` (parity 1). -/
theorem sBlock_branch_10 (n : Nat) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (hk : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ψ : Fin (2 ^ n) → ℂ) :
    (projHalf (axisMat (n + 1) [(⟨n, .x⟩ : PFactor)]) false).mulVec
      ((projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) true).mulVec
        (tensorHigh n 1 Complex.I ψ))
      = (-(2⁻¹ : ℂ) * phaseC (-(Real.pi / 4)))
          • tensorHigh n 1 1
              ((axisMat n P).mulVec
                ((rotOf (Real.pi / 4) (axisMat n P)).mulVec ψ)) := by
  have h1 : (projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) true).mulVec
      (tensorHigh n 1 Complex.I ψ)
      = (2⁻¹ : ℂ) • (tensorHigh n 1 Complex.I ψ
          - tensorHigh n 1 (-Complex.I) ((axisMat n P).mulVec ψ)) := by
    rw [projHalf_mulVec, mulVec_joint_tensorHigh n P hs hw hk]
    simp [sub_eq_add_neg]
  rw [h1, projHalf_mulVec, Matrix.mulVec_smul, Matrix.mulVec_sub,
      mulVec_xn_tensorHigh, mulVec_xn_tensorHigh, rotOf,
      Matrix.sub_mulVec, smul_mulVec, smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, axisMat_mul_self, Matrix.one_mulVec]
  funext m
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Bool.false_eq_true,
    if_false, one_smul, Pi.sub_apply, tensorHigh]
  rw [phaseC_eq, Real.cos_neg, Real.sin_neg]
  have hd : Complex.sin ((Real.pi : ℂ) * (1 / 4))
      = Complex.cos ((Real.pi : ℂ) * (1 / 4)) := by
    have hr : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have harg : ((Real.pi : ℂ) * (1 / 4)) = ((Real.pi / 4 : Real) : ℂ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
    exact_mod_cast hr
  have hc2 : Complex.cos ((Real.pi : ℂ) * (1 / 4)) ^ 2 = 1 / 2 := by
    have hr2 : 2 * Real.cos (Real.pi / 4) ^ 2 = 1 := by
      rw [Real.cos_pi_div_four]
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
      norm_num
    have harg : ((Real.pi : ℂ) * (1 / 4)) = ((Real.pi / 4 : Real) : ℂ) := by
      push_cast
      ring
    have hC : 2 * Complex.cos ((Real.pi : ℂ) * (1 / 4)) ^ 2 = 1 := by
      rw [harg, ← Complex.ofReal_cos]
      exact_mod_cast hr2
    linear_combination hC / 2
  by_cases h : (m : Nat).testBit n <;>
    simp only [h, if_true] <;>
    push_cast <;>
    ring_nf <;>
    simp only [Complex.I_sq, hd] <;>
    linear_combination (((((axisMat n P).mulVec ψ) (lowBits n m) - ψ (lowBits n m))
      - Complex.I * (ψ (lowBits n m)
          + ((axisMat n P).mulVec ψ) (lowBits n m))) / 2) * hc2

/-- **S-block branch (a=1, b=1)**: no correction (parity 0). -/
theorem sBlock_branch_11 (n : Nat) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (hk : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ψ : Fin (2 ^ n) → ℂ) :
    (projHalf (axisMat (n + 1) [(⟨n, .x⟩ : PFactor)]) true).mulVec
      ((projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) true).mulVec
        (tensorHigh n 1 Complex.I ψ))
      = ((2⁻¹ : ℂ) * phaseC (-(Real.pi / 4)))
          • tensorHigh n 1 (-1)
              ((rotOf (Real.pi / 4) (axisMat n P)).mulVec ψ) := by
  have h1 : (projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) true).mulVec
      (tensorHigh n 1 Complex.I ψ)
      = (2⁻¹ : ℂ) • (tensorHigh n 1 Complex.I ψ
          - tensorHigh n 1 (-Complex.I) ((axisMat n P).mulVec ψ)) := by
    rw [projHalf_mulVec, mulVec_joint_tensorHigh n P hs hw hk]
    simp [sub_eq_add_neg]
  rw [h1, projHalf_mulVec, Matrix.mulVec_smul, Matrix.mulVec_sub,
      mulVec_xn_tensorHigh, mulVec_xn_tensorHigh, rotOf,
      Matrix.sub_mulVec, smul_mulVec, smul_mulVec, Matrix.one_mulVec]
  funext m
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Pi.sub_apply, tensorHigh]
  rw [phaseC_eq, Real.cos_neg, Real.sin_neg]
  have hd : Complex.sin ((Real.pi : ℂ) * (1 / 4))
      = Complex.cos ((Real.pi : ℂ) * (1 / 4)) := by
    have hr : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have harg : ((Real.pi : ℂ) * (1 / 4)) = ((Real.pi / 4 : Real) : ℂ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
    exact_mod_cast hr
  have hc2 : Complex.cos ((Real.pi : ℂ) * (1 / 4)) ^ 2 = 1 / 2 := by
    have hr2 : 2 * Real.cos (Real.pi / 4) ^ 2 = 1 := by
      rw [Real.cos_pi_div_four]
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
      norm_num
    have harg : ((Real.pi : ℂ) * (1 / 4)) = ((Real.pi / 4 : Real) : ℂ) := by
      push_cast
      ring
    have hC : 2 * Complex.cos ((Real.pi : ℂ) * (1 / 4)) ^ 2 = 1 := by
      rw [harg, ← Complex.ofReal_cos]
      exact_mod_cast hr2
    linear_combination hC / 2
  by_cases h : (m : Nat).testBit n <;>
    simp only [h, if_true] <;>
    push_cast <;>
    ring_nf <;>
    simp only [Complex.I_sq, hd] <;>
    first
      | linear_combination (((ψ (lowBits n m) - ((axisMat n P).mulVec ψ) (lowBits n m))
          - Complex.I * (ψ (lowBits n m)
              + ((axisMat n P).mulVec ψ) (lowBits n m))) / 2) * hc2
      | linear_combination (-(((ψ (lowBits n m) - ((axisMat n P).mulVec ψ) (lowBits n m))
          - Complex.I * (ψ (lowBits n m)
              + ((axisMat n P).mulVec ψ) (lowBits n m))) / 2)) * hc2

end FormalRV.PauliRotation
