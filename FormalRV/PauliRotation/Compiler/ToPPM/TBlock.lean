/-
  FormalRV.PauliRotation.Compiler.ToPPM.TBlock
  ───────────────────────────────────
  **B1 — THE π/8 TELEPORT-BLOCK IDENTITIES.**

  The lowering's T-block on data axis `P` with the `|T⟩` ancilla at wire `n`:

      c_a = Measure  P·Z[n]
      c_b = MeasureIf c_a then Y[n] else X[n]      (selective destruction)
      if c_b == 1 then frame P

  This file proves the four outcome branches in matrix-land: applying the
  branch projectors to `ψ ⊗ |T⟩` (amplitudes `(1, e^{iπ/4})`, the `1/√2`
  normalizations tracked in the explicit Born scalars) yields

      (scalar) • (correction ∘ e^{−iπ/8 P}) ψ ⊗ (collapsed ancilla)

  with the data correction `P` exactly when the SECOND outcome is `1` —
  i.e. the emitted `correct [c_b] P` statement is the right one, on every
  branch.  The proofs are coefficient-wise `ring` identities after the
  double-angle substitution `π/4 = 2·(π/8)`; no Pythagorean relation and
  no normalization conventions are needed.
-/
import FormalRV.PauliRotation.Compiler.ToPPM.BlockIdentities

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-! ## §1. Branch projectors and linearity helpers. -/

/-- The outcome-`b` branch projector of the ±1 observable `M`:
`½(1 + (−1)^b M)`. -/
noncomputable def projHalf {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℂ) (b : Bool) : Matrix d d ℂ :=
  (2⁻¹ : ℂ) • (1 + (if b then (-1 : ℂ) else 1) • M)

theorem projHalf_mulVec {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℂ) (b : Bool) (v : d → ℂ) :
    (projHalf M b).mulVec v
      = (2⁻¹ : ℂ) • (v + (if b then (-1 : ℂ) else 1) • M.mulVec v) := by
  unfold projHalf
  rw [smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, smul_mulVec]

theorem tensorHigh_amps_add (n : Nat) (α α' β β' : ℂ) (ψ : Fin (2 ^ n) → ℂ) :
    tensorHigh n (α + α') (β + β') ψ
      = tensorHigh n α β ψ + tensorHigh n α' β' ψ := by
  funext m
  show (if (m : Nat).testBit n then β + β' else α + α') * ψ (lowBits n m)
      = (if (m : Nat).testBit n then β else α) * ψ (lowBits n m)
        + (if (m : Nat).testBit n then β' else α') * ψ (lowBits n m)
  by_cases h : (m : Nat).testBit n <;> simp [h] <;> ring

theorem tensorHigh_amps_smul (n : Nat) (c α β : ℂ) (ψ : Fin (2 ^ n) → ℂ) :
    tensorHigh n (c * α) (c * β) ψ = c • tensorHigh n α β ψ :=
  tensorHigh_smul n c α β ψ

/-! ## §2. The T-block branches. -/

/-- **Branch (a=0, b=0)**: joint outcome `+1`, X-destruction outcome `+1` —
the data holds `e^{−iπ/8 P}ψ`, ancilla collapses to `|+⟩`, no correction. -/
theorem tBlock_branch_00 (n : Nat) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (hk : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ψ : Fin (2 ^ n) → ℂ) :
    (projHalf (axisMat (n + 1) [(⟨n, .x⟩ : PFactor)]) false).mulVec
      ((projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) false).mulVec
        (tensorHigh n 1 (phaseC (Real.pi / 4)) ψ))
      = ((2⁻¹ : ℂ) * phaseC (Real.pi / 8))
          • tensorHigh n 1 1 ((rotOf (Real.pi / 8) (axisMat n P)).mulVec ψ) := by
  have h1 : (projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) false).mulVec
      (tensorHigh n 1 (phaseC (Real.pi / 4)) ψ)
      = (2⁻¹ : ℂ) • (tensorHigh n 1 (phaseC (Real.pi / 4)) ψ
          + tensorHigh n 1 (-(phaseC (Real.pi / 4)))
              ((axisMat n P).mulVec ψ)) := by
    rw [projHalf_mulVec, mulVec_joint_tensorHigh n P hs hw hk]
    simp
  rw [h1, projHalf_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add,
      mulVec_xn_tensorHigh, mulVec_xn_tensorHigh, rotOf,
      Matrix.sub_mulVec, smul_mulVec, smul_mulVec, Matrix.one_mulVec]
  funext m
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Bool.false_eq_true,
    if_false, one_smul, Pi.sub_apply, tensorHigh]
  rw [phaseC_eq, phaseC_eq,
      show Real.pi / 4 = 2 * (Real.pi / 8) from by ring,
      Real.cos_two_mul, Real.sin_two_mul]
  have hpy : Complex.sin ((Real.pi : ℂ) * (1 / 8)) ^ 2
      = 1 - Complex.cos ((Real.pi : ℂ) * (1 / 8)) ^ 2 := by
    linear_combination Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * (1 / 8))
  by_cases h : (m : Nat).testBit n <;>
    simp only [h, if_true] <;>
    push_cast <;>
    ring_nf <;>
    simp only [Complex.I_sq, hpy] <;>
    ring

/-- **Branch (a=0, b=1)**: X-destruction outcome `−1` — the data holds
`P·e^{−iπ/8 P}ψ` (the emitted `correct [c_b] P` fixes it), ancilla `|−⟩`. -/
theorem tBlock_branch_01 (n : Nat) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (hk : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ψ : Fin (2 ^ n) → ℂ) :
    (projHalf (axisMat (n + 1) [(⟨n, .x⟩ : PFactor)]) true).mulVec
      ((projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) false).mulVec
        (tensorHigh n 1 (phaseC (Real.pi / 4)) ψ))
      = ((2⁻¹ : ℂ) * phaseC (Real.pi / 8))
          • tensorHigh n 1 (-1)
              ((axisMat n P).mulVec
                ((rotOf (Real.pi / 8) (axisMat n P)).mulVec ψ)) := by
  have h1 : (projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) false).mulVec
      (tensorHigh n 1 (phaseC (Real.pi / 4)) ψ)
      = (2⁻¹ : ℂ) • (tensorHigh n 1 (phaseC (Real.pi / 4)) ψ
          + tensorHigh n 1 (-(phaseC (Real.pi / 4)))
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
  rw [phaseC_eq, phaseC_eq,
      show Real.pi / 4 = 2 * (Real.pi / 8) from by ring,
      Real.cos_two_mul, Real.sin_two_mul]
  have hpy : Complex.sin ((Real.pi : ℂ) * (1 / 8)) ^ 2
      = 1 - Complex.cos ((Real.pi : ℂ) * (1 / 8)) ^ 2 := by
    linear_combination Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * (1 / 8))
  by_cases h : (m : Nat).testBit n <;>
    simp only [h, if_true] <;>
    push_cast <;>
    ring_nf <;>
    simp only [Complex.I_sq, hpy] <;>
    ring

/-- **Branch (a=1, c=0)**: joint outcome `−1`, Y-destruction outcome `+1` —
the data holds `e^{−iπ/8 P}ψ` directly, ancilla `|+y⟩`, no correction. -/
theorem tBlock_branch_10 (n : Nat) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (hk : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ψ : Fin (2 ^ n) → ℂ) :
    (projHalf (axisMat (n + 1) [(⟨n, .y⟩ : PFactor)]) false).mulVec
      ((projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) true).mulVec
        (tensorHigh n 1 (phaseC (Real.pi / 4)) ψ))
      = ((2⁻¹ : ℂ) * phaseC (-(Real.pi / 8)))
          • tensorHigh n 1 Complex.I
              ((rotOf (Real.pi / 8) (axisMat n P)).mulVec ψ) := by
  have h1 : (projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) true).mulVec
      (tensorHigh n 1 (phaseC (Real.pi / 4)) ψ)
      = (2⁻¹ : ℂ) • (tensorHigh n 1 (phaseC (Real.pi / 4)) ψ
          - tensorHigh n 1 (-(phaseC (Real.pi / 4)))
              ((axisMat n P).mulVec ψ)) := by
    rw [projHalf_mulVec, mulVec_joint_tensorHigh n P hs hw hk]
    simp [sub_eq_add_neg]
  rw [h1, projHalf_mulVec, Matrix.mulVec_smul, Matrix.mulVec_sub,
      mulVec_yn_tensorHigh, mulVec_yn_tensorHigh, rotOf,
      Matrix.sub_mulVec, smul_mulVec, smul_mulVec, Matrix.one_mulVec]
  funext m
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Pi.sub_apply, tensorHigh]
  rw [phaseC_eq, phaseC_eq, Real.cos_neg, Real.sin_neg,
      show Real.pi / 4 = 2 * (Real.pi / 8) from by ring,
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
    have h1 := Real.sin_two_mul (Real.pi / 8)
    have h2 := Real.cos_two_mul (Real.pi / 8)
    have h3 : (2 : Real) * (Real.pi / 8) = Real.pi / 4 := by ring
    rw [h3] at h1 h2
    have h4 : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hr2 : 2 * (Real.cos (Real.pi / 8) * Real.sin (Real.pi / 8))
        = 2 * Real.cos (Real.pi / 8) ^ 2 - 1 := by nlinarith [h1, h2, h4]
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
    linear_combination ((Complex.I + 1)
      * (ψ (lowBits n m) + ((axisMat n P).mulVec ψ) (lowBits n m)) / 2) * h45

/-- **Branch (a=1, c=1)**: joint outcome `−1`, Y-destruction outcome `−1` —
the data holds `P·e^{−iπ/8 P}ψ` (the `correct [c_b] P` fixes it),
ancilla `|−y⟩`. -/
theorem tBlock_branch_11 (n : Nat) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (hk : ∀ f ∈ P, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ψ : Fin (2 ^ n) → ℂ) :
    (projHalf (axisMat (n + 1) [(⟨n, .y⟩ : PFactor)]) true).mulVec
      ((projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) true).mulVec
        (tensorHigh n 1 (phaseC (Real.pi / 4)) ψ))
      = (-(2⁻¹ : ℂ) * phaseC (-(Real.pi / 8)))
          • tensorHigh n 1 (-Complex.I)
              ((axisMat n P).mulVec
                ((rotOf (Real.pi / 8) (axisMat n P)).mulVec ψ)) := by
  have h1 : (projHalf (axisMat (n + 1) (P ++ [⟨n, .z⟩])) true).mulVec
      (tensorHigh n 1 (phaseC (Real.pi / 4)) ψ)
      = (2⁻¹ : ℂ) • (tensorHigh n 1 (phaseC (Real.pi / 4)) ψ
          - tensorHigh n 1 (-(phaseC (Real.pi / 4)))
              ((axisMat n P).mulVec ψ)) := by
    rw [projHalf_mulVec, mulVec_joint_tensorHigh n P hs hw hk]
    simp [sub_eq_add_neg]
  rw [h1, projHalf_mulVec, Matrix.mulVec_smul, Matrix.mulVec_sub,
      mulVec_yn_tensorHigh, mulVec_yn_tensorHigh, rotOf,
      Matrix.sub_mulVec, smul_mulVec, smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, axisMat_mul_self, Matrix.one_mulVec]
  funext m
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Pi.sub_apply, tensorHigh]
  rw [phaseC_eq, phaseC_eq, Real.cos_neg, Real.sin_neg,
      show Real.pi / 4 = 2 * (Real.pi / 8) from by ring,
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
    have h1 := Real.sin_two_mul (Real.pi / 8)
    have h2 := Real.cos_two_mul (Real.pi / 8)
    have h3 : (2 : Real) * (Real.pi / 8) = Real.pi / 4 := by ring
    rw [h3] at h1 h2
    have h4 : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hr2 : 2 * (Real.cos (Real.pi / 8) * Real.sin (Real.pi / 8))
        = 2 * Real.cos (Real.pi / 8) ^ 2 - 1 := by nlinarith [h1, h2, h4]
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
    linear_combination (-(Complex.I + 1)
      * (ψ (lowBits n m) + ((axisMat n P).mulVec ψ) (lowBits n m)) / 2) * h45

end FormalRV.PauliRotation
