/-
  FormalRV.PauliRotation.Compiler.ToPPM.RotStep
  ────────────────────────────────────
  **THE SINGLE-ROTATION STEP THEOREMS**: one rotation's lowered block,
  executed by the branch semantics `progDenote`, equals an explicit
  branch scalar times the rotation's OWN matrix semantics `Rot.denote`
  applied to the data — uniformly on every outcome branch (the emitted
  `correct` statement cancels the teleport's Pauli residue).

    • `lowerRot_denote_free`    — π and π/2 (no ancilla, width `n`),
    • `lowerRot_denote_quarter` — the |Y⟩ S-block (ancilla at wire `n`),
    • `lowerRot_denote_eighth`  — the |T⟩/|T†⟩ T-block (selective
                                   destruction, both chiralities).

  The data factor is `(Rot.denote n r).mulVec ψ` in every case, so the
  program induction composes these to `(seqDenote n rs).mulVec ψ` — the
  rotation layer's own semantics.
-/
import FormalRV.PauliRotation.Compiler.ToPPM.TBlockNeg

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-! ## §1. Parity bookkeeping. -/

theorem xorParity_single (outs : List Bool) (c : Nat) :
    xorParity outs [c] = outs.getD c false := by
  unfold xorParity
  show (false ^^ outs.getD c false) = _
  rw [Bool.false_xor]

theorem xorParity_pair (outs : List Bool) (c c' : Nat) :
    xorParity outs [c, c'] = (outs.getD c false ^^ outs.getD c' false) := by
  unfold xorParity
  show ((false ^^ outs.getD c false) ^^ outs.getD c' false) = _
  rw [Bool.false_xor]

theorem getD_append_self (l : List Bool) (x : Bool) :
    (l ++ [x]).getD l.length false = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem getD_append_lt (l l' : List Bool) (i : Nat) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
      List.getD_eq_getElem?_getD]

/-! ## §2. The branch tables. -/

/-- The ancilla input amplitude pair `(1, ancInAmp r)`. -/
noncomputable def ancInAmp (r : Rot) : ℂ :=
  match r.angle with
  | .piQuarter => Complex.I
  | .piEighth  => if r.neg then phaseC (-(Real.pi / 4)) else phaseC (Real.pi / 4)
  | _          => 0

/-- The collapsed ancilla amplitude pair `(1, ancOutAmp r o₁ o₂)`. -/
noncomputable def ancOutAmp (r : Rot) (o₁ o₂ : Bool) : ℂ :=
  match r.angle with
  | .piQuarter => if o₂ then -1 else 1
  | .piEighth  =>
      if o₁ then (if o₂ then -Complex.I else Complex.I)
      else (if o₂ then -1 else 1)
  | _          => 0

/-- The branch scalar of one lowered rotation. -/
noncomputable def rotScalar (r : Rot) (o₁ o₂ : Bool) : ℂ :=
  match r.angle with
  | .pi     => -1
  | .piHalf => if r.neg then -Complex.I else Complex.I
  | .piQuarter =>
      (if r.neg then -Complex.I else 1) *
      (if o₁ then
        (if o₂ then (2⁻¹ : ℂ) * phaseC (-(Real.pi / 4))
         else -(2⁻¹ : ℂ) * phaseC (-(Real.pi / 4)))
       else (2⁻¹ : ℂ) * phaseC (Real.pi / 4))
  | .piEighth =>
      if r.neg then
        (if o₁ then
          (if o₂ then (2⁻¹ : ℂ) * phaseC (Real.pi / 8)
           else -(2⁻¹ : ℂ) * phaseC (Real.pi / 8))
         else (2⁻¹ : ℂ) * phaseC (-(Real.pi / 8)))
      else
        (if o₁ then
          (if o₂ then -(2⁻¹ : ℂ) * phaseC (-(Real.pi / 8))
           else (2⁻¹ : ℂ) * phaseC (-(Real.pi / 8)))
         else (2⁻¹ : ℂ) * phaseC (Real.pi / 8))

/-! ## §3. The ancilla-free rotations (π, π/2). -/

theorem lowerRot_denote_free (n : Nat) (r : Rot) (a c : Nat)
    (hanc : rotAnc r = 0)
    (ω : Nat → Bool) (outs : List Bool) (ψ : Fin (2 ^ n) → ℂ) :
    (progDenote n ω outs (lowerRot a c r)).mulVec ψ
      = rotScalar r (ω outs.length) (ω (outs.length + 1))
          • (Rot.denote n r).mulVec ψ := by
  unfold Rot.denote Rot.theta
  cases hang : r.angle with
  | pi =>
      simp only [lowerRot, hang]
      rw [show progDenote n ω outs []
            = (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) from rfl,
          Matrix.one_mulVec]
      cases hneg : r.neg <;>
        simp only [hang, Bool.false_eq_true, if_false, if_true,
          RAngle.val, rotScalar] <;>
        [rw [rotOf_pi]; rw [rotOf_neg_pi]] <;>
        rw [show (-1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
              = -(1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) from rfl,
            Matrix.neg_mulVec, Matrix.one_mulVec] <;>
        simp
  | piHalf =>
      simp only [lowerRot, hang]
      rw [show progDenote n ω outs [.frame r.axis]
            = (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
                * stmtDenote n outs (ω outs.length) (.frame r.axis) from rfl,
          Matrix.one_mul]
      show (axisMat n r.axis).mulVec ψ = _
      cases hneg : r.neg <;>
        simp only [hang, hneg, Bool.false_eq_true, if_false, if_true,
          RAngle.val, rotScalar] <;>
        [rw [rotOf_pi_div_two]; rw [rotOf_neg_pi_div_two]] <;>
        rw [smul_mulVec, smul_smul] <;>
        [rw [show Complex.I * -Complex.I = 1 from by
            rw [mul_neg, Complex.I_mul_I, neg_neg]];
         rw [show -Complex.I * Complex.I = 1 from by
            rw [neg_mul, Complex.I_mul_I, neg_neg]]] <;>
        rw [one_smul]
  | piQuarter => simp [rotAnc, hang] at hanc
  | piEighth => simp [rotAnc, hang] at hanc

/-! ## §4. The π/8 step (the |T⟩/|T†⟩ teleport block). -/

theorem getD_two_snd (outs : List Bool) (x y : Bool) :
    ((outs ++ [x]) ++ [y]).getD (outs.length + 1) false = y := by
  rw [show outs.length + 1 = (outs ++ [x]).length from by simp,
      getD_append_self]

theorem getD_two_fst (outs : List Bool) (x y : Bool) :
    ((outs ++ [x]) ++ [y]).getD outs.length false = x := by
  rw [getD_append_lt _ _ _ (by simp), getD_append_self]

/-- **π/8 lowers correctly**: the lowered block on `ψ ⊗ |T^{(†)}⟩` (ancilla
at wire `n`) equals the explicit branch scalar times `Rot.denote` applied
to the data, tensored with the collapsed ancilla — on EVERY branch. -/
theorem lowerRot_denote_eighth (n : Nat) (r : Rot)
    (hang : r.angle = RAngle.piEighth)
    (hs : sortedStrict r.axis = true)
    (hw : PauliProduct.width r.axis ≤ n)
    (hk : ∀ f ∈ r.axis, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ω : Nat → Bool) (outs : List Bool) (ψ : Fin (2 ^ n) → ℂ) :
    (progDenote (n + 1) ω outs (lowerRot n outs.length r)).mulVec
        (tensorHigh n 1 (ancInAmp r) ψ)
      = rotScalar r (ω outs.length) (ω (outs.length + 1))
          • tensorHigh n 1 (ancOutAmp r (ω outs.length) (ω (outs.length + 1)))
              ((Rot.denote n r).mulVec ψ) := by
  simp only [lowerRot, hang, ancInAmp, ancOutAmp, rotScalar]
  unfold Rot.denote Rot.theta
  simp only [hang, RAngle.val]
  simp only [progDenote, stmtDenote, PPMStmt.binds, List.replicate,
    List.append_nil, List.length_append, List.length_cons, List.length_nil,
    Matrix.mul_one, Matrix.one_mul]
  rw [xorParity_single, getD_append_self,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  cases hneg : r.neg with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [xorParity_single, getD_two_snd]
      cases ho₁ : ω outs.length <;> cases ho₂ : ω (outs.length + 1) <;>
        simp only [Bool.false_eq_true, if_false, if_true]
      · rw [tBlock_branch_00 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            show axisMat (n + 1) ([] : PauliProduct) = 1 from
              opsMat_one (n + 1), Matrix.one_mulVec]
      · rw [tBlock_branch_01 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            mulVec_axis_tensorHigh' n r.axis hs hw,
            Matrix.mulVec_mulVec, axisMat_mul_self, Matrix.one_mulVec]
      · rw [tBlock_branch_10 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            show axisMat (n + 1) ([] : PauliProduct) = 1 from
              opsMat_one (n + 1), Matrix.one_mulVec]
      · rw [tBlock_branch_11 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            mulVec_axis_tensorHigh' n r.axis hs hw,
            Matrix.mulVec_mulVec, axisMat_mul_self, Matrix.one_mulVec]
  | true =>
      simp only [if_true]
      rw [xorParity_pair, getD_two_fst, getD_two_snd]
      cases ho₁ : ω outs.length <;> cases ho₂ : ω (outs.length + 1) <;>
        simp only [Bool.false_eq_true, Bool.xor_false, Bool.xor_true,
          Bool.not_false, Bool.not_true, if_false, if_true]
      · rw [tBlockNeg_branch_00 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            show axisMat (n + 1) ([] : PauliProduct) = 1 from
              opsMat_one (n + 1), Matrix.one_mulVec]
      · rw [tBlockNeg_branch_01 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            mulVec_axis_tensorHigh' n r.axis hs hw,
            Matrix.mulVec_mulVec, axisMat_mul_self, Matrix.one_mulVec]
      · rw [tBlockNeg_branch_10 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            mulVec_axis_tensorHigh' n r.axis hs hw,
            Matrix.mulVec_mulVec, axisMat_mul_self, Matrix.one_mulVec]
      · rw [tBlockNeg_branch_11 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            show axisMat (n + 1) ([] : PauliProduct) = 1 from
              opsMat_one (n + 1), Matrix.one_mulVec]

/-! ## §5. The π/4 step (the |Y⟩ S-block). -/

/-- The negative π/4 absorbs as `P·e^{−iπ/4 P} = −i·e^{+iπ/4 P}` (the
appended `frame` plus phase). -/
theorem axisMat_mul_rotOf_quarter (n : Nat) (P : PauliProduct) :
    axisMat n P * rotOf (Real.pi / 4) (axisMat n P)
      = (-Complex.I) • rotOf (-(Real.pi / 4)) (axisMat n P) := by
  unfold rotOf
  rw [Real.cos_neg, Real.sin_neg, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.mul_one, Matrix.mul_smul, axisMat_mul_self,
      show Real.cos (Real.pi / 4) = Real.sin (Real.pi / 4) from by
        rw [Real.sin_pi_div_four, Real.cos_pi_div_four]]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases h : i = j <;> simp [h] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- **π/4 lowers correctly**: the lowered S-block on `ψ ⊗ |Y⟩` (ancilla at
wire `n`) equals the branch scalar times `Rot.denote` applied to the data,
tensored with the collapsed ancilla — on EVERY branch. -/
theorem lowerRot_denote_quarter (n : Nat) (r : Rot)
    (hang : r.angle = RAngle.piQuarter)
    (hs : sortedStrict r.axis = true)
    (hw : PauliProduct.width r.axis ≤ n)
    (hk : ∀ f ∈ r.axis, f.kind = PKind.z ∨ f.kind = PKind.x)
    (ω : Nat → Bool) (outs : List Bool) (ψ : Fin (2 ^ n) → ℂ) :
    (progDenote (n + 1) ω outs (lowerRot n outs.length r)).mulVec
        (tensorHigh n 1 (ancInAmp r) ψ)
      = rotScalar r (ω outs.length) (ω (outs.length + 1))
          • tensorHigh n 1 (ancOutAmp r (ω outs.length) (ω (outs.length + 1)))
              ((Rot.denote n r).mulVec ψ) := by
  simp only [lowerRot, hang, ancInAmp, ancOutAmp, rotScalar]
  unfold Rot.denote Rot.theta
  simp only [hang, RAngle.val]
  cases hneg : r.neg with
  | false =>
      simp only [Bool.false_eq_true, if_false, List.append_nil]
      simp only [progDenote, stmtDenote, PPMStmt.binds, List.replicate,
        List.length_append, List.length_cons, List.length_nil,
        Matrix.one_mul]
      rw [xorParity_pair, getD_two_fst, getD_two_snd,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      cases ho₁ : ω outs.length <;> cases ho₂ : ω (outs.length + 1) <;>
        (try simp only [Bool.false_eq_true, Bool.xor_false, Bool.xor_true,
          Bool.not_false, Bool.not_true, if_false, if_true, one_mul])
      · rw [sBlock_branch_00 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            show axisMat (n + 1) ([] : PauliProduct) = 1 from
              opsMat_one (n + 1), Matrix.one_mulVec]
      · rw [sBlock_branch_01 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            mulVec_axis_tensorHigh' n r.axis hs hw,
            Matrix.mulVec_mulVec, axisMat_mul_self, Matrix.one_mulVec]
      · rw [sBlock_branch_10 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            mulVec_axis_tensorHigh' n r.axis hs hw,
            Matrix.mulVec_mulVec, axisMat_mul_self, Matrix.one_mulVec]
      · rw [sBlock_branch_11 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            show axisMat (n + 1) ([] : PauliProduct) = 1 from
              opsMat_one (n + 1), Matrix.one_mulVec]
  | true =>
      simp only [if_true, List.cons_append, List.nil_append]
      simp only [progDenote, stmtDenote, PPMStmt.binds, List.replicate,
        List.length_append, List.length_cons, List.length_nil,
        Matrix.one_mul]
      rw [xorParity_pair, getD_two_fst, getD_two_snd,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec]
      cases ho₁ : ω outs.length <;> cases ho₂ : ω (outs.length + 1) <;>
        (try simp only [Bool.false_eq_true, Bool.xor_false, Bool.xor_true,
          Bool.not_false, Bool.not_true, if_false, if_true])
      · rw [sBlock_branch_00 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            show axisMat (n + 1) ([] : PauliProduct) = 1 from
              opsMat_one (n + 1), Matrix.one_mulVec, Matrix.mulVec_smul,
            mulVec_axis_tensorHigh' n r.axis hs hw,
            Matrix.mulVec_mulVec, axisMat_mul_rotOf_quarter,
            smul_mulVec, tensorHigh_vec_smul, smul_smul]
        congr 1
        ring
      · rw [sBlock_branch_01 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            mulVec_axis_tensorHigh' n r.axis hs hw,
            Matrix.mulVec_mulVec, axisMat_mul_self, Matrix.one_mulVec,
            Matrix.mulVec_smul, mulVec_axis_tensorHigh' n r.axis hs hw,
            Matrix.mulVec_mulVec, axisMat_mul_rotOf_quarter,
            smul_mulVec, tensorHigh_vec_smul, smul_smul]
        congr 1
        ring
      · rw [sBlock_branch_10 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            mulVec_axis_tensorHigh' n r.axis hs hw,
            Matrix.mulVec_mulVec, axisMat_mul_self, Matrix.one_mulVec,
            Matrix.mulVec_smul, mulVec_axis_tensorHigh' n r.axis hs hw,
            Matrix.mulVec_mulVec, axisMat_mul_rotOf_quarter,
            smul_mulVec, tensorHigh_vec_smul, smul_smul]
        congr 1
        ring
      · rw [sBlock_branch_11 n r.axis hs hw hk ψ, Matrix.mulVec_smul,
            show axisMat (n + 1) ([] : PauliProduct) = 1 from
              opsMat_one (n + 1), Matrix.one_mulVec, Matrix.mulVec_smul,
            mulVec_axis_tensorHigh' n r.axis hs hw,
            Matrix.mulVec_mulVec, axisMat_mul_rotOf_quarter,
            smul_mulVec, tensorHigh_vec_smul, smul_smul]
        congr 1
        ring

end FormalRV.PauliRotation
