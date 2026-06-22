/-
  FormalRV.PauliRotation.Correctness.CCXRow
  ─────────────────────────────
  THE CCX ROW: `gateRots (CCX a b t) = H_t ; CCZ(sort₃ a b t) ; H_t`
  denotes the Toffoli's Boolean semantics, with explicit global phase
  `−e^{−iπ/8}` — combining the proven H row (`hGate_denote`, the
  generalized Hadamard `(Z_t+X_t)/√2`) with the proven CCZ diagonal
  (`ccz_rots_denote`) by a conjugation computation in the
  diagonal/permutation calculus of `BasisAction`.

    §1  `seqDenote_append` — sequences compose contravariantly.
    §2  `flipT` and the X-permutation collapse lemmas
        (`xMat_mul_apply`, `mul_xMat_apply`).
    §3  `applyMat_CCX` + `sort3_bits` (the sorted triple tests the same
        bit set).
    §4  **`ccx_rots_applyNat`** — the end-to-end CCX row.
-/
import FormalRV.PauliRotation.Correctness.CCZRow

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open FormalRV.BQAlgo
open FormalRV.Framework (update update_apply)
open Matrix

/-! ## §1. Sequencing. -/

theorem seqDenote_append (n : Nat) (l₁ l₂ : List Rot) :
    seqDenote n (l₁ ++ l₂) = seqDenote n l₂ * seqDenote n l₁ := by
  induction l₁ with
  | nil => simp [seqDenote]
  | cons r l ih =>
      show seqDenote n (l ++ l₂) * Rot.denote n r = _
      rw [ih, Matrix.mul_assoc]
      rfl

/-! ## §2. The bit-flip permutation collapse. -/

/-- The bit-`t` flip as a `Fin` permutation. -/
def flipT (n t : Nat) (ht : t < n) (i : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨(i : Nat) ^^^ 2 ^ t,
   Nat.xor_lt_two_pow i.isLt (Nat.pow_lt_pow_right (by norm_num) ht)⟩

@[simp] theorem flipT_val (n t : Nat) (ht : t < n) (i : Fin (2 ^ n)) :
    ((flipT n t ht i : Fin (2 ^ n)) : Nat) = (i : Nat) ^^^ 2 ^ t := rfl

theorem flipT_flipT (n t : Nat) (ht : t < n) (i : Fin (2 ^ n)) :
    flipT n t ht (flipT n t ht i) = i := by
  apply Fin.ext
  show ((i : Nat) ^^^ 2 ^ t) ^^^ 2 ^ t = (i : Nat)
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- Left multiplication by `X_t` pre-flips the row index. -/
theorem xMat_mul_apply (n t : Nat) (ht : t < n)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (i j : Fin (2 ^ n)) :
    (axisMat n [(⟨t, .x⟩ : PFactor)] * M) i j = M (flipT n t ht i) j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (flipT n t ht i)]
  · rw [axisMat_single_x_apply n t ht]
    have : (i : Nat) = ((flipT n t ht i : Fin (2 ^ n)) : Nat) ^^^ 2 ^ t := by
      show (i : Nat) = ((i : Nat) ^^^ 2 ^ t) ^^^ 2 ^ t
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [if_pos this, one_mul]
  · intro k _ hk
    rw [axisMat_single_x_apply n t ht, if_neg, zero_mul]
    intro hik
    apply hk
    apply Fin.ext
    show (k : Nat) = (i : Nat) ^^^ 2 ^ t
    rw [hik, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- Right multiplication by `X_t` flips the column index. -/
theorem mul_xMat_apply (n t : Nat) (ht : t < n)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (i j : Fin (2 ^ n)) :
    (M * axisMat n [(⟨t, .x⟩ : PFactor)]) i j = M i (flipT n t ht j) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (flipT n t ht j)]
  · rw [axisMat_single_x_apply n t ht]
    have : ((flipT n t ht j : Fin (2 ^ n)) : Nat) = (j : Nat) ^^^ 2 ^ t := rfl
    rw [if_pos this, mul_one]
  · intro k _ hk
    rw [axisMat_single_x_apply n t ht, if_neg, mul_zero]
    intro hkj
    apply hk
    apply Fin.ext
    exact hkj
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-! ## §3. The CCX permutation and the sorted-triple bit set. -/

/-- The CCX gate's matrix: flip bit `t` exactly when bits `a` and `b` are
both set. -/
theorem applyMat_CCX (n a b t : Nat) (hat : a ≠ t) (hbt : b ≠ t) (ht : t < n)
    (i j : Fin (2 ^ n)) :
    applyMat n (.CCX a b t) i j
      = if (i : Nat) = (if (j : Nat).testBit a && (j : Nat).testBit b
            then (j : Nat) ^^^ 2 ^ t else (j : Nat))
        then 1 else 0 := by
  unfold applyMat
  congr 1
  rw [eq_iff_iff]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < n
    · rw [h k hk, Gate.applyNat_CCX, update_apply]
      by_cases hab : (j : Nat).testBit a && (j : Nat).testBit b
      · rw [if_pos hab]
        by_cases hkt : k = t
        · subst hkt
          rw [if_pos rfl, Nat.testBit_xor, Nat.testBit_two_pow_self]
          have h2 : ((j : Nat).testBit a && (j : Nat).testBit b) = true := hab
          simp at h2 ⊢
          simp [h2]
        · rw [if_neg hkt, Nat.testBit_xor, Nat.testBit_two_pow,
              decide_eq_false (fun hh => hkt hh.symm)]
          simp
      · rw [if_neg hab]
        by_cases hkt : k = t
        · subst hkt
          rw [if_pos rfl]
          have h2 : ((j : Nat).testBit k
              ^^ ((j : Nat).testBit a && (j : Nat).testBit b))
              = (j : Nat).testBit k := by
            simp [hab]
          exact h2
        · rw [if_neg hkt]
    · have hi : (i : Nat).testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have hj2 : (if (j : Nat).testBit a && (j : Nat).testBit b
          then (j : Nat) ^^^ 2 ^ t else (j : Nat)) < 2 ^ n := by
        by_cases hab : (j : Nat).testBit a && (j : Nat).testBit b
        · rw [if_pos hab]
          exact Nat.xor_lt_two_pow j.isLt
            (Nat.pow_lt_pow_right (by norm_num) ht)
        · rw [if_neg hab]
          exact j.isLt
      rw [hi, Nat.testBit_lt_two_pow (lt_of_lt_of_le hj2
        (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · intro h k hk
    rw [h, Gate.applyNat_CCX, update_apply]
    by_cases hab : (j : Nat).testBit a && (j : Nat).testBit b
    · rw [if_pos hab]
      by_cases hkt : k = t
      · subst hkt
        rw [if_pos rfl, Nat.testBit_xor, Nat.testBit_two_pow_self]
        have h2 : ((j : Nat).testBit a && (j : Nat).testBit b) = true := hab
        simp at h2 ⊢
        simp [h2]
      · rw [if_neg hkt, Nat.testBit_xor, Nat.testBit_two_pow,
            decide_eq_false (fun hh => hkt hh.symm)]
        simp
    · rw [if_neg hab]
      by_cases hkt : k = t
      · subst hkt
        rw [if_pos rfl]
        have h2 : ((j : Nat).testBit k
            ^^ ((j : Nat).testBit a && (j : Nat).testBit b))
            = (j : Nat).testBit k := by
          simp [hab]
        exact h2.symm
      · rw [if_neg hkt]

/-- Sorting the operand triple does not change the tested bit SET. -/
theorem sort3_bits (f : Nat → Bool) (a b t : Nat) :
    (f (sort3 a b t).1 && f (sort3 a b t).2.1 && f (sort3 a b t).2.2)
      = (f a && f b && f t) := by
  unfold sort3
  split_ifs <;> cases f a <;> cases f b <;> cases f t <;> rfl

/-! ## §4. The Hadamard conjugation core. -/

/-- The flip at `t` toggles bit `t`. -/
theorem testBit_xor_self_bit (m t : Nat) :
    (m ^^^ 2 ^ t).testBit t = !m.testBit t := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_self, Bool.xor_true]

/-- **THE CONJUGATION CORE**: conjugating the CCZ diagonal (stated over the
unsorted operand bits) by the unnormalized Hadamard `Z_t + X_t` gives twice
the Toffoli permutation. -/
theorem had_conj_core (n a b t : Nat) (hat : a ≠ t) (hbt : b ≠ t)
    (ht : t < n) :
    (axisMat n [(⟨t, .z⟩ : PFactor)] + axisMat n [(⟨t, .x⟩ : PFactor)])
        * Matrix.diagonal (fun m : Fin (2 ^ n) =>
            if (m : Nat).testBit a && (m : Nat).testBit b
                && (m : Nat).testBit t then (-1 : ℂ) else 1)
        * (axisMat n [(⟨t, .z⟩ : PFactor)] + axisMat n [(⟨t, .x⟩ : PFactor)])
      = (2 : ℂ) • applyMat n (.CCX a b t) := by
  set D := Matrix.diagonal (fun m : Fin (2 ^ n) =>
    if (m : Nat).testBit a && (m : Nat).testBit b && (m : Nat).testBit t
    then (-1 : ℂ) else 1) with hD
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
      axisMat_single_z_diag n t ht,
      show Matrix.diagonal (fun k : Fin (2 ^ n) =>
          if (k : Nat).testBit t then (-1 : ℂ) else 1) * D
        = Matrix.diagonal (fun k : Fin (2 ^ n) =>
            (if (k : Nat).testBit t then (-1 : ℂ) else 1)
              * (if (k : Nat).testBit a && (k : Nat).testBit b
                  && (k : Nat).testBit t then (-1 : ℂ) else 1))
        from Matrix.diagonal_mul_diagonal _ _]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply]
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal,
      mul_xMat_apply n t ht, mul_xMat_apply n t ht,
      xMat_mul_apply n t ht, xMat_mul_apply n t ht, hD,
      Matrix.diagonal_apply, Matrix.diagonal_apply, Matrix.diagonal_apply,
      Matrix.diagonal_apply, applyMat_CCX n a b t hat hbt ht]
  have hxx : (j : Nat) ^^^ 2 ^ t ≠ (j : Nat) := xor_two_pow_ne _ t
  have hxor2 : ((j : Nat) ^^^ 2 ^ t) ^^^ 2 ^ t = (j : Nat) := by
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have hc1 : ((i : Nat) ^^^ 2 ^ t = (j : Nat))
      ↔ ((i : Nat) = (j : Nat) ^^^ 2 ^ t) := by
    constructor
    · intro h
      rw [← h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · intro h
      rw [h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have hc2 : ((i : Nat) ^^^ 2 ^ t = (j : Nat) ^^^ 2 ^ t)
      ↔ ((i : Nat) = (j : Nat)) := by
    constructor
    · intro h
      have := congrArg (· ^^^ 2 ^ t) h
      simpa [Nat.xor_assoc] using this
    · intro h
      rw [h]
  by_cases hca : (j : Nat).testBit a <;>
    by_cases hcb : (j : Nat).testBit b <;>
      by_cases hbt' : (j : Nat).testBit t <;>
        by_cases hij : i = j <;>
          by_cases hijx : (i : Nat) = (j : Nat) ^^^ 2 ^ t <;>
            simp [Fin.ext_iff, Fin.val_inj, hca, hcb, hbt', hij, hijx, hxor2,
              hxx, Ne.symm hxx, hc1, hc2, testBit_xor_other hat,
              testBit_xor_other hbt] <;>
            first
              | omega
              | norm_num

/-! ## §5. THE CCX ROW, end-to-end. -/

/-- **THE CCX ROW, END-TO-END vs `Gate.applyNat`**: at any pairwise-distinct
wires `a, b, t < n`, the dictionary's thirteen rotations (`H_t ; CCZ ; H_t`)
denote the Toffoli's Boolean semantics as a matrix, with the explicit
global phase `−e^{−iπ/8}`. -/
theorem ccx_rots_applyNat (n a b t : Nat)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ha : a < n) (hb : b < n) (ht : t < n) :
    seqDenote n (gateRots (.CCX a b t))
      = (-(phaseC (-(Real.pi / 8)))) • applyMat n (.CCX a b t) := by
  obtain ⟨hxy, hyz, hmax⟩ := sort3_spec a b t hab hat hbt
  have hz : (sort3 a b t).2.2 < n := by omega
  have hccz : cczMat n (sort3 a b t).1 (sort3 a b t).2.1 (sort3 a b t).2.2
      = Matrix.diagonal (fun m : Fin (2 ^ n) =>
          if (m : Nat).testBit a && (m : Nat).testBit b && (m : Nat).testBit t
          then (-1 : ℂ) else 1) := by
    unfold cczMat
    congr 1
    funext m
    rw [sort3_bits (fun w => (m : Nat).testBit w) a b t]
  show seqDenote n (((hGate t).flatten
      ++ (cczGate (sort3 a b t).1 (sort3 a b t).2.1 (sort3 a b t).2.2).flatten)
      ++ (hGate t).flatten) = _
  rw [seqDenote_append, seqDenote_append, hGate_denote n t ht,
      ccz_rots_denote n _ _ _ hxy hyz hz, hccz]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← Matrix.mul_assoc, had_conj_core n a b t hat hbt ht, smul_smul]
  congr 1
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring_nf
  rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 from by rw [sq]; exact hs2]
  ring

end FormalRV.PauliRotation
