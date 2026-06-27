/- E2RunwaySynthSwap — Â§4-4b value-level conjugation + stage permutations.  Part of the `E2RunwaySynthSwap` re-export shim (same namespace). -/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.Stages

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthMCX
open FormalRV.Shor.WindowedCircuit (writeReg writeReg_at writeReg_frame
  decodeReg_testBit decodeReg_lt_two_pow decodeReg_succ_eq)


/-! ## §4. Value-level reasoning for the conjugation. -/

/-- When bit `p` of `z` is set, `clearBit z p = z XOR 2^p`. -/
theorem clearBit_eq_xor (z p : Nat) (hzp : z.testBit p = true) :
    clearBit z p = z ^^^ 2 ^ p := by
  unfold clearBit
  congr 1
  -- z &&& 2^p = 2^p
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hip : i = p
  · subst hip; rw [hzp]; simp
  · have : ¬ p = i := fun h => hip h.symm
    simp [this]

/-- `andExceptP M p k = true` for `M = maskAllExceptP k p` (every bit `i ≠ p`,
    `i < k`, of `M` is set). -/
theorem andExceptP_maskAllExceptP (k p : Nat) :
    andExceptP (maskAllExceptP k p) p k = true := by
  unfold andExceptP
  rw [List.all_eq_true]
  intro i hi
  obtain ⟨hilt, hip⟩ := (mem_ctrlIdxs k p i).mp hi
  rw [maskAllExceptP_testBit k p i hilt]
  simp [hip]

/-- `andExceptP (2^p XOR M) p k = true` (each bit `i ≠ p`, `i < k`, is
    `false XOR true = true`). -/
theorem andExceptP_two_pow_xor_mask (k p : Nat) (_hp : p < k) :
    andExceptP (2 ^ p ^^^ maskAllExceptP k p) p k = true := by
  unfold andExceptP
  rw [List.all_eq_true]
  intro i hi
  obtain ⟨hilt, hip⟩ := (mem_ctrlIdxs k p i).mp hi
  rw [Nat.testBit_xor, maskAllExceptP_testBit k p i hilt, Nat.testBit_two_pow]
  have : ¬ p = i := fun h => hip h.symm
  simp [hip, this]

/-! ## §4b. The stage permutations as named functions. -/

/-- `πreduce z p`: the reduceCNOT value permutation. -/
def piReduce (z p : Nat) (v : Nat) : Nat := if v.testBit p then v ^^^ clearBit z p else v

/-- `πanti k p`: the antiCtrlX value permutation (swaps `0 ↔ 2^p`, fixes others). -/
def piAnti (k p : Nat) (v : Nat) : Nat :=
  if andExceptP (v ^^^ maskAllExceptP k p) p k then v ^^^ 2 ^ p else v

/-- `clearBit z p` has bit `p` clear. -/
theorem clearBit_testBit_self (z p : Nat) : (clearBit z p).testBit p = false := by
  rw [clearBit_testBit]; simp

/-- `piReduce` preserves bit `p`. -/
theorem piReduce_testBit_p (z p v : Nat) : (piReduce z p v).testBit p = v.testBit p := by
  unfold piReduce
  by_cases hb : v.testBit p
  · rw [if_pos hb, Nat.testBit_xor, clearBit_testBit_self, Bool.xor_false]
  · rw [if_neg hb]

/-- `piReduce` is an involution. -/
theorem piReduce_involutive (z p v : Nat) : piReduce z p (piReduce z p v) = v := by
  unfold piReduce
  by_cases hb : v.testBit p
  · have hb' : (v ^^^ clearBit z p).testBit p = true := by
      rw [Nat.testBit_xor, clearBit_testBit_self, Bool.xor_false]; exact hb
    rw [if_pos hb, if_pos hb', Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · rw [if_neg hb, if_neg hb]

/-- `piAnti` fixes every value not in `{0, 2^p}` (when `p < k`).  More precisely:
    if some bit `i ≠ p` (`i < k`) of `w` is set, `piAnti` fixes `w`. -/
theorem piAnti_fix (k p w : Nat) (_hp : p < k)
    (hne : ¬ andExceptP (w ^^^ maskAllExceptP k p) p k) : piAnti k p w = w := by
  unfold piAnti; rw [if_neg hne]

/-- The net value permutation of the conjugation (`x ≠ y` case). -/
noncomputable def swapNet (k x y : Nat) (v : Nat) : Nat :=
  (piReduce (x ^^^ y) (lowestBit (x ^^^ y))
    (piAnti k (lowestBit (x ^^^ y))
      (piReduce (x ^^^ y) (lowestBit (x ^^^ y)) (v ^^^ x)))) ^^^ x

/-! ### The two moved values. -/

/-- `swapNet` sends `x` to `y`. -/
theorem swapNet_x (k x y : Nat) (hxy : x ≠ y) (_hp : lowestBit (x ^^^ y) < k) :
    swapNet k x y x = y := by
  have hz : x ^^^ y ≠ 0 := fun h => hxy (Nat.xor_eq_zero_iff.mp h)
  set z := x ^^^ y with hzdef
  set p := lowestBit z with hpdef
  have hzp : z.testBit p = true := by rw [hpdef]; exact testBit_lowestBit z hz
  unfold swapNet
  rw [← hzdef, ← hpdef]
  -- v ^^^ x = x ^^^ x = 0
  rw [Nat.xor_self]
  -- piReduce z p 0 = 0 (bit p of 0 is false)
  have h0 : piReduce z p 0 = 0 := by unfold piReduce; simp
  rw [h0]
  -- piAnti k p 0 = 0 ^^^ 2^p (condition true)
  have hanti : piAnti k p 0 = 2 ^ p := by
    unfold piAnti
    rw [Nat.zero_xor, if_pos (andExceptP_maskAllExceptP k p), Nat.zero_xor]
  rw [hanti]
  -- piReduce z p (2^p) = 2^p ^^^ clearBit z p = z
  have hred : piReduce z p (2 ^ p) = z := by
    unfold piReduce
    rw [if_pos (by rw [Nat.testBit_two_pow_self]), clearBit_eq_xor z p hzp]
    -- 2^p ^^^ (z ^^^ 2^p) = z
    rw [Nat.xor_comm z (2 ^ p), ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [hred]
  -- z ^^^ x = (x ^^^ y) ^^^ x = y
  rw [hzdef, Nat.xor_comm x y, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- `swapNet` sends `y` to `x`. -/
theorem swapNet_y (k x y : Nat) (hxy : x ≠ y) (hp : lowestBit (x ^^^ y) < k) :
    swapNet k x y y = x := by
  have hz : x ^^^ y ≠ 0 := fun h => hxy (Nat.xor_eq_zero_iff.mp h)
  set z := x ^^^ y with hzdef
  set p := lowestBit z with hpdef
  have hzp : z.testBit p = true := by rw [hpdef]; exact testBit_lowestBit z hz
  unfold swapNet
  rw [← hzdef, ← hpdef]
  -- y ^^^ x = z
  have hyx : y ^^^ x = z := by rw [hzdef, Nat.xor_comm]
  rw [hyx]
  -- piReduce z p z = z ^^^ clearBit z p = 2^p
  have hred1 : piReduce z p z = 2 ^ p := by
    unfold piReduce
    rw [if_pos hzp, clearBit_eq_xor z p hzp, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [hred1]
  -- piAnti k p (2^p) = 0  (condition true; 2^p ^^^ 2^p = 0)
  have hanti : piAnti k p (2 ^ p) = 0 := by
    unfold piAnti
    rw [if_pos (andExceptP_two_pow_xor_mask k p hp), Nat.xor_self]
  rw [hanti]
  -- piReduce z p 0 = 0
  have hred2 : piReduce z p 0 = 0 := by unfold piReduce; simp
  rw [hred2, Nat.zero_xor]

/-- If the anti-condition holds for `w < 2^k`, then `w ∈ {0, 2^p}` (`p < k`). -/
theorem andExceptP_xor_mask_cases (k p w : Nat) (hp : p < k) (hw : w < 2 ^ k)
    (hcond : andExceptP (w ^^^ maskAllExceptP k p) p k = true) :
    w = 0 ∨ w = 2 ^ p := by
  -- every bit i ≠ p (i < k) of w is 0; and bits ≥ k are 0 (w < 2^k).
  have hbits : ∀ i, i ≠ p → w.testBit i = false := by
    intro i hip
    by_cases hik : i < k
    · -- use the condition
      unfold andExceptP at hcond
      rw [List.all_eq_true] at hcond
      have hi_mem : i ∈ ctrlIdxs k p := (mem_ctrlIdxs k p i).mpr ⟨hik, hip⟩
      have := hcond i hi_mem
      rw [Nat.testBit_xor, maskAllExceptP_testBit k p i hik] at this
      simp [hip] at this
      exact this
    · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hik)))
  by_cases hwp : w.testBit p
  · right
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_two_pow]
    by_cases hip : i = p
    · subst hip; rw [hwp]; simp
    · rw [hbits i hip]; have : ¬ p = i := fun h => hip h.symm; simp [this]
  · left
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_cases hip : i = p
    · subst hip; exact Bool.not_eq_true _ ▸ hwp
    · exact hbits i hip

/-- `swapNet` fixes every value other than `x` and `y` (in range). -/
theorem swapNet_other (k x y : Nat) (hxy : x ≠ y)
    (hp : lowestBit (x ^^^ y) < k) (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (v : Nat) (hv : v < 2 ^ k) (hvx : v ≠ x) (hvy : v ≠ y) :
    swapNet k x y v = v := by
  have hz : x ^^^ y ≠ 0 := fun h => hxy (Nat.xor_eq_zero_iff.mp h)
  set z := x ^^^ y with hzdef
  set p := lowestBit z with hpdef
  -- g v := piReduce z p (v ^^^ x); it is < 2^k.
  set g := piReduce z p (v ^^^ x) with hg
  have hzlt : z < 2 ^ k := hzdef ▸ Nat.xor_lt_two_pow hx hy
  have hg_lt : g < 2 ^ k := by
    rw [hg]; unfold piReduce
    by_cases hb : (v ^^^ x).testBit p
    · rw [if_pos hb]; exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hv hx) (clearBit_lt z p k hzlt)
    · rw [if_neg hb]; exact Nat.xor_lt_two_pow hv hx
  -- the anti-condition must be false, else g ∈ {0, 2^p} ⇒ v ∈ {x, y}.
  have hcond_false : andExceptP (g ^^^ maskAllExceptP k p) p k = false := by
    by_contra hc
    have hc' : andExceptP (g ^^^ maskAllExceptP k p) p k = true := Bool.not_eq_false _ ▸ hc
    rcases andExceptP_xor_mask_cases k p g hp hg_lt hc' with hg0 | hgp
    · -- g = 0 ⇒ v ^^^ x = 0 ⇒ v = x.
      apply hvx
      have : piReduce z p (v ^^^ x) = 0 := hg0
      have h2 : v ^^^ x = 0 := by
        have := congrArg (piReduce z p) this
        rwa [piReduce_involutive, show piReduce z p 0 = 0 from by unfold piReduce; simp] at this
      exact Nat.xor_eq_zero_iff.mp h2
    · -- g = 2^p ⇒ v ^^^ x = z ⇒ v = y.
      apply hvy
      have : piReduce z p (v ^^^ x) = 2 ^ p := hgp
      have h2 : v ^^^ x = z := by
        have hh := congrArg (piReduce z p) this
        rw [piReduce_involutive] at hh
        -- piReduce z p (2^p) = z
        have hzp : z.testBit p = true := by rw [hpdef]; exact testBit_lowestBit z hz
        have hred : piReduce z p (2 ^ p) = z := by
          unfold piReduce
          rw [if_pos (by rw [Nat.testBit_two_pow_self]), clearBit_eq_xor z p hzp,
              Nat.xor_comm z (2 ^ p), ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
        rw [hred] at hh; exact hh
      -- v = y: v ^^^ x = x ^^^ y ⇒ v = y
      have : v = z ^^^ x := by rw [← h2, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [this, hzdef, Nat.xor_comm x y, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  -- with the condition false, piAnti fixes g, and the conjugation collapses.
  unfold swapNet
  rw [← hzdef, ← hpdef, ← hg, piAnti_fix k p g hp (by rw [hcond_false]; simp)]
  rw [hg, piReduce_involutive, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]


end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap
