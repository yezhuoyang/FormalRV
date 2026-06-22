/-
  FormalRV.Shor.GidneyInPlace.ReducedLookupStepAction — gate-specific BASIS one-step action for ONE reduced window step
  of the Cuccaro coset multiplier (multiplier-local; NO Shor/QPE).
-/
import FormalRV.Shor.GidneyInPlace.ReducedLookup.Def.ReducedLookupCosetGate
import FormalRV.Arithmetic.Windowed.WindowedInPlace
import FormalRV.Shor.GidneyInPlace.Gate.Proof.CuccaroGatePerm
import FormalRV.Shor.GidneyInPlace.Gate.Spec.UCEvalBridge

namespace FormalRV.Shor.GidneyInPlace.ReducedLookupStepAction

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.WindowedArith (tableValue window)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate
open FormalRV.Shor.GidneyInPlace.GatePerm
open FormalRV.Shor.GidneyInPlace.UCEvalBridge
open FormalRV.Shor.GidneyInPlace.CuccaroGatePerm

/-! ## LEMMA 1 — StepInv extensionality (Cuccaro). -/

/-- **StepInv determines `mulInputAccOf`.**  Any state satisfying the window-step
    invariant with partial sum `s` IS (bit-for-bit) the nonzero-accumulator input
    state with accumulator `s % 2^bits`. -/
theorem stepInv_determines_mulInputAccOf (w bits numWin y s : Nat) (g : Nat → Bool)
    (hg : StepInv cuccaroAdder w bits numWin y s g) :
    g = mulInputAccOf cuccaroAdder w bits numWin (s % 2 ^ bits) y := by
  obtain ⟨hF, hD, hC, hV⟩ := hg
  -- Cuccaro layout facts.
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  -- The injectivity of the augend positions (for writeReg_at).
  have hinj : ∀ i j, i < bits → j < bits →
      cuccaroAdder.augendIdx (1 + 2 * w) i = cuccaroAdder.augendIdx (1 + 2 * w) j → i = j :=
    fun i j _ _ h => cuccaroAdder_augendIdx_inj (1 + 2 * w) i j h
  funext p
  unfold mulInputAccOf
  -- Block trichotomy by omega.  Distinguish in-block vs off-block.
  by_cases hin : inBlock (1 + 2 * w) (cuccaroAdder.span bits) p
  · -- In-block: p is carry-in (1+2w), an augend (1+2w+2i+1), or an addend (1+2w+2i+2).
    rw [hspan] at hin
    unfold inBlock at hin
    obtain ⟨hlo, hhi⟩ := hin
    by_cases hcarry : p = 1 + 2 * w
    · -- Carry-in.  g p = false (by C); writeReg frame (carry not an augend) + mulInputOf_low.
      subst hcarry
      rw [hC]
      rw [writeReg_frame _ _ _ _ _ (fun i hi heq => by
        -- augendIdx (1+2w) i = 1+2w+2i+1 ≠ 1+2w
        have : cuccaroAdder.augendIdx (1 + 2 * w) i = 1 + 2 * w + 2 * i + 1 := rfl
        omega)]
      exact (mulInputOf_low cuccaroAdder w bits numWin y _
        (by unfold ulookup_ctrl_idx; omega) (by rw [hspan]; omega)).symm
    · -- Not carry-in.  p ≥ 1+2w+1, p < 1+2w+2*bits+1.  Even (addend) or odd (augend).
      by_cases hpar : (p - (1 + 2 * w)) % 2 = 1
      · -- Odd offset ⇒ augend: p = 1+2w+2*i+1 with i = (p-(1+2w)-1)/2 < bits.
        set i := (p - (1 + 2 * w) - 1) / 2 with hidef
        have hi : i < bits := by omega
        have hpeq : p = cuccaroAdder.augendIdx (1 + 2 * w) i := by
          show p = 1 + 2 * w + 2 * i + 1
          omega
        rw [hpeq]
        -- g (augend i) = (s % 2^bits).testBit i, via V + decodeReg_testBit.
        rw [← decodeReg_testBit (cuccaroAdder.augendIdx (1 + 2 * w)) bits g i hi, hV]
        rw [writeReg_at _ bits (s % 2 ^ bits) _ hinj i hi]
      · -- Even offset ⇒ addend: p = 1+2w+2*i+2 with i = (p-(1+2w)-2)/2 < bits.
        set i := (p - (1 + 2 * w) - 2) / 2 with hidef
        have hi : i < bits := by omega
        have hpeq : p = cuccaroAdder.addendIdx (1 + 2 * w) i := by
          show p = 1 + 2 * w + 2 * i + 2
          omega
        rw [hpeq, hD i hi]
        -- mulInputAccOf (addend i): writeReg frame (addend ≠ augend) + mulInputOf_low.
        rw [writeReg_frame _ _ _ _ _ (fun k hk =>
              Ne.symm (cuccaroAdder.augend_addend_disjoint (1 + 2 * w) k i))]
        have hblk := cuccaroAdder.addendIdx_inBlock bits (1 + 2 * w) i hi
        unfold inBlock at hblk
        exact (mulInputOf_low cuccaroAdder w bits numWin y _
          (by unfold ulookup_ctrl_idx; omega) (by rw [hspan] at hblk ⊢; omega)).symm
  · -- Off-block: g p = mulInputOf p (by F); writeReg frame (p off-block, augend in-block).
    rw [hF p hin]
    rw [writeReg_frame _ _ _ _ _ (fun i hi heq => hin (by
      rw [heq]; exact cuccaroAdder.augendIdx_inBlock bits (1 + 2 * w) i hi))]

/-! ## LEMMA 2 — basis applyNat one-step action. -/

/-- **One reduced window step on the accumulator input.**  Applying the reduced-lookup
    window step `j` (Cuccaro) to `mulInputAccOf .. z y` advances the accumulator by
    `tableValue a N w j (window w y j)` mod `2^bits`. -/
theorem reducedWindowStep_applyNat (w bits N a numWin z y j : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin) :
    Gate.applyNat (reducedWindowStepOf cuccaroAdder w bits N a bits (1 + 2 * w)
        (1 + 2 * w + cuccaroAdder.span bits) j)
        (mulInputAccOf cuccaroAdder w bits numWin z y)
      = mulInputAccOf cuccaroAdder w bits numWin
          ((z + tableValue a N w j (window w y j)) % 2 ^ bits) y := by
  have hinj : ∀ i j, i < bits → j < bits →
      cuccaroAdder.augendIdx (1 + 2 * w) i = cuccaroAdder.augendIdx (1 + 2 * w) j → i = j :=
    fun i j _ _ h => cuccaroAdder_augendIdx_inj (1 + 2 * w) i j h
  -- The Cuccaro ancilla-clean precondition: the carry-in (= block base) is false in the input.
  have hclean : cuccaroAdder.ancClean (mulInputAccOf cuccaroAdder w bits numWin z y) bits
      (1 + 2 * w) := by
    show mulInputAccOf cuccaroAdder w bits numWin z y (1 + 2 * w) = false
    unfold mulInputAccOf
    rw [writeReg_frame _ _ _ _ _ (fun i hi heq => by
      have : cuccaroAdder.augendIdx (1 + 2 * w) i = 1 + 2 * w + 2 * i + 1 := rfl
      omega)]
    have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
    exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega) (by rw [hspan]; omega)
  -- The invariant holds at start value z.
  have hstart : StepInv cuccaroAdder w bits numWin y z
      (mulInputAccOf cuccaroAdder w bits numWin z y) :=
    stepInv_init_acc cuccaroAdder w bits numWin z y hinj hclean
  -- One generic table step (the gate is DEFEQ to windowStepTOf at table tableValue a N w j).
  have hstep := stepInv_stepT cuccaroAdder w bits (tableValue a N w j) numWin y hw j hj z
    (mulInputAccOf cuccaroAdder w bits numWin z y) hstart
  -- LEMMA 1 turns the post-state into the shifted accumulator input.
  have hpost := stepInv_determines_mulInputAccOf w bits numWin y
    (z + tableValue a N w j (window w y j))
    (Gate.applyNat (windowStepTOf cuccaroAdder w bits (tableValue a N w j) bits (1 + 2 * w)
        (1 + 2 * w + cuccaroAdder.span bits) j)
      (mulInputAccOf cuccaroAdder w bits numWin z y)) hstep
  -- reducedWindowStepOf .. = windowStepTOf .. (tableValue a N w j) is rfl.
  exact hpost

/-! ## LEMMA 3 — uc_eval / basis-vector one-step action. -/

/-- The `mulInputAccOf` register support fits in `[0, cosetDim)` under `numWin*w = bits`,
    so `extendBool (cosetDim) (restriction) = mulInputAccOf` as `Nat → Bool`. -/
theorem extendBool_mulInputAccOf (w bits _N _a numWin z y : Nat) (hbits : numWin * w = bits) :
    extendBool (cosetDim w bits)
        (fun i => mulInputAccOf cuccaroAdder w bits numWin z y i.val)
      = mulInputAccOf cuccaroAdder w bits numWin z y := by
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  -- mulInputAccOf reads false at every k ≥ cosetDim.
  have hzero : ∀ k, cosetDim w bits ≤ k →
      mulInputAccOf cuccaroAdder w bits numWin z y k = false := by
    intro k hk
    unfold mulInputAccOf
    -- writeReg only touches augend positions 1+2w+2i+1 < cosetDim ≤ k, so frame.
    rw [writeReg_frame _ _ _ _ _ (fun i hi heq => by
      have haug : cuccaroAdder.augendIdx (1 + 2 * w) i = 1 + 2 * w + 2 * i + 1 := rfl
      unfold cosetDim at hk
      omega)]
    -- mulInputOf k: ctrl=0 < cosetDim ≤ k so k≠0; encodeReg high gives false.
    unfold cosetDim at hk
    rw [mulInputOf_eq_encodeReg cuccaroAdder w bits numWin y _
        (by unfold ulookup_ctrl_idx; omega)]
    refine encodeReg_high _ _ _ _ ?_
    rw [hspan]
    -- need 1 + 2*w + (2*bits+1) + numWin*w ≤ k; numWin*w = bits, cosetDim = 2+2w+3*bits ≤ k.
    rw [hbits]
    omega
  funext k
  unfold extendBool
  by_cases hkd : k < cosetDim w bits
  · rw [dif_pos hkd]
  · rw [dif_neg hkd]
    exact (hzero k (by omega)).symm

/-- **One reduced window step on the basis vector (uc_eval form).**  The literal SQIR
    unitary of the Cuccaro reduced window step `j` maps the basis vector of the
    accumulator input `z` to the basis vector of the shifted accumulator input. -/
theorem reducedWindowStep_uc_eval (w bits N a numWin z y j : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin) :
    Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (reducedWindowStepOf cuccaroAdder w bits N a bits (1 + 2 * w)
          (1 + 2 * w + cuccaroAdder.span bits) j))
      * Framework.basis_vector (2 ^ cosetDim w bits)
          (funboolNat (cosetDim w bits)
            (fun i => mulInputAccOf cuccaroAdder w bits numWin z y i.val)).val
    = Framework.basis_vector (2 ^ cosetDim w bits)
        (funboolNat (cosetDim w bits)
          (fun i => mulInputAccOf cuccaroAdder w bits numWin
            ((z + tableValue a N w j (window w y j)) % 2 ^ bits) y i.val)).val := by
  set hwt := reducedWindowStepOf_cuccaro_wellTyped w bits N a numWin j (cosetDim w bits)
    hw hbits hj (by unfold cosetDim; omega) with hwtdef
  rw [uc_eval_basis_agree _ _ hwt, gateToPerm_funboolNat _ _ hwt]
  -- applyFin (step) (cosetDim) (input restriction) = output restriction (as Fin dim → Bool).
  have hfun : applyFin (reducedWindowStepOf cuccaroAdder w bits N a bits (1 + 2 * w)
        (1 + 2 * w + cuccaroAdder.span bits) j) (cosetDim w bits)
        (fun i => mulInputAccOf cuccaroAdder w bits numWin z y i.val)
      = (fun i => mulInputAccOf cuccaroAdder w bits numWin
          ((z + tableValue a N w j (window w y j)) % 2 ^ bits) y i.val) := by
    funext i
    show Gate.applyNat (reducedWindowStepOf cuccaroAdder w bits N a bits (1 + 2 * w)
          (1 + 2 * w + cuccaroAdder.span bits) j)
        (extendBool (cosetDim w bits)
          (fun i => mulInputAccOf cuccaroAdder w bits numWin z y i.val)) i.val
      = mulInputAccOf cuccaroAdder w bits numWin
          ((z + tableValue a N w j (window w y j)) % 2 ^ bits) y i.val
    rw [extendBool_mulInputAccOf w bits N a numWin z y hbits,
        reducedWindowStep_applyNat w bits N a numWin z y j hw hbits hj]
  rw [hfun]

end FormalRV.Shor.GidneyInPlace.ReducedLookupStepAction