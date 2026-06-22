/-
  FormalRV.Shor.GidneyInPlace.InPlaceStepAction
  ─────────────────────────────────────────────────
  BRICK 4 of the two-register in-place coset-multiplier DYNAMICS transport — where the
  dynamics begins.  ONE relocated product-add step `relocatedProductAddStep`, lifted
  through the equiv `eGid` (Bricks 1-3): in the `xCtrlGid` work branch, it advances the
  RAW accumulator branch value `z` to the literal

        z' = (z + T (window w y j)) % 2 ^ bits

  (`T : Nat → Nat` is the abstract per-step table — the full multiplier's `Tfam j`),
  with the control/work branch shape unchanged, scratch restored, multiplicand fixed.

  This is the relocated-layout analog of `ReducedLookupEgate.step_perm_through_e_gate`
  / `ReducedLookupStepAction.reducedWindowStep_applyNat`.  Built STRICTLY from the
  ONE-STEP theorem `relocatedProductAddStep_inv` (NOT the whole-fold
  `gidneyProductAddTOf_state`), plus the one-step frame `relocatedProductAddStep_frame`:
   • `inplaceAccInput_RelocStepInv` — the eGid accumulator-input basis state satisfies
     `RelocStepInv` at partial sum `z` (the Brick-2 fact, restated directly for
     `inplaceAccInput`, no `cosetDim` bound needed).
   • `relocatedProductAddStep_offAcc` — one step leaves every NON-accumulator position
     unchanged (mirrors `gidneyProductAddTOf_offAcc`, one step): scratch/temp/carry
     restored and multiplicand preserved by the invariant, everything else framed.
   • `relocatedProductAddStep_applyNat` — THE one-step boolean action:
       `applyNat step (inplaceAccInput z) = inplaceAccInput ((z + T (window w y j)) % 2^bits)`.
     LITERAL `% 2^bits` (the register modulus), NOT `% N`.  The accumulator block is
     updated through the adder; the `copyWindow` load/unload only touches the address
     wires (framed), so it does not change the accumulator branch except via the step.
   • `extendBool_inplaceAccInput` — `inplaceAccInput`'s support fits in `[0, cosetDim)`.
   • `relocatedStep_perm_through_eGid` — THE eGid statement (the deliverable):
       `gateToPerm step (eGid (xCtrlGid, ⟨z⟩)) = eGid (xCtrlGid, ⟨(z + T (window w y j)) % 2^bits⟩)`,
     with `pass1`/`pass2` corollaries (`hpresY` discharged by
     `relocated_pass{1,2}_multiplicand_preserved`).

  AUDIT (per directive).  Uses the ONE-STEP `relocatedProductAddStep_inv`.  Update is
  LITERAL `% 2^bits`.  `z` is a RAW `Fin (2^bits)` branch index throughout (no residue
  mod N).  No coset superposition sum, no bad-set, no norm bound.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Input.InPlaceCosetInputGid

namespace FormalRV.Shor.GidneyInPlace.InPlaceStepAction

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.WindowedArith (window)
open FormalRV.Shor.GidneyInPlace.GatePerm (funboolNat gateToPerm extendBool applyFin)
open FormalRV.Shor.GidneyInPlace.CuccaroGatePerm (gateToPerm_funboolNat)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate
open FormalRV.Shor.GidneyInPlace.ProductAddWrapper
  (relocatedProductAddStep relocatedProductAddStep_wellTyped)
open FormalRV.Shor.GidneyInPlace.ProductAddArith
  (RelocStepInv relocatedProductAddStep_inv relocatedProductAddStep_frame)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputGid

/-! ## §1. `inplaceAccInput` satisfies `RelocStepInv` at partial sum `z`. -/

/-- The eGid accumulator-input basis state `inplaceAccInput z` satisfies the product-add
    per-step invariant `RelocStepInv … z`: ctrl set; address/AND/temp/carry clean;
    multiplicand `y` at `yBase`; accumulator decodes to `z`.  (Brick-2 content restated
    directly for `inplaceAccInput`; no `cosetDim` bound needed since `inplaceAccInput`
    is a total `Nat → Bool`.) -/
theorem inplaceAccInput_RelocStepInv (w bits numWin accBase tempBase yBase y z : Nat)
    (hbits : numWin * w = bits)
    (hacc : 2 * w < accBase) (hyy : 2 * w < yBase)
    (hv : accBase + bits ≤ tempBase) (hytemp : yBase + bits ≤ tempBase)
    (hYAccDisj : yBase + bits ≤ accBase ∨ accBase + bits ≤ yBase) :
    RelocStepInv w bits numWin y accBase tempBase yBase z
      (inplaceAccInput w bits numWin accBase yBase z y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [inplaceAccInput]
    rw [if_neg (by unfold ulookup_ctrl_idx; omega)]
    simp [inplaceWorkInput]
  · intro i hi
    simp only [inplaceAccInput]
    rw [if_neg (by unfold ulookup_address_idx; omega)]
    simp only [inplaceWorkInput]
    rw [if_neg (by unfold ulookup_address_idx ulookup_ctrl_idx; omega)]
    unfold encodeReg; rw [if_neg (by unfold ulookup_address_idx; omega)]
  · intro i hi
    simp only [inplaceAccInput]
    rw [if_neg (by unfold ulookup_and_idx; omega)]
    simp only [inplaceWorkInput]
    rw [if_neg (by unfold ulookup_and_idx ulookup_ctrl_idx; omega)]
    unfold encodeReg; rw [if_neg (by unfold ulookup_and_idx; omega)]
  · intro i hi
    simp only [inplaceAccInput]
    rw [if_neg (by omega)]
    simp only [inplaceWorkInput]
    rw [if_neg (by unfold ulookup_ctrl_idx; omega)]
    exact encodeReg_high yBase (numWin * w) y (tempBase + i) (by omega)
  · simp only [inplaceAccInput]
    rw [if_neg (by omega)]
    simp only [inplaceWorkInput]
    rw [if_neg (by unfold ulookup_ctrl_idx; omega)]
    exact encodeReg_high yBase (numWin * w) y (tempBase + bits) (by omega)
  · intro i hi
    simp only [inplaceAccInput]
    rw [if_neg (by rcases hYAccDisj with h | h <;> omega)]
    simp only [inplaceWorkInput]
    rw [if_neg (by unfold ulookup_ctrl_idx; omega)]
  · apply decodeReg_eq_mod_of_testBit
    intro i hi
    show inplaceAccInput w bits numWin accBase yBase z y (accBase + i) = z.testBit i
    simp only [inplaceAccInput]
    rw [if_pos ⟨by omega, by omega⟩]
    congr 1; omega

/-! ## §2. One step leaves every non-accumulator position unchanged. -/

/-- One relocated product-add step restores every NON-accumulator position, for an input
    satisfying `RelocStepInv` (mirrors `gidneyProductAddTOf_offAcc`, ONE step): the
    scratch/temp/carry are restored and the multiplicand preserved by the invariant
    (before = after on these), and any unrelated position is framed. -/
theorem relocatedProductAddStep_offAcc (w bits numWin : Nat) (T : Nat → Nat)
    (y accBase tempBase yBase j s : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin)
    (hv : accBase + bits ≤ tempBase) (hacc : 2 * w < accBase) (hyy : 2 * w < yBase)
    (hytemp : yBase + bits ≤ tempBase)
    (hpresY : ∀ (f' : Nat → Bool) i, i < numWin * w →
      Gate.applyNat (FormalRV.BQAlgo.relocatedAdderCircuit accBase tempBase bits) f' (yBase + i)
        = f' (yBase + i))
    (hcover : ∀ q, accBase ≤ q → q < tempBase + bits + 1 →
      (∃ i, i < bits ∧ q = accBase + i) ∨ (∃ i, i < bits ∧ q = tempBase + i)
        ∨ q = tempBase + bits ∨ (∃ i, i < numWin * w ∧ q = yBase + i))
    (g : Nat → Bool) (hg : RelocStepInv w bits numWin y accBase tempBase yBase s g)
    (p : Nat) (hp_acc : ∀ i, i < bits → p ≠ accBase + i) :
    Gate.applyNat (relocatedProductAddStep w bits T accBase tempBase yBase j) g p = g p := by
  have hafter := relocatedProductAddStep_inv w bits numWin T y accBase tempBase yBase j s
    hw hbits hj hv hacc hyy hytemp hpresY g hg
  obtain ⟨hgc, hg1, hg2, hg3, hg4, hg5, _⟩ := hg
  obtain ⟨hac, ha1, ha2, ha3, ha4, ha5, _⟩ := hafter
  by_cases hctrl : p = ulookup_ctrl_idx
  · rw [hctrl, hac, hgc]
  by_cases haddr : ∃ i, i < w ∧ p = ulookup_address_idx i
  · obtain ⟨i, hi, rfl⟩ := haddr; rw [ha1 i hi, hg1 i hi]
  by_cases hand : ∃ i, i < w ∧ p = ulookup_and_idx i
  · obtain ⟨i, hi, rfl⟩ := hand; rw [ha2 i hi, hg2 i hi]
  by_cases htmp : ∃ i, i < bits ∧ p = tempBase + i
  · obtain ⟨i, hi, rfl⟩ := htmp; rw [ha3 i hi, hg3 i hi]
  by_cases hcry : p = tempBase + bits
  · rw [hcry, ha4, hg4]
  by_cases hyb : ∃ i, i < numWin * w ∧ p = yBase + i
  · obtain ⟨i, hi, rfl⟩ := hyb; rw [ha5 i hi, hg5 i hi]
  have hbound : ¬ inBlock accBase (tempBase + bits + 1 - accBase) p := by
    intro hin
    unfold inBlock at hin
    rcases hcover p hin.1 (by omega) with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl | ⟨i, hi, rfl⟩
    · exact hp_acc i hi rfl
    · exact htmp ⟨i, hi, rfl⟩
    · exact hcry rfl
    · exact hyb ⟨i, hi, rfl⟩
  exact relocatedProductAddStep_frame w bits T accBase tempBase yBase j hv (by omega) p
    (fun i hi h => haddr ⟨i, hi, h⟩) hbound g

/-! ## §3. The one-step boolean action (LITERAL `% 2^bits`). -/

/-- **THE ONE-STEP BOOLEAN ACTION.**  One relocated product-add step maps the eGid
    accumulator input `inplaceAccInput z` to `inplaceAccInput ((z + T (window w y j)) %
    2^bits)`: the accumulator advances by the literal `j`-th window addend `mod 2^bits`,
    scratch/multiplicand unchanged.  Built from `relocatedProductAddStep_inv` (one step)
    + `relocatedProductAddStep_offAcc`. -/
theorem relocatedProductAddStep_applyNat (w bits numWin : Nat) (T : Nat → Nat)
    (y accBase tempBase yBase j z : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin)
    (hv : accBase + bits ≤ tempBase) (hacc : 2 * w < accBase) (hyy : 2 * w < yBase)
    (hytemp : yBase + bits ≤ tempBase)
    (hYAccDisj : yBase + bits ≤ accBase ∨ accBase + bits ≤ yBase)
    (hpresY : ∀ (f' : Nat → Bool) i, i < numWin * w →
      Gate.applyNat (FormalRV.BQAlgo.relocatedAdderCircuit accBase tempBase bits) f' (yBase + i)
        = f' (yBase + i))
    (hcover : ∀ q, accBase ≤ q → q < tempBase + bits + 1 →
      (∃ i, i < bits ∧ q = accBase + i) ∨ (∃ i, i < bits ∧ q = tempBase + i)
        ∨ q = tempBase + bits ∨ (∃ i, i < numWin * w ∧ q = yBase + i)) :
    Gate.applyNat (relocatedProductAddStep w bits T accBase tempBase yBase j)
        (inplaceAccInput w bits numWin accBase yBase z y)
      = inplaceAccInput w bits numWin accBase yBase ((z + T (window w y j)) % 2 ^ bits) y := by
  have hg : RelocStepInv w bits numWin y accBase tempBase yBase z
      (inplaceAccInput w bits numWin accBase yBase z y) :=
    inplaceAccInput_RelocStepInv w bits numWin accBase tempBase yBase y z hbits hacc hyy hv hytemp hYAccDisj
  have hafter := relocatedProductAddStep_inv w bits numWin T y accBase tempBase yBase j z
    hw hbits hj hv hacc hyy hytemp hpresY _ hg
  funext p
  by_cases hpacc : accBase ≤ p ∧ p < accBase + bits
  · -- accumulator block: read the advanced decode
    obtain ⟨h1, h2⟩ := hpacc
    have hdt := decodeReg_testBit (fun i => accBase + i) bits
      (Gate.applyNat (relocatedProductAddStep w bits T accBase tempBase yBase j)
        (inplaceAccInput w bits numWin accBase yBase z y)) (p - accBase) (by omega)
    rw [hafter.2.2.2.2.2.2] at hdt
    have hpe : (fun i => accBase + i) (p - accBase) = p := by
      show accBase + (p - accBase) = p; omega
    rw [hpe] at hdt
    rw [hdt.symm]
    simp only [inplaceAccInput]
    rw [if_pos ⟨h1, h2⟩]
  · -- off the accumulator block: framed, and the two `inplaceAccInput`s agree there
    rw [relocatedProductAddStep_offAcc w bits numWin T y accBase tempBase yBase j z
        hw hbits hj hv hacc hyy hytemp hpresY hcover _ hg p
        (fun i hi heq => hpacc ⟨by omega, by omega⟩)]
    simp only [inplaceAccInput]
    rw [if_neg hpacc, if_neg hpacc]

/-! ## §4. `inplaceAccInput` fits in `[0, cosetDim)`. -/

/-- `inplaceAccInput`'s support fits in `[0, cosetDim)`, so `extendBool (cosetDim) (its
    restriction) = inplaceAccInput` as `Nat → Bool` (mirrors `extendBool_mulInputAccOf`). -/
theorem extendBool_inplaceAccInput (w bits numWin accBase tempBase yBase z y : Nat)
    (hbits : numWin * w = bits) (hyy : 2 * w < yBase)
    (hytemp : yBase + bits ≤ tempBase)
    (haccfit : accBase + bits ≤ cosetDim w bits) (htfit : tempBase + bits < cosetDim w bits) :
    extendBool (cosetDim w bits)
        (fun i => inplaceAccInput w bits numWin accBase yBase z y i.val)
      = inplaceAccInput w bits numWin accBase yBase z y := by
  have hzero : ∀ k, cosetDim w bits ≤ k →
      inplaceAccInput w bits numWin accBase yBase z y k = false := by
    intro k hk
    simp only [inplaceAccInput]
    rw [if_neg (by omega)]
    simp only [inplaceWorkInput]
    rw [if_neg (by unfold ulookup_ctrl_idx; omega)]
    exact encodeReg_high yBase (numWin * w) y k (by omega)
  funext k
  unfold extendBool
  by_cases hkd : k < cosetDim w bits
  · rw [dif_pos hkd]
  · rw [dif_neg hkd]; exact (hzero k (by omega)).symm

/-! ## §5. The eGid step statement (the deliverable). -/

/-- **BRICK 4 — one product-add step through `eGid`.**  In the `xCtrlGid` work branch,
    one `relocatedProductAddStep` advances the RAW accumulator branch value `z` to
    `(z + T (window w y j)) % 2^bits` — same work/control branch, scratch restored,
    multiplicand fixed.  Relocated analog of `step_perm_through_e_gate`.  `hwt` is the
    step's well-typedness; `pass1`/`pass2` supply it and `hpresY`/`hcover`. -/
theorem relocatedStep_perm_through_eGid (w bits numWin : Nat) (T : Nat → Nat)
    (accBase tempBase yBase y z j : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin)
    (hz : z < 2 ^ bits) (hz2 : (z + T (window w y j)) % 2 ^ bits < 2 ^ bits)
    (hv : accBase + bits ≤ tempBase) (hacc : 2 * w < accBase) (hyy : 2 * w < yBase)
    (hytemp : yBase + bits ≤ tempBase)
    (hYAccDisj : yBase + bits ≤ accBase ∨ accBase + bits ≤ yBase)
    (haccfit : accBase + bits ≤ cosetDim w bits) (htfit : tempBase + bits < cosetDim w bits)
    (hpresY : ∀ (f' : Nat → Bool) i, i < numWin * w →
      Gate.applyNat (FormalRV.BQAlgo.relocatedAdderCircuit accBase tempBase bits) f' (yBase + i)
        = f' (yBase + i))
    (hcover : ∀ q, accBase ≤ q → q < tempBase + bits + 1 →
      (∃ i, i < bits ∧ q = accBase + i) ∨ (∃ i, i < bits ∧ q = tempBase + i)
        ∨ q = tempBase + bits ∨ (∃ i, i < numWin * w ∧ q = yBase + i))
    (hwt : Gate.WellTyped (cosetDim w bits) (relocatedProductAddStep w bits T accBase tempBase yBase j)) :
    gateToPerm (relocatedProductAddStep w bits T accBase tempBase yBase j) (cosetDim w bits) hwt
        (eGid w bits accBase haccfit (xCtrlGid w bits numWin accBase yBase y, ⟨z, hz⟩))
      = eGid w bits accBase haccfit
          (xCtrlGid w bits numWin accBase yBase y, ⟨(z + T (window w y j)) % 2 ^ bits, hz2⟩) := by
  rw [eGid_apply w bits numWin accBase yBase y z hz haccfit,
      eGid_apply w bits numWin accBase yBase y ((z + T (window w y j)) % 2 ^ bits) hz2 haccfit,
      gateToPerm_funboolNat]
  congr 1
  funext i
  show Gate.applyNat (relocatedProductAddStep w bits T accBase tempBase yBase j)
        (extendBool (cosetDim w bits)
          (fun i => inplaceAccInput w bits numWin accBase yBase z y i.val)) i.val
    = inplaceAccInput w bits numWin accBase yBase ((z + T (window w y j)) % 2 ^ bits) y i.val
  rw [extendBool_inplaceAccInput w bits numWin accBase tempBase yBase z y hbits hyy hytemp haccfit htfit,
      relocatedProductAddStep_applyNat w bits numWin T y accBase tempBase yBase j z
        hw hbits hj hv hacc hyy hytemp hYAccDisj hpresY hcover]

/-! ## §6. The faithful-layout corollaries. -/

/-- Pass 1 (`b += a·k`): accumulator `b @ 1+2w+bits`, multiplicand `a @ 1+2w`. -/
theorem relocatedStep_pass1_perm_through_eGid (w bits numWin : Nat) (T : Nat → Nat)
    (y z j : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin)
    (hz : z < 2 ^ bits) (hz2 : (z + T (window w y j)) % 2 ^ bits < 2 ^ bits)
    (hwt : Gate.WellTyped (cosetDim w bits)
      (relocatedProductAddStep w bits T (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) j)) :
    gateToPerm (relocatedProductAddStep w bits T (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) j)
        (cosetDim w bits) hwt
        (eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) y, ⟨z, hz⟩))
      = eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) y,
            ⟨(z + T (window w y j)) % 2 ^ bits, hz2⟩) :=
  relocatedStep_perm_through_eGid w bits numWin T (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w)
    y z j hw hbits hj hz hz2 (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
    (by unfold cosetDim; omega) (by unfold cosetDim; omega)
    (fun f' i hi => relocated_pass1_multiplicand_preserved w bits f' i (by omega))
    (fun q hq1 hq2 => by
      rcases Nat.lt_or_ge q (1 + 2 * w + 2 * bits) with h | h
      · exact Or.inl ⟨q - (1 + 2 * w + bits), by omega, by omega⟩
      rcases Nat.lt_or_ge q (1 + 2 * w + 3 * bits) with h2 | h2
      · exact Or.inr (Or.inl ⟨q - (1 + 2 * w + 2 * bits), by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl (by omega))))
    hwt

/-- Pass 2 (`a -= b·kInv`): accumulator `a @ 1+2w`, multiplicand `b @ 1+2w+bits` (the
    GAP — the y-disjunct of `hcover` is the gap-block branch). -/
theorem relocatedStep_pass2_perm_through_eGid (w bits numWin : Nat) (T : Nat → Nat)
    (y z j : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin)
    (hz : z < 2 ^ bits) (hz2 : (z + T (window w y j)) % 2 ^ bits < 2 ^ bits)
    (hwt : Gate.WellTyped (cosetDim w bits)
      (relocatedProductAddStep w bits T (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) j)) :
    gateToPerm (relocatedProductAddStep w bits T (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) j)
        (cosetDim w bits) hwt
        (eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) y, ⟨z, hz⟩))
      = eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) y,
            ⟨(z + T (window w y j)) % 2 ^ bits, hz2⟩) :=
  relocatedStep_perm_through_eGid w bits numWin T (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits)
    y z j hw hbits hj hz hz2 (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
    (by unfold cosetDim; omega) (by unfold cosetDim; omega)
    (fun f' i hi => relocated_pass2_multiplicand_preserved w bits f' i (by omega))
    (fun q hq1 hq2 => by
      rcases Nat.lt_or_ge q (1 + 2 * w + bits) with h | h
      · exact Or.inl ⟨q - (1 + 2 * w), by omega, by omega⟩
      rcases Nat.lt_or_ge q (1 + 2 * w + 2 * bits) with h2 | h2
      · exact Or.inr (Or.inr (Or.inr ⟨q - (1 + 2 * w + bits), by omega, by omega⟩))
      rcases Nat.lt_or_ge q (1 + 2 * w + 3 * bits) with h3 | h3
      · exact Or.inr (Or.inl ⟨q - (1 + 2 * w + 2 * bits), by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl (by omega))))
    hwt

end FormalRV.Shor.GidneyInPlace.InPlaceStepAction
