/-
  FormalRV.Shor.GidneyInPlace.InPlaceEgateInput
  ─────────────────────────────────────────────────
  BRICK 2 of the two-register in-place coset-multiplier DYNAMICS transport:
  the clean control value `xCtrlGid` for `eGid` (BRICK 1), and the proof that under
  `eGid` a data-branch value `z` corresponds to a CONCRETE basis state satisfying
  `ProductAddArith.RelocStepInv` — the per-step invariant consumed by the already-proven
  boolean product-add state theorem `gidneyProductAddTOf_state`/`_decode`.

  This is the relocated-layout analog of `ReducedLookupEgate.xCtrl` / `assembleE_xCtrl`
  / `mulInputAccOf`:
   • `inplaceWorkInput` — the clean WORK register basis function (ctrl bit set;
     address/AND/temp/carry clean; multiplicand `y` encoded at `yBase`).  Scratch
     positions are clean because they lie OUTSIDE the multiplicand window
     `[yBase, yBase+numWin·w)` (so `encodeReg` returns `false` there).
   • `inplaceAccInput z` — `inplaceWorkInput` with the accumulator block `[accBase,
     accBase+bits)` holding the data value `z` (little-endian).  This is the
     `mulInputAccOf` analog: the basis state `eGid` sends `(xCtrlGid, z)` to.
   • `xCtrlGid` — the `eGid` control value: `decodeReg compIdxGid` of `inplaceWorkInput`.
   • `assembleEGid_xCtrlGid` — pointwise: `assembleEGid (xCtrlGid) z = inplaceAccInput z`
     on `[0, cosetDim)` (the brick-3 `eGid_apply` ingredient).
   • `xCtrlGid_RelocStepInv` — the payoff: `RelocStepInv … z (assembleEGid (xCtrlGid) z)`,
     i.e. the eGid data-branch value `z` IS a valid product-add input with accumulator
     `z`.  PARAMETERIZED by `accBase`/`yBase`/`tempBase`; the `pass1`/`pass2` corollaries
     instantiate the faithful layout (pass-1 acc `b @ 1+2w+bits`, mult `a @ 1+2w`;
     pass-2 acc `a @ 1+2w`, mult `b @ 1+2w+bits` — the GAP, off the acc block via
     `hYAccDisj`).

  Acceptance (per directive):  identifies the accBase-selected accumulator block (NOT
  hard-wired to pass-1's `bBase`); the complement/work bits ARE exactly the
  ctrl/address/AND/temp/carry assumptions of `RelocStepInv`; the multiplicand block is
  PLACED at `yBase` disjoint from the accumulator block; serves BOTH passes.  NO
  coset-state / bad-set lift.

  SCOPE OF THE GAP CLAIM (honest distinction).  This is an INPUT-STATE brick, so the
  pass-2 multiplicand sitting in the gap is handled by the STATIC layout disjointness
  `hYAccDisj : yBase+bits ≤ accBase ∨ accBase+bits ≤ yBase` (the `assembleEGid` write to
  the accumulator block misses the `yBase` window).  This is NOT the DYNAMIC gap-frame
  (`RelocatedTransport.relocated_gap_frame` / `relocated_pass2_multiplicand_preserved`),
  which proves the relocated ADDER leaves the gap untouched DURING evaluation — a
  separate evaluation-time fact consumed downstream by `gidneyProductAdd_pass2_decode`
  (the `hpresY` argument), NOT used here.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Def.InPlaceEgate
import FormalRV.Shor.GidneyInPlace.Adder.Spec.ProductAddArith

namespace FormalRV.Shor.GidneyInPlace.InPlaceEgateInput

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate
open FormalRV.Shor.GidneyInPlace.ProductAddArith (RelocStepInv)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate

/-! ## §1. The clean work-input and accumulator-input basis functions. -/

/-- The clean WORK register basis function: ctrl bit set; the multiplicand `y` encoded
    at `[yBase, yBase+numWin·w)`; everything else `false` (so the address/AND/temp/carry
    scratch — all OUTSIDE the multiplicand window — read clean). -/
def inplaceWorkInput (numWin w yBase y : Nat) : Nat → Bool :=
  fun p => if p = ulookup_ctrl_idx then true else encodeReg yBase (numWin * w) y p

/-- `inplaceWorkInput` with the contiguous accumulator block `[accBase, accBase+bits)`
    set to the data value `z`.  This is the `mulInputAccOf` analog — the basis state
    `eGid` sends `(xCtrlGid, z)` to. -/
def inplaceAccInput (w bits numWin accBase yBase z y : Nat) : Nat → Bool :=
  fun p => if accBase ≤ p ∧ p < accBase + bits then z.testBit (p - accBase)
           else inplaceWorkInput numWin w yBase y p

/-- The `eGid` control value: the complement-register decode of the clean work input. -/
noncomputable def xCtrlGid (w bits numWin accBase yBase y : Nat) :
    Fin (2 ^ (cosetDim w bits - bits)) :=
  ⟨decodeReg (compIdxGid bits accBase) (cosetDim w bits - bits)
      (inplaceWorkInput numWin w yBase y),
   decodeReg_lt_two_pow _ _ _⟩

/-! ## §2. `assembleEGid` of the clean control value IS `inplaceAccInput`. -/

/-- **The brick-3 `eGid_apply` ingredient.**  `assembleEGid` of the clean control value
    `xCtrlGid` at data `z` equals `inplaceAccInput z` on `[0, cosetDim)` — the
    relocated analog of `assembleE_xCtrl … = mulInputAccOf`. -/
theorem assembleEGid_xCtrlGid (w bits numWin accBase yBase y z p : Nat)
    (haccfit : accBase + bits ≤ cosetDim w bits) (hp : p < cosetDim w bits) :
    assembleEGid w bits accBase (xCtrlGid w bits numWin accBase yBase y).val z p
      = inplaceAccInput w bits numWin accBase yBase z y p := by
  rcases coverGid w bits accBase p haccfit hp with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · -- accumulator position `accBase + i`
    rw [assembleEGid_data w bits accBase _ z i hi]
    simp only [inplaceAccInput]
    rw [if_pos ⟨Nat.le_add_right _ _, by omega⟩]
    congr 1; omega
  · -- complement position `compIdxGid j`
    rw [assembleEGid_comp w bits accBase _ z j hj,
        show (xCtrlGid w bits numWin accBase yBase y).val
            = decodeReg (compIdxGid bits accBase) (cosetDim w bits - bits)
                (inplaceWorkInput numWin w yBase y) from rfl,
        decodeReg_testBit (compIdxGid bits accBase) (cosetDim w bits - bits) _ j hj]
    simp only [inplaceAccInput]
    rw [if_neg (compIdxGid_off_block bits accBase j)]

/-! ## §3. The payoff: the eGid data branch `z` satisfies `RelocStepInv`. -/

/-- **BRICK 2 — `RelocStepInv` for the eGid control branch.**  For the clean control
    value `xCtrlGid` and any data value `z`, the assembled basis state
    `assembleEGid (xCtrlGid) z` satisfies the product-add per-step invariant
    `RelocStepInv … z`: ctrl set; address/AND/temp/carry clean; multiplicand `y`
    preserved at `yBase`; accumulator decodes to `z`.  This is the bridge from `eGid`'s
    data factor to the boolean `gidneyProductAddTOf_state`/`_decode`.

    Hypotheses are the layout bounds (all discharged by the `pass1`/`pass2` corollaries):
    `hacc`/`hyy` put the lookup zone `[0,2w]` below the accumulator and multiplicand;
    `hv`/`hytemp`/`htfit`/`haccfit` place the temp/carry block and bound `cosetDim`;
    `hYAccDisj` is the STATIC disjointness of the multiplicand window from the
    accumulator block (for pass-2 the multiplicand `b` is placed in the gap ABOVE the
    accumulator — `Or.inr`).  This is input-state placement only; the dynamic adder
    gap-frame is a separate downstream fact (see the file header). -/
theorem xCtrlGid_RelocStepInv (w bits numWin accBase tempBase yBase y z : Nat)
    (hbits : numWin * w = bits)
    (hacc : 2 * w < accBase) (hyy : 2 * w < yBase)
    (hv : accBase + bits ≤ tempBase) (hytemp : yBase + bits ≤ tempBase)
    (haccfit : accBase + bits ≤ cosetDim w bits) (htfit : tempBase + bits < cosetDim w bits)
    (hYAccDisj : yBase + bits ≤ accBase ∨ accBase + bits ≤ yBase) :
    RelocStepInv w bits numWin y accBase tempBase yBase z
      (assembleEGid w bits accBase (xCtrlGid w bits numWin accBase yBase y).val z) := by
  have hpt : ∀ p, p < cosetDim w bits →
      assembleEGid w bits accBase (xCtrlGid w bits numWin accBase yBase y).val z p
        = inplaceAccInput w bits numWin accBase yBase z y p :=
    fun p hp => assembleEGid_xCtrlGid w bits numWin accBase yBase y z p haccfit hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ctrl bit set
    rw [hpt ulookup_ctrl_idx (by unfold ulookup_ctrl_idx; omega)]
    simp only [inplaceAccInput]
    rw [if_neg (by unfold ulookup_ctrl_idx; omega)]
    simp [inplaceWorkInput]
  · -- address clean
    intro i hi
    rw [hpt (ulookup_address_idx i) (by unfold ulookup_address_idx; omega)]
    simp only [inplaceAccInput]
    rw [if_neg (by unfold ulookup_address_idx; omega)]
    simp only [inplaceWorkInput]
    rw [if_neg (by unfold ulookup_address_idx ulookup_ctrl_idx; omega)]
    unfold encodeReg; rw [if_neg (by unfold ulookup_address_idx; omega)]
  · -- AND ancilla clean
    intro i hi
    rw [hpt (ulookup_and_idx i) (by unfold ulookup_and_idx; omega)]
    simp only [inplaceAccInput]
    rw [if_neg (by unfold ulookup_and_idx; omega)]
    simp only [inplaceWorkInput]
    rw [if_neg (by unfold ulookup_and_idx ulookup_ctrl_idx; omega)]
    unfold encodeReg; rw [if_neg (by unfold ulookup_and_idx; omega)]
  · -- addend-temp clean
    intro i hi
    rw [hpt (tempBase + i) (by omega)]
    simp only [inplaceAccInput]
    rw [if_neg (by omega)]
    simp only [inplaceWorkInput]
    rw [if_neg (by unfold ulookup_ctrl_idx; omega)]
    exact encodeReg_high yBase (numWin * w) y (tempBase + i) (by omega)
  · -- carry clean
    rw [hpt (tempBase + bits) htfit]
    simp only [inplaceAccInput]
    rw [if_neg (by omega)]
    simp only [inplaceWorkInput]
    rw [if_neg (by unfold ulookup_ctrl_idx; omega)]
    exact encodeReg_high yBase (numWin * w) y (tempBase + bits) (by omega)
  · -- multiplicand `y` preserved at `yBase`
    intro i hi
    rw [hpt (yBase + i) (by omega)]
    simp only [inplaceAccInput]
    rw [if_neg (by rcases hYAccDisj with h | h <;> omega)]
    simp only [inplaceWorkInput]
    rw [if_neg (by unfold ulookup_ctrl_idx; omega)]
  · -- accumulator decodes to `z`
    apply decodeReg_eq_mod_of_testBit
    intro i hi
    exact assembleEGid_data w bits accBase _ z i hi

/-! ## §4. The faithful-layout corollaries: both passes. -/

/-- Pass 1 (`b += a·k`): accumulator `b @ 1+2w+bits`, multiplicand `a @ 1+2w`
    (below the accumulator), temp `@ 1+2w+2bits`. -/
theorem xCtrlGid_pass1_RelocStepInv (w bits numWin y z : Nat) (hbits : numWin * w = bits) :
    RelocStepInv w bits numWin y (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) z
      (assembleEGid w bits (1 + 2 * w + bits)
        (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) y).val z) :=
  xCtrlGid_RelocStepInv w bits numWin (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) y z
    hbits (by omega) (by omega) (by omega) (by omega)
    (by unfold cosetDim; omega) (by unfold cosetDim; omega) (Or.inl (by omega))

/-- Pass 2 (`a -= b·kInv`): accumulator `a @ 1+2w`, multiplicand `b @ 1+2w+bits` (the
    GAP, ABOVE the accumulator — `hYAccDisj` right disjunct), temp `@ 1+2w+2bits`. -/
theorem xCtrlGid_pass2_RelocStepInv (w bits numWin y z : Nat) (hbits : numWin * w = bits) :
    RelocStepInv w bits numWin y (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) z
      (assembleEGid w bits (1 + 2 * w)
        (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) y).val z) :=
  xCtrlGid_RelocStepInv w bits numWin (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) y z
    hbits (by omega) (by omega) (by omega) (by omega)
    (by unfold cosetDim; omega) (by unfold cosetDim; omega) (Or.inr (by omega))

end FormalRV.Shor.GidneyInPlace.InPlaceEgateInput
