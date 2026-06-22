/-
  FormalRV.Shor.GidneyInPlace.InPlaceFoldAction
  ─────────────────────────────────────────────────
  BRICK 5 of the two-register in-place coset-multiplier DYNAMICS transport: the FOLD.
  The WHOLE product-add `gidneyProductAddTOf` (all `numWin` windows), lifted through the
  equiv `eGid` (Bricks 1-4): in the `xCtrlGid` work branch, it advances the RAW
  accumulator branch value `z` to the literal

        z' = (z + ∑ k<numWin, Tfam k (window w y k)) % 2 ^ bits

  with the control/work branch unchanged.  Relocated analog of
  `ReducedLookupCosetShift.reducedWindowedMul_cosetInput` — but at the BRANCH-VALUE
  level (no `cosetState`, no `% N`), purely register arithmetic.

  COMPOSITIONAL, not reverse-engineered from the whole-fold decode.  The fold is an
  INDUCTION over the `gidneyProductAddTOf` foldl (peeled by `List.range_succ` +
  `Gate.applyNat_seq`), whose STEP is the Brick-4 one-step action
  `relocatedProductAddStep_applyNat` (the boolean engine of
  `relocatedStep_perm_through_eGid`).  It does NOT use the whole-fold
  `gidneyProductAddTOf_state`/`_decode`.  The running sum is the EXACT
  `∑ k ∈ Finset.range numWin, Tfam k (window w y k)` (the same `Finset.sum_range`/window
  machinery as `gidneyProductAddTOf_decode`), and the per-step accumulation uses
  `Nat.mod_add_mod` to keep the literal `% 2^bits` form.

  Contents:
   • `gidneyProductAddTOf_applyNat` — THE boolean fold:
       `applyNat (gidneyProductAddTOf … numWin) (inplaceAccInput z)
          = inplaceAccInput ((z + ∑ k<numWin, Tfam k (window w y k)) % 2^bits)`.
   • `gidneyProductAddTOf_perm_through_eGid` — THE eGid statement (the deliverable),
     the single `gateToPerm_funboolNat` lift (mirrors `relocatedStep_perm_through_eGid`),
     with `pass1`/`pass2` corollaries.

  AUDIT (per directive).  Induction over the fold structure (criterion 1).  Step =
  the Brick-4 per-step action `relocatedProductAddStep_applyNat` (criterion 2 — this is
  the boolean engine of `relocatedStep_perm_through_eGid`; the eGid-level statement is
  the single lift, NOT the whole-fold decode).  Running sum exposed as
  `∑ Finset.range` (criterion 3).  LITERAL `% 2^bits`, NO `% N` (criteria 4, 5).  No
  coset-state norm bound (criterion 6).  `z` a RAW `Fin (2^bits)` branch index.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceStepAction

namespace FormalRV.Shor.GidneyInPlace.InPlaceFoldAction

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.WindowedArith (window)
open FormalRV.Shor.GidneyInPlace.GatePerm (funboolNat gateToPerm extendBool)
open FormalRV.Shor.GidneyInPlace.CuccaroGatePerm (gateToPerm_funboolNat)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate
open FormalRV.Shor.GidneyInPlace.ProductAddWrapper (gidneyProductAddTOf relocatedProductAddStep)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputGid
open FormalRV.Shor.GidneyInPlace.InPlaceStepAction

/-! ## §1. The boolean fold (induction over the windows, LITERAL `% 2^bits`). -/

/-- **THE BOOLEAN FOLD.**  The whole product-add maps the eGid accumulator input
    `inplaceAccInput z` to `inplaceAccInput ((z + ∑ k<numWin, Tfam k (window w y k)) %
    2^bits)`.  Induction over the `gidneyProductAddTOf` foldl, step =
    `relocatedProductAddStep_applyNat` (Brick 4); `Nat.mod_add_mod` keeps the literal
    `% 2^bits` across windows. -/
theorem gidneyProductAddTOf_applyNat (w bits numWin : Nat) (Tfam : Nat → Nat → Nat)
    (y accBase tempBase yBase z : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hz : z < 2 ^ bits)
    (hv : accBase + bits ≤ tempBase) (hacc : 2 * w < accBase) (hyy : 2 * w < yBase)
    (hytemp : yBase + bits ≤ tempBase)
    (hYAccDisj : yBase + bits ≤ accBase ∨ accBase + bits ≤ yBase)
    (hpresY : ∀ (f' : Nat → Bool) i, i < numWin * w →
      Gate.applyNat (FormalRV.BQAlgo.relocatedAdderCircuit accBase tempBase bits) f' (yBase + i)
        = f' (yBase + i))
    (hcover : ∀ q, accBase ≤ q → q < tempBase + bits + 1 →
      (∃ i, i < bits ∧ q = accBase + i) ∨ (∃ i, i < bits ∧ q = tempBase + i)
        ∨ q = tempBase + bits ∨ (∃ i, i < numWin * w ∧ q = yBase + i)) :
    Gate.applyNat (gidneyProductAddTOf w bits Tfam accBase tempBase yBase numWin)
        (inplaceAccInput w bits numWin accBase yBase z y)
      = inplaceAccInput w bits numWin accBase yBase
          ((z + ∑ k ∈ Finset.range numWin, Tfam k (window w y k)) % 2 ^ bits) y := by
  suffices haux : ∀ t, t ≤ numWin →
      Gate.applyNat (gidneyProductAddTOf w bits Tfam accBase tempBase yBase t)
          (inplaceAccInput w bits numWin accBase yBase z y)
        = inplaceAccInput w bits numWin accBase yBase
            ((z + ∑ k ∈ Finset.range t, Tfam k (window w y k)) % 2 ^ bits) y by
    exact haux numWin (le_refl _)
  intro t
  induction t with
  | zero =>
      intro _
      rw [show gidneyProductAddTOf w bits Tfam accBase tempBase yBase 0 = Gate.I from rfl,
          Gate.applyNat_I, Finset.sum_range_zero, Nat.add_zero, Nat.mod_eq_of_lt hz]
  | succ m ih =>
      intro hk
      have hmwin : m < numWin := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hk
      have hsplit : gidneyProductAddTOf w bits Tfam accBase tempBase yBase (m + 1)
          = Gate.seq (gidneyProductAddTOf w bits Tfam accBase tempBase yBase m)
              (relocatedProductAddStep w bits (Tfam m) accBase tempBase yBase m) := by
        unfold gidneyProductAddTOf
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hsplit, Gate.applyNat_seq, ih (by omega),
          relocatedProductAddStep_applyNat w bits numWin (Tfam m) y accBase tempBase yBase m
            ((z + ∑ k ∈ Finset.range m, Tfam k (window w y k)) % 2 ^ bits)
            hw hbits hmwin hv hacc hyy hytemp hYAccDisj hpresY hcover]
      have hval : ((z + ∑ k ∈ Finset.range m, Tfam k (window w y k)) % 2 ^ bits
            + Tfam m (window w y m)) % 2 ^ bits
          = (z + ∑ k ∈ Finset.range (m + 1), Tfam k (window w y k)) % 2 ^ bits := by
        rw [Nat.mod_add_mod, Finset.sum_range_succ]
        congr 1; omega
      rw [hval]

/-! ## §2. The eGid fold statement (the deliverable). -/

/-- **BRICK 5 — the product-add fold through `eGid`.**  In the `xCtrlGid` work branch,
    the whole `gidneyProductAddTOf` advances the RAW accumulator branch value `z` to
    `(z + ∑ k<numWin, Tfam k (window w y k)) % 2^bits` — same work/control branch.  The
    single `gateToPerm_funboolNat` lift of the boolean fold (mirrors
    `relocatedStep_perm_through_eGid`).  `pass1`/`pass2` supply `hwt`/`hpresY`/`hcover`. -/
theorem gidneyProductAddTOf_perm_through_eGid (w bits numWin : Nat) (Tfam : Nat → Nat → Nat)
    (accBase tempBase yBase y z : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hz : z < 2 ^ bits)
    (hz2 : (z + ∑ k ∈ Finset.range numWin, Tfam k (window w y k)) % 2 ^ bits < 2 ^ bits)
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
    (hwt : Gate.WellTyped (cosetDim w bits)
      (gidneyProductAddTOf w bits Tfam accBase tempBase yBase numWin)) :
    gateToPerm (gidneyProductAddTOf w bits Tfam accBase tempBase yBase numWin) (cosetDim w bits) hwt
        (eGid w bits accBase haccfit (xCtrlGid w bits numWin accBase yBase y, ⟨z, hz⟩))
      = eGid w bits accBase haccfit
          (xCtrlGid w bits numWin accBase yBase y,
            ⟨(z + ∑ k ∈ Finset.range numWin, Tfam k (window w y k)) % 2 ^ bits, hz2⟩) := by
  rw [eGid_apply w bits numWin accBase yBase y z hz haccfit,
      eGid_apply w bits numWin accBase yBase y _ hz2 haccfit,
      gateToPerm_funboolNat]
  congr 1
  funext i
  show Gate.applyNat (gidneyProductAddTOf w bits Tfam accBase tempBase yBase numWin)
        (extendBool (cosetDim w bits)
          (fun i => inplaceAccInput w bits numWin accBase yBase z y i.val)) i.val
    = inplaceAccInput w bits numWin accBase yBase
        ((z + ∑ k ∈ Finset.range numWin, Tfam k (window w y k)) % 2 ^ bits) y i.val
  rw [extendBool_inplaceAccInput w bits numWin accBase tempBase yBase z y hbits hyy hytemp haccfit htfit,
      gidneyProductAddTOf_applyNat w bits numWin Tfam y accBase tempBase yBase z
        hw hbits hz hv hacc hyy hytemp hYAccDisj hpresY hcover]

/-! ## §3. The faithful-layout corollaries. -/

/-- Pass 1 (`b += a·k`): accumulator `b @ 1+2w+bits`, multiplicand `a @ 1+2w`. -/
theorem gidneyProductAddTOf_pass1_perm_through_eGid (w bits numWin : Nat) (Tfam : Nat → Nat → Nat)
    (y z : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (hz : z < 2 ^ bits)
    (hz2 : (z + ∑ k ∈ Finset.range numWin, Tfam k (window w y k)) % 2 ^ bits < 2 ^ bits)
    (hwt : Gate.WellTyped (cosetDim w bits)
      (gidneyProductAddTOf w bits Tfam (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin)) :
    gateToPerm (gidneyProductAddTOf w bits Tfam (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin)
        (cosetDim w bits) hwt
        (eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) y, ⟨z, hz⟩))
      = eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) y,
            ⟨(z + ∑ k ∈ Finset.range numWin, Tfam k (window w y k)) % 2 ^ bits, hz2⟩) :=
  gidneyProductAddTOf_perm_through_eGid w bits numWin Tfam (1 + 2 * w + bits) (1 + 2 * w + 2 * bits)
    (1 + 2 * w) y z hw hbits hz hz2 (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
    (by unfold cosetDim; omega) (by unfold cosetDim; omega)
    (fun f' i hi => relocated_pass1_multiplicand_preserved w bits f' i (by omega))
    (fun q hq1 hq2 => by
      rcases Nat.lt_or_ge q (1 + 2 * w + 2 * bits) with h | h
      · exact Or.inl ⟨q - (1 + 2 * w + bits), by omega, by omega⟩
      rcases Nat.lt_or_ge q (1 + 2 * w + 3 * bits) with h2 | h2
      · exact Or.inr (Or.inl ⟨q - (1 + 2 * w + 2 * bits), by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl (by omega))))
    hwt

/-- Pass 2 (`a -= b·kInv`): accumulator `a @ 1+2w`, multiplicand `b @ 1+2w+bits` (the gap). -/
theorem gidneyProductAddTOf_pass2_perm_through_eGid (w bits numWin : Nat) (Tfam : Nat → Nat → Nat)
    (y z : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (hz : z < 2 ^ bits)
    (hz2 : (z + ∑ k ∈ Finset.range numWin, Tfam k (window w y k)) % 2 ^ bits < 2 ^ bits)
    (hwt : Gate.WellTyped (cosetDim w bits)
      (gidneyProductAddTOf w bits Tfam (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin)) :
    gateToPerm (gidneyProductAddTOf w bits Tfam (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin)
        (cosetDim w bits) hwt
        (eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) y, ⟨z, hz⟩))
      = eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) y,
            ⟨(z + ∑ k ∈ Finset.range numWin, Tfam k (window w y k)) % 2 ^ bits, hz2⟩) :=
  gidneyProductAddTOf_perm_through_eGid w bits numWin Tfam (1 + 2 * w) (1 + 2 * w + 2 * bits)
    (1 + 2 * w + bits) y z hw hbits hz hz2 (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
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

end FormalRV.Shor.GidneyInPlace.InPlaceFoldAction
