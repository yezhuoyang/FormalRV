/-
  FormalRV.Shor.GidneyInPlace.InPlaceComposedBranch
  ───────────────────────────────────────────────────
  PACKAGING checkpoint 2b: the COMPOSED-gate per-branch action of
  `gidneyInPlaceWithSwap = gidneyTwoRegInPlaceCosetMul ; swapAB`.

  The faithful multiplier sends the input eGid branch `(a = ja, b = jb)` to the pass-2
  factorization branch `(a = modSub …, b = jb')` (Brick 9, `gidneyTwoRegInPlace_branch_action`):
  pre-swap PHYSICAL blocks are  a = modSub (cleared),  b = jb' (product).
  The final `swapAB` then EXCHANGES the two physical blocks, so the composed gate lands at:

      a' = jb'                       -- PRODUCT branch  (physical a-block, the output)
      b' = modSub bits ja Sinv       -- CLEARED branch  (physical b-block, the ancilla)

  This fixes the post-swap physical convention: physical a holds the product, physical b is
  cleared.  Raw `Fin (2^bits)` branch indices; NO bad set, NO mass.

  Method: `gateToPerm_seq` decomposes the composed permutation; `gidneyTwoRegInPlace_branch_action`
  gives the pre-swap branch; a dedicated `swapAB` BRANCH action (`swapAB_branch_action`, NOT the
  state-level `swapAB_cosetInputTwoReg`) carries the eGid@aBase branch to the value-swapped branch,
  via `eGid_apply` + `gateToPerm_funboolNat` + the physical block-value swap on `inplaceAccInput`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceComposedGate
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceBranchAction
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceEgidRefactor

namespace FormalRV.Shor.GidneyInPlace.InPlaceComposedBranch

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit (encodeReg)
open FormalRV.Shor.WindowedArith (window)
open FormalRV.Shor.GidneyInPlace.GatePerm
  (gateToPerm funboolNat funboolEquiv extendBool applyFin funboolNat_injective)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.CuccaroGatePerm (gateToPerm_funboolNat)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate (eGid pass1_accfit pass2_accfit)
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput (inplaceAccInput inplaceWorkInput xCtrlGid)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputGid (eGid_apply)
open FormalRV.Shor.GidneyInPlace.InPlaceBranchAction
  (gateToPerm_seq modSub gidneyTwoRegInPlace_branch_action)
open FormalRV.Shor.GidneyInPlace.GidneyTwoRegInPlace
  (gidneyTwoRegInPlaceCosetMul gidneyTwoRegInPlaceCosetMul_wellTyped)
open FormalRV.Shor.GidneyInPlace.InPlaceSwapBlocks
  (swapAB swapAB_wellTyped swapAB_posA swapAB_posB swapAB_frameOff)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate
  (gidneyInPlaceWithSwap gidneyInPlaceWithSwap_wellTyped gidneyInPlaceWithSwap_unfold)

/-! ## §1. The physical block-value swap on `inplaceAccInput`. -/

/-- **`extendBool` collapse.**  The `cosetDim`-restricted `inplaceAccInput` extends back to
    the full `inplaceAccInput` (which is already `false` above `cosetDim`: the acc block and
    multiplicand window both lie inside `[0, cosetDim)`). -/
theorem extendBool_inplaceAccInput (w bits numWin z y : Nat) (hbits : numWin * w = bits) :
    extendBool (cosetDim w bits)
        (fun p : Fin (cosetDim w bits) =>
          inplaceAccInput w bits numWin (1 + 2 * w) (1 + 2 * w + bits) z y p.val)
      = inplaceAccInput w bits numWin (1 + 2 * w) (1 + 2 * w + bits) z y := by
  funext k
  unfold extendBool
  by_cases hk : k < cosetDim w bits
  · rw [dif_pos hk]
  · rw [dif_neg hk]
    have hkge : cosetDim w bits ≤ k := Nat.le_of_not_lt hk
    unfold cosetDim at hkge
    simp only [inplaceAccInput, inplaceWorkInput, encodeReg, ulookup_ctrl_idx]
    rw [hbits]
    split_ifs <;> first | rfl | omega

/-- **The physical block-value swap.**  Applying `swapAB` to the config with a-block `= z`
    and b-block `= y` produces the config with a-block `= y` and b-block `= z` — the swap
    EXCHANGES the two block values (in the aBase factorization `accBase = 1+2w`,
    `yBase = 1+2w+bits`, the acc value and the multiplicand value trade places). -/
theorem applyNat_swapAB_inplaceAccInput (w bits numWin z y : Nat) (hbits : numWin * w = bits) :
    Gate.applyNat (swapAB w bits) (inplaceAccInput w bits numWin (1 + 2 * w) (1 + 2 * w + bits) z y)
      = inplaceAccInput w bits numWin (1 + 2 * w) (1 + 2 * w + bits) y z := by
  -- literal-position variants of the swap action (defeq to `aBase`/`bBase` forms)
  have posA : ∀ (g : Nat → Bool) (j : Nat), j < bits →
      Gate.applyNat (swapAB w bits) g (1 + 2 * w + j) = g (1 + 2 * w + bits + j) :=
    fun g j hj => swapAB_posA w bits g j hj
  have posB : ∀ (g : Nat → Bool) (j : Nat), j < bits →
      Gate.applyNat (swapAB w bits) g (1 + 2 * w + bits + j) = g (1 + 2 * w + j) :=
    fun g j hj => swapAB_posB w bits g j hj
  have frameOff : ∀ (g : Nat → Bool) (q : Nat),
      ¬ (1 + 2 * w ≤ q ∧ q < 1 + 2 * w + bits) →
      ¬ (1 + 2 * w + bits ≤ q ∧ q < 1 + 2 * w + bits + bits) →
      Gate.applyNat (swapAB w bits) g q = g q :=
    fun g q ha hb => swapAB_frameOff w bits g q ha hb
  funext p
  by_cases hpa : 1 + 2 * w ≤ p ∧ p < 1 + 2 * w + bits
  · -- a-block position
    have hj : p - (1 + 2 * w) < bits := by omega
    have hpeq : p = (1 + 2 * w) + (p - (1 + 2 * w)) := by omega
    rw [hpeq, posA _ (p - (1 + 2 * w)) hj]
    simp only [inplaceAccInput, inplaceWorkInput, encodeReg, ulookup_ctrl_idx]
    rw [hbits]
    split_ifs <;> first | rfl | omega | (congr 1; omega)
  · by_cases hpb : 1 + 2 * w + bits ≤ p ∧ p < 1 + 2 * w + bits + bits
    · -- b-block position
      have hj : p - (1 + 2 * w + bits) < bits := by omega
      have hpeq : p = (1 + 2 * w + bits) + (p - (1 + 2 * w + bits)) := by omega
      rw [hpeq, posB _ (p - (1 + 2 * w + bits)) hj]
      simp only [inplaceAccInput, inplaceWorkInput, encodeReg, ulookup_ctrl_idx]
      rw [hbits]
      split_ifs <;> first | rfl | omega | (congr 1; omega)
    · -- off both blocks
      rw [frameOff _ p hpa hpb]
      simp only [inplaceAccInput, inplaceWorkInput, encodeReg, ulookup_ctrl_idx]
      rw [hbits]
      split_ifs <;> rfl

/-! ## §2. The `swapAB` branch action on an eGid@aBase branch. -/

/-- **`swapAB` BRANCH action.**  `swapAB` carries the eGid@aBase branch with multiplicand
    `y` and data `z` to the one with multiplicand `z` and data `y` — i.e. it exchanges the
    two physical block values, expressed in the SAME pass-2 (aBase) factorization. -/
theorem swapAB_branch_action (w bits numWin y z : Nat) (hbits : numWin * w = bits)
    (hy : y < 2 ^ bits) (hz : z < 2 ^ bits) :
    gateToPerm (swapAB w bits) (cosetDim w bits) (swapAB_wellTyped w bits)
        (eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) y, ⟨z, hz⟩))
      = eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) z, ⟨y, hy⟩) := by
  rw [eGid_apply w bits numWin (1 + 2 * w) (1 + 2 * w + bits) y z hz (pass2_accfit w bits),
      gateToPerm_funboolNat (swapAB w bits) (cosetDim w bits) (swapAB_wellTyped w bits),
      eGid_apply w bits numWin (1 + 2 * w) (1 + 2 * w + bits) z y hy (pass2_accfit w bits)]
  apply congrArg (funboolNat (cosetDim w bits))
  funext p
  show Gate.applyNat (swapAB w bits)
      (extendBool (cosetDim w bits)
        (fun q : Fin (cosetDim w bits) =>
          inplaceAccInput w bits numWin (1 + 2 * w) (1 + 2 * w + bits) z y q.val)) p.val
    = inplaceAccInput w bits numWin (1 + 2 * w) (1 + 2 * w + bits) y z p.val
  rw [extendBool_inplaceAccInput w bits numWin z y hbits,
      applyNat_swapAB_inplaceAccInput w bits numWin z y hbits]

/-! ## §3. The composed-gate branch action (multiply ; swap). -/

/-- **THE COMPOSED-GATE BRANCH ACTION.**  `gidneyInPlaceWithSwap` sends the input eGid
    branch `(a = ja, b = jb)` to the eGid@aBase branch with PHYSICAL a-block `= jb'` (the
    PRODUCT) and physical b-block `= modSub bits ja Sinv` (the CLEARED ancilla), where
    `jb' = (jb + ∑ₖ TfamK k (window w ja k)) % 2^bits` and
    `Sinv = ∑ₖ TfamKinv k (window w jb' k)`.  Post-swap physical convention:
    physical a = product branch, physical b = cleared branch.  Raw `Fin (2^bits)` indices. -/
theorem gidneyInPlaceWithSwap_branch_action (w bits numWin : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (ja jb : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (hja : ja < 2 ^ bits) (hjb : jb < 2 ^ bits) :
    gateToPerm (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin) (cosetDim w bits)
        (gidneyInPlaceWithSwap_wellTyped w bits TfamK TfamKinv numWin hw hbits)
        (eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja, ⟨jb, hjb⟩))
      = eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits)
              (modSub bits ja (∑ k ∈ Finset.range numWin, TfamKinv k
                (window w ((jb + ∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) % 2 ^ bits) k))),
            ⟨(jb + ∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) % 2 ^ bits,
              Nat.mod_lt _ (by positivity)⟩) := by
  have hjb' : (jb + ∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) % 2 ^ bits < 2 ^ bits :=
    Nat.mod_lt _ (by positivity)
  have hmodSub : modSub bits ja (∑ k ∈ Finset.range numWin, TfamKinv k
      (window w ((jb + ∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) % 2 ^ bits) k))
      < 2 ^ bits := Nat.mod_lt _ (by positivity)
  -- decompose the composed permutation (`gateToPerm_seq`, applied at the defeq `Gate.seq` form)
  have hseq : gateToPerm (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin) (cosetDim w bits)
        (gidneyInPlaceWithSwap_wellTyped w bits TfamK TfamKinv numWin hw hbits)
        (eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja, ⟨jb, hjb⟩))
      = gateToPerm (swapAB w bits) (cosetDim w bits) (swapAB_wellTyped w bits)
          (gateToPerm (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) (cosetDim w bits)
            (gidneyTwoRegInPlaceCosetMul_wellTyped w bits TfamK TfamKinv numWin hw hbits)
            (eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
              (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja, ⟨jb, hjb⟩))) :=
    gateToPerm_seq (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) (swapAB w bits)
      (cosetDim w bits) (gidneyTwoRegInPlaceCosetMul_wellTyped w bits TfamK TfamKinv numWin hw hbits)
      (swapAB_wellTyped w bits)
      (gidneyInPlaceWithSwap_wellTyped w bits TfamK TfamKinv numWin hw hbits) _
  rw [hseq,
      gidneyTwoRegInPlace_branch_action w bits numWin TfamK TfamKinv ja jb hw hbits hja hjb
        (gidneyTwoRegInPlaceCosetMul_wellTyped w bits TfamK TfamKinv numWin hw hbits)]
  exact swapAB_branch_action w bits numWin
    ((jb + ∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) % 2 ^ bits)
    (modSub bits ja (∑ k ∈ Finset.range numWin, TfamKinv k
      (window w ((jb + ∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) % 2 ^ bits) k)))
    hbits hjb' hmodSub
