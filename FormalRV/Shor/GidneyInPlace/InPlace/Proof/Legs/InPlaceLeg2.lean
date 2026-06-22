/-
  FormalRV.Shor.GidneyInPlace.InPlaceLeg2
  ───────────────────────────────────────────────
  LEG 2 of the two-register in-place coset-multiplier norm bound (Architecture B):
  the FORWARD pass-2 deviation
    normSqDist (uc_eval(pass2) · cosetInputVec 0 ((k·x)%N)) (cosetInputVec x ((k·x)%N))
      ≤ numWin·(2/2^cm).

  The MIRROR of Leg 1 (`InPlaceLeg1`) under the a↔b register swap: pass-2 (`a += b·kInv`)
  acts, in the aBase factorization (data = a, control = b + scratch), as the windowed
  product-add ON THE a-REGISTER, per b-control-branch.  Multiplier `kInv`; the b-register
  (multiplicand) ranges over `cosetWindow ((k·x)%N)`; the target a-residue is `x` because
  `kInv·((k·x)%N) ≡ x (mod N)` (`revCanonical_eq`, the explicit audit point).

  Reuses Leg 1's GENERIC lemmas verbatim: `cosetState_modSub_shift`,
  `cosetInputTwoReg_support_nonzero`, `leg1_actualAcc_eq` (generic in the multiplier `K`).
  The pass-specific lemmas are mirrored with `bBase↔aBase`, `betaB↔betaA`,
  `ctrlFunB↔ctrlFunA`, `passB↔passA`, B5-pass1↔B5-pass2.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceLeg1

namespace FormalRV.Shor.GidneyInPlace.InPlaceLeg2

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer (normSqDist)
open FormalRV.Shor.WindowedArith (window tableValue)
open FormalRV.Shor.GidneyInPlace.ApproxOp (cosetState permState)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow cosetWindow_card)
open FormalRV.Shor.GidneyInPlace.InPlaceBranchAction (modSub modSub_add)
open FormalRV.Shor.GidneyInPlace.BranchFactor (branchOfE)
open FormalRV.Shor.GidneyInPlace.GatePerm (gateToPerm extendBool funboolNat)
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_eq_permState)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate
  (eGid pass2_accfit assembleEGid assembleEGid_data assembleEGid_comp compIdxGid compIdxGid_lt)
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput
  (xCtrlGid assembleEGid_xCtrlGid inplaceAccInput inplaceWorkInput)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputGid (eGid_apply)
open FormalRV.Shor.GidneyInPlace.ProductAddWrapper (gidneyProductAddTOf)
open FormalRV.Shor.GidneyInPlace.InPlaceFoldAction (gidneyProductAddTOf_pass2_perm_through_eGid)
open FormalRV.BQAlgo (ulookup_ctrl_idx)
open FormalRV.Shor.WindowedCircuit (decodeReg_lt_two_pow)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg
  (cosetInputTwoReg betaA branchOfE_cosetInputTwoReg_passA bBase aBase ctrlFunA scratchClean)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.CosetMul (actualAcc runningSum)
open FormalRV.Shor.GidneyInPlace.CosetTableSum (cosetWindowConst)
open FormalRV.Shor.GidneyInPlace.InPlaceEndpoint (canonicalSum_eq_runningSum)
open FormalRV.Shor.GidneyInPlace.InPlaceBadSet (revCanonical_eq)
open FormalRV.Shor.GidneyInPlace.CosetDeviationE (cosetOutOfPlace_hfwd_E)
open FormalRV.Shor.GidneyInPlace.InPlaceLeg1
  (cosetState_modSub_shift cosetInputTwoReg_support_nonzero leg1_actualAcc_eq)

/-! ## §1. The residue bridge (the revCanonical audit point). -/

/-- **Residue bridge (the audit point).**  Every active b-branch `jb ∈ cosetWindow ((k·x)%N)`
    has residue `(k·x)%N`, so multiplying by `kInv` targets residue `x` (NOT merely
    `(kInv·jb)%N`): `(kInv·jb)%N = x`, via `revCanonical_eq` (`kInv·k ≡ 1 mod N`, `x < N`). -/
theorem leg2_residue (bits N cm k kInv x jb : Nat) (hN : 0 < N) (hxN : x < N)
    (hkInv : (kInv * k) % N = 1 % N) (hjb : jb < 2 ^ bits)
    (hmem : (⟨jb, hjb⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm ((k * x) % N)) :
    (kInv * jb) % N = x := by
  rw [mem_cosetWindow (2 ^ bits) N cm ((k * x) % N) hN] at hmem
  obtain ⟨p, hp, hval⟩ := hmem
  replace hval : jb = (k * x) % N + p * N := hval
  rw [hval, Nat.mul_add, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
  exact revCanonical_eq N k kInv x hxN hkInv

/-! ## §2. The per-branch pass-2 dynamics lift (mirror of Leg 1's crux). -/

/-- **Pass-2 per-branch dynamics.**  Projected onto the b-control branch `xCtrlGid … jb`
    (aBase factorization, data = a), the gate output `uc_eval(pass2) · cosetInputVec 0 xb`
    is the fresh a-accumulator (`cosetState 0`) shifted by the windowed running sum
    `S = ∑ₖ TfamKinv k (window w jb k)` — i.e. `betaA · cosetState S`.  Mirror of
    `leg1_branchOfE_dynamics` via B5-pass2 + `uc_eval_eq_permState` + the (reused) shift
    identity. -/
theorem leg2_branchOfE_dynamics (w bits numWin N cm : Nat) (TfamKinv : Nat → Nat → Nat)
    (xb jb : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hfit : (∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k)) + (2 ^ cm - 1) * N < 2 ^ bits)
    (hwt : Gate.WellTyped (cosetDim w bits)
      (gidneyProductAddTOf w bits TfamKinv (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin)) :
    branchOfE (eGid w bits (1 + 2 * w) (pass2_accfit w bits))
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (gidneyProductAddTOf w bits TfamKinv (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin))
          * cosetInputVec w bits N cm 0 xb)
        (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb)
      = fun i z => betaA w bits N cm xb (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb).val
          * cosetState (2 ^ bits) N cm (∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k)) i z := by
  have hSlt : (∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k)) < 2 ^ bits := by
    have : (0 : Nat) ≤ (2 ^ cm - 1) * N := Nat.zero_le _
    omega
  funext i z
  have hinv : (gateToPerm (gidneyProductAddTOf w bits TfamKinv
        (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin) (cosetDim w bits) hwt).symm
      (eGid w bits (1 + 2 * w) (pass2_accfit w bits)
        (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb, i))
      = eGid w bits (1 + 2 * w) (pass2_accfit w bits)
        (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb,
          ⟨modSub bits i.val (∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k)),
            Nat.mod_lt _ (by positivity)⟩) := by
    rw [Equiv.symm_apply_eq]
    have hb5 := gidneyProductAddTOf_pass2_perm_through_eGid w bits numWin TfamKinv jb
      (modSub bits i.val (∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k)))
      hw hbits (Nat.mod_lt _ (by positivity))
      (by rw [modSub_add bits i.val _ i.isLt]; exact i.isLt) hwt
    rw [hb5]
    congr 1
    apply congrArg
    apply Fin.ext
    show i.val = (modSub bits i.val (∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k))
        + ∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k)) % 2 ^ bits
    rw [modSub_add bits i.val _ i.isLt]
  show (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
          (gidneyProductAddTOf w bits TfamKinv (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin))
        * cosetInputVec w bits N cm 0 xb)
      (eGid w bits (1 + 2 * w) (pass2_accfit w bits)
        (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb, i)) 0
    = betaA w bits N cm xb (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb).val
        * cosetState (2 ^ bits) N cm (∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k)) i z
  rw [uc_eval_eq_permState (gidneyProductAddTOf w bits TfamKinv
        (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin) (cosetDim w bits) hwt
        (cosetInputVec w bits N cm 0 xb)]
  show cosetInputVec w bits N cm 0 xb
      ((gateToPerm (gidneyProductAddTOf w bits TfamKinv
          (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin) (cosetDim w bits) hwt).symm
        (eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb, i))) 0
    = betaA w bits N cm xb (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb).val
        * cosetState (2 ^ bits) N cm (∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k)) i z
  rw [hinv]
  show branchOfE (eGid w bits (aBase w) (pass2_accfit w bits))
        (cosetInputTwoReg w bits N cm 0 xb)
        (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb)
        ⟨modSub bits i.val (∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k)),
          Nat.mod_lt _ (by positivity)⟩ z
    = betaA w bits N cm xb (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb).val
        * cosetState (2 ^ bits) N cm (∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k)) i z
  rw [branchOfE_cosetInputTwoReg_passA w bits N cm 0 xb
        (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb)]
  show betaA w bits N cm xb (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb).val
        * cosetState (2 ^ bits) N cm 0
          ⟨modSub bits i.val (∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k)),
            Nat.mod_lt _ (by positivity)⟩ z
    = betaA w bits N cm xb (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb).val
        * cosetState (2 ^ bits) N cm (∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k)) i z
  rw [cosetState_modSub_shift bits N cm
        (∑ k ∈ Finset.range numWin, TfamKinv k (window w jb k)) hN hSlt hfit i z]

/-! ## §3. Clean-control roundtrip + xval roundtrip (aBase factorization). -/

/-- Mirror of `clean_ctrl_eq_xCtrlGid` for the aBase factorization: a clean control whose
    b-block decodes to `jb` IS `xCtrlGid aBase bBase jb`. -/
theorem leg2_clean_ctrl (w bits numWin jb : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (ctrl : Fin (2 ^ (cosetDim w bits - bits)))
    (hclean : scratchClean w bits (ctrlFunA w bits ctrl.val))
    (hdec : decodeReg (fun i => bBase w bits + i) bits (ctrlFunA w bits ctrl.val) = jb) :
    ctrl = xCtrlGid w bits numWin (aBase w) (bBase w bits) jb := by
  have hfeq : ∀ p, p < cosetDim w bits →
      ctrlFunA w bits ctrl.val p = inplaceWorkInput numWin w (bBase w bits) jb p := by
    intro p hp
    by_cases hctrl : p = ulookup_ctrl_idx
    · subst hctrl
      rw [hclean.1]
      show true = (if ulookup_ctrl_idx = ulookup_ctrl_idx then true
        else FormalRV.Shor.WindowedCircuit.encodeReg (bBase w bits) (numWin * w) jb ulookup_ctrl_idx)
      rw [if_pos rfl]
    by_cases hb : bBase w bits ≤ p ∧ p < bBase w bits + bits
    · obtain ⟨i, rfl⟩ : ∃ i, p = bBase w bits + i := ⟨p - bBase w bits, by omega⟩
      have hi : i < bits := by omega
      have hbit : ctrlFunA w bits ctrl.val (bBase w bits + i) = jb.testBit i := by
        have h := FormalRV.Shor.WindowedCircuit.decodeReg_testBit (fun i => bBase w bits + i) bits
          (ctrlFunA w bits ctrl.val) i hi
        rw [hdec] at h; exact h.symm
      rw [hbit]
      show jb.testBit i = (if bBase w bits + i = ulookup_ctrl_idx then true
        else FormalRV.Shor.WindowedCircuit.encodeReg (bBase w bits) (numWin * w) jb (bBase w bits + i))
      rw [if_neg (by unfold ulookup_ctrl_idx bBase; omega)]
      show jb.testBit i = (if bBase w bits ≤ bBase w bits + i ∧ bBase w bits + i < bBase w bits + numWin * w
        then jb.testBit (bBase w bits + i - bBase w bits) else false)
      rw [if_pos ⟨by omega, by rw [hbits]; omega⟩, Nat.add_sub_cancel_left]
    by_cases ha : aBase w ≤ p ∧ p < aBase w + bits
    · obtain ⟨i, rfl⟩ : ∃ i, p = aBase w + i := ⟨p - aBase w, by omega⟩
      have hi : i < bits := by omega
      show ctrlFunA w bits ctrl.val (aBase w + i) = inplaceWorkInput numWin w (bBase w bits) jb (aBase w + i)
      rw [show ctrlFunA w bits ctrl.val (aBase w + i)
            = assembleEGid w bits (aBase w) ctrl.val 0 (aBase w + i) from rfl,
          assembleEGid_data w bits (aBase w) ctrl.val 0 i hi, Nat.zero_testBit]
      show false = (if aBase w + i = ulookup_ctrl_idx then true
        else FormalRV.Shor.WindowedCircuit.encodeReg (bBase w bits) (numWin * w) jb (aBase w + i))
      rw [if_neg (by unfold ulookup_ctrl_idx aBase; omega)]
      show false = (if bBase w bits ≤ aBase w + i ∧ aBase w + i < bBase w bits + numWin * w
        then jb.testBit (aBase w + i - bBase w bits) else false)
      rw [if_neg (by unfold bBase aBase; rw [hbits]; omega)]
    · rw [hclean.2 p hp ha hb hctrl]
      show false = (if p = ulookup_ctrl_idx then true
        else FormalRV.Shor.WindowedCircuit.encodeReg (bBase w bits) (numWin * w) jb p)
      rw [if_neg hctrl]
      show false = (if bBase w bits ≤ p ∧ p < bBase w bits + numWin * w then jb.testBit (p - bBase w bits) else false)
      rw [if_neg (by rw [hbits]; exact hb)]
  apply Fin.ext
  show ctrl.val = decodeReg (compIdxGid bits (aBase w)) (cosetDim w bits - bits)
      (inplaceWorkInput numWin w (bBase w bits) jb)
  rw [FormalRV.Shor.WindowedCircuit.decodeReg_eq_mod_of_testBit (compIdxGid bits (aBase w))
        (cosetDim w bits - bits) ctrl.val (inplaceWorkInput numWin w (bBase w bits) jb) (fun j hj => ?_),
      Nat.mod_eq_of_lt ctrl.isLt]
  rw [← hfeq (compIdxGid bits (aBase w) j) (compIdxGid_lt w bits (aBase w) j (pass2_accfit w bits) hj)]
  exact assembleEGid_comp w bits (aBase w) ctrl.val 0 j hj

/-- Mirror of `leg1_xval_roundtrip`: the b-block (multiplicand) decode of `xCtrlGid aBase
    bBase jb` is `jb`. -/
theorem leg2_xval_roundtrip (w bits numWin jb : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hjb : jb < 2 ^ bits) :
    decodeReg (fun i => bBase w bits + i) bits
        (ctrlFunA w bits (xCtrlGid w bits numWin (aBase w) (bBase w bits) jb).val) = jb := by
  rw [FormalRV.Shor.WindowedCircuit.decodeReg_eq_mod_of_testBit (fun i => bBase w bits + i) bits jb _,
      Nat.mod_eq_of_lt hjb]
  intro i hi
  show assembleEGid w bits (aBase w)
      (xCtrlGid w bits numWin (aBase w) (bBase w bits) jb).val 0 (bBase w bits + i) = jb.testBit i
  rw [assembleEGid_xCtrlGid w bits numWin (aBase w) (bBase w bits) jb 0 (bBase w bits + i)
        (pass2_accfit w bits) (by unfold cosetDim bBase; omega)]
  unfold inplaceAccInput inplaceWorkInput FormalRV.Shor.WindowedCircuit.encodeReg
  rw [if_neg (by unfold aBase bBase; omega)]
  rw [if_neg (by show bBase w bits + i ≠ ulookup_ctrl_idx; unfold ulookup_ctrl_idx bBase; omega)]
  rw [if_pos (by unfold bBase; exact ⟨by omega, by rw [hbits]; omega⟩)]
  congr 1
  unfold bBase; omega

/-! ## §4. Preimage-as-eGid-image (aBase factorization). -/

/-- Mirror of `P_as_eGid_image`: a clean index with a-block (acc) decode `z` and b-block
    (mult) decode `jb` IS `eGid aBase (xCtrlGid aBase bBase jb, ⟨z⟩)`. -/
theorem leg2_P_as_eGid_image (w bits numWin jb z : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hz : z < 2 ^ bits) (idx : Fin (2 ^ cosetDim w bits))
    (hclean : scratchClean w bits (nat_to_funbool (cosetDim w bits) idx.val))
    (ha : decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val) = z)
    (hb : decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val) = jb) :
    idx = eGid w bits (aBase w) (pass2_accfit w bits)
        (xCtrlGid w bits numWin (aBase w) (bBase w bits) jb, ⟨z, hz⟩) := by
  rw [eGid_apply w bits numWin (aBase w) (bBase w bits) jb z hz (pass2_accfit w bits)]
  apply Fin.ext
  show idx.val = funbool_to_nat (cosetDim w bits)
      (extendBool (cosetDim w bits)
        (fun p => inplaceAccInput w bits numWin (aBase w) (bBase w bits) z jb p.val))
  rw [← funbool_to_nat_nat_to_funbool (cosetDim w bits) idx.val idx.isLt]
  apply FormalRV.Shor.GidneyInPlace.UCEvalBridge.funbool_to_nat_congr
  intro p hp
  rw [show extendBool (cosetDim w bits)
        (fun p => inplaceAccInput w bits numWin (aBase w) (bBase w bits) z jb p.val) p
      = inplaceAccInput w bits numWin (aBase w) (bBase w bits) z jb p from by
        unfold extendBool; rw [dif_pos hp]]
  by_cases hctrl : p = ulookup_ctrl_idx
  · subst hctrl
    rw [hclean.1]
    show true = inplaceAccInput w bits numWin (aBase w) (bBase w bits) z jb ulookup_ctrl_idx
    unfold inplaceAccInput inplaceWorkInput
    rw [if_neg (by unfold ulookup_ctrl_idx aBase; omega), if_pos rfl]
  by_cases ha' : aBase w ≤ p ∧ p < aBase w + bits
  · obtain ⟨i, rfl⟩ : ∃ i, p = aBase w + i := ⟨p - aBase w, by omega⟩
    have hi : i < bits := by omega
    have hbit : nat_to_funbool (cosetDim w bits) idx.val (aBase w + i) = z.testBit i := by
      have h := FormalRV.Shor.WindowedCircuit.decodeReg_testBit (fun i => aBase w + i) bits
        (nat_to_funbool (cosetDim w bits) idx.val) i hi
      rw [ha] at h; exact h.symm
    rw [hbit]
    show z.testBit i = inplaceAccInput w bits numWin (aBase w) (bBase w bits) z jb (aBase w + i)
    unfold inplaceAccInput
    rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
  by_cases hb' : bBase w bits ≤ p ∧ p < bBase w bits + bits
  · obtain ⟨i, rfl⟩ : ∃ i, p = bBase w bits + i := ⟨p - bBase w bits, by omega⟩
    have hi : i < bits := by omega
    have hbit : nat_to_funbool (cosetDim w bits) idx.val (bBase w bits + i) = jb.testBit i := by
      have h := FormalRV.Shor.WindowedCircuit.decodeReg_testBit (fun i => bBase w bits + i) bits
        (nat_to_funbool (cosetDim w bits) idx.val) i hi
      rw [hb] at h; exact h.symm
    rw [hbit]
    show jb.testBit i = inplaceAccInput w bits numWin (aBase w) (bBase w bits) z jb (bBase w bits + i)
    unfold inplaceAccInput inplaceWorkInput FormalRV.Shor.WindowedCircuit.encodeReg
    rw [if_neg (by unfold aBase bBase; omega), if_neg (by unfold ulookup_ctrl_idx bBase; omega)]
    show jb.testBit i = (if bBase w bits ≤ bBase w bits + i ∧ bBase w bits + i < bBase w bits + numWin * w
      then jb.testBit (bBase w bits + i - bBase w bits) else false)
    rw [if_pos ⟨by omega, by rw [hbits]; omega⟩, Nat.add_sub_cancel_left]
  · rw [hclean.2 p hp ha' hb' hctrl]
    show false = inplaceAccInput w bits numWin (aBase w) (bBase w bits) z jb p
    unfold inplaceAccInput inplaceWorkInput FormalRV.Shor.WindowedCircuit.encodeReg
    rw [if_neg ha', if_neg hctrl]
    show false = (if bBase w bits ≤ p ∧ p < bBase w bits + numWin * w then jb.testBit (p - bBase w bits) else false)
    rw [if_neg (by rw [hbits]; exact hb')]

/-! ## §5. The idle-branch (hzero) support lemma (aBase factorization). -/

/-- Mirror of `leg1_hzero`: off the active b-window image, both `uc_eval(pass2)·cosetInputVec
    0 xb` and `cosetInputVec x xb` project (via `branchOfE` over the aBase factorization) to
    the ZERO substate.  Actual side: contrapositive via clean preimage (`P_as_eGid_image` +
    B5-pass2); ideal side: `betaA = 0` off active (`leg2_clean_ctrl`).  `a = acc ∈
    cosetWindow 0` arbitrary, `b ∈ cosetWindow xb`. -/
theorem leg2_hzero (w bits numWin N cm x xb : Nat) (TfamKinv : Nat → Nat → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hwt : Gate.WellTyped (cosetDim w bits)
      (gidneyProductAddTOf w bits TfamKinv (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin))
    (ctrl : Fin (2 ^ (cosetDim w bits - bits)))
    (hctrl : ctrl ∉ (cosetWindow (2 ^ bits) N cm xb).image
        (fun jb : Fin (2 ^ bits) => xCtrlGid w bits numWin (aBase w) (bBase w bits) jb.val)) :
    branchOfE (eGid w bits (aBase w) (pass2_accfit w bits))
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (gidneyProductAddTOf w bits TfamKinv (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin))
          * cosetInputVec w bits N cm 0 xb) ctrl
      = branchOfE (eGid w bits (aBase w) (pass2_accfit w bits))
          (cosetInputVec w bits N cm x xb) ctrl := by
  have hact : branchOfE (eGid w bits (aBase w) (pass2_accfit w bits))
      (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
          (gidneyProductAddTOf w bits TfamKinv (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin))
        * cosetInputVec w bits N cm 0 xb) ctrl = (fun _ _ => 0) := by
    funext i z
    show (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (gidneyProductAddTOf w bits TfamKinv (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin))
        * cosetInputVec w bits N cm 0 xb)
        (eGid w bits (aBase w) (pass2_accfit w bits) (ctrl, i)) 0 = 0
    rw [uc_eval_eq_permState (gidneyProductAddTOf w bits TfamKinv
          (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin) (cosetDim w bits) hwt
          (cosetInputVec w bits N cm 0 xb)]
    show cosetInputVec w bits N cm 0 xb
        ((gateToPerm (gidneyProductAddTOf w bits TfamKinv
            (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin) (cosetDim w bits) hwt).symm
          (eGid w bits (aBase w) (pass2_accfit w bits) (ctrl, i))) 0 = 0
    by_contra hne
    apply hctrl
    set Q := (gateToPerm (gidneyProductAddTOf w bits TfamKinv
        (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin) (cosetDim w bits) hwt).symm
        (eGid w bits (aBase w) (pass2_accfit w bits) (ctrl, i)) with hQ
    obtain ⟨hclean, _ha_win, hjb_win⟩ := cosetInputTwoReg_support_nonzero w bits N cm 0 xb Q 0 hne
    have hzlt : decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) Q.val)
        < 2 ^ bits := decodeReg_lt_two_pow _ _ _
    have hQeq : Q = eGid w bits (aBase w) (pass2_accfit w bits)
        (xCtrlGid w bits numWin (aBase w) (bBase w bits)
            (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) Q.val)),
          ⟨decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) Q.val), hzlt⟩) :=
      leg2_P_as_eGid_image w bits numWin _ _ hw hbits hzlt Q hclean rfl rfl
    have hσQ : gateToPerm (gidneyProductAddTOf w bits TfamKinv
        (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin) (cosetDim w bits) hwt Q
        = eGid w bits (aBase w) (pass2_accfit w bits) (ctrl, i) := by
      rw [hQ]; exact Equiv.apply_symm_apply _ _
    rw [hQeq] at hσQ
    simp only [aBase, bBase] at hσQ
    rw [gidneyProductAddTOf_pass2_perm_through_eGid w bits numWin TfamKinv
          (decodeReg (fun i => 1 + 2 * w + bits + i) bits (nat_to_funbool (cosetDim w bits) Q.val))
          (decodeReg (fun i => 1 + 2 * w + i) bits (nat_to_funbool (cosetDim w bits) Q.val))
          hw hbits (decodeReg_lt_two_pow _ _ _) (Nat.mod_lt _ (by positivity)) hwt] at hσQ
    rw [Finset.mem_image]
    refine ⟨⟨decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) Q.val),
        decodeReg_lt_two_pow _ _ _⟩, hjb_win, ?_⟩
    exact congrArg Prod.fst
      ((eGid w bits (aBase w) (pass2_accfit w bits)).injective hσQ)
  have hidl : branchOfE (eGid w bits (aBase w) (pass2_accfit w bits))
      (cosetInputVec w bits N cm x xb) ctrl = (fun _ _ => 0) := by
    show branchOfE (eGid w bits (aBase w) (pass2_accfit w bits))
        (cosetInputTwoReg w bits N cm x xb) ctrl = (fun _ _ => 0)
    rw [branchOfE_cosetInputTwoReg_passA w bits N cm x xb ctrl]
    have hbeta : betaA w bits N cm xb ctrl.val = 0 := by
      by_contra hbne
      apply hctrl
      have hsc : scratchClean w bits (ctrlFunA w bits ctrl.val) := by
        by_contra hsc; apply hbne; unfold betaA; rw [if_neg hsc]
      have hmem : (⟨decodeReg (fun i => bBase w bits + i) bits (ctrlFunA w bits ctrl.val),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xb := by
        by_contra hm; apply hbne; unfold betaA; rw [if_pos hsc, if_neg hm]
      rw [Finset.mem_image]
      exact ⟨⟨decodeReg (fun i => bBase w bits + i) bits (ctrlFunA w bits ctrl.val),
          decodeReg_lt_two_pow _ _ _⟩, hmem,
        (leg2_clean_ctrl w bits numWin _ hw hbits ctrl hsc rfl).symm⟩
    rw [hbeta]; funext i z; simp
  rw [hact, hidl]

/-! ## §6. The β-weight normalization (betaA, b-window) + LEG 2. -/

set_option maxHeartbeats 800000 in
/-- Mirror of `leg1_hweight`: the betaA β-weights over the active b-control window sum `≤ 1`. -/
theorem leg2_hweight (w bits numWin N cm xb : Nat) (hN : 0 < N)
    (hfit : xb + (2 ^ cm - 1) * N < 2 ^ bits) :
    ∑ ctrl ∈ (cosetWindow (2 ^ bits) N cm xb).image
        (fun jb : Fin (2 ^ bits) => xCtrlGid w bits numWin (aBase w) (bBase w bits) jb.val),
      Complex.normSq (betaA w bits N cm xb ctrl.val) ≤ 1 := by
  classical
  have hc : Complex.normSq ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) = 1 / 2 ^ cm := by
    rw [Complex.normSq_ofReal, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by positivity)]
  have h0 : Complex.normSq (0 : ℂ) ≤ 1 / 2 ^ cm := by rw [Complex.normSq_zero]; positivity
  have hbound : ∀ ctrl : Fin (2 ^ (cosetDim w bits - bits)),
      Complex.normSq (betaA w bits N cm xb ctrl.val) ≤ 1 / 2 ^ cm := by
    intro ctrl
    unfold betaA
    by_cases hA : scratchClean w bits (ctrlFunA w bits ctrl.val)
    · rw [if_pos hA]
      by_cases hB : (⟨decodeReg (fun i => bBase w bits + i) bits (ctrlFunA w bits ctrl.val),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xb
      · rw [if_pos hB]; exact le_of_eq hc
      · rw [if_neg hB]; exact h0
    · rw [if_neg hA]; exact h0
  have hcard : ((cosetWindow (2 ^ bits) N cm xb).image
      (fun jb : Fin (2 ^ bits) => xCtrlGid w bits numWin (aBase w) (bBase w bits) jb.val)).card
      ≤ 2 ^ cm :=
    le_trans Finset.card_image_le (le_of_eq (cosetWindow_card (2 ^ bits) N cm xb hN hfit))
  refine le_trans (Finset.sum_le_card_nsmul _ _ (1 / 2 ^ cm : ℝ) (fun ctrl _ => hbound ctrl)) ?_
  rw [nsmul_eq_mul, mul_one_div, div_le_one (by positivity)]
  exact_mod_cast hcard

/-- **LEG 2 (the forward pass-2 deviation).**  `pass2` (`a += b·kInv`), applied to
    `cosetInputVec 0 ((k·x)%N)` (a = cosetState 0, b = cosetState ((k·x)%N)), is within
    `numWin·(2/2^cm)` of `cosetInputVec x ((k·x)%N)` (a becomes cosetState x — because
    `kInv·((k·x)%N) ≡ x` by `revCanonical_eq` — b stays cosetState ((k·x)%N)).  The a↔b
    mirror of Leg 1, via the same forward engine over the b-coset control window. -/
theorem gidneyTwoRegInPlace_leg2_deviation (w bits numWin N cm k kInv x : Nat)
    (TfamKinv : Nat → Nat → Nat)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkInv : (kInv * k) % N = 1 % N)
    (hfit_engine : N + 2 ^ cm * N ≤ 2 ^ bits)
    (hfitAll : ∀ jb : Fin (2 ^ bits),
      runningSum (cosetWindowConst kInv N w jb.val) numWin + (2 ^ cm - 1) * N < 2 ^ bits)
    (hwt : Gate.WellTyped (cosetDim w bits)
      (gidneyProductAddTOf w bits TfamKinv (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin)) :
    normSqDist
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (gidneyProductAddTOf w bits TfamKinv (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin))
          * cosetInputVec w bits N cm 0 ((k * x) % N))
        (cosetInputVec w bits N cm x ((k * x) % N))
      ≤ (numWin : ℝ) * (2 / 2 ^ cm) := by
  have hpow : (2 : Nat) ^ bits = (2 ^ w) ^ numWin := by
    rw [← hbits, Nat.mul_comm numWin w, Nat.pow_mul]
  refine cosetOutOfPlace_hfwd_E (eGid w bits (aBase w) (pass2_accfit w bits))
    (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (gidneyProductAddTOf w bits TfamKinv (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin))
      * cosetInputVec w bits N cm 0 ((k * x) % N))
    (cosetInputVec w bits N cm x ((k * x) % N))
    ((cosetWindow (2 ^ bits) N cm ((k * x) % N)).image
      (fun jb : Fin (2 ^ bits) => xCtrlGid w bits numWin (aBase w) (bBase w bits) jb.val))
    (fun ctrl => betaA w bits N cm ((k * x) % N) ctrl.val)
    kInv N cm w numWin
    (fun ctrl => decodeReg (fun i => bBase w bits + i) bits (ctrlFunA w bits ctrl.val))
    hN ?_ hfit_engine ?_ ?_ ?_ ?_
  · -- hxval
    intro b _; rw [← hpow]; exact decodeReg_lt_two_pow _ _ _
  · -- hzero
    intro ctrl hctrl
    exact leg2_hzero w bits numWin N cm x ((k * x) % N) TfamKinv hw hbits hwt ctrl hctrl
  · -- hfac_act
    intro ctrl hctrl
    obtain ⟨jb, hjb_mem, rfl⟩ := Finset.mem_image.mp hctrl
    dsimp only
    rw [leg2_xval_roundtrip w bits numWin jb.val hw hbits jb.isLt,
        leg1_actualAcc_eq w bits numWin N cm kInv jb.val TfamKinv hTfamKinv hN]
    exact leg2_branchOfE_dynamics w bits numWin N cm TfamKinv ((k * x) % N) jb.val hw hbits hN
      (by rw [canonicalSum_eq_runningSum kInv N w numWin jb.val TfamKinv hTfamKinv]; exact hfitAll jb) hwt
  · -- hfac_idl
    intro ctrl hctrl
    obtain ⟨jb, hjb_mem, rfl⟩ := Finset.mem_image.mp hctrl
    dsimp only
    rw [leg2_xval_roundtrip w bits numWin jb.val hw hbits jb.isLt]
    show branchOfE (eGid w bits (aBase w) (pass2_accfit w bits))
        (cosetInputTwoReg w bits N cm x ((k * x) % N))
        (xCtrlGid w bits numWin (aBase w) (bBase w bits) jb.val)
      = fun i z => betaA w bits N cm ((k * x) % N)
            (xCtrlGid w bits numWin (aBase w) (bBase w bits) jb.val).val
          * cosetState (2 ^ bits) N cm ((kInv * jb.val) % N) i z
    rw [branchOfE_cosetInputTwoReg_passA w bits N cm x ((k * x) % N)
          (xCtrlGid w bits numWin (aBase w) (bBase w bits) jb.val),
        leg2_residue bits N cm k kInv x jb.val hN hxN hkInv jb.isLt hjb_mem]
  · -- hweight
    have hfit_hweight : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits := by
      have hkxN : (k * x) % N < N := Nat.mod_lt _ hN
      have h1 : (2 ^ cm - 1) * N = 2 ^ cm * N - N := Nat.sub_one_mul _ _
      have h2 : N ≤ 2 ^ cm * N := Nat.le_mul_of_pos_left N (by positivity)
      omega
    exact leg2_hweight w bits numWin N cm ((k * x) % N) hN hfit_hweight

end FormalRV.Shor.GidneyInPlace.InPlaceLeg2
