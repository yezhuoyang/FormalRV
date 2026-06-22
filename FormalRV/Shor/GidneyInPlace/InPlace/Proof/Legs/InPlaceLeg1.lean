/-
  FormalRV.Shor.GidneyInPlace.InPlaceLeg1
  ───────────────────────────────────────────────
  LEG 1 of the two-register in-place coset-multiplier norm bound (Architecture B):
  the FORWARD pass-1 deviation
    normSqDist (uc_eval(pass1) · cosetInputVec x 0) (cosetInputVec x ((k·x)%N))
      ≤ numWin·(2/2^cm).

  pass-1 (`b += a·k`) acts, in the bBase factorization (data = b, control = a + scratch),
  as the windowed product-add ON THE b-REGISTER, per a-control-branch.  This file builds
  the foundational dynamics:

   • `cosetState_modSub_shift` — the SHIFT IDENTITY: off the window-fit, `cosetState 0`
     evaluated at the inverse-shifted index `modSub bits i s` equals `cosetState s` at `i`.
     (The b-register shift `z ↦ (z+s)%2^bits` sends `cosetState 0` to `cosetState s`.)

  Audit: every a-branch `ja ∈ cosetWindow x` has residue `x mod N`, so multiplying by `k`
  targets the SAME residue `(k·x)%N` — made explicit where used.  No reverse leg, no
  triangle, no in-place theorem here.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Mass.InPlaceNormBound
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceBranchAction
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceEndpoint

namespace FormalRV.Shor.GidneyInPlace.InPlaceLeg1

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer (normSqDist)
open FormalRV.Shor.WindowedArith (window)
open FormalRV.Shor.GidneyInPlace.ApproxOp (cosetState permState)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow cosetWindow_card)
open FormalRV.Shor.GidneyInPlace.InPlaceBranchAction (modSub modSub_add)
open FormalRV.Shor.GidneyInPlace.BranchFactor (branchOfE)
open FormalRV.Shor.GidneyInPlace.GatePerm (gateToPerm extendBool funboolNat)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputGid (eGid_apply)
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_eq_permState)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate
  (eGid pass1_accfit assembleEGid assembleEGid_data assembleEGid_comp compIdxGid compIdxGid_lt)
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput (xCtrlGid)
open FormalRV.Shor.GidneyInPlace.ProductAddWrapper (gidneyProductAddTOf)
open FormalRV.Shor.GidneyInPlace.InPlaceFoldAction (gidneyProductAddTOf_pass1_perm_through_eGid)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.BQAlgo (ulookup_ctrl_idx)
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput
  (assembleEGid_xCtrlGid inplaceAccInput inplaceWorkInput)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg
  (cosetInputTwoReg betaB branchOfE_cosetInputTwoReg_passB bBase aBase ctrlFunB scratchClean)
open FormalRV.Shor.WindowedCircuit (decodeReg_lt_two_pow)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.CosetMul (actualAcc actualAcc_eq_cosetState_runningSum runningSum)
open FormalRV.Shor.GidneyInPlace.CosetDeviationE (cosetOutOfPlace_hfwd_E)
open FormalRV.Shor.GidneyInPlace.CosetTableSum (cosetWindowConst)
open FormalRV.Shor.GidneyInPlace.InPlaceEndpoint (canonicalSum_eq_runningSum)

/-! ## §1. The shift identity. -/

/-- **The window-membership shift.**  Off the window-fit `s + (2^cm−1)·N < 2^bits`, the
    inverse shift `modSub bits i s` lands in `cosetWindow 0` iff `i` lands in
    `cosetWindow s`.  (The two windows differ by the uniform shift `s`; no wrap occurs
    under the fit.) -/
theorem mem_cosetWindow_modSub (bits N cm s : Nat) (hN : 0 < N) (hs : s < 2 ^ bits)
    (hfit : s + (2 ^ cm - 1) * N < 2 ^ bits) (i : Fin (2 ^ bits)) :
    (⟨modSub bits i.val s, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ bits))
        ∈ cosetWindow (2 ^ bits) N cm 0
      ↔ i ∈ cosetWindow (2 ^ bits) N cm s := by
  rw [mem_cosetWindow _ N cm 0 hN, mem_cosetWindow _ N cm s hN]
  constructor
  · rintro ⟨j', hj', hval⟩
    rw [Nat.zero_add] at hval
    replace hval : modSub bits i.val s = j' * N := hval
    refine ⟨j', hj', ?_⟩
    have hma := modSub_add bits i.val s i.isLt
    rw [hval] at hma
    have hlt : j' * N + s < 2 ^ bits := by
      have : j' * N ≤ (2 ^ cm - 1) * N := Nat.mul_le_mul_right _ (by omega)
      omega
    rw [Nat.mod_eq_of_lt hlt] at hma
    omega
  · rintro ⟨j, hj, hval⟩
    refine ⟨j, hj, ?_⟩
    rw [Nat.zero_add]
    show modSub bits i.val s = j * N
    unfold modSub
    rw [hval, Nat.mod_eq_of_lt hs]
    have hlt : j * N < 2 ^ bits := by
      have : j * N ≤ (2 ^ cm - 1) * N := Nat.mul_le_mul_right _ (by omega)
      omega
    have hrw : s + j * N + 2 ^ bits - s = 2 ^ bits + j * N := by omega
    rw [hrw, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

/-- **The cosetState shift identity.**  `cosetState 0` at the inverse-shifted index
    `modSub bits i s` equals `cosetState s` at `i` (off the window-fit).  This is the
    per-branch b-register dynamics ingredient: the pass-1 shift `z ↦ (z+s)%2^bits` carries
    `cosetState 0 ↦ cosetState s`. -/
theorem cosetState_modSub_shift (bits N cm s : Nat) (hN : 0 < N) (hs : s < 2 ^ bits)
    (hfit : s + (2 ^ cm - 1) * N < 2 ^ bits) (i : Fin (2 ^ bits)) (z : Fin 1) :
    cosetState (2 ^ bits) N cm 0 ⟨modSub bits i.val s, Nat.mod_lt _ (by positivity)⟩ z
      = cosetState (2 ^ bits) N cm s i z := by
  show (if (⟨modSub bits i.val s, _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm 0
        then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
      = (if i ∈ cosetWindow (2 ^ bits) N cm s then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
  by_cases h : i ∈ cosetWindow (2 ^ bits) N cm s
  · rw [if_pos ((mem_cosetWindow_modSub bits N cm s hN hs hfit i).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((mem_cosetWindow_modSub bits N cm s hN hs hfit i).mp hc)), if_neg h]

/-! ## §2. The per-branch pass-1 dynamics lift. -/

/-- **Pass-1 per-branch dynamics (the crux of Leg 1).**  Projected onto the a-control
    branch `xCtrlGid … ja` (bBase factorization, data = b), the gate output
    `uc_eval(pass1) · cosetInputVec x 0` is the fresh b-accumulator (`cosetState 0`) shifted
    by the windowed running sum `S = ∑ₖ TfamK k (window w ja k)` — i.e. `betaB · cosetState S`.
    Lifts the B5 BASIS map `gidneyProductAddTOf_pass1_perm_through_eGid` to the cosetState
    superposition via `uc_eval_eq_permState` (pushforward) + the shift identity §1.  No
    per-window re-induction (B5 already did it). -/
theorem leg1_branchOfE_dynamics (w bits numWin N cm : Nat) (TfamK : Nat → Nat → Nat)
    (x ja : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hfit : (∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) + (2 ^ cm - 1) * N < 2 ^ bits)
    (hwt : Gate.WellTyped (cosetDim w bits)
      (gidneyProductAddTOf w bits TfamK (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin)) :
    branchOfE (eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits))
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (gidneyProductAddTOf w bits TfamK (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin))
          * cosetInputVec w bits N cm x 0)
        (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja)
      = fun i z => betaB w bits N cm x (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja).val
          * cosetState (2 ^ bits) N cm (∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) i z := by
  have hSlt : (∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) < 2 ^ bits := by
    have : (0 : Nat) ≤ (2 ^ cm - 1) * N := Nat.zero_le _
    omega
  funext i z
  -- inverse permutation through eGid (control preserved, data inverse-shifted)
  have hinv : (gateToPerm (gidneyProductAddTOf w bits TfamK
        (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin) (cosetDim w bits) hwt).symm
      (eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
        (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja, i))
      = eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
        (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja,
          ⟨modSub bits i.val (∑ k ∈ Finset.range numWin, TfamK k (window w ja k)),
            Nat.mod_lt _ (by positivity)⟩) := by
    rw [Equiv.symm_apply_eq]
    have hb5 := gidneyProductAddTOf_pass1_perm_through_eGid w bits numWin TfamK ja
      (modSub bits i.val (∑ k ∈ Finset.range numWin, TfamK k (window w ja k)))
      hw hbits (Nat.mod_lt _ (by positivity))
      (by rw [modSub_add bits i.val _ i.isLt]; exact i.isLt) hwt
    rw [hb5]
    congr 1
    apply congrArg
    apply Fin.ext
    show i.val = (modSub bits i.val (∑ k ∈ Finset.range numWin, TfamK k (window w ja k))
        + ∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) % 2 ^ bits
    rw [modSub_add bits i.val _ i.isLt]
  show (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
          (gidneyProductAddTOf w bits TfamK (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin))
        * cosetInputVec w bits N cm x 0)
      (eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
        (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja, i)) 0
    = betaB w bits N cm x (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja).val
        * cosetState (2 ^ bits) N cm (∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) i z
  rw [uc_eval_eq_permState (gidneyProductAddTOf w bits TfamK
        (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin) (cosetDim w bits) hwt
        (cosetInputVec w bits N cm x 0)]
  show cosetInputVec w bits N cm x 0
      ((gateToPerm (gidneyProductAddTOf w bits TfamK
          (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin) (cosetDim w bits) hwt).symm
        (eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja, i))) 0
    = betaB w bits N cm x (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja).val
        * cosetState (2 ^ bits) N cm (∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) i z
  rw [hinv]
  show branchOfE (eGid w bits (bBase w bits) (pass1_accfit w bits))
        (cosetInputTwoReg w bits N cm x 0)
        (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja)
        ⟨modSub bits i.val (∑ k ∈ Finset.range numWin, TfamK k (window w ja k)),
          Nat.mod_lt _ (by positivity)⟩ z
    = betaB w bits N cm x (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja).val
        * cosetState (2 ^ bits) N cm (∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) i z
  rw [branchOfE_cosetInputTwoReg_passB w bits N cm x 0
        (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja)]
  show betaB w bits N cm x (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja).val
        * cosetState (2 ^ bits) N cm 0
          ⟨modSub bits i.val (∑ k ∈ Finset.range numWin, TfamK k (window w ja k)),
            Nat.mod_lt _ (by positivity)⟩ z
    = betaB w bits N cm x (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja).val
        * cosetState (2 ^ bits) N cm (∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) i z
  rw [cosetState_modSub_shift bits N cm
        (∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) hN hSlt hfit i z]

/-! ## §3. The residue and canonical-table bridges. -/

/-- **Residue bridge (the audit point).**  Every active a-branch `ja ∈ cosetWindow x` has
    residue `x mod N`, so multiplying by `k` targets the SAME residue: `(k·ja)%N = (k·x)%N`. -/
theorem leg1_residue (bits N cm k x ja : Nat) (hN : 0 < N) (hja : ja < 2 ^ bits)
    (hmem : (⟨ja, hja⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm x) :
    (k * ja) % N = (k * x) % N := by
  rw [mem_cosetWindow (2 ^ bits) N cm x hN] at hmem
  obtain ⟨p, hp, hval⟩ := hmem
  replace hval : ja = x + p * N := hval
  rw [hval, Nat.mul_add, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]

/-- **Canonical-table bridge.**  Under the canonical table family, the coset fold
    `actualAcc` of the window constants equals the cosetState at the LITERAL running sum
    `∑ₖ TfamK k (window w ja k)` (= `runningSum (cosetWindowConst k N w ja)`). -/
theorem leg1_actualAcc_eq (w bits numWin N cm k ja : Nat) (TfamK : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr) (hN : 0 < N) :
    actualAcc (2 ^ bits) N cm 0 (cosetWindowConst k N w ja) numWin
      = cosetState (2 ^ bits) N cm (∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) := by
  rw [actualAcc_eq_cosetState_runningSum (2 ^ bits) N cm 0 (cosetWindowConst k N w ja) hN numWin,
      Nat.zero_add, ← canonicalSum_eq_runningSum k N w numWin ja TfamK hTfamK]

/-! ## §4. The `xval` roundtrip (decode of the control branch). -/

/-- **`xval` roundtrip.**  The a-value decoded from the control branch `xCtrlGid … ja`
    (exactly the a-value `betaB` reads) is `ja`.  Via `assembleEGid_xCtrlGid` (control =
    `inplaceAccInput`) + `decodeReg_eq_mod_of_testBit` (the multiplicand sits at the
    `aBase` block via `encodeReg`). -/
theorem leg1_xval_roundtrip (w bits numWin ja : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hja : ja < 2 ^ bits) :
    decodeReg (fun i => aBase w + i) bits
        (ctrlFunB w bits (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja).val) = ja := by
  rw [FormalRV.Shor.WindowedCircuit.decodeReg_eq_mod_of_testBit (fun i => aBase w + i) bits ja _,
      Nat.mod_eq_of_lt hja]
  intro i hi
  show assembleEGid w bits (bBase w bits)
      (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja).val 0 (aBase w + i) = ja.testBit i
  rw [assembleEGid_xCtrlGid w bits numWin (bBase w bits) (aBase w) ja 0 (aBase w + i)
        (pass1_accfit w bits) (by unfold cosetDim aBase; omega)]
  unfold inplaceAccInput inplaceWorkInput FormalRV.Shor.WindowedCircuit.encodeReg
  rw [if_neg (by unfold bBase aBase; omega)]
  rw [if_neg (by show aBase w + i ≠ ulookup_ctrl_idx; unfold aBase ulookup_ctrl_idx; omega)]
  rw [if_pos (by unfold aBase; exact ⟨by omega, by rw [hbits]; omega⟩)]
  congr 1
  unfold aBase; omega

/-! ## §5. The β-weight normalization (hweight, via counting). -/

set_option maxHeartbeats 800000 in
/-- **Weight bound (`hweight`).**  The β-weights `betaB` over the active a-control branches
    (`xCtrlGid` of the a-coset window) sum to `≤ 1`.  Counting: each `normSq(betaB) ≤
    1/2^cm` (betaB ∈ {0, 1/√2^cm}), and the active set has `≤ |cosetWindow x| = 2^cm`
    elements (`card_image_le` + `cosetWindow_card`). -/
theorem leg1_hweight (w bits numWin N cm x : Nat) (hN : 0 < N)
    (hfit : x + (2 ^ cm - 1) * N < 2 ^ bits) :
    ∑ ctrl ∈ (cosetWindow (2 ^ bits) N cm x).image
        (fun ja : Fin (2 ^ bits) => xCtrlGid w bits numWin (bBase w bits) (aBase w) ja.val),
      Complex.normSq (betaB w bits N cm x ctrl.val) ≤ 1 := by
  classical
  have hc : Complex.normSq ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) = 1 / 2 ^ cm := by
    rw [Complex.normSq_ofReal, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by positivity)]
  have h0 : Complex.normSq (0 : ℂ) ≤ 1 / 2 ^ cm := by rw [Complex.normSq_zero]; positivity
  -- bound betaB's normSq by `by_cases` (propositional em; `if_pos`/`if_neg` are generic
  -- over the Decidable instance), avoiding any reduction of the `cosetWindow` membership.
  have hbound : ∀ ctrl : Fin (2 ^ (cosetDim w bits - bits)),
      Complex.normSq (betaB w bits N cm x ctrl.val) ≤ 1 / 2 ^ cm := by
    intro ctrl
    unfold betaB
    by_cases hA : scratchClean w bits (ctrlFunB w bits ctrl.val)
    · rw [if_pos hA]
      by_cases hB : (⟨decodeReg (fun i => aBase w + i) bits (ctrlFunB w bits ctrl.val),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm x
      · rw [if_pos hB]; exact le_of_eq hc
      · rw [if_neg hB]; exact h0
    · rw [if_neg hA]; exact h0
  have hcard : ((cosetWindow (2 ^ bits) N cm x).image
      (fun ja : Fin (2 ^ bits) => xCtrlGid w bits numWin (bBase w bits) (aBase w) ja.val)).card
      ≤ 2 ^ cm :=
    le_trans Finset.card_image_le (le_of_eq (cosetWindow_card (2 ^ bits) N cm x hN hfit))
  refine le_trans (Finset.sum_le_card_nsmul _ _ (1 / 2 ^ cm : ℝ) (fun ctrl _ => hbound ctrl)) ?_
  rw [nsmul_eq_mul, mul_one_div, div_le_one (by positivity)]
  exact_mod_cast hcard

/-! ## §6. The clean-control roundtrip (a control branch that decodes to `ja` IS `xCtrlGid ja`). -/

/-- **Clean-control roundtrip.**  A control branch `ctrl` whose assembled bit-function is
    scratch-clean and whose a-block decodes to `ja` is EXACTLY `xCtrlGid … ja`.  Proven by
    POINTWISE bit-function equality `ctrlFunB ctrl = inplaceWorkInput … ja` on `[0,cosetDim)`
    (cases: the ctrl bit = true; the a-block bits encode `ja`; the b-block and all
    lookup/temp/carry scratch bits = false), then `decodeReg`-roundtrip on the complement
    enumerator.  No dynamics, no amplitude reasoning. -/
theorem clean_ctrl_eq_xCtrlGid (w bits numWin ja : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (ctrl : Fin (2 ^ (cosetDim w bits - bits)))
    (hclean : scratchClean w bits (ctrlFunB w bits ctrl.val))
    (hdec : decodeReg (fun i => aBase w + i) bits (ctrlFunB w bits ctrl.val) = ja) :
    ctrl = xCtrlGid w bits numWin (bBase w bits) (aBase w) ja := by
  -- pointwise: ctrlFunB ctrl agrees with inplaceWorkInput ja on [0, cosetDim)
  have hfeq : ∀ p, p < cosetDim w bits →
      ctrlFunB w bits ctrl.val p = inplaceWorkInput numWin w (aBase w) ja p := by
    intro p hp
    by_cases hctrl : p = ulookup_ctrl_idx
    · subst hctrl
      rw [hclean.1]
      show true = (if ulookup_ctrl_idx = ulookup_ctrl_idx then true
        else FormalRV.Shor.WindowedCircuit.encodeReg (aBase w) (numWin * w) ja ulookup_ctrl_idx)
      rw [if_pos rfl]
    by_cases ha : aBase w ≤ p ∧ p < aBase w + bits
    · obtain ⟨i, rfl⟩ : ∃ i, p = aBase w + i := ⟨p - aBase w, by omega⟩
      have hi : i < bits := by omega
      have hbit : ctrlFunB w bits ctrl.val (aBase w + i) = ja.testBit i := by
        have h := FormalRV.Shor.WindowedCircuit.decodeReg_testBit (fun i => aBase w + i) bits
          (ctrlFunB w bits ctrl.val) i hi
        rw [hdec] at h; exact h.symm
      rw [hbit]
      show ja.testBit i = (if aBase w + i = ulookup_ctrl_idx then true
        else FormalRV.Shor.WindowedCircuit.encodeReg (aBase w) (numWin * w) ja (aBase w + i))
      rw [if_neg (by unfold ulookup_ctrl_idx aBase; omega)]
      show ja.testBit i = (if aBase w ≤ aBase w + i ∧ aBase w + i < aBase w + numWin * w
        then ja.testBit (aBase w + i - aBase w) else false)
      rw [if_pos ⟨by omega, by rw [hbits]; omega⟩, Nat.add_sub_cancel_left]
    by_cases hb : bBase w bits ≤ p ∧ p < bBase w bits + bits
    · obtain ⟨i, rfl⟩ : ∃ i, p = bBase w bits + i := ⟨p - bBase w bits, by omega⟩
      have hi : i < bits := by omega
      show ctrlFunB w bits ctrl.val (bBase w bits + i) = inplaceWorkInput numWin w (aBase w) ja (bBase w bits + i)
      rw [show ctrlFunB w bits ctrl.val (bBase w bits + i)
            = assembleEGid w bits (bBase w bits) ctrl.val 0 (bBase w bits + i) from rfl,
          assembleEGid_data w bits (bBase w bits) ctrl.val 0 i hi, Nat.zero_testBit]
      show false = (if bBase w bits + i = ulookup_ctrl_idx then true
        else FormalRV.Shor.WindowedCircuit.encodeReg (aBase w) (numWin * w) ja (bBase w bits + i))
      rw [if_neg (by unfold ulookup_ctrl_idx bBase; omega)]
      show false = (if aBase w ≤ bBase w bits + i ∧ bBase w bits + i < aBase w + numWin * w
        then ja.testBit (bBase w bits + i - aBase w) else false)
      rw [if_neg (by unfold bBase aBase; rw [hbits]; omega)]
    · rw [hclean.2 p hp ha hb hctrl]
      show false = (if p = ulookup_ctrl_idx then true
        else FormalRV.Shor.WindowedCircuit.encodeReg (aBase w) (numWin * w) ja p)
      rw [if_neg hctrl]
      show false = (if aBase w ≤ p ∧ p < aBase w + numWin * w
        then ja.testBit (p - aBase w) else false)
      rw [if_neg (by rw [hbits]; exact ha)]
  -- conclude: ctrl.val = (xCtrlGid …).val = decodeReg compIdxGid (inplaceWorkInput …)
  apply Fin.ext
  show ctrl.val = decodeReg (compIdxGid bits (bBase w bits)) (cosetDim w bits - bits)
      (inplaceWorkInput numWin w (aBase w) ja)
  rw [FormalRV.Shor.WindowedCircuit.decodeReg_eq_mod_of_testBit (compIdxGid bits (bBase w bits))
        (cosetDim w bits - bits) ctrl.val (inplaceWorkInput numWin w (aBase w) ja) (fun j hj => ?_),
      Nat.mod_eq_of_lt ctrl.isLt]
  rw [← hfeq (compIdxGid bits (bBase w bits) j)
        (compIdxGid_lt w bits (bBase w bits) j (pass1_accfit w bits) hj)]
  exact assembleEGid_comp w bits (bBase w bits) ctrl.val 0 j hj

/-! ## §7. The input-state support lemma. -/

/-- **Input support.**  Where `cosetInputTwoReg xa xb` has a NONZERO amplitude, the index's
    bit-function is scratch-clean and BOTH register decodes lie in their coset windows
    (a-block ∈ cosetWindow xa, b-block ∈ cosetWindow xb).  Pure input-state fact — no gate
    dynamics, raw `Fin (2^bits)` decodes; the three facts are extracted from the nonzero
    product amplitude by `if`/`mul_ne_zero` reasoning. -/
theorem cosetInputTwoReg_support_nonzero (w bits N cm xa xb : Nat)
    (idx : Fin (2 ^ cosetDim w bits)) (z : Fin 1)
    (h : cosetInputTwoReg w bits N cm xa xb idx z ≠ 0) :
    scratchClean w bits (nat_to_funbool
        (cosetDim w bits) idx.val)
    ∧ (⟨decodeReg (fun i => aBase w + i) bits
          (nat_to_funbool (cosetDim w bits) idx.val),
        decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xa
    ∧ (⟨decodeReg (fun i => bBase w bits + i) bits
          (nat_to_funbool (cosetDim w bits) idx.val),
        decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xb := by
  classical
  have hV : cosetInputTwoReg w bits N cm xa xb idx z
      = (if scratchClean w bits (nat_to_funbool
            (cosetDim w bits) idx.val) then
          (if (⟨decodeReg (fun i => aBase w + i) bits
                (nat_to_funbool (cosetDim w bits) idx.val),
              decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xa
            then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
          * (if (⟨decodeReg (fun i => bBase w bits + i) bits
                (nat_to_funbool (cosetDim w bits) idx.val),
              decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xb
            then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
        else 0) := rfl
  rw [hV] at h
  have hsc : scratchClean w bits (nat_to_funbool
      (cosetDim w bits) idx.val) := by
    by_contra hc; rw [if_neg hc] at h; exact h rfl
  rw [if_pos hsc] at h
  obtain ⟨hA, hB⟩ := mul_ne_zero_iff.mp h
  refine ⟨hsc, ?_, ?_⟩
  · by_contra hc; rw [if_neg hc] at hA; exact hA rfl
  · by_contra hc; rw [if_neg hc] at hB; exact hB rfl

/-! ## §8. The preimage-as-eGid-image reconstruction. -/

/-- **Preimage as an eGid image.**  A basis index `idx` whose bit-function is scratch-clean
    with a-block decode `ja` and b-block decode `z` (`z ∈ cosetWindow 0` in use — NOT
    necessarily `0`) is EXACTLY the eGid image `eGid bBase (xCtrlGid ja, ⟨z⟩)`.  Pointwise
    bit-function equality `nat_to_funbool idx = inplaceAccInput … z ja` (cases: ctrl bit;
    a-block = `ja`; b-block = `z`; scratch = false), lifted to indices through
    `funbool_to_nat` + `eGid_apply`.  No dynamics. -/
theorem P_as_eGid_image (w bits numWin ja z : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hz : z < 2 ^ bits) (idx : Fin (2 ^ cosetDim w bits))
    (hclean : scratchClean w bits (nat_to_funbool (cosetDim w bits) idx.val))
    (ha : decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val) = ja)
    (hb : decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val) = z) :
    idx = eGid w bits (bBase w bits) (pass1_accfit w bits)
        (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja, ⟨z, hz⟩) := by
  rw [eGid_apply w bits numWin (bBase w bits) (aBase w) ja z hz (pass1_accfit w bits)]
  apply Fin.ext
  show idx.val = funbool_to_nat (cosetDim w bits)
      (extendBool (cosetDim w bits)
        (fun p => inplaceAccInput w bits numWin (bBase w bits) (aBase w) z ja p.val))
  rw [← funbool_to_nat_nat_to_funbool (cosetDim w bits) idx.val idx.isLt]
  apply FormalRV.Shor.GidneyInPlace.UCEvalBridge.funbool_to_nat_congr
  intro p hp
  rw [show extendBool (cosetDim w bits)
        (fun p => inplaceAccInput w bits numWin (bBase w bits) (aBase w) z ja p.val) p
      = inplaceAccInput w bits numWin (bBase w bits) (aBase w) z ja p from by
        unfold extendBool; rw [dif_pos hp]]
  -- nat_to_funbool idx p = inplaceAccInput (bBase)(aBase) z ja p   (4 cases)
  by_cases hctrl : p = ulookup_ctrl_idx
  · subst hctrl
    rw [hclean.1]
    show true = inplaceAccInput w bits numWin (bBase w bits) (aBase w) z ja ulookup_ctrl_idx
    unfold inplaceAccInput inplaceWorkInput
    rw [if_neg (by unfold ulookup_ctrl_idx bBase; omega), if_pos rfl]
  by_cases ha' : aBase w ≤ p ∧ p < aBase w + bits
  · obtain ⟨i, rfl⟩ : ∃ i, p = aBase w + i := ⟨p - aBase w, by omega⟩
    have hi : i < bits := by omega
    have hbit : nat_to_funbool (cosetDim w bits) idx.val (aBase w + i) = ja.testBit i := by
      have h := FormalRV.Shor.WindowedCircuit.decodeReg_testBit (fun i => aBase w + i) bits
        (nat_to_funbool (cosetDim w bits) idx.val) i hi
      rw [ha] at h; exact h.symm
    rw [hbit]
    show ja.testBit i = inplaceAccInput w bits numWin (bBase w bits) (aBase w) z ja (aBase w + i)
    unfold inplaceAccInput inplaceWorkInput
    rw [if_neg (by unfold bBase aBase; omega), if_neg (by unfold ulookup_ctrl_idx aBase; omega)]
    show ja.testBit i = (if aBase w ≤ aBase w + i ∧ aBase w + i < aBase w + numWin * w
      then ja.testBit (aBase w + i - aBase w) else false)
    rw [if_pos ⟨by omega, by rw [hbits]; omega⟩, Nat.add_sub_cancel_left]
  by_cases hb' : bBase w bits ≤ p ∧ p < bBase w bits + bits
  · obtain ⟨i, rfl⟩ : ∃ i, p = bBase w bits + i := ⟨p - bBase w bits, by omega⟩
    have hi : i < bits := by omega
    have hbit : nat_to_funbool (cosetDim w bits) idx.val (bBase w bits + i) = z.testBit i := by
      have h := FormalRV.Shor.WindowedCircuit.decodeReg_testBit (fun i => bBase w bits + i) bits
        (nat_to_funbool (cosetDim w bits) idx.val) i hi
      rw [hb] at h; exact h.symm
    rw [hbit]
    show z.testBit i = inplaceAccInput w bits numWin (bBase w bits) (aBase w) z ja (bBase w bits + i)
    unfold inplaceAccInput
    rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
  · rw [hclean.2 p hp ha' hb' hctrl]
    show false = inplaceAccInput w bits numWin (bBase w bits) (aBase w) z ja p
    unfold inplaceAccInput inplaceWorkInput
    rw [if_neg hb', if_neg hctrl]
    show false = (if aBase w ≤ p ∧ p < aBase w + numWin * w then ja.testBit (p - aBase w) else false)
    rw [if_neg (by rw [hbits]; exact ha')]

/-! ## §9. The idle-branch (hzero) support lemma. -/

/-- **Off-active branches vanish (hzero).**  For a control branch `ctrl` OUTSIDE the active
    a-window image, BOTH the pass-1 output `uc_eval(pass1)·cosetInputVec x 0` and the ideal
    `cosetInputVec x ((k·x)%N)` project (via `branchOfE`) to the ZERO substate.  The actual
    side uses the contrapositive: a nonzero output projection has a clean preimage in the
    input support (`uc_eval_eq_permState` + `cosetInputTwoReg_support_nonzero`), which is an
    eGid branch (`P_as_eGid_image`) whose pass-1 image (B5) preserves the control as
    `xCtrlGid ja` with `ja ∈ cosetWindow x` — forcing `ctrl ∈ active`, contradiction.  The
    ideal side: `betaB = 0` off active (`clean_ctrl_eq_xCtrlGid`).  NB: `z = b ∈ cosetWindow
    0`, never assumed `= 0`. -/
theorem leg1_hzero (w bits numWin N cm k x : Nat) (TfamK : Nat → Nat → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hwt : Gate.WellTyped (cosetDim w bits)
      (gidneyProductAddTOf w bits TfamK (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin))
    (ctrl : Fin (2 ^ (cosetDim w bits - bits)))
    (hctrl : ctrl ∉ (cosetWindow (2 ^ bits) N cm x).image
        (fun ja : Fin (2 ^ bits) => xCtrlGid w bits numWin (bBase w bits) (aBase w) ja.val)) :
    branchOfE (eGid w bits (bBase w bits) (pass1_accfit w bits))
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (gidneyProductAddTOf w bits TfamK (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin))
          * cosetInputVec w bits N cm x 0) ctrl
      = branchOfE (eGid w bits (bBase w bits) (pass1_accfit w bits))
          (cosetInputVec w bits N cm x ((k * x) % N)) ctrl := by
  have hact : branchOfE (eGid w bits (bBase w bits) (pass1_accfit w bits))
      (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
          (gidneyProductAddTOf w bits TfamK (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin))
        * cosetInputVec w bits N cm x 0) ctrl = (fun _ _ => 0) := by
    funext i z
    show (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (gidneyProductAddTOf w bits TfamK (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin))
        * cosetInputVec w bits N cm x 0)
        (eGid w bits (bBase w bits) (pass1_accfit w bits) (ctrl, i)) 0 = 0
    rw [uc_eval_eq_permState (gidneyProductAddTOf w bits TfamK
          (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin) (cosetDim w bits) hwt
          (cosetInputVec w bits N cm x 0)]
    show cosetInputVec w bits N cm x 0
        ((gateToPerm (gidneyProductAddTOf w bits TfamK
            (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin) (cosetDim w bits) hwt).symm
          (eGid w bits (bBase w bits) (pass1_accfit w bits) (ctrl, i))) 0 = 0
    by_contra hne
    apply hctrl
    set Q := (gateToPerm (gidneyProductAddTOf w bits TfamK
        (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin) (cosetDim w bits) hwt).symm
        (eGid w bits (bBase w bits) (pass1_accfit w bits) (ctrl, i)) with hQ
    obtain ⟨hclean, hja_win, _hz_win⟩ := cosetInputTwoReg_support_nonzero w bits N cm x 0 Q 0 hne
    have hzlt : decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) Q.val)
        < 2 ^ bits := decodeReg_lt_two_pow _ _ _
    have hQeq : Q = eGid w bits (bBase w bits) (pass1_accfit w bits)
        (xCtrlGid w bits numWin (bBase w bits) (aBase w)
            (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) Q.val)),
          ⟨decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) Q.val), hzlt⟩) :=
      P_as_eGid_image w bits numWin _ _ hw hbits hzlt Q hclean rfl rfl
    have hσQ : gateToPerm (gidneyProductAddTOf w bits TfamK
        (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin) (cosetDim w bits) hwt Q
        = eGid w bits (bBase w bits) (pass1_accfit w bits) (ctrl, i) := by
      rw [hQ]; exact Equiv.apply_symm_apply _ _
    rw [hQeq] at hσQ
    simp only [bBase, aBase] at hσQ
    rw [gidneyProductAddTOf_pass1_perm_through_eGid w bits numWin TfamK
          (decodeReg (fun i => 1 + 2 * w + i) bits (nat_to_funbool (cosetDim w bits) Q.val))
          (decodeReg (fun i => 1 + 2 * w + bits + i) bits (nat_to_funbool (cosetDim w bits) Q.val))
          hw hbits (decodeReg_lt_two_pow _ _ _) (Nat.mod_lt _ (by positivity)) hwt] at hσQ
    rw [Finset.mem_image]
    refine ⟨⟨decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) Q.val),
        decodeReg_lt_two_pow _ _ _⟩, hja_win, ?_⟩
    exact congrArg Prod.fst
      ((eGid w bits (bBase w bits) (pass1_accfit w bits)).injective hσQ)
  have hidl : branchOfE (eGid w bits (bBase w bits) (pass1_accfit w bits))
      (cosetInputVec w bits N cm x ((k * x) % N)) ctrl = (fun _ _ => 0) := by
    show branchOfE (eGid w bits (bBase w bits) (pass1_accfit w bits))
        (cosetInputTwoReg w bits N cm x ((k * x) % N)) ctrl = (fun _ _ => 0)
    rw [branchOfE_cosetInputTwoReg_passB w bits N cm x ((k * x) % N) ctrl]
    have hbeta : betaB w bits N cm x ctrl.val = 0 := by
      by_contra hbne
      apply hctrl
      have hsc : scratchClean w bits (ctrlFunB w bits ctrl.val) := by
        by_contra hsc; apply hbne; unfold betaB; rw [if_neg hsc]
      have hmem : (⟨decodeReg (fun i => aBase w + i) bits (ctrlFunB w bits ctrl.val),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm x := by
        by_contra hm; apply hbne; unfold betaB; rw [if_pos hsc, if_neg hm]
      rw [Finset.mem_image]
      exact ⟨⟨decodeReg (fun i => aBase w + i) bits (ctrlFunB w bits ctrl.val),
          decodeReg_lt_two_pow _ _ _⟩, hmem,
        (clean_ctrl_eq_xCtrlGid w bits numWin _ hw hbits ctrl hsc rfl).symm⟩
    rw [hbeta]; funext i z; simp
  rw [hact, hidl]

/-! ## §10. LEG 1 — the forward pass-1 deviation. -/

/-- **LEG 1 (the forward pass-1 deviation).**  `pass1` (`b += a·k`), applied to the
    two-register coset input `cosetInputTwoReg x 0`, is within `numWin·(2/2^cm)` (Born-L1
    `normSqDist`) of the ideal post-pass-1 intermediate `cosetInputTwoReg x ((k·x)%N)`
    (a stays `cosetState x`, b becomes `cosetState ((k·x)%N)`).  Assembled by the forward
    branchOfE controlled-lift engine `cosetOutOfPlace_hfwd_E` over the a-coset control
    window: per active branch `ja ∈ cosetWindow x`, pass-1 runs the windowed product-add on
    b (`leg1_branchOfE_dynamics` + `leg1_actualAcc_eq`, residue `(k·ja)%N = (k·x)%N` by
    `leg1_residue`); off-active branches vanish (`leg1_hzero`); the β-weights sum `≤ 1`
    (`leg1_hweight`).  `b ∈ cosetWindow 0` throughout (never `= 0`). -/
theorem gidneyTwoRegInPlace_leg1_deviation (w bits numWin N cm k x : Nat) (TfamK : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hfit_engine : N + 2 ^ cm * N ≤ 2 ^ bits)
    (hfitAll : ∀ ja : Fin (2 ^ bits),
      runningSum (cosetWindowConst k N w ja.val) numWin + (2 ^ cm - 1) * N < 2 ^ bits)
    (hwt : Gate.WellTyped (cosetDim w bits)
      (gidneyProductAddTOf w bits TfamK (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin)) :
    normSqDist
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (gidneyProductAddTOf w bits TfamK (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin))
          * cosetInputVec w bits N cm x 0)
        (cosetInputVec w bits N cm x ((k * x) % N))
      ≤ (numWin : ℝ) * (2 / 2 ^ cm) := by
  have hpow : (2 : Nat) ^ bits = (2 ^ w) ^ numWin := by
    rw [← hbits, Nat.mul_comm numWin w, Nat.pow_mul]
  refine cosetOutOfPlace_hfwd_E (eGid w bits (bBase w bits) (pass1_accfit w bits))
    (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (gidneyProductAddTOf w bits TfamK (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin))
      * cosetInputVec w bits N cm x 0)
    (cosetInputVec w bits N cm x ((k * x) % N))
    ((cosetWindow (2 ^ bits) N cm x).image
      (fun ja : Fin (2 ^ bits) => xCtrlGid w bits numWin (bBase w bits) (aBase w) ja.val))
    (fun ctrl => betaB w bits N cm x ctrl.val)
    k N cm w numWin
    (fun ctrl => decodeReg (fun i => aBase w + i) bits (ctrlFunB w bits ctrl.val))
    hN ?_ hfit_engine ?_ ?_ ?_ ?_
  · -- hxval
    intro b _; rw [← hpow]; exact decodeReg_lt_two_pow _ _ _
  · -- hzero
    intro ctrl hctrl
    exact leg1_hzero w bits numWin N cm k x TfamK hw hbits hwt ctrl hctrl
  · -- hfac_act
    intro ctrl hctrl
    obtain ⟨ja, hja_mem, rfl⟩ := Finset.mem_image.mp hctrl
    dsimp only
    rw [leg1_xval_roundtrip w bits numWin ja.val hw hbits ja.isLt,
        leg1_actualAcc_eq w bits numWin N cm k ja.val TfamK hTfamK hN]
    exact leg1_branchOfE_dynamics w bits numWin N cm TfamK x ja.val hw hbits hN
      (by rw [canonicalSum_eq_runningSum k N w numWin ja.val TfamK hTfamK]; exact hfitAll ja) hwt
  · -- hfac_idl
    intro ctrl hctrl
    obtain ⟨ja, hja_mem, rfl⟩ := Finset.mem_image.mp hctrl
    dsimp only
    rw [leg1_xval_roundtrip w bits numWin ja.val hw hbits ja.isLt]
    show branchOfE (eGid w bits (bBase w bits) (pass1_accfit w bits))
        (cosetInputTwoReg w bits N cm x ((k * x) % N))
        (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja.val)
      = fun i z => betaB w bits N cm x (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja.val).val
          * cosetState (2 ^ bits) N cm ((k * ja.val) % N) i z
    rw [branchOfE_cosetInputTwoReg_passB w bits N cm x ((k * x) % N)
          (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja.val),
        leg1_residue bits N cm k x ja.val hN ja.isLt hja_mem]
  · -- hweight
    have hfit_hweight : x + (2 ^ cm - 1) * N < 2 ^ bits := by
      have h1 : (2 ^ cm - 1) * N = 2 ^ cm * N - N := Nat.sub_one_mul _ _
      have h2 : N ≤ 2 ^ cm * N := Nat.le_mul_of_pos_left N (by positivity)
      omega
    exact leg1_hweight w bits numWin N cm x hN hfit_hweight

end FormalRV.Shor.GidneyInPlace.InPlaceLeg1
