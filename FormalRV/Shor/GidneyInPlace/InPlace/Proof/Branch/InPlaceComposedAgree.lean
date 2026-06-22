/-
  FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree
  ──────────────────────────────────────────────────
  PACKAGING checkpoint 2c (part 1 of the full agree-off): the eGid-branch AMPLITUDE
  EVALUATION of the two-register coset input — the value of `cosetInputVec xa xb` at an
  eGid control×data branch is the PRODUCT of the two block window indicators.

  This is the reusable foundation the `good_branch_amplitude_eq` and the symmetric-difference
  bad set rest on:
   • `betaB_xCtrlGid` / `betaA_xCtrlGid` — the control weights `β` at the clean control
     `xCtrlGid` collapse to a single window indicator (scratch is clean, the encoded block
     decodes back via `leg1/leg2_xval_roundtrip`).
   • `cosetInputVec_at_bBase` / `_at_aBase` — `cosetInputVec` at an input (bBase) / output
     (aBase) eGid branch is `(a-block ∈ window xa) · (b-block ∈ window xb)`, via
     `branchOfE_cosetInputTwoReg_passB/passA`.

  Raw `Fin (2^bits)` branch indices; NO gate dynamics, NO bad set, NO mass.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceComposedBranch
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceAgreeOff
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceLeg2

namespace FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedCircuit (encodeReg decodeReg_lt_two_pow)
open FormalRV.Shor.WindowedArith (window tableValue)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.ApproxOp (cosetState permState)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow)
open FormalRV.Shor.GidneyInPlace.BranchFactor (branchOfE)
open FormalRV.Shor.GidneyInPlace.GatePerm (gateToPerm)
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_eq_permState)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate (eGid pass1_accfit pass2_accfit)
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput
  (inplaceAccInput inplaceWorkInput xCtrlGid assembleEGid_xCtrlGid)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg
  (aBase bBase scratchClean cosetInputTwoReg scratchClean_congr_offBlocks
   ctrlFunA ctrlFunB betaA betaB
   branchOfE_cosetInputTwoReg_passA branchOfE_cosetInputTwoReg_passB)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceLeg1
  (leg1_xval_roundtrip cosetInputTwoReg_support_nonzero P_as_eGid_image)
open FormalRV.Shor.GidneyInPlace.InPlaceLeg2 (leg2_xval_roundtrip)
open FormalRV.Shor.GidneyInPlace.InPlaceBranchAction (modSub)
open FormalRV.Shor.GidneyInPlace.InPlaceAgreeOff (goodPair gidneyTwoRegInPlace_agree_off)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate
  (gidneyInPlaceWithSwap gidneyInPlaceWithSwap_wellTyped)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedBranch (gidneyInPlaceWithSwap_branch_action)

/-! ## §1. `scratchClean` of the clean `inplaceAccInput` (data lives in the excluded blocks). -/

/-- `inplaceAccInput` with `accBase = bBase`, `yBase = aBase` is scratch-clean: its only set
    bits are in the two data blocks (which `scratchClean` excludes) and the ctrl bit. -/
theorem scratchClean_inplaceAccInput_bAcc (w bits numWin z y : Nat) (hbits : numWin * w = bits) :
    scratchClean w bits (inplaceAccInput w bits numWin (bBase w bits) (aBase w) z y) := by
  refine ⟨?_, ?_⟩
  · show inplaceAccInput w bits numWin (bBase w bits) (aBase w) z y ulookup_ctrl_idx = true
    unfold inplaceAccInput inplaceWorkInput
    rw [if_neg (by unfold bBase ulookup_ctrl_idx; omega), if_pos rfl]
  · intro p hp hna hnb hpc
    simp only [inplaceAccInput, inplaceWorkInput, encodeReg, ulookup_ctrl_idx, aBase, bBase] at *
    rw [hbits]
    split_ifs <;> rfl

/-- `inplaceAccInput` with `accBase = aBase`, `yBase = bBase` is scratch-clean (symmetric). -/
theorem scratchClean_inplaceAccInput_aAcc (w bits numWin z y : Nat) (hbits : numWin * w = bits) :
    scratchClean w bits (inplaceAccInput w bits numWin (aBase w) (bBase w bits) z y) := by
  refine ⟨?_, ?_⟩
  · show inplaceAccInput w bits numWin (aBase w) (bBase w bits) z y ulookup_ctrl_idx = true
    unfold inplaceAccInput inplaceWorkInput
    rw [if_neg (by unfold aBase ulookup_ctrl_idx; omega), if_pos rfl]
  · intro p hp hna hnb hpc
    simp only [inplaceAccInput, inplaceWorkInput, encodeReg, ulookup_ctrl_idx, aBase, bBase] at *
    rw [hbits]
    split_ifs <;> rfl

/-! ## §2. The control weights `β` at the clean control `xCtrlGid`. -/

/-- The pass-B control weight at the clean control `xCtrlGid bBase aBase ja` collapses to the
    a-block window indicator at `ja`. -/
theorem betaB_xCtrlGid (w bits numWin N cm xa ja : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hja : ja < 2 ^ bits) :
    betaB w bits N cm xa (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja).val
      = if (⟨ja, hja⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xa
          then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0 := by
  have hsc : scratchClean w bits (ctrlFunB w bits
      (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja).val) := by
    refine (scratchClean_congr_offBlocks w bits _
      (inplaceAccInput w bits numWin (bBase w bits) (aBase w) 0 ja) ?_).mpr
      (scratchClean_inplaceAccInput_bAcc w bits numWin 0 ja hbits)
    intro p hp _ _
    exact assembleEGid_xCtrlGid w bits numWin (bBase w bits) (aBase w) ja 0 p
      (pass1_accfit w bits) hp
  unfold betaB
  rw [if_pos hsc,
      show (⟨decodeReg (fun i => aBase w + i) bits
            (ctrlFunB w bits (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja).val),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) = ⟨ja, hja⟩ from
        Fin.ext (leg1_xval_roundtrip w bits numWin ja hw hbits hja)]

/-- The pass-A control weight at the clean control `xCtrlGid aBase bBase jb` collapses to the
    b-block window indicator at `jb`. -/
theorem betaA_xCtrlGid (w bits numWin N cm xb jb : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hjb : jb < 2 ^ bits) :
    betaA w bits N cm xb (xCtrlGid w bits numWin (aBase w) (bBase w bits) jb).val
      = if (⟨jb, hjb⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xb
          then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0 := by
  have hsc : scratchClean w bits (ctrlFunA w bits
      (xCtrlGid w bits numWin (aBase w) (bBase w bits) jb).val) := by
    refine (scratchClean_congr_offBlocks w bits _
      (inplaceAccInput w bits numWin (aBase w) (bBase w bits) 0 jb) ?_).mpr
      (scratchClean_inplaceAccInput_aAcc w bits numWin 0 jb hbits)
    intro p hp _ _
    exact assembleEGid_xCtrlGid w bits numWin (aBase w) (bBase w bits) jb 0 p
      (pass2_accfit w bits) hp
  unfold betaA
  rw [if_pos hsc,
      show (⟨decodeReg (fun i => bBase w bits + i) bits
            (ctrlFunA w bits (xCtrlGid w bits numWin (aBase w) (bBase w bits) jb).val),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) = ⟨jb, hjb⟩ from
        Fin.ext (leg2_xval_roundtrip w bits numWin jb hw hbits hjb)]

/-! ## §3. The eGid-branch amplitude of `cosetInputVec` (product of two window indicators). -/

/-- **`cosetInputVec` at an INPUT (bBase) eGid branch.**  Reading the two-register coset
    input at the input branch `(a = ja, b = jb)` gives the product of the a-block window
    indicator (at `xa`) and the b-block window indicator (at `xb`). -/
theorem cosetInputVec_at_bBase (w bits numWin N cm xa xb ja jb : Nat) (hw : 0 < w)
    (hbits : numWin * w = bits) (hja : ja < 2 ^ bits) (hjb : jb < 2 ^ bits) :
    cosetInputVec w bits N cm xa xb (eGid w bits (bBase w bits) (pass1_accfit w bits)
        (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja, ⟨jb, hjb⟩)) 0
      = (if (⟨ja, hja⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xa
          then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
      * (if (⟨jb, hjb⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xb
          then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0) := by
  have h1 : cosetInputTwoReg w bits N cm xa xb (eGid w bits (bBase w bits) (pass1_accfit w bits)
        (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja, ⟨jb, hjb⟩)) 0
      = betaB w bits N cm xa (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja).val
        * cosetState (2 ^ bits) N cm xb ⟨jb, hjb⟩ 0 :=
    congrFun (congrFun (branchOfE_cosetInputTwoReg_passB w bits N cm xa xb
      (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja)) ⟨jb, hjb⟩) 0
  show cosetInputTwoReg w bits N cm xa xb _ 0 = _
  rw [h1, betaB_xCtrlGid w bits numWin N cm xa ja hw hbits hja]
  congr 1

/-- **`cosetInputVec` at an OUTPUT (aBase) eGid branch.**  Reading the coset input at the
    output branch `(a = data, b = mult)` gives the product of the a-block window indicator
    (at `xa`, on the data factor) and the b-block window indicator (at `xb`, on `mult`). -/
theorem cosetInputVec_at_aBase (w bits numWin N cm xa xb mult data : Nat) (hw : 0 < w)
    (hbits : numWin * w = bits) (hmult : mult < 2 ^ bits) (hdata : data < 2 ^ bits) :
    cosetInputVec w bits N cm xa xb (eGid w bits (aBase w) (pass2_accfit w bits)
        (xCtrlGid w bits numWin (aBase w) (bBase w bits) mult, ⟨data, hdata⟩)) 0
      = (if (⟨data, hdata⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xa
          then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
      * (if (⟨mult, hmult⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xb
          then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0) := by
  have h1 : cosetInputTwoReg w bits N cm xa xb (eGid w bits (aBase w) (pass2_accfit w bits)
        (xCtrlGid w bits numWin (aBase w) (bBase w bits) mult, ⟨data, hdata⟩)) 0
      = betaA w bits N cm xb (xCtrlGid w bits numWin (aBase w) (bBase w bits) mult).val
        * cosetState (2 ^ bits) N cm xa ⟨data, hdata⟩ 0 :=
    congrFun (congrFun (branchOfE_cosetInputTwoReg_passA w bits N cm xa xb
      (xCtrlGid w bits numWin (aBase w) (bBase w bits) mult)) ⟨data, hdata⟩) 0
  show cosetInputTwoReg w bits N cm xa xb _ 0 = _
  rw [h1, betaA_xCtrlGid w bits numWin N cm xb mult hw hbits hmult, mul_comm]
  congr 1

/-! ## §4. Good-branch amplitude equality (input branch ↦ output branch, equal mass). -/

/-- **GOOD-BRANCH AMPLITUDE EQUALITY.**  For a good branch pair, the input amplitude at
    `(a = ja, b = jb)` equals the target amplitude at the composed output branch
    `(a = jb', b = modSub)`: both are `1/√(2^cm) · 1/√(2^cm)` because all four blocks lie in
    their windows (`ja ∈ window x`, `jb ∈ window 0`, `jb' ∈ window ((k·x)%N)`,
    `modSub ∈ window 0`).  This is the per-branch heart of the agree-off. -/
theorem good_branch_amplitude_eq (w bits numWin N cm x k ja jb jb' modSub : Nat) (hw : 0 < w)
    (hbits : numWin * w = bits) (hja : ja < 2 ^ bits) (hjb : jb < 2 ^ bits)
    (hjb' : jb' < 2 ^ bits) (hmod : modSub < 2 ^ bits)
    (hjaW : (⟨ja, hja⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm x)
    (hjbW : (⟨jb, hjb⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm 0)
    (hjb'W : (⟨jb', hjb'⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm ((k * x) % N))
    (hmodW : (⟨modSub, hmod⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm 0) :
    cosetInputVec w bits N cm x 0 (eGid w bits (bBase w bits) (pass1_accfit w bits)
        (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja, ⟨jb, hjb⟩)) 0
      = cosetInputVec w bits N cm ((k * x) % N) 0 (eGid w bits (aBase w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (aBase w) (bBase w bits) modSub, ⟨jb', hjb'⟩)) 0 := by
  rw [cosetInputVec_at_bBase w bits numWin N cm x 0 ja jb hw hbits hja hjb,
      cosetInputVec_at_aBase w bits numWin N cm ((k * x) % N) 0 modSub jb' hw hbits hmod hjb',
      if_pos hjaW, if_pos hjbW, if_pos hjb'W, if_pos hmodW]

/-! ## §5. The agree-off wrapper: support value + good→target. -/

/-- On its support, `cosetInputVec` takes the single value `1/√(2^cm) · 1/√(2^cm)`. -/
theorem cosetInputVec_nonzero_eq (w bits N cm xa xb : Nat) (idx : Fin (2 ^ cosetDim w bits))
    (h : cosetInputVec w bits N cm xa xb idx 0 ≠ 0) :
    cosetInputVec w bits N cm xa xb idx 0
      = ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) * ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) := by
  classical
  obtain ⟨hsc, hA, hB⟩ := cosetInputTwoReg_support_nonzero w bits N cm xa xb idx 0 h
  have hV : cosetInputTwoReg w bits N cm xa xb idx 0
      = (if scratchClean w bits (nat_to_funbool (cosetDim w bits) idx.val) then
          (if (⟨decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val),
              decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xa
            then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
          * (if (⟨decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val),
              decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xb
            then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
        else 0) := rfl
  show cosetInputTwoReg w bits N cm xa xb idx 0 = _
  rw [hV, if_pos hsc, if_pos hA, if_pos hB]

/-- **Good inputs map into the target support.**  For an input-support index whose decoded
    branch is a `goodPair`, the composed gate's image lies in the target support — its target
    amplitude equals the (nonzero) input amplitude.  This is where the composed branch action
    `gidneyInPlaceWithSwap_branch_action` and `good_branch_amplitude_eq` are load-bearing. -/
theorem good_input_maps_to_target (w bits numWin N cm k kInv x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfit : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (idx : Fin (2 ^ cosetDim w bits))
    (hidx : cosetInputVec w bits N cm x 0 idx 0 ≠ 0)
    (hgood : goodPair w bits numWin N cm k x TfamK TfamKinv
        (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val))
        (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val))) :
    cosetInputVec w bits N cm ((k * x) % N) 0
        (gateToPerm (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin) (cosetDim w bits)
          (gidneyInPlaceWithSwap_wellTyped w bits TfamK TfamKinv numWin hw hbits) idx) 0 ≠ 0 := by
  obtain ⟨hsc, hA, hB⟩ := cosetInputTwoReg_support_nonzero w bits N cm x 0 idx 0 hidx
  set ja := decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val) with hjadef
  set z := decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val) with hzdef
  have hja : ja < 2 ^ bits := decodeReg_lt_two_pow _ _ _
  have hz : z < 2 ^ bits := decodeReg_lt_two_pow _ _ _
  have hidxeq : idx = eGid w bits (bBase w bits) (pass1_accfit w bits)
      (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja, ⟨z, hz⟩) :=
    P_as_eGid_image w bits numWin ja z hw hbits hz idx hsc hjadef.symm hzdef.symm
  obtain ⟨hjb'W, hmodW⟩ := gidneyTwoRegInPlace_agree_off w bits numWin N cm k kInv x TfamK TfamKinv
    hTfamK hTfamKinv hbits hN hxN hkkinv hfit ja z hja hz hA hB hgood
  have hJB' : (z + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits < 2 ^ bits :=
    Nat.mod_lt _ (by positivity)
  have hMOD : modSub bits ja (∑ j ∈ Finset.range numWin, TfamKinv j
      (window w ((z + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j)) < 2 ^ bits :=
    Nat.mod_lt _ (by positivity)
  have heq := good_branch_amplitude_eq w bits numWin N cm x k ja z
    ((z + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits)
    (modSub bits ja (∑ j ∈ Finset.range numWin, TfamKinv j
      (window w ((z + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j)))
    hw hbits hja hz hJB' hMOD hA hB (hjb'W hJB') (hmodW hMOD)
  rw [hidxeq] at hidx
  rw [heq] at hidx
  have hσ : gateToPerm (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin) (cosetDim w bits)
        (gidneyInPlaceWithSwap_wellTyped w bits TfamK TfamKinv numWin hw hbits) idx
      = eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits)
              (modSub bits ja (∑ j ∈ Finset.range numWin, TfamKinv j
                (window w ((z + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j))),
            ⟨(z + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits,
              Nat.mod_lt _ (by positivity)⟩) := by
    rw [hidxeq]
    exact gidneyInPlaceWithSwap_branch_action w bits numWin TfamK TfamKinv ja z hw hbits hja hz
  rw [hσ]
  exact hidx

/-! ## §5b. The bad set as TOP-LEVEL defs (frozen, single source of truth — no drift). -/

/-- The composed-gate basis permutation `σ = gateToPerm gidneyInPlaceWithSwap`. -/
noncomputable def inplaceSigma (w bits numWin : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) : Equiv.Perm (Fin (2 ^ cosetDim w bits)) :=
  gateToPerm (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin) (cosetDim w bits)
    (gidneyInPlaceWithSwap_wellTyped w bits TfamK TfamKinv numWin hw hbits)

open Classical in
/-- The INPUT support: indices where `cosetInputVec x 0` is nonzero. -/
noncomputable def inplaceInputSupp (w bits N cm x : Nat) : Finset (Fin (2 ^ cosetDim w bits)) :=
  Finset.univ.filter (fun i => cosetInputVec w bits N cm x 0 i 0 ≠ 0)

open Classical in
/-- The TARGET (output) support: indices where `cosetInputVec ((k·x)%N) 0` is nonzero. -/
noncomputable def inplaceTargetSupp (w bits N cm k x : Nat) : Finset (Fin (2 ^ cosetDim w bits)) :=
  Finset.univ.filter (fun i => cosetInputVec w bits N cm ((k * x) % N) 0 i 0 ≠ 0)

open Classical in
/-- GOOD input branches: in the input support, with a `goodPair` decode. -/
noncomputable def inplaceGoodIn (w bits numWin N cm k x : Nat) (TfamK TfamKinv : Nat → Nat → Nat) :
    Finset (Fin (2 ^ cosetDim w bits)) :=
  Finset.univ.filter (fun idx => cosetInputVec w bits N cm x 0 idx 0 ≠ 0
    ∧ goodPair w bits numWin N cm k x TfamK TfamKinv
        (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val))
        (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val)))

open Classical in
/-- BAD input branches: in the input support, with a non-`goodPair` decode. -/
noncomputable def inplaceBadIn (w bits numWin N cm k x : Nat) (TfamK TfamKinv : Nat → Nat → Nat) :
    Finset (Fin (2 ^ cosetDim w bits)) :=
  Finset.univ.filter (fun idx => cosetInputVec w bits N cm x 0 idx 0 ≠ 0
    ∧ ¬ goodPair w bits numWin N cm k x TfamK TfamKinv
        (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val))
        (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val)))

/-- **THE bad set** `B = (targetSupp \ σ(goodIn)) ∪ (σ(badIn) \ targetSupp)` — frozen top-level. -/
noncomputable def inplaceBadSetB (w bits numWin N cm k x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) : Finset (Fin (2 ^ cosetDim w bits)) :=
  (inplaceTargetSupp w bits N cm k x \
      (inplaceGoodIn w bits numWin N cm k x TfamK TfamKinv).image
        (inplaceSigma w bits numWin TfamK TfamKinv hw hbits))
  ∪ ((inplaceBadIn w bits numWin N cm k x TfamK TfamKinv).image
        (inplaceSigma w bits numWin TfamK TfamKinv hw hbits)
      \ inplaceTargetSupp w bits N cm k x)

/-- The input support partitions into good ∪ bad (same leading nonzero conjunct, `goodPair` split). -/
theorem inplaceInputSupp_eq_union (w bits numWin N cm k x : Nat) (TfamK TfamKinv : Nat → Nat → Nat) :
    inplaceInputSupp w bits N cm x
      = inplaceGoodIn w bits numWin N cm k x TfamK TfamKinv
        ∪ inplaceBadIn w bits numWin N cm k x TfamK TfamKinv := by
  classical
  ext idx
  simp only [inplaceInputSupp, inplaceGoodIn, inplaceBadIn, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases hg : goodPair w bits numWin N cm k x TfamK TfamKinv
      (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val))
      (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val))
  · constructor
    · intro h; exact Or.inl ⟨h, hg⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · constructor
    · intro h; exact Or.inr ⟨h, hg⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

/-- Good and bad input branches are disjoint (`goodPair` vs `¬goodPair`). -/
theorem inplaceGoodIn_disjoint_badIn (w bits numWin N cm k x : Nat) (TfamK TfamKinv : Nat → Nat → Nat) :
    Disjoint (inplaceGoodIn w bits numWin N cm k x TfamK TfamKinv)
      (inplaceBadIn w bits numWin N cm k x TfamK TfamKinv) := by
  classical
  rw [Finset.disjoint_left]
  intro idx hg hb
  simp only [inplaceGoodIn, inplaceBadIn, Finset.mem_filter] at hg hb
  exact hb.2.2 hg.2.2

/-! ## §5c. The two legs `Bfwd`/`Brev` of the bad set (D2.0 structural setup). -/

open Classical in
/-- FORWARD-overflow leg: bad input branches whose forward sum overflows the window
    (`¬` of `goodPair`'s first clause). -/
noncomputable def inplaceBfwd (w bits numWin N cm k x : Nat) (TfamK TfamKinv : Nat → Nat → Nat) :
    Finset (Fin (2 ^ cosetDim w bits)) :=
  Finset.univ.filter (fun idx => cosetInputVec w bits N cm x 0 idx 0 ≠ 0
    ∧ ¬ (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val)
          + (∑ j ∈ Finset.range numWin, TfamK j
              (window w (decodeReg (fun i => aBase w + i) bits
                (nat_to_funbool (cosetDim w bits) idx.val)) j))
          < (k * x) % N + 2 ^ cm * N))

open Classical in
/-- REVERSE-underflow leg: bad input branches whose reverse sum underflows
    (`¬` of `goodPair`'s second clause). -/
noncomputable def inplaceBrev (w bits numWin N cm k x : Nat) (TfamK TfamKinv : Nat → Nat → Nat) :
    Finset (Fin (2 ^ cosetDim w bits)) :=
  Finset.univ.filter (fun idx => cosetInputVec w bits N cm x 0 idx 0 ≠ 0
    ∧ ¬ ((∑ j ∈ Finset.range numWin, TfamKinv j
            (window w ((decodeReg (fun i => bBase w bits + i) bits
                (nat_to_funbool (cosetDim w bits) idx.val)
              + ∑ j ∈ Finset.range numWin, TfamK j
                  (window w (decodeReg (fun i => aBase w + i) bits
                    (nat_to_funbool (cosetDim w bits) idx.val)) j)) % 2 ^ bits) j))
          ≤ decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val)))

/-- **Exact decomposition** (D2.0): the bad input set is the union of the two legs.  Same
    object — `inplaceBadIn = inplaceBfwd ∪ inplaceBrev` — via `goodPair = A ∧ B`,
    `not_and_or`, `Finset.filter_or`. -/
theorem inplaceBadIn_eq_union (w bits numWin N cm k x : Nat) (TfamK TfamKinv : Nat → Nat → Nat) :
    inplaceBadIn w bits numWin N cm k x TfamK TfamKinv
      = inplaceBfwd w bits numWin N cm k x TfamK TfamKinv
        ∪ inplaceBrev w bits numWin N cm k x TfamK TfamKinv := by
  classical
  ext idx
  simp only [inplaceBadIn, inplaceBfwd, inplaceBrev, Finset.mem_filter, Finset.mem_union,
    Finset.mem_univ, true_and, goodPair, not_and_or]
  tauto

/-! ## §6. THE FULL POINTWISE AGREE-OFF. -/

/-- **THE FULL POINTWISE AGREE-OFF for `gidneyInPlaceWithSwap`.**  Off the symmetric-difference
    bad set `B = (targetSupport \ σ(goodInput)) ∪ (σ(badInput) \ targetSupport)` (raw output
    basis indices; `σ = gateToPerm`), the composed gate carries the two-register coset input
    `cosetInputVec x 0` to the post-swap target `cosetInputVec ((k·x)%N) 0` EXACTLY — physical a
    holds the product, physical b is cleared.  No mass bound, no `normSqDist`; built from the
    composed branch action `gidneyInPlaceWithSwap_branch_action` and `good_branch_amplitude_eq`,
    NOT from the scalar norm theorem. -/
theorem gidneyInPlaceWithSwap_agree_off (w bits numWin N cm k kInv x : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfit : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits) :
    ∃ B : Finset (Fin (2 ^ cosetDim w bits)),
      ∀ i : Fin (2 ^ cosetDim w bits), i ∉ B →
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin))
          * cosetInputVec w bits N cm x 0) i 0
          = cosetInputVec w bits N cm ((k * x) % N) 0 i 0 := by
  classical
  set σ := gateToPerm (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin) (cosetDim w bits)
    (gidneyInPlaceWithSwap_wellTyped w bits TfamK TfamKinv numWin hw hbits) with hσdef
  set targetSupp : Finset (Fin (2 ^ cosetDim w bits)) :=
    Finset.univ.filter (fun i => cosetInputVec w bits N cm ((k * x) % N) 0 i 0 ≠ 0) with htgtdef
  set goodIn : Finset (Fin (2 ^ cosetDim w bits)) :=
    Finset.univ.filter (fun idx => cosetInputVec w bits N cm x 0 idx 0 ≠ 0
      ∧ goodPair w bits numWin N cm k x TfamK TfamKinv
          (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val))
          (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val)))
    with hgooddef
  set badIn : Finset (Fin (2 ^ cosetDim w bits)) :=
    Finset.univ.filter (fun idx => cosetInputVec w bits N cm x 0 idx 0 ≠ 0
      ∧ ¬ goodPair w bits numWin N cm k x TfamK TfamKinv
          (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val))
          (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val)))
    with hbaddef
  refine ⟨inplaceBadSetB w bits numWin N cm k x TfamK TfamKinv hw hbits, ?_⟩
  -- the frozen `inplaceBadSetB` is DEFINITIONALLY this symmetric difference (same-B guard)
  show ∀ i : Fin (2 ^ cosetDim w bits),
      i ∉ (targetSupp \ goodIn.image σ) ∪ (badIn.image σ \ targetSupp) →
      (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
          (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin)) * cosetInputVec w bits N cm x 0) i 0
        = cosetInputVec w bits N cm ((k * x) % N) 0 i 0
  intro i hiB
  rw [uc_eval_eq_permState (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin) (cosetDim w bits)
    (gidneyInPlaceWithSwap_wellTyped w bits TfamK TfamKinv numWin hw hbits)]
  show cosetInputVec w bits N cm x 0 (σ.symm i) 0 = cosetInputVec w bits N cm ((k * x) % N) 0 i 0
  simp only [Finset.mem_union, Finset.mem_sdiff, not_or, not_and, not_not] at hiB
  obtain ⟨hiB1, hiB2⟩ := hiB
  by_cases hin : cosetInputVec w bits N cm x 0 (σ.symm i) 0 = 0
  · -- LHS = 0 ⇒ show RHS = 0 (else `i` would have a good preimage in the support)
    rw [hin]; symm
    by_contra hRne
    have hitgt : i ∈ targetSupp := by
      rw [htgtdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hRne⟩
    obtain ⟨P, hPgood, hPσ⟩ := Finset.mem_image.mp (hiB1 hitgt)
    have hsi : σ.symm i = P := by rw [← hPσ, Equiv.symm_apply_apply]
    rw [hsi] at hin
    rw [hgooddef, Finset.mem_filter] at hPgood
    exact hPgood.2.1 hin
  · -- LHS ≠ 0 ⇒ both sides equal the single support value `c·c`
    have hLc := cosetInputVec_nonzero_eq w bits N cm x 0 (σ.symm i) hin
    by_cases hgood : goodPair w bits numWin N cm k x TfamK TfamKinv
        (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) (σ.symm i).val))
        (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) (σ.symm i).val))
    · -- good preimage ⇒ `i` is in the target support, with equal amplitude
      have hgi := good_input_maps_to_target w bits numWin N cm k kInv x TfamK TfamKinv
        hTfamK hTfamKinv hw hbits hN hxN hkkinv hfit (σ.symm i) hin hgood
      rw [← hσdef, Equiv.apply_symm_apply] at hgi
      rw [hLc, cosetInputVec_nonzero_eq w bits N cm ((k * x) % N) 0 i hgi]
    · -- bad preimage ⇒ `i ∈ σ(badInput)`; off `B` forces `i ∈ targetSupport`, equal amplitude
      have hPbad : σ.symm i ∈ badIn := by
        rw [hbaddef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hin, hgood⟩
      have hibad : i ∈ badIn.image σ :=
        Finset.mem_image.mpr ⟨σ.symm i, hPbad, Equiv.apply_symm_apply σ i⟩
      have hitgt := hiB2 hibad
      rw [htgtdef, Finset.mem_filter] at hitgt
      rw [hLc, cosetInputVec_nonzero_eq w bits N cm ((k * x) % N) 0 i hitgt.2]

/-! ## §7. hred — the exact reduction the mass transport consumes (Checkpoint B). -/

/-- **hred** (Checkpoint B, for the EXACT frozen `inplaceBadSetB`).  A nonzero-input preimage of
    `B` under `σ.symm` lies in `badIn`.  Pure Finset/`Equiv` bookkeeping: a support index is good
    or bad; a good one would map into `σ(goodIn)`, contradicting membership in `B` (whose left
    part sdiff-excludes `σ(goodIn)` and whose right part is disjoint from `σ(goodIn)` by `σ`
    injectivity + good/bad disjointness). -/
theorem inplace_hred (w bits numWin N cm k x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (j : Fin (2 ^ cosetDim w bits))
    (hj : j ∈ (inplaceBadSetB w bits numWin N cm k x TfamK TfamKinv hw hbits).image
        (inplaceSigma w bits numWin TfamK TfamKinv hw hbits).symm)
    (hjne : cosetInputVec w bits N cm x 0 j 0 ≠ 0) :
    j ∈ inplaceBadIn w bits numWin N cm k x TfamK TfamKinv := by
  classical
  obtain ⟨i, hiB, hσ⟩ := Finset.mem_image.mp hj
  have hsupp : j ∈ inplaceGoodIn w bits numWin N cm k x TfamK TfamKinv
      ∪ inplaceBadIn w bits numWin N cm k x TfamK TfamKinv := by
    rw [← inplaceInputSupp_eq_union]
    simp only [inplaceInputSupp, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hjne⟩
  rcases Finset.mem_union.mp hsupp with hg | hb
  · exfalso
    have hij : inplaceSigma w bits numWin TfamK TfamKinv hw hbits j = i := by
      rw [← hσ, Equiv.apply_symm_apply]
    have hisg : i ∈ (inplaceGoodIn w bits numWin N cm k x TfamK TfamKinv).image
        (inplaceSigma w bits numWin TfamK TfamKinv hw hbits) :=
      Finset.mem_image.mpr ⟨j, hg, hij⟩
    simp only [inplaceBadSetB, Finset.mem_union] at hiB
    rcases hiB with hL | hR
    · exact (Finset.mem_sdiff.mp hL).2 hisg
    · obtain ⟨Pb, hPb, hPbσ⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hR).1
      have hPbj : Pb = j :=
        (inplaceSigma w bits numWin TfamK TfamKinv hw hbits).injective (by rw [hPbσ, hij])
      rw [hPbj] at hPb
      exact Finset.disjoint_left.mp
        (inplaceGoodIn_disjoint_badIn w bits numWin N cm k x TfamK TfamKinv) hg hPb
  · exact hb

end FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree
