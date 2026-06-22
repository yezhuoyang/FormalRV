/-
  FormalRV.Shor.GidneyInPlace.InPlaceAgreeOffExplicit — T2: the agree-off
  with the EXACT bad set `inplaceBadSetB` (no existential sibling).
  ════════════════════════════════════════════════════════════════════════════

  `InPlaceComposedAgree.gidneyInPlaceWithSwap_agree_off` proves the off-bad agreement but
  WRAPS the witness in `∃ B`, so a consumer cannot align `B` with the `inplaceBadSetB` that
  the D5 / target-mass theorems use.  This file exposes the EXPLICIT-`B` form (concluding
  `∀ i ∉ inplaceBadSetB, evolved i = target i`), lifting the §6 proof body verbatim; the
  `∃`-version is re-derived from it.  This is the `hagreeB` hypothesis of
  `InPlaceTargetMassLeg.inplaceBadSetB_target_bornWeight_le`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceComposedAgree

namespace FormalRV.Shor.GidneyInPlace.InPlaceAgreeOffExplicit

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.GatePerm (gateToPerm)
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_eq_permState)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg (aBase bBase)
open FormalRV.Shor.GidneyInPlace.InPlaceAgreeOff (goodPair)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate
  (gidneyInPlaceWithSwap gidneyInPlaceWithSwap_wellTyped)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree
  (inplaceBadSetB cosetInputVec_nonzero_eq good_input_maps_to_target)

/-- **T2 — explicit-B agree-off.**  Off the EXACT bad set `inplaceBadSetB` (not an existential
    sibling), the evolved two-register state equals the post-swap target.  Body lifted from the
    §6 `gidneyInPlaceWithSwap_agree_off` proof; `hiB` is converted from the `inplaceBadSetB` form
    to the symmetric-difference form (definitionally equal) up front. -/
theorem gidneyInPlaceWithSwap_agree_off_explicit
    (w bits numWin N cm k kInv x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfit : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (i : Fin (2 ^ cosetDim w bits))
    (hiB : i ∉ inplaceBadSetB w bits numWin N cm k x TfamK TfamKinv hw hbits) :
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
  -- `inplaceBadSetB` is DEFINITIONALLY this symmetric difference (same-B guard).
  have hiB' : i ∉ (targetSupp \ goodIn.image σ) ∪ (badIn.image σ \ targetSupp) := hiB
  rw [uc_eval_eq_permState (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin) (cosetDim w bits)
    (gidneyInPlaceWithSwap_wellTyped w bits TfamK TfamKinv numWin hw hbits)]
  show cosetInputVec w bits N cm x 0 (σ.symm i) 0 = cosetInputVec w bits N cm ((k * x) % N) 0 i 0
  simp only [Finset.mem_union, Finset.mem_sdiff, not_or, not_and, not_not] at hiB'
  obtain ⟨hiB1, hiB2⟩ := hiB'
  by_cases hin : cosetInputVec w bits N cm x 0 (σ.symm i) 0 = 0
  · rw [hin]; symm
    by_contra hRne
    have hitgt : i ∈ targetSupp := by
      rw [htgtdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hRne⟩
    obtain ⟨P, hPgood, hPσ⟩ := Finset.mem_image.mp (hiB1 hitgt)
    have hsi : σ.symm i = P := by rw [← hPσ, Equiv.symm_apply_apply]
    rw [hsi] at hin
    rw [hgooddef, Finset.mem_filter] at hPgood
    exact hPgood.2.1 hin
  · have hLc := cosetInputVec_nonzero_eq w bits N cm x 0 (σ.symm i) hin
    by_cases hgood : goodPair w bits numWin N cm k x TfamK TfamKinv
        (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) (σ.symm i).val))
        (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) (σ.symm i).val))
    · have hgi := good_input_maps_to_target w bits numWin N cm k kInv x TfamK TfamKinv
        hTfamK hTfamKinv hw hbits hN hxN hkkinv hfit (σ.symm i) hin hgood
      rw [← hσdef, Equiv.apply_symm_apply] at hgi
      rw [hLc, cosetInputVec_nonzero_eq w bits N cm ((k * x) % N) 0 i hgi]
    · have hPbad : σ.symm i ∈ badIn := by
        rw [hbaddef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hin, hgood⟩
      have hibad : i ∈ badIn.image σ :=
        Finset.mem_image.mpr ⟨σ.symm i, hPbad, Equiv.apply_symm_apply σ i⟩
      have hitgt := hiB2 hibad
      rw [htgtdef, Finset.mem_filter] at hitgt
      rw [hLc, cosetInputVec_nonzero_eq w bits N cm ((k * x) % N) 0 i hitgt.2]

/-- The original existential form, re-derived from the explicit-`B` lemma. -/
theorem gidneyInPlaceWithSwap_agree_off'
    (w bits numWin N cm k kInv x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
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
          = cosetInputVec w bits N cm ((k * x) % N) 0 i 0 :=
  ⟨inplaceBadSetB w bits numWin N cm k x TfamK TfamKinv hw hbits,
    gidneyInPlaceWithSwap_agree_off_explicit w bits numWin N cm k kInv x TfamK TfamKinv
      hTfamK hTfamKinv hw hbits hN hxN hkkinv hfit⟩

end FormalRV.Shor.GidneyInPlace.InPlaceAgreeOffExplicit
