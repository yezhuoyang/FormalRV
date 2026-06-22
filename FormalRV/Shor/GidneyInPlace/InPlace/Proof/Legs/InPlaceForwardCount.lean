/-
  FormalRV.Shor.GidneyInPlace.InPlaceForwardCount
  ─────────────────────────────────────────────────
  PACKAGING checkpoint D2.1: the FORWARD leg cardinality + mass.

      card (inplaceBfwd) ≤ numWin · 2^cm        (the eGid product fibration)
      bornWeightOn (cosetInputVec x 0) inplaceBfwd ≤ numWin / 2^cm   (× the D1 per-point mass)

  Forward count only (D3 reverse is a separate checkpoint).  No `normSqDist`, no single-register
  bad set, no redefinition of `inplaceBfwd` (the exact top-level leg from `InPlaceComposedAgree`).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Mass.InPlaceComposedMass
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceReverseRekey

namespace FormalRV.Shor.GidneyInPlace.InPlaceForwardCount

open FormalRV.Framework (nat_to_funbool)
open FormalRV.BQAlgo (decodeReg)
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.WindowedArith (window tableValue)
open FormalRV.Shor.WindowedCircuit (decodeReg_lt_two_pow)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow cosetWindow_card)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceReverseRekey (windowSum_wrap_le)
open FormalRV.Shor.GidneyInPlace.InPlaceEndpoint (endpoint_residue_modN)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg (aBase bBase)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate (eGid pass1_accfit)
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput (xCtrlGid)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree (inplaceBfwd)
open FormalRV.Shor.GidneyInPlace.InPlaceLeg1 (P_as_eGid_image cosetInputTwoReg_support_nonzero)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedMass (cosetInputVec_bornWeight_le_card)

/-! ## §1. The per-`ja` bad-`jb` count `≤ numWin`. -/

/-- **Per-`ja` forward-overflow count.**  For a fixed multiplier branch `ja ∈ window x`, the number
    of accumulator branches `jb ∈ window 0` whose forward sum overflows (`¬` of `goodPair`'s first
    clause) is at most `numWin` — the wrap count `s(ja) ≤ numWin`.  Injection `jb ↦ jb.val / N` into
    `Ico (2^cm - s) (2^cm)`, mirroring `windowDiff_card_le`. -/
theorem fwd_badjb_card_le (w bits numWin N cm k x ja : Nat) (TfamK : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hbits : numWin * w = bits) (hN : 0 < N)
    (hja : ja < 2 ^ bits)
    (hja_win : (⟨ja, hja⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm x) :
    (Finset.univ.filter (fun jb : Fin (2 ^ bits) =>
        jb ∈ cosetWindow (2 ^ bits) N cm 0
        ∧ ¬ (jb.val + (∑ j ∈ Finset.range numWin, TfamK j (window w ja j))
              < (k * x) % N + 2 ^ cm * N))).card ≤ numWin := by
  classical
  have hpow : (2 : Nat) ^ bits = (2 ^ w) ^ numWin := by
    rw [← hbits, Nat.mul_comm numWin w, Nat.pow_mul]
  have hjalt : ja < (2 ^ w) ^ numWin := by rw [← hpow]; exact hja
  obtain ⟨p, hp, hja_eq⟩ := (mem_cosetWindow (2 ^ bits) N cm x hN ⟨ja, hja⟩).mp hja_win
  replace hja_eq : ja = x + p * N := hja_eq
  have hSfwd_mod : (∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % N = (k * x) % N := by
    have h := endpoint_residue_modN k N w numWin ja 0 TfamK hTfamK hN hjalt
    rw [Nat.zero_add, Nat.zero_add] at h
    rw [h, hja_eq, Nat.mul_add, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
  obtain ⟨s, hs_eq⟩ :
      ∃ s, (∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) = (k * x) % N + s * N :=
    ⟨(∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) / N, by
      have hdm := Nat.div_add_mod (∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) N
      rw [hSfwd_mod] at hdm
      have hc : N * ((∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) / N)
          = ((∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) / N) * N := Nat.mul_comm _ _
      omega⟩
  have hs_le : s ≤ numWin := windowSum_wrap_le k N w numWin ja ((k * x) % N) s TfamK hTfamK hN hs_eq
  have hScard : (Finset.Ico (2 ^ cm - s) (2 ^ cm)).card ≤ numWin := by
    rw [Nat.card_Ico]; omega
  refine le_trans (Finset.card_le_card_of_injOn (fun jb => jb.val / N) ?_ ?_) hScard
  · intro jb hjb
    rw [Finset.mem_coe, Finset.mem_filter] at hjb
    obtain ⟨_, hjbwin, hnA⟩ := hjb
    obtain ⟨qb, hqb, hjbval⟩ := (mem_cosetWindow (2 ^ bits) N cm 0 hN jb).mp hjbwin
    rw [Nat.zero_add] at hjbval
    have hdiv : jb.val / N = qb := by rw [hjbval, Nat.mul_div_cancel _ hN]
    rw [not_lt, hjbval, hs_eq] at hnA
    have hqbs : 2 ^ cm ≤ qb + s := by
      have h1 : (2 ^ cm) * N ≤ (qb + s) * N := by rw [Nat.add_mul]; omega
      exact Nat.le_of_mul_le_mul_right h1 hN
    simp only [Finset.mem_coe, Finset.mem_Ico, hdiv]
    exact ⟨by omega, hqb⟩
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    obtain ⟨qa, _, haval⟩ := (mem_cosetWindow (2 ^ bits) N cm 0 hN a).mp ha.2.1
    obtain ⟨qb, _, hbval⟩ := (mem_cosetWindow (2 ^ bits) N cm 0 hN b).mp hb.2.1
    rw [Nat.zero_add] at haval hbval
    have hqa : a.val / N = qa := by rw [haval, Nat.mul_div_cancel _ hN]
    have hqb : b.val / N = qb := by rw [hbval, Nat.mul_div_cancel _ hN]
    apply Fin.ext
    rw [haval, hbval]
    have : qa = qb := by rw [← hqa, ← hqb]; exact hab
    rw [this]

/-! ## §2. The forward leg cardinality (eGid fibration over `decode-a`). -/

/-- **Forward leg cardinality** (D2.1).  `card (inplaceBfwd) ≤ numWin · 2^cm`: fiber over the
    a-decode `ja ∈ window x` (card `2^cm`), each fiber injects (via the b-decode, `P_as_eGid_image`)
    into the per-`ja` bad-`jb` set (`≤ numWin` by `fwd_badjb_card_le`). -/
theorem inplaceBfwd_card_le (w bits numWin N cm k x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hxfit : x + (2 ^ cm - 1) * N < 2 ^ bits) :
    (inplaceBfwd w bits numWin N cm k x TfamK TfamKinv).card ≤ numWin * 2 ^ cm := by
  classical
  set f : Fin (2 ^ cosetDim w bits) → Fin (2 ^ bits) :=
    fun idx => ⟨decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val),
        decodeReg_lt_two_pow _ _ _⟩ with hf
  have hmaps : ∀ idx ∈ inplaceBfwd w bits numWin N cm k x TfamK TfamKinv,
      f idx ∈ cosetWindow (2 ^ bits) N cm x := by
    intro idx hidx
    simp only [inplaceBfwd, Finset.mem_filter] at hidx
    exact (cosetInputTwoReg_support_nonzero w bits N cm x 0 idx 0 hidx.2.1).2.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ ja ∈ cosetWindow (2 ^ bits) N cm x,
        ((inplaceBfwd w bits numWin N cm k x TfamK TfamKinv).filter (fun idx => f idx = ja)).card
      ≤ ∑ _ja ∈ cosetWindow (2 ^ bits) N cm x, numWin := Finset.sum_le_sum fun ja hja => ?_
    _ = numWin * 2 ^ cm := by
        rw [Finset.sum_const, cosetWindow_card (2 ^ bits) N cm x hN hxfit, smul_eq_mul, Nat.mul_comm]
  refine le_trans (Finset.card_le_card_of_injOn
      (fun idx => (⟨decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))) ?_ ?_)
      (fwd_badjb_card_le w bits numWin N cm k x ja.val TfamK hTfamK hbits hN ja.isLt hja)
  · intro idx hidx
    rw [Finset.mem_coe, Finset.mem_filter] at hidx
    obtain ⟨hidxBfwd, hfja⟩ := hidx
    simp only [inplaceBfwd, Finset.mem_filter] at hidxBfwd
    obtain ⟨hsc, hawin, hbwin⟩ := cosetInputTwoReg_support_nonzero w bits N cm x 0 idx 0 hidxBfwd.2.1
    have hda : decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val)
        = ja.val := congrArg Fin.val hfja
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hbwin, ?_⟩
    have hnA := hidxBfwd.2.2
    rw [hda] at hnA
    exact hnA
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    obtain ⟨haBfwd, hfa⟩ := ha
    obtain ⟨hbBfwd, hfb⟩ := hb
    simp only [inplaceBfwd, Finset.mem_filter] at haBfwd hbBfwd
    obtain ⟨hsca, _, _⟩ := cosetInputTwoReg_support_nonzero w bits N cm x 0 a 0 haBfwd.2.1
    obtain ⟨hscb, _, _⟩ := cosetInputTwoReg_support_nonzero w bits N cm x 0 b 0 hbBfwd.2.1
    have hdaa : decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) a.val)
        = ja.val := congrArg Fin.val hfa
    have hdab : decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) b.val)
        = ja.val := congrArg Fin.val hfb
    have hdb : decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) a.val)
        = decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) b.val) :=
      congrArg Fin.val hab
    have hza := P_as_eGid_image w bits numWin ja.val
      (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) a.val))
      hw hbits (decodeReg_lt_two_pow _ _ _) a hsca hdaa rfl
    have hzb := P_as_eGid_image w bits numWin ja.val
      (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) b.val))
      hw hbits (decodeReg_lt_two_pow _ _ _) b hscb hdab rfl
    rw [hza, hzb]
    congr 2

/-! ## §3. The forward leg mass bound (× D1). -/

/-- **Forward leg Born mass** (D2.1 conclusion).  `bornWeightOn (cosetInputVec x 0) inplaceBfwd
    ≤ numWin / 2^cm` — the D1 per-point mass times the forward cardinality, cancelling one `2^cm`. -/
theorem inplaceBfwd_bornWeight_le (w bits numWin N cm k x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hxfit : x + (2 ^ cm - 1) * N < 2 ^ bits) :
    bornWeightOn (cosetInputVec w bits N cm x 0)
        (inplaceBfwd w bits numWin N cm k x TfamK TfamKinv) ≤ (numWin : ℝ) / 2 ^ cm := by
  have hcard := inplaceBfwd_card_le w bits numWin N cm k x TfamK TfamKinv hTfamK hw hbits hN hxfit
  have hpos : (0 : ℝ) < 2 ^ cm := by positivity
  calc bornWeightOn (cosetInputVec w bits N cm x 0)
          (inplaceBfwd w bits numWin N cm k x TfamK TfamKinv)
      ≤ ((inplaceBfwd w bits numWin N cm k x TfamK TfamKinv).card : ℝ) * (1 / 2 ^ cm * (1 / 2 ^ cm)) :=
        cosetInputVec_bornWeight_le_card w bits N cm x _
    _ ≤ ((numWin * 2 ^ cm : Nat) : ℝ) * (1 / 2 ^ cm * (1 / 2 ^ cm)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
    _ = (numWin : ℝ) / 2 ^ cm := by
        push_cast
        field_simp

end FormalRV.Shor.GidneyInPlace.InPlaceForwardCount
