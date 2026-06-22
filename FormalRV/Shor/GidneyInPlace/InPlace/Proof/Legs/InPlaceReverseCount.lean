/-
  FormalRV.Shor.GidneyInPlace.InPlaceReverseCount
  ─────────────────────────────────────────────────
  PACKAGING checkpoint D3: the REVERSE leg (sharper, `Brev \ Bfwd`) cardinality + mass.

      bornWeightOn (cosetInputVec x 0) (inplaceBrev \ inplaceBfwd) ≤ numWin / 2^cm

  The crux (per the design): FIBER OVER THE b-OUTPUT `jb' ∈ window((k·x)%N)`, NOT over `ja`/`jb`.
  On `Brev \ Bfwd` the forward leg is good (`A` holds), so `jb' = jb + Sfwd` is no-wrap and lands
  in `window((k·x)%N)` (`fwd_jbp_landing`); the reverse-bad count per fixed `jb'` is `≤ t ≤ numWin`
  (`Sinv_residue_decomp`) — D3-free, on the single input state.

  No `normSqDist`, no single-register bad set, no redefinition of the legs.
  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceForwardCount

namespace FormalRV.Shor.GidneyInPlace.InPlaceReverseCount

open FormalRV.Framework (nat_to_funbool)
open FormalRV.BQAlgo (decodeReg)
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.WindowedArith (window tableValue)
open FormalRV.Shor.WindowedCircuit (decodeReg_lt_two_pow)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow cosetWindow_card)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceReverseRekey (Sinv_residue_decomp fwd_jbp_landing)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg (aBase bBase)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate (eGid pass1_accfit)
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput (xCtrlGid)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree (inplaceBfwd inplaceBrev)
open FormalRV.Shor.GidneyInPlace.InPlaceLeg1 (P_as_eGid_image cosetInputTwoReg_support_nonzero)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedMass (cosetInputVec_bornWeight_le_card)

/-! ## §1. The per-`jb'` reverse-underflow count `≤ numWin`. -/

/-- **Per-`jb'` reverse-underflow count.**  For a fixed b-output `jb' ∈ window((k·x)%N)`, the number
    of multiplier branches `ja ∈ window x` with reverse underflow (`ja < Sinv(jb')`) is at most
    `numWin`: `Sinv(jb') = x + t·N` with `t ≤ numWin` (`Sinv_residue_decomp`), `ja = x + p·N`, so the
    underflow is `p < t`.  Injection `ja ↦ (ja.val − x)/N` into `Finset.range t`. -/
theorem rev_badja_card_le (w bits numWin N cm k kInv x jbp : Nat) (TfamKinv : Nat → Nat → Nat)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hjbp : jbp < 2 ^ bits)
    (hjbp_win : (⟨jbp, hjbp⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm ((k * x) % N)) :
    (Finset.univ.filter (fun ja : Fin (2 ^ bits) =>
        ja ∈ cosetWindow (2 ^ bits) N cm x
        ∧ ja.val < (∑ j ∈ Finset.range numWin, TfamKinv j (window w jbp j)))).card ≤ numWin := by
  classical
  have hpow : (2 : Nat) ^ bits = (2 ^ w) ^ numWin := by
    rw [← hbits, Nat.mul_comm numWin w, Nat.pow_mul]
  have hjbplt : jbp < (2 ^ w) ^ numWin := by rw [← hpow]; exact hjbp
  have hjbpmod : jbp % N = (k * x) % N := by
    obtain ⟨r, hr, hjbpval⟩ := (mem_cosetWindow (2 ^ bits) N cm ((k * x) % N) hN ⟨jbp, hjbp⟩).mp hjbp_win
    replace hjbpval : jbp = (k * x) % N + r * N := hjbpval
    rw [hjbpval, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Nat.mod_lt _ hN)]
  obtain ⟨t, ht_le, ht_eq⟩ :=
    Sinv_residue_decomp w numWin N k kInv x jbp TfamKinv hTfamKinv hN hxN hkkinv hjbplt hjbpmod
  have hsub : (Finset.univ.filter (fun ja : Fin (2 ^ bits) =>
        ja ∈ cosetWindow (2 ^ bits) N cm x
        ∧ ja.val < (∑ j ∈ Finset.range numWin, TfamKinv j (window w jbp j)))).card
      ≤ (Finset.range t).card := by
    apply Finset.card_le_card_of_injOn (fun ja => (ja.val - x) / N)
    · intro ja hja
      rw [Finset.mem_coe, Finset.mem_filter] at hja
      obtain ⟨_, hjawin, hlt⟩ := hja
      obtain ⟨p, hp, hjaval⟩ := (mem_cosetWindow (2 ^ bits) N cm x hN ja).mp hjawin
      have hpdiv : (ja.val - x) / N = p := by
        rw [hjaval, Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hN]
      rw [ht_eq, hjaval] at hlt
      simp only [Finset.mem_coe, Finset.mem_range, hpdiv]
      have h1 : p * N < t * N := by omega
      exact lt_of_mul_lt_mul_right h1 (Nat.zero_le N)
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      obtain ⟨pa, _, haval⟩ := (mem_cosetWindow (2 ^ bits) N cm x hN a).mp ha.2.1
      obtain ⟨pb, _, hbval⟩ := (mem_cosetWindow (2 ^ bits) N cm x hN b).mp hb.2.1
      have hpa : (a.val - x) / N = pa := by rw [haval, Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hN]
      have hpb : (b.val - x) / N = pb := by rw [hbval, Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hN]
      apply Fin.ext
      rw [haval, hbval]
      have : pa = pb := by rw [← hpa, ← hpb]; exact hab
      rw [this]
  rw [Finset.card_range] at hsub
  exact le_trans hsub ht_le

/-! ## §2. The reverse leg cardinality (fibration over the b-output `jb'`). -/

/-- **Reverse leg cardinality** (D3, sharper form).  `card (inplaceBrev \ inplaceBfwd) ≤ numWin · 2^cm`:
    fiber over the b-OUTPUT `jb' = (jb + Sfwd) % 2^bits ∈ window((k·x)%N)` (card `2^cm`).  On
    `Brev \ Bfwd` the forward leg is good, so `jb' = jb + Sfwd` is no-wrap (`fwd_jbp_landing`), each
    fiber injects (via the a-decode) into the per-`jb'` reverse-bad set (`≤ numWin`, `rev_badja_card_le`). -/
theorem inplaceBrevSdiff_card_le (w bits numWin N cm k kInv x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfit : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits) :
    ((inplaceBrev w bits numWin N cm k x TfamK TfamKinv)
      \ (inplaceBfwd w bits numWin N cm k x TfamK TfamKinv)).card ≤ numWin * 2 ^ cm := by
  classical
  set g : Fin (2 ^ cosetDim w bits) → Fin (2 ^ bits) :=
    fun idx => ⟨(decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val)
        + ∑ j ∈ Finset.range numWin, TfamK j
            (window w (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val)) j))
        % 2 ^ bits, Nat.mod_lt _ (by positivity)⟩ with hg
  -- Per-index extraction: clean, a-window, no-wrap forward sum, reverse-bad, jb'-window.
  have hext : ∀ idx ∈ (inplaceBrev w bits numWin N cm k x TfamK TfamKinv)
        \ (inplaceBfwd w bits numWin N cm k x TfamK TfamKinv),
      (⟨decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm x
      ∧ decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val)
          + (∑ j ∈ Finset.range numWin, TfamK j (window w
              (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val)) j))
          = (g idx).val
      ∧ decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val)
          < (∑ j ∈ Finset.range numWin, TfamKinv j (window w (g idx).val j))
      ∧ g idx ∈ cosetWindow (2 ^ bits) N cm ((k * x) % N)
      ∧ InPlaceCosetInputTwoReg.scratchClean w bits (nat_to_funbool (cosetDim w bits) idx.val) := by
    intro idx hidx
    rw [Finset.mem_sdiff] at hidx
    obtain ⟨hbrev, hnbfwd⟩ := hidx
    simp only [inplaceBrev, Finset.mem_filter, Finset.mem_univ, true_and] at hbrev
    simp only [inplaceBfwd, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hnbfwd
    obtain ⟨hnz, hnB⟩ := hbrev
    have hA := hnbfwd hnz
    obtain ⟨hsc, hawin, hbwin⟩ := cosetInputTwoReg_support_nonzero w bits N cm x 0 idx 0 hnz
    obtain ⟨r, hr, hraw, hmod⟩ := fwd_jbp_landing w bits numWin N cm k x
      (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val))
      (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val))
      TfamK hTfamK hbits hN hfit (decodeReg_lt_two_pow _ _ _) (decodeReg_lt_two_pow _ _ _)
      hawin hbwin hA
    have hnowrap : decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val)
          + (∑ j ∈ Finset.range numWin, TfamK j (window w
              (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val)) j))
        = (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val)
          + (∑ j ∈ Finset.range numWin, TfamK j (window w
              (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val)) j)))
          % 2 ^ bits := hraw.trans hmod.symm
    have hgval : (g idx).val
        = decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val)
          + (∑ j ∈ Finset.range numWin, TfamK j (window w
              (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val)) j)) := by
      show (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val)
          + (∑ j ∈ Finset.range numWin, TfamK j (window w
              (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val)) j)))
          % 2 ^ bits = _
      exact hnowrap.symm
    refine ⟨hawin, hgval.symm, ?_, ?_, hsc⟩
    · exact Nat.lt_of_not_le hnB
    · exact (mem_cosetWindow (2 ^ bits) N cm ((k * x) % N) hN (g idx)).mpr ⟨r, hr, by rw [hgval, hraw]⟩
  have hmaps : ∀ idx ∈ (inplaceBrev w bits numWin N cm k x TfamK TfamKinv)
        \ (inplaceBfwd w bits numWin N cm k x TfamK TfamKinv),
      g idx ∈ cosetWindow (2 ^ bits) N cm ((k * x) % N) := fun idx hidx => (hext idx hidx).2.2.2.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ jbp ∈ cosetWindow (2 ^ bits) N cm ((k * x) % N),
        (((inplaceBrev w bits numWin N cm k x TfamK TfamKinv)
          \ (inplaceBfwd w bits numWin N cm k x TfamK TfamKinv)).filter (fun idx => g idx = jbp)).card
      ≤ ∑ _jbp ∈ cosetWindow (2 ^ bits) N cm ((k * x) % N), numWin := Finset.sum_le_sum fun jbp hjbp => ?_
    _ = numWin * 2 ^ cm := by
        rw [Finset.sum_const, cosetWindow_card (2 ^ bits) N cm ((k * x) % N) hN hfit, smul_eq_mul,
          Nat.mul_comm]
  refine le_trans (Finset.card_le_card_of_injOn
      (fun idx => (⟨decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))) ?_ ?_)
      (rev_badja_card_le w bits numWin N cm k kInv x jbp.val TfamKinv hTfamKinv hbits hN hxN hkkinv
        jbp.isLt hjbp)
  · intro idx hidx
    rw [Finset.mem_coe, Finset.mem_filter] at hidx
    obtain ⟨hidxS, hgjbp⟩ := hidx
    obtain ⟨hawin, hnowrap, hrevbad, _, _⟩ := hext idx hidxS
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hawin, ?_⟩
    rw [← hgjbp]; exact hrevbad
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    obtain ⟨haS, hga⟩ := ha
    obtain ⟨hbS, hgb⟩ := hb
    obtain ⟨_, hnwa, _, _, hsca⟩ := hext a haS
    obtain ⟨_, hnwb, _, _, hscb⟩ := hext b hbS
    have hdaa : decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) a.val)
        = decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) b.val) :=
      congrArg Fin.val hab
    have hgval : (g a).val = (g b).val := by rw [hga, hgb]
    have hdb : decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) a.val)
        = decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) b.val) := by
      have h1 := hnwa
      rw [hgval] at h1
      rw [hdaa] at h1
      omega
    have hza := P_as_eGid_image w bits numWin
      (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) a.val))
      (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) a.val))
      hw hbits (decodeReg_lt_two_pow _ _ _) a hsca rfl rfl
    have hzb := P_as_eGid_image w bits numWin
      (decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) b.val))
      (decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) b.val))
      hw hbits (decodeReg_lt_two_pow _ _ _) b hscb rfl rfl
    rw [hza, hzb]
    simp only [hdaa, hdb]

/-- **Reverse leg Born mass** (D3).  `bornWeightOn (cosetInputVec x 0) (inplaceBrev \ inplaceBfwd) ≤ numWin/2^cm`:
    the sharper, non-overlapping form (the part of the reverse-bad set not already counted by the forward
    leg).  Cardinality `≤ numWin·2^cm` (`inplaceBrevSdiff_card_le`) times the per-index Born mass
    `1/2^cm·1/2^cm` (`cosetInputVec_bornWeight_le_card`), cancelling one factor `2^cm`. -/
theorem inplaceBrevSdiff_bornWeight_le (w bits numWin N cm k kInv x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfit : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits) :
    bornWeightOn (cosetInputVec w bits N cm x 0)
        ((inplaceBrev w bits numWin N cm k x TfamK TfamKinv)
          \ (inplaceBfwd w bits numWin N cm k x TfamK TfamKinv)) ≤ (numWin : ℝ) / 2 ^ cm := by
  have hcard := inplaceBrevSdiff_card_le w bits numWin N cm k kInv x TfamK TfamKinv hTfamK hTfamKinv
    hw hbits hN hxN hkkinv hfit
  calc bornWeightOn (cosetInputVec w bits N cm x 0)
          ((inplaceBrev w bits numWin N cm k x TfamK TfamKinv)
            \ (inplaceBfwd w bits numWin N cm k x TfamK TfamKinv))
      ≤ (((inplaceBrev w bits numWin N cm k x TfamK TfamKinv)
            \ (inplaceBfwd w bits numWin N cm k x TfamK TfamKinv)).card : ℝ) * (1 / 2 ^ cm * (1 / 2 ^ cm)) :=
        cosetInputVec_bornWeight_le_card w bits N cm x _
    _ ≤ ((numWin * 2 ^ cm : Nat) : ℝ) * (1 / 2 ^ cm * (1 / 2 ^ cm)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
    _ = (numWin : ℝ) / 2 ^ cm := by
        push_cast
        field_simp

/-! ## §3. The union: total bad-set Born mass (D4). -/

/-- **Total bad-set Born mass** (D4).  `bornWeightOn (cosetInputVec x 0) inplaceBadIn ≤ 2·numWin/2^cm`:
    `inplaceBadIn = inplaceBfwd ∪ inplaceBrev = inplaceBfwd ∪ (inplaceBrev \ inplaceBfwd)`, so by
    subadditivity (`bornWeightOn_union_le`) the total is bounded by the forward-leg mass
    (`inplaceBfwd_bornWeight_le`, ≤ numWin/2^cm) plus the disjoint reverse-leg remainder
    (`inplaceBrevSdiff_bornWeight_le`, ≤ numWin/2^cm) — the sharper split that avoids double-counting. -/
theorem inplaceBadIn_bornWeight_le (w bits numWin N cm k kInv x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfit : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (hxfit : x + (2 ^ cm - 1) * N < 2 ^ bits) :
    bornWeightOn (cosetInputVec w bits N cm x 0)
        (InPlaceComposedAgree.inplaceBadIn w bits numWin N cm k x TfamK TfamKinv)
      ≤ 2 * (numWin : ℝ) / 2 ^ cm := by
  rw [InPlaceComposedAgree.inplaceBadIn_eq_union, ← Finset.union_sdiff_self_eq_union]
  refine le_trans (FormalRV.Shor.CosetBornWeight.bornWeightOn_union_le _ _ _) ?_
  have h1 := InPlaceForwardCount.inplaceBfwd_bornWeight_le w bits numWin N cm k x TfamK TfamKinv
    hTfamK hw hbits hN hxfit
  have h2 := inplaceBrevSdiff_bornWeight_le w bits numWin N cm k kInv x TfamK TfamKinv
    hTfamK hTfamKinv hw hbits hN hxN hkkinv hfit
  have hsum : (numWin : ℝ) / 2 ^ cm + (numWin : ℝ) / 2 ^ cm = 2 * (numWin : ℝ) / 2 ^ cm := by ring
  linarith

end FormalRV.Shor.GidneyInPlace.InPlaceReverseCount
