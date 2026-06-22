/-
  FormalRV.Shor.GidneyInPlace.InPlaceAgreeOff
  ───────────────────────────────────────────────
  The TWO-REGISTER per-branch-pair AGREE-OFF: off the union wrap band, the in-place
  coset multiplier maps an input branch pair into the TARGET coset windows.

  Input (raw `Fin (2^bits)` branch indices):
    a-register  `ja ∈ cosetWindow x`        (multiplicand, coset of `x`)
    b-register  `jb ∈ cosetWindow 0`        (fresh accumulator, coset of `0`)

  The whole gate's per-branch action (`gidneyTwoRegInPlace_branch_action`, Brick 9)
  sends `(ja, jb)` to the pass-2 factorization branch:
    b-register  `jb' = (jb + ∑ₖ TfamK k (window w ja k)) % 2^bits`     (pass-1 result)
    a-register  `a'  = modSub bits ja (∑ₖ TfamKinv k (window w jb' k))`  (reverse-pass2)

  THE THEOREM (`gidneyTwoRegInPlace_agree_off`).  Off the union wrap band — i.e. for
  every `(ja, jb)` satisfying `goodPair` (no window overflow on the forward leg, no
  underflow on the reverse leg) — the two output branches land in the TARGET windows:
    `jb' ∈ cosetWindow ((k·x) % N)`     and     `a'  ∈ cosetWindow 0`.

  This is the per-branch MEMBERSHIP content (the "forward direction" of the eventual
  branch bijection).  It is proven DIRECTLY:
    • b-leg: off bad, `jb' = (k·x)%N + (q+s)·N` with `q+s < 2^cm`  (window placement).
        residue `Sfwd ≡ k·x (mod N)` via `endpoint_residue_modN`; `jb ≡ 0`, `ja ≡ x`.
    • a-leg: off bad, `a' = ja - Sinv = (p-t)·N`  (the a-register CLEARS to coset 0).
        residue `Sinv ≡ x (mod N)` via `endpoint_residue_modN` + `revCanonical_eq`;
        `a' + Sinv ≡ ja` (`modSub_add`) read forward as `a' = (p-t)·N`.
  No symmetric-difference machinery is needed for MEMBERSHIP (that is purely the mass
  layer).  The Born-mass bound (≤ 2·numWin/2^cm) and the `normSqDist` lift are SEPARATE
  (next bricks); this file proves NO mass and NO `normSqDist`.

  AUDIT.  `branch_action` is the only gate-dynamics fact (its `jb'`/`modSub` outputs are
  the theorem's subjects verbatim).  The bad set is stated over RAW branch pairs
  (`goodPair`, raw `ja`, `jb`), not decoded residues.  The reverse leg's `a'` is genuine
  modular subtraction (`modSub`), read FORWARD into `cosetWindow 0`, not "adding Sinv
  returns ja".  B6 `endpoint_residue_modN` is used for both legs' residues.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceBranchAction
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceEndpoint

namespace FormalRV.Shor.GidneyInPlace.InPlaceAgreeOff

open FormalRV.Shor.WindowedArith (window tableValue)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow)
open FormalRV.Shor.GidneyInPlace.InPlaceBranchAction (modSub modSub_add)
open FormalRV.Shor.GidneyInPlace.InPlaceEndpoint (endpoint_residue_modN)
open FormalRV.Shor.GidneyInPlace.InPlaceBadSet (revCanonical_eq)

/-! ## §1. The off-bad (good) predicate over RAW branch pairs. -/

/-- **The per-branch-pair GOOD predicate** (complement of the union wrap band), over RAW
    branch indices `ja`, `jb`:
      • forward leg does NOT overflow its window:
        `jb + Sfwd < (k·x)%N + 2^cm·N`  (i.e. `q + s < 2^cm`), and
      • reverse leg does NOT underflow:
        `Sinv ≤ ja`  (i.e. `p ≥ t`),
    where `Sfwd = ∑ₖ TfamK k (window w ja k)`, `jb' = (jb + Sfwd) % 2^bits`,
    `Sinv = ∑ₖ TfamKinv k (window w jb' k)`.  The bad set is `{(ja, jb) : ¬ goodPair …}`. -/
def goodPair (w bits numWin N cm k x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (ja jb : Nat) : Prop :=
  jb + (∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) < (k * x) % N + 2 ^ cm * N
  ∧ (∑ j ∈ Finset.range numWin, TfamKinv j
      (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j)) ≤ ja

/-! ## §2. The agree-off membership theorem. -/

/-- **TWO-REGISTER AGREE-OFF (per-branch membership).**  For `(ja, jb)` outside the union
    wrap band (`goodPair`), with input windows `ja ∈ cosetWindow x`, `jb ∈ cosetWindow 0`,
    the gate's two output branches land in the TARGET windows: the b-register output
    `jb' ∈ cosetWindow ((k·x) % N)` and the a-register output `modSub bits ja Sinv ∈
    cosetWindow 0`.  Raw `Fin (2^bits)` branch indices throughout; no mass, no
    `normSqDist`. -/
theorem gidneyTwoRegInPlace_agree_off
    (w bits numWin N cm k kInv x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfit : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (ja jb : Nat) (hja : ja < 2 ^ bits) (hjb : jb < 2 ^ bits)
    (hja_win : (⟨ja, hja⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm x)
    (hjb_win : (⟨jb, hjb⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm 0)
    (hgood : goodPair w bits numWin N cm k x TfamK TfamKinv ja jb) :
    (∀ h, (⟨(jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits, h⟩
        : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm ((k * x) % N))
    ∧ (∀ h, (⟨modSub bits ja (∑ j ∈ Finset.range numWin, TfamKinv j
          (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j)), h⟩
        : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm 0) := by
  obtain ⟨hgoodB, hgoodA⟩ := hgood
  -- 2^bits = (2^w)^numWin (the eGid fold-arity bound)
  have hpow : (2 : Nat) ^ bits = (2 ^ w) ^ numWin := by
    rw [← hbits, Nat.mul_comm numWin w, Nat.pow_mul]
  -- representatives: ja = x + p·N, jb = q·N (p, q < 2^cm)
  obtain ⟨p, hp, hja_eq⟩ := (mem_cosetWindow (2 ^ bits) N cm x hN ⟨ja, hja⟩).mp hja_win
  obtain ⟨q, hq, hjb_eq⟩ := (mem_cosetWindow (2 ^ bits) N cm 0 hN ⟨jb, hjb⟩).mp hjb_win
  replace hja_eq : ja = x + p * N := hja_eq
  replace hjb_eq : jb = q * N := by rw [Nat.zero_add] at hjb_eq; exact hjb_eq
  -- forward leg: Sfwd ≡ k·x (mod N)  [endpoint_residue_modN, ja ≡ x]
  have hjalt : ja < (2 ^ w) ^ numWin := by rw [← hpow]; exact hja
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
  -- b-leg value: jb' = (k·x)%N + (q+s)·N, off the window-overflow band
  have hsum : jb + (∑ j ∈ Finset.range numWin, TfamK j (window w ja j))
      = (k * x) % N + (q + s) * N := by rw [hjb_eq, hs_eq, Nat.add_mul]; omega
  have hqs : q + s < 2 ^ cm := by
    have hlt : (k * x) % N + (q + s) * N < (k * x) % N + 2 ^ cm * N := hsum ▸ hgoodB
    have h2 : (q + s) * N < 2 ^ cm * N := by omega
    exact lt_of_mul_lt_mul_right h2 (Nat.zero_le N)
  have hbound : jb + (∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) < 2 ^ bits := by
    rw [hsum]
    have h1 : (q + s) * N ≤ (2 ^ cm - 1) * N := Nat.mul_le_mul_right _ (by omega)
    omega
  have hbval : (jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits
      = (k * x) % N + (q + s) * N := by rw [Nat.mod_eq_of_lt hbound]; exact hsum
  -- reverse leg: Sinv ≡ x (mod N)  [endpoint_residue_modN at jb', then revCanonical_eq]
  have hjb'lt : (jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits
      < (2 ^ w) ^ numWin := by rw [← hpow]; exact Nat.mod_lt _ (by positivity)
  have hSinv_mod : (∑ j ∈ Finset.range numWin, TfamKinv j
      (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j)) % N
      = x := by
    have h := endpoint_residue_modN kInv N w numWin
      ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) 0
      TfamKinv hTfamKinv hN hjb'lt
    rw [Nat.zero_add, Nat.zero_add] at h
    rw [h, hbval, Nat.mul_add, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
    exact revCanonical_eq N k kInv x hxN hkkinv
  obtain ⟨t, ht_eq⟩ :
      ∃ t, (∑ j ∈ Finset.range numWin, TfamKinv j
          (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j))
        = x + t * N :=
    ⟨(∑ j ∈ Finset.range numWin, TfamKinv j
        (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j)) / N, by
      have hdm := Nat.div_add_mod (∑ j ∈ Finset.range numWin, TfamKinv j
        (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j)) N
      rw [hSinv_mod] at hdm
      have hc : N * ((∑ j ∈ Finset.range numWin, TfamKinv j
            (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j)) / N)
          = ((∑ j ∈ Finset.range numWin, TfamKinv j
            (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j)) / N)
              * N := Nat.mul_comm _ _
      omega⟩
  -- a-leg value: a' = ja - Sinv = (p - t)·N, off the underflow band
  have htp : t ≤ p := by
    have hle : t * N ≤ p * N := by
      have hsi : x + t * N ≤ x + p * N := by rw [← ht_eq, ← hja_eq]; exact hgoodA
      omega
    exact Nat.le_of_mul_le_mul_right hle hN
  have hsinv_lt : (∑ j ∈ Finset.range numWin, TfamKinv j
      (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j))
      < 2 ^ bits := lt_of_le_of_lt hgoodA hja
  have hamod : modSub bits ja (∑ j ∈ Finset.range numWin, TfamKinv j
      (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j))
      = (p - t) * N := by
    unfold modSub
    rw [Nat.mod_eq_of_lt hsinv_lt]
    have h1 : ja + 2 ^ bits - (∑ j ∈ Finset.range numWin, TfamKinv j
        (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j))
        = 2 ^ bits + (ja - (∑ j ∈ Finset.range numWin, TfamKinv j
          (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j))) := by
      omega
    rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (show ja - (∑ j ∈ Finset.range numWin, TfamKinv j
        (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j))
        < 2 ^ bits by omega)]
    rw [ht_eq, hja_eq, Nat.add_sub_add_left, ← Nat.sub_mul]
  -- assemble the two memberships
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [mem_cosetWindow (2 ^ bits) N cm ((k * x) % N) hN]
    exact ⟨q + s, hqs, hbval⟩
  · rw [mem_cosetWindow (2 ^ bits) N cm 0 hN]
    refine ⟨p - t, by omega, ?_⟩
    show modSub bits ja (∑ j ∈ Finset.range numWin, TfamKinv j
        (window w ((jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits) j))
      = 0 + (p - t) * N
    rw [hamod, Nat.zero_add]

end FormalRV.Shor.GidneyInPlace.InPlaceAgreeOff
