/-
  FormalRV.Shor.GidneyInPlace.InPlaceReverseRekey
  ─────────────────────────────────────────────────
  PACKAGING checkpoint 2d (Checkpoint C): the reverse re-keying arithmetic — previously
  proof-local inside `gidneyTwoRegInPlace_agree_off` (`InPlaceAgreeOff.lean:114-186`) —
  extracted as REUSABLE top-level lemmas, in exactly the shape the `Bfwd`/`Brev`
  cardinality bounds need.  NO cardinality/mass proof here; NO change to `inplaceBadSetB`,
  `inplaceBadIn`, or the a/b convention.

   • `windowSum_wrap_le`     — the wrap count `m ≤ numWin` whenever the windowed table sum
                                equals `c + m·N` (the `s ≤ numWin` / `t ≤ numWin` engine).
   • `fwd_jbp_landing`       — on fwd-good inputs the forward output is `jb' = jb + Sfwd`
                                (NO modular wrap) `= (k·x)%N + r·N` with `r < 2^cm`
                                (hence `jb' ∈ window((k·x)%N)`), and `jb ↦ jb'` is additive
                                ⇒ injective per `ja`.
   • `Sinv_residue_decomp`   — for any `y ≡ (k·x)%N` (e.g. `y ∈ window((k·x)%N)`), the reverse
                                table sum `Sinv(y) = x + t·N` with `t ≤ numWin` (the per-`jb'`
                                reverse-leg fact the re-keyed count consumes).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceAgreeOff
import FormalRV.Shor.GidneyInPlace.OutOfPlaceCoset.Proof.CosetFoldWindowed

namespace FormalRV.Shor.GidneyInPlace.InPlaceReverseRekey

open FormalRV.Shor.WindowedArith (window tableValue)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow)
open FormalRV.Shor.GidneyInPlace.CosetMul (runningSum)
open FormalRV.Shor.GidneyInPlace.CosetTableSum (cosetWindowConst cosetWindowConst_lt)
open FormalRV.Shor.GidneyInPlace.CosetFoldWindowed (runningSum_lt)
open FormalRV.Shor.GidneyInPlace.InPlaceEndpoint (canonicalSum_eq_runningSum endpoint_residue_modN)
open FormalRV.Shor.GidneyInPlace.InPlaceBadSet (revCanonical_eq)

/-! ## §1. The wrap-count bound `≤ numWin`. -/

/-- **Wrap count ≤ numWin.**  If the canonical windowed table sum (multiplier `K`) equals
    `c + m·N`, then the wrap count `m ≤ numWin`: the running sum is `< numWin·N`. -/
theorem windowSum_wrap_le (K N w numWin y c m : Nat) (Tfam : Nat → Nat → Nat)
    (hTfam : ∀ j addr, Tfam j addr = tableValue K N w j addr) (hN : 0 < N)
    (heq : (∑ j ∈ Finset.range numWin, Tfam j (window w y j)) = c + m * N) :
    m ≤ numWin := by
  rcases Nat.eq_zero_or_pos numWin with h0 | h0
  · subst h0
    simp only [Finset.range_zero, Finset.sum_empty] at heq
    have hmN : m * N = 0 := by omega
    rcases Nat.mul_eq_zero.mp hmN with h | h
    · omega
    · omega
  · have hlt : (∑ j ∈ Finset.range numWin, Tfam j (window w y j)) < numWin * N := by
      rw [canonicalSum_eq_runningSum K N w numWin y Tfam hTfam]
      exact runningSum_lt _ N (fun i => cosetWindowConst_lt K N w y hN i) numWin h0
    rw [heq] at hlt
    have hm : m * N < numWin * N := by omega
    exact Nat.le_of_lt (lt_of_mul_lt_mul_right hm (Nat.zero_le N))

/-! ## §2. The forward landing: no-wrap + canonical window placement. -/

/-- **Forward landing (no-wrap + window).**  On a fwd-good input `(ja ∈ window x, jb ∈ window 0)`
    the forward output `jb' = (jb + Sfwd)%2^bits` does NOT wrap (`= jb + Sfwd`) and is the
    canonical window value `(k·x)%N + r·N` with `r < 2^cm` — so `jb' ∈ window((k·x)%N)`.  Since
    `jb' = jb + Sfwd` (additive), `jb ↦ jb'` is injective for fixed `ja`. -/
theorem fwd_jbp_landing (w bits numWin N cm k x ja jb : Nat) (TfamK : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hbits : numWin * w = bits) (hN : 0 < N)
    (hfit : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (hja : ja < 2 ^ bits) (hjb : jb < 2 ^ bits)
    (hja_win : (⟨ja, hja⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm x)
    (hjb_win : (⟨jb, hjb⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm 0)
    (hfwdgood : jb + (∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) < (k * x) % N + 2 ^ cm * N) :
    ∃ r, r < 2 ^ cm
      ∧ jb + (∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) = (k * x) % N + r * N
      ∧ (jb + ∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) % 2 ^ bits = (k * x) % N + r * N := by
  have hpow : (2 : Nat) ^ bits = (2 ^ w) ^ numWin := by
    rw [← hbits, Nat.mul_comm numWin w, Nat.pow_mul]
  obtain ⟨p, hp, hja_eq⟩ := (mem_cosetWindow (2 ^ bits) N cm x hN ⟨ja, hja⟩).mp hja_win
  obtain ⟨q, hq, hjb_eq⟩ := (mem_cosetWindow (2 ^ bits) N cm 0 hN ⟨jb, hjb⟩).mp hjb_win
  replace hja_eq : ja = x + p * N := hja_eq
  replace hjb_eq : jb = q * N := by rw [Nat.zero_add] at hjb_eq; exact hjb_eq
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
  have hsum : jb + (∑ j ∈ Finset.range numWin, TfamK j (window w ja j))
      = (k * x) % N + (q + s) * N := by rw [hjb_eq, hs_eq, Nat.add_mul]; omega
  have hqs : q + s < 2 ^ cm := by
    have hlt : (k * x) % N + (q + s) * N < (k * x) % N + 2 ^ cm * N := hsum ▸ hfwdgood
    have h2 : (q + s) * N < 2 ^ cm * N := by omega
    exact lt_of_mul_lt_mul_right h2 (Nat.zero_le N)
  have hbound : jb + (∑ j ∈ Finset.range numWin, TfamK j (window w ja j)) < 2 ^ bits := by
    rw [hsum]
    have h1 : (q + s) * N ≤ (2 ^ cm - 1) * N := Nat.mul_le_mul_right _ (by omega)
    omega
  exact ⟨q + s, hqs, hsum, by rw [Nat.mod_eq_of_lt hbound]; exact hsum⟩

/-! ## §3. The reverse per-`y` fact: residue + decomposition + wrap bound. -/

/-- **Reverse residue + decomposition.**  For any `y < (2^w)^numWin` with `y ≡ (k·x)%N (mod N)`
    (in particular `y ∈ window((k·x)%N)`), the reverse windowed table sum `Sinv(y)` satisfies
    `Sinv(y) = x + t·N` with `t ≤ numWin` (via `revCanonical_eq` for the residue and the wrap
    bound for `t`).  This is the per-`jb'` fact the re-keyed reverse count consumes. -/
theorem Sinv_residue_decomp (w numWin N k kInv x y : Nat) (TfamKinv : Nat → Nat → Nat)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N) (hy : y < (2 ^ w) ^ numWin) (hymod : y % N = (k * x) % N) :
    ∃ t, t ≤ numWin ∧ (∑ j ∈ Finset.range numWin, TfamKinv j (window w y j)) = x + t * N := by
  have hSinv_mod : (∑ j ∈ Finset.range numWin, TfamKinv j (window w y j)) % N = x := by
    have h := endpoint_residue_modN kInv N w numWin y 0 TfamKinv hTfamKinv hN hy
    rw [Nat.zero_add, Nat.zero_add] at h
    rw [h]
    have hy_modeq : y % N = ((k * x) % N) % N := by rw [Nat.mod_mod]; exact hymod
    calc kInv * y % N = kInv * ((k * x) % N) % N := Nat.ModEq.mul_left kInv hy_modeq
      _ = x := revCanonical_eq N k kInv x hxN hkkinv
  have hdecomp : (∑ j ∈ Finset.range numWin, TfamKinv j (window w y j))
      = x + ((∑ j ∈ Finset.range numWin, TfamKinv j (window w y j)) / N) * N := by
    have hdm := Nat.div_add_mod (∑ j ∈ Finset.range numWin, TfamKinv j (window w y j)) N
    rw [hSinv_mod] at hdm
    have hc : N * ((∑ j ∈ Finset.range numWin, TfamKinv j (window w y j)) / N)
        = ((∑ j ∈ Finset.range numWin, TfamKinv j (window w y j)) / N) * N := Nat.mul_comm _ _
    omega
  exact ⟨_, windowSum_wrap_le kInv N w numWin y x _ TfamKinv hTfamKinv hN hdecomp, hdecomp⟩

end FormalRV.Shor.GidneyInPlace.InPlaceReverseRekey
