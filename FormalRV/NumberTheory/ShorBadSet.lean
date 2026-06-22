/-
  FormalRV.NumberTheory.ShorBadSet — (R4) the ≥1/2 good-element bound on `(ℤ/N)ˣ`, `N = p·q`.

  The abstract counting (`GoodElements.card_prodBad_le_half`) says: in a product of two finite
  cyclic groups of even order, the "bad" set (order odd, or both half-powers `≠ 1`) is at most half.
  Here we TRANSPORT that to the actual Shor bad set on `(ℤ/N)ˣ` for a semiprime `N = p·q`
  (distinct odd primes) via the CRT iso `(ℤ/N)ˣ ≅ (ℤ/p)ˣ × (ℤ/q)ˣ`, using that each `(ℤ/p)ˣ` is a
  field's unit group so the square roots of `1` are exactly `±1` — hence `s^(r/2) = −1 ↔ s^(r/2) ≠ 1`.

  Result: `card_bad_le_half` — `|{a ∈ (ℤ/N)ˣ : ord a odd ∨ a^(ord a/2) = −1}| ≤ φ(N)/2`.
  Combined with `ShorReduction.shor_classical_step_correct`, a uniformly random unit is "good"
  (yields a factor via Shor) with probability ≥ 1/2.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.NumberTheory.GoodElements

namespace FormalRV.NumberTheory

open Finset

/-! ### Field square-root facts in `(ℤ/p)ˣ`. -/

/-- In `(ℤ/p)ˣ` (a field's unit group) the only square roots of `1` are `±1`. -/
theorem units_sq_eq_one {p : ℕ} [Fact p.Prime] (x : (ZMod p)ˣ) (h : x ^ 2 = 1) :
    x = 1 ∨ x = -1 := by
  have hv : (x : ZMod p) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  rw [sq, mul_self_eq_one_iff] at hv
  rcases hv with h1 | h1
  · exact Or.inl (Units.ext (by simpa using h1))
  · exact Or.inr (Units.ext (by simpa using h1))

/-- For odd `p`, `−1 ≠ 1` in `(ℤ/p)ˣ`. -/
theorem units_neg_one_ne_one {p : ℕ} [Fact p.Prime] (hp : 2 < p) : (-1 : (ZMod p)ˣ) ≠ 1 := by
  intro h
  have hv : (-1 : ZMod p) = 1 := by simpa using congrArg Units.val h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    have : (2 : ZMod p) = 0 := by rw [show (2 : ZMod p) = 1 - (-1) by ring, hv]; ring
    simpa using this
  have : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2
  have := Nat.le_of_dvd (by norm_num) this
  omega

/-- A square root of `1` in `(ℤ/p)ˣ` (`p` odd) is `−1` exactly when it is `≠ 1`. -/
theorem units_eq_neg_one_iff_ne_one {p : ℕ} [Fact p.Prime] (hp : 2 < p) (s : (ZMod p)ˣ)
    (hs : s ^ 2 = 1) : s = -1 ↔ s ≠ 1 := by
  constructor
  · intro h; rw [h]; exact units_neg_one_ne_one hp
  · intro h; rcases units_sq_eq_one s hs with h1 | h1
    · exact absurd h1 h
    · exact h1

/-- `(ℤ/p)ˣ` has even order for odd primes `p`. -/
theorem two_dvd_card_units {p : ℕ} [Fact p.Prime] (hp : 2 < p) :
    2 ∣ Fintype.card (ZMod p)ˣ := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  rcases (Fact.out : p.Prime).odd_of_ne_two (by omega) with ⟨k, hk⟩
  omega

/-! ### The CRT units equivalence and its action on `−1`. -/

/-- `(ℤ/(p·q))ˣ ≃* (ℤ/p)ˣ × (ℤ/q)ˣ` for coprime `p, q`. -/
noncomputable def unitsCRT {p q : ℕ} (hcop : Nat.Coprime p q) :
    (ZMod (p * q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder hcop).toMulEquiv).trans MulEquiv.prodUnits

/-- The CRT units iso sends `−1` to `(−1, −1)`. -/
theorem unitsCRT_neg_one {p q : ℕ} (hcop : Nat.Coprime p q) :
    unitsCRT hcop (-1) = (-1, -1) := by
  have hr : (ZMod.chineseRemainder hcop) (-1 : ZMod (p * q)) = (-1, -1) := by
    rw [map_neg, map_one]; rfl
  have hval : ((-1 : (ZMod (p * q))ˣ) : ZMod (p * q)) = -1 := by simp
  refine Prod.ext_iff.mpr ⟨Units.ext ?_, Units.ext ?_⟩
  · calc ((unitsCRT hcop (-1)).1 : ZMod p)
        = ((ZMod.chineseRemainder hcop) ((-1 : (ZMod (p * q))ˣ) : ZMod (p * q))).1 := rfl
      _ = ((-1 : (ZMod p)ˣ) : ZMod p) := by rw [hval, hr]; simp
  · calc ((unitsCRT hcop (-1)).2 : ZMod q)
        = ((ZMod.chineseRemainder hcop) ((-1 : (ZMod (p * q))ˣ) : ZMod (p * q))).2 := rfl
      _ = ((-1 : (ZMod q)ˣ) : ZMod q) := by rw [hval, hr]; simp

/-! ### (R4) The bad set on `(ℤ/N)ˣ` is at most half. -/

/-- **★ (R4) The Shor bad set has at most half the units. ★**  For `N = p·q` (distinct odd primes),
    `|{a ∈ (ℤ/N)ˣ : ord a odd ∨ a^(ord a/2) = −1}| ≤ φ(N)/2`.  So a uniformly random unit is "good"
    (even order, `a^(r/2) ≢ −1` — yielding a factor via `shor_classical_step_correct`) with
    probability `≥ 1/2`.  Transports `card_prodBad_le_half` along the CRT iso, converting the
    component `= −1` conditions to `≠ 1` via the field square-root dichotomy. -/
theorem card_bad_le_half {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 2 < p) (hq : 2 < q) (hpq : p ≠ q) :
    (univ.filter (fun a : (ZMod (p * q))ˣ =>
        Odd (orderOf a) ∨ a ^ (orderOf a / 2) = -1)).card
      ≤ Fintype.card (ZMod (p * q))ˣ / 2 := by
  haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne q)⟩
  have hcop : Nat.Coprime p q := (Nat.coprime_primes Fact.out Fact.out).mpr hpq
  set e := unitsCRT hcop with he
  have hset : (univ.filter (fun a : (ZMod (p * q))ˣ =>
        Odd (orderOf a) ∨ a ^ (orderOf a / 2) = -1)).card
      = (univ.filter (fun w : (ZMod p)ˣ × (ZMod q)ˣ => Odd (orderOf w) ∨
          (w.1 ^ (orderOf w / 2) ≠ 1 ∧ w.2 ^ (orderOf w / 2) ≠ 1))).card := by
    apply Finset.card_equiv e.toEquiv
    intro a
    simp only [mem_filter, mem_univ, true_and]
    rw [show e.toEquiv a = e a from rfl]
    -- order is preserved by the iso
    have horder : orderOf (e a) = orderOf a :=
      orderOf_injective e.toMonoidHom e.injective a
    -- e turns `a^k = -1` into the two component `= -1` conditions
    have htrans : ∀ k : ℕ, a ^ k = -1 ↔ (e a).1 ^ k = -1 ∧ (e a).2 ^ k = -1 := by
      intro k
      rw [← EmbeddingLike.apply_eq_iff_eq e, map_pow, he, unitsCRT_neg_one,
          show ((e a) ^ k) = ((e a).1 ^ k, (e a).2 ^ k) from rfl, Prod.mk.injEq]
    rw [horder]
    -- both half-powers are square roots of 1 when the (even) order is `orderOf a`
    constructor
    · rintro (ho | ha)
      · exact Or.inl ho
      · by_cases ho : Odd (orderOf a)
        · exact Or.inl ho
        · have hev : 2 ∣ orderOf a := by
            rcases Nat.even_or_odd (orderOf a) with he | ho'
            · exact he.two_dvd
            · exact absurd ho' ho
          have hcomp := (htrans (orderOf a / 2)).mp ha
          refine Or.inr ⟨?_, ?_⟩
          · intro hc
            have : (e a).1 ^ (orderOf a / 2) = 1 := hc
            rw [hcomp.1] at this; exact units_neg_one_ne_one hp this
          · intro hc
            have : (e a).2 ^ (orderOf a / 2) = 1 := hc
            rw [hcomp.2] at this; exact units_neg_one_ne_one hq this
    · rintro (ho | ⟨hx, hy⟩)
      · exact Or.inl ho
      · by_cases ho : Odd (orderOf a)
        · exact Or.inl ho
        · have hev : 2 ∣ orderOf a := by
            rcases Nat.even_or_odd (orderOf a) with he | ho'
            · exact he.two_dvd
            · exact absurd ho' ho
          have hea_pow : (e a) ^ orderOf a = 1 := by rw [← horder]; exact pow_orderOf_eq_one (e a)
          have hpow1 : (e a).1 ^ orderOf a = 1 := by
            have h : ((e a) ^ orderOf a).1 = (e a).1 ^ orderOf a := rfl
            rw [← h, hea_pow]; rfl
          have hpow2 : (e a).2 ^ orderOf a = 1 := by
            have h : ((e a) ^ orderOf a).2 = (e a).2 ^ orderOf a := rfl
            rw [← h, hea_pow]; rfl
          have hsq1 : ((e a).1 ^ (orderOf a / 2)) ^ 2 = 1 := by
            rw [← pow_mul, show orderOf a / 2 * 2 = orderOf a from by omega, hpow1]
          have hsq2 : ((e a).2 ^ (orderOf a / 2)) ^ 2 = 1 := by
            rw [← pow_mul, show orderOf a / 2 * 2 = orderOf a from by omega, hpow2]
          refine Or.inr ((htrans (orderOf a / 2)).mpr
            ⟨(units_eq_neg_one_iff_ne_one hp _ hsq1).mpr hx,
             (units_eq_neg_one_iff_ne_one hq _ hsq2).mpr hy⟩)
  rw [hset, Fintype.card_congr e.toEquiv]
  exact card_prodBad_le_half _ _ (two_dvd_card_units hp) (two_dvd_card_units hq)

/-- **★ At least half the units are "good". ★**  For `N = p·q` (distinct odd primes), at least
    `φ(N)/2` units `a` have even order with `a^(ord a/2) ≢ −1` — i.e. Shor's classical step
    (`shor_classical_step_correct`) extracts a nontrivial factor from `a`.  So picking `a` uniformly
    at random succeeds with probability `≥ 1/2`.  Immediate complement of `card_bad_le_half`. -/
theorem card_good_ge_half {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 2 < p) (hq : 2 < q) (hpq : p ≠ q) :
    Fintype.card (ZMod (p * q))ˣ / 2
      ≤ (univ.filter (fun a : (ZMod (p * q))ˣ =>
          ¬ (Odd (orderOf a) ∨ a ^ (orderOf a / 2) = -1))).card := by
  haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne q)⟩
  have hbad := card_bad_le_half hp hq hpq
  rw [Finset.filter_not, Finset.card_univ_diff]
  omega

end FormalRV.NumberTheory
