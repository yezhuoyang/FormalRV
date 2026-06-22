/-
  FormalRV.NumberTheory.GoodElements — the ≥1/2 success-probability bound for Shor's algorithm
  on a SEMIPRIME N = p·q (the RSA case), the standard textbook counting (Nielsen–Chuang A4.13).

  GOAL: a uniformly random `a ∈ (ℤ/N)ˣ` is "good" (even order `r`, `a^(r/2) ≢ −1 mod N`) with
  probability ≥ 1/2 — so the order→factoring reduction (`NumberTheory.ShorReduction`) succeeds after
  O(1) expected tries.

  STATUS — the two reusable KERNELS of the textbook counting are PROVEN here (axiom-clean):
  * `diag_card_le` — PURE COMBINATORICS: if every fiber `{b : g b = k}` has ≤ c elements, the
    "diagonal" `{(a,b) : f a = g b}` has ≤ |A|·c elements.  This is the `|bad| = ∑_v aᵥ·bᵥ ≤
    (max atom)·|A|` step, instantiated with `A = (ℤ/p)ˣ`, `c = |（ℤ/q)ˣ|/2`.
  * `card_sqrt_one_eq_two` — in a finite cyclic group of even order there are exactly two square
    roots of 1.
  * `card_squares_eq_half` — exactly half the elements are squares (the squaring map is 2-to-1: each
    fiber is a coset of the 2-element kernel).  [= R1]

  * `card_atom_le_half` [R2] — every `v₂(ord)`-atom `{a : v₂(ord a)=v}` ≤ |G|/2 (each atom lands in
    `{ord ∣ |G|/2}` or its complement, both of size |G|/2; `{ord ∣ |G|/2}` counted via `∑φ = |G|/2`).
  * `card_diag_v2_le_half` [R4 core] — for `G × H` both even cyclic, the diagonal
    `{(x,y) : v₂(ord x) = v₂(ord y)}` ≤ |G×H|/2.  THE textbook Shor/Miller ≥1/2 counting.
  * `orderOf_prod_mk` / `factorization_lcm_two` — `ord(a,b) = lcm`, `v₂(lcm) = max`.
  * `prodBad_iff_diag` [R3] — `(x,y)` bad (`Odd(ord(x,y)) ∨ (x^(r/2)≠1 ∧ y^(r/2)≠1)`) ⟺
    `v₂(ord x) = v₂(ord y)`.  (The `≠ 1` form needs no order-2 element; the `= −1` identification is
    done at the field level in `ShorBadSet`.)  Hence `card_prodBad_le_half` — bad set ≤ |G×H|/2.

  The transport to the actual Shor bad set on `(ℤ/N)ˣ` (`N = p·q`) — `card_bad_le_half` /
  `card_good_ge_half` — is in `FormalRV.NumberTheory.ShorBadSet` (CRT iso + field square roots).

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import Mathlib

namespace FormalRV.NumberTheory

open scoped BigOperators
open Finset

/-- **Diagonal counting bound (pure combinatorics).**  If for every `k` the fiber
    `{b : g b = k}` has at most `c` elements, then the diagonal `{(a,b) : f a = g b}` has at most
    `|A|·c` elements.  This is the `∑_v Pr[d₁=v]·Pr[d₂=v] ≤ (max_v Pr[d₂=v])·1` step of the
    Shor counting, with `c = max atom`. -/
theorem diag_card_le {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (f : A → ℕ) (g : B → ℕ) (c : ℕ)
    (hfib : ∀ k, (univ.filter (fun b : B => g b = k)).card ≤ c) :
    (univ.filter (fun p : A × B => f p.1 = g p.2)).card ≤ Fintype.card A * c := by
  classical
  have hsum : (univ.filter (fun p : A × B => f p.1 = g p.2)).card
      = ∑ a : A, (univ.filter (fun b : B => g b = f a)).card := by
    simp_rw [Finset.card_filter]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp [eq_comm]
  rw [hsum]
  calc ∑ a : A, (univ.filter (fun b : B => g b = f a)).card
      ≤ ∑ _a : A, c := Finset.sum_le_sum (fun a _ => hfib (f a))
    _ = Fintype.card A * c := by rw [Finset.sum_const, Finset.card_univ]; ring

/-- **Square roots of 1 in a finite cyclic group of even order: exactly two** (`1` and the unique
    order-2 element).  Via `IsCyclic.card_orderOf_eq_totient`: `a²=1 ⟺ orderOf a ∈ {1,2}`, and the
    order-1/order-2 classes have `φ(1)=φ(2)=1` elements each. -/
theorem card_sqrt_one_eq_two (G : Type*) [Group G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (hev : 2 ∣ Fintype.card G) :
    (univ.filter (fun a : G => a ^ 2 = 1)).card = 2 := by
  classical
  have h1 : (univ.filter (fun a : G => orderOf a = 1)).card = 1 := by
    simpa using IsCyclic.card_orderOf_eq_totient (α := G) (d := 1) (one_dvd _)
  have h2 : (univ.filter (fun a : G => orderOf a = 2)).card = 1 := by
    simpa [Nat.totient_two] using IsCyclic.card_orderOf_eq_totient (α := G) (d := 2) hev
  have hunion : (univ.filter (fun a : G => a ^ 2 = 1))
      = (univ.filter (fun a : G => orderOf a = 1)) ∪ (univ.filter (fun a : G => orderOf a = 2)) := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · intro h
      have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h
      exact (Nat.prime_two.eq_one_or_self_of_dvd _ hdvd)
    · rintro (h | h)
      · rw [orderOf_eq_one_iff.mp h]; simp
      · rw [← h]; exact pow_orderOf_eq_one a
  have hdisj : Disjoint (univ.filter (fun a : G => orderOf a = 1))
      (univ.filter (fun a : G => orderOf a = 2)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [mem_filter] at ha hb
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj, h1, h2]

/-- **Exactly half the elements of a finite cyclic group of even order are squares.**  The squaring
    map is 2-to-1 (each fiber is a coset of the 2-element kernel `{z : z²=1}`), so
    `|squares|·2 = |G|`. -/
theorem card_squares_eq_half (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (hev : 2 ∣ Fintype.card G) :
    (univ.filter (fun a : G => IsSquare a)).card * 2 = Fintype.card G := by
  classical
  -- image of squaring = squares
  have himg : univ.image (fun a : G => a ^ 2) = univ.filter (fun a : G => IsSquare a) := by
    ext s
    simp only [mem_image, mem_univ, true_and, mem_filter, isSquare_iff_exists_sq]
    exact ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩
  -- every fiber of squaring (over a square) has exactly 2 elements
  have hfiber : ∀ s ∈ univ.image (fun a : G => a ^ 2),
      (univ.filter (fun a : G => a ^ 2 = s)).card = 2 := by
    intro s hs
    rw [mem_image] at hs
    obtain ⟨a0, _, ha0⟩ := hs
    have hbij : (univ.filter (fun a : G => a ^ 2 = s)).card
        = (univ.filter (fun a : G => a ^ 2 = 1)).card := by
      apply Finset.card_bij' (fun a _ => a * a0⁻¹) (fun z _ => z * a0)
      · intro a ha
        simp only [mem_filter, mem_univ, true_and] at ha ⊢
        rw [mul_pow, ha, ← ha0]; group
      · intro z hz
        simp only [mem_filter, mem_univ, true_and] at hz ⊢
        rw [mul_pow, hz, ← ha0]; group
      · intro a _; group
      · intro z _; group
    rw [hbij, card_sqrt_one_eq_two G hev]
  -- |G| = Σ_{s ∈ squares} |fiber s| = Σ 2 = |squares|·2
  have hfw := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset G)) (t := univ.image (fun a : G => a ^ 2))
    (f := fun a : G => a ^ 2) (fun a _ => mem_image_of_mem _ (mem_univ a))
  rw [Finset.card_univ] at hfw
  rw [hfw, Finset.sum_congr rfl hfiber, Finset.sum_const, himg, smul_eq_mul]

/-! ## §2. (R2) The per-`v₂(ord)`-atom bound: every atom ≤ |G|/2. -/

/-- Nat arithmetic: with `r ∣ n` and `2 ∣ n`, `r ∣ n/2 ↔ v₂(r) < v₂(n)`. -/
private theorem dvd_half_iff_factorization (r n : ℕ) (hr : r ∣ n) (hn0 : 0 < n) (hev : 2 ∣ n) :
    r ∣ n / 2 ↔ r.factorization 2 < n.factorization 2 := by
  have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hr hn0
  rw [Nat.dvd_div_iff_mul_dvd hev,
      ← Nat.factorization_le_iff_dvd (Nat.mul_ne_zero two_ne_zero hr0.ne') hn0.ne',
      Nat.factorization_mul two_ne_zero hr0.ne',
      Nat.Prime.factorization Nat.prime_two, Finsupp.le_def]
  have hrn := Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd hr0.ne' hn0.ne').mpr hr)
  constructor
  · intro h
    have h2 := h 2
    rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl] at h2
    omega
  · intro h p
    rw [Finsupp.add_apply, Finsupp.single_apply]
    rcases eq_or_ne (2 : ℕ) p with hp | hp
    · subst hp; rw [if_pos rfl]; omega
    · rw [if_neg hp]; have := hrn p; omega

/-- In a finite cyclic group of even order, the elements whose order divides `|G|/2` are exactly
    half: `|{a : ord a ∣ |G|/2}| = |G|/2` (via `∑_{d ∣ |G|/2} φ(d) = |G|/2`). -/
theorem card_orderOf_dvd_half (G : Type*) [Group G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (hev : 2 ∣ Fintype.card G) :
    (univ.filter (fun a : G => orderOf a ∣ Fintype.card G / 2)).card = Fintype.card G / 2 := by
  classical
  set n := Fintype.card G with hn
  have hn0 : 0 < n := Fintype.card_pos
  have hstep : (univ.filter (fun a : G => orderOf a ∣ n / 2)).card
      = ∑ d ∈ (n / 2).divisors, d.totient := by
    rw [Finset.card_eq_sum_card_fiberwise
      (s := univ.filter (fun a : G => orderOf a ∣ n / 2))
      (f := fun a : G => orderOf a) (t := (n / 2).divisors)
      (fun a ha => by
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Nat.mem_divisors] at ha ⊢
        exact ⟨ha, by omega⟩)]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Nat.mem_divisors] at hd
    have hdn : d ∣ n := hd.1.trans (Nat.div_dvd_of_dvd hev)
    have heq : (univ.filter (fun a : G => orderOf a ∣ n / 2)).filter (fun a : G => orderOf a = d)
        = univ.filter (fun a : G => orderOf a = d) := by
      ext a; simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
      intro h; rw [h]; exact hd.1
    rw [heq]
    exact IsCyclic.card_orderOf_eq_totient hdn
  rw [hstep, Nat.sum_totient]

/-- **★ (R2) Atom bound. ★**  In a finite cyclic group of even order, for every `v` the set of
    elements whose order has 2-adic valuation `= v` has at most `|G|/2` elements: each atom lies
    entirely inside `{a : ord a ∣ |G|/2}` (if `v < v₂|G|`) or its complement (if `v = v₂|G|`), both
    of size `|G|/2`. -/
theorem card_atom_le_half (G : Type*) [Group G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (hev : 2 ∣ Fintype.card G) (v : ℕ) :
    (univ.filter (fun a : G => (orderOf a).factorization 2 = v)).card ≤ Fintype.card G / 2 := by
  classical
  set n := Fintype.card G with hn
  have hn0 : 0 < n := Fintype.card_pos
  have hH := card_orderOf_dvd_half G hev
  by_cases hv : v < n.factorization 2
  · -- atom ⊆ {ord ∣ n/2}
    refine le_trans (Finset.card_le_card ?_) (le_of_eq hH)
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    have hrdvd : orderOf a ∣ n := orderOf_dvd_card
    rw [dvd_half_iff_factorization _ n hrdvd hn0 hev, ha]; exact hv
  · -- atom ⊆ complement {¬ ord ∣ n/2}, whose card is n - n/2 = n/2
    have hsub : (univ.filter (fun a : G => (orderOf a).factorization 2 = v))
        ⊆ univ.filter (fun a : G => ¬ orderOf a ∣ n / 2) := by
      intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      have hrdvd : orderOf a ∣ n := orderOf_dvd_card
      rw [dvd_half_iff_factorization _ n hrdvd hn0 hev, ha]; omega
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Finset.filter_not, Finset.card_univ_diff, ← hn, hH]
    omega

/-! ## §3. (R4 core) The ≥1/2 bound for a product of two even-order cyclic groups. -/

/-- **★ The diagonal `2`-adic-valuation set is at most half. ★**  For `G × H` with both `G`, `H`
    finite cyclic of even order, the set of `(x,y)` with `v₂(ord x) = v₂(ord y)` has at most
    `|G×H|/2` elements.  This is the textbook Shor/Miller counting: it bounds the "bad" set (which,
    through the CRT iso `(ℤ/N)ˣ ≅ (ℤ/p)ˣ×(ℤ/q)ˣ`, is exactly this diagonal — see `ShorReduction`).
    Proof: `diag_card_le` with `c = |H|/2` (every atom of `H` is ≤ `|H|/2`, `card_atom_le_half`). -/
theorem card_diag_v2_le_half (G H : Type*) [Group G] [Group H] [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H] [IsCyclic G] [IsCyclic H]
    (hG : 2 ∣ Fintype.card G) (hH : 2 ∣ Fintype.card H) :
    (univ.filter (fun p : G × H =>
        (orderOf p.1).factorization 2 = (orderOf p.2).factorization 2)).card
      ≤ Fintype.card (G × H) / 2 := by
  have hdiag := diag_card_le (A := G) (B := H)
    (f := fun a : G => (orderOf a).factorization 2)
    (g := fun b : H => (orderOf b).factorization 2)
    (c := Fintype.card H / 2) (fun k => card_atom_le_half H hH k)
  rw [Fintype.card_prod, Nat.mul_div_assoc _ hH]
  exact hdiag

/-! ## §4. (R3) The bad set IS the `v₂`-diagonal — characterization for a product. -/

/-- `orderOf` in a product group is the `lcm` of the component orders. -/
theorem orderOf_prod_mk {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (a : G) (b : H) : orderOf (a, b) = Nat.lcm (orderOf a) (orderOf b) := by
  have key : ∀ n : ℕ, (a, b) ^ n = 1 ↔ a ^ n = 1 ∧ b ^ n = 1 := by
    intro n
    rw [show ((a, b) ^ n) = (a ^ n, b ^ n) from rfl, Prod.mk_eq_one]
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, key]
    exact ⟨orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_left _ _),
           orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_right _ _)⟩
  · rw [Nat.lcm_dvd_iff]
    have h := (key (orderOf (a, b))).mp (pow_orderOf_eq_one (a, b))
    exact ⟨orderOf_dvd_of_pow_eq_one h.1, orderOf_dvd_of_pow_eq_one h.2⟩

/-- `v₂(lcm a b) = max (v₂ a) (v₂ b)`. -/
theorem factorization_lcm_two (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b).factorization 2 = max (a.factorization 2) (b.factorization 2) := by
  rw [Nat.factorization_lcm ha hb, Finsupp.sup_apply]

/-- **★ (R3) The bad set is exactly the `v₂`-diagonal. ★**  In `G × H` (both finite cyclic of even
    order), an element `(x,y)` is "bad" — its order `r` is odd, OR both half-power components
    `x^(r/2)`, `y^(r/2)` are `≠ 1` (i.e. `(x,y)^(r/2)` is the order-2 element `(z₁,z₂)`, which for
    `(ℤ/p)ˣ` is `−1`) — **iff** `v₂(ord x) = v₂(ord y)`.  This is the group-theoretic core of Shor's
    `≥ 1/2`: combined with `card_diag_v2_le_half`, the bad set has at most half the elements. -/
theorem prodBad_iff_diag {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H] [IsCyclic G] [IsCyclic H]
    (x : G) (y : H) :
    (Odd (orderOf (x, y)) ∨
        (x ^ (orderOf (x, y) / 2) ≠ 1 ∧ y ^ (orderOf (x, y) / 2) ≠ 1))
      ↔ (orderOf x).factorization 2 = (orderOf y).factorization 2 := by
  have hr_lcm : orderOf (x, y) = Nat.lcm (orderOf x) (orderOf y) := orderOf_prod_mk x y
  have hdvdx : orderOf x ∣ orderOf (x, y) := by rw [hr_lcm]; exact Nat.dvd_lcm_left _ _
  have hdvdy : orderOf y ∣ orderOf (x, y) := by rw [hr_lcm]; exact Nat.dvd_lcm_right _ _
  have hdr : (orderOf (x, y)).factorization 2
      = max ((orderOf x).factorization 2) ((orderOf y).factorization 2) := by
    rw [hr_lcm]; exact factorization_lcm_two _ _ (orderOf_pos x).ne' (orderOf_pos y).ne'
  by_cases h2 : 2 ∣ orderOf (x, y)
  · -- `r` even: bad ⟺ both v₂ = v₂ r = max ⟺ v₂ ord x = v₂ ord y
    have hx1 : x ^ (orderOf (x, y) / 2) = 1
        ↔ (orderOf x).factorization 2 < (orderOf (x, y)).factorization 2 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact dvd_half_iff_factorization _ _ hdvdx (orderOf_pos _) h2
    have hy1 : y ^ (orderOf (x, y) / 2) = 1
        ↔ (orderOf y).factorization 2 < (orderOf (x, y)).factorization 2 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact dvd_half_iff_factorization _ _ hdvdy (orderOf_pos _) h2
    have hodd : ¬ Odd (orderOf (x, y)) := by rw [Nat.odd_iff]; omega
    constructor
    · rintro (hr | ⟨hxne, hyne⟩)
      · exact absurd hr hodd
      · have hdx : ¬ ((orderOf x).factorization 2 < (orderOf (x, y)).factorization 2) :=
          fun hh => hxne (hx1.mpr hh)
        have hdy : ¬ ((orderOf y).factorization 2 < (orderOf (x, y)).factorization 2) :=
          fun hh => hyne (hy1.mpr hh)
        omega
    · intro hdxy
      refine Or.inr ⟨fun hx => ?_, fun hy => ?_⟩
      · have := hx1.mp hx; omega
      · have := hy1.mp hy; omega
  · -- `r` odd: both v₂ = 0, bad via the odd disjunct
    have hodd : Odd (orderOf (x, y)) := by rw [Nat.odd_iff]; omega
    have hdr0 : (orderOf (x, y)).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2
    constructor
    · intro _; omega
    · intro _; exact Or.inl hodd

/-- **★ The bad set is at most half (abstract product form). ★**  In `G × H` both finite cyclic of
    even order, the set of "bad" `(x,y)` (order odd, or both half-powers `≠ 1`) has at most `|G×H|/2`
    elements — the full Shor/Miller `≥ 1/2`, transported to `(ℤ/N)ˣ` in R4. -/
theorem card_prodBad_le_half (G H : Type*) [Group G] [Group H] [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H] [IsCyclic G] [IsCyclic H]
    (hG : 2 ∣ Fintype.card G) (hH : 2 ∣ Fintype.card H) :
    (univ.filter (fun p : G × H => Odd (orderOf p) ∨
        (p.1 ^ (orderOf p / 2) ≠ 1 ∧ p.2 ^ (orderOf p / 2) ≠ 1))).card
      ≤ Fintype.card (G × H) / 2 := by
  have hset : (univ.filter (fun p : G × H => Odd (orderOf p) ∨
        (p.1 ^ (orderOf p / 2) ≠ 1 ∧ p.2 ^ (orderOf p / 2) ≠ 1)))
      = univ.filter (fun p : G × H =>
        (orderOf p.1).factorization 2 = (orderOf p.2).factorization 2) := by
    apply Finset.filter_congr
    intro p _
    have h := prodBad_iff_diag p.1 p.2
    rwa [Prod.mk.eta] at h
  rw [hset]
  exact card_diag_v2_le_half G H hG hH

end FormalRV.NumberTheory
