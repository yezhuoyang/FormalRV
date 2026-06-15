/-
  FormalRV.SQIRPort.TotientLowerBound

  Elementary proof of the Euler totient lower bound used by Shor:

      ((Nat.totient r : ℝ) / r) ≥ Real.exp (-2) / (Nat.log2 N)^4

  whenever `0 < r ≤ N`.

  The proof avoids Mertens' theorem entirely; the target bound is weak
  enough that an elementary distinct-prime-factor argument suffices:

  1. The number of distinct prime factors of `r` is at most `log₂ r`
     (each prime is ≥ 2 and their product divides `r`).
  2. The totient ratio admits the product representation
     `φ(r)/r = ∏_{p | r} (1 - 1/p)`.
  3. Sorting the distinct primes `p_0 < p_1 < ... < p_{k-1}`, we have
     `p_i ≥ i + 2`, so `1 - 1/p_i ≥ (i+1)/(i+2)`, and the product
     telescopes to `1/(k+1)`.
  4. Hence `φ(r)/r ≥ 1/(card+1) ≥ 1/(log₂ r + 1) ≥ 1/(log₂ N + 1)`.
  5. Real-arithmetic: `1/(L+1) ≥ exp(-2)/L^4` for all `L : ℕ`.
-/

import Mathlib

namespace FormalRV.SQIRPort

open Real

noncomputable def totFactor (p : Nat) : ℝ := 1 - (p : ℝ)⁻¹

/-! ## Step A: indexed lower bound for sorted Nat lists -/

/-- **Strictly-sorted list of Nats ≥ b has i-th element ≥ i + b.** Induction
on the list, threading an increasing offset through the cons case. -/
private lemma sorted_lower_bound (xs : List Nat) (h_sorted : xs.Pairwise (· < ·))
    (b : Nat) (h_b : ∀ x ∈ xs, b ≤ x)
    (i : Nat) (hi : i < xs.length) :
    i + b ≤ xs[i]'hi := by
  induction xs generalizing b i with
  | nil => simp at hi
  | cons hd tl ih =>
    cases i with
    | zero => simp; exact h_b hd (by simp)
    | succ k =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      simp only [List.getElem_cons_succ]
      have h_tl_sorted : tl.Pairwise (· < ·) := h_sorted.of_cons
      have h_tl_b : ∀ x ∈ tl, b + 1 ≤ x := by
        intros x hx
        rcases h_sorted with _ | ⟨h_hd, _⟩
        have hd_lt_x : hd < x := h_hd x hx
        have : b ≤ hd := h_b hd (by simp)
        omega
      have ih_app := ih h_tl_sorted (b + 1) h_tl_b k hi
      omega

/-! ## Step B: per-factor bounds -/

private lemma totFactor_nonneg (p : Nat) (hp : 1 ≤ p) : 0 ≤ totFactor p := by
  unfold totFactor
  have : (p : ℝ) ≥ 1 := by exact_mod_cast hp
  have h_inv : (p : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; linarith
  linarith

/-- **Per-factor lower bound**: for `p ≥ s + 1` with `s ≥ 1`,
`totFactor p = 1 - 1/p ≥ s/(s+1)`. -/
private lemma totFactor_ge_one_sub_inv (p s : Nat) (hp : s + 1 ≤ p) (hs : 1 ≤ s) :
    (s : ℝ) / ((s : ℝ) + 1) ≤ totFactor p := by
  unfold totFactor
  have hp_R : (p : ℝ) ≥ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast hp
  have h_sp1_R : ((s + 1 : ℕ) : ℝ) = (s : ℝ) + 1 := by push_cast; ring
  rw [h_sp1_R] at hp_R
  have hs_R : (s : ℝ) ≥ 1 := by exact_mod_cast hs
  have hs1_pos : (s : ℝ) + 1 > 0 := by linarith
  have hp_pos : (p : ℝ) > 0 := by linarith
  have h_inv : (p : ℝ)⁻¹ ≤ ((s : ℝ) + 1)⁻¹ := by
    have h1 : 1 / (p : ℝ) ≤ 1 / ((s : ℝ) + 1) := one_div_le_one_div_of_le hs1_pos hp_R
    simpa [one_div] using h1
  have h_eq : (s : ℝ) / ((s : ℝ) + 1) = 1 - ((s : ℝ) + 1)⁻¹ := by
    field_simp; ring
  rw [h_eq]; linarith

/-! ## Step C: list-level product bound -/

/-- **List-level telescoped product bound**. For a strictly-sorted list `xs`
of Nats each ≥ `c + 1` (where `c ≥ 1`),
`∏_{x ∈ xs} (1 - 1/x) ≥ c / (c + xs.length)`. Proof by induction on the
list, threading the offset through the cons case. The base case is
`c/c = 1`; the step uses `1 - 1/hd ≥ c/(c+1)` plus the IH applied at
offset `c + 1`. -/
private lemma list_prod_one_sub_inv_from
    (xs : List Nat) (h_sorted : xs.Pairwise (· < ·))
    (c : Nat) (h_c : 1 ≤ c) (h_b : ∀ x ∈ xs, c + 1 ≤ x) :
    (c : ℝ) / ((c + xs.length : ℕ) : ℝ) ≤ (xs.map totFactor).prod := by
  induction xs generalizing c with
  | nil =>
    simp
    have h_c_R : (c : ℝ) ≥ 1 := by exact_mod_cast h_c
    have h_c_pos : (c : ℝ) > 0 := by linarith
    rw [div_self h_c_pos.ne']
  | cons hd tl ih =>
    have h_hd_ge : c + 1 ≤ hd := h_b hd (by simp)
    have h_tl_sorted : tl.Pairwise (· < ·) := h_sorted.of_cons
    have h_tl_b : ∀ x ∈ tl, c + 1 + 1 ≤ x := by
      intros x hx
      rcases h_sorted with _ | ⟨h_hd, _⟩
      have : hd < x := h_hd x hx
      omega
    have ih_app := ih h_tl_sorted (c + 1) (by omega) h_tl_b
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    have h_hd_factor : (c : ℝ) / ((c : ℝ) + 1) ≤ totFactor hd :=
      totFactor_ge_one_sub_inv hd c h_hd_ge h_c
    have h_prod_nonneg : 0 ≤ (tl.map totFactor).prod := by
      apply List.prod_nonneg
      intros y hy
      rcases List.mem_map.mp hy with ⟨p, hp, rfl⟩
      have : 1 ≤ p := by have := h_tl_b p hp; omega
      exact totFactor_nonneg p this
    have h_c_R : (c : ℝ) ≥ 1 := by exact_mod_cast h_c
    have h_div_pos : (c : ℝ) / ((c : ℝ) + 1) ≥ 0 := by positivity
    have h_step :
        ((c : ℝ) / ((c : ℝ) + 1)) *
          (((c + 1 : ℕ) : ℝ) / ((c + 1 + tl.length : ℕ) : ℝ))
          ≤ totFactor hd * (tl.map totFactor).prod := by
      have h_num_nn : ((c + 1 : ℕ) : ℝ) ≥ 0 := by positivity
      have h_den_pos : ((c + 1 + tl.length : ℕ) : ℝ) > 0 := by
        have : 0 < c + 1 + tl.length := by omega
        exact_mod_cast this
      have h_div_aux : 0 ≤ (((c + 1 : ℕ) : ℝ) / ((c + 1 + tl.length : ℕ) : ℝ)) :=
        div_nonneg h_num_nn h_den_pos.le
      have h_totFactor_nn : 0 ≤ totFactor hd := le_trans h_div_pos h_hd_factor
      exact mul_le_mul h_hd_factor ih_app h_div_aux h_totFactor_nn
    have h_simplify :
        (c : ℝ) / ((c + (tl.length + 1) : ℕ) : ℝ)
          = ((c : ℝ) / ((c : ℝ) + 1)) *
            (((c + 1 : ℕ) : ℝ) / ((c + 1 + tl.length : ℕ) : ℝ)) := by
      have h1 : ((c + 1 : ℕ) : ℝ) = (c : ℝ) + 1 := by push_cast; ring
      have h2 : ((c + (tl.length + 1) : ℕ) : ℝ) = (c : ℝ) + tl.length + 1 := by
        push_cast; ring
      have h3 : ((c + 1 + tl.length : ℕ) : ℝ) = (c : ℝ) + tl.length + 1 := by
        push_cast; ring
      rw [h1, h2, h3]
      have h_c_pos : (c : ℝ) > 0 := by linarith
      have h_sum_pos : (c : ℝ) + tl.length + 1 > 0 := by linarith
      have h_cp1_pos : (c : ℝ) + 1 > 0 := by linarith
      field_simp
    rw [h_simplify]; exact h_step

/-! ## Step D: Finset-level product bound for primeFactors -/

/-- **Pairwise (· < ·) for sorted primeFactors list.** -/
private lemma primeFactors_sort_pairwise_lt (n : Nat) :
    (n.primeFactors.sort (· ≤ ·)).Pairwise (· < ·) := by
  have h_nodup : (n.primeFactors.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  have h_sorted : (n.primeFactors.sort (· ≤ ·)).Pairwise (· ≤ ·) :=
    Finset.pairwise_sort _ _
  have h_ne : (n.primeFactors.sort (· ≤ ·)).Pairwise (· ≠ ·) :=
    List.nodup_iff_pairwise_ne.mp h_nodup
  exact h_sorted.and h_ne |>.imp (fun ⟨h_le, h_ne⟩ => lt_of_le_of_ne h_le h_ne)

/-- **Bridge to Finset product** via the sort permutation. -/
private lemma sort_map_totFactor_prod (n : Nat) :
    ((n.primeFactors.sort (· ≤ ·)).map totFactor).prod
      = ∏ p ∈ n.primeFactors, totFactor p := by
  rw [← Finset.prod_map_toList]
  apply List.Perm.prod_eq
  apply List.Perm.map
  exact Finset.sort_perm_toList _ _

/-- **Product lower bound on primeFactors** (Finset form): for any `n`,
`∏_{p | n} (1 - 1/p) ≥ 1/(card(primeFactors n) + 1)`. -/
theorem primeFactors_totient_product_ge (n : Nat) :
    (1 : ℝ) / ((n.primeFactors.card + 1 : ℕ) : ℝ)
      ≤ ∏ p ∈ n.primeFactors, totFactor p := by
  rw [← sort_map_totFactor_prod n]
  -- Apply list_prod_one_sub_inv_from with c = 1.
  have h_sort_pairwise : (n.primeFactors.sort (· ≤ ·)).Pairwise (· < ·) :=
    primeFactors_sort_pairwise_lt n
  have h_two_le : ∀ x ∈ n.primeFactors.sort (· ≤ ·), 2 ≤ x := by
    intros x hx
    have hx_pf : x ∈ n.primeFactors := (Finset.mem_sort _).mp hx
    exact (Nat.prime_of_mem_primeFactors hx_pf).two_le
  have h_b : ∀ x ∈ n.primeFactors.sort (· ≤ ·), 1 + 1 ≤ x := h_two_le
  have h_len : (n.primeFactors.sort (· ≤ ·)).length = n.primeFactors.card :=
    Finset.length_sort _
  have h_bound := list_prod_one_sub_inv_from (n.primeFactors.sort (· ≤ ·))
    h_sort_pairwise 1 (le_refl _) h_b
  -- h_bound : (1 : ℝ) / ((1 + sort.length : ℕ) : ℝ) ≤ ...
  rw [h_len] at h_bound
  -- Goal: 1 / ↑(card + 1) ≤ prod
  -- h_bound: ↑1 / ↑(1 + card) ≤ prod
  -- Convert via comm.
  have h_eq : ((n.primeFactors.card + 1 : ℕ) : ℝ) = ((1 + n.primeFactors.card : ℕ) : ℝ) := by
    push_cast; ring
  rw [h_eq]
  convert h_bound using 1
  norm_num

/-! ## Step E: distinct-prime-factor count is at most log₂ -/

/-- **Distinct-prime-factor count bound**: `card(primeFactors n) ≤ log₂ n` for
`n > 0`. Proof: `∏_{p ∈ primeFactors n} p ≥ 2^card` (each prime ≥ 2) and
divides `n` (so ≤ n for n > 0). Combine to get `2^card ≤ n`, hence
`card ≤ log₂ n` via `Nat.le_log2`. -/
theorem card_primeFactors_le_log2 (n : Nat) (hn : 0 < n) :
    n.primeFactors.card ≤ Nat.log2 n := by
  rw [Nat.le_log2 hn.ne']
  have h_each_ge : ∀ p ∈ n.primeFactors, 2 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le
  have h_pow_le_prod : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    have h1 : ∏ _ ∈ n.primeFactors, (2 : Nat) ≤ ∏ p ∈ n.primeFactors, p :=
      Finset.prod_le_prod' h_each_ge
    calc 2 ^ n.primeFactors.card
        = ∏ _ ∈ n.primeFactors, (2 : Nat) := by simp [Finset.prod_const]
      _ ≤ ∏ p ∈ n.primeFactors, p := h1
  have h_prod_dvd : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
  have h_prod_le : (∏ p ∈ n.primeFactors, p) ≤ n := Nat.le_of_dvd hn h_prod_dvd
  exact le_trans h_pow_le_prod h_prod_le

/-! ## Step F: real-arithmetic tail bound `1/(L+1) ≥ exp(-2)/L^4` -/

/-- **Real-arithmetic tail bound**: `exp(-2)/L^4 ≤ 1/(L+1)` for all `L : ℕ`.

- `L = 0`: RHS = 1, LHS = `exp(-2)/0` = 0 in ℝ. `1 ≥ 0`. ✓
- `L ≥ 1`: rearrange to `(L+1) · exp(-2) ≤ L^4`, then case on `L`.

Proof handles `L = 0` separately (division by zero in ℝ is `0`); for
`L ≥ 1` uses `exp(-2) ≤ 1/2` (a standard bound) combined with
`L^4 ≥ L+1` for `L ≥ 1`. -/
theorem exp_neg_two_div_pow_four_le_one_div_succ (L : Nat) :
    Real.exp (-2) / (L : ℝ)^4 ≤ 1 / ((L : ℝ) + 1) := by
  by_cases hL : L = 0
  · subst hL
    simp
  · have hL_pos : 0 < L := Nat.pos_of_ne_zero hL
    have hL_R : (L : ℝ) ≥ 1 := by exact_mod_cast hL_pos
    have hL_pow_pos : (0 : ℝ) < (L : ℝ)^4 := by positivity
    have hLp1_pos : (0 : ℝ) < (L : ℝ) + 1 := by linarith
    rw [div_le_div_iff₀ hL_pow_pos hLp1_pos]
    -- Goal: exp(-2) * (L + 1) ≤ 1 * L^4
    rw [one_mul]
    -- Need: exp(-2) * (L + 1) ≤ L^4.
    -- Use exp(-2) ≤ 1/2 (standard).
    have h_exp_le : Real.exp (-2) ≤ 1 / 2 := by
      have : Real.exp (-2) = (Real.exp 2)⁻¹ := by
        rw [Real.exp_neg]
      rw [this]
      have h_exp2_ge : Real.exp 2 ≥ 2 := by
        have := Real.add_one_le_exp (2 : ℝ)
        linarith
      rw [inv_le_iff_one_le_mul₀ (by linarith : (0 : ℝ) < Real.exp 2)]
      linarith
    -- LHS ≤ (1/2) * (L + 1)
    have h_lhs_bound : Real.exp (-2) * ((L : ℝ) + 1) ≤ (1/2) * ((L : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_right h_exp_le (by linarith)
    -- Need: (1/2) * (L + 1) ≤ L^4 for L ≥ 1
    -- For L = 1: (1/2)*2 = 1 ≤ 1 = L^4. ✓
    -- For L ≥ 2: (L+1)/2 ≤ L ≤ L^4. ✓
    have h_half_bound : (1/2 : ℝ) * ((L : ℝ) + 1) ≤ (L : ℝ)^4 := by
      have h_pow_ge : (L : ℝ)^4 ≥ (L : ℝ) := by
        have h1 : (L : ℝ)^4 = (L : ℝ) * (L : ℝ)^3 := by ring
        rw [h1]
        have h_pow3_ge_one : (L : ℝ)^3 ≥ 1 := by
          have : (L : ℝ)^3 ≥ (1 : ℝ)^3 := pow_le_pow_left₀ (by linarith) hL_R 3
          simpa using this
        nlinarith [hL_R, h_pow3_ge_one]
      have h_half_LP1 : (1/2 : ℝ) * ((L : ℝ) + 1) ≤ (L : ℝ) := by linarith
      linarith
    linarith

/-! ## Final assembly: the Shor totient lower bound -/

/-- **`phi_n_over_n_lowerbound`** — elementary proof, replacing the axiom
of the same name in `Shor.lean`.

For `0 < r ≤ N`, the Euler totient ratio satisfies

    φ(r) / r  ≥  exp(-2) / (log₂ N)^4.

Assembly chain:
1. `Nat.totient_eq_mul_prod_factors`: `φ(r) = r · ∏_{p | r} (1 - 1/p)`,
   so `φ(r)/r = ∏ totFactor p`.
2. `primeFactors_totient_product_ge`: `∏ totFactor p ≥ 1/(card+1)`,
   via the strictly-sorted-list telescoping argument.
3. `card_primeFactors_le_log2`: `card ≤ log₂ r`, via
   `2^card ≤ ∏ p ≤ r`.
4. `Nat.log2_le_log2`: `log₂ r ≤ log₂ N`, so `1/(card+1) ≥ 1/(log₂ N + 1)`.
5. `exp_neg_two_div_pow_four_le_one_div_succ`: `1/(L+1) ≥ exp(-2)/L^4`,
   handling `L = 0` separately. -/
theorem phi_n_over_n_lowerbound_proved (r N : Nat) (h_r_pos : 0 < r) (h_le : r ≤ N) :
    ((Nat.totient r : ℝ) / (r : ℝ))
      ≥ Real.exp (-2) / (Nat.log2 N : ℝ)^4 := by
  have h_r_R_pos : (0 : ℝ) < r := by exact_mod_cast h_r_pos
  have h_id : (Nat.totient r : ℝ) / (r : ℝ) = ∏ p ∈ r.primeFactors, totFactor p := by
    have h := Nat.totient_eq_mul_prod_factors r
    have hQ : ((r.totient : ℚ) : ℝ)
              = ((r : ℚ) * ∏ p ∈ r.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) := by
      exact_mod_cast h
    push_cast at hQ
    have hR : (r.totient : ℝ)
              = (r : ℝ) * ∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹) := hQ
    rw [hR]
    -- Each summand: 1 - 1/p = totFactor p (definitional).
    have h_factor_eq : ∀ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹ : ℝ) = totFactor p :=
      fun p _ => rfl
    rw [Finset.prod_congr rfl h_factor_eq]
    field_simp
  rw [h_id]
  have h1 : (1 : ℝ) / ((r.primeFactors.card + 1 : ℕ) : ℝ)
            ≤ ∏ p ∈ r.primeFactors, totFactor p :=
    primeFactors_totient_product_ge r
  have h2 : r.primeFactors.card ≤ Nat.log2 r := card_primeFactors_le_log2 r h_r_pos
  have h_log2_le : Nat.log2 r ≤ Nat.log2 N := by
    rw [Nat.le_log2 (by omega : N ≠ 0)]
    exact le_trans (Nat.log2_self_le h_r_pos.ne') h_le
  have h_card_le : r.primeFactors.card ≤ Nat.log2 N := le_trans h2 h_log2_le
  have h_card_le_R : ((r.primeFactors.card + 1 : ℕ) : ℝ) ≤ ((Nat.log2 N + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right h_card_le 1
  have h_card_pos : (0 : ℝ) < ((r.primeFactors.card + 1 : ℕ) : ℝ) := by
    have : 0 < r.primeFactors.card + 1 := by omega
    exact_mod_cast this
  have h_inv_le : (1 : ℝ) / ((Nat.log2 N + 1 : ℕ) : ℝ)
                  ≤ 1 / ((r.primeFactors.card + 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le h_card_pos h_card_le_R
  have h_real := exp_neg_two_div_pow_four_le_one_div_succ (Nat.log2 N)
  have h_cast : ((Nat.log2 N + 1 : ℕ) : ℝ) = (Nat.log2 N : ℝ) + 1 := by push_cast; ring
  rw [h_cast] at h_inv_le
  linarith

end FormalRV.SQIRPort
