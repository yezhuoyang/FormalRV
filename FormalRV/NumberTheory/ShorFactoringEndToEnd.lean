/-
  FormalRV.NumberTheory.ShorFactoringEndToEnd — the END-TO-END Shor factoring success theorem.
  ════════════════════════════════════════════════════════════════════════════════════════════

  GAP ④ CLOSED — axiom-clean, NO literature conjecture, NO Ekerå–Håstad heuristic.

  This composes the two already-axiom-clean halves of Shor's factoring algorithm into ONE
  factoring-success-probability bound on the actual measurement distribution:

    • QUANTUM order-finding  (`Shor_correct_var_relaxed`, axiom-clean):  with probability
      `≥ κ/(log₂N)⁴` the QPE measurement + continued-fraction post-processing `OF_post`
      recovers the true multiplicative order `r` of `a` mod `N`.
    • CLASSICAL reduction    (`shor_classical_step_correct`, axiom-clean):  for a GOOD base `a`
      (even order, `a^(r/2) ≢ −1`), the recovered order DETERMINISTICALLY yields a NONTRIVIAL
      FACTOR of `N` via the gcd step.
    • COUNTING               (`card_good_ge_half`, axiom-clean):  for `N = p·q` (distinct odd
      primes), at least half the bases are good.

  HEADLINE `shor_factoring_succeeds_good_base`:  for a good base,
      `factoringSuccessProb a N m n anc u ≥ κ/(log₂N)⁴`  ∧  `∃ d, d ∣ N ∧ 1 < d ∧ d < N`,
  where `factoringSuccessProb` is the measure of measurement outcomes whose post-processed order
  yields a nontrivial factor — i.e. the probability the algorithm outputs a FACTOR of `N`, not
  merely the order.

  WHY NO EKERÅ–HÅSTAD / ASSUMPTION 1:  this is VANILLA order-finding (continued fractions on a
  full `m`-bit phase register, `Shor_correct_var_relaxed`).  Ekerå–Håstad (short-exponent
  discrete log) is a qubit-COUNT optimisation that lets the phase register be shorter; it is NOT
  required for factoring CORRECTNESS, and its success heuristic ("Assumption 1") is therefore
  NOT invoked anywhere in this closure.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.VerifiedShor.RelaxedQPE_MMI
import FormalRV.NumberTheory.ShorReduction
import FormalRV.NumberTheory.ShorBadSet

namespace FormalRV.NumberTheory.ShorFactoring

open FormalRV.SQIRPort
open FormalRV.BQAlgo

/-! ## §1. The "recovered order witnesses a factor" predicate. -/

/-- A recovered order `o` WITNESSES a factor of `N`: it is the true even multiplicative order of
    `a` mod `N` (positive, `a^o ≡ 1`, minimal) with `a^(o/2) ≢ −1` — exactly Shor's good
    condition.  By minimality this holds iff `o = ord_N(a)` and `a` is a good base. -/
def factorWitnessed (a N o : Nat) : Prop :=
  Even o ∧ 0 < o ∧ (a : ℤ) ^ o ≡ 1 [ZMOD (N : ℤ)] ∧
  (∀ k, 0 < k → k < o → ¬ (a : ℤ) ^ k ≡ 1 [ZMOD (N : ℤ)]) ∧
  ¬ (a : ℤ) ^ (o / 2) ≡ -1 [ZMOD (N : ℤ)]

/-- A witnessed order deterministically yields a nontrivial factor (Shor's classical gcd step). -/
theorem factorWitnessed_yields_factor {a N o : Nat} (hN : 1 < N)
    (h : factorWitnessed a N o) : ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N := by
  obtain ⟨he, hpos, hord, hmin, hgood⟩ := h
  exact shor_classical_step_correct N hN (a : ℤ) o he hpos hord hmin hgood

/-! ## §2. Nat-order ⇒ Int-congruence bridges (the `% N` ↔ `[ZMOD N]` glue). -/

/-- `a^r % N = 1`  ⇒  `(a:ℤ)^r ≡ 1 [ZMOD N]`  (for `1 < N`). -/
theorem pow_modEq_one_int {a r N : Nat} (hN : 1 < N) (h : a ^ r % N = 1) :
    (a : ℤ) ^ r ≡ 1 [ZMOD (N : ℤ)] := by
  have hmod : a ^ r ≡ 1 [MOD N] := by
    unfold Nat.ModEq; rw [h, Nat.mod_eq_of_lt hN]
  have h1 : ((a ^ r : ℕ) : ℤ) ≡ ((1 : ℕ) : ℤ) [ZMOD (N : ℤ)] :=
    Int.natCast_modEq_iff.mpr hmod
  push_cast at h1; exact h1

/-- minimality transfer: `∀ s, a^s % N ≠ 1` ⇒ `∀ k, ¬ (a:ℤ)^k ≡ 1 [ZMOD N]` (for `1 < N`). -/
theorem pow_ne_one_int {a r N : Nat} (hN : 1 < N)
    (hmin : ∀ s, 0 < s → s < r → a ^ s % N ≠ 1) :
    ∀ k, 0 < k → k < r → ¬ (a : ℤ) ^ k ≡ 1 [ZMOD (N : ℤ)] := by
  intro k hk0 hkr hcon
  have h1 : ((a ^ k : ℕ) : ℤ) ≡ ((1 : ℕ) : ℤ) [ZMOD (N : ℤ)] := by push_cast; exact hcon
  have hmod : a ^ k ≡ 1 [MOD N] := Int.natCast_modEq_iff.mp h1
  have hval : a ^ k % N = 1 := by
    have := hmod; unfold Nat.ModEq at this; rwa [Nat.mod_eq_of_lt hN] at this
  exact hmin k hk0 hkr hval

/-! ## §3. The factoring-success probability. -/

open Classical in
/-- 0/1 indicator: the post-processed order `o` from a measurement outcome yields a factor. -/
noncomputable def factorIndicator (a N o : Nat) : ℝ :=
  if factorWitnessed a N o then 1 else 0

/-- **The factoring-success probability** — the measure of measurement outcomes `x` whose
    continued-fraction-recovered order `OF_post a N x m` yields a nontrivial factor of `N`.  This
    is the probability the WHOLE algorithm (QPE + post-processing + classical gcd) outputs a
    FACTOR of `N`, not merely the order. -/
noncomputable def factoringSuccessProb (a N m n anc : Nat)
    (u : Nat → BaseUCom (n + anc)) : ℝ :=
  ∑ x ∈ Finset.range (2 ^ m),
    factorIndicator a N (OF_post a N x m) *
      prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc u)

/-- For a good base, every outcome that recovers the true order is also a factor-yielding
    outcome:  `r_found x m r a N ≤ factorIndicator a N (OF_post a N x m)`. -/
theorem r_found_le_factorIndicator {a r N : Nat} (hN : 1 < N)
    (h_ord : Order a r N) (hr_even : Even r)
    (hgood : ¬ (a : ℤ) ^ (r / 2) ≡ -1 [ZMOD (N : ℤ)])
    (x m : Nat) :
    r_found x m r a N ≤ factorIndicator a N (OF_post a N x m) := by
  obtain ⟨hr_pos, h_arN, h_min⟩ := h_ord
  rcases eq_or_ne (OF_post a N x m) r with hx | hx
  · have hfw : factorWitnessed a N (OF_post a N x m) := by
      rw [hx]
      exact ⟨hr_even, hr_pos, pow_modEq_one_int hN h_arN, pow_ne_one_int hN h_min, hgood⟩
    have heq : r_found x m r a N = factorIndicator a N (OF_post a N x m) := by
      unfold r_found factorIndicator; rw [if_pos hx, if_pos hfw]
    exact le_of_eq heq
  · have hz : r_found x m r a N = 0 := by unfold r_found; rw [if_neg hx]
    rw [hz]; unfold factorIndicator; split_ifs <;> norm_num

/-! ## §4. THE HEADLINE — Shor's algorithm outputs a factor with prob `≥ κ/(log₂N)⁴`. -/

/-- **★ GAP ④ CLOSED — end-to-end Shor factoring success for a good base ★.**  For a base `a`
    with (even) multiplicative order `r` mod `N` and `a^(r/2) ≢ −1` (a "good" base), running
    Shor's algorithm with ANY correct modular-multiplier family `u`:

    1. outputs a nontrivial factor of `N` with probability `≥ κ/(log₂N)⁴`
       (`factoringSuccessProb`), and
    2. the factor concretely exists (`∃ d, d ∣ N ∧ 1 < d ∧ d < N`).

    Both halves are axiom-clean: (1) composes the quantum order-finding bound
    (`Shor_correct_var_relaxed`) with the deterministic classical reduction, since recovering the
    order entails recovering a factor for a good base; (2) is `shor_classical_step_correct`.

    This is VANILLA order-finding — no Ekerå–Håstad, no Assumption 1. -/
theorem shor_factoring_succeeds_good_base
    {a r N m n anc : Nat} {u : Nat → BaseUCom (n + anc)}
    (h_setting : BasicSettingRelaxed a r N m n)
    (h_modmul : ModMulImpl a N n anc u)
    (h_wt : ∀ i, i < m → uc_well_typed (u i))
    (hN : 1 < N)
    (hr_even : Even r)
    (hgood : ¬ (a : ℤ) ^ (r / 2) ≡ -1 [ZMOD (N : ℤ)]) :
    factoringSuccessProb a N m n anc u ≥ κ / (Nat.log2 N : ℝ) ^ 4
    ∧ ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N := by
  have h_ord : Order a r N := BasicSettingRelaxed_order h_setting
  obtain ⟨hr_pos, h_arN, h_min⟩ := h_ord
  refine ⟨?_, ?_⟩
  · -- factoringSuccessProb ≥ probability_of_success ≥ κ/(log₂N)⁴
    have hqpe : probability_of_success a r N m n anc u ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
      Shor_correct_var_relaxed a r N m n anc u h_setting h_modmul h_wt
    have hge : probability_of_success a r N m n anc u ≤ factoringSuccessProb a N m n anc u := by
      unfold probability_of_success factoringSuccessProb
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_right
        (r_found_le_factorIndicator hN ⟨hr_pos, h_arN, h_min⟩ hr_even hgood x m)
        (prob_partial_meas_nonneg _ _)
    linarith
  · exact factorWitnessed_yields_factor hN
      ⟨hr_even, hr_pos, pow_modEq_one_int hN h_arN, pow_ne_one_int hN h_min, hgood⟩

/-! ## §5. The good-base fraction is `≥ ½` (Shor/Miller counting), making `a` random-choosable. -/

/-- **The good-base fraction is `≥ ½`.**  For `N = p·q` (distinct odd primes) at least half the
    units `a ∈ (ℤ/N)ˣ` are good (even order, `a^(ord/2) ≠ −1`) — so a uniformly random base feeds
    `shor_factoring_succeeds_good_base` with probability `≥ 1/2`, giving the standard
    `O((log N)⁴)`-expected-shot factoring algorithm.  Re-exported from `card_good_ge_half`. -/
theorem good_base_fraction_ge_half {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 2 < p) (hq : 2 < q) (hpq : p ≠ q) :
    Fintype.card (ZMod (p * q))ˣ / 2 ≤
      (Finset.univ.filter (fun a : (ZMod (p * q))ˣ =>
        ¬ (Odd (orderOf a) ∨ a ^ (orderOf a / 2) = -1))).card :=
  card_good_ge_half hp hq hpq

end FormalRV.NumberTheory.ShorFactoring
