/-
  FormalRV.Shor.CFS.EkeraLemma7 — the FAITHFUL Ekerå–Håstad Lemma 7 (1702.00249,
  `lemma-probability-good-pair`): a specific good pair occurs with probability ≥ 2^{-(m+ℓ+2)}.

  This formalises the paper's ACTUAL argument (NOT the factorised two-1-register-peak idealisation),
  built bottom-up from its three claims:

    * `sum_unit_vectors_sq_ge`  — `claim-sum-unit-vectors` (constructive interference): a sum of `N`
      unit phasors all within angle `π/4` has squared modulus `≥ N²/2`.  Elementary: the real part
      is `≥ N·cos(π/4) = N/√2`.
    * `good_pair_angle_le`      — the good-pair condition `|{dj+2^m k}_{2^(ℓ+m)}| ≤ 2^{m-2}` forces
      every per-`b` phase angle `(2π/2^(ℓ+m))·(b−2^{ℓ-1})·{dj+2^m k}` to be `≤ π/4` (the paper's
      bound, l.646–651).
    * `sq_sum_le_card_mul_sum_sq` / `sum_Te_sq_ge` — `claim-sum-Te-2`: Cauchy–Schwarz gives
      `∑_e T_e² ≥ (∑_e T_e)² / (#e) = 2^{3ℓ+m−1}`.

  The per-outcome phase here is the paper's EXACT fixed formula `(b − 2^{ℓ-1})·{dj + 2^m k}` — a
  function of the outcome `(j,k)` and the summation index `b`, NOT a per-outcome free choice; the
  good-pair hypothesis is genuinely used.  No `sorry`, no `native_decide`, no axioms beyond prelude.
-/
import Mathlib
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS.EkeraLemma7

open scoped BigOperators

/-! ## §1. `claim-sum-unit-vectors` — constructive interference. -/

/-- **Ekerå–Håstad `claim-sum-unit-vectors` (1702.00249 l.316–343).**  If `N` phase angles all satisfy
    `|θ i| ≤ π/4`, then `|∑ exp(i θ_i)|² ≥ N²/2`.  Proof: the real part is `∑ cos θ_i ≥ N·(√2/2)`
    (since `cos` is `≥ √2/2 = cos(π/4)` on `[−π/4, π/4]`), and `normSq z ≥ (re z)²`. -/
theorem sum_unit_vectors_sq_ge {ι : Type*} (s : Finset ι) (θ : ι → ℝ)
    (hθ : ∀ i ∈ s, |θ i| ≤ Real.pi / 4) :
    (s.card : ℝ) ^ 2 / 2
      ≤ Complex.normSq (∑ i ∈ s, Complex.exp ((θ i : ℂ) * Complex.I)) := by
  -- the real part of the sum is `∑ cos θ_i`
  have hre : (∑ i ∈ s, Complex.exp ((θ i : ℂ) * Complex.I)).re = ∑ i ∈ s, Real.cos (θ i) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.exp_mul_I, Complex.add_re, Complex.cos_ofReal_re, Complex.mul_I_re,
        Complex.sin_ofReal_im]
    ring
  -- each `cos θ_i ≥ √2/2`
  have hcoslb : ∀ i ∈ s, Real.sqrt 2 / 2 ≤ Real.cos (θ i) := by
    intro i hi
    rw [← Real.cos_abs, ← Real.cos_pi_div_four]
    refine Real.strictAntiOn_cos.antitoneOn ⟨abs_nonneg _, ?_⟩ ⟨by positivity, ?_⟩ (hθ i hi)
    · exact le_trans (hθ i hi) (by linarith [Real.pi_pos])
    · linarith [Real.pi_pos]
  -- so `∑ cos θ_i ≥ card·(√2/2)`
  have hsumcos : (s.card : ℝ) * (Real.sqrt 2 / 2) ≤ ∑ i ∈ s, Real.cos (θ i) := by
    calc (s.card : ℝ) * (Real.sqrt 2 / 2)
        = ∑ _i ∈ s, (Real.sqrt 2 / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, Real.cos (θ i) := Finset.sum_le_sum hcoslb
  have hcard_nonneg : (0 : ℝ) ≤ (s.card : ℝ) * (Real.sqrt 2 / 2) := by positivity
  -- `normSq ≥ (re)²`
  have hnsq : ((∑ i ∈ s, Complex.exp ((θ i : ℂ) * Complex.I)).re) ^ 2
      ≤ Complex.normSq (∑ i ∈ s, Complex.exp ((θ i : ℂ) * Complex.I)) := by
    rw [Complex.normSq_apply, sq]
    nlinarith [mul_self_nonneg (∑ i ∈ s, Complex.exp ((θ i : ℂ) * Complex.I)).im]
  rw [hre] at hnsq
  -- `(card·√2/2)² = card²/2`
  have hval : ((s.card : ℝ) * (Real.sqrt 2 / 2)) ^ 2 = (s.card : ℝ) ^ 2 / 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
  calc (s.card : ℝ) ^ 2 / 2
      = ((s.card : ℝ) * (Real.sqrt 2 / 2)) ^ 2 := hval.symm
    _ ≤ (∑ i ∈ s, Real.cos (θ i)) ^ 2 := by
        apply pow_le_pow_left₀ hcard_nonneg hsumcos
    _ ≤ Complex.normSq (∑ i ∈ s, Complex.exp ((θ i : ℂ) * Complex.I)) := hnsq

#verify_clean sum_unit_vectors_sq_ge

/-! ## §2. The good-pair angle bound (1702.00249 l.646–651). -/

/-- **The good-pair angle bound.**  For `0 ≤ b < 2^ℓ` and a balanced residue `c` with `|c| ≤ 2^{m-2}`,
    the per-`b` phase angle `(2π/2^(ℓ+m))·(b − 2^{ℓ-1})·c` has absolute value `≤ π/4`.  (Because
    `|b − 2^{ℓ-1}| ≤ 2^{ℓ-1}` and `2^{ℓ-1}·2^{m-2}·(2π)/2^(ℓ+m) = 2π/8 = π/4`.) -/
theorem good_pair_angle_le (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (hm : 2 ≤ m)
    (b : ℕ) (hb : b < 2 ^ ℓ) (c : ℤ) (hc : |c| ≤ 2 ^ (m - 2)) :
    |(2 * Real.pi / (2 : ℝ) ^ (ℓ + m)) * ((b : ℝ) - (2 : ℝ) ^ (ℓ - 1)) * (c : ℝ)| ≤ Real.pi / 4 := by
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hBpos : (0 : ℝ) < (2 : ℝ) ^ (ℓ - 1) := by positivity
  have hCpos : (0 : ℝ) < (2 : ℝ) ^ (m - 2) := by positivity
  have hpow : (2 : ℝ) ^ (ℓ + m) = 8 * (2 : ℝ) ^ (ℓ - 1) * (2 : ℝ) ^ (m - 2) := by
    rw [show ℓ + m = (ℓ - 1) + (m - 2) + 3 by omega, pow_add, pow_add]; ring
  have h2l : (2 : ℝ) ^ ℓ = 2 * (2 : ℝ) ^ (ℓ - 1) := by
    rw [mul_comm, ← pow_succ]; congr 1; omega
  have hbR : (b : ℝ) < 2 * (2 : ℝ) ^ (ℓ - 1) := by rw [← h2l]; exact_mod_cast hb
  have hbabs : |(b : ℝ) - (2 : ℝ) ^ (ℓ - 1)| ≤ (2 : ℝ) ^ (ℓ - 1) := by
    rw [abs_le]
    exact ⟨by nlinarith [Nat.cast_nonneg (α := ℝ) b], by nlinarith [hbR]⟩
  have hcabs : |(c : ℝ)| ≤ (2 : ℝ) ^ (m - 2) := by
    rw [← Int.cast_abs]; exact_mod_cast hc
  have hK : (0 : ℝ) ≤ 2 * Real.pi / (2 : ℝ) ^ (ℓ + m) := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hK, hpow]
  calc (2 * Real.pi / (8 * (2 : ℝ) ^ (ℓ - 1) * (2 : ℝ) ^ (m - 2)))
          * |(b : ℝ) - (2 : ℝ) ^ (ℓ - 1)| * |(c : ℝ)|
      ≤ (2 * Real.pi / (8 * (2 : ℝ) ^ (ℓ - 1) * (2 : ℝ) ^ (m - 2)))
          * (2 : ℝ) ^ (ℓ - 1) * (2 : ℝ) ^ (m - 2) := by
        apply mul_le_mul _ hcabs (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hbabs (by positivity)
    _ = Real.pi / 4 := by field_simp; ring

/-! ## §3. The `T_e` Cauchy–Schwarz bound (`claim-sum-Te-2`). -/

/-- **`claim-sum-Te-2` (1702.00249 l.617–632).**  If `∑_{e∈E} T_e = 2^{2ℓ+m}` and `E` indexes at most
    `2·2^{ℓ+m}` values of `e`, then `∑_{e∈E} T_e² ≥ 2^{3ℓ+m-1}` (Cauchy–Schwarz). -/
theorem sum_Te_sq_ge {ιe : Type*} (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (E : Finset ιe) (T : ιe → ℝ)
    (hEcard : (E.card : ℝ) ≤ 2 * (2 : ℝ) ^ (ℓ + m))
    (hTtot : ∑ e ∈ E, T e = (2 : ℝ) ^ (2 * ℓ + m)) :
    (2 : ℝ) ^ (3 * ℓ + m - 1) ≤ ∑ e ∈ E, (T e) ^ 2 := by
  have hCS : (∑ e ∈ E, T e) ^ 2 ≤ (E.card : ℝ) * ∑ e ∈ E, (T e) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hTtot] at hCS
  have hXnn : 0 ≤ ∑ e ∈ E, (T e) ^ 2 := Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have hsq : ((2 : ℝ) ^ (2 * ℓ + m)) ^ 2 = (2 : ℝ) ^ (4 * ℓ + 2 * m) := by
    rw [← pow_mul]; congr 1; omega
  have hsplit : (2 : ℝ) ^ (4 * ℓ + 2 * m)
      = (2 * (2 : ℝ) ^ (ℓ + m)) * (2 : ℝ) ^ (3 * ℓ + m - 1) := by
    rw [show (4 * ℓ + 2 * m) = 1 + (ℓ + m) + (3 * ℓ + m - 1) by omega, pow_add, pow_add]; ring
  rw [hsq, hsplit] at hCS
  have hpos : (0 : ℝ) < 2 * (2 : ℝ) ^ (ℓ + m) := by positivity
  have h1 : (2 * (2 : ℝ) ^ (ℓ + m)) * (2 : ℝ) ^ (3 * ℓ + m - 1)
      ≤ (2 * (2 : ℝ) ^ (ℓ + m)) * (∑ e ∈ E, (T e) ^ 2) :=
    le_trans hCS (mul_le_mul_of_nonneg_right hEcard hXnn)
  exact le_of_mul_le_mul_left h1 hpos

/-! ## §4. Lemma 7 assembled — the per-good-pair probability floor `≥ 2^{-(m+ℓ+2)}`. -/

/-- **★ Ekerå–Håstad Lemma 7 (1702.00249 `lemma-probability-good-pair`), the faithful assembly. ★**
    Let `E` index the third-register outcomes `e`, `Be e` the valid `b`-set for `e` (so `(Be e).card`
    is the paper's `T_e`), and `θ e b` the paper's exact centered phase
    `(2π/2^(ℓ+m))·(b − 2^{ℓ-1})·{dj+2^m k}`.  If — for a GOOD pair — every phase angle is `≤ π/4`
    (`hangle`, supplied by `good_pair_angle_le`), the number of `e`-values is `≤ 2·2^{ℓ+m}` (`hEcard`,
    `claim-interval-e`) and the total pair count is `∑_e T_e = 2^{2ℓ+m}` (`hTtot`, `claim-sum-Te`),
    then the measurement probability of `(j,k)` is `≥ 2^{-(m+ℓ+2)}`.

    Proof = the paper's: constructive interference (`sum_unit_vectors_sq_ge`) per `e` gives
    `|∑_b …|² ≥ T_e²/2`; Cauchy–Schwarz (`sum_Te_sq_ge`) gives `∑_e T_e² ≥ 2^{3ℓ+m-1}`; the prefactor
    `1/2^{2(2ℓ+m)}` then yields `2^{-(m+ℓ+2)}`.

    `hEcard`/`hTtot` are the paper's two elementary `(a,b)`-COUNTING claims (`claim-interval-e`,
    `claim-sum-Te`) — pure combinatorics about the index ranges, stated as hypotheses; the genuinely
    analytic content (constructive interference + Cauchy–Schwarz) is fully proven. -/
theorem ekera_lemma7 {ιe : Type*} (ℓ m : ℕ) (hℓ : 1 ≤ ℓ)
    (E : Finset ιe) (Be : ιe → Finset ℕ) (θ : ιe → ℕ → ℝ)
    (hangle : ∀ e ∈ E, ∀ b ∈ Be e, |θ e b| ≤ Real.pi / 4)
    (hEcard : (E.card : ℝ) ≤ 2 * (2 : ℝ) ^ (ℓ + m))
    (hTtot : ∑ e ∈ E, ((Be e).card : ℝ) = (2 : ℝ) ^ (2 * ℓ + m)) :
    (2 : ℝ) ^ (-(ℓ + m + 2 : ℤ))
      ≤ (1 / (2 : ℝ) ^ (2 * (2 * ℓ + m)))
          * ∑ e ∈ E, Complex.normSq (∑ b ∈ Be e, Complex.exp ((θ e b : ℂ) * Complex.I)) := by
  set S := ∑ e ∈ E, Complex.normSq (∑ b ∈ Be e, Complex.exp ((θ e b : ℂ) * Complex.I)) with hSdef
  have hper : ∀ e ∈ E, ((Be e).card : ℝ) ^ 2 / 2
      ≤ Complex.normSq (∑ b ∈ Be e, Complex.exp ((θ e b : ℂ) * Complex.I)) :=
    fun e he => sum_unit_vectors_sq_ge (Be e) (θ e) (fun b hb => hangle e he b hb)
  have hsum : (∑ e ∈ E, ((Be e).card : ℝ) ^ 2) / 2 ≤ S := by
    rw [Finset.sum_div]; exact Finset.sum_le_sum hper
  have hTe : (2 : ℝ) ^ (3 * ℓ + m - 1) ≤ ∑ e ∈ E, ((Be e).card : ℝ) ^ 2 :=
    sum_Te_sq_ge ℓ m hℓ E (fun e => ((Be e).card : ℝ)) hEcard hTtot
  have hSge : (2 : ℝ) ^ (3 * ℓ + m - 1) / 2 ≤ S := le_trans (by linarith [hTe]) hsum
  have hz : (2 : ℝ) ^ (-(↑ℓ + ↑m + 2 : ℤ)) = 1 / (2 : ℝ) ^ (ℓ + m + 2) := by
    rw [show (-(↑ℓ + ↑m + 2 : ℤ)) = -((ℓ + m + 2 : ℕ) : ℤ) by push_cast; ring,
        zpow_neg, zpow_natCast, one_div]
  have hnat : (1 / (2 : ℝ) ^ (2 * (2 * ℓ + m))) * ((2 : ℝ) ^ (3 * ℓ + m - 1) / 2)
      = 1 / (2 : ℝ) ^ (ℓ + m + 2) := by
    rw [div_mul_div_comm, one_mul, div_eq_div_iff (by positivity) (by positivity),
        one_mul, ← pow_add, ← pow_succ]
    congr 1; omega
  calc (2 : ℝ) ^ (-(↑ℓ + ↑m + 2 : ℤ))
      = (1 / (2 : ℝ) ^ (2 * (2 * ℓ + m))) * ((2 : ℝ) ^ (3 * ℓ + m - 1) / 2) := by
        rw [hnat, hz]
    _ ≤ (1 / (2 : ℝ) ^ (2 * (2 * ℓ + m))) * S := mul_le_mul_of_nonneg_left hSge (by positivity)

#verify_clean good_pair_angle_le
#verify_clean sum_Te_sq_ge
#verify_clean ekera_lemma7

/-! ## §5. Discharging the counting claims `claim-interval-e` / `claim-sum-Te`.

We instantiate the index structure concretely: `e` ranges over the integer interval
`(−2^(ℓ+m), 2^(ℓ+m))` (`claim-interval-e`), and `Be e` is the valid `b`-set
`{ b < 2^ℓ : 0 ≤ e+bd < 2^(ℓ+m) }`.  Then `#e ≤ 2·2^(ℓ+m)` and `∑_e T_e = 2^(2ℓ+m)` are proven by
elementary `Int` interval counting + a Fubini double-count — making `ekera_lemma7` UNCONDITIONAL on
the combinatorial side. -/

/-- The `e`-range: integers strictly between `−2^(ℓ+m)` and `2^(ℓ+m)` (`claim-interval-e`). -/
noncomputable def ehE (ℓ m : ℕ) : Finset ℤ := Finset.Ioo (-(2 : ℤ) ^ (ℓ + m)) ((2 : ℤ) ^ (ℓ + m))

/-- The valid-`b` set for outcome `e`: `b ∈ [0, 2^ℓ)` with `0 ≤ e + b·d < 2^(ℓ+m)`
    (equivalently `a = e + b·d ∈ [0, 2^(ℓ+m))`). -/
noncomputable def ehBe (ℓ m d : ℕ) (e : ℤ) : Finset ℕ :=
  (Finset.range (2 ^ ℓ)).filter
    (fun b => 0 ≤ e + (b : ℤ) * (d : ℤ) ∧ e + (b : ℤ) * (d : ℤ) < (2 : ℤ) ^ (ℓ + m))

/-- **`claim-interval-e` (1702.00249 l.593–602).**  At most `2·2^(ℓ+m)` values of `e`. -/
theorem ehE_card_le (ℓ m : ℕ) : ((ehE ℓ m).card : ℝ) ≤ 2 * (2 : ℝ) ^ (ℓ + m) := by
  have hcard : (ehE ℓ m).card ≤ 2 * 2 ^ (ℓ + m) := by
    unfold ehE
    rw [Int.card_Ioo]
    rw [Int.toNat_le]
    push_cast
    have : (0 : ℤ) < 2 ^ (ℓ + m) := by positivity
    linarith
  calc ((ehE ℓ m).card : ℝ) ≤ ((2 * 2 ^ (ℓ + m) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = 2 * (2 : ℝ) ^ (ℓ + m) := by push_cast; ring

/-- The per-`b` fibre count: for each `b < 2^ℓ`, exactly `2^(ℓ+m)` values of `e ∈ ehE` keep
    `a = e+bd` in range (the bijection `e ↦ e+bd` with `[0, 2^(ℓ+m))`). -/
theorem eh_per_b_count (ℓ m d : ℕ) (hdlt : d < 2 ^ m) (b : ℕ) (hb : b < 2 ^ ℓ) :
    ((ehE ℓ m).filter
        (fun e => 0 ≤ e + (b : ℤ) * (d : ℤ) ∧ e + (b : ℤ) * (d : ℤ) < (2 : ℤ) ^ (ℓ + m))).card
      = 2 ^ (ℓ + m) := by
  have hb0 : (0 : ℤ) ≤ (b : ℤ) * (d : ℤ) := by positivity
  have hbd : (b : ℤ) * (d : ℤ) < (2 : ℤ) ^ (ℓ + m) := by
    have h1 : (b : ℤ) ≤ (2 : ℤ) ^ ℓ := by exact_mod_cast Nat.le_of_lt_succ (Nat.lt_succ_of_lt hb)
    have h2 : (d : ℤ) < (2 : ℤ) ^ m := by exact_mod_cast hdlt
    calc (b : ℤ) * (d : ℤ) < (2 : ℤ) ^ ℓ * (2 : ℤ) ^ m :=
          mul_lt_mul' h1 h2 (by positivity) (by positivity)
      _ = (2 : ℤ) ^ (ℓ + m) := by rw [pow_add]
  have heq : (ehE ℓ m).filter
        (fun e => 0 ≤ e + (b : ℤ) * (d : ℤ) ∧ e + (b : ℤ) * (d : ℤ) < (2 : ℤ) ^ (ℓ + m))
      = Finset.Ico (-((b : ℤ) * (d : ℤ))) ((2 : ℤ) ^ (ℓ + m) - (b : ℤ) * (d : ℤ)) := by
    ext e
    simp only [ehE, Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Ico]
    constructor
    · rintro ⟨_, h3, h4⟩; omega
    · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  rw [heq, Int.card_Ico, show (2 : ℤ) ^ (ℓ + m) - (b : ℤ) * (d : ℤ) - -((b : ℤ) * (d : ℤ))
        = (2 : ℤ) ^ (ℓ + m) by ring]
  rw [show ((2 : ℤ) ^ (ℓ + m)) = (((2 ^ (ℓ + m) : ℕ)) : ℤ) by push_cast; ring, Int.toNat_natCast]

/-- **`claim-sum-Te` (1702.00249 l.605–615).**  `∑_e T_e = 2^(2ℓ+m)` (total `(a,b)` pairs), by
    Fubini over `b` and the per-`b` fibre count. -/
theorem ehTtot (ℓ m d : ℕ) (hdlt : d < 2 ^ m) :
    ∑ e ∈ ehE ℓ m, ((ehBe ℓ m d e).card : ℝ) = (2 : ℝ) ^ (2 * ℓ + m) := by
  have hNat : ∑ e ∈ ehE ℓ m, (ehBe ℓ m d e).card = 2 ^ (2 * ℓ + m) := by
    have hswap : ∑ e ∈ ehE ℓ m, (ehBe ℓ m d e).card
        = ∑ b ∈ Finset.range (2 ^ ℓ),
            ((ehE ℓ m).filter (fun e => 0 ≤ e + (b : ℤ) * (d : ℤ)
              ∧ e + (b : ℤ) * (d : ℤ) < (2 : ℤ) ^ (ℓ + m))).card := by
      simp only [ehBe, Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hswap]
    rw [Finset.sum_congr rfl (fun b hb => eh_per_b_count ℓ m d hdlt b (Finset.mem_range.mp hb))]
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← pow_add]
    congr 1; omega
  calc ∑ e ∈ ehE ℓ m, ((ehBe ℓ m d e).card : ℝ)
      = ((∑ e ∈ ehE ℓ m, (ehBe ℓ m d e).card : ℕ) : ℝ) := by push_cast; rfl
    _ = ((2 ^ (2 * ℓ + m) : ℕ) : ℝ) := by rw [hNat]
    _ = (2 : ℝ) ^ (2 * ℓ + m) := by push_cast; ring

/-- **★ Ekerå–Håstad Lemma 7, UNCONDITIONAL on the combinatorics. ★**  For distinct-prime / short-DLP
    parameters (`ℓ ≥ 1`, `m ≥ 2`, `0 < d < 2^m`) and a GOOD pair (balanced residue `c` with
    `|c| ≤ 2^{m-2}`), the Ekerå–Håstad measurement probability is `≥ 2^{-(m+ℓ+2)}` — with the two
    counting claims `claim-interval-e` and `claim-sum-Te` now DISCHARGED (`ehE_card_le`, `ehTtot`).
    The only remaining (circuit-level) step is identifying this probability EXPRESSION with the
    physical Born probability (the paper's steps 1–4 QFT algebra, on `short_dlp_orbit_joint_eigen`). -/
theorem ekera_lemma7_unconditional (ℓ m d : ℕ) (hℓ : 1 ≤ ℓ) (hm : 2 ≤ m) (hdlt : d < 2 ^ m)
    (c : ℤ) (hc : |c| ≤ 2 ^ (m - 2)) :
    (2 : ℝ) ^ (-(ℓ + m + 2 : ℤ))
      ≤ (1 / (2 : ℝ) ^ (2 * (2 * ℓ + m)))
          * ∑ e ∈ ehE ℓ m, Complex.normSq (∑ b ∈ ehBe ℓ m d e,
              Complex.exp (((2 * Real.pi / (2 : ℝ) ^ (ℓ + m))
                * ((b : ℝ) - (2 : ℝ) ^ (ℓ - 1)) * (c : ℝ) : ℝ) * Complex.I)) := by
  refine ekera_lemma7 ℓ m hℓ (ehE ℓ m) (ehBe ℓ m d)
    (fun _e b => (2 * Real.pi / (2 : ℝ) ^ (ℓ + m)) * ((b : ℝ) - (2 : ℝ) ^ (ℓ - 1)) * (c : ℝ))
    (fun e _he b hb => ?_) (ehE_card_le ℓ m) (ehTtot ℓ m d hdlt)
  have hb' : b < 2 ^ ℓ := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  exact good_pair_angle_le ℓ m hℓ hm b hb' c hc

#verify_clean ehE_card_le
#verify_clean eh_per_b_count
#verify_clean ehTtot
#verify_clean ekera_lemma7_unconditional

end FormalRV.CFS.EkeraLemma7
