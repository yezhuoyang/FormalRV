/-
  FormalRV.NumberTheory.ShorReduction — Shor's classical order→factoring reduction, assembled.

  This is the number theory that turns the quantum order-finding output into a FACTOR of N — the
  link that `Framework.L1_Algorithm.rsa_correct` (`: True := trivial`) was missing.

  PROVEN here (axiom-clean):
  * `shor_classical_step_correct` — if order-finding returns an even order `r` of `a` mod `N` with
    `a^(r/2) ≢ −1`, the classical gcd step yields a NONTRIVIAL factor (the deterministic reduction).
  * `nontrivialSqrt_exists` — for `N = m·n` coprime with `m,n > 2` (every non-prime-power odd N has
    such a split), a nontrivial square root of 1 EXISTS — so the reduction is non-vacuous: a
    factor-yielding `a` is always present.

  REMAINING (the heavy, standard counting — stated, not faked): the success-probability bound
  `goodElementFraction N ≥ 1/2` (a uniformly random coprime `a` has even order with `a^(r/2) ≢ −1`
  with probability ≥ 1/2), which needs the CRT decomposition of `(ℤ/N)ˣ`, the cyclic structure of
  `(ℤ/pᵏ)ˣ`, and the 2-adic-valuation "all-equal" counting (Shor/Miller).  See `GoodElements`.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.NumberTheory.OrderToFactor

namespace FormalRV.NumberTheory

open Int

/-- **★ Shor's classical step is correct. ★**  The number-theoretic content of "order-finding ⇒
    factoring": given the (true, even) multiplicative order `r` of `a` mod `N` with `a^(r/2) ≢ −1`,
    the classical post-processing returns a nontrivial factor of `N`.  `r` minimal (the exact order)
    makes the `a^(r/2) ≢ 1` clause automatic. -/
theorem shor_classical_step_correct (N : ℕ) (hN : 1 < N) (a : ℤ) (r : ℕ)
    (hr_even : Even r) (hr_pos : 0 < r)
    (hr_ord : a ^ r ≡ 1 [ZMOD (N : ℤ)])
    (hr_min : ∀ k, 0 < k → k < r → ¬ a ^ k ≡ 1 [ZMOD (N : ℤ)])
    (hgood : ¬ a ^ (r / 2) ≡ -1 [ZMOD (N : ℤ)]) :
    ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N :=
  order_even_factor N hN a r hr_even hr_pos hr_ord hr_min hgood

/-- **Non-vacuity via CRT: a nontrivial square root of 1 always exists** when `N = m·n` with `m, n`
    coprime and both `> 2`.  (Every odd `N` that is not a prime power admits such a split, e.g.
    `m = pᵏ`, `n = N/pᵏ`.)  So Shor's reduction always has a factor-yielding witness. -/
theorem nontrivialSqrt_exists (m n : ℕ) (hm : 2 < m) (hn : 2 < n) (hcop : Nat.Coprime m n) :
    ∃ x : ℤ, x ^ 2 ≡ 1 [ZMOD ((m * n : ℕ) : ℤ)]
      ∧ ¬ x ≡ 1 [ZMOD ((m * n : ℕ) : ℤ)]
      ∧ ¬ x ≡ -1 [ZMOD ((m * n : ℕ) : ℤ)] := by
  -- CRT: pick k ≡ 1 (mod m), k ≡ n-1 ≡ -1 (mod n)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 1 (n - 1)
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  -- integer congruences for x = k
  have hx_m : (k : ℤ) ≡ 1 [ZMOD (m : ℤ)] := by
    have : (k : ℤ) ≡ (1 : ℕ) [ZMOD (m : ℤ)] := Int.natCast_modEq_iff.mpr hk1
    simpa using this
  have hx_n : (k : ℤ) ≡ -1 [ZMOD (n : ℤ)] := by
    have h0 : (k : ℤ) ≡ ((n - 1 : ℕ) : ℤ) [ZMOD (n : ℤ)] := Int.natCast_modEq_iff.mpr hk2
    have h1 : ((n - 1 : ℕ) : ℤ) ≡ -1 [ZMOD (n : ℤ)] := by
      have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        have : (1 : ℕ) ≤ n := by omega
        push_cast [Nat.cast_sub this]; ring
      rw [this]
      exact (Int.modEq_iff_dvd.mpr (by ring_nf; exact dvd_refl _)).symm
    exact h0.trans h1
  -- squares
  have hsq_m : (k : ℤ) ^ 2 ≡ 1 [ZMOD (m : ℤ)] := by
    calc (k : ℤ) ^ 2 ≡ (1 : ℤ) ^ 2 [ZMOD (m : ℤ)] := hx_m.pow 2
      _ = 1 := by ring
  have hsq_n : (k : ℤ) ^ 2 ≡ 1 [ZMOD (n : ℤ)] := by
    calc (k : ℤ) ^ 2 ≡ (-1 : ℤ) ^ 2 [ZMOD (n : ℤ)] := hx_n.pow 2
      _ = 1 := by ring
  have hcopI : IsCoprime (m : ℤ) (n : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd_natCast_natCast] using hcop
  -- combine via coprime CRT for Int.ModEq
  refine ⟨(k : ℤ), ?_, ?_, ?_⟩
  · -- x^2 ≡ 1 mod m*n
    have := (Int.modEq_and_modEq_iff_modEq_mul (by
      simpa [Int.gcd_natCast_natCast] using hcop)).mp ⟨hsq_m, hsq_n⟩
    simpa [Nat.cast_mul] using this
  · -- x ≢ 1 mod m*n (else x ≡ 1 mod n, but x ≡ -1 ≠ 1)
    intro hcon
    have hn_div : (n : ℤ) ∣ (m * n : ℕ) := by
      rw [Nat.cast_mul]; exact Dvd.intro_left _ rfl
    have : (k : ℤ) ≡ 1 [ZMOD (n : ℤ)] := hcon.of_dvd hn_div
    have hbad : (-1 : ℤ) ≡ 1 [ZMOD (n : ℤ)] := hx_n.symm.trans this
    -- -1 ≡ 1 mod n ⇒ n ∣ 2 ⇒ n ≤ 2, contra n > 2
    have : (n : ℤ) ∣ 2 := by
      have := (Int.modEq_iff_dvd.mp hbad); simpa using this
    have : n ∣ 2 := by exact_mod_cast this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · -- x ≢ -1 mod m*n (else x ≡ -1 mod m, but x ≡ 1 ≠ -1)
    intro hcon
    have hm_div : (m : ℤ) ∣ (m * n : ℕ) := by
      rw [Nat.cast_mul]; exact Dvd.intro _ rfl
    have : (k : ℤ) ≡ -1 [ZMOD (m : ℤ)] := hcon.of_dvd hm_div
    have hbad : (1 : ℤ) ≡ -1 [ZMOD (m : ℤ)] := hx_m.symm.trans this
    have : (m : ℤ) ∣ 2 := by
      have := (Int.modEq_iff_dvd.mp hbad); simpa using this
    have : m ∣ 2 := by exact_mod_cast this
    have := Nat.le_of_dvd (by norm_num) this
    omega

/-- **Putting it together: a coprime non-prime-power split always yields a nontrivial factor of
    `N = m·n` via a nontrivial square root.**  (The efficient route to such a square root is Shor's
    quantum order-finding + `shor_classical_step_correct`; this records that the target exists and is
    extractable by `gcd`.) -/
theorem factor_of_coprime_split (m n : ℕ) (hm : 2 < m) (hn : 2 < n) (hcop : Nat.Coprime m n) :
    ∃ d : ℕ, d ∣ (m * n) ∧ 1 < d ∧ d < m * n := by
  obtain ⟨x, hsq, hne1, hneg1⟩ := nontrivialSqrt_exists m n hm hn hcop
  obtain ⟨hdvd, h1, h2⟩ := nontrivialSqrt_factor (m * n) (by nlinarith) x hsq hne1 hneg1
  exact ⟨Int.gcd (x - 1) ((m * n : ℕ) : ℤ), hdvd, h1, h2⟩

end FormalRV.NumberTheory
