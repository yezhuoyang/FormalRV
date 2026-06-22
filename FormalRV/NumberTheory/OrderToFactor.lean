/-
  FormalRV.NumberTheory.OrderToFactor — from a multiplicative ORDER to a nontrivial FACTOR.

  The classical step of Shor's algorithm: once the quantum subroutine has produced the order `r`
  of `a` mod `N`, IF `r` is even and `a^(r/2) ≢ −1 (mod N)`, then `x := a^(r/2)` is a nontrivial
  square root of 1 (`x² = a^r ≡ 1`, `x ≢ ±1`), so `gcd(x−1, N)` is a nontrivial factor of `N`
  (`NontrivialSqrt.nontrivialSqrt_factor`).  When `r` is the EXACT order, `a^(r/2) ≢ 1` is automatic
  (minimality), so the only nondegeneracy hypothesis is `a^(r/2) ≢ −1` — the standard "good `a`"
  condition whose probability is bounded in `GoodElements`.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.NumberTheory.NontrivialSqrt

namespace FormalRV.NumberTheory

open Int

/-- **Even power giving a nontrivial factor.**  If `r` is even, `a^r ≡ 1 (mod N)`, and
    `a^(r/2) ≢ ±1 (mod N)`, then `N` has a nontrivial factor (`gcd(a^(r/2)−1, N)`). -/
theorem evenPow_factor (N : ℕ) (hN : 1 < N) (a : ℤ) (r : ℕ)
    (hr_even : Even r)
    (hr1 : a ^ r ≡ 1 [ZMOD (N : ℤ)])
    (hhalf1 : ¬ a ^ (r / 2) ≡ 1 [ZMOD (N : ℤ)])
    (hhalf2 : ¬ a ^ (r / 2) ≡ -1 [ZMOD (N : ℤ)]) :
    ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N := by
  obtain ⟨k, hk⟩ := hr_even
  have hpow : (a ^ (r / 2)) ^ 2 ≡ 1 [ZMOD (N : ℤ)] := by
    have he : (a ^ (r / 2)) ^ 2 = a ^ r := by rw [← pow_mul]; congr 1; omega
    rw [he]; exact hr1
  exact ⟨Int.gcd (a ^ (r / 2) - 1) (N : ℤ),
    nontrivialSqrt_factor N hN (a ^ (r / 2)) hpow hhalf1 hhalf2⟩

/-- **★ Order → factor (the exact-order form). ★**  If `r` is the EXACT multiplicative order of `a`
    mod `N` (i.e. `a^r ≡ 1` and `r` is minimal positive with this property), `r` is even, and
    `a^(r/2) ≢ −1 (mod N)`, then `N` has a nontrivial factor.  The `a^(r/2) ≢ 1` clause is FREE here
    (it would contradict minimality), so the only "luck" needed of `a` is even order and
    `a^(r/2) ≢ −1`. -/
theorem order_even_factor (N : ℕ) (hN : 1 < N) (a : ℤ) (r : ℕ)
    (hr_even : Even r) (hr_pos : 0 < r)
    (hr1 : a ^ r ≡ 1 [ZMOD (N : ℤ)])
    (hmin : ∀ k, 0 < k → k < r → ¬ a ^ k ≡ 1 [ZMOD (N : ℤ)])
    (hhalf2 : ¬ a ^ (r / 2) ≡ -1 [ZMOD (N : ℤ)]) :
    ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N := by
  obtain ⟨k, hk⟩ := hr_even
  have hhalf1 : ¬ a ^ (r / 2) ≡ 1 [ZMOD (N : ℤ)] :=
    hmin (r / 2) (by omega) (by omega)
  exact evenPow_factor N hN a r ⟨k, hk⟩ hr1 hhalf1 hhalf2

/-- **The easy case: a common factor with `N`.**  If `1 < gcd(a, N) < N` (i.e. `a` is NOT coprime
    to `N` and not a multiple), the gcd is itself a nontrivial factor — no order needed.  (Shor's
    classical preprocessing: try `gcd(a,N)` first.) -/
theorem common_factor (N : ℕ) (a : ℕ) (h1 : 1 < Nat.gcd a N) (h2 : Nat.gcd a N < N) :
    ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N :=
  ⟨Nat.gcd a N, Nat.gcd_dvd_right a N, h1, h2⟩

end FormalRV.NumberTheory
