/-
  FormalRV.NumberTheory.NontrivialSqrt — the deterministic heart of Shor's classical
  order→factoring reduction: a NONTRIVIAL square root of 1 mod N yields a NONTRIVIAL factor.

  ## Why this is THE necessary number theory

  Shor's quantum subroutine finds the multiplicative order `r` of `a` mod `N`
  (`FormalRV.SQIRPort.Shor_correct_var` : `probability_of_success ≥ κ/(log₂N)⁴`).  By itself
  that does NOT factor `N` — the bridge from "order found" to "factor found" is purely classical
  number theory, and in this repo it was previously absent (`Framework.L1_Algorithm.rsa_correct`
  is literally `: True := trivial`).  This file (and `OrderToFactor`, `ShorReduction`) supplies it.

  The crux: if `x² ≡ 1 (mod N)` but `x ≢ ±1 (mod N)`, then `N ∣ (x−1)(x+1)` while `N ∤ (x−1)` and
  `N ∤ (x+1)`, so `gcd(x−1, N)` is a PROPER, NONTRIVIAL divisor of `N` (`1 < gcd < N`).  Taking
  `x = a^(r/2)` for an even order `r` with `a^(r/2) ≢ −1` gives Shor's factor.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import Mathlib

namespace FormalRV.NumberTheory

open Int

/-- **★ A nontrivial square root of 1 gives a nontrivial factor. ★**  If `x² ≡ 1 (mod N)` with
    `x ≢ 1` and `x ≢ −1 (mod N)` (and `N > 1`), then `gcd(x−1, N)` is a proper nontrivial divisor
    of `N`: it divides `N`, exceeds `1`, and is `< N`.  This is the classical core of Shor's
    factoring reduction — no quantum content. -/
theorem nontrivialSqrt_factor (N : ℕ) (hN : 1 < N) (x : ℤ)
    (hsq : x ^ 2 ≡ 1 [ZMOD (N : ℤ)])
    (hne1 : ¬ x ≡ 1 [ZMOD (N : ℤ)])
    (hneg1 : ¬ x ≡ -1 [ZMOD (N : ℤ)]) :
    (Int.gcd (x - 1) (N : ℤ)) ∣ N
      ∧ 1 < Int.gcd (x - 1) (N : ℤ)
      ∧ Int.gcd (x - 1) (N : ℤ) < N := by
  set g : ℕ := Int.gcd (x - 1) (N : ℤ) with hg
  -- N ∣ (x-1)(x+1)
  have hdvd : (N : ℤ) ∣ (x - 1) * (x + 1) := by
    have h : (N : ℤ) ∣ 1 - x ^ 2 := Int.ModEq.dvd hsq
    have he : (1 : ℤ) - x ^ 2 = -((x - 1) * (x + 1)) := by ring
    rw [he] at h
    exact (dvd_neg.mp h)
  -- g ∣ N (as naturals)
  have hgN : g ∣ N := by
    have : (g : ℤ) ∣ (N : ℤ) := Int.gcd_dvd_right (x - 1) (N : ℤ)
    exact_mod_cast this
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgN (by omega)
  have hgle : g ≤ N := Nat.le_of_dvd (by omega) hgN
  -- g ≠ N : else N ∣ (x-1) ⇒ x ≡ 1
  have hgneN : g ≠ N := by
    intro hEq
    have hdvdx : (N : ℤ) ∣ (x - 1) := by
      have : (g : ℤ) ∣ (x - 1) := Int.gcd_dvd_left (x - 1) (N : ℤ)
      rwa [hEq] at this
    exact hne1 (Int.ModEq.symm ((Int.modEq_iff_dvd).mpr (by simpa using hdvdx)))
  -- g ≠ 1 : else gcd(x-1,N)=1, with N ∣ (x-1)(x+1) ⇒ N ∣ (x+1) ⇒ x ≡ -1
  have hgne1 : g ≠ 1 := by
    intro hEq
    have hcop : IsCoprime (x - 1) (N : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]; exact hEq
    have hNx1 : (N : ℤ) ∣ (x + 1) :=
      (hcop.symm).dvd_of_dvd_mul_left hdvd
    -- N ∣ (x+1) = x - (-1) ⇒ x ≡ -1
    have : x ≡ -1 [ZMOD (N : ℤ)] :=
      Int.ModEq.symm ((Int.modEq_iff_dvd).mpr (by simpa [sub_neg_eq_add] using hNx1))
    exact hneg1 this
  exact ⟨hgN, by omega, by omega⟩

end FormalRV.NumberTheory
