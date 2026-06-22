/-
  FormalRV.Shor.CFS.Assumptions — the ONE genuine conjecture underlying CFS / Gidney 2025, stated
  precisely as a `Prop` and NEVER asserted (Gidney 2025, main.tex "Assumption 1", line 345–348).

  Per the project's assumption discipline: things provable by mathematics become theorems (layers
  1–5 of `FormalRV.Shor.CFS`); things genuinely NOT provable become explicit, named assumptions
  taken as hypotheses — never silently `axiom`-ed true.  CFS rests on exactly one such conjecture:
  that a prime set with a large product AND a tiny modular deviation can be found.  We give its
  EXISTENCE statement here (the paper's `O(2^f·poly)` findability is a strengthening we do not need
  for correctness).  No theorem proves `SmallPrimeRNSModulusExists`; downstream results that need it
  take it as a hypothesis, so the dependency is visible.  (Its `ℓ`-bit-free weakening
  `UnboundedPrimeRNSModulusExists` IS provable — see `RNSModulusExistence` — but is useless to the
  algorithm; that is precisely why the `ℓ`-bit clause is load-bearing.)
-/
import FormalRV.Shor.CFS.ModularDeviation

namespace FormalRV.CFS

open scoped BigOperators

/-- **`SmallPrimeRNSModulusExists N m f ℓ`** — Gidney 2025 / CFS **Assumption 1** (main.tex line 346),
    stated precisely and never asserted.  There exists a set `P = {p i}` of primes that is

      * pairwise coprime (automatic for distinct primes, kept explicit for the RNS),
      * **`ℓ`-bit (SMALL): `p i < 2^ℓ`** — the constraint that makes the residue-number-system
        registers small, and the whole reason CFS is efficient,
      * has product `∏P ≥ N^m` (so residue arithmetic mod `L = ∏P` never wraps — eq:bound-L), and
      * has modular deviation `Δ_N(∏P) < 2^{-f}` (so the unknown `L mod N` offset is negligible).

    The deviation condition `Δ_N(L) < 2^{-f}` is encoded with denominators cleared: writing the
    paper's `Δ_N(L) = modDev N L 0 / N`, the inequality `modDev N L 0 / N < 1 / 2^f` is exactly
    `modDev N L 0 * 2^f < N`.

    This is a number-theoretic CONJECTURE (the paper provides numerical evidence and a 25000-prime
    example for RSA-2048 with `Δ < 2^{-32}`, but no proof).  It is the genuine assumption; the
    framework never discharges it.  WARNING: dropping the `ℓ`-bit clause gives the much weaker
    `UnboundedPrimeRNSModulusExists` (in `RNSModulusExistence`), which IS provable (via huge primes
    `≡ 1 mod N`) but is useless for the algorithm — see that file. -/
def SmallPrimeRNSModulusExists (N m f ℓ : ℕ) : Prop :=
  ∃ (t : ℕ) (p : Fin t → ℕ),
    (∀ i j, i ≠ j → Nat.Coprime (p i) (p j)) ∧
    (∀ i, (p i).Prime) ∧
    (∀ i, p i < 2 ^ ℓ) ∧
    N ^ m ≤ ∏ i, p i ∧
    modDev N (∏ i, p i) 0 * 2 ^ f < N

/-- The deviation clause, restated as the paper's `Δ_N(L) < 2^{-f}` with explicit rational
    denominators — a sanity bridge showing the cleared form means what it should. -/
theorem rnsModulus_deviation_meaning (N L f : ℕ) (hN : 0 < N) :
    (modDev N L 0 * 2 ^ f < N) ↔ (modDev N L 0 : ℚ) / N < 1 / 2 ^ f := by
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  constructor
  · intro h; have : (modDev N L 0 : ℚ) * 2 ^ f < (N : ℚ) := by exact_mod_cast h
    linarith [this]
  · intro h
    have : (modDev N L 0 : ℚ) * 2 ^ f < (N : ℚ) := by
      have := h; push_cast at this ⊢; linarith
    exact_mod_cast this

#verify_clean rnsModulus_deviation_meaning

end FormalRV.CFS
