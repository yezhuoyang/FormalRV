/-
  FormalRV.NumberTheory — the classical number theory Shor's algorithm needs to FACTOR.

  Shor's quantum subroutine finds the multiplicative order `r` of `a` mod `N`
  (`FormalRV.SQIRPort.Shor_correct_var`).  Turning that order into a FACTOR of `N` is pure classical
  number theory, previously absent from this repo (`Framework.L1_Algorithm.rsa_correct : True`).
  This folder supplies it, separating PROVEN mathematics from genuinely-conjectural assumptions.

  PROVEN (all axiom-clean `[propext, Classical.choice, Quot.sound]`):
  * `NontrivialSqrt` — a nontrivial square root of 1 mod N yields a nontrivial factor via gcd.
  * `OrderToFactor` — even order `r` with `a^(r/2) ≢ −1` yields a nontrivial factor
    (`order_even_factor`); plus the common-factor easy case.
  * `ShorReduction` — `shor_classical_step_correct` (the order→factor reduction) and
    `nontrivialSqrt_exists` / `factor_of_coprime_split` (non-vacuity via CRT: a factor-witness always
    exists for a coprime non-prime-power split).
  * `GoodElements` — the Shor/Miller `≥ 1/2` COUNTING, in full: in any finite cyclic group of even
    order every `v₂(ord)`-atom is `≤ |G|/2` (`card_atom_le_half`); for a product `G × H` the
    `v₂`-diagonal is `≤ |G×H|/2` (`card_diag_v2_le_half`); the "bad" set IS that diagonal
    (`prodBad_iff_diag`, via `orderOf` = lcm and `v₂`(lcm) = max), so `card_prodBad_le_half`.
  * `ShorBadSet` — the `≥ 1/2` bound TRANSPORTED to `(ℤ/N)ˣ` for `N = p·q` (distinct odd primes) via
    the CRT iso + the field square-root dichotomy `s^(r/2) = −1 ↔ s^(r/2) ≠ 1`:
    `card_bad_le_half` (`|{a : ord a odd ∨ a^(ord a/2) = −1}| ≤ φ(N)/2`) and its complement
    `card_good_ge_half` (a uniformly random unit is good — yields a factor — with probability ≥ 1/2).

  REMAINING (genuinely conjectural — NOT proven, never faked):
  * `FormalRV.CFS.SmallPrimeRNSModulusExists` (Gidney 2025 / CFS prime-set + modular-deviation conjecture) and the
    Ekerå-2023 short-DLP success lemmas — the papers themselves leave these conjectural / give only
    analytic bounds; they remain explicit named assumptions, not theorems.
-/
import FormalRV.NumberTheory.NontrivialSqrt
import FormalRV.NumberTheory.OrderToFactor
import FormalRV.NumberTheory.ShorReduction
import FormalRV.NumberTheory.GoodElements
import FormalRV.NumberTheory.ShorBadSet
-- The END-TO-END composition (GAP ④): the quantum order-finding bound (`Shor_correct_var_relaxed`)
-- welded to the classical reduction into ONE factoring-success-probability theorem
-- `shor_factoring_succeeds_good_base` (`factoringSuccessProb ≥ κ/(log₂N)⁴` ∧ a factor exists).
-- Axiom-clean, VANILLA order-finding — no Ekerå–Håstad, no Assumption 1.
import FormalRV.NumberTheory.ShorFactoringEndToEnd
