/-
  FormalRV.Shor.VerifiedShor.RelaxedSetting
  ─────────────────────────────────────────
  Shor-algorithm SETTING predicates for the verified modular multiplier.
  Relocated here (from Arithmetic/ModMult) so the ModMult folder stays purely
  about modular multiplication: these mention `Order` / QPE register sizing —
  Shor setup, not modmult arithmetic. No proofs.
-/
import FormalRV.Arithmetic.ModMult

namespace FormalRV.BQAlgo

open FormalRV.Framework

/-- Relaxed `BasicSetting` (drops the unused `2^n ≤ 2N` bound).
**Deprecated 2026-05-29:** `VerifiedShor.ShorSetting` is an `abbrev` for this. -/
def BasicSettingRelaxed (a r N m n : Nat) : Prop :=
  (0 < a ∧ a < N) ∧
  FormalRV.SQIRPort.Order a r N ∧
  (N ^ 2 < 2 ^ m ∧ 2 ^ m ≤ 2 * N ^ 2) ∧
  N < 2 ^ n

/-- Sizing predicate for the verified SQIR multiplier (`2N ≤ 2^bits`).
**Deprecated 2026-05-29:** `VerifiedShor.CircuitSizing` is an `abbrev` for this. -/
def VerifiedCircuitSizing (N bits : Nat) : Prop :=
  1 ≤ bits ∧ N ≤ 2 ^ bits ∧ 2 * N ≤ 2 ^ bits

end FormalRV.BQAlgo
