/-
  FormalRV.Arithmetic.SQIRModMult.SQIRModMultSizing
  ─────────────────────────────────────────────────
  Sizing / setting predicates for the verified modular multiplier.

  NOTE: `BasicSettingRelaxed` is a Shor-algorithm SETTING predicate (it mentions
  `Order` and the QPE register sizing) and is STAGED here pending relocation to
  `Shor/VerifiedShor/` together with the Shor-correctness proofs. `VerifiedCircuitSizing`
  (`2N ≤ 2^bits`) is genuinely about the multiplier register. No proofs.
-/
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultDef

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
