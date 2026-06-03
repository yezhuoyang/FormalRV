/-
  FormalRV.Arithmetic.SQIRModMult.ModExpCount — a CONCRETE Shor modular-exponentiation
  circuit (the explicit chain of verified modular multipliers) with an EXACT T-count.

  `shorModExp bits N a` is a concrete `Gate` IR term: the sequential composition of
  `2·bits` verified modular multipliers (`sqir_modmult_const_gate`), one per exponent-
  register bit, multiplying by `a^(2^k)`.  Its T-count is EXACTLY `112·bits³` for any valid
  Shor base — not a bound.  So the formula is provably the gate count of the actual circuit:
  if you compiled `shorModExp 2048 N a` and counted its T-gates, you would get exactly
  `112·2048³` (and exactly `16·2048³ = 137 438 953 472` Toffolis / magic states).

  EXACT, derived by induction (math — the 2048 circuit is never built), no `sorry`/`axiom`.
-/
import FormalRV.Arithmetic.SQIRModMult.ToffoliCount

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- Concrete Shor modular exponentiation as the explicit chain of `m` verified modular
    multipliers: step `k` multiplies by `a^(2^k)` (reduced mod `N` internally by the
    multiplier).  This is the exact `Gate` IR whose count the formulas below compute. -/
def shorModExpChain (m bits N a : Nat) : Gate :=
  match m with
  | 0 => Gate.I
  | k + 1 => seq (shorModExpChain k bits N a) (sqir_modmult_const_gate bits N (a ^ 2 ^ k))

/-- **EXACT** T-count of the `m`-fold modular-multiplier chain: `m · 56·bits²`, for any
    valid Shor base (`gcd(a,N)=1`, `N` odd, `N>1` — so every multiplier step is non-trivial). -/
theorem tcount_shorModExpChain (m bits N a : Nat)
    (hcop : Nat.Coprime a N) (hodd : Odd N) (h1 : 1 < N) :
    tcount (shorModExpChain m bits N a) = m * (56 * bits ^ 2) := by
  induction m with
  | zero => simp [shorModExpChain, tcount]
  | succ k ih =>
      simp only [shorModExpChain, tcount]
      rw [ih, tcount_sqir_modmult_const_gate_shor bits N (a ^ 2 ^ k)
            (hcop.pow_left _) hodd h1]
      ring

/-- The full Shor modular exponentiation: `2·bits` modular multipliers (the full-precision
    exponent register of order finding). -/
def shorModExp (bits N a : Nat) : Gate := shorModExpChain (2 * bits) bits N a

/-- **EXACT** T-count of the full concrete Shor modular exponentiation: `112·bits³`. -/
theorem tcount_shorModExp (bits N a : Nat)
    (hcop : Nat.Coprime a N) (hodd : Odd N) (h1 : 1 < N) :
    tcount (shorModExp bits N a) = 112 * bits ^ 3 := by
  unfold shorModExp
  rw [tcount_shorModExpChain (2 * bits) bits N a hcop hodd h1]; ring

/-! ## Smoke check: the formula matches the ACTUAL circuit's count at a concrete base.

    `N = 15, a = 7` is a valid base (coprime, odd, > 1).  The formula gives `112·4³ = 7168`;
    `#eval` traverses the actual `Gate` term and counts the same — i.e. "compile the
    circuit, count exactly the calculated number". -/

example : tcount (shorModExp 4 15 7) = 112 * 4 ^ 3 :=
  tcount_shorModExp 4 15 7 (by decide) (by decide) (by decide)

#eval tcount (shorModExp 4 15 7)     -- 7168  (actual circuit traversal)
#eval (112 * 4 ^ 3 : Nat)            -- 7168  (the formula)

end FormalRV.BQAlgo
