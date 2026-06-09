/-
  FormalRV.Arithmetic.ModExp.ModExpResource — EXACT T-counts of two concrete mod-exp-shaped
  `Gate` IR chains.  The counts are exact and machine-checked; the LABELS below are carefully
  honest about what each chain is (a counting audit, 2026-06-03, flagged earlier overclaims).

  TWO chains, TWO numbers — do NOT confuse them:

  * `shorModExp` (this section): chains the OUT-OF-PLACE `modmult_const_gate` (8·bits²
    Toffoli/step).  T-count EXACTLY `112·bits³` (= 16·bits³ Toffoli; `16·2048³ =
    137 438 953 472`).  ⚠ This is a COUNTING MODEL only: an out-of-place multiplier writes
    `a·x` into a FRESH accumulator with no feedback, so a chain of them does NOT compute
    modular exponentiation.  It is NOT the term the verified Shor algorithm uses.  Keep it
    only as the per-step structural skeleton.

  * `shorModExpVerified` (below): chains the IN-PLACE verified oracle `modmult_MCP_gate`
    (16·bits² Toffoli/step) — the term the verified Shor theorem actually uses.  T-count
    EXACTLY `224·bits³` (= 32·bits³ Toffoli; `32·2048³ = 274 877 906 944` = 2× the above, the
    in-place forward+uncompute factor).  This is the honest verified-oracle arithmetic figure.

  HONEST STATUS (CLAUDE.md "semantic correctness before resource counts"): the COUNTS are
  exact, but NEITHER chain has a proof that it computes `a^x mod N`.  Each per-step multiplier
  is semantically verified (`const_gate`: (a·m)%N decode; `MCP`: MultiplyCircuitProperty), but
  the chain-realizes-modular-exponentiation theorem is NOT proved here (the verified mod-exp
  semantics lives in `Shor_correct_verified_no_modmult_axioms` via `controlled_powers`, a
  DIFFERENT BaseUCom-level term — no bridge to these Gate chains yet).  So both chains are
  SCAFFOLDED (count-only), and the `2·bits` exponent-register multiplicity is structural.

  EXACT counts derived by induction (math — the 2048 circuit is never built), no `sorry`/`axiom`.
-/
import FormalRV.Arithmetic.ModMult

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- COUNTING-MODEL chain of `m` OUT-OF-PLACE `const_gate` multipliers (step `k` multiplies by
    `a^(2^k)`).  ⚠ Not a valid modular-exponentiation circuit (out-of-place = no feedback) and
    NOT the verified Shor oracle term — kept only for its per-step Toffoli structure.  For the
    verified-oracle chain use `shorModExpVerified`. -/
def shorModExpChain (m bits N a : Nat) : Gate :=
  match m with
  | 0 => Gate.I
  | k + 1 => seq (shorModExpChain k bits N a) (modmult_const_gate bits N (a ^ 2 ^ k))

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

/-- COUNTING-MODEL mod-exp skeleton: `2·bits` out-of-place multipliers.  ⚠ Not a valid
    mod-exp (no feedback) and not the verified oracle — see header; use `shorModExpVerified`. -/
def shorModExp (bits N a : Nat) : Gate := shorModExpChain (2 * bits) bits N a

/-- **EXACT** T-count of the out-of-place counting-model chain `shorModExp`: `112·bits³`
    (= `16·bits³` Toffoli).  Exact count of THIS concrete term; the term is a counting model,
    NOT the verified Shor circuit (header). -/
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

/-! ## The mod-exp on the ACTUAL VERIFIED ORACLE term (in-place MCP multiplier).

    `shorModExp` above chains the out-of-place `const_gate`.  The verified Shor algorithm
    instead uses the in-place `modmult_MCP_gate` (forward + uncompute = 2 const_gates).
    This chain counts EXACTLY that verified building block, so the arithmetic Toffoli total
    is on the term the verified Shor theorem actually uses.  (Each oracle has identical count
    `112·bits²` regardless of the specific valid constant `a^(2^k)`, so we may chain a fixed
    `(a,ainv)`; the count is the same as the constant-varying real circuit.) -/
def shorModExpMCPChain (m bits N a ainv : Nat) : Gate :=
  match m with
  | 0 => Gate.I
  | k + 1 => seq (shorModExpMCPChain k bits N a ainv) (modmult_MCP_gate bits N a ainv)

theorem tcount_shorModExpMCPChain (m bits N a ainv : Nat)
    (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) :
    tcount (shorModExpMCPChain m bits N a ainv) = m * (112 * bits ^ 2) := by
  induction m with
  | zero => simp [shorModExpMCPChain, tcount]
  | succ k ih =>
      simp only [shorModExpMCPChain, tcount]
      rw [ih, tcount_sqir_modmult_MCP_gate_shor bits N a ainv hcop hcopinv hpos hlt hodd h1]
      ring

/-- Mod-exp-shaped chain of `2·bits` VERIFIED in-place MCP oracles — the honest arithmetic
    figure (each step is the term the verified Shor theorem uses).  ⚠ Count-only/SCAFFOLDED:
    no proof yet that the chain computes `a^x mod N` (header); `2·bits` is structural. -/
def shorModExpVerified (bits N a ainv : Nat) : Gate := shorModExpMCPChain (2 * bits) bits N a ainv

/-- **EXACT** T-count of the verified-oracle chain `shorModExpVerified`: `224·bits³`
    (= `32·bits³` Toffoli; twice `shorModExp`, the in-place forward+uncompute factor).  This
    is the count on the verified-oracle building block — count-only (mod-exp semantics not
    proved for the chain; see header). -/
theorem tcount_shorModExpVerified (bits N a ainv : Nat)
    (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) :
    tcount (shorModExpVerified bits N a ainv) = 224 * bits ^ 3 := by
  unfold shorModExpVerified
  rw [tcount_shorModExpMCPChain (2 * bits) bits N a ainv hcop hcopinv hpos hlt hodd h1]; ring

-- Smoke: actual circuit traversal at (N=15, a=7, ainv=13) matches the formula 224·2³=1792.
example : tcount (shorModExpVerified 2 15 7 13) = 224 * 2 ^ 3 :=
  tcount_shorModExpVerified 2 15 7 13 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
#eval tcount (shorModExpVerified 2 15 7 13)   -- 1792  (actual MCP-chain traversal)

end FormalRV.BQAlgo
