/-
  FormalRV.Arithmetic.ModMult.ModMultResource
  ───────────────────────────────────────────────────
  THE resource theorem for the SQIR-faithful in-place modular multiplier, and
  the theorem tying the resource to the SAME gate the correctness theorem
  verifies.

  Headlines:
    • `modmult_tcount`   — EXACT T-count = 112·bits²  (an equality, not a bound).
    • `modmult_verified` — resource AFTER correctness: the one gate is both
      MultiplyCircuitProperty-correct AND has T-count 112·bits².
-/
import FormalRV.Arithmetic.ModMult.ModMultDef
import FormalRV.Arithmetic.ModMult.Internal.ToffoliCount
import FormalRV.Arithmetic.ModMult.ModMultCorrectness

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- **SQIR modular multiplier — resource (THE headline, EXACT).**
T-count `= 112 · bits²` for the verified MCP oracle, for any valid Shor base
`a` and inverse `ainv` (coprime to an odd modulus `N > 1`). This is an exact
equality, computed structurally from the construction. -/
theorem modmult_tcount (bits N a ainv : Nat)
    (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) :
    tcount (modmult_MCP_gate bits N a ainv) = 112 * bits ^ 2 :=
  tcount_sqir_modmult_MCP_gate_shor bits N a ainv hcop hcopinv hpos hlt hodd h1

/-- **SQIR modular multiplier — verified-with-resource (resource AFTER
correctness).** The single gate `modmult_MCP_gate bits N a ainv` is
simultaneously (i) `MultiplyCircuitProperty a N`-correct and (ii) exactly
`112 · bits²` T-gates. The resource is stated about exactly the verified gate. -/
theorem modmult_verified (bits N a ainv : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1)
    (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) :
    FormalRV.SQIRPort.MultiplyCircuitProperty a N bits (sqir_modmult_rev_anc bits)
        (Gate.toUCom (modmult_total_dim bits) (modmult_MCP_gate bits N a ainv))
    ∧ tcount (modmult_MCP_gate bits N a ainv) = 112 * bits ^ 2 :=
  ⟨modmult_correct bits N a ainv hbits hN_pos hN hN2 h_ainv_le h_inv,
   modmult_tcount bits N a ainv hcop hcopinv hpos hlt hodd h1⟩

end FormalRV.BQAlgo
