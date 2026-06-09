/-
  FormalRV.Arithmetic.SQIRModMult.SQIRModMultCorrectness
  ──────────────────────────────────────────────────────
  THE semantic-correctness theorem for the SQIR-faithful in-place modular
  multiplier.

  Definition (THE multiplier): `sqir_modmult_MCP_gate` in
  `SQIRModMultDefinitions.lean`. Correctness is stated through the shared
  `Gate.applyNat` semantic core (the proof routes via
  `sqir_modmult_MCP_gate_apply_encode`). The single theorem to audit is
  `sqir_modmult_correct`.
-/
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultDef
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultAccumulatorRange

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- **SQIR modular multiplier — semantic correctness (THE headline).**

For valid Shor parameters (`a·ainv ≡ 1 mod N`, `2N ≤ 2^bits`), the MCP-layout
gate `sqir_modmult_MCP_gate bits N a ainv` satisfies
`MultiplyCircuitProperty a N` — i.e. on the SQIR-faithful encoding it maps the
data register `x ↦ (a · x) mod N` in place. Proven through the `Gate.applyNat`
semantic core. -/
theorem sqir_modmult_correct (bits N a ainv : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    FormalRV.SQIRPort.MultiplyCircuitProperty a N bits (sqir_modmult_rev_anc bits)
      (Gate.toUCom (sqir_total_dim bits) (sqir_modmult_MCP_gate bits N a ainv)) :=
  sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty bits N a ainv
    hbits hN_pos hN hN2 h_ainv_le h_inv

end FormalRV.BQAlgo
