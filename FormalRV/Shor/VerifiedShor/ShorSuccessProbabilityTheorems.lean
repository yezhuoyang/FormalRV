import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.ModularMultiplicationGates

namespace VerifiedShor
namespace ModMul
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)




/-- **Ancilla width** for the verified modular multiplier at width
`bits` (currently `3*bits + 11` per the SQIR-faithful layout). -/
def ancillaWidth (bits : Nat) : Nat := sqir_modmult_rev_anc bits

/-- **Total dimension** of the verified modular multiplier:
`bits + ancillaWidth bits`. -/
def totalDim (bits : Nat) : Nat := modmult_total_dim bits

/-- **Verified modular multiplication gate** in the `encodeDataZeroAnc`
/ `MultiplyCircuitProperty` layout.  Three-stage composition:
data-register adapter → in-place modular multiplier → adapter. -/
def gateMCP (bits N a ainv : Nat) : Gate :=
  modmult_MCP_gate bits N a ainv

/-- **Apply correctness in the encoded layout.**  Maps
`encodeDataZeroAnc bits anc x` to
`encodeDataZeroAnc bits anc ((a*x) % N)`. -/
theorem gateMCP_apply_encode
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (gateMCP bits N a ainv)
        (encodeDataZeroAnc bits (ancillaWidth bits) x)
      = encodeDataZeroAnc bits (ancillaWidth bits) ((a * x) % N) :=
  modmult_MCP_gate_apply_encode bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv

/-- **Gate is well-typed at `totalDim bits`.** -/
theorem gateMCP_wellTyped
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    Gate.WellTyped (totalDim bits) (gateMCP bits N a ainv) :=
  modmult_MCP_gate_wellTyped bits N a ainv hbits hN_pos hN hN2

/-- **Main bridge theorem**: the verified gate, compiled to a `BaseUCom`,
satisfies SQIR's `MultiplyCircuitProperty` — the spec consumed by
`ModMulImpl` and downstream Shor correctness. -/
theorem satisfiesMultiplyCircuitProperty
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    MultiplyCircuitProperty a N bits (ancillaWidth bits)
      (Gate.toUCom (totalDim bits) (gateMCP bits N a ainv)) :=
  modmult_MCP_gate_satisfies_MultiplyCircuitProperty
    bits N a ainv hbits hN_pos hN hN2 h_ainv_le h_inv

/-- **Per-QPE-iteration modular multiplication family**:
`circuitFamily a ainv N bits i` is the compiled `BaseUCom` for
multiplication by `a^(2^i) mod N` at the verified bit width. -/
noncomputable def circuitFamily (a ainv N bits : Nat) :
    Nat → BaseUCom (bits + ancillaWidth bits) :=
  f_modmult_circuit_verified_bits a ainv N bits

/-- **Verified `ModMulImpl` instance** for the family — the precise
SQIR interface that `Shor_correct_var` (and `VerifiedShor.correct*`)
consume. -/
theorem circuitFamily_modMulImpl
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_ge_2 : 2 ≤ N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (h_inv : a * ainv % N = 1) :
    ModMulImpl a N bits (ancillaWidth bits)
      (circuitFamily a ainv N bits) :=
  f_modmult_circuit_verified_bits_MMI a ainv N bits hbits hN_ge_2 hN hN2 h_inv

/-- **Per-iterate `MultiplyCircuitProperty`**: iterate `i` of the
family is a verified `a^(2^i) mod N` multiplier.  Follows from
`circuitFamily_modMulImpl`. -/
theorem circuitFamily_perIterate
    (a ainv N bits i : Nat) (hbits : 1 ≤ bits) (hN_ge_2 : 2 ≤ N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_inv : a * ainv % N = 1) :
    MultiplyCircuitProperty (a^(2^i)) N bits (ancillaWidth bits)
      (circuitFamily a ainv N bits i) :=
  circuitFamily_modMulImpl a ainv N bits hbits hN_ge_2 hN hN2 h_inv i

/-- **Every iterate is well-typed** at the family's total dimension. -/
theorem circuitFamily_wellTyped
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    ∀ i, uc_well_typed (circuitFamily a ainv N bits i) :=
  f_modmult_circuit_verified_bits_uc_well_typed a ainv N bits hbits hN_pos hN hN2

end ModMul
end VerifiedShor
