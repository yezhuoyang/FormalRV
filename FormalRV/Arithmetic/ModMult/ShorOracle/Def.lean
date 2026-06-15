/-
  FormalRV.Arithmetic.ModMult.ShorOracle.Def
  The Shor-layout in-place modular multiplier `modMultInPlaceShor` — a SECOND
  modmult variant (distinct from modmult_MCP_gate): it wraps the faithfully-verified
  Gidney ripple-carry in-place multiplier (ModularAdder/Gidney) with register-swap
  adapters, living at the Shor order-finding dimension multBits + adder_n_qubits(bits+1)+1
  = 4*bits+6. This is the modmult that Shor's order-finding oracle consumes.
-/
import FormalRV.Arithmetic.ModularAdder

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.SQIRPort

/-- **Shor-shaped in-place modular multiplier gate.**  Three-stage
composition: SWAP → in-place multiplier → SWAP.  Takes
`encodeDataZeroAnc` input and produces `encodeDataZeroAnc` output with
the data register replaced by `(a*x) mod N`. -/
def modMultInPlaceShor (bits N a ainv multBits : Nat) : Gate :=
  Gate.seq (reverse_register_swap multBits 0 (adder_n_qubits (bits + 1)))
           (Gate.seq (modMultInPlace bits N a ainv multBits)
                     (reverse_register_swap multBits 0 (adder_n_qubits (bits + 1))))


end FormalRV.BQAlgo
