/-
  FormalRV.Arithmetic.ModExp.ModExpDef
  The verified modular-exponentiation ORACLE FAMILY: the squared-power chain of
  in-place modular multipliers (iterate i multiplies by a^(2^i) mod N). Relocated
  from MCPBridge so the modexp gadget lives in its own folder, built on ModMult.
-/
import FormalRV.Arithmetic.ModMult

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.SQIRPort

/-- The Shor-shaped modular multiplication family indexed by QPE
iterate.  At iterate `i`, the gate multiplies by `a^(2^i) mod N`
in-place.  Each per-iterate gate uses `(a^(2^i)) % N` as its base
multiplier (so the constant fits in `[0, N)`) and `(ainv^(2^i)) % N`
as its modular inverse (since `(a*ainv) ≡ 1 (mod N)` implies
`(a*ainv)^(2^i) ≡ 1 (mod N)`, hence `(a^(2^i)) * (ainv^(2^i)) ≡ 1
(mod N)`). -/
noncomputable def our_modmult_family (bits N a ainv multBits : Nat) :
    Nat → FormalRV.SQIRPort.BaseUCom
            (multBits + (adder_n_qubits (bits + 1) + 1)) :=
  fun i => Gate.toUCom (multBits + (adder_n_qubits (bits + 1) + 1))
            (modMultInPlaceShor bits N (a^(2^i) % N) (ainv^(2^i) % N) multBits)


/-- **WellTyped for the squared-power family.**  For every iterate
`i`, the compiled `BaseUCom` is well-typed at the Shor dimension. -/
theorem our_modmult_family_uc_well_typed
    (bits N a ainv multBits : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) (h_multBits_pos : 0 < multBits) :
    ∀ i, FormalRV.SQIRPort.uc_well_typed
            (our_modmult_family bits N a ainv multBits i) := by
  intro i
  unfold our_modmult_family
  exact uc_well_typed_toUCom_of_Gate_WellTyped _ _
    (modMultInPlaceShor_wellTyped bits N (a^(2^i) % N) (ainv^(2^i) % N)
      multBits hbits h_multBits_le h_multBits_pos)


end FormalRV.BQAlgo
