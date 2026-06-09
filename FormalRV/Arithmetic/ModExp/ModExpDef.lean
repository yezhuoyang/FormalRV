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


/-! ## Generic modexp oracle — parametric over ANY verified modmult.

    The point of the modularized design: ModExp does not care which modmult
    implementation (or how many ancilla qubits it uses). Given any per-constant
    modmult gate builder at some dimension `dim`, the squared-power family is the
    modexp oracle. `our_modmult_family` above is the `modMultInPlaceShor` instance
    (ancilla `adder_n_qubits (bits+1) + 1`); `modexpFamilyMCP` below is the
    `modmult_MCP_gate` instance (ancilla `sqir_modmult_rev_anc bits`) — same
    construction, different ancilla count. -/

/-- Generic squared-power modexp oracle family: iterate `i` is `gate` applied to
the reduced constant `a^(2^i) mod N` (with its inverse), at dimension `dim`. -/
noncomputable def modexpOracleFamily (dim N a ainv : Nat) (gate : Nat → Nat → Gate) :
    Nat → FormalRV.SQIRPort.BaseUCom dim :=
  fun i => Gate.toUCom dim (gate (a ^ (2 ^ i) % N) (ainv ^ (2 ^ i) % N))

/-- ModExp instantiated on the SQIR-layout ModMult gadget `modmult_MCP_gate`
(dim `bits + sqir_modmult_rev_anc bits`). -/
noncomputable def modexpFamilyMCP (bits N a ainv : Nat) :
    Nat → FormalRV.SQIRPort.BaseUCom (bits + sqir_modmult_rev_anc bits) :=
  modexpOracleFamily (bits + sqir_modmult_rev_anc bits) N a ainv
    (fun c cinv => modmult_MCP_gate bits N c cinv)

end FormalRV.BQAlgo
