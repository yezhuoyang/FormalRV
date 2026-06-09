/-
  FormalRV.Arithmetic.SQIRModMult.SQIRModMultFamily
  ─────────────────────────────────────────────────
  The verified `BaseUCom` oracle FAMILIES built from `sqir_modmult_MCP_gate`,
  indexed for Shor's order-finding (`a^(2^i) mod N`). These are the bridge
  objects consumed by the Shor wiring. No proofs.
-/
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultDef

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- Verified modular-multiplier family at dimension `(n+1) + sqir_modmult_rev_anc (n+1)`. -/
noncomputable def f_modmult_circuit_verified (a ainv N n : Nat) :
    Nat → FormalRV.Framework.BaseUCom ((n + 1) + sqir_modmult_rev_anc (n + 1)) :=
  fun i =>
    Gate.toUCom ((n + 1) + sqir_modmult_rev_anc (n + 1))
      (sqir_modmult_MCP_gate (n + 1) N ((a ^ (2 ^ i)) % N) ((ainv ^ (2 ^ i)) % N))

/-- Bits-parameterized verified modular-multiplier family. -/
noncomputable def f_modmult_circuit_verified_bits (a ainv N bits : Nat) :
    Nat → FormalRV.Framework.BaseUCom (bits + sqir_modmult_rev_anc bits) :=
  fun i =>
    Gate.toUCom (bits + sqir_modmult_rev_anc bits)
      (sqir_modmult_MCP_gate bits N ((a ^ (2 ^ i)) % N) ((ainv ^ (2 ^ i)) % N))

end FormalRV.BQAlgo
