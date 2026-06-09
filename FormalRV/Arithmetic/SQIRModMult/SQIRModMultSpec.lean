/-
  FormalRV.Arithmetic.SQIRModMult.SQIRModMultSpec
  ───────────────────────────────────────────────
  The CLASSICAL specification of the modular multiplier's action — the
  shift-and-accumulate loop, as a pure `Nat` recursion. These are the reference
  values the gate-level correctness proofs decode to. No proofs.
-/
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultDef

namespace FormalRV.BQAlgo

/-- Accumulator after the first `k` multiplier bits, starting from 0. -/
def sqir_modmult_acc_spec (N a m : Nat) : Nat → Nat
  | 0     => 0
  | k + 1 =>
    if m.testBit k then (sqir_modmult_acc_spec N a m k + (a * 2 ^ k) % N) % N
    else sqir_modmult_acc_spec N a m k

/-- Like `sqir_modmult_acc_spec` but starting from `acc` (for the uncompute step). -/
def sqir_modmult_acc_spec_from (N a m acc : Nat) : Nat → Nat
  | 0     => acc
  | k + 1 =>
    if m.testBit k then (sqir_modmult_acc_spec_from N a m acc k + (a * 2 ^ k) % N) % N
    else sqir_modmult_acc_spec_from N a m acc k

end FormalRV.BQAlgo
