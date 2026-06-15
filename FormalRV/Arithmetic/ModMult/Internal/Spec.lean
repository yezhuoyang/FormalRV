/-
  FormalRV.Arithmetic.ModMult.Internal.Spec
  ───────────────────────────────────────────────
  The CLASSICAL specification of the modular multiplier's action — the
  shift-and-accumulate loop, as a pure `Nat` recursion. These are the reference
  values the gate-level correctness proofs decode to. No proofs.
-/
import FormalRV.Arithmetic.ModMult.ModMultDef

namespace FormalRV.BQAlgo

/-- Accumulator after the first `k` multiplier bits, starting from 0. -/
def modmult_acc_spec (N a m : Nat) : Nat → Nat
  | 0     => 0
  | k + 1 =>
    if m.testBit k then (modmult_acc_spec N a m k + (a * 2 ^ k) % N) % N
    else modmult_acc_spec N a m k

/-- Like `modmult_acc_spec` but starting from `acc` (for the uncompute step). -/
def modmult_acc_spec_from (N a m acc : Nat) : Nat → Nat
  | 0     => acc
  | k + 1 =>
    if m.testBit k then (modmult_acc_spec_from N a m acc k + (a * 2 ^ k) % N) % N
    else modmult_acc_spec_from N a m acc k

end FormalRV.BQAlgo
