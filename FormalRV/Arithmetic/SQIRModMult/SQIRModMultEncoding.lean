/-
  FormalRV.Arithmetic.SQIRModMult.SQIRModMultEncoding
  ───────────────────────────────────────────────────
  The basis-state INPUT ENCODING for the SQIR modular multiplier: the boolean
  state functions that place the accumulator and multiplier registers, and its
  shifted (external-data-register) variant. Used to STATE the correctness
  theorems. No proofs.
-/
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultDef

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- Input state for the modular multiplier: Cuccaro accumulator state at
`q_start = 2` plus the multiplier bits `m.testBit j` in the control register. -/
def sqir_mult_input_F (bits m acc : Nat) : Nat → Bool := fun q =>
  if q < 2 + 2 * bits + 1 then
    cuccaro_input_F 2 false 0 acc q
  else if q < 2 + 2 * bits + 1 + bits then
    m.testBit (q - (2 + 2 * bits + 1))
  else false

/-- The input encoding shifted up by `bits` (positions `[0,bits)` reserved for
the external data register). -/
def sqir_mult_input_F_shifted (bits x acc : Nat) : Nat → Bool :=
  fun q => if q < bits then false else sqir_mult_input_F bits x acc (q - bits)

end FormalRV.BQAlgo
