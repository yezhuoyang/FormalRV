/-
  FormalRV.Arithmetic.Cuccaro.CuccaroAdderCorrectness
  ───────────────────────────────────────────────────
  THE semantic-correctness theorem for the Cuccaro n-bit adder.

  Imports the definition from `CuccaroAdderDef.lean`. The single theorem to
  audit is `cuccaro_adder_correct`. Its proof is delegated to the supporting
  lemmas in `CuccaroDecoded.lean` / `CuccaroFull.lean` / `CuccaroCorrectness.lean`.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroAdderDef
import FormalRV.Arithmetic.Cuccaro.CuccaroDecoded

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.Framework.Boolean

/-- **Cuccaro adder — semantic correctness (THE headline).**

Running `cuccaro_n_bit_adder_full bits q_start` on the standard input
encoding `cuccaro_input_F q_start false a b` (carry-in 0, target register
= b, read register = a, with `a, b < 2^bits`) leaves the **target register
decoding to `(a + b) mod 2^bits`**.

The companion facts — read register restored to `a`, carry-in restored to
0, and WellTyped on the `2*bits + 1` qubit budget — are bundled in
`cuccaro_adder_correct_full` below. -/
theorem cuccaro_adder_correct (bits q_start a b : Nat)
    (ha : a < 2 ^ bits) (hb : b < 2 ^ bits) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
          (cuccaro_input_F q_start false a b))
      = (a + b) % 2 ^ bits :=
  cuccaro_n_bit_adder_full_target_decode bits q_start a b ha hb

/-- **Cuccaro adder — full correctness bundle.** The adder is WellTyped on
the `2*bits + 1` qubit budget, writes `(a+b) % 2^bits` to the target
register, preserves the read register `a`, and restores the carry-in to 0. -/
theorem cuccaro_adder_correct_full (bits q_start a b : Nat)
    (ha : a < 2 ^ bits) (hb : b < 2 ^ bits) :
    Gate.WellTyped (q_start + (2 * bits + 1)) (cuccaro_n_bit_adder_full bits q_start)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (cuccaro_input_F q_start false a b)) = (a + b) % 2 ^ bits
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (cuccaro_input_F q_start false a b)) = a
    ∧ Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
          (cuccaro_input_F q_start false a b) q_start = false :=
  cuccaro_n_bit_adder_full_primitive bits q_start a b ha hb

end FormalRV.BQAlgo
