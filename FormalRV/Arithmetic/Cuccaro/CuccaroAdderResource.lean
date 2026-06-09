/-
  FormalRV.Arithmetic.Cuccaro.CuccaroAdderResource
  ────────────────────────────────────────────────
  THE resource theorem for the Cuccaro n-bit adder, and the theorem that
  ties the resource to the SAME circuit the correctness theorem verifies.

  Imports the definition from `CuccaroAdderDef.lean` and the correctness
  bundle from `CuccaroAdderCorrectness.lean`.

  Headlines:
    • `cuccaro_adder_tcount`   — T-count = 14·n.
    • `cuccaro_adder_verified` — resource-after-correctness: the one circuit
      is simultaneously correct, WellTyped on 2n+1 qubits, and 14n T-gates.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroAdderDef
import FormalRV.Arithmetic.Cuccaro.CuccaroFull
import FormalRV.Arithmetic.Cuccaro.CuccaroAdderCorrectness

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- **Cuccaro adder — resource (THE headline).**  The full n-bit adder uses
exactly `14 * n` T-gates (n MAJ + n UMA gadgets, 7 T each; CX/CCX-internal
CXs are T-free). -/
theorem cuccaro_adder_tcount (bits q_start : Nat) :
    tcount (cuccaro_n_bit_adder_full bits q_start) = 14 * bits :=
  tcount_cuccaro_n_bit_adder_full bits q_start

/-- **Cuccaro adder — verified-with-resource (resource AFTER correctness).**

The single object `cuccaro_n_bit_adder_full bits q_start` is simultaneously:
  1. semantically correct — writes `(a+b) % 2^bits`, preserves `a`, restores
     the carry-in (the `cuccaro_adder_correct_full` bundle);
  2. **WellTyped on the `2*bits + 1` qubit budget**;
  3. **`14 * bits` T-gates**.

The resource bounds are stated about *exactly* the circuit the correctness
theorem verifies, so "resource" is established only after "correctness". -/
theorem cuccaro_adder_verified (bits q_start a b : Nat)
    (ha : a < 2 ^ bits) (hb : b < 2 ^ bits) :
    (Gate.WellTyped (q_start + (2 * bits + 1)) (cuccaro_n_bit_adder_full bits q_start)
      ∧ cuccaro_target_val bits q_start
            (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
              (cuccaro_input_F q_start false a b)) = (a + b) % 2 ^ bits
      ∧ cuccaro_read_val bits q_start
            (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
              (cuccaro_input_F q_start false a b)) = a
      ∧ Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (cuccaro_input_F q_start false a b) q_start = false)
    ∧ tcount (cuccaro_n_bit_adder_full bits q_start) = 14 * bits :=
  ⟨cuccaro_adder_correct_full bits q_start a b ha hb,
   cuccaro_adder_tcount bits q_start⟩

end FormalRV.BQAlgo
