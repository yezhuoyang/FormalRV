/-
  FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderCorrectness
  ────────────────────────────────────────────────────────────────
  THE semantic-correctness theorems for the Gidney ripple-carry adder.

  Imports the definition from `RippleCarryAdderDef.lean`. The theorems to
  audit are surfaced here as thin wrappers; their (heavy) proofs live in the
  supporting files and are delegated to in one line each.

  Two circuits, two headlines:
    • `gidney_adder_correct` — the base adder `gidney_adder` writes the sum
      bits to the target register (read register preserved; **carries are
      left dirty** — see `RippleCarryAdderPropagationReverse`).
    • `gidney_adder_correct_full` — the carry-clearing **patched** adder is
      simultaneously WellTyped, decodes the target to `(a+b) mod 2^bits`,
      preserves the read register, AND clears the carry register. This is the
      bundle the modular-adder layer builds on (`gidney_adder_patched_primitive`).

  Where to look next:
    • Resources (T-count / qubits / RSA-2048) : `RippleCarryAdderResource.lean`
    • Worked example + OpenQASM                : `RippleCarryAdderExample.lean`
    • Supporting proofs : `RippleCarryAdderPropagationReverse.lean`
      (assembled target/read correctness, applyNat bridge, patched carry-clearing),
      `RippleCarryAdderUncomputeCascade.lean` (packaged primitive + WellTyped),
      `RippleCarryAdderDecideWitnesses.lean`, `RippleCarryAdderClassicalBridge.lean`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderPropagationReverse
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderUncomputeCascade

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## The base adder `gidney_adder` -/

/-- **Gidney adder — semantic correctness (THE headline).**

Running `gidney_adder n` (the canonical no-measurement faithful adder) on the
standard input encoding `adder_input_F n a b` (read register = `a`, target
register = `b`, carries 0, with `a, b < 2^n` and `1 < n`) leaves the **target
register holding the sum bits** `(a + b).testBit i` for every `i < n`.

The read register is restored to `a` (`gidney_adder_read_preserved`). The carry
register is **left dirty** in this base adder — use the patched adder
(`gidney_adder_correct_full`) when clean carries are required. -/
theorem gidney_adder_correct (n a b : Nat)
    (hn : 1 < n) (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    ∀ i, i < n →
      Gate.applyNat (gidney_adder n) (adder_input_F n a b) (target_idx i)
        = adder_sum_bit_classical a b i := by
  unfold gidney_adder
  exact gidney_adder_full_faithful_no_measurement_target_correct n a b hn ha hb

/-- **Gidney adder — read register preserved.** `gidney_adder n` leaves the
read register holding `a` (bit `i` = `a.testBit i`) for every `i < n`. -/
theorem gidney_adder_read_preserved (n a b : Nat)
    (hn : 1 < n) (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    ∀ i, i < n →
      Gate.applyNat (gidney_adder n) (adder_input_F n a b) (read_idx i)
        = a.testBit i := by
  unfold gidney_adder
  exact gidney_adder_full_faithful_no_measurement_read_correct n a b hn ha hb

/-! ## The carry-clearing patched adder (the reusable primitive) -/

/-- **Gidney adder — full correctness bundle (carry-clean).**

The patched adder `gidney_adder_full_faithful_no_measurement_patched bits` is,
for `bits ≥ 2` and `a, b < 2^bits`, simultaneously:
  1. **WellTyped** on the `adder_n_qubits bits = 3·bits + 2` qubit budget;
  2. decodes the target register to `(a + b) mod 2^bits`;
  3. preserves the read register (`= a`);
  4. **clears the carry register** (every carry qubit back to `0`).

This is the bundled primitive the modular-adder layer calls; it is exactly
`gidney_adder_patched_primitive`. -/
theorem gidney_adder_correct_full (bits a b : Nat)
    (hbits : 2 ≤ bits) (ha : a < 2 ^ bits) (hb : b < 2 ^ bits) :
    Gate.WellTyped (adder_n_qubits bits)
        (gidney_adder_full_faithful_no_measurement_patched bits)
    ∧ gidney_target_val bits
          (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
            (adder_input_F bits a b))
        = (a + b) % 2 ^ bits
    ∧ (∀ i, i < bits →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits a b) (read_idx i) = a.testBit i)
    ∧ (∀ i, i < bits →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits a b) (carry_idx i) = false) :=
  gidney_adder_patched_primitive bits a b hbits ha hb

end FormalRV.BQAlgo
