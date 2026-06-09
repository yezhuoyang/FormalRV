/-
  FormalRV.Arithmetic.ModularAdder.Gidney.Correctness
  ───────────────────────────────────────────────────
  THE semantic-correctness theorems for the Gidney-based modular adder
  `(x + c) mod N`. Surfaced here as thin wrappers; the heavy proofs live in the
  supporting files (`ForwardFaithfulness.lean`, `ControlledPipeline.lean`,
  `PowerOfTwoCase.lean`).

  Headlines:
    • `modAddConst_correct`           — the uncontrolled `(x + c) mod N` gate is
      WellTyped, decodes the target register to `(x+c) mod N`, and restores the
      read / carry registers and the comparison flag.
    • `controlledModAddConst_correct` — the controlled version writes
      `(x+c) mod N` to the target iff the control bit is set (else leaves `x`),
      with all workspace restored.

  Where to look next:
    • Definition              : `Gidney/Def.lean`
    • Resource (qubit budget) : `Gidney/Resource.lean`
-/
import FormalRV.Arithmetic.ModularAdder.Gidney.ForwardFaithfulness
import FormalRV.Arithmetic.ModularAdder.Gidney.ControlledPipeline

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- **Gidney modular adder — correctness (THE headline).** For `1 ≤ bits`,
`0 < N ≤ 2^bits`, `x < N`, and `0 < c < N`, the gate `modAddConstGate bits N c`
applied to the clean input `adder_input_F (bits+1) 0 x` (data `x` in the target
register, read register 0, carries 0, flag 0):
  1. is `WellTyped` on `adder_n_qubits (bits+1) + 1` qubits;
  2. decodes the target register to `(x + c) mod N`;
  3. restores the read register to 0;
  4. restores the carry register to 0;
  5. restores the comparison flag to 0. -/
theorem modAddConst_correct
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hx : x < N) (hc_pos : 0 < c) (hc : c < N) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + 1) (modAddConstGate bits N c)
    ∧ gidney_target_val bits
        (Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x))
      = (x + c) % N
    ∧ (∀ i, i < bits + 1 →
        Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x)
          (read_idx i) = false)
    ∧ (∀ i, i < bits + 1 →
        Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x)
          (carry_idx i) = false)
    ∧ Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x)
        (adder_n_qubits (bits + 1)) = false :=
  modAddConstGate_clean bits N c x hbits hN_pos hN hx hc_pos hc

/-- **Gidney controlled modular adder — correctness.** For any `controlBit` and
out-of-band `controlIdx < flagIdx`, `controlledModAddConstGate bits N c controlIdx flagIdx`
writes `(x+c) mod N` to the target register iff the control bit is set (otherwise
leaves `x`), with all workspace (read / carry / flag, control bit) restored. -/
theorem controlledModAddConst_correct
    (bits N c x : Nat) (controlBit : Bool) (controlIdx flagIdx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx)
      (update (adder_input_F (bits + 1) 0 x) controlIdx controlBit)
    = update (adder_input_F (bits + 1) 0 (if controlBit then (x + c) % N else x))
        controlIdx controlBit :=
  controlledModAddConstGate_correct bits N c x controlBit controlIdx flagIdx
    hbits hN_pos hN hx hc_pos hc hcontrolIdx hflagIdx

end FormalRV.BQAlgo
