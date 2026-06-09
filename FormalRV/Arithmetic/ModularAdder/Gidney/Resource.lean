/-
  FormalRV.Arithmetic.ModularAdder.Gidney.Resource
  ────────────────────────────────────────────────
  THE resource theorem for the Gidney-based modular adder. The natural resource
  here is the **qubit budget**: the (controlled) modular adder is `WellTyped` on
  a fixed number of qubits (the widened `bits+1` adder block, plus the
  out-of-band control/flag qubits). Surfaced as a thin wrapper.

  T-count note: `modAddConstGate` is exactly **five** invocations of the patched
  Gidney adder — add `c`, subtract `N`, conditional add-back `N`, then subtract
  `c` and add `c` to uncompute the flag — wrapped by T-free X/CX prepare
  cascades. So its T-count is `5 ×` the base adder's; the controlled multiplier
  applies one such block per multiplier bit. No separate closed-form T-count is
  proven here (the base adder owns the T-count theorem).

  Where to look next:
    • Definition  : `Gidney/Def.lean`
    • Correctness : `Gidney/Correctness.lean`
-/
import FormalRV.Arithmetic.ModularAdder.Gidney.ForwardFaithfulness
import FormalRV.Arithmetic.ModularAdder.Gidney.ControlledPipeline

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- **Gidney controlled modular adder — qubit budget (THE resource headline).**
For `1 ≤ bits` and out-of-band `adder_n_qubits (bits+1) ≤ controlIdx < flagIdx`,
the controlled modular adder is `WellTyped` on `flagIdx + 1` qubits (the
`bits+1`-wide adder block `adder_n_qubits (bits+1) = 3·(bits+1) + 2`, the
comparison flag, and the external control). -/
theorem controlledModAddConst_wellTyped
    (bits N c controlIdx flagIdx : Nat) (hbits : 1 ≤ bits)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.WellTyped (flagIdx + 1) (controlledModAddConstGate bits N c controlIdx flagIdx) :=
  controlledModAddConstGate_wellTyped bits N c controlIdx flagIdx hbits hcontrolIdx hflagIdx

/-- **Gidney modular multiplier — qubit budget at the Shor dimension.** The
repeated-controlled-addition multiplier `modMultConstGate` is `WellTyped` on the
Shor register dimension. -/
theorem modMultConst_wellTyped_at_shor_dim
    (bits N a multBits : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
      (modMultConstGate bits N a multBits) :=
  modMultConstGate_wellTyped_at_shor_dim bits N a multBits hbits

end FormalRV.BQAlgo
