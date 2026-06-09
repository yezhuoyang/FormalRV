/-
  FormalRV.Arithmetic.ModularAdder.Cuccaro.Resource
  ─────────────────────────────────────────────────
  THE resource theorem for the Cuccaro/SQIR-style modular adder. As with the
  Gidney spine the natural resource is the **qubit budget**: the modular adder is
  `WellTyped` on `sqir_modmult_rev_anc bits` qubits (the SQIR `ModMult.v` reverse
  workspace — the `2·bits`-wide Cuccaro block at `q_start = 2`, the flag at
  position 1, plus the reverse ancillas). Surfaced as thin wrappers extracting
  the WellTyped conjunct of the clean correctness bundles.

  T-count note: each modular-add block is a constant number of Cuccaro adders
  (add `c`, compare `N`, conditional subtract `N`, cleanup); the verified
  multiplier applies one controlled block per multiplier bit, giving the
  `modmult_tcount = 112·bits²` figure proved in `ModMult/`. No separate
  closed-form T-count is restated here.

  Where to look next:
    • Definition  : `Cuccaro/Def.lean`
    • Correctness : `Cuccaro/Correctness.lean`
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroCleanModularAddCorrectness
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroControlledModularAddCorrectness

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- **Cuccaro modular adder — qubit budget (uncontrolled).** `WellTyped` on
`sqir_modmult_rev_anc bits` qubits. -/
theorem cuccaroModAddConst_wellTyped
    (bits N c x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (hc : c < N) (hx : x < N) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
      (sqir_style_modAddConst_clean_gate bits N c) :=
  (sqir_style_modAddConst_clean_gate_clean bits N c x hbits hN_pos hN hN2 hc hx).1

/-- **Cuccaro controlled modular adder — qubit budget (THE resource headline).**
`WellTyped` on `sqir_modmult_rev_anc bits` qubits, for out-of-band
`controlIdx ≠ 1` with `controlIdx < sqir_modmult_rev_anc bits`. -/
theorem cuccaroControlledModAddConst_wellTyped
    (bits N c x controlIdx : Nat) (control : Bool) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1)
    (h_control_workspace_lt : controlIdx < sqir_modmult_rev_anc bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
      (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1) :=
  (sqir_style_controlledModAddConst_gate_clean bits N c x controlIdx control hbits
    hN_pos hN hN2 hc hx hcontrol_out hcontrol_ne_flag h_control_workspace_lt).1

end FormalRV.BQAlgo
