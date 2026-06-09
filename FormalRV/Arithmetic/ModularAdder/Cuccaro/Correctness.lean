/-
  FormalRV.Arithmetic.ModularAdder.Cuccaro.Correctness
  ────────────────────────────────────────────────────
  THE semantic-correctness theorems for the Cuccaro/SQIR-style modular adder
  `(x + c) mod N` (the LIVE one). Surfaced here as thin wrappers; the heavy
  proofs live in `Cuccaro/CuccaroSQIRDirtyFlag/` (kept there — consumed by
  `ModMult/`).

  Headlines (at the SQIR layout `q_start = 2`, `flagPos = 1`):
    • `cuccaroModAddConst_correct`           — uncontrolled `(x + c) mod N`.
    • `cuccaroControlledModAddConst_correct`  — controlled version (THE gate the
      verified modular multiplier uses).

  Both decode the target register to `(x+c) mod N` and certify that the read
  register, top carry, and flag are restored (the controlled one additionally
  preserves the control bit and gates on it).
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroCleanModularAddCorrectness
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroControlledModularAddCorrectness

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- **Cuccaro modular adder — correctness (uncontrolled).** For `1 ≤ bits`,
`0 < N`, `N ≤ 2^bits`, `2N ≤ 2^bits`, `c < N`, `x < N`, the gate
`sqir_style_modAddConst_clean_gate bits N c` on the clean SQIR-layout input is
WellTyped on `sqir_modmult_rev_anc bits` qubits, decodes the target register to
`(x+c) mod N`, and restores the read register, the top carry, and the flag. -/
theorem cuccaroModAddConst_correct
    (bits N c x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (hc : c < N) (hx : x < N) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_modAddConst_clean_gate bits N c)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat (sqir_style_modAddConst_clean_gate bits N c)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = (x + c) % N
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_modAddConst_clean_gate bits N c)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = 0
    ∧ Gate.applyNat (sqir_style_modAddConst_clean_gate bits N c)
          (update (cuccaro_input_F 2 false 0 x) 1 false) (2 + 2 * bits) = false
    ∧ Gate.applyNat (sqir_style_modAddConst_clean_gate bits N c)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 1 = false :=
  sqir_style_modAddConst_clean_gate_clean bits N c x hbits hN_pos hN hN2 hc hx

/-- **Cuccaro controlled modular adder — correctness (THE live headline).** For
any `control` and out-of-band `controlIdx ≠ 1` with
`controlIdx < sqir_modmult_rev_anc bits`,
`sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1` decodes the
target to `(x+c) mod N` iff `control` is set (else leaves `x`), restoring the
read register / top carry / flag and preserving the control bit. -/
theorem cuccaroControlledModAddConst_correct
    (bits N c x controlIdx : Nat) (control : Bool) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1)
    (h_control_workspace_lt : controlIdx < sqir_modmult_rev_anc bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = (if control then (x + c) % N else x)
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control)) = 0
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) (2 + 2 * bits) = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) 1 = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx = control :=
  sqir_style_controlledModAddConst_gate_clean bits N c x controlIdx control hbits
    hN_pos hN hN2 hc hx hcontrol_out hcontrol_ne_flag h_control_workspace_lt

end FormalRV.BQAlgo
