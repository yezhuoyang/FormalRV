/-
  FormalRV.PPM.Gadgets.ModularAdder.CuccaroModAddPPM — compiled-PPM semantic
  correctness for the CUCCARO (SQIR-style) modular adders, plain and
  controlled, against ANY `PPMCompilerSpec`.

  Arithmetic content: `cuccaroModAddConst_correct` /
  `cuccaroControlledModAddConst_correct` (Arithmetic/ModularAdder/Cuccaro).
  The controlled form is the workhorse inside `modmult_MCP_gate`.

  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.Gadgets.CompilerContract
import FormalRV.Arithmetic.ModularAdder.Cuccaro.Correctness

namespace FormalRV.PPM.Gadgets.ModularAdderPPM

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.Framework.Gate

/-- **The Cuccaro modular adder, compiled by any contract compiler, observes
    `x ↦ (x + c) mod N`** on the target register, with the read register
    returned clean. -/
theorem cuccaroModAdd_compiles_to_PPM (S : PPMCompilerSpec)
    (bits N c x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (hc : c < N) (hx : x < N) :
    ∃ out, S.Observes (S.compile (sqir_style_modAddConst_clean_gate bits N c))
        (update (cuccaro_input_F 2 false 0 x) 1 false) out
      ∧ cuccaro_target_val bits 2 out = (x + c) % N
      ∧ cuccaro_read_val bits 2 out = 0 := by
  obtain ⟨-, htarget, hread, -, -⟩ :=
    cuccaroModAddConst_correct bits N c x hbits hN_pos hN hN2 hc hx
  exact ⟨_, S.compile_observes _ _, htarget, hread⟩

/-- **The CONTROLLED Cuccaro modular adder, compiled by any contract
    compiler, observes `x ↦ (x + c) mod N` exactly when the control is
    set** (else leaves `x`), restoring the read register and preserving
    the control bit. -/
theorem cuccaroControlledModAdd_compiles_to_PPM (S : PPMCompilerSpec)
    (bits N c x controlIdx : Nat) (control : Bool) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1)
    (h_control_workspace_lt : controlIdx < sqir_modmult_rev_anc bits) :
    ∃ out, S.Observes
        (S.compile (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1))
        (update (cuccaro_input_F 2 false 0 x) controlIdx control) out
      ∧ cuccaro_target_val bits 2 out = (if control then (x + c) % N else x)
      ∧ cuccaro_read_val bits 2 out = 0
      ∧ out controlIdx = control := by
  obtain ⟨-, htarget, hread, -, -, hctrl⟩ :=
    cuccaroControlledModAddConst_correct bits N c x controlIdx control hbits
      hN_pos hN hN2 hc hx hcontrol_out hcontrol_ne_flag h_control_workspace_lt
  exact ⟨_, S.compile_observes _ _, htarget, hread, hctrl⟩

end FormalRV.PPM.Gadgets.ModularAdderPPM
