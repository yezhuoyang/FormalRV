/-
  FormalRV.PPM.Gadgets.ModularAdder.GidneyModAddPPM — compiled-PPM semantic
  correctness for the GIDNEY modular adders, plain and controlled, against
  ANY `PPMCompilerSpec`.

  Arithmetic content: `modAddConst_correct` / `controlledModAddConst_correct`
  (Arithmetic/ModularAdder/Gidney).  The controlled form's correctness is a
  FULL-STATE equation, so its PPM statement is an exact observed-state
  round-trip (the strongest shape in this folder).

  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.Gadgets.CompilerContract
import FormalRV.Arithmetic.ModularAdder.Gidney.Correctness

namespace FormalRV.PPM.Gadgets.ModularAdderPPM

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.Framework.Gate

/-- **The Gidney modular adder, compiled by any contract compiler, observes
    `x ↦ (x + c) mod N`** with read and carry registers returned clean. -/
theorem gidneyModAdd_compiles_to_PPM (S : PPMCompilerSpec)
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hx : x < N) (hc_pos : 0 < c) (hc : c < N) :
    ∃ out, S.Observes (S.compile (modAddConstGate bits N c))
        (adder_input_F (bits + 1) 0 x) out
      ∧ gidney_target_val bits out = (x + c) % N
      ∧ (∀ i, i < bits + 1 → out (read_idx i) = false)
      ∧ (∀ i, i < bits + 1 → out (carry_idx i) = false) := by
  obtain ⟨-, htarget, hread, hcarry, -⟩ :=
    modAddConst_correct bits N c x hbits hN_pos hN hx hc_pos hc
  exact ⟨_, S.compile_observes _ _, htarget, hread, hcarry⟩

/-- **The CONTROLLED Gidney modular adder, compiled by any contract
    compiler, observes the EXACT output state**: the clean input layout with
    the target holding `(x + c) mod N` iff the control is set. -/
theorem gidneyControlledModAdd_compiles_to_PPM (S : PPMCompilerSpec)
    (bits N c x : Nat) (controlBit : Bool) (controlIdx flagIdx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    S.Observes (S.compile (controlledModAddConstGate bits N c controlIdx flagIdx))
      (update (adder_input_F (bits + 1) 0 x) controlIdx controlBit)
      (update (adder_input_F (bits + 1) 0 (if controlBit then (x + c) % N else x))
        controlIdx controlBit) := by
  have h := S.compile_observes (controlledModAddConstGate bits N c controlIdx flagIdx)
      (update (adder_input_F (bits + 1) 0 x) controlIdx controlBit)
  rwa [controlledModAddConst_correct bits N c x controlBit controlIdx flagIdx
        hbits hN_pos hN hx hc_pos hc hcontrolIdx hflagIdx] at h

end FormalRV.PPM.Gadgets.ModularAdderPPM
