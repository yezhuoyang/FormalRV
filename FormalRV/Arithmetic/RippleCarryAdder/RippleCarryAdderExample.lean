/-
  FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderExample
  ────────────────────────────────────────────────────────────
  A worked example for the Gidney adder + its `Gadget` descriptor for the
  uniform QASM emitter.

  This file contains `#eval` demos, so it is kept OFF the default build path
  (not imported by the `Arithmetic` umbrella). Build / run on demand:
    lake build FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderExample
-/
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderResource
import FormalRV.Codegen.QASMEmit

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.Codegen (Gadget emitQASM)

/-! ## Worked example: the verified 2-bit adder (8 qubits = 3·2+2). -/

/-- The 2-bit Gidney adder. -/
def gidney_adder_2bit : Gate := gidney_adder 2

/-- Its T-count is `14 · 2 = 28` (instance of `gidney_adder_tcount`). -/
example : tcount gidney_adder_2bit = 28 := gidney_adder_tcount 0

-- Correctness, concretely instantiated: on 2 bits, with read register
-- `a = 1`, target register `b = 2`, the target decodes to bit i of `(1+2) mod 2²`.
#check (gidney_adder_correct 2 1 2 (by decide) (by decide) (by decide) :
    ∀ i, i < 2 →
      Gate.applyNat (gidney_adder 2) (adder_input_F 2 1 2) (target_idx i)
        = adder_sum_bit_classical 1 2 i)

/-! ## Uniform QASM emission.

The Gidney adder plugs into the project-wide `Gadget` / `emitQASM` framework
(`FormalRV.Codegen.QASMEmit`). The SAME `emitQASM` works for every gadget. -/

/-- The Gidney adder as a uniform, emittable `Gadget` descriptor. -/
def GidneyAdder : Gadget :=
  { name := "gidney_adder", circuit := fun n => gidney_adder n }

-- Emit the 2- and 3-bit adders as OpenQASM 2.0 via the uniform emitter.
#eval IO.println (emitQASM GidneyAdder 2)
#eval IO.println (emitQASM GidneyAdder 3)

/-! ## Exact resource (computed structurally from the construction). -/

-- The EXACT concrete resource for the RSA-2048 adder block (q_A = 33).
#eval IO.println (GidneyAdder.resourceReport 33)   -- T = 14 * 33 = 462

/-- The descriptor's structurally-computed T-count is *exactly* the proven
closed form `14 · n` — for every `n ≥ 2`. -/
example (n : Nat) : GidneyAdder.tcount (n + 2) = 14 * (n + 2) := by
  simpa [Gadget.tcount, GidneyAdder] using gidney_adder_tcount n

/-! ## Emit native-basis QASM to file (input to `scripts/draw_qasm.py` → PNG). -/

#eval (do
  IO.FS.createDirAll "FormalRV/Arithmetic/RippleCarryAdder/diagrams"
  IO.FS.writeFile "FormalRV/Arithmetic/RippleCarryAdder/diagrams/gidney_adder_2bit.qasm"
    (GidneyAdder.toQASMNative 2)
  IO.println "wrote diagrams/gidney_adder_2bit.qasm" : IO Unit)

end FormalRV.BQAlgo
