/-
  FormalRV.Arithmetic.Cuccaro.CuccaroAdderExample
  ───────────────────────────────────────────────
  A worked example for the Cuccaro adder + its `Gadget` descriptor for the
  uniform QASM emitter.

  This file contains `#eval` demos, so it is kept OFF the default build path
  (not imported by the `Arithmetic` umbrella). Build / run on demand:
    lake build FormalRV.Arithmetic.Cuccaro.CuccaroAdderExample
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroAdderResource
import FormalRV.Codegen.QASMEmit

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.Codegen (Gadget emitQASM)

/-! ## Worked example: the verified 2-bit adder (5 qubits = 2·2+1). -/

/-- The 2-bit Cuccaro adder. -/
def cuccaro_adder_2bit : Gate := cuccaro_n_bit_adder_full 2 0

/-- Its T-count is `14 · 2 = 28` (instance of `cuccaro_adder_tcount`). -/
example : tcount cuccaro_adder_2bit = 28 := by decide

-- Correctness, concretely instantiated: on 2 bits, with carry-in 0,
-- read register `a = 1`, target register `b = 2`, the target decodes to
-- `(1 + 2) mod 2^2`.
#check (cuccaro_adder_correct 2 0 1 2 (by decide) (by decide) :
    cuccaro_target_val 2 0
        (Gate.applyNat (cuccaro_n_bit_adder_full 2 0) (cuccaro_input_F 0 false 1 2))
      = (1 + 2) % 2 ^ 2)

/-! ## Uniform QASM emission.

The Cuccaro adder plugs into the project-wide `Gadget` / `emitQASM`
framework (`FormalRV.Codegen.QASMEmit`). The SAME `emitQASM` works for every
gadget. -/

/-- The Cuccaro adder as a uniform, emittable `Gadget` descriptor. -/
def CuccaroAdder : Gadget :=
  { name := "cuccaro_adder", circuit := fun n => cuccaro_n_bit_adder_full n 0 }

-- Emit the 2- and 3-bit adders as OpenQASM 2.0 via the uniform emitter.
#eval IO.println (emitQASM CuccaroAdder 2)
#eval IO.println (emitQASM CuccaroAdder 3)

/-! ## Exact resource (computed structurally from the construction). -/

-- The EXACT concrete resource for a 2048-bit adder (gates + T-count), read
-- straight off the circuit — no bound, the precise integers.
#eval IO.println (CuccaroAdder.resourceReport 2048)   -- T = 14 * 2048 = 28672

/-- The descriptor's structurally-computed T-count is *exactly* the proven
closed form `14 · n` — for every `n`. -/
example (n : Nat) : CuccaroAdder.tcount n = 14 * n := by
  simpa [Gadget.tcount, CuccaroAdder] using cuccaro_adder_tcount n 0

/-! ## Emit native-basis QASM to file (input to `scripts/draw_qasm.py` → PNG). -/

#eval (do
  IO.FS.createDirAll "FormalRV/Arithmetic/Cuccaro/diagrams"
  IO.FS.writeFile "FormalRV/Arithmetic/Cuccaro/diagrams/cuccaro_adder_2bit.qasm"
    (CuccaroAdder.toQASMNative 2)
  IO.println "wrote diagrams/cuccaro_adder_2bit.qasm" : IO Unit)

end FormalRV.BQAlgo
