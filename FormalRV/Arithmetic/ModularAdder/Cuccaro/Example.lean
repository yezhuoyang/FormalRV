/-
  FormalRV.Arithmetic.ModularAdder.Cuccaro.Example
  ────────────────────────────────────────────────
  Worked example + native-QASM emission for the Cuccaro/SQIR modular adder.
  Contains `#eval` demos, so it is OFF the default build path. Build / run:
    lake build FormalRV.Arithmetic.ModularAdder.Cuccaro.Example
-/
import FormalRV.Arithmetic.ModularAdder.Cuccaro
import FormalRV.Codegen.GateQasm

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Codegen

-- The verified instance behind the README diagram: `(x + 1) mod 3` at
-- `bits = 3` (the Cuccaro adder needs `2N ≤ 2^bits`), with `x = 1`, decodes the
-- target to `(1 + 1) mod 3 = 2`.
#check (cuccaroModAddConst_correct 3 3 1 1
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

-- Its exact size: 9 qubits, 91 gates, 168 T.
example : Gate.tcount (sqir_style_modAddConst_clean_gate 3 3 1) = 168 := by decide

/-! ## Emit native-basis QASM to file (input to `scripts/draw_qasm.py` → PNG). -/

#eval (do
  IO.FS.createDirAll "FormalRV/Arithmetic/ModularAdder/Cuccaro/diagrams"
  IO.FS.writeFile "FormalRV/Arithmetic/ModularAdder/Cuccaro/diagrams/cuccaro_modadd_3_3_1.qasm"
    (toQasm (sqir_style_modAddConst_clean_gate 3 3 1) false
      (widthOf (sqir_style_modAddConst_clean_gate 3 3 1)))
  IO.println "wrote diagrams/cuccaro_modadd_3_3_1.qasm" : IO Unit)

end FormalRV.BQAlgo
