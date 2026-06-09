/-
  FormalRV.Arithmetic.ModularAdder.Gidney.Example
  ───────────────────────────────────────────────
  Worked example + native-QASM emission for the Gidney modular adder. Contains
  `#eval` demos, so it is OFF the default build path (not imported by any
  umbrella). Build / run on demand:
    lake build FormalRV.Arithmetic.ModularAdder.Gidney.Example
-/
import FormalRV.Arithmetic.ModularAdder.Gidney
import FormalRV.Codegen.GateQasm

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Codegen

-- The verified instance behind the README diagram: `(x + 1) mod 3` at
-- `bits = 2`, with `x = 1`, decodes the target to `(1 + 1) mod 3 = 2`.
#check (modAddConst_correct 2 3 1 1
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

-- Its exact size: 12 qubits, 141 gates, 210 T.
example : Gate.tcount (modAddConstGate 2 3 1) = 210 := by decide

/-! ## Emit native-basis QASM to file (input to `scripts/draw_qasm.py` → PNG). -/

#eval (do
  IO.FS.createDirAll "FormalRV/Arithmetic/ModularAdder/Gidney/diagrams"
  IO.FS.writeFile "FormalRV/Arithmetic/ModularAdder/Gidney/diagrams/gidney_modadd_2_3_1.qasm"
    (toQasm (modAddConstGate 2 3 1) false (widthOf (modAddConstGate 2 3 1)))
  IO.println "wrote diagrams/gidney_modadd_2_3_1.qasm" : IO Unit)

end FormalRV.BQAlgo
