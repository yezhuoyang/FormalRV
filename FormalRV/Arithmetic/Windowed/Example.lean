/-
  FormalRV.Arithmetic.Windowed.Example
  ────────────────────────────────────
  Worked example + diagram emission for the ADDER-GENERIC windowed multiplier:
  the same circuit on the Cuccaro and the Gidney adder. Contains `#eval` demos,
  so it is OFF the default build path. Build / run on demand:
    lake build FormalRV.Arithmetic.Windowed.Example
-/
import FormalRV.Arithmetic.Windowed.WindowedCircuitCorrect
import FormalRV.Codegen.GateQasm

namespace FormalRV.Shor.WindowedCircuit

open FormalRV.Framework FormalRV.Codegen FormalRV.BQAlgo

/-! ## Head-to-head: same multiplier, two adders (`bits = 4`, `a = 3`). -/

private def report (nm : String) (A : Adder) (w numWin : Nat) : String :=
  let g := windowedMulCircuitOf A w 4 3 numWin
  s!"{nm} w={w} numWin={numWin}: toffoli={toffoliCount g} tcount={Gate.tcount g} gcount={Gate.gcount g} width={width g}"

#eval IO.println (report "cuccaro" cuccaroAdder 1 4)
#eval IO.println (report "cuccaro" cuccaroAdder 2 2)
#eval IO.println (report "cuccaro" cuccaroAdder 3 2)
#eval IO.println (report "gidney " gidneyAdder 1 4)
#eval IO.println (report "gidney " gidneyAdder 2 2)
#eval IO.println (report "gidney " gidneyAdder 3 2)

/-! ## The verified instances behind the README diagrams (`(3·y) mod 4`, w=2). -/

-- Same theorem, both adders — "any adder + window size ⇒ verified multiplier".
#check fun (y : Nat) (hy : y < 2 ^ (2 * 1)) =>
  windowedMulCircuit_correct_cuccaro 2 2 3 1 y (by decide) hy
#check fun (y : Nat) (hy : y < 2 ^ (2 * 1)) =>
  windowedMulCircuit_correct_gidney 2 2 3 1 y (by decide) hy

-- Identical Toffoli cost across adders at this instance; widths differ (12 vs 15).
example : toffoliCount (windowedMulCircuitOf cuccaroAdder 2 2 3 1)
        = toffoliCount (windowedMulCircuitOf gidneyAdder 2 2 3 1) := by decide
example : width (windowedMulCircuitOf cuccaroAdder 2 2 3 1) = 12 := by decide
example : width (windowedMulCircuitOf gidneyAdder 2 2 3 1) = 15 := by decide

/-! ## Emit native-basis QASM (input to `scripts/draw_qasm.py` → PNG). -/

#eval (do
  let d := "FormalRV/Arithmetic/Windowed/diagrams"
  IO.FS.createDirAll d
  let gC := windowedMulCircuitOf cuccaroAdder 2 2 3 1
  let gG := windowedMulCircuitOf gidneyAdder 2 2 3 1
  IO.FS.writeFile s!"{d}/windowed_mul_cuccaro_w2.qasm" (toQasm gC false (width gC))
  IO.FS.writeFile s!"{d}/windowed_mul_gidney_w2.qasm" (toQasm gG false (width gG))
  IO.println "wrote both windowed-multiplier qasm files" : IO Unit)

end FormalRV.Shor.WindowedCircuit
