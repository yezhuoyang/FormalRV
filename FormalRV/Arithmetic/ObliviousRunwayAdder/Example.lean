import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd
import FormalRV.Arithmetic.Windowed.WindowedCircuit
import FormalRV.Codegen.GateQasm

open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
open FormalRV.Shor.WindowedCircuit
open FormalRV.Framework

/-! Concrete oblivious-carry-runway adders: `k` segments of `gSep` data bits. -/
private def report (gSep k : Nat) : String :=
  let g := runwayAddK gSep k
  s!"runwayAddK gSep={gSep} k={k} (n={gSep*k}): toffoli={toffoliCount g} tcount={Gate.tcount g} gcount={Gate.gcount g} width={width g}"
#eval IO.println (report 4 2)
#eval IO.println (report 4 4)
#eval IO.println (report 8 4)

/-! Emit native-basis OpenQASM (input to scripts/draw_qasm.py). -/
#eval (do
  let d := "FormalRV/Arithmetic/ObliviousRunwayAdder/diagrams"
  IO.FS.createDirAll d
  let g := runwayAddK 2 2
  IO.FS.writeFile s!"{d}/oblivious_runway_adder_g2_k2.qasm" (FormalRV.Codegen.toQasm g false (width g))
  IO.println "wrote oblivious_runway_adder_g2_k2.qasm" : IO Unit)
