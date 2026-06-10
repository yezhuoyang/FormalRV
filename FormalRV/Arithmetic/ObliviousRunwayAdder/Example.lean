import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd
import FormalRV.Arithmetic.Windowed.WindowedCircuit
import FormalRV.Codegen.GateQasm

open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
open FormalRV.Shor.WindowedCircuit
open FormalRV.Framework
open FormalRV.BQAlgo

/-! Concrete oblivious-carry-runway adders: `k` segments of `gSep` data bits. -/
private def report (gSep k : Nat) : String :=
  let g := runwayAddK gSep k
  s!"runwayAddK gSep={gSep} k={k} (n={gSep*k}): toffoli={toffoliCount g} tcount={Gate.tcount g} gcount={Gate.gcount g} width={width g}"
#eval IO.println (report 4 2)
#eval IO.println (report 4 4)
#eval IO.println (report 8 4)

/-! ## Honest resource comparison vs a plain Cuccaro adder (same n = 8).
    `Gate.depth` here = SEQUENTIAL gate count (it sums over `seq`); the `Gate` IR has no
    parallel constructor, so this `runwayAddK` (a `seq` of disjoint segments) shows NO depth
    win — it is WORSE than a plain Cuccaro on toffoli / depth / width. The runway's theoretical
    depth advantage requires running the disjoint segments CONCURRENTLY (one segment's depth
    instead of the sum), which is outside this IR/measure. -/
private def cmpRpt (nm : String) (g : Gate) : String :=
  s!"{nm}: toffoli={toffoliCount g} gates={Gate.gcount g} depth(seq)={Gate.depth g} width={width g}"
#eval IO.println (cmpRpt "plain cuccaro n=8 (1 block)" (cuccaroAdder.circuit 8 0))
#eval IO.println (cmpRpt "runway g4 k2  (n=8)        " (runwayAddK 4 2))
#eval IO.println (cmpRpt "runway g2 k4  (n=8)        " (runwayAddK 2 4))
#eval IO.println s!"one g4 segment (cuccaro 5) depth = {Gate.depth (cuccaroAdder.circuit 5 0)}  (the PARALLEL depth g4k2 COULD reach if its 2 disjoint segments ran concurrently; actual seq depth is 2x this)"

/-! ## Emit native-basis OpenQASM (input to scripts/draw_qasm.py and verify_qasm.py). -/
#eval (do
  let d := "FormalRV/Arithmetic/ObliviousRunwayAdder/diagrams"
  IO.FS.createDirAll d
  IO.FS.writeFile s!"{d}/oblivious_runway_adder_g2_k2.qasm"
    (FormalRV.Codegen.toQasm (runwayAddK 2 2) false (width (runwayAddK 2 2)))
  IO.FS.writeFile s!"{d}/runway_g4_k1.qasm"
    (FormalRV.Codegen.toQasm (runwayAddK 4 1) false (width (runwayAddK 4 1)))
  IO.FS.writeFile s!"{d}/runway_g4_k2.qasm"
    (FormalRV.Codegen.toQasm (runwayAddK 4 2) false (width (runwayAddK 4 2)))
  IO.println "wrote g2k2 + g4k1 + g4k2 qasm" : IO Unit)
