import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd
import FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth
import FormalRV.Arithmetic.Windowed.WindowedCircuit
import FormalRV.Codegen.GateQasm

open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
open FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth
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

/-! ## §★ THE REALIZED PARALLEL-DEPTH ADVANTAGE (ParallelDepth.lean).

`parallelDepth` = ASAP critical-path depth: gates on DISJOINT qubits run
concurrently (proved `parallelDepth (seq g₁ g₂) = max … …` when supports are
disjoint).  The runway adder is a `seq` of `k` disjoint segments, so its parallel
depth is CONSTANT in `k` (= one segment's), while:
  • `Gate.depth` (sequential count) grows ~linearly in k, and
  • a plain `n`-bit Cuccaro adder (n = gSep·k) has parallel depth growing with n
    (its carry chain serializes).
The constant runway parallel-depth column next to the growing plain-adder column
IS the visible advantage proved in `parallelDepth_runwayAddK_eq`. -/
private def pdRow (gSep k : Nat) : String :=
  let runway := runwayAddK gSep k
  let plain  := cuccaroAdder.circuit (gSep * k) 0   -- same n = gSep·k, one block
  s!"gSep={gSep} k={k} (n={gSep*k}): " ++
  s!"runway parDepth={parallelDepth runway} (CONSTANT in k) | " ++
  s!"runway seqDepth={Gate.depth runway} (grows ~k) | " ++
  s!"plain(n) parDepth={parallelDepth plain} (grows ~n) | " ++
  s!"plain(n) seqDepth={Gate.depth plain}"
#eval IO.println "── parallelDepth: runway (constant) vs plain adder (grows) ──"
#eval IO.println (pdRow 4 1)
#eval IO.println (pdRow 4 2)
#eval IO.println (pdRow 4 4)
#eval IO.println (pdRow 4 8)
-- A second gSep to show the constant tracks gSep (= O(gSep) per the headline):
#eval IO.println (pdRow 2 1)
#eval IO.println (pdRow 2 2)
#eval IO.println (pdRow 2 4)
#eval IO.println (pdRow 2 8)
-- One-segment reference (what runwayAddK gSep k equals for every k≥1):
#eval IO.println s!"one g4 segment parDepth = {parallelDepth (cuccaroAdder.circuit 5 (segBase 4 0))} (= runway g4 parDepth for all k≥1, by parallelDepth_runwayAddK_eq)"
-- Plain Cuccaro: parallelDepth vs sequential Gate.depth (carry chain serializes):
#eval IO.println s!"plain cuccaro n=8: parDepth={parallelDepth (cuccaroAdder.circuit 8 0)} vs seqDepth(Gate.depth)={Gate.depth (cuccaroAdder.circuit 8 0)}"
#eval IO.println s!"plain cuccaro n=16: parDepth={parallelDepth (cuccaroAdder.circuit 16 0)} vs seqDepth(Gate.depth)={Gate.depth (cuccaroAdder.circuit 16 0)}"
-- Sanity: same-qubit serial = 2, disjoint-qubit parallel = 1.
#eval IO.println s!"sanity: parallelDepth (X 0; X 0) = {parallelDepth (Gate.seq (Gate.X 0) (Gate.X 0))} (serial=2),  parallelDepth (X 0; X 1) = {parallelDepth (Gate.seq (Gate.X 0) (Gate.X 1))} (parallel=1)"

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
