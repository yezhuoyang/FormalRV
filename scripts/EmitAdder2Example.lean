/-
  End-to-end worked example for the README: the verified **2-bit Cuccaro adder**
  (`cuccaro_n_bit_adder_full 2 0`, proven by `cuccaro_n_bit_adder_full_correct`).
  Emits its OpenQASM and its PPM (Pauli-product-measurement) program from the REAL
  compilers, and prints the Lean gate/T counts.  Run:
    `lake env lean --run scripts/EmitAdder2Example.lean`
  Output: PyCircuits/qasm/adder2.qasm , PyCircuits/ppm/adder2_ppm.txt
-/
import FormalRV.Core.GateQASM
import FormalRV.Arithmetic.Cuccaro.CuccaroFull
import FormalRV.PPM.CircuitToPPMInterface

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.Framework.Architecture
open FormalRV.Framework.CircuitToPPMInterface
open FormalRV.BQAlgo

def pkStr : PauliKind → String
  | .I => "I" | .X => "X" | .Y => "Y" | .Z => "Z"

def cmdStr : PPMCommand → String
  | .measurePauliKind pk qs => "M " ++ pkStr pk ++ " " ++ String.intercalate "," (qs.map toString)
  | .applyFrameUpdate qs    => "F " ++ String.intercalate "," (qs.map toString)
  | .useMagicT q            => "T " ++ toString q

def main : IO Unit := do
  IO.FS.createDirAll "PyCircuits/qasm"
  IO.FS.createDirAll "PyCircuits/ppm"
  let g := cuccaro_n_bit_adder_full 2 0
  IO.FS.writeFile "PyCircuits/qasm/adder2.qasm" (toQASM g)
  IO.println s!"adder2 QASM: qubits={maxQubit g + 1} numX={numX g} numCX={numCX g} numCCX={numCCX g} gcount={gcount g} tcount={tcount g}"
  let prog := compileArithmeticGateToPPM g
  IO.FS.writeFile "PyCircuits/ppm/adder2_ppm.txt" (String.intercalate "\n" (prog.map cmdStr) ++ "\n")
  IO.println s!"adder2 PPM: {prog.length} commands"
