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
  let ppmHeader : String :=
    "# PPM program (Pauli-Product-Measurement / Litinski form) of the 2-bit Cuccaro adder.\n" ++
    "# One instruction per line; lines beginning with '#' are comments. Syntax:\n" ++
    "#   M <P> q1,q2,...  measure the joint Pauli operator P on qubits q1,q2,... (i.e. P_q1 (x) P_q2 (x) ...,\n" ++
    "#                    P in {X,Y,Z}); a single destructive multi-qubit LOGICAL-PARITY measurement.\n" ++
    "#                    e.g. 'M Z 2,1' = measure Z_2 (x) Z_1 (the joint Z-parity of qubits 2 and 1).\n" ++
    "#   F q1,q2,...      Pauli-FRAME update: a classically-tracked Pauli correction on those qubits,\n" ++
    "#                    conditioned on earlier measurement outcomes (feed-forward; NOT a physical gate).\n" ++
    "#   T q              consume one MAGIC state routed to qubit q (the only non-Clifford resource;\n" ++
    "#                    each Toffoli/CCX consumes one |CCZ> magic state via this injection).\n"
  IO.FS.writeFile "PyCircuits/ppm/adder2_ppm.txt" (ppmHeader ++ String.intercalate "\n" (prog.map cmdStr) ++ "\n")
  IO.println s!"adder2 PPM: {prog.length} commands"
