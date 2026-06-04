/-
  Emit the FULL PPM program of the verified 3-bit Cuccaro adder, by running the
  real compiler `compileArithmeticGateToPPM` (CircuitToPPMInterface) on the real
  adder Gate IR `cuccaro_n_bit_adder_full 3 0`.  Run:
    `lake env lean --run scripts/EmitAdderPPM.lean`
  Output: PyCircuits/ppm/adder3_ppm.txt  (one PPM command per line), rendered by
  PyCircuits/draw_ppm.py into docs/diagrams/ppm_adder3.png.
-/
import FormalRV.PPM.CircuitToPPMInterface
import FormalRV.Arithmetic.Cuccaro.CuccaroFull

open FormalRV.Framework
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
  IO.FS.createDirAll "PyCircuits/ppm"
  let prog := compileArithmeticGateToPPM (cuccaro_n_bit_adder_full 3 0)
  IO.FS.writeFile "PyCircuits/ppm/adder3_ppm.txt"
    (String.intercalate "\n" (prog.map cmdStr) ++ "\n")
  IO.println s!"emitted adder3 PPM program: {prog.length} commands"
