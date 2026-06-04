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
import FormalRV.Arithmetic.SQIRModMult.Defs

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

def emitProg (name : String) (g : Gate) : IO Unit := do
  let prog := compileArithmeticGateToPPM g
  IO.FS.writeFile s!"PyCircuits/ppm/{name}.txt"
    (String.intercalate "\n" (prog.map cmdStr) ++ "\n")
  IO.println s!"emitted {name} PPM program: {prog.length} commands"

def main : IO Unit := do
  IO.FS.createDirAll "PyCircuits/ppm"
  -- the verified 3-bit Cuccaro adder
  emitProg "adder3_ppm" (cuccaro_n_bit_adder_full 3 0)
  -- the verified modular multiplier x ↦ 7·x mod 15
  emitProg "modmult_215_7_ppm" (sqir_modmult_const_gate 2 15 7)
