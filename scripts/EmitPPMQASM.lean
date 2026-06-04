/-
  Emit the verified PPM magic-state-teleportation gadgets (T and CCZ) as runnable
  OpenQASM 3, for the README circuit diagrams.  Run:
    `lake env lean --run scripts/EmitPPMQASM.lean`
  The same gadgets are proven correct in `PPM/TGadgetTeleport.lean`
  (`t_gadget_with_feedback`) and `PPM/CCZGadgetTeleport.lean`, and cross-checked by
  `PyCircuits/ppm_qasm_verification.py`.
-/
import FormalRV.PPM.PPMToQASM

open FormalRV.PPM.PPMToQASM

def main : IO Unit := do
  IO.FS.writeFile "PyCircuits/qasm/t_gadget.qasm"   tGadgetQASM
  IO.FS.writeFile "PyCircuits/qasm/ccz_gadget.qasm" cczGadgetQASM
  IO.println "emitted PyCircuits/qasm/t_gadget.qasm and ccz_gadget.qasm"
