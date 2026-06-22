/-
  scripts/EmitQECCompiled.lean — emit the W2-compiled heterogeneous QEC
  program (`QECScheduleToSystem.demoCompiled`: X-merge, CCZ magic
  injection, Z-merge — every SysCall derived from connection matrices) to
  DEVICE-PROGRAM text, for the FTQ-VM half of the cross-check.

  The Lean half is the `demoCompiled_passes` / `demoCompiled_decode_ids_unique`
  native_decide theorems; the VM runs the SAME bytes against the SAME
  catalog backend (`backend_magicstock.json`, generated from
  `HardwareCatalog.adder_d3_magicStock`).

  Run:  lake env lean --run scripts/EmitQECCompiled.lean
-/
import FormalRV.Codegen.SysCallEmit
import FormalRV.System.Compile.QECScheduleToSystem

open FormalRV.System.Architecture
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.QECScheduleToSystem
open FormalRV.Codegen.SysCallEmit

def main : IO Unit := do
  let dir := "ftq_vm/backend/examples/corpus"
  IO.FS.writeFile (dir ++ "/qec_compiled.dp")
    (emitSchedule
      "qec-compiled {backend=magicstock} W2-driver output: X-merge + CCZ injection + Z-merge"
      demoCompiled ++ "\n")
  IO.println s!"qec_compiled.dp: {demoCompiled.length} syscalls, wallclock {scheduleWallclockUs demoCompiled} us, {(decodeIds demoCompiled).length} unique decode rounds"
