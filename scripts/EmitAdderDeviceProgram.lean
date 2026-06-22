/-
  scripts/EmitAdderDeviceProgram.lean — emit the d=3 surface-code 2-bit-adder
  surgery schedule as a shared DEVICE-PROGRAM 1.0 file (plus the intentionally
  invalid parallel variant), the SAME schedule objects certified by
  `Example/Adder2EndToEnd.lean` (`schedule_fits`) and
  `Examples/AdderSystem.lean` (`bad_parallel_adder_schedule_rejected`).

  Run from the repo root:
      lake env lean --run scripts/EmitAdderDeviceProgram.lean

  Writes:
      ftq_vm/backend/examples/adder_d3.dp        (12 merge blocks, PASSES)
      ftq_vm/backend/examples/adder_d3_bad.dp    (2 parallel blocks, REJECTED)
-/
import FormalRV.Codegen.SysCallEmit
import FormalRV.System.Compile.SurgeryGadgetToSysCalls
import FormalRV.System.Core.ScheduleCombinators
import FormalRV.System.Examples.AdderSystem
import FormalRV.System.Params.HardwareCatalog

open FormalRV.System.Architecture
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.AdderSystem
open FormalRV.Codegen.SysCallEmit

/-- The full adder surgery schedule: 12 sequential merge blocks (one per joint
    PPM measurement of the compiled 2-bit Cuccaro adder), each block = τ_s = 3
    syndrome rounds on a d=3 patch + the Pauli-frame update. 192 SysCalls,
    192 µs. Matches `Example/Adder2EndToEnd.exampleSchedule`. -/
def adderSchedule : List SysCall :=
  seqManySchedules (List.replicate 12 (compileSurgeryGadgetToSysCalls surgery_ppm_A))

def main : IO Unit := do
  let dir := "ftq_vm/backend/examples"
  let good := emitSchedule
    "adder-2bit-cuccaro d=3 surgery schedule (12 merge blocks x 3 syndrome rounds)"
    adderSchedule
  let bad := emitSchedule
    "adder-2bit BAD: two merge blocks in parallel (exceeds gate2q capacity 1)"
    bad_parallel_adder_syscalls
  IO.FS.writeFile (dir ++ "/adder_d3.dp") (good ++ "\n")
  IO.FS.writeFile (dir ++ "/adder_d3_bad.dp") (bad ++ "\n")
  -- the VM backends are GENERATED from the hardware catalog: configure in
  -- FormalRV/System/Params/HardwareCatalog.lean, never in the JSON
  IO.FS.writeFile (dir ++ "/adder_d3_backend.json")
    FormalRV.System.HardwareCatalog.adder_d3.toBackendJson
  IO.FS.writeFile (dir ++ "/adder_d3_dualrail_backend.json")
    FormalRV.System.HardwareCatalog.adder_d3_dualRail.toBackendJson
  IO.println s!"adder_d3.dp:     {adderSchedule.length} syscalls, wallclock {scheduleWallclockUs adderSchedule} us"
  IO.println s!"adder_d3_bad.dp: {bad_parallel_adder_syscalls.length} syscalls, wallclock {scheduleWallclockUs bad_parallel_adder_syscalls} us"
  IO.println "backends generated from HardwareCatalog: adder_d3_backend.json, adder_d3_dualrail_backend.json"
