/-
  scripts/EmitGE2021Ready.lean — emit the GE2021 readiness artifacts:

    * `backend_ge2021.json` — the PATCH-granular Gidney–Ekerå 2021
      machine, GENERATED from `HardwareCatalog.ge2021_logical` (d = 27
      patches; 62 000 decode lanes / 10 µs reaction; 1093-factory magic
      curve; the 6200-patch × 728-bit syndrome link);
    * `ge2021_probe.dp` — the W2-compiled d = 27 probe program
      (X-merge ∥ CCZ injection ∥ Z-merge, tau_s = 27).

  Lean half: `ge2021_probe_passes` / `..._fails_without_reaction_budget` /
  `..._decode_ids_unique` (native_decide) + the audit pin
  `catalog_ge2021_arch_eq` (rfl).  The VM runs the same bytes
  (`tests/test_ge2021_ready.py`).

  Run:  lake env lean --run scripts/EmitGE2021Ready.lean
-/
import FormalRV.Codegen.SysCallEmit
import FormalRV.System.Compile.QECScheduleToSystem

open FormalRV.System.Architecture
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.QECScheduleToSystem
open FormalRV.Codegen.SysCallEmit

def main : IO Unit := do
  let dir := "ftq_vm/backend/examples/corpus"
  IO.FS.writeFile (dir ++ "/backend_ge2021.json")
    FormalRV.System.HardwareCatalog.ge2021_logical.toBackendJson
  IO.FS.writeFile (dir ++ "/ge2021_probe.dp")
    (emitSchedule
      "ge2021-probe {backend=ge2021} d=27 W2 output: X-merge + CCZ injection + Z-merge, tau_s=27"
      ge2021ProbeCompiled ++ "\n")
  IO.println s!"ge2021_probe.dp: {ge2021ProbeCompiled.length} syscalls, wallclock {scheduleWallclockUs ge2021ProbeCompiled} us, {(FormalRV.Resource.SysCallCount.decodeIds ge2021ProbeCompiled).length} decode rounds"
