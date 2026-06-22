/-
  scripts/CheckDeviceProgram.lean — the Lean side of the shared-syntax loop:
  PARSE the shared backend JSON + DEVICE-PROGRAM files from disk and run the
  SAME decidable strict invariant bundle the `native_decide` theorems certify.

  Run from the repo root (after EmitAdderDeviceProgram):
      lake env lean --run scripts/CheckDeviceProgram.lean

  Verifies:
    1. round-trip: parsing `adder_d3.dp` reproduces the in-Lean schedule
       object exactly (and likewise for the bad variant);
    2. file-driven verdicts: the strict bundle on the PARSED inputs returns
       PASS for adder_d3.dp and FAIL for adder_d3_bad.dp — matching both the
       static theorems and the FTQ-VM's verdicts on the same files.
-/
import FormalRV.Codegen.DeviceProgramParse
import FormalRV.Codegen.SysCallEmit
import FormalRV.System.Compile.SurgeryGadgetToSysCalls
import FormalRV.System.Core.ScheduleCombinators
import FormalRV.System.Examples.AdderSystem
import FormalRV.System.Params.HardwareCatalog

open FormalRV.System.Architecture
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.AdderSystem
open FormalRV.Codegen.DeviceProgramParse

def adderSchedule : List SysCall :=
  seqManySchedules (List.replicate 12 (compileSurgeryGadgetToSysCalls surgery_ppm_A))

/-- Structural equality via `Repr` (SysCall derives no BEq; fine for a script). -/
def schedEq (a b : List SysCall) : Bool :=
  toString (repr a) == toString (repr b)

def main : IO UInt32 := do
  let dir := "ftq_vm/backend/examples"
  let backendText ← IO.FS.readFile (dir ++ "/adder_d3_backend.json")
  let goodText ← IO.FS.readFile (dir ++ "/adder_d3.dp")
  let badText ← IO.FS.readFile (dir ++ "/adder_d3_bad.dp")

  let mut failures := 0

  -- 1. round-trip: parse (emit s) = s
  match parseDeviceProgram goodText with
  | .error e => IO.println s!"PARSE ERROR (good): {e}"; failures := failures + 1
  | .ok parsed =>
      if schedEq parsed adderSchedule then
        IO.println s!"round-trip OK: adder_d3.dp parses to the in-Lean schedule ({parsed.length} syscalls)"
      else
        IO.println "ROUND-TRIP MISMATCH: adder_d3.dp ≠ in-Lean schedule"
        failures := failures + 1
  match parseDeviceProgram badText with
  | .error e => IO.println s!"PARSE ERROR (bad): {e}"; failures := failures + 1
  | .ok parsed =>
      if schedEq parsed bad_parallel_adder_syscalls then
        IO.println s!"round-trip OK: adder_d3_bad.dp parses to bad_parallel_adder_syscalls ({parsed.length} syscalls)"
      else
        IO.println "ROUND-TRIP MISMATCH: adder_d3_bad.dp ≠ bad_parallel_adder_syscalls"
        failures := failures + 1

  -- 2. file-driven verdicts through the strict bundle
  match checkDeviceProgram backendText goodText with
  | .error e => IO.println s!"CHECK ERROR (good): {e}"; failures := failures + 1
  | .ok verdict =>
      let v := if verdict then "PASS" else "FAIL"
      IO.println s!"Lean strict bundle on parsed adder_d3.dp:     {v} (expected PASS)"
      if ¬ verdict then failures := failures + 1
  match checkDeviceProgram backendText badText with
  | .error e => IO.println s!"CHECK ERROR (bad): {e}"; failures := failures + 1
  | .ok verdict =>
      let v := if verdict then "PASS" else "FAIL"
      IO.println s!"Lean strict bundle on parsed adder_d3_bad.dp: {v} (expected FAIL)"
      if verdict then failures := failures + 1

  -- 3. catalog consistency: the backend FILE (generated from the hardware
  --    catalog) parses back to exactly the catalog entry's derived models —
  --    one Lean definition is the source of truth for BOTH checkers.
  let spec := FormalRV.System.HardwareCatalog.adder_d3
  match parseBackend backendText with
  | .error e => IO.println s!"BACKEND PARSE ERROR: {e}"; failures := failures + 1
  | .ok pb =>
      let opCapOk := toString (repr pb.opCap) == toString (repr spec.toOpCap)
      let slotOk := toString (repr pb.slotCap) == toString (repr spec.toSlotCap)
      let ancOk := toString (repr pb.ancillaModel) == toString (repr spec.toAncillaModel)
      let gateOk := toString (repr pb.gateTable) == toString (repr spec.toGateTable)
      let scalarsOk := pb.t_react_us == spec.decoder.max_latency_us
        && pb.window_us == spec.window_us
        && pb.max_per_window == spec.max_per_window
        && pb.arch.total_sites == spec.toZonedArch.total_sites
        && pb.arch.t_cycle_us == spec.toZonedArch.t_cycle_us
      if opCapOk && slotOk && ancOk && gateOk && scalarsOk then
        IO.println "catalog round-trip OK: parseBackend(file) = HardwareCatalog.adder_d3 derivations"
      else
        IO.println s!"CATALOG MISMATCH: opCap={opCapOk} slot={slotOk} anc={ancOk} gates={gateOk} scalars={scalarsOk}"
        failures := failures + 1

  -- 4. parallel-layer recognition (exact-interval grouping, shared rule
  --    with the VM's parallel_groups): the good schedule is fully
  --    sequential; the bad one runs two blocks simultaneously.
  match parseDeviceProgram goodText, parseDeviceProgram badText with
  | .ok good, .ok bad =>
      let mGood := maxSimultaneous good
      let mBad := maxSimultaneous bad
      let wideBad := ((parallelGroups bad).filter (fun g => g.2.length > 1)).length
      IO.println s!"parallel layers: adder_d3 max simultaneity {mGood} (expected 1); adder_d3_bad max {mBad} across {wideBad} two-op layers (expected 2 across 16)"
      if mGood ≠ 1 ∨ mBad ≠ 2 ∨ wideBad ≠ 16 then failures := failures + 1
  | _, _ => failures := failures + 1

  if failures == 0 then
    IO.println "ALL LEAN-SIDE CHECKS OK"
    return 0
  else
    IO.println s!"{failures} FAILURE(S)"
    return 1
