/-
  scripts/EmitResourceCounts.lean — the Lean half of the L4
  resource-counting consistency check: run THE canonical counters
  (`Resource/SysCallCount`) on parsed DEVICE-PROGRAM schedules and emit
  the numbers as JSON.  `ftq_vm/backend/tests/test_resource_counts.py`
  recomputes every quantity INDEPENDENTLY from the FTQ-VM's parse of the
  same files and asserts exact agreement (time, op counts, qubit
  footprint as a SET of sites, peak occupancy).

  Run:  lake env lean --run scripts/EmitResourceCounts.lean
-/
import FormalRV.Codegen.DeviceProgramParse
import FormalRV.Resource.SysCallCount

open FormalRV.Codegen.DeviceProgramParse
open FormalRV.Resource.SysCallCount

def countsJson (sched : List FormalRV.System.Architecture.SysCall) : String :=
  let sites := (sitesTouched sched).mergeSort (· ≤ ·)
  let siteList := String.intercalate ", " (sites.map toString)
  "{"
  ++ s!"\"wallclock_us\": {wallclockUs sched}, "
  ++ s!"\"busy_us\": {totalBusyUs sched}, "
  ++ s!"\"syscall_count\": {opCountS sched}, "
  ++ s!"\"gate1q\": {countGate1q sched}, "
  ++ s!"\"gate2q\": {countGate2q sched}, "
  ++ s!"\"measure\": {countMeasure sched}, "
  ++ s!"\"transit\": {countTransit sched}, "
  ++ s!"\"fresh_ancilla\": {countFreshAnc sched}, "
  ++ s!"\"magic_req\": {countMagicReq sched}, "
  ++ s!"\"decode\": {countDecode sched}, "
  ++ s!"\"feedback\": {countFeedback sched}, "
  ++ s!"\"qubit_footprint\": {qubitFootprint sched}, "
  ++ s!"\"peak_sites\": {peakSiteOccupancy sched}, "
  ++ s!"\"sites\": [{siteList}]"
  ++ "}"

def main : IO UInt32 := do
  let corpus := "ftq_vm/backend/examples/corpus"
  let entries : List (String × String) :=
    [ ("qec_compiled",       s!"{corpus}/qec_compiled.dp")
    , ("e01_clean",          s!"{corpus}/e01_clean.dp")
    , ("e19_syndrome_flood", s!"{corpus}/e19_syndrome_flood.dp")
    , ("e21_decoder_paced",  s!"{corpus}/e21_decoder_paced.dp")
    , ("adder_d3",           "ftq_vm/backend/examples/adder_d3.dp") ]
  let mut rows : List String := []
  for (name, path) in entries do
    let text ← IO.FS.readFile path
    match parseDeviceProgram text with
    | .error e => IO.println s!"PARSE ERROR {name}: {e}"; return 1
    | .ok sched =>
        rows := rows ++ [s!"  \"{name}\": {countsJson sched}"]
        IO.println s!"{name}: {opCountS sched} ops, wallclock {wallclockUs sched} us, footprint {qubitFootprint sched} sites, peak {peakSiteOccupancy sched}"
  IO.FS.writeFile s!"{corpus}/lean_resource_counts.json"
    ("{\n" ++ String.intercalate ",\n" rows ++ "\n}\n")
  IO.println "wrote lean_resource_counts.json"
  return 0
