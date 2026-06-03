import FormalRV.LatticeSurgery.ScheduleEmit
import FormalRV.Corpus.SurgeryDemoSurface

open FormalRV.LatticeSurgery.ScheduleEmit
open FormalRV.Corpus.SurgeryDemoSurface
open FormalRV.Framework.SurgerySchedule

-- A demo Shor surgery schedule: 3 logical-X̄ merges on the verified [[13,1,3]] code.
def shorDemoSchedule : Schedule := List.replicate 3 surface3_x_surgery

def main : IO Unit := do
  IO.FS.writeFile "PyCircuits/shor_demo_schedule.stim" (emitScheduleStim shorDemoSchedule)
  IO.println s!"emitted {(shorDemoSchedule).length} surgeries, {scheduleFootprint shorDemoSchedule} physical qubits"
