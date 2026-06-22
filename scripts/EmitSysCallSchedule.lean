/-
  Emit FormalRV's SYSTEM-LEVEL schedule (the verified SysCall stream + the zoned-architecture
  layout) so the tqec block-graph translator can lay patches out CONSISTENTLY WITH OUR SYSTEM
  SPECIFICATION — the Data/Ancilla/Factory zones and the per-gadget site assignments, not an
  arbitrary layout.  Run: `lake env lean --run scripts/EmitSysCallSchedule.lean`.
  Output: PyCircuits/syscalls/{ppm_block,adder}.txt  (ZONE lines + one SysCall per line).
-/
import FormalRV.System.Examples.AdderSystem

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.AdderSystem

def kindStr : SysCallKind → String
  | .Gate1q q _            => s!"GATE1Q {q}"
  | .Gate2q a b _          => s!"GATE2Q {a} {b}"
  | .Measure q _           => s!"MEAS {q}"
  | .TransitQubit q c      => s!"TRANSIT {q} {c}"
  | .RequestFreshAncilla z => s!"FRESHANC {z}"
  | .RequestMagicState f   => s!"MAGIC {f}"
  | .DecodeSyndrome r      => s!"DECODE {r}"
  | .PauliFrameUpdate c    => s!"PFU {c}"

def scStr (sc : SysCall) : String := s!"{kindStr sc.kind} {sc.begin_us} {sc.end_us}"

def zoneStr (z : ArchZone) : String := s!"ZONE {z.name} {z.site_lo} {z.site_hi}"

def writeSched (name : String) (zlines slines : List String) : IO Unit := do
  IO.FS.writeFile s!"PyCircuits/syscalls/{name}.txt"
    (String.intercalate "\n" (zlines ++ slines) ++ "\n")
  IO.println s!"emitted {name}: {slines.length} syscalls, {zlines.length} zones"

def main : IO Unit := do
  IO.FS.createDirAll "PyCircuits/syscalls"
  let zlines := adder_demo_arch.zones.map zoneStr
  writeSched "ppm_block" zlines ((compileSurgeryGadgetToSysCalls surgery_ppm_A).map scStr)
  writeSched "adder" zlines (adder_n1_syscalls.map scStr)
