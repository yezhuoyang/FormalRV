import FormalRV.System.AdderSystem
import FormalRV.System.Architecture
import FormalRV.System.CodedLayout
import FormalRV.System.CompressedRepeatSoundness
import FormalRV.System.DependencyGraph
import FormalRV.System.DeviceSchedule
import FormalRV.System.FTFramework
import FormalRV.System.FaultTolerantSchedule
import FormalRV.System.HardwareErrorParams
import FormalRV.System.HardwareParams
import FormalRV.System.HardwareSensitivity
import FormalRV.System.InvariantFramework
import FormalRV.System.LayeredArtifactInterface
import FormalRV.System.MagicScheduleComplete
import FormalRV.System.MagicStateReadiness
import FormalRV.System.NaiveSchedule
import FormalRV.System.NaiveUpperBound
import FormalRV.System.ParallelismVerification
import FormalRV.System.RoutingResourceModel
import FormalRV.System.ScheduleAdvance
import FormalRV.System.ScheduleBounds
import FormalRV.System.ScheduleInvariantsExplicit
import FormalRV.System.ScheduleLowerBound
import FormalRV.System.SystemChecker
import FormalRV.System.SystemInvariantExamples
import FormalRV.System.SystemInvariantStrengthening

/-!
# FormalRV.System

System invariants: scheduling, layout, architecture, capacity/latency/bandwidth checks.

This umbrella imports every module under `System/`.

**Single entry point:** `FormalRV.System.FTFramework` is the coherent front door tying the two
scheduling subsystems together — canonical hardware (`HardwareParams.MachineParams`, one decoder-
reaction budget), schedule well-formedness (`DeviceSchedule.scheduleValid` /
`ScheduleInv.all_invariants_ok`), the resource BRACKET (`ScheduleBounds.resource_bracket`: lower
floor ≤ workload ≤ upper ceiling, with `naive_peak_le_total` the peak ≤ footprint upper bound), and
hardware SENSITIVITY (`HardwareSensitivity.HW.timeLB`).  The two naive efforts
(`NaiveSchedule` over `DSchedule`, `NaiveUpperBound` over `ResourceEstimate`) and the two checkers
(`DeviceSchedule` over `DeviceOp`, `InvariantFramework` over `SysCall`) are connected by theorems,
not merged.
-/
