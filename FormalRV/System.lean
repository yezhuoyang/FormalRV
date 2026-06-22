-- Core IR: zones, channels, SysCall schedule model, coded layouts
import FormalRV.System.Core.Architecture
import FormalRV.System.Core.CodedLayout
-- Decidable invariant checkers (SysCall lane): I1-I4 + strengthened bundles
import FormalRV.System.Invariants.ScheduleInvariantsExplicit
import FormalRV.System.Invariants.InvariantFramework
import FormalRV.System.Invariants.SystemInvariantStrengthening
-- Checker bundles + honest gap audit
import FormalRV.System.Checkers.SystemChecker
import FormalRV.System.Checkers.FaultTolerantSchedule
-- The DeviceOp lane (second schedule formalization; connected by theorems)
import FormalRV.System.DeviceLane.DeviceSchedule
import FormalRV.System.DeviceLane.RoutingResourceModel
import FormalRV.System.DeviceLane.DependencyGraph
-- Decoder / syndrome-stream rate models
import FormalRV.System.Decoder.DecoderBacklogModel
import FormalRV.System.Decoder.DecodeLatencySensitivity
import FormalRV.System.Decoder.ReactionLimitedRuntime
import FormalRV.System.Decoder.SyndromeMeasurementLatency
import FormalRV.System.Decoder.ResourceAuditGaps
-- Magic-state pipeline (readiness, whole-circuit wait law)
import FormalRV.System.Magic.MagicStateReadiness
import FormalRV.System.Magic.MagicScheduleComplete
-- Resource bounds: floors, ceilings, sensitivity
import FormalRV.System.Bounds.ScheduleLowerBound
import FormalRV.System.Bounds.NaiveSchedule
import FormalRV.System.Bounds.NaiveUpperBound
import FormalRV.System.Bounds.ScheduleBounds
import FormalRV.System.Bounds.HardwareSensitivity
import FormalRV.System.Bounds.ScheduleAdvance
-- Gadget -> SysCall compilation (surface-code pipeline)
import FormalRV.System.Compile.SurgeryGadgetToSysCalls
-- W2: whole-program QEC-surgery -> SysCall driver (unique decode ids,
-- recursive resource counts)
import FormalRV.System.Compile.QECScheduleToSystem
import FormalRV.System.Compile.LatticeSurgeryPPMContract
import FormalRV.System.Compile.SurfaceSystemCompile
-- Certificates / compressed schedules (Lean<->Python artifact interface)
import FormalRV.System.Artifacts.LayeredArtifactInterface
import FormalRV.System.Artifacts.CompressedRepeatSoundness
-- Symbolic resource evaluator = canonical counters on the expansion
import FormalRV.System.Artifacts.CompressedRepeat.ResourceCorrectness
-- Worked examples & demos
import FormalRV.System.Examples.SystemInvariantExamples
import FormalRV.System.Examples.AdderSystem
import FormalRV.System.Examples.ParallelismVerification
import FormalRV.System.Examples.CostModelWeightDemo
import FormalRV.System.Examples.ConcreteMachineFeasibility
-- Hardware parameter records + canonical workload constants
import FormalRV.System.Params.HardwareParams
import FormalRV.System.Params.ZoneBudget
import FormalRV.System.Params.RSA2048
import FormalRV.System.Params.HardwareCatalog
-- The facade (single coherent entry point)
import FormalRV.System.FTFramework
-- Composition bridge: System resource/runtime numbers tied to the verified composed circuit
import FormalRV.System.Compose.VerifiedWorkloadBridge

/-!
# FormalRV.System

System invariants: scheduling, layout, architecture, capacity/latency/bandwidth checks.

This umbrella imports every module under `System/`.  Layout (post 2026-06-11 reorg,
see `System/VM_AUDIT.md` §4):

- `Core/`       — `Architecture` (Zone/Channel/SysCall IR), `CodedLayout` (+ `syscall_acts_on`)
- `Invariants/` — decidable I1–I4 checkers and the strengthened bundles
- `Checkers/`   — `SystemChecker` (adversarial gap audit), `FaultTolerantSchedule`
- `DeviceLane/` — the parallel `DeviceOp` schedule engine + routing + dependency graphs
- `Decoder/`    — decoder backlog/reaction/syndrome-latency rate models
- `Magic/`      — magic-state readiness and whole-circuit wait laws
- `Bounds/`     — lower floors, naive ceilings, hardware sensitivity
- `Compile/`    — surgery-gadget → SysCall compilation and full surface-Shor schedules
- `Artifacts/`  — layered artifact/certificate interface, compressed-repeat soundness
  (the landing zone for the FTQ-VM `certificate.json` checker)
- `Examples/`   — worked invariant examples and demo instances
- `Params/`     — hardware parameter records and zone budgets

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
