/-
  FormalRV.Audit.Common — shared infrastructure used by MULTIPLE paper audits
  (surface-code surgery gadgets, Shor/Surface/Windowed machinery, cost/decoder/zone
  models, paper-claim constants).  Per-paper folders under Audit/ import from here;
  it is NOT about any single paper.
-/
import FormalRV.Audit.Common.ConcreteMachineFeasibility
import FormalRV.Audit.Common.CostModelWeightDemo
import FormalRV.Audit.Common.DecodeLatencySensitivity
import FormalRV.Audit.Common.DecoderBacklogModel
import FormalRV.Audit.Common.GateSyndromeWorkedExample
import FormalRV.Audit.Common.LaSsynthImport
import FormalRV.Audit.Common.MagicInjectionSurgery
import FormalRV.Audit.Common.NaiveBaselineCost
import FormalRV.Audit.Common.PaperClaims
import FormalRV.Audit.Common.ReactionLimitedRuntime
import FormalRV.Audit.Common.ResourceAuditGaps
import FormalRV.Audit.Common.ShorCriticalPathFloor
import FormalRV.Audit.Common.ShorEmit
import FormalRV.Audit.Common.ShorEmitDistance
import FormalRV.Audit.Common.ShorFullMachineRequirement
import FormalRV.Audit.Common.ShorLPContract
import FormalRV.Audit.Common.ShorModMulPPMFactoryE2E
import FormalRV.Audit.Common.ShorOnLPBridge
import FormalRV.Audit.Common.ShorPPMEndToEnd
import FormalRV.Audit.Common.ShorPPMUnitaryReduction
import FormalRV.Audit.Common.StabilizerScheduleVerify
import FormalRV.Audit.Common.SurfaceShorFullSchedule
import FormalRV.Audit.Common.SurfaceShorFullStack
import FormalRV.Audit.Common.SurfaceShorPPMEndToEnd
import FormalRV.Audit.Common.SurfaceShorResourceCount
import FormalRV.Audit.Common.SurfaceSystemCompile
import FormalRV.Audit.Common.SurgeryDemoCNOT
import FormalRV.Audit.Common.SurgeryDemoMerge
import FormalRV.Audit.Common.SurgeryDemoSteane
import FormalRV.Audit.Common.SurgeryDemoSurface
import FormalRV.Audit.Common.SyndromeMeasurementLatency
import FormalRV.Audit.Common.TeleportCCXGrounded
import FormalRV.Audit.Common.WindowedShorDeviceSchedule
import FormalRV.Audit.Common.WindowedShorPPMFactoryE2E
import FormalRV.Audit.Common.WindowedShorPhysicalEstimate
import FormalRV.Audit.Common.ZoneBudget
