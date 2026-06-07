import FormalRV.Shor.AQFTCompile
import FormalRV.Shor.AQFTCompileSemantics
import FormalRV.Shor.Approx
import FormalRV.Shor.ApproxTransfer
import FormalRV.Shor.CliffordTControlledModExp
import FormalRV.Shor.ControlledGates
import FormalRV.Shor.ControlledModExpCount
import FormalRV.Shor.Eigenstate
import FormalRV.Shor.EncodingAgnostic
import FormalRV.Shor.Main
import FormalRV.Shor.MeasUncompute
import FormalRV.Shor.ModExpToffoliCount
import FormalRV.Shor.PPMShorMaster
import FormalRV.Shor.PhaseKickback
import FormalRV.Shor.PostQFT
import FormalRV.Shor.ProbabilityTransfer
import FormalRV.Shor.QPE
import FormalRV.Shor.QPEAmplitude
import FormalRV.Shor.MainAlgorithm
import FormalRV.Shor.SuccessSensitivity
import FormalRV.Shor.TotientLowerBound
import FormalRV.Shor.VerifiedShor
import FormalRV.Shor.WindowedArith
import FormalRV.Shor.WindowedCapstone
import FormalRV.Shor.WindowedCircuit
import FormalRV.Shor.WindowedComposed
import FormalRV.Shor.WindowedComposedCost
import FormalRV.Shor.WindowedCostModel
import FormalRV.Shor.WindowedEndToEnd
import FormalRV.Shor.WindowedLookupAdd
import FormalRV.Shor.WindowedPPM
import FormalRV.Shor.WindowedShorConnection
import FormalRV.Shor.WindowedTimeCost
import FormalRV.Shor.WindowedWidth
import FormalRV.Shor.ShorEmit
import FormalRV.Shor.ShorEmitDistance
import FormalRV.Shor.ShorPPMEndToEnd
import FormalRV.Shor.ShorPPMUnitaryReduction
import FormalRV.Shor.ShorModMulPPMFactoryE2E
import FormalRV.Shor.WindowedShorPPMFactoryE2E
import FormalRV.Shor.TeleportCCXGrounded
import FormalRV.Shor.ShorCriticalPathFloor
import FormalRV.Shor.ShorFullMachineRequirement

/-!
# FormalRV.Shor

The main result: Shor order-finding success probability (see `Shor/Main.lean`), QPE, phase kickback, inverse-QFT.

This umbrella imports every module under `Shor/`.
-/
