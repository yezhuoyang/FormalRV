import FormalRV.QFT.AQFTCompile
import FormalRV.QFT.AQFTCompileSemantics
import FormalRV.Shor.Approx
import FormalRV.Shor.ApproxTransfer
import FormalRV.Shor.CliffordTControlledModExp
import FormalRV.QPE.ControlledGates
import FormalRV.Shor.ControlledModExpCount
import FormalRV.Shor.Eigenstate
import FormalRV.Shor.EncodingAgnostic
import FormalRV.Shor.Main
import FormalRV.Shor.MeasUncompute
import FormalRV.Shor.ModExpToffoliCount
import FormalRV.Shor.PPMShorMaster
import FormalRV.QPE.PhaseKickback
import FormalRV.Shor.PostQFT
import FormalRV.Shor.ProbabilityTransfer
import FormalRV.QPE.QPE
import FormalRV.QPE.QPEAmplitude
import FormalRV.Shor.MainAlgorithm
import FormalRV.Shor.SuccessSensitivity
import FormalRV.Shor.TotientLowerBound
import FormalRV.Shor.VerifiedShor
-- Windowed arithmetic gadgets relocated to FormalRV.Arithmetic.Windowed (2026-06-09);
-- the Shor-specific windowed glue stays here.
import FormalRV.Shor.WindowedCapstone
import FormalRV.Shor.WindowedComposed
import FormalRV.Shor.WindowedComposedCost
import FormalRV.Shor.WindowedEndToEnd
import FormalRV.Shor.WindowedPPM
import FormalRV.Shor.WindowedShorConnection
import FormalRV.Shor.WindowedTimeCost
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
