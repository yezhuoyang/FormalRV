import FormalRV.QFT.AQFTCompile
import FormalRV.QFT.AQFTCompileSemantics
import FormalRV.Shor.Approx
import FormalRV.Shor.ApproxTransfer
import FormalRV.Shor.Resource.CliffordTControlledModExp
import FormalRV.QPE.ControlledGates
import FormalRV.Shor.Resource.ControlledModExpCount
import FormalRV.Shor.OrderFinding.Eigenstate
import FormalRV.Shor.OrderFinding.EncodingAgnostic
import FormalRV.Shor.Main
import FormalRV.Shor.MeasUncompute
-- The two ripple-adder-lineage modular multipliers as instances of the
-- canonical `EncodeRoundTripModMul` multiplier interface.
import FormalRV.Shor.MultiplierInstances
import FormalRV.Shor.Resource.ModExpToffoliCount
import FormalRV.Shor.PPM.PPMShorMaster
import FormalRV.QPE.PhaseKickback
import FormalRV.Shor.PostQFT
import FormalRV.Shor.OrderFinding.ProbabilityTransfer
import FormalRV.QPE.QPE
import FormalRV.QPE.QPEAmplitude
import FormalRV.Shor.MainAlgorithm
import FormalRV.Shor.OrderFinding.SuccessSensitivity
import FormalRV.Shor.OrderFinding.TotientLowerBound
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
import FormalRV.Shor.PPM.ShorEmit
import FormalRV.Shor.PPM.ShorEmitDistance
import FormalRV.Shor.PPM.ShorPPMEndToEnd
import FormalRV.Shor.PPM.ShorPPMUnitaryReduction
import FormalRV.Shor.PPM.ShorModMulPPMFactoryE2E
import FormalRV.Shor.WindowedShorPPMFactoryE2E
import FormalRV.Shor.PPM.TeleportCCXGrounded
import FormalRV.Shor.Resource.ShorCriticalPathFloor
import FormalRV.Shor.Resource.ShorFullMachineRequirement

/-!
# FormalRV.Shor

The main result: Shor order-finding success probability (see `Shor/Main.lean`), QPE, phase kickback, inverse-QFT.

This umbrella imports every module under `Shor/`.
-/
