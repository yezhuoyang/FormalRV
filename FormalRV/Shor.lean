import FormalRV.Shor.AQFTCompile
import FormalRV.Shor.AQFTCompileSemantics
import FormalRV.Shor.ControlledGates
import FormalRV.Shor.Eigenstate
import FormalRV.Shor.Main
import FormalRV.Shor.PhaseKickback
import FormalRV.Shor.PostQFT
import FormalRV.Shor.QPE
import FormalRV.Shor.QPEAmplitude
import FormalRV.Shor.Shor
import FormalRV.Shor.SuccessSensitivity
import FormalRV.Shor.TotientLowerBound
import FormalRV.Shor.VerifiedShor
import FormalRV.Shor.WindowedShorConnection

/-!
# FormalRV.Shor

The main result: Shor order-finding success probability (see `Shor/Main.lean`), QPE, phase kickback, inverse-QFT.

This umbrella imports every module under `Shor/`.
-/
