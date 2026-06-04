import FormalRV.Shor.Approx
import FormalRV.Shor.ControlledGates
import FormalRV.Shor.Eigenstate
import FormalRV.Shor.EkeraHastad
import FormalRV.Shor.EncodingAgnostic
import FormalRV.Shor.Main
import FormalRV.Shor.MeasUncompute
import FormalRV.Shor.PhaseKickback
import FormalRV.Shor.PostQFT
import FormalRV.Shor.QPE
import FormalRV.Shor.QPEAmplitude
import FormalRV.Shor.Shor
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

/-!
# FormalRV.Shor

The main result: Shor order-finding success probability (see `Shor/Main.lean`), QPE, phase kickback, inverse-QFT.

This umbrella imports every module under `Shor/`.
-/
