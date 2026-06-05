import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.ShorAPIDeprecationCompat

namespace VerifiedShor
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)


/-! ## Compatibility note

The following names from the old API remain available (now deprecated):
- `FormalRV.SQIRPort.Shor_correct`
- `FormalRV.SQIRPort.f_modmult_circuit`
- `FormalRV.SQIRPort.f_modmult_circuit_MMI`
- `FormalRV.SQIRPort.f_modmult_circuit_uc_well_typed`

Each is marked `@[deprecated VerifiedShor.correct]` (or the
corresponding constructive verified replacement).  See
`Shor.lean:4570-4716` for the deprecation site. -/

end VerifiedShor
