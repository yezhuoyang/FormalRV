import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.PublicApi
import FormalRV.Shor.VerifiedShor.RelaxedSetting

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


/-! ## Public predicates -/

/-- **Shor setting** for verified Shor (relaxed — no upper register
bound on `n`).  Mathematical content matches `BasicSettingRelaxed`
but the name is the public stable alias. -/
abbrev ShorSetting := FormalRV.BQAlgo.BasicSettingRelaxed

/-- **Verified-circuit sizing**: data register has at least 1 bit, holds
`N`, and is wide enough for `2*N`.  Public stable alias for
`VerifiedCircuitSizing`. -/
abbrev CircuitSizing := FormalRV.BQAlgo.VerifiedCircuitSizing

end VerifiedShor
