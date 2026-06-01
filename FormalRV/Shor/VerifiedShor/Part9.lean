import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.Part8

namespace VerifiedShor
namespace VerifiedModMulFamily
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


/-- **Shor success-probability bound — generic over any verified
multiplier family.**  This is the application-facing theorem: pick
any `F : VerifiedModMulFamily a N bits anc` and a relaxed Shor
setting, and the bound follows. -/
theorem shorCorrect
    {a N bits anc : Nat} (F : VerifiedModMulFamily a N bits anc)
    (r m : Nat) (h_setting : ShorSetting a r N m bits) :
    FormalRV.SQIRPort.probability_of_success a r N m bits anc F.family
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 :=
  correct_parametric a r N m bits anc F.family h_setting F.mmi
    (fun i _ => F.wellTyped i)

end VerifiedModMulFamily
end VerifiedShor
