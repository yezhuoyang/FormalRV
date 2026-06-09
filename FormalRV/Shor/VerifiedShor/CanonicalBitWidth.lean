import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.CircuitSizingStub

namespace VerifiedShor
namespace CircuitSizing
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


/-- **Canonical sizing**: `CircuitSizing N (Nat.log2 (2*N) + 1)` holds
whenever `0 < N`.  Public alias for
`VerifiedCircuitSizing_canonical_pow2_succ`. -/
theorem canonical (N : Nat) (hN : 0 < N) :
    CircuitSizing N (Nat.log2 (2 * N) + 1) :=
  FormalRV.BQAlgo.VerifiedCircuitSizing_canonical_pow2_succ N hN

end CircuitSizing
end VerifiedShor
