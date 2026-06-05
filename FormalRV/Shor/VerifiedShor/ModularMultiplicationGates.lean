import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.CanonicalBitWidth

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


/-! ## Canonical bit width and sizing discharge -/

/-- **Canonical bit width** for the verified modular multiplier:
`Nat.log2 (2 * N) + 1`.  Always satisfies `CircuitSizing N _`. -/
def canonicalBits (N : Nat) : Nat := Nat.log2 (2 * N) + 1

/-- **Canonical sizing is always satisfiable** for `0 < N`. -/
theorem circuitSizing_canonical (N : Nat) (hN : 0 < N) :
    CircuitSizing N (canonicalBits N) :=
  CircuitSizing.canonical N hN

/-! ## Verified modular multiplication layer -/

end VerifiedShor
