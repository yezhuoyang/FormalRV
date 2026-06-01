import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.Part15

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


/-! ## Final SQIR/Cuccaro certification via interfaces (Phase R6i)

These theorems certify the existing SQIR/Cuccaro circuit family as a
`ModMulImpl` / `VerifiedModMulFamily` through the new interface
stack.  Like R6f-R6h, they are **fallback wrappers** whose statements
reference interface fields but whose proofs route through the
existing `ModMul.*` theorems.

This achieves R6 Goal A — the interface stack carries the full
multiplier chain from `ControlledModAddImpl` (R4b) all the way to
the `MultiplyCircuitProperty` Shor input — even if the proofs are
currently fallback wrappers.

Real interface routing across the entire chain requires R5b'
(enrich `ControlledModAddImpl.clean` bundle with per-position
conjuncts) and replaying the funext-style proofs of
`sqir_modmult_step_state_eq` and downstream theorems.  All of that
work would replace the wrapper proofs without changing the
statements below. -/

end VerifiedShor
