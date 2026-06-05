import FormalRV.Shor.MainAlgorithm.QuantumAndContinuedFractions
import FormalRV.Shor.MainAlgorithm.ContinuedFractionBridge
import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement
import FormalRV.Shor.MainAlgorithm.SuccessProbability

/-!
# FormalRV.Shor.MainAlgorithm

The SQIR-ported Shor order-finding correctness chain (`namespace FormalRV.SQIRPort`), in dependency
order:

1. `QuantumAndContinuedFractions` — QPE / quantum primitives, number-theoretic order + modular
   exponentiation, continued-fraction infrastructure, the order-finding post-processor, the Shor
   parameter regime + I/O states, the success constant `kappa`, and the QPE peak / Khinchin bridge.
2. `ContinuedFractionBridge` — equivalence of the `cf_aux` Euclidean state machine with mathlib's
   `GenContFract`, convergent denominators, Fibonacci bounds, termination.
3. `PostProcessingAndMeasurement` — the `r_found` recovery branches and the partial-measurement /
   analytic-QPE chain.
4. `SuccessProbability` — the headline `Shor_correct_var*` success-probability theorems, the
   remaining Tier-3 number-theory / circuit obligations, and the modular-multiplier interface.

(Formerly the non-descriptive `FormalRV/Shor/Shor/Part1..4.lean`.)
-/
