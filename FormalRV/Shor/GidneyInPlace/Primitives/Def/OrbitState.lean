/-
  FormalRV.Shor.GidneyInPlace.OrbitState — the QPE orbit-fold primitive.
  ════════════════════════════════════════════════════════════════════════════

  `orbitState F init n = F (n-1) ∘ … ∘ F 0` applied to `init` — the generic step-folded
  trajectory the QPE stage decomposition and the pmDist telescope are stated over.

  Extracted from `EmbedOrbitCompose` (which otherwise carries the DEAD `EmbedAgreeOff`
  orbit-composition engine) so the live hybrid route depends only on this 4-line primitive
  and never transitively imports the dead EmbedAgreeOff / phase-marginal route.
-/
import FormalRV.Shor.MainAlgorithm.QuantumAndContinuedFractions.QuantumPrimitives

namespace FormalRV.Shor.GidneyInPlace.OrbitState

open FormalRV.SQIRPort

/-- The orbit state after `numIter` steps: `F (numIter-1) ∘ … ∘ F 0` applied to `init`. -/
def orbitState {full_dim : Nat} (F : Nat → QState full_dim → QState full_dim)
    (init : QState full_dim) : Nat → QState full_dim
  | 0 => init
  | k + 1 => F k (orbitState F init k)

end FormalRV.Shor.GidneyInPlace.OrbitState
