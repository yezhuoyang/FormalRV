/-
  FormalRV.System.ReactionLimitedRuntime — d-cycle vs reaction-limited runtime.

  `surfaceModel.tauToff = d` charges `d` code cycles (27 µs at d=27, 1 µs cycle)
  per logical Toffoli, sequentially.  GE2021 instead runs REACTION-LIMITED
  (notes/gidney-ekera-2021.md; paper §"reaction time 10 µs"): the next Toffoli
  starts after one decode + feed-forward reaction time (10 µs), not after `d`
  full cycles.  For RSA-2048 (2.7×10⁹ Toffolis):

      d-cycle (ours)        : 2.7×10⁹ · 27 µs = 72 900 s = 20.25 h   (our ceiling)
      reaction-limited (GE) : 2.7×10⁹ · 10 µs = 27 000 s =  7.5 h    (≈ GE2021 7.4 h)

  So the "2.5× gap" between our ceiling and GE2021's figure is EXACTLY the
  27 µs / 10 µs cost-model ratio (`gap_is_dcycle_vs_reaction`) — no unexplained
  algorithmic speed-up.

  Residual assumption: reaction-limited execution requires the classical decoder
  to return within ONE reaction time for every patch, every step — a real-time
  load of `realtimeDecodeLoad` ≈ 6.2×10⁹ decode-tasks/s, a CLASSICAL resource
  outside the 20 M qubit budget.  If decoding falls behind, the reaction time
  grows (Fowler/Terhal backlog) and the runtime degrades toward — or past — the
  d-cycle ceiling.  The queue dynamics and the provisioned/divergent dichotomy
  are proved in `DecoderBacklogModel`.

  No `sorry`, no new `axiom`.
-/

import FormalRV.Shor.Resource.ShorFullMachineRequirement
import FormalRV.System.Params.RSA2048

namespace FormalRV.System.ReactionLimitedRuntime

/-! ## §1. The two cost models, side by side (tenths-of-µs) -/

/-- GE2021 reaction time: 10 µs = 100 tenths-µs (paper §2.13). -/
def reactionTime_tenthsUs : Nat := 100

/-- REACTION-LIMITED runtime = (sequential Toffoli depth) × reaction time. -/
def reactionLimitedRuntime (toffoliDepth : Nat) : Nat := toffoliDepth * reactionTime_tenthsUs

/-- d-CYCLE runtime (our `surfaceModel`) = (Toffoli count) × d × cycle time. -/
def dCycleRuntime (toffoli d cycle_tenthsUs : Nat) : Nat := toffoli * d * cycle_tenthsUs

/-! ## §2. RSA-2048 (2.7×10⁹ Toffolis, d=27, 1 µs cycle) -/

/-- Our d-cycle ceiling: 20.25 h (729×10⁹ tenths-µs). -/
theorem rsa2048_dcycle : dCycleRuntime 2_700_000_000 27 10 = 729_000_000_000 := by decide

/-- The reaction-limited runtime: 7.5 h (270×10⁹ tenths-µs) — matching GE2021's
    ~7.4 h reported figure. -/
theorem rsa2048_reaction_limited : reactionLimitedRuntime 2_700_000_000 = 270_000_000_000 := by decide

/-- **The "2.5× gap" is the d-cycle (27 µs) vs reaction-time (10 µs) ratio**, not
    an unexplained optimisation: our ceiling is between 2× and 3× the reaction-
    limited runtime that reproduces GE2021. -/
theorem gap_is_dcycle_vs_reaction :
    2 * reactionLimitedRuntime 2_700_000_000 ≤ dCycleRuntime 2_700_000_000 27 10
    ∧ dCycleRuntime 2_700_000_000 27 10 ≤ 3 * reactionLimitedRuntime 2_700_000_000 := by decide

/-! ## §3. The decoder-throughput dependency (the uncounted assumption)

    Reaction-limited execution holds ONLY IF the decoder delivers within one
    reaction time for every patch every step.  We make the real-time decoding
    LOAD explicit so it can no longer hide. -/

/-- RSA-2048 live logical patches (≈ data-block logical qubits). -/
def rsa2048_patches : Nat := FormalRV.System.RSA2048.patches

/-- Syndrome rounds per second per patch (1 µs cycle ⇒ 10⁶/s). -/
def syndromeRoundsPerSec : Nat := 1_000_000

/-- **Real-time decoding load**: patches × rounds/s = the number of decode tasks
    per second the classical decoder fabric must sustain to keep the reaction time
    at 10 µs.  6.2×10⁹ decode-tasks/s — a CLASSICAL resource NOT in the 20 M qubit
    budget and NOT bounded by our `decoderInv`. -/
def realtimeDecodeLoad : Nat := rsa2048_patches * syndromeRoundsPerSec

theorem realtimeDecodeLoad_value : realtimeDecodeLoad = 6_200_000_000 := by decide

/-- Definitional restatement (`rfl`) of `reactionLimitedRuntime`, kept as the
    NAMED marker of the modelling assumption: the 7.5 h figure charges exactly
    one reaction time per Toffoli, which presumes the decoder sustains
    `realtimeDecodeLoad`.  This is a documentation-level claim, not verified
    content — the actual decoder condition is proved in `DecoderBacklogModel`
    (provisioned ⇒ zero backlog; under-provisioned ⇒ divergence). -/
theorem reaction_limited_assumes_decoder (toffoli : Nat) :
    reactionLimitedRuntime toffoli = toffoli * reactionTime_tenthsUs := rfl

end FormalRV.System.ReactionLimitedRuntime
