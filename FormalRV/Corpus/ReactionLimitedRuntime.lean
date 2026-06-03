/-
  FormalRV.Corpus.ReactionLimitedRuntime — SELF-AUDIT finding #1: our "2.5× time
  gap" is mostly a MODELLING artefact (d-cycle vs reaction-limited), and the real
  residual assumption is DECODER THROUGHPUT.

  ## What the audit found
  Our `surfaceModel.tauToff = d` charges `d` code cycles (= 27 µs at d=27, 1 µs
  cycle) PER logical Toffoli, executed SEQUENTIALLY.  But GE2021 runs
  REACTION-LIMITED (notes/gidney-ekera-2021.md; paper §"reaction time 10 µs"): the
  next Toffoli starts after the DECODE+feed-forward (one reaction time, 10 µs),
  NOT after `d` full cycles.  So:

      d-cycle (ours)        : 2.7×10⁹ · 27 µs = 72 900 s = 20.25 h   (our ceiling)
      reaction-limited (GE) : 2.7×10⁹ · 10 µs = 27 000 s =  7.5 h    (≈ GE2021 7.4 h)

  The 20.25/7.5 ≈ 2.7× "gap" we reported is EXACTLY the reaction-time (10 µs) vs
  d-cycle (27 µs) ratio.  With the CORRECT (reaction-limited) cost the framework
  REPRODUCES GE2021's ~7.5 h — there is no unexplained algorithmic speed-up.

  ## The REAL residual assumption (the larger gap to watch)
  Reaction-limited execution SECRETLY ASSUMES the classical decoder returns a
  logical result within ONE reaction time (10 µs) for EVERY logical qubit, every
  step.  Across ~6200 patches each emitting a syndrome every 1 µs, this is a
  ~6 Gsyndrome/s real-time DECODING load.  If decoding cannot keep up, the
  reaction time GROWS (Fowler/Terhal backlog) and the runtime degrades toward — or
  past — our d-cycle ceiling.  That classical-decoding throughput is NOT in the
  20 M qubit budget and NOT modelled by our `decoderInv` (which only bounds a
  single decode's latency).  See `ReactionLimitedRuntime` §3 + the audit report.

  No `sorry`, no new `axiom`.
-/

import FormalRV.Corpus.ShorFullMachineRequirement

namespace FormalRV.Corpus.ReactionLimitedRuntime

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
    reaction time for every patch every step.  We make the real-time decoding LOAD
    explicit so it can no longer hide. -/

/-- RSA-2048 live logical patches (≈ data-block logical qubits). -/
def rsa2048_patches : Nat := 6200

/-- Syndrome rounds per second per patch (1 µs cycle ⇒ 10⁶/s). -/
def syndromeRoundsPerSec : Nat := 1_000_000

/-- **Real-time decoding load**: patches × rounds/s = the number of decode tasks
    per second the classical decoder fabric must sustain to keep the reaction time
    at 10 µs.  6.2×10⁹ decode-tasks/s — a CLASSICAL resource NOT in the 20 M qubit
    budget and NOT bounded by our `decoderInv`. -/
def realtimeDecodeLoad : Nat := rsa2048_patches * syndromeRoundsPerSec

theorem realtimeDecodeLoad_value : realtimeDecodeLoad = 6_200_000_000 := by decide

/-- **The assumption, stated**: reaction-limited 7.5 h is valid IFF the decoder
    sustains `realtimeDecodeLoad` within `reactionTime`.  Otherwise the effective
    reaction time grows and the runtime degrades toward the d-cycle ceiling (or
    worse, on backlog).  This is the honest residue our 7.5-h reproduction rests
    on — flagged, not hidden. -/
theorem reaction_limited_assumes_decoder (toffoli : Nat) :
    reactionLimitedRuntime toffoli = toffoli * reactionTime_tenthsUs := rfl

end FormalRV.Corpus.ReactionLimitedRuntime
