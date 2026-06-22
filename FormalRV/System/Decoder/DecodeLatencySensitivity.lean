/-
  FormalRV.System.DecodeLatencySensitivity — the decode latency as a first-class
  USER-SPECIFIED input that flows into the verified runtime (not a buried
  constant), coupled to the decoder provisioning it also drives:

    • `reactionLimitedModel decodeLatency` — a cost model whose `tauToff` IS the
      decode latency (in cycles), so the verified `estimateWith` time is
      `n_toff · decodeLatency · cycle`;
    • MONOTONICITY: a slower decoder ⇒ a larger verified runtime;
    • a SENSITIVITY table for RSA-2048 (latency 10/20/27/40 µs →
      7.5/15/20.25/30 h), with the crossover at latency = d, where
      reaction-limited meets the d-cycle ceiling;
    • COUPLING: the SAME decode-latency input also scales the decoder LANE
      requirement (`patches · decodeLatency`, `DecoderBacklogModel`), so a
      slower decoder costs BOTH time and classical hardware.

  No `sorry`, no new `axiom`.
-/

import FormalRV.System.Compile.SurfaceSystemCompile
import FormalRV.System.Decoder.DecoderBacklogModel
import FormalRV.System.Decoder.ReactionLimitedRuntime

namespace FormalRV.System.DecodeLatencySensitivity

open FormalRV.Framework
open FormalRV.Framework.Resource
open FormalRV.System.SurfaceSystemCompile
open FormalRV.LatticeSurgery.SurfaceShorResourceCount

/-! ## §1. Decode latency as the per-Toffoli cost (a tunable cost model) -/

/-- **Reaction-limited cost model.**  The logical-Toffoli cost `tauToff` is the
    DECODE LATENCY (in code cycles) — a USER-SPECIFIED input — not the code
    distance `d`.  Everything else mirrors `surfaceModel`. -/
def reactionLimitedModel (decodeLatencyCycles factory : Nat) : CostModel :=
  { name    := "reaction-limited (tauToff = decode latency)"
    tauToff := fun _ => decodeLatencyCycles
    physPer := fun c => 2 * physPerLogical c
    ancilla := fun _ _ _ _ => { syndrome := 0, surgery := 0 }
    factory := fun _ => factory }

/-- **The decode latency FLOWS INTO the verified time.**  Through the rfl-proven
    `estimateWith` framework, the runtime is `n_toff · decodeLatency · cycle` — a
    function of the user's decode-latency input. -/
theorem reactionLimited_time (decodeLatencyCycles factory : Nat)
    (hw : Hardware) (w : Workload) (c : QECCode) (ow p : Nat) :
    (estimateWith (reactionLimitedModel decodeLatencyCycles factory) hw w c ow p).time_us_tenths
      = w.n_toff * decodeLatencyCycles * hw.cycle_time_us_tenths := rfl

/-- **MONOTONE in the decode latency.**  A slower decoder (larger latency) gives a
    larger verified runtime, all else equal — so the latency genuinely affects the
    verified time (it is not inert). -/
theorem time_mono_decodeLatency (L L' factory : Nat)
    (hw : Hardware) (w : Workload) (c : QECCode) (ow p : Nat) (h : L ≤ L') :
    (estimateWith (reactionLimitedModel L factory) hw w c ow p).time_us_tenths
      ≤ (estimateWith (reactionLimitedModel L' factory) hw w c ow p).time_us_tenths := by
  rw [reactionLimited_time, reactionLimited_time]
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) h) (Nat.le_refl _)

/-! ## §2. Sensitivity: RSA-2048 runtime as a function of the decode latency

    2.7×10⁹ Toffolis, 1 µs cycle (10 tenths-µs); decode latency in code cycles. -/

/-- RSA-2048 verified runtime (tenths-µs) at decode latency `L` cycles. -/
def rsa2048_runtime (L : Nat) : Nat := 2_700_000_000 * L * 10

theorem rsa2048_runtime_eq (L : Nat) :
    (estimateWith (reactionLimitedModel L 0) { cycle_time_us_tenths := 10 }
        (shorWorkload 2_700_000_000 6200) (surfaceCodeD 27) 0 0).time_us_tenths
      = rsa2048_runtime L := by
  rw [reactionLimited_time]; rfl

/-- 10 µs decoder ⇒ 7.5 h (= 270×10⁹ tenths-µs). -/
theorem rsa2048_at_10 : rsa2048_runtime 10 = 270_000_000_000 := by decide
/-- 20 µs decoder ⇒ 15 h — DOUBLING the decode latency DOUBLES the runtime. -/
theorem rsa2048_at_20 : rsa2048_runtime 20 = 540_000_000_000 := by decide
/-- Decode latency = d = 27 cycles ⇒ 20.25 h — reaction-limited meets the d-cycle
    ceiling (the crossover: a decoder this slow gives no pipelining benefit). -/
theorem rsa2048_at_27 : rsa2048_runtime 27 = 729_000_000_000 := by decide
/-- 40 µs decoder ⇒ 30 h — past the crossover the decoder DOMINATES the runtime. -/
theorem rsa2048_at_40 : rsa2048_runtime 40 = 1_080_000_000_000 := by decide

/-- The crossover is at latency = code distance: there the verified reaction-limited
    runtime equals the d-cycle ceiling (`ReactionLimitedRuntime.rsa2048_dcycle`). -/
theorem crossover_at_distance :
    rsa2048_runtime 27 = ReactionLimitedRuntime.dCycleRuntime 2_700_000_000 27 10 := by decide

/-! ## §3. COUPLING — the same decode-latency input also scales the decoder lanes

    Increasing the decode latency increases BOTH the runtime (×n_toff, §2) AND
    the decoder LANE requirement (patches·latency, `DecoderBacklogModel`).  A
    slower decoder costs time AND classical hardware. -/

open FormalRV.System.DecoderBacklogModel in
/-- At 10 µs: runtime 7.5 h AND 62 000 decode lanes. -/
theorem coupling_10 :
    rsa2048_runtime 10 = 270_000_000_000
    ∧ arrivalsPerWindow 6200 10 = 62_000 := by decide

open FormalRV.System.DecoderBacklogModel in
/-- At 20 µs: runtime 15 h AND 124 000 lanes — doubling the latency doubles BOTH. -/
theorem coupling_20 :
    rsa2048_runtime 20 = 540_000_000_000
    ∧ arrivalsPerWindow 6200 20 = 124_000 := by decide

open FormalRV.System.DecoderBacklogModel in
/-- The two linear effects packaged parametrically.  DEFINITIONAL content: this
    is just the conjunction of `reactionLimited_time` with the unfolding of
    `arrivalsPerWindow` — for any decode latency `L` and patch count `p`, the
    runtime is `n_toff·L·cycle` and the backlog-free lane threshold is `p·L`. -/
theorem decode_latency_drives_time_and_lanes
    (L p factory : Nat) (hw : Hardware) (w : Workload) (c : QECCode) (ow pp : Nat) :
    (estimateWith (reactionLimitedModel L factory) hw w c ow pp).time_us_tenths
        = w.n_toff * L * hw.cycle_time_us_tenths
    ∧ arrivalsPerWindow p L = p * L := by
  exact ⟨reactionLimited_time L factory hw w c ow pp, rfl⟩

end FormalRV.System.DecodeLatencySensitivity
