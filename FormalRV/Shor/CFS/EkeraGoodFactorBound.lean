/-
  FormalRV.Shor.CFS.EkeraGoodFactorBound — the C2 → Ekerå-good-factor connector.

  The transcribed Ekerå-2023 good factor `EkeraSuccess.ekeraGoodFactor τ`
  (`= max 0 (1 − 1/2^τ − 1/(2·2^{2τ}) − 1/(6·2^{3τ}))`) bakes in the Nemes rational majorant of the
  trigamma value `ψ'(2^τ)`.  This file connects it to the proven trigamma bound
  (`TrigammaBound.nemes_trigamma_bound`): the good factor is a valid lower bound on the genuine
  (clamped) Lemma-1 good-pair probability `max 0 (1 − ψ'(2^τ))`.

  ## Honest scope

  This is the C2-to-`good_obl` BRIDGE, modulo Ekerå 2023 Lemma 1 itself (that the true conditional
  good-pair probability is `≥ 1 − ψ'(2^τ)`).  Lemma 1 is a fact about the short-DLP MEASUREMENT
  DISTRIBUTION (the Fourier identity `condGood = 1 − ψ'`), which is NOT yet built — so this connector
  does NOT by itself discharge `EkeraDLPSuccess.good_obl`; it supplies the analytic half
  (`ekeraGoodFactor τ ≤ max 0 (1 − ψ'(2^τ))`) that Lemma 1 would compose with.  We do NOT inhabit the
  obligation structure with a cherry-picked `condGood` to feign a discharge.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CFS.EkeraSuccess
import FormalRV.Shor.CFS.TrigammaBound

namespace FormalRV.CFS

open scoped BigOperators

/-- **The Ekerå good factor is a lower bound on the clamped trigamma good-pair probability.**
    `ekeraGoodFactor τ ≤ max 0 (1 − ψ'(2^τ))`, via the proven Nemes bound
    `ψ'(2^τ) ≤ 1/2^τ + 1/(2·2^{2τ}) + 1/(6·2^{3τ})` (so `1 − [bracket] ≤ 1 − ψ'(2^τ)`).

    Both sides are `max 0`-clamped — necessarily: the un-clamped `ekeraGoodFactor τ ≤ 1 − ψ'(2^τ)` is
    FALSE at `τ = 0` (`ekeraGoodFactor 0 = 0` but `1 − ψ'(1) = 1 − π²/6 < 0`), which is exactly why
    Ekerå's factor and the true good-pair probability are both clamped at `0`.

    This is the genuine analytic content linking STEP C2 to `good_obl`; it still requires Ekerå-2023
    Lemma 1 (`condGood ≥ 1 − ψ'(2^τ)`, a measurement-distribution fact) to discharge the obligation. -/
theorem ekeraGoodFactor_le_clamped_trigamma (τ : ℕ) :
    ekeraGoodFactor τ ≤ max 0 (1 - FormalRV.CFS.Trigamma.trigamma ((2 : ℝ) ^ τ)) := by
  have htri : FormalRV.CFS.Trigamma.trigamma ((2 : ℝ) ^ τ) ≤
      1 / (2 : ℝ) ^ τ + 1 / (2 * (2 : ℝ) ^ (2 * τ)) + 1 / (6 * (2 : ℝ) ^ (3 * τ)) := by
    have hx : (0 : ℝ) < (2 : ℝ) ^ τ := by positivity
    have h := FormalRV.CFS.Trigamma.nemes_trigamma_bound ((2 : ℝ) ^ τ) hx
    have e2 : ((2 : ℝ) ^ τ) ^ 2 = (2 : ℝ) ^ (2 * τ) := by rw [← pow_mul]; ring_nf
    have e3 : ((2 : ℝ) ^ τ) ^ 3 = (2 : ℝ) ^ (3 * τ) := by rw [← pow_mul]; ring_nf
    rw [e2, e3] at h; exact h
  unfold ekeraGoodFactor
  apply max_le
  · exact le_max_left _ _
  · exact le_trans (by linarith [htri]) (le_max_right _ _)

#verify_clean ekeraGoodFactor_le_clamped_trigamma

end FormalRV.CFS
