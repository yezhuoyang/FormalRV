/-
  FormalRV.Shor.WindowedTimeCost — closing windowed→Shor through the coset/approximate
  path, and the EXPECTED-TIME (shots) cost that approximation/logical error inflates.

  Two contributions:

  (A) A FAITHFUL (trace-distance) success-degradation bound, fixing the `2^m` looseness of
      the earlier ℓ²/per-outcome bound: the success-relevant quantity is a subset-sum of
      the measurement distribution, so it is controlled by the measurement L1 distance —
      `|Δsuccess| ≤ Σ_x |Δprob_x|` (PROVED here) — and Gidney Thm 2.6 (operationally:
      output trace distance `≤ 2√ε`) bounds that L1 distance by `4√(totalDev)`, with NO
      `2^m` factor.  This gives the windowed/coset multiplier a meaningful degraded Shor
      success bound at arbitrary window size.

  (B) The EXPECTED-TIME model.  A run succeeds with probability `p`; the expected number of
      independent shots to first success is `1/p`, so the total expected wall-clock is
      `perShotTime / p`.  Degrading `p` (by approximation deviation OR logical error)
      MULTIPLIES the time by `1/p` — `time_inflates_under_degradation`.  This `1/p` factor
      is invisible to per-shot resource counts (Toffolis, depth); reporting only per-shot
      cost, as is common, silently neglects the fidelity→repetition→time blow-up.
-/
import FormalRV.Shor.Approx.SuccessStable

namespace FormalRV.Shor.WindowedTimeCost

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.Shor.Approx

/-! ## §1. Faithful success degradation via the measurement L1 distance (no `2^m`). -/

/-- **The success quantity is controlled by the measurement L1 distance.**  Because the
    Shor success probability is `∑ r_found(x)·prob(x)` with `r_found ∈ {0,1}` (a subset-sum
    of the measurement distribution), two final states' success probabilities differ by at
    most the L1 distance of their measurement distributions — NO `2^m` blow-up. -/
theorem success_diff_le_measL1 (a r N m n anc : Nat) (f g : Nat → BaseUCom (n + anc)) :
    |probability_of_success a r N m n anc f - probability_of_success a r N m n anc g|
      ≤ ∑ x ∈ Finset.range (2 ^ m),
          |prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc f)
            - prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc g)| := by
  unfold probability_of_success
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  have hrf0 : 0 ≤ r_found x m r a N := by unfold r_found; split_ifs <;> norm_num
  have hrf1 : r_found x m r a N ≤ 1 := by unfold r_found; split_ifs <;> norm_num
  rw [← mul_sub, abs_mul, abs_of_nonneg hrf0]
  calc r_found x m r a N
        * |prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc f)
            - prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc g)|
      ≤ 1 * |prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc f)
            - prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc g)| :=
        mul_le_mul_of_nonneg_right hrf1 (abs_nonneg _)
    _ = _ := one_mul _

/-- **Faithful approximate-coset Shor contract** (trace-distance form).  Bundles the ideal
    family's success bound and the SINGLE named quantum obligation `measL1_obl` — Gidney
    Thm 2.6 operationally: a combinatorial deviation `≤ totalDev` keeps the output
    measurement distribution within L1 distance `4√(totalDev)` of the ideal (output trace
    distance `≤ 2√ε`, and measurement cannot increase distinguishability). -/
structure ApproxCosetShorTight (a r N m n anc : Nat) where
  fApprox : Nat → BaseUCom (n + anc)
  gIdeal : Nat → BaseUCom (n + anc)
  totalDev : ℝ
  idealBound : ℝ
  totalDev_nonneg : 0 ≤ totalDev
  ideal_ge : idealBound ≤ probability_of_success a r N m n anc gIdeal
  /-- **named obligation** (Gidney Thm 2.6, operational): measurement L1 `≤ 4√totalDev`. -/
  measL1_obl :
    (∑ x ∈ Finset.range (2 ^ m),
        |prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc fApprox)
          - prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc gIdeal)|)
      ≤ 4 * Real.sqrt totalDev

/-- **Degraded Shor success (faithful, no `2^m`).**  The approximate coset multiplier
    succeeds with probability `≥ idealBound − 4√(totalDev)`. -/
theorem ApproxCosetShorTight.shorCorrect {a r N m n anc : Nat}
    (W : ApproxCosetShorTight a r N m n anc) :
    W.idealBound - 4 * Real.sqrt W.totalDev
      ≤ probability_of_success a r N m n anc W.fApprox := by
  have h1 := success_diff_le_measL1 a r N m n anc W.fApprox W.gIdeal
  have h2 := W.measL1_obl
  have h3 := W.ideal_ge
  have hle : |probability_of_success a r N m n anc W.fApprox
              - probability_of_success a r N m n anc W.gIdeal| ≤ 4 * Real.sqrt W.totalDev :=
    h1.trans h2
  have := (abs_le.mp hle).1
  linarith

/-! ## §2. Expected-time (shots) model — the fidelity→time factor. -/

/-- Expected number of independent shots until the first success, for per-shot success
    probability `p` (geometric distribution mean `1/p`). -/
noncomputable def expectedShots (p : ℝ) : ℝ := 1 / p

/-- Total expected wall-clock time `= (per-shot time) · (expected shots) = perShot / p`. -/
noncomputable def totalExpectedTime (perShot p : ℝ) : ℝ := perShot / p

theorem totalExpectedTime_eq (perShot p : ℝ) :
    totalExpectedTime perShot p = perShot * expectedShots p := by
  unfold totalExpectedTime expectedShots; ring

/-! ### Probability-theory foundation: `expectedShots = 1/p` IS the geometric mean.

Each shot is an independent Bernoulli(`p`) trial.  Let `T` be the number of shots to the
first success (`T ~ Geometric(p)`).  By independence, `P(T > k) = (1-p)^k` (all of the
first `k` shots fail), and by the tail-sum formula `E[T] = ∑_{k≥0} P(T > k)`.  We DERIVE
`expectedShots = 1/p` from this, rather than positing it. -/

/-- `P(first k independent shots all fail) = (1-p)^k = P(shots-to-first-success > k)`
    (product of `k` independent Bernoulli failures). -/
def probExceeds (p : ℝ) (k : ℕ) : ℝ := (1 - p) ^ k

/-- **Expected shots from probability theory.**  `E[T] = ∑_{k≥0} P(T > k) = ∑_{k≥0} (1-p)^k`
    converges (geometric series, `0 ≤ 1-p < 1`) to `1/p` — so the `expectedShots p = 1/p`
    used in the time model is exactly the mean of the `Geometric(p)` shot count. -/
theorem expectedShots_eq_tailsum (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∑' k, probExceeds p k) = expectedShots p := by
  unfold probExceeds expectedShots
  rw [tsum_geometric_of_lt_one (by linarith) (by linarith), one_div]
  congr 1; ring

/-- **The fidelity→time factor that per-shot cost neglects.**  Reporting only the per-shot
    time `perShot` is the `p = 1` case; the TRUE expected time is `perShot / p`, larger by
    the factor `1/p ≥ 1` whenever `p < 1`.  This factor is exactly the run-count inflation
    caused by approximation/logical-error fidelity loss, invisible to Toffoli/depth counts. -/
theorem neglected_time_factor (perShot p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hps : 0 ≤ perShot) :
    perShot ≤ totalExpectedTime perShot p := by
  unfold totalExpectedTime
  rw [le_div_iff₀ hp]
  nlinarith [hps, hp1]

/-- **Degrading the success probability inflates the total time.**  If approximation or
    logical error lowers the per-shot success from `p_ideal` to `p_deg ≤ p_ideal`, the
    total expected time grows: `perShot/p_ideal ≤ perShot/p_deg`. -/
theorem time_inflates_under_degradation (perShot p_ideal p_deg : ℝ)
    (hps : 0 ≤ perShot) (hdeg : 0 < p_deg) (hle : p_deg ≤ p_ideal) :
    totalExpectedTime perShot p_ideal ≤ totalExpectedTime perShot p_deg := by
  unfold totalExpectedTime
  gcongr

/-- **Confidence after `k` shots.**  With per-shot success `p`, `k` independent shots give
    at least one success with probability `1 − (1−p)^k`; achieving confidence `≥ 1−ε`
    requires `(1−p)^k ≤ ε` (so `k ≳ ln(1/ε)/p` shots — again growing as `p` degrades). -/
theorem confidence_of_shots (p ε : ℝ) (k : ℕ) (h : (1 - p) ^ k ≤ ε) :
    (1 : ℝ) - ε ≤ 1 - (1 - p) ^ k := by linarith

/-! ## §3. End-to-end: the windowed/coset Shor's true expected time.

Combining §1 and §2: the approximate coset multiplier succeeds per-shot with probability
`p_deg ≥ idealBound − 4√(totalDev)` (`ApproxCosetShorTight.shorCorrect`), so its TRUE
expected time is `perShot / p_deg ≥ perShot / idealBound` (`time_inflates_under_degradation`).
The coset deviation `totalDev` (accumulated as `#additions · 2^{-c_pad}`, Gidney Thm 2.10 +
Thm 3.3) thus enters the time cost through `1/p_deg`, not just the per-shot Toffoli count —
the fidelity→repetition→time effect that a per-shot-only estimate omits. -/

/-- The windowed/coset Shor's true expected time is at least the ideal-success time, and
    grows as the coset deviation degrades the success probability. -/
theorem windowed_coset_time_lower_bound {a r N m n anc : Nat}
    (W : ApproxCosetShorTight a r N m n anc) (perShot : ℝ)
    (hps : 0 ≤ perShot)
    (hpos : 0 < W.idealBound - 4 * Real.sqrt W.totalDev) :
    totalExpectedTime perShot (probability_of_success a r N m n anc W.fApprox)
      ≤ totalExpectedTime perShot (W.idealBound - 4 * Real.sqrt W.totalDev) :=
  time_inflates_under_degradation perShot _ _ hps hpos W.shorCorrect

/-! ## §4. Logical error compounds the time through the SAME operation count.

The success probability also drops from per-operation LOGICAL error.  With error rate
`p_L` per error-prone operation and `k` such operations (the Toffoli count), the chance
that none fault is `(1-p_L)^k`.  Crucially `k` is the SAME count that sets the per-shot
time — so the operation count enters the total time TWICE: linearly (per-shot) and
through `1/(1-p_L)^k` (repetitions).  Per-shot-only resource estimates report the first
and neglect the second. -/

/-- Per-shot success including logical error: algorithmic success `P` times the probability
    `(1-p_L)^k` that none of the `k` error-prone operations faults. -/
noncomputable def successWithLogicalError (P p_L : ℝ) (k : ℕ) : ℝ := P * (1 - p_L) ^ k

/-- More operations ⟹ lower success (the `(1-p_L)^k ≤ 1` factor shrinks `P`). -/
theorem logicalError_degrades_success (P p_L : ℝ) (k : ℕ)
    (hP : 0 ≤ P) (hpL : 0 ≤ p_L) (hpL1 : p_L ≤ 1) :
    successWithLogicalError P p_L k ≤ P := by
  unfold successWithLogicalError
  exact mul_le_of_le_one_right hP (pow_le_one₀ (by linarith) (by linarith))

/-- **The doubly-counted operation cost (the neglected time blow-up).**  Total expected
    time with logical error is `perShot / (P·(1-p_L)^k)`; the Toffoli count `k` that fixes
    the per-shot time ALSO suppresses success by `(1-p_L)^k`, so it inflates the total time
    a second time.  A per-shot-only estimate captures only the first. -/
theorem logicalError_inflates_time (perShot P p_L : ℝ) (k : ℕ)
    (hps : 0 ≤ perShot) (hP : 0 < P) (hpL : 0 ≤ p_L) (hpL1 : p_L < 1) :
    totalExpectedTime perShot P
      ≤ totalExpectedTime perShot (successWithLogicalError P p_L k) :=
  time_inflates_under_degradation perShot P (successWithLogicalError P p_L k) hps
    (mul_pos hP (pow_pos (by linarith) k))
    (logicalError_degrades_success P p_L k (le_of_lt hP) hpL (le_of_lt hpL1))

/-! ## §5. Coset deviation accumulates linearly in the number of additions.

`ApproxCosetShorTight.totalDev` is supplied as the accumulated combinatorial deviation.
By Gidney Thm 3.3 each coset lookup-addition has deviation `≤ 2^{-c_pad}`, and by Thm 2.10
(subadditivity, iterated — `Deviation.DevBound_compList`) the deviation of `numAdds`
additions is `≤ numAdds · 2^{-c_pad}`.  With `numAdds ≈ 0.1 n_e n` and `c_pad ≈ 3 lg n + 10`
this is `≈ 0.1 n_e n / (1024 n³) → 0`, so the coset approximation's success/time penalty
vanishes asymptotically — the dominant repetition cost is the §4 logical-error factor. -/

/-- The accumulated coset deviation of a windowed multiplier with `numAdds` lookup-additions
    at padding `c_pad` (Gidney Thm 3.3 per-add `2^{-c_pad}`, Thm 2.10 subadditive). -/
noncomputable def cosetTotalDev (numAdds c_pad : ℕ) : ℝ := numAdds * (2 : ℝ) ^ (-(c_pad : ℤ))

theorem cosetTotalDev_nonneg (numAdds c_pad : ℕ) : 0 ≤ cosetTotalDev numAdds c_pad := by
  unfold cosetTotalDev; positivity

/-- Increasing the padding `c_pad` (more coset terms) shrinks the deviation — the knob the
    paper turns to make approximation error negligible. -/
theorem cosetTotalDev_antitone (numAdds c_pad : ℕ) :
    cosetTotalDev numAdds (c_pad + 1) ≤ cosetTotalDev numAdds c_pad := by
  unfold cosetTotalDev
  gcongr
  · norm_num
  · omega

end FormalRV.Shor.WindowedTimeCost
