/-
  FormalRV.Shor.CFS.ShortDLPPeakLaw — STEP A: the TWO-REGISTER short-discrete-log QPE
  measurement distribution and its per-good-pair probability lower bound.

  ## What STEP A is and why it factorizes

  Ekerå–Håstad short-DLP factoring (1702.00249; the 8-hours paper's quantum core) runs a
  TWO-register QPE: two precision registers (`m`- and `ℓ`-bit), each estimating one phase of a
  joint eigenstate of the short-DLP oracle `x ↦ g^x`.  The post-measurement distribution is the
  two-dimensional analogue of order finding's QPE peak.

  The KEY structural insight (App A.2.1): the joint phase register decouples into a TENSOR PRODUCT,
  so the 2-D amplitude is the PRODUCT of two independent 1-register amplitudes, and the 2-D
  Dirichlet kernel is a product of two 1-D Dirichlet kernels.  This file makes that precise and
  proves everything DOWNSTREAM of the one carried structural bridge, axiom-clean:

    1. `qpe_amp_2d` / `qpe_prob_2d` — the 2-register amplitude and Born probability, DEFINED as the
       product of the proven 1-register `qpe_amp` / `qpe_prob` (`FormalRV.Framework.QPEAmplitude`).
    2. `qpe_prob_2d_factorizes` — the factorization law `qpe_prob_2d = qpe_prob · qpe_prob`, proven
       from `Complex.normSq_mul`.  (This is the whole point of the tensor decoupling.)
    3. `qpe_prob_2d_peak_bound` — the per-pair conditional bound `≥ (4/π²)²`, REUSING the proven
       1-register Dirichlet peak bound `qpe_prob_peak_bound` TWICE (once per register), via the
       factorization.  No re-derivation of the Dirichlet kernel.
    4. `short_dlp_measurement_dist` — the concrete two-index measurement distribution.
    5. `short_dlp_prob_bound_of_phase_bounds` — the paper's per-good-pair floor `≥ 2^{-(m+ℓ+2)}`
       (1702.00249 Lemma 7, downstream half), obtained from the `(4/π²)²` product bound + the numeric
       comparison `2^{-(m+ℓ+2)} ≤ (4/π²)²` (for `m+ℓ ≥ 1`), GIVEN the two per-register phase bounds.

  ## Honest scope / the ONE remaining obligation (documented, not faked, not a decorative hypothesis)

  The genuinely-quantum step that is NOT proven here is the **residue-to-phase bridge**: turning the
  good-pair balanced-residue condition `EHGoodPair m ℓ d j k` (a single bound on the *joint* residue
  `{dj + 2^m k}_{2^(ℓ+m)}`) into the *two separate* per-register phase discrepancy bounds
  `|2^m·θ_j - j| ≤ 1/2` and `|2^ℓ·θ_k - k| ≤ 1/2`.  That is a lattice-geometry step
  (1702.00249 App A.2.1) requiring the short-DLP orbit-state eigendecomposition — the 2-D analogue of
  order finding's (now-discharged) `h_orbit_exists` / `qpe_phase_discrepancy_s_closest_le_half`.  We
  do NOT smuggle it in as an unused `EHGoodPair` hypothesis: `short_dlp_prob_bound_of_phase_bounds`
  takes ONLY the two phase bounds (the bridge's conclusion).  Everything downstream of the bridge —
  the product amplitude, the factorization, the double application of the proven peak bound, and the
  numeric `2^{-(m+ℓ+2)}` floor — is proven axiom-clean.  The bridge itself is the next target.
-/
import FormalRV.QPE.QPEAmplitude
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS

open FormalRV.Framework
open scoped BigOperators

/-! ## §1. The two-register QPE amplitude and probability (product form). -/

/-- **Two-register QPE amplitude.**  At measurement outcome `(j, k)` (first register `m`-bit, second
    register `ℓ`-bit) for the joint phase pair `θ = (θ_j, θ_k)`, the amplitude is the PRODUCT of the
    two independent 1-register ideal QPE amplitudes — the tensor-product decoupling of the joint
    phase register (1702.00249 App A.2.1).  This is the precise sense in which the 2-D Dirichlet
    kernel is a product of 1-D kernels. -/
noncomputable def qpe_amp_2d (m ℓ j k : Nat) (θ : ℝ × ℝ) : ℂ :=
  qpe_amp m j θ.1 * qpe_amp ℓ k θ.2

/-- **Two-register QPE outcome probability** `‖qpe_amp_2d‖²`. -/
noncomputable def qpe_prob_2d (m ℓ j k : Nat) (θ : ℝ × ℝ) : ℝ :=
  Complex.normSq (qpe_amp_2d m ℓ j k θ)

/-- The 2-register outcome probability is non-negative. -/
theorem qpe_prob_2d_nonneg (m ℓ j k : Nat) (θ : ℝ × ℝ) : 0 ≤ qpe_prob_2d m ℓ j k θ :=
  Complex.normSq_nonneg _

/-- **Factorization law (the key STEP A structural fact).**  The 2-register probability is the
    PRODUCT of the two 1-register probabilities — the modulus of a product is the product of the
    moduli (`Complex.normSq_mul`).  This is what makes the 2-D peak analysis reduce to TWO 1-D
    applications of the already-proven Dirichlet-kernel bound. -/
theorem qpe_prob_2d_factorizes (m ℓ j k : Nat) (θ : ℝ × ℝ) :
    qpe_prob_2d m ℓ j k θ = qpe_prob m j θ.1 * qpe_prob ℓ k θ.2 := by
  unfold qpe_prob_2d qpe_amp_2d qpe_prob
  rw [Complex.normSq_mul]

/-! ## §2. The per-good-pair peak bound: REUSE the 1-register Dirichlet peak bound twice. -/

/-- **Two-register peak bound from two independent phase bounds (the `(4/π²)²` floor).**  If each
    register's phase discrepancy is at most `1/2` (`|2^m·θ_j - j| ≤ 1/2`, `|2^ℓ·θ_k - k| ≤ 1/2`),
    then the 2-register outcome probability at `(j, k)` is at least `(4/π²)²`.

    PROVEN by REUSE: factorize via `qpe_prob_2d_factorizes`, then apply the proven 1-register
    `qpe_prob_peak_bound` to EACH factor.  No new Dirichlet-kernel analysis. -/
theorem qpe_prob_2d_peak_bound (m ℓ j k : Nat) (θ : ℝ × ℝ)
    (hj : |qpe_phase_discrepancy m j θ.1| ≤ 1 / 2)
    (hk : |qpe_phase_discrepancy ℓ k θ.2| ≤ 1 / 2) :
    qpe_prob_2d m ℓ j k θ ≥ (4 / Real.pi ^ 2) ^ 2 := by
  rw [qpe_prob_2d_factorizes]
  have hbj : qpe_prob m j θ.1 ≥ 4 / Real.pi ^ 2 := qpe_prob_peak_bound m j θ.1 hj
  have hbk : qpe_prob ℓ k θ.2 ≥ 4 / Real.pi ^ 2 := qpe_prob_peak_bound ℓ k θ.2 hk
  have hpos : (0 : ℝ) ≤ 4 / Real.pi ^ 2 := by positivity
  calc (4 / Real.pi ^ 2) ^ 2
      = (4 / Real.pi ^ 2) * (4 / Real.pi ^ 2) := by ring
    _ ≤ qpe_prob m j θ.1 * qpe_prob ℓ k θ.2 :=
        mul_le_mul hbj hbk hpos (le_trans hpos hbj)

/-! ## §3. The numeric floor `2^{-(m+ℓ+2)} ≤ (4/π²)²` (for `m+ℓ ≥ 1`). -/

/-- **`(4/π²)² ≥ 1/8`.**  Since `π < 3.15` (`Real.pi_lt_d2`), `π² < 10`, so `4/π² > 2/5`, hence
    `(4/π²)² > (2/5)² = 4/25 > 1/8`.  (Note `(4/π²)² ≈ 0.164 > 0.125 = 1/8`.) -/
theorem peak_sq_ge_eighth : (1 : ℝ) / 8 ≤ (4 / Real.pi ^ 2) ^ 2 := by
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_pi_sq_pos : (0 : ℝ) < Real.pi ^ 2 := pow_pos h_pi_pos 2
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have h_pi_sq_lt : Real.pi ^ 2 < 10 := by nlinarith [h_pi_pos, h_pi_lt]
  have h4 : (2 : ℝ) / 5 ≤ 4 / Real.pi ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num) h_pi_sq_pos]
    nlinarith [h_pi_sq_lt]
  calc (1 : ℝ) / 8 ≤ (2 / 5) ^ 2 := by norm_num
    _ ≤ (4 / Real.pi ^ 2) ^ 2 := pow_le_pow_left₀ (by norm_num) h4 2

/-- **`2^{-(m+ℓ+2)} ≤ 1/8` for `m+ℓ ≥ 1`.**  The exponent `m+ℓ+2 ≥ 3`, so the power is at most
    `2^{-3} = 1/8`. -/
theorem two_pow_neg_le_eighth (m ℓ : Nat) (h : 1 ≤ m + ℓ) :
    (2 : ℝ) ^ (-(m + ℓ + 2 : ℤ)) ≤ 1 / 8 := by
  have hstep : (2 : ℝ) ^ (-(m + ℓ + 2 : ℤ)) ≤ (2 : ℝ) ^ (-3 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hval : (2 : ℝ) ^ (-3 : ℤ) = 1 / 8 := by norm_num
  linarith [hval ▸ hstep]

/-- **The paper's `2^{-(m+ℓ+2)}` floor is below the proven product peak bound `(4/π²)²`**
    (for `m+ℓ ≥ 1`).  1702.00249 Lemma 7 states the simpler conservative floor `2^{-(m+ℓ+2)}`; the
    product Dirichlet bound we prove is the strictly stronger `(4/π²)²`. -/
theorem two_pow_neg_le_peak_sq (m ℓ : Nat) (h : 1 ≤ m + ℓ) :
    (2 : ℝ) ^ (-(m + ℓ + 2 : ℤ)) ≤ (4 / Real.pi ^ 2) ^ 2 :=
  le_trans (two_pow_neg_le_eighth m ℓ h) peak_sq_ge_eighth

/-! ## §4. The concrete two-register measurement distribution. -/

/-- **The concrete two-register short-DLP measurement distribution.**  Indexed by the pair of
    outcomes `(j, k)` (one per precision register), with the per-register true phases supplied by
    `x_reg`/`y_reg` (the phase numerators for outcome `(j,k)`); the probability is the product of
    the two 1-register Born probabilities.  This matches the paper's algorithm outline: the joint
    distribution is a product over the two decoupled precision registers. -/
noncomputable def short_dlp_measurement_dist (m ℓ : Nat) (x_reg y_reg : Nat → Nat → ℝ) :
    Nat → Nat → ℝ :=
  fun j k => qpe_prob m j (x_reg j k / 2 ^ m) * qpe_prob ℓ k (y_reg j k / 2 ^ ℓ)

/-- The measurement distribution agrees with `qpe_prob_2d` at the per-outcome phases. -/
theorem short_dlp_measurement_dist_eq_qpe_prob_2d (m ℓ : Nat) (x_reg y_reg : Nat → Nat → ℝ)
    (j k : Nat) :
    short_dlp_measurement_dist m ℓ x_reg y_reg j k
      = qpe_prob_2d m ℓ j k (x_reg j k / 2 ^ m, y_reg j k / 2 ^ ℓ) := by
  unfold short_dlp_measurement_dist
  rw [qpe_prob_2d_factorizes]

/-- The measurement distribution is non-negative. -/
theorem short_dlp_measurement_dist_nonneg (m ℓ : Nat) (x_reg y_reg : Nat → Nat → ℝ) (j k : Nat) :
    0 ≤ short_dlp_measurement_dist m ℓ x_reg y_reg j k := by
  rw [short_dlp_measurement_dist_eq_qpe_prob_2d]
  exact qpe_prob_2d_nonneg _ _ _ _ _

/-! ## §5. The probability floor GIVEN the per-register phase bounds.

    This proves the downstream half of 1702.00249 Lemma 7: GIVEN that each register's phase
    discrepancy is `≤ 1/2`, the two-register probability is `≥ 2^{-(m+ℓ+2)}`.

    The GENUINE Lemma-7 content not proven here is the **residue-to-phase bridge** — that a good pair
    `EHGoodPair m ℓ d j k` (one bound on the JOINT residue `{dj+2^m k}_{2^(ℓ+m)}`) implies the TWO
    separate per-register phase bounds.  That is a lattice-geometry step requiring the short-DLP
    orbit-state eigendecomposition (the 2-register analogue of order finding's now-discharged
    `h_orbit_exists` / `qpe_phase_discrepancy_s_closest_le_half`).  It is deliberately NOT stated as a
    decorative unused hypothesis here; it is the next target (see the module header / NARROWING doc).
    Everything below is proven axiom-clean, with NO hidden good-pair hypothesis. -/

/-- **The two-register probability floor `≥ 2^{-(m+ℓ+2)}` from the per-register phase bounds.**
    REUSES the proven 1-register Dirichlet peak bound twice (`qpe_prob_2d_peak_bound`) + the numeric
    comparison (`two_pow_neg_le_peak_sq`).  No hidden hypotheses: the only inputs are the two phase
    discrepancy bounds (the conclusion of the unbuilt residue-to-phase bridge). -/
theorem short_dlp_prob_bound_of_phase_bounds (m ℓ : Nat) (x_reg y_reg : Nat → Nat → ℝ)
    (j k : Nat) (hℓm : 1 ≤ m + ℓ)
    (phase_bounds :
        |qpe_phase_discrepancy m j (x_reg j k / 2 ^ m)| ≤ 1 / 2 ∧
        |qpe_phase_discrepancy ℓ k (y_reg j k / 2 ^ ℓ)| ≤ 1 / 2) :
    short_dlp_measurement_dist m ℓ x_reg y_reg j k ≥ (2 : ℝ) ^ (-(m + ℓ + 2 : ℤ)) := by
  rw [short_dlp_measurement_dist_eq_qpe_prob_2d]
  obtain ⟨hbj, hbk⟩ := phase_bounds
  have hpeak : qpe_prob_2d m ℓ j k (x_reg j k / 2 ^ m, y_reg j k / 2 ^ ℓ) ≥ (4 / Real.pi ^ 2) ^ 2 :=
    qpe_prob_2d_peak_bound m ℓ j k (x_reg j k / 2 ^ m, y_reg j k / 2 ^ ℓ) hbj hbk
  exact le_trans (two_pow_neg_le_peak_sq m ℓ hℓm) hpeak

/-! ## The STEP A results pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean qpe_prob_2d_factorizes
#verify_clean qpe_prob_2d_peak_bound
#verify_clean peak_sq_ge_eighth
#verify_clean two_pow_neg_le_eighth
#verify_clean two_pow_neg_le_peak_sq
#verify_clean short_dlp_measurement_dist_eq_qpe_prob_2d
#verify_clean short_dlp_measurement_dist_nonneg
#verify_clean short_dlp_prob_bound_of_phase_bounds

end FormalRV.CFS
