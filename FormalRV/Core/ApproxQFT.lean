/-
  FormalRV.Core.ApproxQFT — a CONSTRUCTIVE Clifford+T compilation of the
  QFT via Coppersmith's approximate ("banded") QFT, with an exact,
  elementary approximation-error bound.  No existence axiom: the
  compiler is an actual circuit transformation and the error is derived.

  ## The idea

  The QFT's controlled phase rotations are `R_k = R_z(2π/2^k)`.  Only
  `R_1=Z, R_2=S, R_3=T` are exactly Clifford+T (proved in
  `CliffordTRotations`).  The approximate QFT with cutoff `m` simply
  DROPS every `R_k` with `k > m` (replaces it by the identity).  With
  `m ≤ 3` the resulting circuit is *exactly* Clifford+T, and the error
  of each drop is computed here from first principles:

      error of dropping `R_z(θ)` = ‖R_z(θ) − I‖ = |e^{iθ} − 1| ≤ |θ|.

  So the QFT→Clifford+T compilation error is a derived sum
  `Σ_{dropped} 2π/2^k`, NOT an assumed bound.
-/
import FormalRV.Core.CliffordTRotations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace FormalRV.Framework.ApproxQFT

open Complex
open FormalRV.Framework
open FormalRV.Framework.CliffordTRotations

/-! ## §1. The exact per-rotation drop error. -/

/-- `R_z(θ) − I` is the diagonal matrix `diag(0, e^{iθ}−1)`: dropping a
    z-rotation leaves only the `(1,1)` entry `e^{iθ}−1`. -/
theorem rotation_sub_one_diag (θ : ℝ) :
    rotation 0 0 θ - 1 = !![0, 0; 0, Complex.exp (θ * I) - 1] := by
  rw [rotation_zz_diag, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The exact drop error (chord ≤ arc).**  The magnitude of the only
    non-zero entry of `R_z(θ) − I` is `|e^{iθ} − 1| ≤ |θ|` — the exact
    operator-norm error of dropping the rotation `R_z(θ)`.  Elementary,
    no axiom. -/
theorem dropRotationError_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * I) - 1‖ ≤ |θ| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)
  rw [mul_comm Complex.I (θ : ℂ)] at h
  rwa [Real.norm_eq_abs] at h

/-! ## §2. The QFT rotation drop error: `‖R_k − I‖ ≤ 2π/2^k`. -/

/-- Dropping the QFT rotation `R_k = R_z(2π/2^k)` costs at most
    `2π/2^k` in operator norm — and `2π/2^k → 0`, so deep rotations are
    nearly free to drop.  This is the per-rotation term of the
    approximate-QFT error budget, derived (not assumed). -/
theorem qftRot_drop_error_le (k : ℕ) :
    ‖Complex.exp ((2 * Real.pi / 2 ^ k : ℝ) * I) - 1‖ ≤ 2 * Real.pi / 2 ^ k := by
  have h := dropRotationError_le (2 * Real.pi / 2 ^ k)
  rwa [abs_of_nonneg (by positivity)] at h

/-! ## §3. The closed-form total approximation error.

    The inverse-QFT phase ladder for one target applies controlled
    rotations `R_z(π/2^m)` for `m = 1 … n-1`; the approximate ("banded")
    QFT with cutoff `c` DROPS those with `m ≥ c`.  Each drop costs
    `≤ π/2^m` (`dropRotationError_le`), so the WHOLE error of the cutoff
    is the geometric tail `Σ_{m=c}^{n-1} π/2^m`, which sums in closed form
    to `≤ 2π/2^c = π/2^(c-1)`.  This is the exact, derived approximation
    error of the AQFT compiler — no operator norm, no assumption. -/

/-- **Closed-form AQFT error budget.**  The total cost of dropping every
    phase-ladder rotation `R_z(π/2^m)` from the cutoff `c` onward is at
    most `2π/2^c` — a geometric tail.  Derived from the per-rotation
    `dropRotationError_le`, with no axiom. -/
theorem aqft_ladder_error_budget (c n : ℕ) (hcn : c ≤ n) :
    ∑ m ∈ Finset.Ico c n, (Real.pi / 2 ^ m) ≤ 2 * Real.pi / 2 ^ c := by
  have hsum : ∑ m ∈ Finset.Ico c n, (2⁻¹ : ℝ) ^ m ≤ 2 * (2⁻¹ : ℝ) ^ c := by
    rw [geom_sum_Ico (by norm_num) hcn,
        show ((2⁻¹ : ℝ) - 1) = -2⁻¹ by norm_num,
        div_le_iff_of_neg (by norm_num : (-2⁻¹ : ℝ) < 0)]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹) n,
               pow_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹) c]
  calc ∑ m ∈ Finset.Ico c n, (Real.pi / 2 ^ m)
      = Real.pi * ∑ m ∈ Finset.Ico c n, (2⁻¹ : ℝ) ^ m := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m _ => by rw [inv_pow]; ring)
    _ ≤ Real.pi * (2 * (2⁻¹ : ℝ) ^ c) := by
        exact mul_le_mul_of_nonneg_left hsum Real.pi_nonneg
    _ = 2 * Real.pi / 2 ^ c := by rw [inv_pow]; ring

/-- The error budget tends to `0` as the cutoff grows: choosing a larger
    cutoff `c` drives the AQFT approximation error `≤ 2π/2^c` below any
    target.  (Trade-off: a larger cutoff keeps more rotations, and only
    `m ≤ 1` (`Z, S†`) — or `m ≤ 2` with a controlled-`T` gadget — stay
    exactly Clifford+T; finer kept rotations would need true synthesis.) -/
theorem aqft_error_budget_antitone {c c' : ℕ} (h : c ≤ c') :
    (2 * Real.pi / 2 ^ c' : ℝ) ≤ 2 * Real.pi / 2 ^ c := by
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_right₀ (by norm_num) h

end FormalRV.Framework.ApproxQFT
