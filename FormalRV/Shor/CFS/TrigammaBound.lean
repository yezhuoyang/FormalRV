/-
# The Nemes rational upper bound on the trigamma function (STEP C2)

This file discharges the **standalone analytic obligation C2** isolated in
`EKERA_OBLIGATIONS_NARROWING.md`: Mathlib has no polygamma/trigamma function, so the
trigamma value baked into `EkeraSuccess.ekeraGoodFactor` must be defined as the series
`ψ'(x) = ∑_{n ≥ 0} 1/(x+n)²` and the Nemes (2014) rational upper bound

  `ψ'(x) ≤ 1/x + 1/(2x²) + 1/(6x³)`   (for `x > 0`)

proved from scratch.  *Lit:* Nemes, "Generalization of the bounds on the psi/polygamma
functions" (2014); Ekerå 2023 (2309.01754) Claim `bound-trigamma`.

## The proof (elementary, exact constants — no integrals / Euler–Maclaurin needed)

The decisive observation is a **telescoping** identity.  Put

  `H y := 1/y + 1/(2y²) + 1/(6y³)`.

Then for every `y > 0` an exact algebraic identity holds:

  `H y - H (y+1) - 1/y² = 1 / (6 · y³ · (y+1)³)  ≥  0`,

so each summand is dominated termwise:

  `1/(x+n)²  ≤  H (x+n) - H (x+n+1)`.

The right-hand side telescopes (`H (x+n) → 0`), summing to `H x`.  Hence

  `ψ'(x) = ∑_{n≥0} 1/(x+n)²  ≤  ∑_{n≥0} (H (x+n) - H (x+n+1)) = H x
         = 1/x + 1/(2x²) + 1/(6x³).`

This gives the **tight** Nemes constants (`1/2`, `1/6`) — strictly sharper than the loose
integral-comparison bound `1/x + 1/x²` — and is valid for all `x > 0`, not merely `x ≥ 1`.
-/
import Mathlib

namespace FormalRV.CFS.Trigamma

open scoped BigOperators
open Filter Topology

/-- The trigamma function `ψ'(x) = ∑_{n ≥ 0} 1/(x+n)²`, defined as the real series. -/
noncomputable def trigamma (x : ℝ) : ℝ := ∑' n : ℕ, 1 / (x + n) ^ 2

/-- The Nemes rational majorant `H y = 1/y + 1/(2y²) + 1/(6y³)`.  It will turn out that
`trigamma x ≤ H x`, and `H x` is exactly the bound used in `EkeraSuccess.ekeraGoodFactor`. -/
noncomputable def nemesH (y : ℝ) : ℝ := 1 / y + 1 / (2 * y ^ 2) + 1 / (6 * y ^ 3)

/-- **The exact telescoping identity.**  For `y > 0`,
`H y - H (y+1) - 1/y² = 1 / (6 · y³ · (y+1)³)`. -/
theorem nemesH_telescope_identity (y : ℝ) (hy : 0 < y) :
    nemesH y - nemesH (y + 1) - 1 / y ^ 2 = 1 / (6 * y ^ 3 * (y + 1) ^ 3) := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hy1 : y + 1 ≠ 0 := by positivity
  unfold nemesH
  field_simp
  ring

/-- **Termwise domination.**  For `y > 0`, `1/y² ≤ H y - H (y+1)`. -/
theorem nemesH_telescope_ge (y : ℝ) (hy : 0 < y) :
    1 / y ^ 2 ≤ nemesH y - nemesH (y + 1) := by
  have hid := nemesH_telescope_identity y hy
  have hpos : 0 ≤ 1 / (6 * y ^ 3 * (y + 1) ^ 3) := by positivity
  linarith

/-- Each telescoping increment is nonnegative (needed for the nonneg-series criterion). -/
theorem nemesH_telescope_nonneg (y : ℝ) (hy : 0 < y) :
    0 ≤ nemesH y - nemesH (y + 1) := by
  have : (0:ℝ) ≤ 1 / y ^ 2 := by positivity
  exact le_trans this (nemesH_telescope_ge y hy)

/-- `H (x + n) → 0` as `n → ∞`, for `x > 0`. -/
theorem nemesH_tendsto_zero (x : ℝ) (_hx : 0 < x) :
    Tendsto (fun n : ℕ => nemesH (x + n)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop
  -- termwise limits
  have t1 : Tendsto (fun n : ℕ => 1 / (x + (n:ℝ))) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp hbase).congr (by intro n; simp [one_div])
  have t2 : Tendsto (fun n : ℕ => 1 / (2 * (x + (n:ℝ)) ^ 2)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n : ℕ => 2 * (x + (n:ℝ)) ^ 2) atTop atTop := by
      apply Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2)
      exact (hbase.atTop_mul_atTop₀ hbase).congr (by intro n; ring)
    exact (tendsto_inv_atTop_zero.comp hsq).congr (by intro n; simp [one_div])
  have t3 : Tendsto (fun n : ℕ => 1 / (6 * (x + (n:ℝ)) ^ 3)) atTop (𝓝 0) := by
    have hcube : Tendsto (fun n : ℕ => 6 * (x + (n:ℝ)) ^ 3) atTop atTop := by
      apply Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 6)
      have : Tendsto (fun n : ℕ => (x + (n:ℝ)) * (x + (n:ℝ)) * (x + (n:ℝ))) atTop atTop :=
        (hbase.atTop_mul_atTop₀ hbase).atTop_mul_atTop₀ hbase
      exact this.congr (by intro n; ring)
    exact (tendsto_inv_atTop_zero.comp hcube).congr (by intro n; simp [one_div])
  have hsum := (t1.add t2).add t3
  rw [show (0:ℝ) = 0 + 0 + 0 by ring]
  refine hsum.congr (by intro n; simp [nemesH])

/-- **The telescoping series sums to `H x`.**  For `x > 0`,
`HasSum (fun n => H (x+n) - H (x+n+1)) (H x)`. -/
theorem hasSum_nemesH_telescope (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => nemesH (x + (n:ℝ)) - nemesH (x + ((n:ℝ) + 1))) (nemesH x) := by
  set g : ℕ → ℝ := fun n => nemesH (x + n) with hg
  -- the telescoping term equals g n - g (n+1)
  have hterm : ∀ n : ℕ, nemesH (x + (n:ℝ)) - nemesH (x + ((n:ℝ) + 1)) = g n - g (n + 1) := by
    intro n
    simp only [hg]
    rw [show x + ((n:ℝ) + 1) = x + ((n + 1 : ℕ) : ℝ) by push_cast; ring]
  -- nonnegativity of each term
  have hnn : ∀ n : ℕ, 0 ≤ g n - g (n + 1) := by
    intro n
    have hxn : 0 < x + (n : ℝ) := by positivity
    have hnn0 := nemesH_telescope_nonneg (x + (n : ℝ)) hxn
    rw [show x + (n : ℝ) + 1 = x + ((n : ℝ) + 1) by ring] at hnn0
    rw [← hterm n]; exact hnn0
  -- partial sums telescope: ∑_{i<N} (g i - g (i+1)) = g 0 - g N
  have htel : ∀ N : ℕ, ∑ i ∈ Finset.range N, (g i - g (i + 1)) = g 0 - g N :=
    fun N => Finset.sum_range_sub' g N
  -- g N → 0
  have hgz : Tendsto g atTop (𝓝 0) := nemesH_tendsto_zero x hx
  have hg0 : g 0 = nemesH x := by simp [hg]
  -- partial sums tend to g 0 - 0 = nemesH x
  have htend : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (g i - g (i + 1))) atTop
      (𝓝 (nemesH x)) := by
    have hbase : Tendsto (fun N : ℕ => g 0 - g N) atTop (𝓝 (g 0 - 0)) :=
      tendsto_const_nhds.sub hgz
    rw [hg0, sub_zero] at hbase
    refine hbase.congr (fun N => ?_)
    rw [htel N, hg0]
  -- conclude HasSum (g n - g (n+1)) via the nonneg criterion
  have key : HasSum (fun n : ℕ => g n - g (n + 1)) (nemesH x) :=
    (hasSum_iff_tendsto_nat_of_nonneg hnn (nemesH x)).2 htend
  -- align indexing back to the stated telescoping term
  exact key.congr_fun (fun n => hterm n)

/-- The telescoping majorant series is summable. -/
theorem summable_nemesH_telescope (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => nemesH (x + (n:ℝ)) - nemesH (x + ((n:ℝ) + 1))) :=
  (hasSum_nemesH_telescope x hx).summable

/-- **Per-term majorization** (the form matching the telescoping series): for `x > 0`,
`1/(x+n)² ≤ H (x+n) - H (x+(n+1))`. -/
theorem trigamma_term_le (x : ℝ) (hx : 0 < x) (n : ℕ) :
    1 / (x + (n : ℝ)) ^ 2 ≤ nemesH (x + (n : ℝ)) - nemesH (x + ((n : ℝ) + 1)) := by
  have hxn : 0 < x + (n : ℝ) := by positivity
  have hge := nemesH_telescope_ge (x + (n : ℝ)) hxn
  rw [show x + (n : ℝ) + 1 = x + ((n : ℝ) + 1) by ring] at hge
  exact hge

/-- **Summability of the trigamma series** for `x > 0`, by comparison with the telescoping
majorant. -/
theorem trigamma_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => 1 / (x + (n : ℝ)) ^ 2) := by
  apply Summable.of_nonneg_of_le (g := fun n : ℕ => 1 / (x + (n:ℝ)) ^ 2)
    (f := fun n : ℕ => nemesH (x + (n:ℝ)) - nemesH (x + ((n:ℝ) + 1)))
  · intro n; positivity
  · intro n; exact trigamma_term_le x hx n
  · exact summable_nemesH_telescope x hx

/-- **Nemes' rational upper bound on the trigamma function.**  For `x > 0`,
`ψ'(x) ≤ 1/x + 1/(2x²) + 1/(6x³)`.  (Tight constants; valid for all positive `x`, hence in
particular for `x ≥ 1`.) -/
theorem nemes_trigamma_bound (x : ℝ) (hx : 0 < x) :
    trigamma x ≤ 1 / x + 1 / (2 * x ^ 2) + 1 / (6 * x ^ 3) := by
  have hsumm_tri := trigamma_summable x hx
  have hsumm_tel := summable_nemesH_telescope x hx
  have hle : ∀ n : ℕ,
      1 / (x + (n:ℝ)) ^ 2 ≤ nemesH (x + (n:ℝ)) - nemesH (x + ((n:ℝ) + 1)) :=
    fun n => trigamma_term_le x hx n
  have hcmp : trigamma x ≤ ∑' n : ℕ, (nemesH (x + (n:ℝ)) - nemesH (x + ((n:ℝ) + 1))) := by
    unfold trigamma
    exact hsumm_tri.tsum_le_tsum hle hsumm_tel
  have hval : (∑' n : ℕ, (nemesH (x + (n:ℝ)) - nemesH (x + ((n:ℝ) + 1)))) = nemesH x :=
    (hasSum_nemesH_telescope x hx).tsum_eq
  rw [hval] at hcmp
  simpa [nemesH] using hcmp

/-- **Nemes' bound, the paper's `x ≥ 1` form** (a direct corollary of the stronger `x > 0`
version above).  This is the exact statement cited as Ekerå 2023 Claim `bound-trigamma`. -/
theorem nemes_trigamma_bound_ge_one (x : ℝ) (hx : x ≥ 1) :
    trigamma x ≤ 1 / x + 1 / (2 * x ^ 2) + 1 / (6 * x ^ 3) :=
  nemes_trigamma_bound x (lt_of_lt_of_le one_pos hx)

/-- **Application to Ekerå** (matches `EkeraSuccess.ekeraGoodFactor`'s baked-in bound).
Instantiating Nemes at `x = 2^τ` for `τ > 0` (so `2^τ ≥ 2 > 0`):
`ψ'(2^τ) ≤ 1/2^τ + 1/(2·2^{2τ}) + 1/(6·2^{3τ})`. -/
theorem ekeraGoodFactor_trigamma (τ : ℕ) (_hτ : τ > 0) :
    trigamma ((2 : ℝ) ^ τ) ≤
      1 / (2 : ℝ) ^ τ + 1 / (2 * (2 : ℝ) ^ (2 * τ)) + 1 / (6 * (2 : ℝ) ^ (3 * τ)) := by
  -- the Nemes bound holds for all `x > 0`, and `2^τ > 0` unconditionally, so `_hτ` is not needed
  have hx : (0 : ℝ) < (2 : ℝ) ^ τ := by positivity
  have h := nemes_trigamma_bound ((2 : ℝ) ^ τ) hx
  have e2 : ((2 : ℝ) ^ τ) ^ 2 = (2 : ℝ) ^ (2 * τ) := by
    rw [← pow_mul]; ring_nf
  have e3 : ((2 : ℝ) ^ τ) ^ 3 = (2 : ℝ) ^ (3 * τ) := by
    rw [← pow_mul]; ring_nf
  rw [e2, e3] at h
  exact h

end FormalRV.CFS.Trigamma
