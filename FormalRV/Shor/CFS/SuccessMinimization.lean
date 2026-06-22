/-
  FormalRV.Shor.CFS.SuccessMinimization — Stage-6 per-shot success minimization (Gidney 2025 §2,
  lines 802/808/814).

  The masked approximate-period-finding per-shot deviation rate is `P_deviant ≤ S + ε/S`, where `S`
  is the mask-superposition width parameter and `ε` the single-point modular deviation (Stage 3/4,
  `modDev_truncAcc_normalized` + `approx_periodic`).  Minimizing the upper bound `S + ε/S` over `S > 0`
  (AM–GM) gives the minimum `2√ε`, attained at `S = √ε`:

      P_deviant ≤ S + ε/S ≥ 2√ε  (equality at S = √ε).

  This file proves the elementary real-analysis content: the lower bound `2√ε ≤ S + ε/S` for all
  `S > 0` and the attainment at `S = √ε`.  Kernel-clean (Mathlib `Real.sqrt` only).
-/
import FormalRV.Shor.CFS.ModularDeviation

namespace FormalRV.CFS

/-- **The deviation-rate lower bound (AM–GM).**  For single-point deviation `ε ≥ 0` and mask width
    `S > 0`, the Gidney bound `S + ε/S` is at least `2√ε` — so the per-shot deviant rate can be no
    smaller than `2√ε` for any mask choice.  Proof: `S + ε/S - 2√ε = (S - √ε)²/S ≥ 0`. -/
theorem cfs_deviant_bound (ε S : ℝ) (hε : 0 ≤ ε) (hS : 0 < S) :
    2 * Real.sqrt ε ≤ S + ε / S := by
  have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε
  have h1 : 2 * Real.sqrt ε * S ≤ S * S + ε := by
    nlinarith [sq_nonneg (S - Real.sqrt ε), hsq]
  have h2 : (S * S + ε) / S = S + ε / S := by field_simp
  have h3 : 2 * Real.sqrt ε ≤ (S * S + ε) / S := by rw [le_div_iff₀ hS]; linarith [h1]
  rwa [h2] at h3

/-- **The minimizer.**  At the optimal mask width `S = √ε` (for `ε > 0`), the bound `S + ε/S`
    attains exactly its minimum value `2√ε`. -/
theorem cfs_deviant_min (ε : ℝ) (hε : 0 < ε) :
    Real.sqrt ε + ε / Real.sqrt ε = 2 * Real.sqrt ε := by
  have hpos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hsq : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt (le_of_lt hε)
  have h : ε / Real.sqrt ε = Real.sqrt ε := by rw [div_eq_iff (ne_of_gt hpos), hsq]
  rw [h]; ring

/-- **The full minimization statement.**  `2√ε` is a lower bound for `S + ε/S` over all `S > 0`
    (`cfs_deviant_bound`) AND is attained at `S = √ε` (`cfs_deviant_min`) — i.e. `min_{S>0} (S+ε/S)
    = 2√ε`, the optimal per-shot deviant-rate bound of the masked CFS period finding. -/
theorem cfs_success_minimization (ε : ℝ) (hε : 0 < ε) :
    (∀ S : ℝ, 0 < S → 2 * Real.sqrt ε ≤ S + ε / S)
    ∧ Real.sqrt ε + ε / Real.sqrt ε = 2 * Real.sqrt ε :=
  ⟨fun S hS => cfs_deviant_bound ε S (le_of_lt hε) hS, cfs_deviant_min ε hε⟩

end FormalRV.CFS
