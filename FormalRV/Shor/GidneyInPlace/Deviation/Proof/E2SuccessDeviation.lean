/-
  FormalRV.Shor.GidneyInPlace.E2SuccessDeviation — H5 of the coset-Shor hybrid route:
  the conditional PROBABILITY capstone (lift the H4 orbit ℓ² bound to success probabilities).
  ════════════════════════════════════════════════════════════════════════════

  H4 (`E2OrbitDeviation.orbit_E2_pmDist_deviation`) bounds the orbit-level ℓ² deviation of the
  actual physical machine from the ideal runway machine by `m · √(8·numWin/2^cm)`.  This file
  lifts that STATE deviation to the SUCCESS PROBABILITY via a SUMMED measurement-stability bound,
  then bridges the ideal-runway probability to the ordinary plain-Shor probability via P1.3.

  THE SUMMED MEASUREMENT-STABILITY BOUND (the genuinely-new content).  The per-outcome H2
  (`GracefulDegradation.prob_partial_meas_diff_le_two_dist`) bounds a SINGLE outcome's marginal
  by `2·pmDist`.  But the success probability is a `r_found`-weighted SUM over ALL `2^m` phase
  outcomes; summing the per-outcome bound would give the useless `2^m · 2·pmDist`.  The correct
  bound is `2·pmDist` for the WHOLE weighted sum (projector form): for `0/1`-valued (more
  generally `[0,1]`-valued) weights `c`,

    `|∑ₓ c x · P(x|φ) − ∑ₓ c x · P(x|ψ)| ≤ 2·pmDist φ ψ`   (`prob_success_weighted_diff_le_two_dist`).

  Proof: decompose to `∑ₓ∑_y c x (‖φ‖²−‖ψ‖²)`, bound `|·| ≤ ∑∑ c x ‖Δ‖(‖φ‖+‖ψ‖)`, DROP `c x ≤ 1`
  and extend the index to the FULL register, then ONE Cauchy–Schwarz over `Fin full_dim`:
  `≤ √(∑‖Δ‖²)·√(∑(‖φ‖+‖ψ‖)²) ≤ √(pmDist²)·√4 = 2·pmDist`.  (Extending to the full register is why
  no slice-disjointness is needed — the same trick H2 uses for a single slice, here for all of
  them at once.)  Reuses H2's building blocks `normSq_sub_le`, `pmDist_sq`, `pmNorm_sq` and the
  Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq`.

  H5 (`coset_route2_success_hybrid_norm_E2`).  Combine:
    • the summed bound at `c := r_found`, `φ := Shor_final_state_E2coset f_runwayPhysical`,
      `ψ := Shor_final_state_E2coset f_runwayIdeal`, with H4's `pmDist ≤ m·√(…)`;
    • P1.3's bridge `probability_of_success_E2coset_eq` (the ideal-runway success probability
      equals the ordinary plain-Shor `probability_of_success f_residueIdeal`).
  Result:  `probability_of_success_E2coset f_runwayPhysical
              ≥ probability_of_success f_residueIdeal − 2·m·√(8·numWin/2^cm)`.

  HYPOTHESES carried EXPLICITLY (dischargeable later; the SQUARE-ROOT error term is sound but
  weaker than a linear term): `hisom` (per-stage isometry → `hU`); `hf_physical`/`hf_runway`
  (realizations); `hnormP`/`hnormI` (the two final states are unit-norm — `E2runwayInit` is a
  unit vector and the stages are isometries); the P1.3 bridge data (`hf_residue`, `hsupp_res`).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond `{propext, Classical.choice,
  Quot.sound}`.
-/
import FormalRV.Shor.GidneyInPlace.Deviation.Proof.E2OrbitDeviation
import FormalRV.Shor.GidneyInPlace.Deviation.Proof.E2ResidueEmbed
import FormalRV.Shor.ApproxTransfer

namespace FormalRV.Shor.GidneyInPlace.E2SuccessDeviation

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Shor.Approx
  (pmDist pmNorm pmDist_sq pmNorm_sq pmDist_nonneg pmNorm_nonneg normSq_sub_le)
open FormalRV.SQIRPort.ApproxTransfer
  (jointIdx sum_jointIdx_eq prob_partial_meas_basis_eq r_found_nonneg r_found_le_one)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate (gidneyInPlaceWithSwap)
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp (qpeStageMap)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq)
open FormalRV.Shor.GidneyInPlace.ControlOracleLift (workMat)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess
  (Shor_final_state_E2coset probability_of_success_E2coset probability_of_success_E2coset_def)
open FormalRV.Shor.GidneyInPlace.E2OrbitDeviation (orbit_E2_pmDist_deviation)
open FormalRV.Shor.GidneyInPlace.E2ResidueEmbed (probability_of_success_E2coset_eq)

/-! ## §1. The summed (projector-form) ℓ² measurement-stability bound. -/

/-- **Summed measurement stability — the `[0,1]`-weighted version.**  For weights `c x ∈ [0,1]`
    and normalized states (`pmNorm ≤ 1`), the `c`-weighted measurement-probability sum is
    `2`-Lipschitz in the ℓ² state distance `pmDist`:
      `|∑ₓ c x · P(x|φ) − ∑ₓ c x · P(x|ψ)| ≤ 2·pmDist φ ψ`.
    Unlike the per-outcome H2, the constant does NOT scale with the number of outcomes — the
    weight-drop `c x ≤ 1` lets the Cauchy–Schwarz run over the full register at once. -/
theorem prob_success_weighted_diff_le_two_dist
    {m_dim full_dim : Nat} (h_dvd : m_dim ∣ full_dim)
    (c : Fin m_dim → ℝ) (hc0 : ∀ x, 0 ≤ c x) (hc1 : ∀ x, c x ≤ 1)
    (φ ψ : QState full_dim) (hφ : pmNorm φ ≤ 1) (hψ : pmNorm ψ ≤ 1) :
    |(∑ x : Fin m_dim, c x * prob_partial_meas (basis_vector m_dim x.val) φ)
       - (∑ x : Fin m_dim, c x * prob_partial_meas (basis_vector m_dim x.val) ψ)|
      ≤ 2 * pmDist φ ψ := by
  classical
  set f : Fin full_dim → ℝ := fun i => ‖φ i 0 - ψ i 0‖ with hf
  set G : Fin full_dim → ℝ := fun i => ‖φ i 0‖ + ‖ψ i 0‖ with hG
  -- Step A: the weighted difference is the weighted double sum of the slice-wise `‖·‖²` differences.
  have hdecomp : (∑ x : Fin m_dim, c x * prob_partial_meas (basis_vector m_dim x.val) φ)
       - (∑ x : Fin m_dim, c x * prob_partial_meas (basis_vector m_dim x.val) ψ)
      = ∑ x : Fin m_dim, ∑ y : Fin (full_dim / m_dim),
          c x * (Complex.normSq (φ (jointIdx h_dvd x y) 0)
                 - Complex.normSq (ψ (jointIdx h_dvd x y) 0)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro x _
    rw [prob_partial_meas_basis_eq φ x h_dvd, prob_partial_meas_basis_eq ψ x h_dvd,
        Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro y _; ring
  rw [hdecomp]
  -- Step B: |weighted double sum| ≤ ∑∑ (f·G at the joint index)  (drop `c x ≤ 1`, use `normSq_sub_le`).
  have hkey : |∑ x : Fin m_dim, ∑ y : Fin (full_dim / m_dim),
        c x * (Complex.normSq (φ (jointIdx h_dvd x y) 0)
               - Complex.normSq (ψ (jointIdx h_dvd x y) 0))|
      ≤ ∑ x : Fin m_dim, ∑ y : Fin (full_dim / m_dim),
          f (jointIdx h_dvd x y) * G (jointIdx h_dvd x y) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun x _ => ?_))
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun y _ => ?_))
    rw [abs_mul, abs_of_nonneg (hc0 x)]
    calc c x * |Complex.normSq (φ (jointIdx h_dvd x y) 0)
                - Complex.normSq (ψ (jointIdx h_dvd x y) 0)|
        ≤ 1 * |Complex.normSq (φ (jointIdx h_dvd x y) 0)
                - Complex.normSq (ψ (jointIdx h_dvd x y) 0)| :=
          mul_le_mul_of_nonneg_right (hc1 x) (abs_nonneg _)
      _ = |Complex.normSq (φ (jointIdx h_dvd x y) 0)
                - Complex.normSq (ψ (jointIdx h_dvd x y) 0)| := one_mul _
      _ ≤ f (jointIdx h_dvd x y) * G (jointIdx h_dvd x y) := by
          simp only [hf, hG]; exact normSq_sub_le _ _
  refine le_trans hkey ?_
  -- reindex the joint double sum to the full register.
  rw [sum_jointIdx_eq h_dvd (fun i => f i * G i)]
  -- Step C: one Cauchy–Schwarz over `Fin full_dim`.
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f G
  have hf2 : (∑ i, (f i) ^ 2) = (pmDist φ ψ) ^ 2 := by
    rw [pmDist_sq]
    apply Finset.sum_congr rfl; intro i _
    simp only [hf]; rw [Complex.normSq_eq_norm_sq]
  have hG2 : (∑ i, (G i) ^ 2) ≤ 4 := by
    have hpt : ∀ i, (G i) ^ 2 ≤ 2 * Complex.normSq (φ i 0) + 2 * Complex.normSq (ψ i 0) := by
      intro i; simp only [hG]
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (φ i 0), norm_nonneg (ψ i 0),
                 sq_nonneg (‖φ i 0‖ - ‖ψ i 0‖)]
    refine (Finset.sum_le_sum fun i _ => hpt i).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hbφ : (∑ i, Complex.normSq (φ i 0)) ≤ 1 := by
      rw [← pmNorm_sq]; nlinarith [pmNorm_nonneg φ]
    have hbψ : (∑ i, Complex.normSq (ψ i 0)) ≤ 1 := by
      rw [← pmNorm_sq]; nlinarith [pmNorm_nonneg ψ]
    linarith
  have hsum_nn : 0 ≤ ∑ i, f i * G i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (by positivity)
  have hprod : (∑ i, f i * G i) ^ 2 ≤ (2 * pmDist φ ψ) ^ 2 := by
    refine hcs.trans ?_
    calc (∑ i, (f i) ^ 2) * (∑ i, (G i) ^ 2)
        ≤ (pmDist φ ψ) ^ 2 * 4 := by
          rw [hf2]; exact mul_le_mul_of_nonneg_left hG2 (sq_nonneg _)
      _ = (2 * pmDist φ ψ) ^ 2 := by ring
  have := Real.sqrt_le_sqrt hprod
  rwa [Real.sqrt_sq hsum_nn,
       Real.sqrt_sq (by have := pmDist_nonneg φ ψ; linarith : (0:ℝ) ≤ 2 * pmDist φ ψ)] at this

/-! ## §2. The actual-vs-ideal-runway success-probability deviation (H4 lifted to probabilities). -/

/-- **Actual-vs-ideal-runway success deviation.**  The physical-machine and ideal-runway-machine
    `E2coset` success probabilities differ by at most `2·m·√(8·numWin/2^cm)`.  Combines the summed
    measurement-stability bound (`prob_success_weighted_diff_le_two_dist` at the `r_found` weights)
    with H4's orbit ℓ² bound `pmDist ≤ m·√(…)`.  The per-stage fit hypotheses H4 needs are derived
    from the single full-blocks budget `hMN : 2^cm·N ≤ 2^bits`. -/
theorem E2coset_prob_success_diff_le
    (a r N m w bits numWin cm : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat) (mult kInv : Nat → Nat)
    (f_runwayPhysical f_runwayIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwtP : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayPhysical j))
    (hwtI : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hTfamK : ∀ k j addr, TfamK k j addr = tableValue (mult k) N w j addr)
    (hTfamKinv : ∀ k j addr, TfamKinv k j addr = tableValue (kInv k) N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hN1 : 1 < N)
    (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (hkkinv : ∀ k, (kInv k * mult k) % N = 1 % N)
    (hisom : ∀ (k : Nat) (a b : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits))),
        pmDist (qpeStageMap m bits (cosetAnc w bits) f_runwayPhysical k a)
               (qpeStageMap m bits (cosetAnc w bits) f_runwayPhysical k b) = pmDist a b)
    (hf_physical : ∀ (k : Nat), k < m → ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayPhysical (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = (FormalRV.Framework.uc_eval (Gate.toUCom (cosetDim w bits)
                (gidneyInPlaceWithSwap w bits (TfamK k) (TfamKinv k) numWin))
              * cosetInputVec w bits N cm z 0) (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_runway : ∀ (k : Nat) (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = cosetInputVec w bits N cm ((mult k * z) % N) 0
              (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hnormP : pmNorm (Shor_final_state_E2coset m w bits N cm f_runwayPhysical) ≤ 1)
    (hnormI : pmNorm (Shor_final_state_E2coset m w bits N cm f_runwayIdeal) ≤ 1) :
    |probability_of_success_E2coset a r N m w bits cm f_runwayPhysical
        - probability_of_success_E2coset a r N m w bits cm f_runwayIdeal|
      ≤ 2 * (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) := by
  -- the full-blocks budget delivers H4's per-stage fit hypotheses.
  have hbudget : ∀ v : Nat, v < N → v + (2 ^ cm - 1) * N < 2 ^ bits := by
    intro v hv
    have h2 : 2 ^ cm * N = (2 ^ cm - 1) * N + N := by
      have hle : N ≤ 2 ^ cm * N := Nat.le_mul_of_pos_left N (Nat.two_pow_pos cm)
      rw [Nat.sub_mul, one_mul]; omega
    omega
  have hfit : ∀ (k z : Nat), z < N → (mult k * z) % N + (2 ^ cm - 1) * N < 2 ^ bits :=
    fun k z hz => hbudget _ (Nat.mod_lt _ hN)
  have hxfit : ∀ (z : Nat), z < N → z + (2 ^ cm - 1) * N < 2 ^ bits := fun z hz => hbudget z hz
  -- both success sums as `Fin (2^m)`-sums; the summed measurement-stability bound.
  rw [probability_of_success_E2coset_def, probability_of_success_E2coset_def,
      ← Fin.sum_univ_eq_sum_range
        (fun x => r_found x m r a N * prob_partial_meas (basis_vector (2 ^ m) x)
          (Shor_final_state_E2coset m w bits N cm f_runwayPhysical)) (2 ^ m),
      ← Fin.sum_univ_eq_sum_range
        (fun x => r_found x m r a N * prob_partial_meas (basis_vector (2 ^ m) x)
          (Shor_final_state_E2coset m w bits N cm f_runwayIdeal)) (2 ^ m)]
  have hdvd : (2 ^ m) ∣ (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) :=
    ⟨2 ^ bits * 2 ^ (cosetAnc w bits), by rw [mul_assoc]⟩
  refine le_trans (prob_success_weighted_diff_le_two_dist hdvd
    (fun x => r_found x.val m r a N) (fun x => r_found_nonneg _ _ _ _ _)
    (fun x => r_found_le_one _ _ _ _ _)
    (Shor_final_state_E2coset m w bits N cm f_runwayPhysical)
    (Shor_final_state_E2coset m w bits N cm f_runwayIdeal) hnormP hnormI) ?_
  -- 2·pmDist ≤ 2·m·√(…)  from H4.
  rw [show (2 : ℝ) * (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm)
        = 2 * ((m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm)) from by ring]
  exact mul_le_mul_of_nonneg_left
    (orbit_E2_pmDist_deviation m w bits numWin N cm TfamK TfamKinv mult kInv
      f_runwayPhysical f_runwayIdeal hwtP hwtI hTfamK hTfamKinv hw hbits hN hN1 hkkinv
      hfit hxfit hisom hf_physical hf_runway)
    (by norm_num)

/-! ## §3. H5 — the conditional success-probability capstone. -/

/-- **H5 — the conditional coset-Shor success-probability capstone.**  The ACTUAL physical
    runway/coset machine succeeds almost as well as the ORDINARY plain-Shor ideal machine:
      `probability_of_success_E2coset f_runwayPhysical
         ≥ probability_of_success f_residueIdeal − 2·m·√(8·numWin/2^cm)`.
    Combines `E2coset_prob_success_diff_le` (the actual-vs-ideal-runway gap, H4 lifted to
    probabilities) with P1.3's `probability_of_success_E2coset_eq` (the ideal-runway success
    probability equals the ordinary plain-Shor success probability, via the isometric residue
    embedding).  The SQUARE-ROOT error term `2·m·√(…)` is sound (weaker than a linear term).

    All realization/support hypotheses are carried EXPLICITLY (`hisom` → `hU`; `hf_physical`,
    `hf_runway` realizations; `hf_residue`, `hsupp_res` the P1.3 bridge data; `hnormP`/`hnormI`
    the unit-norm final states).  The single `hf_runway` feeds BOTH H4 and the P1.3 bridge
    (`workMat` unfolds to its `uc_eval`-at-cast form). -/
theorem coset_route2_success_hybrid_norm_E2
    (a r N m w bits numWin cm : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat) (mult kInv : Nat → Nat)
    (f_runwayPhysical f_runwayIdeal f_residueIdeal :
      Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hm : 0 < m) (hbitsPos : 0 < bits)
    (hwtP : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayPhysical j))
    (hwtI : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hwtRes : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_residueIdeal j))
    (hTfamK : ∀ k j addr, TfamK k j addr = tableValue (mult k) N w j addr)
    (hTfamKinv : ∀ k j addr, TfamKinv k j addr = tableValue (kInv k) N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hN1 : 1 < N)
    (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (hkkinv : ∀ k, (kInv k * mult k) % N = 1 % N)
    (hisom : ∀ (k : Nat) (a b : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits))),
        pmDist (qpeStageMap m bits (cosetAnc w bits) f_runwayPhysical k a)
               (qpeStageMap m bits (cosetAnc w bits) f_runwayPhysical k b) = pmDist a b)
    (hf_physical : ∀ (k : Nat), k < m → ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayPhysical (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = (FormalRV.Framework.uc_eval (Gate.toUCom (cosetDim w bits)
                (gidneyInPlaceWithSwap w bits (TfamK k) (TfamKinv k) numWin))
              * cosetInputVec w bits N cm z 0) (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_runway : ∀ (k : Nat) (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = cosetInputVec w bits N cm ((mult k * z) % N) 0
              (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_residue : ∀ (kstep : Nat), kstep < m →
        ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b
          = if a.val = (if b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N
                then ((mult kstep * (b.val / 2 ^ (cosetAnc w bits))) % N) * 2 ^ (cosetAnc w bits)
                else b.val)
              then 1 else 0)
    (hsupp_res : ∀ (x : Fin (2 ^ m))
        (b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        ¬ (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        Shor_final_state m bits (cosetAnc w bits) f_residueIdeal
            (jointIdx (shorDvd m bits (cosetAnc w bits)) x b) 0 = 0)
    (hnormP : pmNorm (Shor_final_state_E2coset m w bits N cm f_runwayPhysical) ≤ 1)
    (hnormI : pmNorm (Shor_final_state_E2coset m w bits N cm f_runwayIdeal) ≤ 1) :
    probability_of_success_E2coset a r N m w bits cm f_runwayPhysical
      ≥ probability_of_success a r N m bits (cosetAnc w bits) f_residueIdeal
          - 2 * (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) := by
  -- P1.3: the ideal-runway success probability equals the ordinary plain-Shor one.
  have hbridge := probability_of_success_E2coset_eq a r N m w bits cm hm hbitsPos mult hN hN1
    numWin hw hbits hMN f_runwayIdeal f_residueIdeal hwtI hwtRes
    (fun kstep _ z hz y => hf_runway kstep z hz y) hf_residue hsupp_res
  -- H4 lifted to probabilities: |P_physical − P_runwayIdeal| ≤ 2·m·√(…).
  have hdiff := E2coset_prob_success_diff_le a r N m w bits numWin cm TfamK TfamKinv mult kInv
    f_runwayPhysical f_runwayIdeal hwtP hwtI hTfamK hTfamKinv hw hbits hN hN1 hMN hkkinv
    hisom hf_physical hf_runway hnormP hnormI
  rw [hbridge] at hdiff
  have hb := (abs_le.mp hdiff).1
  linarith
