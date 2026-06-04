/-
  FormalRV.Shor.ApproxTransfer — GAP 5 (approximate transfer), CLOSED.

  ## What this closes

  `ProbabilityTransfer.lean` (`prob_of_success_congr`) gives the EXACT transfer:
  equal post-circuit states ⇒ equal success probabilities.  GAP 5 is the
  *quantitative* version a real compiler needs: when the compiled final state is
  only ε-CLOSE to the verified ideal state (e.g. AQFT truncation), how much can
  the success probability move?  This file proves a Lipschitz transfer

      |probability_of_success(f₁) − probability_of_success(f₂)|
        ≤ C · D(Shor_final_state f₁, Shor_final_state f₂)

  at three increasingly explicit levels of the distance `D`, all sorry-free and
  axiom-free (only the repo + mathlib).

  ## The three deliverables (each a standalone theorem)

  1. `prob_of_success_transfer_normSqDist` — `D = normSqDist = ∑_i ‖⟨i|s₁⟩‖² −
     ‖⟨i|s₂⟩‖²|`, the classical (TV-like) amplitude-square distance, `C = 1`.
     **No normalization hypothesis.**  This is exactly the user's fallback bound
     `Σ_x |⟨x|s₁⟩|² − |⟨x|s₂⟩|²|` — validated.
  2. `prob_of_success_transfer_ampDist` — `D = ampDist = ∑_i (‖s₁ᵢ‖+‖s₂ᵢ‖)·
     ‖s₁ᵢ − s₂ᵢ‖`, an explicit amplitude expression, `C = 1`.  Refines (1) via
     the pointwise `||a|²−|b|²| ≤ (|a|+|b|)·|a−b|`.
  3. `prob_of_success_transfer_l2` — `D = l2dist = ‖s₁ − s₂‖₂` (Euclidean), the
     headline Lipschitz constant **`C = 2`** for L2-normalized pure states.
     Refines (2) via discrete Cauchy–Schwarz + Minkowski.

  ## Proof skeleton (per CLAUDE.md "semantic correctness BEFORE counts")

  `probability_of_success = ∑_x r_found(x)·prob_partial_meas(|x⟩, s)` with
  `r_found ∈ {0,1}`.  Steps:

    · `prob_partial_meas_basis_eq`  — Born rule: against a basis vector `|x⟩`,
      `prob_partial_meas` collapses to the marginal `∑_y ‖φ_{x·k+y}‖²`.
    · triangle inequality + `r_found ≤ 1` drop the indicator.
    · `sum_jointIdx_eq` — the joint index `(x,y) ↦ x·k+y` is a bijection
      `Fin(2^m) × Fin k ≃ Fin(2^m·2^n·2^anc)` (`finProdFinEquiv`), so the double
      sum reindexes to the whole register, giving exactly `normSqDist`.

  ## Composition with the AQFT error budget (§4)

  `aqft_transfer_compose`: if the ideal verified circuit has
  `probability_of_success ≥ P_ideal` and the AQFT-compiled circuit's final state
  is ε-close in `l2dist`, then the compiled circuit succeeds with probability
  `≥ P_ideal − 2·ε`.  Instantiated with `VerifiedShor`'s `P_ideal = κ/(log₂N)⁴`,
  this is `probability_of_success(PPM/AQFT-compiled) ≥ κ/(log₂N)⁴ − 2·ε`.

  No `sorry`, no new `axiom`.
-/
import FormalRV.Shor.ProbabilityTransfer
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Positivity

namespace FormalRV.SQIRPort.ApproxTransfer

open FormalRV.SQIRPort

/-! ## §0. The Born-rule marginal against a basis vector. -/

/-- The joint index `i = x·k + y` (first register `x`, second register `y`),
    cast into `Fin full_dim`.  This is the index `prob_partial_meas` reads when
    measured against `|x⟩` and summing the unmeasured register `|y⟩`. -/
def jointIdx {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (x : Fin m_dim) (y : Fin (full_dim / m_dim)) : Fin full_dim :=
  Fin.cast (Nat.mul_div_cancel' h)
    ⟨x.val * (full_dim / m_dim) + y.val, by
      have hy : y.val < full_dim / m_dim := y.isLt
      have hx : x.val < m_dim := x.isLt
      calc x.val * (full_dim / m_dim) + y.val
          < x.val * (full_dim / m_dim) + (full_dim / m_dim) := by omega
        _ = (x.val + 1) * (full_dim / m_dim) := by ring
        _ ≤ m_dim * (full_dim / m_dim) := Nat.mul_le_mul_right _ hx⟩

/-- **Born rule.**  `prob_partial_meas` against a basis vector `|x⟩` (with
    `x < m_dim`) collapses to the marginal `∑_y ‖φ_{jointIdx x y}‖²`. -/
theorem prob_partial_meas_basis_eq
    {m_dim full_dim : Nat} (φ : QState full_dim)
    (x : Fin m_dim) (h : m_dim ∣ full_dim) :
    prob_partial_meas (basis_vector m_dim x.val) φ
      = ∑ y : Fin (full_dim / m_dim), Complex.normSq (φ (jointIdx h x y) 0) := by
  unfold prob_partial_meas
  rw [dif_pos h]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  rw [Finset.sum_eq_single x]
  · simp only [basis_vector, FormalRV.Framework.basis_vector_apply, if_pos]
    have hcast : (Fin.cast (Nat.mul_div_cancel' h)
        ⟨x.val * (full_dim / m_dim) + y.val, by
          have hy : y.val < full_dim / m_dim := y.isLt
          calc x.val * (full_dim / m_dim) + y.val
              < x.val * (full_dim / m_dim) + (full_dim / m_dim) := by omega
            _ = (x.val + 1) * (full_dim / m_dim) := by ring
            _ ≤ m_dim * (full_dim / m_dim) := Nat.mul_le_mul_right _ x.isLt⟩)
        = jointIdx h x y := rfl
    rw [hcast]
    simp
  · intro b _ hb
    simp only [basis_vector, FormalRV.Framework.basis_vector_apply]
    rw [if_neg]
    · simp
    · intro hbx
      exact hb (Fin.ext hbx)
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-! ## §1. The amplitude-square distance and the per-outcome bound. -/

/-- The amplitude-square ("classical", TV-like) distance on full-register
    states: `D(s₁,s₂) = ∑_i | ‖⟨i|s₁⟩‖² − ‖⟨i|s₂⟩‖² |`.  This is a genuinely
    PROVABLE distance — a finite sum of absolute values, no norm instance needed. -/
noncomputable def normSqDist {dim : Nat} (s₁ s₂ : QState dim) : ℝ :=
  ∑ i : Fin dim, |Complex.normSq (s₁ i 0) - Complex.normSq (s₂ i 0)|

theorem normSqDist_nonneg {dim : Nat} (s₁ s₂ : QState dim) :
    0 ≤ normSqDist s₁ s₂ :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Per-outcome bound: the difference of Born probabilities at outcome `|x⟩` is
    at most the sum (over the unmeasured register) of per-index normSq
    differences.  Triangle inequality on the Born-rule marginals. -/
theorem prob_partial_meas_basis_sub_abs_le
    {m_dim full_dim : Nat} (s₁ s₂ : QState full_dim)
    (x : Fin m_dim) (h : m_dim ∣ full_dim) :
    |prob_partial_meas (basis_vector m_dim x.val) s₁
        - prob_partial_meas (basis_vector m_dim x.val) s₂|
      ≤ ∑ y : Fin (full_dim / m_dim),
          |Complex.normSq (s₁ (jointIdx h x y) 0)
            - Complex.normSq (s₂ (jointIdx h x y) 0)| := by
  rw [prob_partial_meas_basis_eq s₁ x h, prob_partial_meas_basis_eq s₂ x h,
      ← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-! ## §2. Reindexing the joint index to the full register. -/

/-- `jointIdx` numerically equals `finProdFinEquiv` (cast across
    `full_dim = m_dim · (full_dim/m_dim)`). -/
theorem jointIdx_eq_finProdFinEquiv {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (x : Fin m_dim) (y : Fin (full_dim / m_dim)) :
    jointIdx h x y
      = Fin.cast (Nat.mul_div_cancel' h) (finProdFinEquiv (x, y)) := by
  apply Fin.ext
  simp only [jointIdx, Fin.val_cast, finProdFinEquiv_apply_val]
  ring

/-- Reindexing: summing a function over the joint index `x·k+y` (ranging over
    both registers) equals summing over the whole full register.  `jointIdx`
    realizes the bijection `Fin m_dim × Fin (full_dim/m_dim) ≃ Fin full_dim`. -/
theorem sum_jointIdx_eq {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (g : Fin full_dim → ℝ) :
    ∑ x : Fin m_dim, ∑ y : Fin (full_dim / m_dim), g (jointIdx h x y)
      = ∑ i : Fin full_dim, g i := by
  rw [← Fintype.sum_prod_type']
  have hstep : ∀ p : Fin m_dim × Fin (full_dim / m_dim),
      g (jointIdx h p.1 p.2)
        = (fun q : Fin (m_dim * (full_dim / m_dim)) =>
            g (Fin.cast (Nat.mul_div_cancel' h) q)) (finProdFinEquiv p) := by
    intro p
    rw [jointIdx_eq_finProdFinEquiv]
  rw [Finset.sum_congr rfl (fun p _ => hstep p)]
  rw [Equiv.sum_comp finProdFinEquiv
    (fun q => g (Fin.cast (Nat.mul_div_cancel' h) q))]
  exact Fintype.sum_equiv (finCongr (Nat.mul_div_cancel' h))
    _ _ (fun q => by simp)

/-! ## §3. The headline transfer bound (distance level, `C = 1`). -/

theorem r_found_nonneg (o m r a N : Nat) : 0 ≤ r_found o m r a N := by
  unfold r_found; split <;> norm_num

theorem r_found_le_one (o m r a N : Nat) : r_found o m r a N ≤ 1 := by
  unfold r_found; split <;> norm_num

/-- **GAP 5 — distance level.**  The success probability is
    `normSqDist`-Lipschitz with constant `1`: for ANY two oracle families, the
    success probabilities differ by at most the amplitude-square distance of the
    two post-circuit states.  No normalization hypothesis is needed.

    This is the user's validated fallback bound
    `Σ_x | ‖⟨x|s₁⟩‖² − ‖⟨x|s₂⟩‖² |`. -/
theorem prob_of_success_transfer_normSqDist
    (a r N m n anc : Nat)
    (f₁ f₂ : Nat → BaseUCom (n + anc)) :
    |probability_of_success a r N m n anc f₁
        - probability_of_success a r N m n anc f₂|
      ≤ normSqDist (Shor_final_state m n anc f₁) (Shor_final_state m n anc f₂) := by
  set s₁ := Shor_final_state m n anc f₁ with hs₁
  set s₂ := Shor_final_state m n anc f₂ with hs₂
  have hdvd : (2 ^ m) ∣ (2 ^ m * 2 ^ n * 2 ^ anc) := ⟨2 ^ n * 2 ^ anc, by ring⟩
  -- expand the difference of the two success sums into one indexed difference
  have hdecomp : probability_of_success a r N m n anc f₁
      - probability_of_success a r N m n anc f₂
      = ∑ x ∈ Finset.range (2 ^ m),
          r_found x m r a N *
            (prob_partial_meas (basis_vector (2 ^ m) x) s₁
              - prob_partial_meas (basis_vector (2 ^ m) x) s₂) := by
    unfold probability_of_success
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [← hs₁, ← hs₂]; ring
  rw [hdecomp]
  -- triangle inequality, then convert the range-sum into a Fin (2^m)-sum
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [← Fin.sum_univ_eq_sum_range
    (fun x => |r_found x m r a N *
          (prob_partial_meas (basis_vector (2 ^ m) x) s₁
            - prob_partial_meas (basis_vector (2 ^ m) x) s₂)|) (2 ^ m)]
  -- per-outcome bound (dropping the {0,1} indicator `r_found ≤ 1`)
  refine le_trans (Finset.sum_le_sum (g := fun x : Fin (2 ^ m) =>
      ∑ y : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m),
        |Complex.normSq (s₁ (jointIdx hdvd x y) 0)
          - Complex.normSq (s₂ (jointIdx hdvd x y) 0)|) ?_) ?_
  · intro x _
    rw [abs_mul, abs_of_nonneg (r_found_nonneg x.val m r a N)]
    calc r_found x.val m r a N *
            |prob_partial_meas (basis_vector (2 ^ m) x.val) s₁
              - prob_partial_meas (basis_vector (2 ^ m) x.val) s₂|
        ≤ 1 * |prob_partial_meas (basis_vector (2 ^ m) x.val) s₁
              - prob_partial_meas (basis_vector (2 ^ m) x.val) s₂| :=
          mul_le_mul_of_nonneg_right (r_found_le_one _ _ _ _ _) (abs_nonneg _)
      _ = |prob_partial_meas (basis_vector (2 ^ m) x.val) s₁
              - prob_partial_meas (basis_vector (2 ^ m) x.val) s₂| := one_mul _
      _ ≤ _ := prob_partial_meas_basis_sub_abs_le s₁ s₂ x hdvd
  · -- reindex the double sum to the full register — exactly `normSqDist`
    rw [sum_jointIdx_eq hdvd
      (fun i => |Complex.normSq (s₁ i 0) - Complex.normSq (s₂ i 0)|)]
    rfl

/-! ## §4. Refinement 1 — the amplitude-difference (`ampDist`) bound. -/

/-- Pointwise: `| ‖a‖² − ‖b‖² | ≤ (‖a‖+‖b‖)·‖a−b‖`. -/
theorem normSq_sub_abs_le (a b : ℂ) :
    |Complex.normSq a - Complex.normSq b| ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have h1 : ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) := by ring
  rw [h1, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖a‖ + ‖b‖), mul_comm]
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le a b) (by positivity)

/-- Amplitude distance: `∑_i (‖s₁ᵢ‖+‖s₂ᵢ‖)·‖s₁ᵢ − s₂ᵢ‖`.  The explicit amplitude
    expression dominating `normSqDist`. -/
noncomputable def ampDist {dim : Nat} (s₁ s₂ : QState dim) : ℝ :=
  ∑ i : Fin dim, (‖s₁ i 0‖ + ‖s₂ i 0‖) * ‖s₁ i 0 - s₂ i 0‖

theorem ampDist_nonneg {dim : Nat} (s₁ s₂ : QState dim) : 0 ≤ ampDist s₁ s₂ :=
  Finset.sum_nonneg (fun i _ => by positivity)

/-- `normSqDist ≤ ampDist`, summing the pointwise bound. -/
theorem normSqDist_le_ampDist {dim : Nat} (s₁ s₂ : QState dim) :
    normSqDist s₁ s₂ ≤ ampDist s₁ s₂ := by
  unfold normSqDist ampDist
  exact Finset.sum_le_sum (fun i _ => normSq_sub_abs_le (s₁ i 0) (s₂ i 0))

/-- **GAP 5 — amplitude-difference form.**  `|Δ prob_success| ≤ ampDist`. -/
theorem prob_of_success_transfer_ampDist
    (a r N m n anc : Nat) (f₁ f₂ : Nat → BaseUCom (n + anc)) :
    |probability_of_success a r N m n anc f₁
        - probability_of_success a r N m n anc f₂|
      ≤ ampDist (Shor_final_state m n anc f₁) (Shor_final_state m n anc f₂) :=
  le_trans (prob_of_success_transfer_normSqDist a r N m n anc f₁ f₂)
    (normSqDist_le_ampDist _ _)

/-! ## §5. Refinement 2 — the L2 (Euclidean / Frobenius) `C = 2` bound. -/

/-- Discrete Cauchy–Schwarz: `∑ fᵢ gᵢ ≤ √(∑ fᵢ²)·√(∑ gᵢ²)` for nonneg `f, g`. -/
theorem sum_mul_le_sqrt_mul_sqrt {dim : Nat} (f g : Fin dim → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, f i * g i ≤ Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hnn : 0 ≤ ∑ i, f i * g i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hf i) (hg i))
  rw [← Real.sqrt_mul (by positivity)]
  exact (Real.le_sqrt hnn (by positivity)).mpr hcs

/-- Discrete Minkowski (`p = 2`): `√(∑(fᵢ+gᵢ)²) ≤ √(∑fᵢ²) + √(∑gᵢ²)`. -/
theorem sqrt_sum_add_sq_le {dim : Nat} (f g : Fin dim → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    Real.sqrt (∑ i, (f i + g i) ^ 2)
      ≤ Real.sqrt (∑ i, f i ^ 2) + Real.sqrt (∑ i, g i ^ 2) := by
  have hmink := Real.Lp_add_le_of_nonneg Finset.univ (p := 2) (by norm_num)
    (fun i _ => hf i) (fun i _ => hg i)
  simp only [Real.rpow_two, one_div] at hmink
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  convert hmink using 2 <;> norm_num

/-- L2 (Euclidean / Frobenius) norm of a state vector: `√(∑_i ‖s_i‖²)`. -/
noncomputable def l2norm {dim : Nat} (s : QState dim) : ℝ :=
  Real.sqrt (∑ i : Fin dim, ‖s i 0‖ ^ 2)

/-- L2 distance between two state vectors: `√(∑_i ‖s₁_i − s₂_i‖²)`. -/
noncomputable def l2dist {dim : Nat} (s₁ s₂ : QState dim) : ℝ :=
  Real.sqrt (∑ i : Fin dim, ‖s₁ i 0 - s₂ i 0‖ ^ 2)

theorem l2norm_nonneg {dim : Nat} (s : QState dim) : 0 ≤ l2norm s :=
  Real.sqrt_nonneg _

theorem l2dist_nonneg {dim : Nat} (s₁ s₂ : QState dim) : 0 ≤ l2dist s₁ s₂ :=
  Real.sqrt_nonneg _

/-- The amplitude distance is bounded by `(‖s₁‖₂ + ‖s₂‖₂)·‖s₁−s₂‖₂`
    (Cauchy–Schwarz on the two factor-sequences, then Minkowski on the first). -/
theorem ampDist_le_l2 {dim : Nat} (s₁ s₂ : QState dim) :
    ampDist s₁ s₂ ≤ (l2norm s₁ + l2norm s₂) * l2dist s₁ s₂ := by
  unfold ampDist l2norm l2dist
  refine le_trans (sum_mul_le_sqrt_mul_sqrt
    (fun i => ‖s₁ i 0‖ + ‖s₂ i 0‖) (fun i => ‖s₁ i 0 - s₂ i 0‖)
    (fun i => by positivity) (fun i => norm_nonneg _)) ?_
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact sqrt_sum_add_sq_le (fun i => ‖s₁ i 0‖) (fun i => ‖s₂ i 0‖)
    (fun i => norm_nonneg _) (fun i => norm_nonneg _)

/-- **GAP 5 — L2 / `C = 2` form (headline).**  For pure (L2-normalized)
    post-circuit states, the success probabilities differ by at most
    `2 · ‖s₁ − s₂‖₂`.  This is the Born-rule/Cauchy–Schwarz Lipschitz constant
    `C = 2`. -/
theorem prob_of_success_transfer_l2
    (a r N m n anc : Nat) (f₁ f₂ : Nat → BaseUCom (n + anc))
    (h₁ : l2norm (Shor_final_state m n anc f₁) ≤ 1)
    (h₂ : l2norm (Shor_final_state m n anc f₂) ≤ 1) :
    |probability_of_success a r N m n anc f₁
        - probability_of_success a r N m n anc f₂|
      ≤ 2 * l2dist (Shor_final_state m n anc f₁) (Shor_final_state m n anc f₂) := by
  set s₁ := Shor_final_state m n anc f₁
  set s₂ := Shor_final_state m n anc f₂
  refine le_trans (prob_of_success_transfer_ampDist a r N m n anc f₁ f₂) ?_
  refine le_trans (ampDist_le_l2 s₁ s₂) ?_
  apply mul_le_mul_of_nonneg_right _ (l2dist_nonneg s₁ s₂)
  linarith [h₁, h₂]

/-! ## §6. Composition with the AQFT (ε-close) error budget. -/

/-- **AQFT-budget composition.**  Given (i) the verified ideal lower bound
    `probability_of_success(f_ideal) ≥ P_ideal` and (ii) an ε-bound on the L2
    distance between the AQFT/PPM-compiled final state and the ideal one (with
    both states L2-normalized), the compiled circuit succeeds with probability

        probability_of_success(f_compiled) ≥ P_ideal − 2·ε.

    Here `f_ideal` is the exact-arithmetic oracle family and `f_compiled` the
    one whose `Shor_final_state` is ε-close (the AQFT geometric-tail budget
    `ApproxQFT.aqft_ladder_error_budget` supplies such an ε at the circuit
    layer).  Combined with `VerifiedShor`'s `P_ideal = κ/(log₂N)⁴`, this is

        probability_of_success(PPM-compiled) ≥ κ/(log₂N)⁴ − 2·ε. -/
theorem aqft_transfer_compose
    (a r N m n anc : Nat)
    (f_ideal f_compiled : Nat → BaseUCom (n + anc))
    (P_ideal ε : ℝ)
    (h_ideal : probability_of_success a r N m n anc f_ideal ≥ P_ideal)
    (h_norm_ideal : l2norm (Shor_final_state m n anc f_ideal) ≤ 1)
    (h_norm_comp : l2norm (Shor_final_state m n anc f_compiled) ≤ 1)
    (h_close : l2dist (Shor_final_state m n anc f_compiled)
                      (Shor_final_state m n anc f_ideal) ≤ ε) :
    probability_of_success a r N m n anc f_compiled ≥ P_ideal - 2 * ε := by
  have htrans := prob_of_success_transfer_l2 a r N m n anc
    f_compiled f_ideal h_norm_comp h_norm_ideal
  -- |P(compiled) − P(ideal)| ≤ 2·l2dist ≤ 2·ε  ⇒  P(compiled) ≥ P(ideal) − 2ε
  have hle : |probability_of_success a r N m n anc f_compiled
        - probability_of_success a r N m n anc f_ideal| ≤ 2 * ε := by
    refine le_trans htrans ?_
    have hεnn : 0 ≤ ε := le_trans (l2dist_nonneg _ _) h_close
    nlinarith [h_close, l2dist_nonneg (Shor_final_state m n anc f_compiled)
      (Shor_final_state m n anc f_ideal)]
  have hsub := abs_le.mp hle
  linarith [hsub.1, h_ideal]

end FormalRV.SQIRPort.ApproxTransfer
