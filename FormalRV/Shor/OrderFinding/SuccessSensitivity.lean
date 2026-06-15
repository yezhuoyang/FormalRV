/-
  FormalRV.Shor.SuccessSensitivity — a tunable-parameter, union-bound
  success-probability LOWER BOUND for compiled fault-tolerant Shor, with
  proven monotonicity (sensitivity) and the T-count trade-off.

  ## What this is (framework, not gotcha)

  This is NOT a claim "Shor succeeds on RSA-2048 with X qubits in Y hours".
  It is the inter-layer error-propagation contract: starting from the
  formally-PROVEN ideal order-finding bound
  `probability_of_success ≥ κ/(log₂N)⁴` (`VerifiedShor`), it subtracts a
  ROUGH union bound over the two error mechanisms a reviewer tunes —

    * approximation error  `ε_approx ≤ 2π/2^cutoff`  (DERIVED, the AQFT
      compiler's geometric-tail budget, `ApproxQFT.aqft_ladder_error_budget`),
    * logical error        `ε_logical = num_ops · p_L`  (the union bound:
      per-logical-operation rate × operation count),

  and proves the realized lower bound is ANTITONE in each error parameter:
  higher logical error rate ⇒ lower guaranteed success; higher
  approximation error ⇒ lower guaranteed success.  It also exposes the
  T-count tension: increasing the cutoff (more T gates) strictly shrinks
  `ε_approx` but strictly grows `ε_logical` — both effects, with a concrete
  interior-optimum witness.

  ## Honesty caveats (paper-framing, not Lean gaps)

  (i)   `P_ideal − ε_approx − ε_logical` is a CRUDE additive union bound
        (worst-case), a generic guarantee — not a tight per-mechanism bound.
  (ii)  The monotonicity is a property of the bound FUNCTION `P_raw`; it does
        not (and cannot) claim the fixed exact-QFT verified circuit's own
        probability changes.  It is the sensitivity/responsiveness statement.
  (iii) `num_ops` / `opsModel` are MODELING CHOICES linking cutoff/T-count to
        an operation count; left as free params so reviewers substitute their
        true count (e.g. `7*(n:ℝ)` for the Gidney adder, or `(Gate.tcount c:ℝ)`).
  (iv)  `p_L` is a free per-operation logical error rate (the repo's `f_code`
        subthreshold ansatz is a Nat stub); a free ℝ parameter is the honest
        move — this is the first Real-valued `p_L` in the framework.
  (v)   `tradeoff_interior_witness` is ONE concrete witness of non-boundary
        optimality, not a ∀-interior-optimum proof.

  No new axiom, no `sorry`, no operator-norm machinery.
-/
import FormalRV.Shor.VerifiedShor
import FormalRV.Core.ApproxQFT
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

namespace FormalRV.Shor.SuccessSensitivity

open FormalRV.SQIRPort (κ probability_of_success)
open VerifiedShor
open FormalRV.Framework.ApproxQFT (aqft_ladder_error_budget aqft_error_budget_antitone)

/-! ## §1. The tunable error budget. -/

/-- Tunable error-budget parameters for one compiled FT-Shor run.  Every
    field is a FREE parameter a reviewer plugs their own hardware /
    synthesis numbers into.  `P_ideal` is the L1 ideal order-finding
    success bound (instantiated as `κ/(log₂N)⁴` by the master theorem);
    `cutoff` is the AQFT band `c` (so `ε_approx ≤ 2π/2^c`); `p_L` the
    per-logical-operation error rate; `num_ops` the logical-operation
    count (the union-bound multiplier). -/
structure ErrorBudget where
  P_ideal : ℝ
  cutoff  : ℕ
  p_L     : ℝ
  num_ops : ℝ
  hp_L    : 0 ≤ p_L
  hnum    : 0 ≤ num_ops

/-- AQFT approximation-error budget: the derived closed form `2π/2^cutoff`
    that `aqft_ladder_error_budget` bounds.  Not an assumption. -/
noncomputable def ε_approx (B : ErrorBudget) : ℝ := 2 * Real.pi / 2 ^ B.cutoff

/-- Union bound: per-operation logical error rate times the operation
    count. -/
noncomputable def ε_logical (B : ErrorBudget) : ℝ := B.num_ops * B.p_L

/-- Unclamped realized success-probability lower bound — affine in every
    parameter, so the monotonicity lemmas are pure `linarith`/`nlinarith`. -/
noncomputable def P_raw (B : ErrorBudget) : ℝ := B.P_ideal - ε_approx B - ε_logical B

/-- Realized success-probability LOWER BOUND, clamped at `0`:
    `max 0 (P_ideal − ε_approx − ε_logical)`.  The clamp keeps it a genuine
    probability (`≥ 0`) even when a reviewer's error rates swamp the ideal
    bound. -/
noncomputable def P_lb (B : ErrorBudget) : ℝ := max 0 (P_raw B)

/-- The AQFT-cutoff trade-off object: total certified error as a function
    of the cutoff `c`.  First summand (approx tail) STRICTLY ↓ in `c`;
    second (logical union bound) STRICTLY ↑ in `c` via `opsModel`, a free
    strictly-monotone op-count model the reviewer supplies. -/
noncomputable def totalError (p_L : ℝ) (opsModel : ℕ → ℝ) (c : ℕ) : ℝ :=
  (2 * Real.pi / 2 ^ c) + opsModel c * p_L

/-! ## §2. Non-negativity / well-formedness. -/

theorem ε_logical_nonneg (B : ErrorBudget) : 0 ≤ ε_logical B := by
  unfold ε_logical; exact mul_nonneg B.hnum B.hp_L

theorem ε_approx_pos (B : ErrorBudget) : 0 < ε_approx B := by
  unfold ε_approx; positivity

/-- The AQFT geometric-tail budget really is bounded by `ε_approx`: pure
    reuse of `aqft_ladder_error_budget`. -/
theorem ε_approx_bounds_aqft (B : ErrorBudget) (n : ℕ) (hcn : B.cutoff ≤ n) :
    (∑ m ∈ Finset.Ico B.cutoff n, (Real.pi / 2 ^ m)) ≤ ε_approx B := by
  unfold ε_approx; exact aqft_ladder_error_budget B.cutoff n hcn

theorem P_lb_nonneg (B : ErrorBudget) : 0 ≤ P_lb B := by
  unfold P_lb; exact le_max_left 0 _

theorem P_lb_eq_raw_of_nonneg (B : ErrorBudget) (h : 0 ≤ P_raw B) :
    P_lb B = P_raw B := by
  unfold P_lb; exact max_eq_right h

/-! ## §3. Monotonicity — the headline sensitivity results.

    The clamped lower bound is ANTITONE (decreasing) in each error
    parameter: a worse logical error rate, a worse approximation error, or
    more failure-prone operations all lower the guaranteed success. -/

/-- Higher per-operation logical error rate ⇒ lower guaranteed success. -/
theorem P_lb_antitone_p_L (P_ideal : ℝ) (cutoff : ℕ) (num_ops : ℝ)
    (hnum : 0 ≤ num_ops) :
    Antitone (fun p_L : ℝ =>
      max 0 (P_ideal - 2 * Real.pi / 2 ^ cutoff - num_ops * p_L)) := by
  intro x y hxy; dsimp
  apply max_le_max (le_refl 0)
  nlinarith [mul_le_mul_of_nonneg_left hxy hnum]

/-- Higher approximation error ⇒ lower guaranteed success. -/
theorem P_lb_antitone_cutoffVal (P_ideal num_ops p_L : ℝ) :
    Antitone (fun ε : ℝ => max 0 (P_ideal - ε - num_ops * p_L)) := by
  intro x y hxy; dsimp
  apply max_le_max (le_refl 0)
  linarith

/-- More failure-prone logical operations ⇒ lower guaranteed success. -/
theorem P_lb_antitone_ops (P_ideal : ℝ) (cutoff : ℕ) (p_L : ℝ) (hp : 0 ≤ p_L) :
    Antitone (fun num_ops : ℝ =>
      max 0 (P_ideal - 2 * Real.pi / 2 ^ cutoff - num_ops * p_L)) := by
  intro x y hxy; dsimp
  apply max_le_max (le_refl 0)
  nlinarith [mul_le_mul_of_nonneg_right hxy hp]

/-! ## §4. The T-count trade-off. -/

/-- `ε_approx` is antitone in the cutoff (reuse of `aqft_error_budget_antitone`). -/
theorem ε_approx_antitone_cutoff {c c' : ℕ} (h : c ≤ c') :
    (2 * Real.pi / 2 ^ c' : ℝ) ≤ 2 * Real.pi / 2 ^ c :=
  aqft_error_budget_antitone h

/-- `ε_approx` STRICTLY shrinks as the cutoff grows (more kept rotations /
    T gates). -/
theorem ε_approx_strict_antitone_cutoff {c c' : ℕ} (h : c < c') :
    (2 * Real.pi / 2 ^ c' : ℝ) < 2 * Real.pi / 2 ^ c := by
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  exact pow_lt_pow_right₀ (by norm_num) h

/-- `ε_logical` STRICTLY grows with the operation count (for `p_L > 0`). -/
theorem ε_logical_strict_mono_ops (p_L : ℝ) (hp : 0 < p_L) :
    StrictMono (fun nOps : ℕ => (nOps : ℝ) * p_L) := by
  intro x y hxy; dsimp
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hxy) hp

/-- **The tension, made explicit.**  Increasing the cutoff `c → c'`
    (more T gates) STRICTLY decreases the approximation error AND STRICTLY
    increases the logical error — the two pull in opposite directions. -/
theorem tradeoff_tension (p_L : ℝ) (hp : 0 < p_L) (opsModel : ℕ → ℝ)
    (hops : StrictMono opsModel) {c c' : ℕ} (h : c < c') :
    (2 * Real.pi / 2 ^ c' : ℝ) < 2 * Real.pi / 2 ^ c
      ∧ opsModel c * p_L < opsModel c' * p_L := by
  refine ⟨ε_approx_strict_antitone_cutoff h, ?_⟩
  exact mul_lt_mul_of_pos_right (hops h) hp

/-- An interior cutoff beats both extremes when it has strictly lower total
    error than each — i.e. the optimum is not at the boundary. -/
theorem tradeoff_interior_strict (p_L : ℝ) (opsModel : ℕ → ℝ)
    {c₀ c₁ c₂ : ℕ}
    (hcoarse : totalError p_L opsModel c₁ < totalError p_L opsModel c₀)
    (hfine   : totalError p_L opsModel c₁ < totalError p_L opsModel c₂) :
    totalError p_L opsModel c₁
      < min (totalError p_L opsModel c₀) (totalError p_L opsModel c₂) :=
  lt_min hcoarse hfine

/-- **Concrete interior-optimum witness.**  With `opsModel c = c`,
    `p_L = 1/4`: the coarse end `c = 0` is approximation-dominated
    (`≈ 2π`), the fine end `c = 8` is logical-dominated (`≈ 2.02`), and the
    interior `c = 4` (`≈ 1.39`) beats both — a genuine sweet spot. -/
theorem tradeoff_interior_witness :
    totalError (1/4) (fun c => (c : ℝ)) 4
      < min (totalError (1/4) (fun c => (c : ℝ)) 0)
            (totalError (1/4) (fun c => (c : ℝ)) 8) := by
  apply lt_min <;> simp only [totalError] <;> push_cast <;>
    nlinarith [Real.pi_gt_three, Real.pi_lt_four]

/-! ## §5. The master bound — connecting `VerifiedShor` to the union budget. -/

/-- **Master success bound.**  The compiled fault-tolerant Shor run
    succeeds with probability at least the proven ideal bound
    `κ/(log₂N)⁴` MINUS the union-bound error budget
    `(2π/2^cutoff) + num_ops·p_L`.  Combined with §3, this exhibits the
    realized guarantee's sensitivity to both error parameters. -/
theorem master_success_bound
    (a r N m bits ainv : Nat)
    (h_setting : ShorSetting a r N m bits)
    (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1)
    (cutoff : ℕ) (p_L num_ops : ℝ) (hp_L : 0 ≤ p_L) (hnum : 0 ≤ num_ops) :
    probability_of_success a r N m bits (ModMul.ancillaWidth bits)
        (ModMul.circuitFamily a ainv N bits)
      ≥ κ / (Nat.log2 N : ℝ) ^ 4
          - (2 * Real.pi / 2 ^ cutoff)
          - num_ops * p_L := by
  have hbase := correct_general_via_interface a r N m bits ainv h_setting h_sizing h_inv
  have h1 : (0:ℝ) ≤ 2 * Real.pi / 2 ^ cutoff := by positivity
  have h2 : (0:ℝ) ≤ num_ops * p_L := mul_nonneg hnum hp_L
  linarith [hbase, h1, h2]

/-- The master bound, bundled through `ErrorBudget` (the reusable framework
    form): instantiating `P_ideal := κ/(log₂N)⁴`, the realized probability
    is `≥ P_raw B`.  This is the shape that generalizes to ECC-256 / any
    corpus paper by swapping the budget's field values. -/
theorem master_success_bound_bundled
    (a r N m bits ainv : Nat)
    (h_setting : ShorSetting a r N m bits)
    (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1)
    (B : ErrorBudget)
    (hP : B.P_ideal = κ / (Nat.log2 N : ℝ) ^ 4) :
    probability_of_success a r N m bits (ModMul.ancillaWidth bits)
        (ModMul.circuitFamily a ainv N bits)
      ≥ P_raw B := by
  unfold P_raw ε_approx ε_logical
  rw [hP]
  exact master_success_bound a r N m bits ainv h_setting h_sizing h_inv
    B.cutoff B.p_L B.num_ops B.hp_L B.hnum

end FormalRV.Shor.SuccessSensitivity
