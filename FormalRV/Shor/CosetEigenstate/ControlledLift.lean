/-
  FormalRV.Shor.CosetEigenstate.ControlledLift — the controlled-branch lifting:
  from a per-branch (classical control) deviation to a superposition bound.
  ════════════════════════════════════════════════════════════════════════════

  The windowed coset multiplier is a fold of CONTROLLED additions: each step adds a
  constant into the accumulator IF a control qubit (a bit of the multiplier /
  exponent) is set.  The control register is in superposition, so we must lift the
  single-branch addition deviation (`cosetState_addConst_deviation`) to ARBITRARY
  superpositions over the control register — correctness on quantum superpositions,
  not only classical basis controls.

  This file makes that precise via the repo's existing tensor/branch decomposition
  (`jointIdx`, `sum_jointIdx_eq`), which is exactly the structure to split a
  register into a preserved control factor and a data factor:

    * `branchOf h s x` — the data substate of `s` in the classical control branch
      `x` (the slice `y ↦ ⟨jointIdx x y | s⟩`).
    * `normSqDist_branch_decomp` — `normSqDist` is the SUM over control branches of
      the per-branch `normSqDist`.  The control register is preserved by a
      controlled op, so the Born-L1 distance splits cleanly along it.
    * `normSqDist_controlled_lift` — control=0 branches (`x ∉ active`) where the two
      states AGREE contribute ZERO; control=1 branches (`x ∈ active`) contribute at
      most their per-branch bound `d x`; so the whole-register deviation is at most
      `∑_{x ∈ active} d x`.
    * `normSqDist_smul` — Born-L1 distance scales by `‖β‖²` under a common branch
      amplitude `β`.
    * `normSqDist_controlled_lift_weighted` — the WEIGHTED-SUM lift: each active
      branch is `β x` times a normalized coset-state pair of deviation `≤ D`, so the
      total is `≤ D·∑_{active}‖β x‖²`; with `∑‖β x‖² ≤ 1` (a sub-normalized control)
      this is `≤ D` — the single-branch bound, UNCHANGED by superposition.

  Specialization: the per-branch states fed in are coset-encoded data branches (the
  windowed-multiplier invariant); `normSqDist_branch_decomp` /
  `normSqDist_controlled_lift` themselves hold for arbitrary branch states (a clean
  general block Born-L1 fact), and the coset structure enters only through the
  per-branch deviation hypotheses `d x` (discharged by `cosetState_addConst_deviation`).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.ApproxOp

namespace FormalRV.Shor.CosetEigenstate.ControlledLift

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer

/-- The data substate of `s` in the classical control branch `x`: the slice
    `y ↦ ⟨jointIdx x y | s⟩`.  `full_dim` factors as (control `m_dim`)·(data
    `full_dim/m_dim`) via `h`. -/
noncomputable def branchOf {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (s : QState full_dim) (x : Fin m_dim) : QState (full_dim / m_dim) :=
  fun y _ => s (jointIdx h x y) 0

/-- **Branch decomposition of `normSqDist`.**  The control register is preserved by
    a controlled op, so the Born-L1 distance splits as a SUM over control branches
    of the per-branch distance.  (`sum_jointIdx_eq` applied to the L1 summand.) -/
theorem normSqDist_branch_decomp {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (s₁ s₂ : QState full_dim) :
    normSqDist s₁ s₂
      = ∑ x : Fin m_dim, normSqDist (branchOf h s₁ x) (branchOf h s₂ x) := by
  unfold normSqDist branchOf
  rw [← sum_jointIdx_eq h (fun i => |Complex.normSq (s₁ i 0) - Complex.normSq (s₂ i 0)|)]

/-- **The controlled-branch lifting (precise).**  Decompose by classical control
    branch.  On the control=0 branches (`x ∉ active`) the actual and ideal states
    AGREE, contributing ZERO.  On the control=1 branches (`x ∈ active`) the
    per-branch deviation is at most `d x`.  Hence the whole-register Born-L1
    deviation is at most `∑_{x ∈ active} d x`. -/
theorem normSqDist_controlled_lift {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (s₁ s₂ : QState full_dim) (active : Finset (Fin m_dim)) (d : Fin m_dim → ℝ)
    (hzero : ∀ x, x ∉ active → branchOf h s₁ x = branchOf h s₂ x)
    (hactive : ∀ x, x ∈ active → normSqDist (branchOf h s₁ x) (branchOf h s₂ x) ≤ d x) :
    normSqDist s₁ s₂ ≤ ∑ x ∈ active, d x := by
  rw [normSqDist_branch_decomp h s₁ s₂,
      ← Finset.sum_subset (Finset.subset_univ active)
        (fun x _ hx => by rw [hzero x hx]; unfold normSqDist; simp)]
  exact Finset.sum_le_sum (fun x hx => hactive x hx)

/-- **Born-L1 distance scales by `‖β‖²`.**  A common amplitude `β` on both states
    (the weight of a control branch) scales the Born-L1 distance by `‖β‖²`. -/
theorem normSqDist_smul {dim : Nat} (β : ℂ) (s₁ s₂ : QState dim) :
    normSqDist (fun i z => β * s₁ i z) (fun i z => β * s₂ i z)
      = Complex.normSq β * normSqDist s₁ s₂ := by
  unfold normSqDist
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.normSq_mul, Complex.normSq_mul, ← mul_sub, abs_mul,
      abs_of_nonneg (Complex.normSq_nonneg β)]

/-- **The weighted-sum lift (capstone) — superposition correctness.**  If on each
    active control branch `x` the actual/ideal data substates are a common amplitude
    `β x` times a (normalized) coset-state pair whose Born-L1 deviation is `≤ D`, and
    the control=0 branches agree, then the whole-register deviation is
    `≤ D·∑_{x∈active}‖β x‖²`.  With `∑‖β x‖² ≤ 1` (sub-normalized control) this is
    `≤ D` — the single-branch bound, UNCHANGED by superposing over the control. -/
theorem normSqDist_controlled_lift_weighted {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (s₁ s₂ : QState full_dim) (active : Finset (Fin m_dim))
    (β : Fin m_dim → ℂ) (D : ℝ)
    (a₁ a₂ : Fin m_dim → QState (full_dim / m_dim))
    (hzero : ∀ x, x ∉ active → branchOf h s₁ x = branchOf h s₂ x)
    (hfac₁ : ∀ x, x ∈ active → branchOf h s₁ x = fun i z => β x * a₁ x i z)
    (hfac₂ : ∀ x, x ∈ active → branchOf h s₂ x = fun i z => β x * a₂ x i z)
    (hdev : ∀ x, x ∈ active → normSqDist (a₁ x) (a₂ x) ≤ D) :
    normSqDist s₁ s₂ ≤ D * ∑ x ∈ active, Complex.normSq (β x) := by
  have key : normSqDist s₁ s₂ ≤ ∑ x ∈ active, Complex.normSq (β x) * D := by
    refine normSqDist_controlled_lift h s₁ s₂ active
      (fun x => Complex.normSq (β x) * D) hzero (fun x hx => ?_)
    rw [hfac₁ x hx, hfac₂ x hx, normSqDist_smul]
    exact mul_le_mul_of_nonneg_left (hdev x hx) (Complex.normSq_nonneg (β x))
  calc normSqDist s₁ s₂ ≤ ∑ x ∈ active, Complex.normSq (β x) * D := key
    _ = D * ∑ x ∈ active, Complex.normSq (β x) := by rw [← Finset.sum_mul]; ring

/-- **The sub-normalized corollary.**  When the active control branches carry total
    probability `≤ 1`, the controlled op's Born-L1 deviation is at most the
    single-branch bound `D`.  This is the precise sense in which controlling a
    coset addition on a superposition does NOT amplify its deviation. -/
theorem normSqDist_controlled_lift_subnormalized {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (s₁ s₂ : QState full_dim) (active : Finset (Fin m_dim))
    (β : Fin m_dim → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (a₁ a₂ : Fin m_dim → QState (full_dim / m_dim))
    (hzero : ∀ x, x ∉ active → branchOf h s₁ x = branchOf h s₂ x)
    (hfac₁ : ∀ x, x ∈ active → branchOf h s₁ x = fun i z => β x * a₁ x i z)
    (hfac₂ : ∀ x, x ∈ active → branchOf h s₂ x = fun i z => β x * a₂ x i z)
    (hdev : ∀ x, x ∈ active → normSqDist (a₁ x) (a₂ x) ≤ D)
    (hweight : ∑ x ∈ active, Complex.normSq (β x) ≤ 1) :
    normSqDist s₁ s₂ ≤ D := by
  calc normSqDist s₁ s₂
      ≤ D * ∑ x ∈ active, Complex.normSq (β x) :=
        normSqDist_controlled_lift_weighted h s₁ s₂ active β D a₁ a₂ hzero hfac₁ hfac₂ hdev
    _ ≤ D * 1 := mul_le_mul_of_nonneg_left hweight hD
    _ = D := mul_one D

end FormalRV.Shor.CosetEigenstate.ControlledLift
