/-
  FormalRV.Shor.CosetEigenstate.BranchFactor — the REUSABLE control×data branch
  factorization over an ARBITRARY product equiv (the layout bridge, made explicit).
  ════════════════════════════════════════════════════════════════════════════

  `ControlledLift` factors a register `Fin full_dim` into a control factor `Fin m_dim`
  and a data factor `Fin (full_dim/m_dim)` through the SPECIFIC contiguous index
  `jointIdx h x y = x·(full/m)+y` (control = high digit, data = low digit), and uses
  it ONLY through its bijection property (`sum_jointIdx_eq` = `Equiv.sum_comp`).

  But a real circuit's data register (e.g. a windowed multiplier's ACCUMULATOR) sits
  at SCATTERED qubit positions — the flat `funbool`/`uc_eval` index is NOT contiguous
  control-high/data-low, so it does not match `jointIdx`.  Rather than relabel qubits
  (which would need a qubit-position-permutation marginal-invariance lemma that does not
  exist), we GENERALIZE the factorization to an arbitrary product equiv

      e : Fin m × Fin d ≃ Fin full        (`branchOfE e s x = fun y => s (e (x,y))`)

  so a circuit's NATURAL qubit-block factorization (read the data qubits as the data
  value, the rest as the control value) feeds the deviation engine DIRECTLY, with no
  relabel and no funbool-after-permutation arithmetic.  Everything `ControlledLift`
  proves holds for any `e` (the only register fact used is that `e` is a bijection,
  `Equiv.sum_comp`).  The contiguous `jointIdx` case is recovered as the
  `e := jointEquiv h` instance (`branchOf_eq_branchOfE`), so the existing engine and
  capstone are unaffected.

  This is the reusable, explicit layout bridge — useful again for controlled oracles,
  `jointIdx`, and QPE staging.  It deliberately does NOT mention any multiplier.

    * `branchOfE e s x` — the data substate of `s` in control branch `x` under `e`.
    * `sum_prodEquiv_eq` / `normSqDist_branchOfE_decomp` — the Born-L1 distance splits
      as a SUM over control branches (the bijection fact).
    * `normSqDist_branchOfE_controlled_lift{,_weighted,_subnormalized}` — the controlled
      lifts (agree off-active ⇒ 0; sub-normalized control ⇒ single-branch bound `D`).
    * `jointEquiv h` + `branchOf_eq_branchOfE` — `jointIdx`/`branchOf` is the contiguous
      instance, so this strictly generalizes `ControlledLift`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.ControlledLift

namespace FormalRV.Shor.CosetEigenstate.BranchFactor

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetEigenstate.ControlledLift (normSqDist_smul branchOf)

/-! ## §1. The data substate under an arbitrary product factorization. -/

/-- The data substate of `s` in control branch `x`, under the product factorization
    `e : Fin m × Fin d ≃ Fin full`: the slice `y ↦ ⟨e (x,y) | s⟩`. -/
noncomputable def branchOfE {m d full : Nat} (e : Fin m × Fin d ≃ Fin full)
    (s : QState full) (x : Fin m) : QState d :=
  fun y _ => s (e (x, y)) 0

/-- **Summation reindex through a product equiv.**  `∑ₓ ∑_y g(e (x,y)) = ∑ᵢ g i`
    — the only register fact the branch decomposition needs (that `e` is a bijection). -/
theorem sum_prodEquiv_eq {m d full : Nat} (e : Fin m × Fin d ≃ Fin full)
    (g : Fin full → ℝ) :
    ∑ x : Fin m, ∑ y : Fin d, g (e (x, y)) = ∑ i : Fin full, g i := by
  rw [← Equiv.sum_comp e g, Fintype.sum_prod_type]

/-! ## §2. Branch decomposition and the controlled lifts (mirror `ControlledLift`). -/

/-- **Branch decomposition of `normSqDist` (general factorization).**  The control
    register is preserved, so the Born-L1 distance splits as a SUM over control
    branches of the per-branch distance. -/
theorem normSqDist_branchOfE_decomp {m d full : Nat} (e : Fin m × Fin d ≃ Fin full)
    (s₁ s₂ : QState full) :
    normSqDist s₁ s₂
      = ∑ x : Fin m, normSqDist (branchOfE e s₁ x) (branchOfE e s₂ x) := by
  unfold normSqDist branchOfE
  rw [← sum_prodEquiv_eq e (fun i => |Complex.normSq (s₁ i 0) - Complex.normSq (s₂ i 0)|)]

/-- **Controlled-branch lifting (general factorization).**  Off-active branches agree
    (contribute 0); active branches contribute at most `d x`. -/
theorem normSqDist_branchOfE_controlled_lift {m d full : Nat} (e : Fin m × Fin d ≃ Fin full)
    (s₁ s₂ : QState full) (active : Finset (Fin m)) (dd : Fin m → ℝ)
    (hzero : ∀ x, x ∉ active → branchOfE e s₁ x = branchOfE e s₂ x)
    (hactive : ∀ x, x ∈ active → normSqDist (branchOfE e s₁ x) (branchOfE e s₂ x) ≤ dd x) :
    normSqDist s₁ s₂ ≤ ∑ x ∈ active, dd x := by
  rw [normSqDist_branchOfE_decomp e s₁ s₂,
      ← Finset.sum_subset (Finset.subset_univ active)
        (fun x _ hx => by rw [hzero x hx]; unfold normSqDist; simp)]
  exact Finset.sum_le_sum (fun x hx => hactive x hx)

/-- **Weighted-sum lift (general factorization).**  Each active branch is a common
    amplitude `β x` times a normalized data-state pair of deviation `≤ D`. -/
theorem normSqDist_branchOfE_controlled_lift_weighted {m d full : Nat}
    (e : Fin m × Fin d ≃ Fin full)
    (s₁ s₂ : QState full) (active : Finset (Fin m)) (β : Fin m → ℂ) (D : ℝ)
    (a₁ a₂ : Fin m → QState d)
    (hzero : ∀ x, x ∉ active → branchOfE e s₁ x = branchOfE e s₂ x)
    (hfac₁ : ∀ x, x ∈ active → branchOfE e s₁ x = fun i z => β x * a₁ x i z)
    (hfac₂ : ∀ x, x ∈ active → branchOfE e s₂ x = fun i z => β x * a₂ x i z)
    (hdev : ∀ x, x ∈ active → normSqDist (a₁ x) (a₂ x) ≤ D) :
    normSqDist s₁ s₂ ≤ D * ∑ x ∈ active, Complex.normSq (β x) := by
  have key : normSqDist s₁ s₂ ≤ ∑ x ∈ active, Complex.normSq (β x) * D := by
    refine normSqDist_branchOfE_controlled_lift e s₁ s₂ active
      (fun x => Complex.normSq (β x) * D) hzero (fun x hx => ?_)
    rw [hfac₁ x hx, hfac₂ x hx, normSqDist_smul]
    exact mul_le_mul_of_nonneg_left (hdev x hx) (Complex.normSq_nonneg (β x))
  calc normSqDist s₁ s₂ ≤ ∑ x ∈ active, Complex.normSq (β x) * D := key
    _ = D * ∑ x ∈ active, Complex.normSq (β x) := by rw [← Finset.sum_mul]; ring

/-- **Sub-normalized corollary (general factorization).**  Active branches carry total
    probability `≤ 1` ⇒ the deviation is at most the single-branch bound `D`. -/
theorem normSqDist_branchOfE_controlled_lift_subnormalized {m d full : Nat}
    (e : Fin m × Fin d ≃ Fin full)
    (s₁ s₂ : QState full) (active : Finset (Fin m)) (β : Fin m → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (a₁ a₂ : Fin m → QState d)
    (hzero : ∀ x, x ∉ active → branchOfE e s₁ x = branchOfE e s₂ x)
    (hfac₁ : ∀ x, x ∈ active → branchOfE e s₁ x = fun i z => β x * a₁ x i z)
    (hfac₂ : ∀ x, x ∈ active → branchOfE e s₂ x = fun i z => β x * a₂ x i z)
    (hdev : ∀ x, x ∈ active → normSqDist (a₁ x) (a₂ x) ≤ D)
    (hweight : ∑ x ∈ active, Complex.normSq (β x) ≤ 1) :
    normSqDist s₁ s₂ ≤ D := by
  calc normSqDist s₁ s₂
      ≤ D * ∑ x ∈ active, Complex.normSq (β x) :=
        normSqDist_branchOfE_controlled_lift_weighted e s₁ s₂ active β D a₁ a₂
          hzero hfac₁ hfac₂ hdev
    _ ≤ D * 1 := mul_le_mul_of_nonneg_left hweight hD
    _ = D := mul_one D

/-! ## §3. The contiguous `jointIdx` case is the `jointEquiv h` instance. -/

/-- The contiguous product equiv realizing `jointIdx`: `Fin m_dim × Fin (full/m) ≃ Fin full`,
    `(x,y) ↦ x·(full/m)+y`. -/
noncomputable def jointEquiv {m_dim full_dim : Nat} (h : m_dim ∣ full_dim) :
    Fin m_dim × Fin (full_dim / m_dim) ≃ Fin full_dim :=
  finProdFinEquiv.trans (finCongr (Nat.mul_div_cancel' h))

/-- `jointEquiv` applied is exactly `jointIdx`. -/
theorem jointEquiv_apply {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (x : Fin m_dim) (y : Fin (full_dim / m_dim)) :
    jointEquiv h (x, y) = jointIdx h x y := by
  rw [jointEquiv, jointIdx_eq_finProdFinEquiv]
  rfl

/-- **`branchOf` is the `jointEquiv` instance of `branchOfE`.**  So `BranchFactor`
    strictly generalizes `ControlledLift`; everything stated for `branchOf`/`jointIdx`
    is the `e := jointEquiv h` case here. -/
theorem branchOf_eq_branchOfE {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (s : QState full_dim) (x : Fin m_dim) :
    branchOf h s x = branchOfE (jointEquiv h) s x := by
  unfold branchOfE
  funext y z
  show branchOf h s x y z = s (jointEquiv h (x, y)) 0
  rw [jointEquiv_apply]
  rfl

end FormalRV.Shor.CosetEigenstate.BranchFactor
