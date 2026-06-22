/-
  FormalRV.Shor.GidneyInPlace.PmDistTelescope — H1 of the HYBRID / TELESCOPING route.
  ════════════════════════════════════════════════════════════════════════════

  The generic ℓ²-distance telescoping engine for the coset-Shor success bound.

  WHY THIS FILE EXISTS (H0 — the documented blocker).  The EmbedAgreeOff orbit-fold route
  (`coset_route2_success_conditional` / `embedAgreeOff_oracle_step`) is NOT inhabitable
  non-vacuously for the physical in-place gate: its per-step combinator needs
  `hc_local`'s good-set preservation `hwork` at the INCOMING accumulated `B`, which reduces
  (the oracle permutes the data index) to forward-closure `σ(B) ⊆ B`.  The physical bad set
  `inplaceBadSetB = (targetSupp \ σ(goodIn)) ∪ (σ(badIn) \ targetSupp)` is provably NOT
  σ-closed (the `σ(badIn) \ targetSupp` leg has `i = σ(p)` with forward image `σ²(p) ∉ B`),
  and σ-closing it makes the wrap mass `Ω(1)` (`CosetScalingAudit`), i.e. vacuous.  So we do
  NOT patch `hwork`; we change the abstraction.

  THE NEW ROUTE.  Use the genuine ℓ² distance `pmDist` (`Approx.GracefulDegradation`), which
  IS unitary-invariant — so the inverse QFT is harmless (no phase-indexed σ).  Do NOT use
  `normSqDist` (the L1-Born distance `∑|‖s₁ᵢ‖²−‖s₂ᵢ‖²|`): it is only PERMUTATION-invariant
  and cannot telescope through the (non-permutation) inverse-QFT stage.

  THIS FILE (H1) provides:
    • `pmDist_triangle`           — the ℓ² (Minkowski) triangle inequality, via the
                                    `EuclideanSpace` bridge (`toEuc`, `pmDist_eq_dist`);
    • `pmDist_matrix_unitary_invariant` — a unitary matrix preserves `pmDist`;
    • `pmDist_cast`               — `QState.cast` (a `Fin` reindex) preserves `pmDist`;
    • `pmDist_orbit_telescope`    — **H1**: if each actual step `Fa k` is a `pmDist`-isometry
                                    (`hisom`) and the per-step local deviation against the
                                    ideal trajectory is `≤ δ k` (`hlocal`), then the final
                                    deviation is `≤ ∑ δ k`.  Bad-set-free, `hwork`-free;
    • `qpeStageMap_pmDist_isom`   — reduces H1's `hisom` for a QPE oracle stage to a single
                                    per-stage matrix-unitarity hypothesis `hU`.

  The per-step unitary-invariance is taken as the HYPOTHESIS `hisom` (mirroring the existing
  repo pattern `InPlaceCoset.inPlaceMul_deviation_compose`'s `hrev_isom`), isolating the one
  remaining genuinely-new obligation — per-stage matrix unitarity `hU` — for a later brick.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.  Every proof
  was de-risked via parallel `lean_run_code` verification before landing.
-/
import FormalRV.Shor.Approx.GracefulDegradation
import FormalRV.Shor.GidneyInPlace.Primitives.Def.OrbitState
import FormalRV.Shor.GidneyInPlace.QPE.Def.QPEStageDecomp

namespace FormalRV.Shor.Approx

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.Shor.GidneyInPlace.OrbitState (orbitState)

/-! ## §1. `pmDist` is the genuine `EuclideanSpace` (ℓ²) distance — the triangle inequality. -/

/-- Bridge a column-vector state to `EuclideanSpace ℂ (Fin d)`. -/
noncomputable def toEuc {d : Nat} (φ : QState d) : EuclideanSpace ℂ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℂ)).symm (fun i => φ i 0)

/-- `pmDist` is the genuine `EuclideanSpace` (ℓ²) distance of the bridged states. -/
lemma pmDist_eq_dist {d : Nat} (a b : QState d) :
    pmDist a b = dist (toEuc a) (toEuc b) := by
  rw [EuclideanSpace.dist_eq]
  unfold pmDist toEuc
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.dist_eq, Complex.normSq_eq_norm_sq]
  rfl

/-- **ℓ² (Minkowski) triangle inequality** for `pmDist`. -/
theorem pmDist_triangle {d : Nat} (a b c : QState d) :
    pmDist a c ≤ pmDist a b + pmDist b c := by
  rw [pmDist_eq_dist, pmDist_eq_dist, pmDist_eq_dist]
  exact dist_triangle _ _ _

/-! ## §2. Unitary- and cast-invariance of `pmDist`. -/

/-- **A unitary matrix preserves `pmDist`.**  Stated with explicit `Matrix (Fin d) (Fin 1) ℂ`
    column args (the `QState` `def`-wrapper blocks `HMul`/`HSub` instance synthesis). -/
theorem pmDist_matrix_unitary_invariant {d : Nat} (M : Matrix (Fin d) (Fin d) ℂ)
    (hU : M.conjTranspose * M = 1) (v w : Matrix (Fin d) (Fin 1) ℂ) :
    pmDist (M * v) (M * w) = pmDist v w := by
  have colnorm : ∀ (x : Matrix (Fin d) (Fin 1) ℂ),
      ∑ i, Complex.normSq (x i 0) = ((x.conjTranspose * x) 0 0).re := by
    intro x; rw [Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Matrix.conjTranspose_apply,
        show Complex.normSq (x i 0) = (starRingEnd ℂ (x i 0) * x i 0).re from by
          rw [← Complex.normSq_eq_conj_mul_self]; rfl]; rfl
  have key : ∀ (x : Matrix (Fin d) (Fin 1) ℂ),
      ∑ i, Complex.normSq ((M * x) i 0) = ∑ i, Complex.normSq (x i 0) := by
    intro x; rw [colnorm (M * x), colnorm x]; congr 2
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc M.conjTranspose, hU,
        Matrix.one_mul]
  unfold pmDist; congr 1
  have hsub : ∀ i, ((M * v) i 0 - (M * w) i 0) = ((M * (v - w)) i (0 : Fin 1)) := by
    intro i; have : (M * (v - w)) = M * v - M * w := by rw [Matrix.mul_sub]
    rw [this, Matrix.sub_apply]
  have lhs_eq : (∑ i, Complex.normSq ((M * v) i 0 - (M * w) i 0))
      = ∑ i, Complex.normSq ((M * (v - w)) i 0) := by
    apply Finset.sum_congr rfl; intro i _; rw [hsub i]
  rw [lhs_eq, key (v - w)]; apply Finset.sum_congr rfl; intro i _; rw [Matrix.sub_apply]

/-- **`QState.cast` (a `Fin` reindex) preserves `pmDist`.** -/
theorem pmDist_cast {a b : Nat} (h : a = b) (φ ψ : QState a) :
    pmDist (QState.cast h φ) (QState.cast h ψ) = pmDist φ ψ := by
  unfold pmDist QState.cast; congr 1
  apply Fintype.sum_equiv (finCongr h.symm); intro i; rfl

/-! ## §3. H1 — the generic ℓ² telescoping bound. -/

/-- **H1 — generic telescoping deviation bound.**  Given actual step maps `Fa k` that are
    each `pmDist`-isometries (`hisom`) and a per-step local deviation against the ideal
    trajectory `orbitState Fi init` bounded by `δ k` (`hlocal`), the final-state deviation
    between the actual and ideal orbits is at most `∑ δ k`.  No bad sets, no `hwork`, no
    `EmbedAgreeOff`.  The inverse QFT is harmless because `pmDist` is unitary-invariant. -/
theorem pmDist_orbit_telescope {full_dim : Nat}
    (Fa Fi : Nat → QState full_dim → QState full_dim)
    (init : QState full_dim)
    (δ : Nat → ℝ)
    (hisom : ∀ (k : Nat) (a b : QState full_dim), pmDist (Fa k a) (Fa k b) = pmDist a b)
    (hlocal : ∀ (k : Nat),
        pmDist (Fa k (orbitState Fi init k)) (orbitState Fi init (k + 1)) ≤ δ k) :
    ∀ numIter,
      pmDist (orbitState Fa init numIter) (orbitState Fi init numIter)
        ≤ ∑ k ∈ Finset.range numIter, δ k := by
  intro numIter
  induction numIter with
  | zero => simp [orbitState]; rw [pmDist_eq_dist]; simp
  | succ p ih =>
      show pmDist (Fa p (orbitState Fa init p)) (Fi p (orbitState Fi init p))
            ≤ ∑ k ∈ Finset.range (p + 1), δ k
      calc pmDist (Fa p (orbitState Fa init p)) (Fi p (orbitState Fi init p))
          ≤ pmDist (Fa p (orbitState Fa init p)) (Fa p (orbitState Fi init p))
            + pmDist (Fa p (orbitState Fi init p)) (Fi p (orbitState Fi init p)) :=
              pmDist_triangle _ _ _
        _ = pmDist (orbitState Fa init p) (orbitState Fi init p)
            + pmDist (Fa p (orbitState Fi init p)) (Fi p (orbitState Fi init p)) := by
              rw [hisom]
        _ ≤ (∑ k ∈ Finset.range p, δ k) + δ p := by
              apply add_le_add ih; have := hlocal p; simpa [orbitState] using this
        _ = ∑ k ∈ Finset.range (p + 1), δ k := by rw [Finset.sum_range_succ]

/-! ## §4. Reducing H1's `hisom` for a QPE oracle stage to per-stage matrix unitarity.

`qpeStageMap` is `QState.cast`-conjugated `uc_eval` of the stage circuit `qpeStageUCom`.  Both
the cast and the matrix layer preserve `pmDist`, so the whole stage is a `pmDist`-isometry as
soon as the stage's `uc_eval` matrix is unitary.  This isolates the ONE remaining genuinely-new
obligation: per-stage matrix unitarity `hU` (no packaged `WellTyped ⇒ unitary` lemma exists;
the route is the repo `invert` adjoint machinery + a per-constructor induction). -/

/-- **H1's `hisom` for a QPE oracle stage, modulo per-stage matrix unitarity `hU`.** -/
theorem qpeStageMap_pmDist_isom (m n anc : Nat)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc)) (k : Nat)
    (hU : (FormalRV.Framework.uc_eval
              (FormalRV.Shor.GidneyInPlace.QPEStageDecomp.qpeStageUCom m n anc f k)).conjTranspose
            * FormalRV.Framework.uc_eval
              (FormalRV.Shor.GidneyInPlace.QPEStageDecomp.qpeStageUCom m n anc f k) = 1)
    (a b : QState (2 ^ m * 2 ^ n * 2 ^ anc)) :
    pmDist (FormalRV.Shor.GidneyInPlace.QPEStageDecomp.qpeStageMap m n anc f k a)
        (FormalRV.Shor.GidneyInPlace.QPEStageDecomp.qpeStageMap m n anc f k b)
      = pmDist a b := by
  unfold FormalRV.Shor.GidneyInPlace.QPEStageDecomp.qpeStageMap
  rw [pmDist_cast]
  simp only [FormalRV.SQIRPort.uc_eval]
  rw [pmDist_matrix_unitary_invariant _ hU, pmDist_cast]

end FormalRV.Shor.Approx
