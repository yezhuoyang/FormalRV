/-
  FormalRV.Shor.GidneyInPlace.PhaseMarginalLift — the compositional QPE marginal
  lift: phase-only gates preserve the data-register relabel agreement.
  ════════════════════════════════════════════════════════════════════════════

  The SOUND coset-Shor bound (CosetMarginalShorBound) compares the coset and ideal
  families through the PHASE-REGISTER MARGINAL — invariant under any data-register
  relabeling — NOT through the (discredited, Ω(1)) full-state distance.  The frontier
  is `CosetMarginalRelabel.agree`: off a wrap set, the coset final state is the ideal
  final state with the data register relabeled by a permutation `σ`.

  To BUILD that frontier from the per-iterate coset arithmetic, the relabel relation
  must be lifted through the QPE circuit.  This file proves the COMPOSITIONAL core:

    * `phaseMarginal h φ x` — the phase-register Born marginal `∑_y ‖⟨x,y|φ⟩‖²`
      (sums out the data register `y`).
    * `DataRelabelAgree` / `DataRelabelAgreeOff` — `φ₁⟨x,y⟩ = φ₂⟨x, σ y⟩` (everywhere /
      off a data bad set): the coset state is the ideal with data relabeled by `σ`.
    * `phaseMarginal_relabel_invariant` — a relabel agreement ⇒ EQUAL phase marginals.
    * `phaseMarginal_relabel_offBad` — off a data bad set, the marginals differ by at
      most the bad-set Born mass each carries (the bad-mass transfer).
    * `PhaseLocal` / `phaseLocal_preserves_relabel(_off)` — THE KEYSTONE OF THE QPE
      LIFT: a PHASE-ONLY operation (`(Pφ)⟨x,y⟩ = ∑_{x'} M x x' · φ⟨x',y⟩` — acts on the
      phase index, holds the data index `y` fixed; this is what Hadamards / inverse-QFT
      / control-register gates are) PRESERVES the data-relabel agreement.  So every
      phase-register stage of QPE carries the relabel through unchanged; only the
      controlled modular multiplications (the oracle) UPDATE `σ` step by step.

  This reduces the `CosetMarginalRelabel` frontier to the per-oracle data-relabel
  update (the per-multiply exact off-wrap agreement — the runway multiplier's job),
  composed through the phase-local stages by `phaseLocal_preserves_relabel`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.ApproxTransfer

namespace FormalRV.Shor.GidneyInPlace.PhaseMarginalLift

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer

/-- **The phase-register Born marginal.**  Sums the Born mass over the data register
    `y`, leaving the phase-outcome distribution `x ↦ ∑_y ‖⟨x,y|φ⟩‖²` — exactly what
    `probability_of_success` reads (`prob_partial_meas_basis_eq`). -/
noncomputable def phaseMarginal {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (φ : QState full_dim) (x : Fin m_dim) : ℝ :=
  ∑ y : Fin (full_dim / m_dim), Complex.normSq (φ (jointIdx h x y) 0)

/-- **The data-relabel agreement (everywhere).**  `φ₁`'s `⟨x,y⟩` amplitude equals
    `φ₂`'s `⟨x, σ y⟩` amplitude: `φ₁` is `φ₂` with the data register relabeled by `σ`. -/
def DataRelabelAgree {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (φ₁ φ₂ : QState full_dim) (σ : Equiv.Perm (Fin (full_dim / m_dim))) : Prop :=
  ∀ x y, φ₁ (jointIdx h x y) 0 = φ₂ (jointIdx h x (σ y)) 0

/-- The data-relabel agreement OFF a data bad set `badY` (the wrap offsets).  The
    bad set is a single `Finset` in the DATA register — the wrap is a data-register
    phenomenon, independent of the phase outcome `x`; this uniformity is exactly what
    lets a phase-only op (which mixes phase indices) preserve the off-bad agreement. -/
def DataRelabelAgreeOff {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (φ₁ φ₂ : QState full_dim) (σ : Equiv.Perm (Fin (full_dim / m_dim)))
    (badY : Finset (Fin (full_dim / m_dim))) : Prop :=
  ∀ x y, y ∉ badY → φ₁ (jointIdx h x y) 0 = φ₂ (jointIdx h x (σ y)) 0

/-- **Phase marginal is RELABEL-INVARIANT.**  If `φ₁` is `φ₂` data-relabeled by `σ`,
    their phase marginals coincide at every outcome — the data representation cannot
    change the measured phase statistics.  (Reindex by `Equiv.sum_comp`.) -/
theorem phaseMarginal_relabel_invariant {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (φ₁ φ₂ : QState full_dim) (σ : Equiv.Perm (Fin (full_dim / m_dim)))
    (hagree : DataRelabelAgree h φ₁ φ₂ σ) (x : Fin m_dim) :
    phaseMarginal h φ₁ x = phaseMarginal h φ₂ x := by
  unfold phaseMarginal
  calc ∑ y, Complex.normSq (φ₁ (jointIdx h x y) 0)
      = ∑ y, Complex.normSq (φ₂ (jointIdx h x (σ y)) 0) :=
        Finset.sum_congr rfl (fun y _ => by rw [hagree x y])
    _ = ∑ y, Complex.normSq (φ₂ (jointIdx h x y) 0) :=
        Equiv.sum_comp σ (fun y => Complex.normSq (φ₂ (jointIdx h x y) 0))

/-- **Bad-mass transfer.**  If the relabel agreement holds off a finite data bad set
    `badY`, the two phase marginals differ by at most the Born mass each state carries
    on `badY` (the wrap offsets) — the deviation the approximate bound pays. -/
theorem phaseMarginal_relabel_offBad {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (φ₁ φ₂ : QState full_dim) (σ : Equiv.Perm (Fin (full_dim / m_dim)))
    (x : Fin m_dim) (badY : Finset (Fin (full_dim / m_dim)))
    (hagree : ∀ y, y ∉ badY → φ₁ (jointIdx h x y) 0 = φ₂ (jointIdx h x (σ y)) 0) :
    |phaseMarginal h φ₁ x - phaseMarginal h φ₂ x|
      ≤ (∑ y ∈ badY, Complex.normSq (φ₁ (jointIdx h x y) 0))
        + (∑ y ∈ badY, Complex.normSq (φ₂ (jointIdx h x (σ y)) 0)) := by
  have hreindex : phaseMarginal h φ₂ x
      = ∑ y, Complex.normSq (φ₂ (jointIdx h x (σ y)) 0) :=
    (Equiv.sum_comp σ (fun y => Complex.normSq (φ₂ (jointIdx h x y) 0))).symm
  rw [hreindex]
  unfold phaseMarginal
  rw [← Finset.sum_sub_distrib]
  have hvanish : ∀ y ∈ Finset.univ, y ∉ badY →
      Complex.normSq (φ₁ (jointIdx h x y) 0)
        - Complex.normSq (φ₂ (jointIdx h x (σ y)) 0) = 0 :=
    fun y _ hy => by rw [hagree y hy, sub_self]
  rw [← Finset.sum_subset (Finset.subset_univ badY) hvanish]
  calc |∑ y ∈ badY, (Complex.normSq (φ₁ (jointIdx h x y) 0)
          - Complex.normSq (φ₂ (jointIdx h x (σ y)) 0))|
      ≤ ∑ y ∈ badY, |Complex.normSq (φ₁ (jointIdx h x y) 0)
          - Complex.normSq (φ₂ (jointIdx h x (σ y)) 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ badY, (Complex.normSq (φ₁ (jointIdx h x y) 0)
          + Complex.normSq (φ₂ (jointIdx h x (σ y)) 0)) :=
        Finset.sum_le_sum (fun y _ => by
          have ha := Complex.normSq_nonneg (φ₁ (jointIdx h x y) 0)
          have hb := Complex.normSq_nonneg (φ₂ (jointIdx h x (σ y)) 0)
          rw [abs_le]; constructor <;> linarith)
    _ = _ := Finset.sum_add_distrib

/-- **A phase-only operation.**  `P` acts as a phase-register matrix `M` that mixes
    the phase index `x` while holding the data index `y` fixed:
    `(P φ)⟨x,y⟩ = ∑_{x'} M x x' · φ⟨x',y⟩`.  This is exactly the structure of QPE's
    phase-register stages — Hadamards, the inverse QFT, and control-register gates —
    none of which touch the data register. -/
structure PhaseLocal {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (P : QState full_dim → QState full_dim) where
  M : Fin m_dim → Fin m_dim → ℂ
  acts : ∀ (φ : QState full_dim) (x : Fin m_dim) (y : Fin (full_dim / m_dim)),
    (P φ) (jointIdx h x y) 0 = ∑ x' : Fin m_dim, M x x' * φ (jointIdx h x' y) 0

/-- **THE QPE-LIFT KEYSTONE.**  A phase-only operation PRESERVES the data-relabel
    agreement: if `φ₁` is `φ₂` data-relabeled by `σ`, so are `P φ₁` and `P φ₂`.  (The
    phase matrix `M` mixes only the phase index; the data index `y` is held fixed, so
    the relabel `σ` of the data register passes through untouched.)  Hence every
    Hadamard / inverse-QFT / control stage of QPE carries the relabel through. -/
theorem phaseLocal_preserves_relabel {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    {P : QState full_dim → QState full_dim} (PL : PhaseLocal h P)
    {φ₁ φ₂ : QState full_dim} {σ : Equiv.Perm (Fin (full_dim / m_dim))}
    (hagree : DataRelabelAgree h φ₁ φ₂ σ) :
    DataRelabelAgree h (P φ₁) (P φ₂) σ := by
  intro x y
  rw [PL.acts φ₁ x y, PL.acts φ₂ x (σ y)]
  exact Finset.sum_congr rfl (fun x' _ => by rw [hagree x' y])

/-- The off-bad version: a phase-only operation preserves the relabel agreement off
    the SAME (per-outcome) data bad set (the phase mixing keeps the data index, hence
    the wrap set in `y`, fixed). -/
theorem phaseLocal_preserves_relabel_off {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    {P : QState full_dim → QState full_dim} (PL : PhaseLocal h P)
    {φ₁ φ₂ : QState full_dim} {σ : Equiv.Perm (Fin (full_dim / m_dim))}
    {badY : Finset (Fin (full_dim / m_dim))}
    (hagree : DataRelabelAgreeOff h φ₁ φ₂ σ badY) :
    DataRelabelAgreeOff h (P φ₁) (P φ₂) σ badY := by
  intro x y hy
  rw [PL.acts φ₁ x y, PL.acts φ₂ x (σ y)]
  exact Finset.sum_congr rfl (fun x' _ => by rw [hagree x' y hy])

end FormalRV.Shor.GidneyInPlace.PhaseMarginalLift
