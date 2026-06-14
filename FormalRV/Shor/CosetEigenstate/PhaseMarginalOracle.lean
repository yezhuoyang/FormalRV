/-
  FormalRV.Shor.CosetEigenstate.PhaseMarginalOracle — the oracle step of the QPE
  marginal lift: a controlled multiplication updates the data-relabel by conjugation.
  ════════════════════════════════════════════════════════════════════════════

  The QPE oracle is a sequence of controlled modular multiplications.  This file
  proves the per-step intertwining: one controlled COSET multiplication `O_c` and one
  controlled IDEAL (canonical) multiplication `O_i` carry the data-relabel agreement
  `φ₁⟨x,y⟩ = φ₂⟨x, σ_x y⟩` to the updated relabel `σ'_x = (τ^c_x)⁻¹ ; σ_x ; τ^i_x`,
  where `τ^c_x, τ^i_x` are the per-phase data permutations the two oracles apply.

  ── ANSWER TO THE PHASE-INDEXING QUESTION ──────────────────────────────────────
  The relabel `σ` MUST be PHASE-INDEXED (`σ : Fin m_dim → Equiv.Perm Data`), NOT
  global.  Reason: the controlled-power oracle applies `τ_x = (multiply by a^x)` to
  the data, so after the oracle the coset representative of a residue depends on the
  phase branch `x` (the unreduced accumulated value differs per branch).  The update
  `σ'_x = (τ^c_x)⁻¹ ; σ_x ; τ^i_x` is genuinely `x`-dependent.

  The per-OUTCOME phase-marginal invariance (`PhaseMarginalLift.phaseMarginal_
  relabel_invariant`, applied at outcome `x` with `σ x`) accommodates this — the
  marginal at `x` only needs the agreement at `x`.  TENSION (documented honestly):
  the phase-LOCAL preservation lemma (`phaseLocal_preserves_relabel`, for the
  inverse-QFT stage) needs a GLOBAL `σ` (it mixes phase indices `x'`).  So closing the
  full lift requires EITHER a gadget whose representative map is phase-INDEPENDENT
  (then `σ_x ≡ σ` global and both lemmas apply), OR establishing the relabel directly
  on the final per-outcome state.  The BAD SET is kept phase-independent by taking the
  UNION over branches/steps (`dataBornMass_union_le` below), at the cost of a looser —
  but still summable — Born bound.

  ── DIRECTION (the y=1 / multiplier-a check) ──────────────────────────────────
  `relabelUpdate_intertwines`: `σ'_x (τ^c_x y) = τ^i_x (σ_x y)`.  At `y = 1`,
  `σ_x 1 = 1` (rep of 1 ↔ canonical 1): the coset multiplier sends `1 ↦ τ^c_x 1` (the
  coset rep `a + jN` of `a`), and `σ'_x` sends THAT to `τ^i_x 1` (the canonical
  `a mod N`).  So `σ'` maps the coset representative `a+jN` to the canonical residue
  `a mod N` — the intended direction.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.PhaseMarginalLift

namespace FormalRV.Shor.CosetEigenstate.PhaseMarginalOracle

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer

/-- A phase-controlled DATA oracle: it maps `|x⟩|y⟩ ↦ |x⟩|τ_x y⟩` on the data
    register (the controlled modular multiplication), phase-indexed by the data
    permutation family `τ`.  Stated by its action on amplitudes. -/
structure DataOracle {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (O : QState full_dim → QState full_dim) where
  τ : Fin m_dim → Equiv.Perm (Fin (full_dim / m_dim))
  acts : ∀ (φ : QState full_dim) (x : Fin m_dim) (y : Fin (full_dim / m_dim)),
    (O φ) (jointIdx h x y) 0 = φ (jointIdx h x ((τ x).symm y)) 0

/-- The data-relabel UPDATE under one oracle step: conjugate `σ` by the oracle
    permutations, `σ'_x = (τc_x)⁻¹ ; σ_x ; τi_x`. -/
def relabelUpdate {m_dim full_dim : Nat}
    (σ τc τi : Fin m_dim → Equiv.Perm (Fin (full_dim / m_dim))) :
    Fin m_dim → Equiv.Perm (Fin (full_dim / m_dim)) :=
  fun x => (τc x).symm.trans ((σ x).trans (τi x))

/-- **THE DIRECTION IDENTITY (the y=1 / multiplier-a check).**  `σ'_x (τc_x y) =
    τi_x (σ_x y)`: the coset multiplier sends `y` to its product representative
    `τc_x y`, which `σ'_x` maps to the canonical residue `τi_x (σ_x y)` of the
    product.  At `y = 1` with `σ_x 1 = 1`: `σ'_x` sends the coset rep `τc_x 1` (`= a+jN`)
    to `τi_x 1` (`= a mod N`). -/
theorem relabelUpdate_intertwines {m_dim full_dim : Nat}
    (σ τc τi : Fin m_dim → Equiv.Perm (Fin (full_dim / m_dim)))
    (x : Fin m_dim) (y : Fin (full_dim / m_dim)) :
    relabelUpdate σ τc τi x (τc x y) = τi x (σ x y) := by
  simp [relabelUpdate, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- **THE ORACLE-INTERTWINING LEMMA (phase-indexed `σ`).**  One controlled coset
    multiplication `O_c` and one ideal canonical multiplication `O_i` PRESERVE the
    data-relabel agreement, updating the (phase-indexed) relabel `σ` to its conjugate
    `relabelUpdate σ τ^c τ^i`.  This is the per-step lift of the controlled modular
    multiplication through the marginal relation. -/
theorem dataOracle_intertwines {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    {O_c O_i : QState full_dim → QState full_dim}
    (Oc : DataOracle h O_c) (Oi : DataOracle h O_i)
    {φ₁ φ₂ : QState full_dim} {σ : Fin m_dim → Equiv.Perm (Fin (full_dim / m_dim))}
    (hagree : ∀ x y, φ₁ (jointIdx h x y) 0 = φ₂ (jointIdx h x (σ x y)) 0) :
    ∀ x y, (O_c φ₁) (jointIdx h x y) 0
      = (O_i φ₂) (jointIdx h x (relabelUpdate σ Oc.τ Oi.τ x y)) 0 := by
  intro x y
  rw [Oc.acts φ₁ x y, hagree x ((Oc.τ x).symm y),
      Oi.acts φ₂ x (relabelUpdate σ Oc.τ Oi.τ x y)]
  congr 2
  simp [relabelUpdate, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- The OFF-BAD version: the agreement is preserved off the IMAGE of the bad set
    under the coset oracle permutation, `(τc_x) '' badY` — the per-step wrap moves
    with the data.  (For a phase-independent total bad set, take the union over `x`;
    see `dataBornMass_union_le`.) -/
theorem dataOracle_intertwines_off {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    {O_c O_i : QState full_dim → QState full_dim}
    (Oc : DataOracle h O_c) (Oi : DataOracle h O_i)
    {φ₁ φ₂ : QState full_dim} {σ : Fin m_dim → Equiv.Perm (Fin (full_dim / m_dim))}
    (badY : Fin m_dim → Finset (Fin (full_dim / m_dim)))
    (hagree : ∀ x y, y ∉ badY x → φ₁ (jointIdx h x y) 0 = φ₂ (jointIdx h x (σ x y)) 0) :
    ∀ x y, y ∉ (badY x).map (Oc.τ x).toEmbedding →
      (O_c φ₁) (jointIdx h x y) 0
        = (O_i φ₂) (jointIdx h x (relabelUpdate σ Oc.τ Oi.τ x y)) 0 := by
  intro x y hy
  have hpre : (Oc.τ x).symm y ∉ badY x := by
    intro hmem
    apply hy
    rw [Finset.mem_map]
    exact ⟨(Oc.τ x).symm y, hmem, by simp⟩
  rw [Oc.acts φ₁ x y, hagree x ((Oc.τ x).symm y) hpre,
      Oi.acts φ₂ x (relabelUpdate σ Oc.τ Oi.τ x y)]
  congr 2
  simp [relabelUpdate, Equiv.trans_apply, Equiv.symm_apply_apply]

/-! ## Bad-set accumulation by union / monotonicity. -/

/-- **Born-mass subadditivity over a union.**  The data Born mass on `A ∪ B` is at
    most the sum of the masses on `A` and `B` — so repeated controlled multiplications
    accumulate their per-step wrap sets by UNION with a Born bound `≤` the sum of the
    per-step bounds (the total wrap weight `ge2021_coset_shor_succeeds_marginal`
    consumes). -/
theorem dataBornMass_union_le {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (s : QState full_dim) (x : Fin m_dim)
    (A B : Finset (Fin (full_dim / m_dim))) :
    (∑ y ∈ A ∪ B, Complex.normSq (s (jointIdx h x y) 0))
      ≤ (∑ y ∈ A, Complex.normSq (s (jointIdx h x y) 0))
        + (∑ y ∈ B, Complex.normSq (s (jointIdx h x y) 0)) := by
  have hui := Finset.sum_union_inter (s₁ := A) (s₂ := B)
    (f := fun y => Complex.normSq (s (jointIdx h x y) 0))
  have hnn : 0 ≤ ∑ y ∈ A ∩ B, Complex.normSq (s (jointIdx h x y) 0) :=
    Finset.sum_nonneg (fun y _ => Complex.normSq_nonneg _)
  linarith

end FormalRV.Shor.CosetEigenstate.PhaseMarginalOracle
