/-
  FormalRV.Shor.CosetEigenstate.PhaseMarginalEmbed — the STRONGER, PHASE-INDEPENDENT
  pre-inverse-QFT frontier: a data embedding `I_phase ⊗ E_data`.
  ════════════════════════════════════════════════════════════════════════════

  The phase-INDEXED relabel `σ_x` (PhaseMarginalOracle) does not pass cleanly through
  the inverse QFT (which mixes phase indices and so needs a GLOBAL relation).  This
  file fixes the stronger, PHASE-INDEPENDENT frontier requested:

      actual = (I_phase ⊗ E_data) · ideal        (off the wrap bad set),

  where `E_data` is a FIXED data-register operation — the coset embedding
  `|z⟩ ↦ cosetState N m z` — applied uniformly across all phase branches.  Because
  `E_data` touches only the data register (`I_phase` on the phase register), the
  operation `D = I_phase ⊗ E_data`:

    * COMMUTES with every phase-only operation (`phaseLocal_dataLocal_commute`) — so
      the inverse QFT (and Hadamards, controls) PRESERVE the relation
      (`embedAgree_preserved_by_phaseLocal`);
    * is an ISOMETRY on each data column (`DataLocal.isom`, true of the coset
      embedding by window disjointness), hence PRESERVES the phase marginal
      (`dataLocal_marginal_transfer`), giving the final readout-marginal transfer.

  This is the small assembly/interface theorem: it isolates the remaining circuit
  obligation to a SINGLE phase-independent statement — that the concrete oracle block
  produces `actual = (I_phase ⊗ E_data) ideal` off the wrap bad set — which the runway
  multiplier (next) discharges, with the wrap bad mass bounded by the accumulated
  runway error.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.PhaseMarginalLift

namespace FormalRV.Shor.CosetEigenstate.PhaseMarginalEmbed

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetEigenstate.PhaseMarginalLift (phaseMarginal PhaseLocal)

/-- A PHASE-INDEPENDENT data-register operation `D = I_phase ⊗ E_data`: it acts as the
    fixed matrix `E` on the data index `y`, holding the phase index `x` fixed, AND is
    an isometry on each data column (preserves the phase marginal).  The coset
    embedding `|z⟩ ↦ cosetState N m z` is such a `D` (isometry by window disjointness). -/
structure DataLocal {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (D : QState full_dim → QState full_dim) where
  E : Fin (full_dim / m_dim) → Fin (full_dim / m_dim) → ℂ
  acts : ∀ (φ : QState full_dim) (x : Fin m_dim) (y : Fin (full_dim / m_dim)),
    (D φ) (jointIdx h x y) 0 = ∑ y' : Fin (full_dim / m_dim), E y y' * φ (jointIdx h x y') 0
  isom : ∀ (φ : QState full_dim) (x : Fin m_dim),
    (∑ y, Complex.normSq ((D φ) (jointIdx h x y) 0))
      = ∑ y, Complex.normSq (φ (jointIdx h x y) 0)

/-- **`I_phase ⊗ E_data` COMMUTES with every phase-only operation.**  The phase
    matrix `M` mixes the phase index `x`; the data matrix `E` mixes the data index
    `y`; acting on independent indices they commute (`Finset.sum_comm`).  This is why
    the inverse QFT (phase-local) preserves a data embedding. -/
theorem phaseLocal_dataLocal_commute {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    {P D : QState full_dim → QState full_dim}
    (PL : PhaseLocal h P) (DL : DataLocal h D)
    (φ : QState full_dim) (x : Fin m_dim) (y : Fin (full_dim / m_dim)) :
    (P (D φ)) (jointIdx h x y) 0 = (D (P φ)) (jointIdx h x y) 0 := by
  rw [PL.acts (D φ) x y, DL.acts (P φ) x y]
  simp_rw [DL.acts φ _ y, PL.acts φ x _, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun y' _ => Finset.sum_congr rfl (fun x' _ => by ring))

/-- The data-embedding agreement: `actual = D · ideal` on the `⟨x,y⟩` amplitudes. -/
def EmbedAgree {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (actual ideal : QState full_dim) (D : QState full_dim → QState full_dim) : Prop :=
  ∀ x y, actual (jointIdx h x y) 0 = (D ideal) (jointIdx h x y) 0

/-- **PRESERVED BY THE INVERSE QFT (and every phase stage).**  If `actual = D · ideal`
    and `P` is phase-only, then `P actual = D · (P ideal)` — the data embedding passes
    through unchanged.  (`embedAgree` + `commute`.) -/
theorem embedAgree_preserved_by_phaseLocal {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    {P D : QState full_dim → QState full_dim}
    (PL : PhaseLocal h P) (DL : DataLocal h D)
    {actual ideal : QState full_dim} (hem : EmbedAgree h actual ideal D) :
    EmbedAgree h (P actual) (P ideal) D := by
  intro x y
  calc (P actual) (jointIdx h x y) 0
      = ∑ x', PL.M x x' * actual (jointIdx h x' y) 0 := PL.acts actual x y
    _ = ∑ x', PL.M x x' * (D ideal) (jointIdx h x' y) 0 :=
        Finset.sum_congr rfl (fun x' _ => by rw [hem x' y])
    _ = (P (D ideal)) (jointIdx h x y) 0 := (PL.acts (D ideal) x y).symm
    _ = (D (P ideal)) (jointIdx h x y) 0 := phaseLocal_dataLocal_commute h PL DL ideal x y

/-- **IMPLIES THE READOUT-MARGINAL TRANSFER (exact, everywhere).**  If `actual = D ·
    ideal` and `D` is a data isometry, the phase marginals coincide at every outcome —
    the coset embedding is invisible to the measured phase statistics. -/
theorem dataLocal_marginal_transfer {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    {D : QState full_dim → QState full_dim} (DL : DataLocal h D)
    {actual ideal : QState full_dim} (hem : EmbedAgree h actual ideal D) (x : Fin m_dim) :
    phaseMarginal h actual x = phaseMarginal h ideal x := by
  unfold phaseMarginal
  calc ∑ y, Complex.normSq (actual (jointIdx h x y) 0)
      = ∑ y, Complex.normSq ((D ideal) (jointIdx h x y) 0) :=
        Finset.sum_congr rfl (fun y _ => by rw [hem x y])
    _ = ∑ y, Complex.normSq (ideal (jointIdx h x y) 0) := DL.isom ideal x

/-- **THE OFF-BAD READOUT-MARGINAL TRANSFER.**  If `actual = D · ideal` only off a
    data wrap bad set `badY`, the phase marginals differ by at most the Born mass each
    of `actual` and `D·ideal` carries on `badY` — the wrap deviation the approximate
    bound pays.  (Combined with the union accumulation `PhaseMarginalOracle.dataBornMass_union_le`
    over steps/branches, this is the total wrap weight feeding `ge2021_coset_shor_succeeds_marginal`.) -/
theorem dataLocal_marginal_transfer_offBad {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    {D : QState full_dim → QState full_dim} (DL : DataLocal h D)
    {actual ideal : QState full_dim} (x : Fin m_dim)
    (badY : Finset (Fin (full_dim / m_dim)))
    (hem : ∀ y, y ∉ badY → actual (jointIdx h x y) 0 = (D ideal) (jointIdx h x y) 0) :
    |phaseMarginal h actual x - phaseMarginal h ideal x|
      ≤ (∑ y ∈ badY, Complex.normSq (actual (jointIdx h x y) 0))
        + (∑ y ∈ badY, Complex.normSq ((D ideal) (jointIdx h x y) 0)) := by
  have hidl : phaseMarginal h ideal x = ∑ y, Complex.normSq ((D ideal) (jointIdx h x y) 0) :=
    (DL.isom ideal x).symm
  rw [hidl]
  unfold phaseMarginal
  rw [← Finset.sum_sub_distrib]
  have hvanish : ∀ y ∈ Finset.univ, y ∉ badY →
      Complex.normSq (actual (jointIdx h x y) 0)
        - Complex.normSq ((D ideal) (jointIdx h x y) 0) = 0 :=
    fun y _ hy => by rw [hem y hy, sub_self]
  rw [← Finset.sum_subset (Finset.subset_univ badY) hvanish]
  calc |∑ y ∈ badY, (Complex.normSq (actual (jointIdx h x y) 0)
          - Complex.normSq ((D ideal) (jointIdx h x y) 0))|
      ≤ ∑ y ∈ badY, |Complex.normSq (actual (jointIdx h x y) 0)
          - Complex.normSq ((D ideal) (jointIdx h x y) 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ badY, (Complex.normSq (actual (jointIdx h x y) 0)
          + Complex.normSq ((D ideal) (jointIdx h x y) 0)) :=
        Finset.sum_le_sum (fun y _ => by
          have ha := Complex.normSq_nonneg (actual (jointIdx h x y) 0)
          have hb := Complex.normSq_nonneg ((D ideal) (jointIdx h x y) 0)
          rw [abs_le]; constructor <;> linarith)
    _ = _ := Finset.sum_add_distrib

end FormalRV.Shor.CosetEigenstate.PhaseMarginalEmbed
