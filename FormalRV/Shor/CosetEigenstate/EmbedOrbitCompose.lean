/-
  FormalRV.Shor.CosetEigenstate.EmbedOrbitCompose — obligation (1): the PHASE-INDEPENDENT
  EmbedAgree orbit-composition engine.
  ════════════════════════════════════════════════════════════════════════════

  The Route-2 capstone (`CosetShorEmbedCapstone.coset_shor_succeeds_embed`) needs `hagree`:
  off a wrap bad set, the coset final state equals `(I_phase ⊗ E_phys)` applied to the
  ideal final state.  This file is the ENGINE that produces that relation by composing it
  through the QPE orbit, keeping it STRICTLY PHASE-INDEPENDENT (no phase-indexed `σ_x` —
  the structural obstruction that does not commute through the inverse QFT):

    * `EmbedAgreeOff h actual ideal D badY` — `actual = D ideal` off a SINGLE
      (phase-independent) Finset `badY`.  The bad set is ONE Finset, NOT a function of the
      phase index `x`: phase mixing through the inverse QFT couples outcomes, so a
      per-outcome bad set would break the phase-local preservation (B).  This is the
      soundness point of the whole route.
    * `embedAgreeOff_preserved_by_phaseLocal` — a phase-only gate `P` (Hadamards / inverse
      QFT / control-register stage) PRESERVES `EmbedAgreeOff`, bad set UNCHANGED, given the
      phase-local/data-local COMMUTE `hcomm` (`P ∘ D = D ∘ P`, true of `I_phase ⊗ E_phys`
      by `phaseLocal_dataLocal_commute`'s argument — the `acts`, not the `isom`).
    * `embedAgreeOff_oracle_step` — a CONTROLLED oracle (`O_c` on the coset side, `O_i` on
      the ideal side) UPDATES `EmbedAgreeOff`, accumulating its wrap set `bad_step` by
      UNION, given (i) `O_c` is data-local off `badY` (`hc_local` — diagonal in the data
      index, so off-bad agreement is preserved with no transport) and (ii) the off-`bad_step`
      embedding intertwining `O_c ∘ D = D ∘ O_i` (`hintertwine`, phase-INDEPENDENT).
    * `embedAgree_orbit_fold` — folds `numIter` steps, accumulating bad by union into
      `(range numIter).biUnion bad_delta`; the phase-local stages contribute `bad_delta = ∅`,
      the oracle stages contribute their wrap set.

  HOW IT FEEDS THE CAPSTONE.  `embedAgree_orbit_fold` (with `init_bad = ∅`) yields
  `EmbedAgreeOff h (orbitState Fa Shor_initial numIter) (orbitState Fi Shor_initial numIter)
  E_phys ((range numIter).biUnion bad_delta)`.  Under the QPE stage-decomposition
  `orbitState Fa Shor_initial numIter = Shor_final_state f_coset` (and likewise the ideal),
  this IS the capstone's `hagree` with `embedIdeal = (I_phase ⊗ E_phys)(Shor_final_state
  f_ideal)` and `badY x = (range numIter).biUnion bad_delta` (constant in `x`).

  ⚠ REMAINING INPUTS (the hypotheses, to discharge from `WindowedCosetFamily` — these are
  the genuine circuit/eigenstate content, NOT this engine):
    • the QPE STAGE-DECOMPOSITION: `uc_eval (QPE_var_lsb m _ f)` factored into the
      phase-local stages (H / inverse-QFT / control) and the `numIter` controlled-oracle
      stages, so `orbitState … = Shor_final_state …`;
    • the per-oracle `hintertwine` and the initial `hinit` (`actual_init = E_phys ideal_init`,
      i.e. the coset work-register starts in the coset-embedded state) — obligation (2),
      the eigenstate/coset decomposition;
    • `hcomm` for each phase-local `P` — from `E_phys`'s data-locality (`acts`).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.  Proof
  de-risked via 3 parallel verified attempts.
-/
import FormalRV.Shor.CosetEigenstate.PhaseMarginalEmbed

namespace FormalRV.Shor.CosetEigenstate.EmbedOrbitCompose

open FormalRV.SQIRPort FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetEigenstate.PhaseMarginalLift (PhaseLocal)

/-- **(A) `EmbedAgreeOff`.**  `actual = (I_phase ⊗ E_phys) ideal` off a PHASE-INDEPENDENT
    bad set.  `badY` is a SINGLE `Finset (Fin (full_dim / m_dim))`, NOT a function of the
    phase index `x` — phase mixing through the inverse QFT couples outcomes, so the bad set
    must be one Finset for the orbit-composition engine to be sound. -/
def EmbedAgreeOff {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (actual ideal : QState full_dim) (D : QState full_dim → QState full_dim)
    (badY : Finset (Fin (full_dim / m_dim))) : Prop :=
  ∀ (x : Fin m_dim) (y : Fin (full_dim / m_dim)), y ∉ badY →
    actual (jointIdx h x y) 0 = (D ideal) (jointIdx h x y) 0

/-- **(B) Phase-local gates PRESERVE `EmbedAgreeOff` (bad set unchanged).**  A phase-only
    operation `P` mixes only the phase index `x`; the data index `y` is held fixed.
    Because `badY` is constant (the hypothesis `y ∉ badY` is the same for every phase index
    `x'` in the sum), `hem x' y hy` applies uniformly. -/
theorem embedAgreeOff_preserved_by_phaseLocal {m_dim full_dim} (h : m_dim ∣ full_dim)
    {P D : QState full_dim → QState full_dim}
    (PL : PhaseLocal h P)
    (hcomm : ∀ (φ : QState full_dim) (x : Fin m_dim) (y : Fin (full_dim / m_dim)),
        (P (D φ)) (jointIdx h x y) 0 = (D (P φ)) (jointIdx h x y) 0)
    {actual ideal : QState full_dim} {badY : Finset (Fin (full_dim / m_dim))}
    (hem : EmbedAgreeOff h actual ideal D badY) :
    EmbedAgreeOff h (P actual) (P ideal) D badY := by
  intro x y hy
  calc (P actual) (jointIdx h x y) 0
      = ∑ x', PL.M x x' * actual (jointIdx h x' y) 0 := PL.acts actual x y
    _ = ∑ x', PL.M x x' * (D ideal) (jointIdx h x' y) 0 :=
          Finset.sum_congr rfl (fun x' _ => by rw [hem x' y hy])
    _ = (P (D ideal)) (jointIdx h x y) 0 := (PL.acts (D ideal) x y).symm
    _ = (D (P ideal)) (jointIdx h x y) 0 := hcomm ideal x y

/-- **(C) Oracle step: a data-local control operation UPDATES `EmbedAgreeOff`**, accumulating
    the (phase-independent) `bad_step` set by union.  `O_c`/`O_i` are the coset/ideal
    controlled multiplies; `hc_local` is `O_c`'s data-locality off `badY` (diagonal in the
    data index — no transport); `hintertwine` is the off-`bad_step` embedding intertwining
    `O_c ∘ D = D ∘ O_i` (phase-INDEPENDENT). -/
theorem embedAgreeOff_oracle_step {m_dim full_dim} (h : m_dim ∣ full_dim)
    {O_c O_i D : QState full_dim → QState full_dim}
    {badY bad_step : Finset (Fin (full_dim / m_dim))}
    (hc_local : ∀ (a₁ a₂ : QState full_dim),
        (∀ x y, y ∉ badY → a₁ (jointIdx h x y) 0 = a₂ (jointIdx h x y) 0) →
        ∀ x y, y ∉ badY → (O_c a₁) (jointIdx h x y) 0 = (O_c a₂) (jointIdx h x y) 0)
    (hintertwine : ∀ (φ : QState full_dim) (x : Fin m_dim) (y : Fin (full_dim / m_dim)),
        y ∉ bad_step →
        (O_c (D φ)) (jointIdx h x y) 0 = (D (O_i φ)) (jointIdx h x y) 0)
    {actual ideal : QState full_dim}
    (hem : EmbedAgreeOff h actual ideal D badY) :
    EmbedAgreeOff h (O_c actual) (O_i ideal) D (badY ∪ bad_step) := by
  intro x y hy
  rw [Finset.notMem_union] at hy
  have h1 : (O_c actual) (jointIdx h x y) 0 = (O_c (D ideal)) (jointIdx h x y) 0 :=
    hc_local actual (D ideal) (fun x' y' hy' => hem x' y' hy') x y hy.1
  rw [h1, hintertwine ideal x y hy.2]

/-- The orbit state after `numIter` steps: `F (numIter-1) ∘ … ∘ F 0` applied to `init`. -/
def orbitState {full_dim : Nat} (F : Nat → QState full_dim → QState full_dim)
    (init : QState full_dim) : Nat → QState full_dim
  | 0 => init
  | k + 1 => F k (orbitState F init k)

/-- **(D) THE ORBIT FOLD.**  Compose `numIter` steps, each preserving `EmbedAgreeOff` and
    contributing `bad_delta k`; the bad set accumulates by UNION over `Finset.range
    numIter`.  Phase-local stages contribute `bad_delta = ∅`, oracle stages their wrap set —
    so the final bad set is the total wrap union `(range numIter).biUnion bad_delta`. -/
theorem embedAgree_orbit_fold {m_dim full_dim} (h : m_dim ∣ full_dim)
    (D : QState full_dim → QState full_dim)
    (Fa Fi : Nat → QState full_dim → QState full_dim)
    (bad_delta : Nat → Finset (Fin (full_dim / m_dim)))
    (init_a init_i : QState full_dim) (init_bad : Finset (Fin (full_dim / m_dim)))
    (hstep : ∀ (k : Nat) (a i : QState full_dim) (B : Finset (Fin (full_dim / m_dim))),
        EmbedAgreeOff h a i D B → EmbedAgreeOff h (Fa k a) (Fi k i) D (B ∪ bad_delta k))
    (hinit : EmbedAgreeOff h init_a init_i D init_bad) :
    ∀ numIter, EmbedAgreeOff h (orbitState Fa init_a numIter) (orbitState Fi init_i numIter) D
        (init_bad ∪ (Finset.range numIter).biUnion bad_delta) := by
  intro numIter
  induction numIter with
  | zero =>
      simp only [Finset.range_zero, Finset.biUnion_empty, Finset.union_empty]
      exact hinit
  | succ p ih =>
      have hstep_p := hstep p (orbitState Fa init_a p) (orbitState Fi init_i p)
        (init_bad ∪ (Finset.range p).biUnion bad_delta) ih
      have hbadeq : (init_bad ∪ (Finset.range p).biUnion bad_delta) ∪ bad_delta p
          = init_bad ∪ (Finset.range (p + 1)).biUnion bad_delta := by
        ext z
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
        constructor
        · rintro ((hz | ⟨k, hk, hz⟩) | hz)
          · exact Or.inl hz
          · exact Or.inr ⟨k, by omega, hz⟩
          · exact Or.inr ⟨p, by omega, hz⟩
        · rintro (hz | ⟨k, hk, hz⟩)
          · exact Or.inl (Or.inl hz)
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h' | h'
            · exact Or.inl (Or.inr ⟨k, h', hz⟩)
            · exact Or.inr (h' ▸ hz)
      show EmbedAgreeOff h (Fa p (orbitState Fa init_a p)) (Fi p (orbitState Fi init_i p)) D _
      rw [← hbadeq]
      exact hstep_p

/-- **THE ORBIT EmbedAgree WITNESS (feeds the capstone's `hagree`).**  Given the QPE
    stage-decomposition (`actualFinal`/`idealFinal` are the orbit composites), the per-step
    preservation `hstep`, and the initial embedding `hinit` (with empty initial bad set —
    the coset circuit starts coset-embedded), the coset final state equals `D` applied to
    the ideal final state off the TOTAL wrap union.  This is exactly
    `coset_shor_succeeds_embed`'s `hagree` (with `embedIdeal = D idealFinal`, `badY x =
    (range numIter).biUnion bad_delta`). -/
theorem orbit_final_embedAgree {m_dim full_dim} (h : m_dim ∣ full_dim)
    (D : QState full_dim → QState full_dim)
    (Fa Fi : Nat → QState full_dim → QState full_dim)
    (bad_delta : Nat → Finset (Fin (full_dim / m_dim)))
    (init_a init_i actualFinal idealFinal : QState full_dim) (numIter : Nat)
    (hstep : ∀ (k : Nat) (a i : QState full_dim) (B : Finset (Fin (full_dim / m_dim))),
        EmbedAgreeOff h a i D B → EmbedAgreeOff h (Fa k a) (Fi k i) D (B ∪ bad_delta k))
    (hinit : EmbedAgreeOff h init_a init_i D ∅)
    (hdecomp_a : actualFinal = orbitState Fa init_a numIter)
    (hdecomp_i : idealFinal = orbitState Fi init_i numIter) :
    EmbedAgreeOff h actualFinal idealFinal D ((Finset.range numIter).biUnion bad_delta) := by
  rw [hdecomp_a, hdecomp_i]
  have hf := embedAgree_orbit_fold h D Fa Fi bad_delta init_a init_i ∅ hstep hinit numIter
  rwa [Finset.empty_union] at hf

end FormalRV.Shor.CosetEigenstate.EmbedOrbitCompose
