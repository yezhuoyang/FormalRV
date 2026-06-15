/-
  FormalRV.Shor.CosetShorEmbedCapstone — Route 2 capstone: the EmbedAgree ⇒
  success-probability bound for the PHASE-INDEPENDENT coset embedding `E_phys`.
  ════════════════════════════════════════════════════════════════════════════

  The sound coset-Shor route is the PHASE-INDEPENDENT embedding `I_phase ⊗ E_phys`
  (NOT the phase-indexed data-permutation σ, which does not commute through the inverse
  QFT — the structural obstruction documented in `PhaseMarginalOracle`).  This capstone
  is the success-probability endpoint of that route:

    if the coset final state agrees with `(I_phase ⊗ E_phys)` applied to the ideal final
    state OFF a wrap bad set `B`, AND `E_phys` PRESERVES the per-outcome readout marginal
    of the ideal (its canonical-residue isometry — `PhysEmbedMarginal.physCosetEmbed_isometry`),
    AND both states carry Born weight `≤ ε` on `B`, THEN

        P_success(coset) ≥ P_success(ideal) − 2·ε.

  This mirrors `CosetMarginalShorBound.coset_shor_succeeds_marginal` but consumes the
  EMBEDDING frontier (the spread `E_phys`), not the σ-PERMUTATION frontier `CosetMarginalRelabel`.
  It works at the `Shor_final_state`-amplitude level via `prob_partial_meas_basis_eq` +
  `prob_partial_meas_basis_dataPerm_offBad` (with σ = id, since the off-bad agreement is
  direct, no relabel) + the marginal-preservation hypothesis.  It is INDEPENDENT of
  `QPE_var_lsb`'s internal semantics: the ideal bound is the hypothesis `h_ideal` (which
  carries the Tier-2 SQIR facts), and everything here is the kernel-clean amplitude
  algebra — `coset_shor_succeeds_marginal` (the σ analogue) is verified
  `[propext, Classical.choice, Quot.sound]`, and this shares its machinery.

  ⚠ THE THREE REMAINING OBLIGATIONS (the hypotheses, made explicit — to discharge from
  the concrete `WindowedCosetFamily` construction):
    1. ORBIT COMPOSITION (`hagree`).  The per-MULTIPLY EmbedAgree-off-bad (the windowed
       fold `PhysCosetFold.physCoset_windowed_fold` + the atomic
       `CosetEmbedStep`/`CosetFoldWindowed`) must be lifted through all `m` controlled
       QPE iterates + the inverse QFT to an EmbedAgree on `Shor_final_state`.  The
       phase-INDEPENDENCE of `E_phys` makes this pass through the phase stages
       (`PhaseMarginalEmbed.embedAgree_preserved_by_phaseLocal`); composing the controlled
       oracle steps (`PhaseMarginalOracle.dataOracle_intertwines`) is the work.
    2. EIGENSTATE/COSET DECOMPOSITION (the `embedIdeal` object).  Connecting the
       single-residue work-register init `|1⟩` to the `physCosetState`/eigenstate analysis
       — i.e. exhibiting `embedIdeal = (I_phase ⊗ E_phys)(Shor_final_state f_ideal)` as the
       coset-embedded ideal whose marginal `E_phys` preserves (`hmarg`).
    3. CONCRETE BAD-MASS ACCUMULATION (`h_coset_wrap`, `h_embed_wrap`).  The per-step wrap
       masses (`CosetFoldWindowed`'s `≤ numWin/2^m` per side) accumulated across the
       iterates by union (`PhaseMarginalOracle.dataBornMass_union_le`) to `≤ ε = totalDeviationR`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetMarginalShorBound

namespace FormalRV.Shor.CosetShorEmbedCapstone

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetMarginalShorBound
  (shorDvd prob_partial_meas_basis_dataPerm_offBad)

/-- **ROUTE 2 CAPSTONE — EmbedAgree ⇒ coset Shor success bound.**  For the
    phase-independent coset embedding `E_phys`: if the coset final state agrees with the
    embedded ideal final state `embedIdeal = (I_phase ⊗ E_phys)(Shor_final_state f_ideal)`
    OFF a per-outcome wrap set `badY` (`hagree`), `E_phys` PRESERVES the ideal's per-outcome
    readout marginal (`hmarg` — the canonical-residue isometry), and both states carry Born
    weight `≤ ε` on the wrap sets, then the coset family succeeds with probability
    `≥ P_ideal − 2·ε`.  (The phase-independence is WHY the embedding passes through the
    inverse QFT; see the file header for the three obligations behind `hagree`/`hmarg`/the
    wrap bounds.) -/
theorem coset_shor_succeeds_embed
    (a r N m n anc : Nat) (f_coset f_ideal : Nat → BaseUCom (n + anc))
    (embedIdeal : QState (2 ^ m * 2 ^ n * 2 ^ anc))
    (ε P_ideal : ℝ)
    (h_ideal : probability_of_success a r N m n anc f_ideal ≥ P_ideal)
    (badY : Fin (2 ^ m) → Finset (Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)))
    -- (2) E_phys preserves the ideal's per-outcome readout marginal (the canonical isometry).
    (hmarg : ∀ (x : Fin (2 ^ m)),
        prob_partial_meas (basis_vector (2 ^ m) x.val) embedIdeal
          = prob_partial_meas (basis_vector (2 ^ m) x.val)
              (Shor_final_state m n anc f_ideal))
    -- (1) off the wrap set, the coset final state IS the embedded ideal (orbit-lifted EmbedAgree).
    (hagree : ∀ (x : Fin (2 ^ m)) (y), y ∉ badY x →
        Shor_final_state m n anc f_coset (jointIdx (shorDvd m n anc) x y) 0
          = embedIdeal (jointIdx (shorDvd m n anc) x y) 0)
    -- (3) accumulated wrap Born mass ≤ ε on both sides.
    (h_coset_wrap :
        (∑ x : Fin (2 ^ m), ∑ y ∈ badY x,
            Complex.normSq (Shor_final_state m n anc f_coset
              (jointIdx (shorDvd m n anc) x y) 0)) ≤ ε)
    (h_embed_wrap :
        (∑ x : Fin (2 ^ m), ∑ y ∈ badY x,
            Complex.normSq (embedIdeal (jointIdx (shorDvd m n anc) x y) 0)) ≤ ε) :
    probability_of_success a r N m n anc f_coset ≥ P_ideal - 2 * ε := by
  have hdvd := shorDvd m n anc
  set s₁ := Shor_final_state m n anc f_coset with hs₁
  -- |P(coset) − P(ideal)| ≤ 2ε
  have hbound : |probability_of_success a r N m n anc f_coset
        - probability_of_success a r N m n anc f_ideal| ≤ 2 * ε := by
    -- expand the success-difference, swapping the ideal marginal for the embedded one (hmarg)
    have hdecomp : probability_of_success a r N m n anc f_coset
        - probability_of_success a r N m n anc f_ideal
        = ∑ x ∈ Finset.range (2 ^ m),
            r_found x m r a N *
              (prob_partial_meas (basis_vector (2 ^ m) x) s₁
                - prob_partial_meas (basis_vector (2 ^ m) x) embedIdeal) := by
      unfold probability_of_success
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← hs₁,
          show prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc f_ideal)
              = prob_partial_meas (basis_vector (2 ^ m) x) embedIdeal
            from (hmarg ⟨x, Finset.mem_range.mp hx⟩).symm]
      ring
    rw [hdecomp]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [← Fin.sum_univ_eq_sum_range
      (fun x => |r_found x m r a N *
            (prob_partial_meas (basis_vector (2 ^ m) x) s₁
              - prob_partial_meas (basis_vector (2 ^ m) x) embedIdeal)|) (2 ^ m)]
    have hsplit :
        (∑ x : Fin (2 ^ m), |r_found x.val m r a N *
            (prob_partial_meas (basis_vector (2 ^ m) x.val) s₁
              - prob_partial_meas (basis_vector (2 ^ m) x.val) embedIdeal)|)
          ≤ (∑ x : Fin (2 ^ m), ∑ y ∈ badY x,
                Complex.normSq (s₁ (jointIdx hdvd x y) 0))
            + (∑ x : Fin (2 ^ m), ∑ y ∈ badY x,
                Complex.normSq (embedIdeal (jointIdx hdvd x y) 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (r_found_nonneg x.val m r a N)]
      calc r_found x.val m r a N *
              |prob_partial_meas (basis_vector (2 ^ m) x.val) s₁
                - prob_partial_meas (basis_vector (2 ^ m) x.val) embedIdeal|
          ≤ 1 * |prob_partial_meas (basis_vector (2 ^ m) x.val) s₁
                - prob_partial_meas (basis_vector (2 ^ m) x.val) embedIdeal| :=
            mul_le_mul_of_nonneg_right (r_found_le_one _ _ _ _ _) (abs_nonneg _)
        _ = |prob_partial_meas (basis_vector (2 ^ m) x.val) s₁
                - prob_partial_meas (basis_vector (2 ^ m) x.val) embedIdeal| := one_mul _
        _ ≤ (∑ y ∈ badY x, Complex.normSq (s₁ (jointIdx hdvd x y) 0))
              + (∑ y ∈ badY x, Complex.normSq (embedIdeal (jointIdx hdvd x y) 0)) := by
            have h := prob_partial_meas_basis_dataPerm_offBad hdvd s₁ embedIdeal x
              (Equiv.refl _) (badY x) (fun y hy => hagree x y hy)
            simpa using h
    linarith [hsplit, h_coset_wrap, h_embed_wrap]
  have hsub := abs_le.mp hbound
  linarith [hsub.1, h_ideal]

end FormalRV.Shor.CosetShorEmbedCapstone
