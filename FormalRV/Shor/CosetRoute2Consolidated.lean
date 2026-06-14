/-
  FormalRV.Shor.CosetRoute2Consolidated — the Route-2 CONSOLIDATION milestone: one named
  frontier (`ApproxCosetOrbitShift`) + the conditional final coset-Shor success bound.
  ════════════════════════════════════════════════════════════════════════════

  This freezes a clean checkpoint: EVERYTHING in the Route-2 coset-Shor argument is now
  reduced to VERIFIED infrastructure EXCEPT a single named frontier — the approximate
  coset orbit-shift.  The conditional final theorem `coset_route2_success_conditional`
  derives the success bound `P_coset ≥ P_ideal − 2ε` from that one frontier alone, by
  chaining the kernel-clean engines:

    `ApproxCosetOrbitShift`  ──orbit_final_embedAgree──▶  hagree (EmbedAgree on finals)
                             ──coset_shor_succeeds_embed──▶  P_coset ≥ P_ideal − 2ε

  ══════ THE THEOREM MAP ══════
  VERIFIED (kernel-clean, `[propext, Classical.choice, Quot.sound]`):
    • circuit semantics + literal-cuccaro→coset-shift chain (CuccaroStructuredOutput,
      CuccaroGatePerm, CuccaroPhysCoset, PhysCosetFold);
    • phase-marginal transfer + E_phys canonical-residue isometry (PhaseMarginal*,
      PhysEmbedMarginal);
    • orbit-composition scaffold (EmbedOrbitCompose: EmbedAgreeOff preserve/step/fold/
      orbit_final_embedAgree);
    • wrap-mass accumulation bound (CosetWrapAccumulation: totalWrapMass_le);
    • the success capstone (CosetShorEmbedCapstone: coset_shor_succeeds_embed);
    • the eigenstate-from-cyclic-shift reduction (CosetEigenstateShift).
  OPEN (the SOLE remaining mathematical frontier — this file's hypothesis):
    • the APPROXIMATE coset orbit-shift / runway-coarsening-shift bound, captured by the
      fields of `ApproxCosetOrbitShift` (centrally `hstep`, the per-oracle off-bad
      EmbedAgree update that the approximate orbit-shift supplies).

  ⚠ WHY THE OPEN PIECE IS APPROXIMATE (load-bearing, documented).  The EXACT eigenstate
  shift `U |coset(k)⟩ = |coset(c·k mod N)⟩` is FALSE: the in-place coset multiply sends a
  basis value `k + jN ↦ c·k + j·(cN)`, so the runway spacing goes `N ↦ cN` (coarsened),
  and the image lattice `{c·k + j·cN}` is NOT the canonical coset lattice
  `{c·k mod N + jN}`.  The correct theorem is therefore APPROXIMATE / OFF-BAD: `U` maps the
  runway lattice to a coarsened/permuted lattice agreeing with the canonical coset except
  on a bounded boundary set whose Born mass is the deviation `ε`.  That approximate
  orbit-shift (the real Zalka/Gidney coset-eigenstate lemma) is the next phase — it is NOT
  another plumbing bridge, and `ApproxCosetOrbitShift` is the precise interface it must meet.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetShorEmbedCapstone
import FormalRV.Shor.CosetEigenstate.EmbedOrbitCompose

namespace FormalRV.Shor.CosetRoute2Consolidated

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.CosetShorEmbedCapstone (coset_shor_succeeds_embed)
open FormalRV.Shor.CosetEigenstate.EmbedOrbitCompose (EmbedAgreeOff orbitState orbit_final_embedAgree)

/-- **THE SINGLE NAMED FRONTIER.**  Bundles exactly the conditions the verified engines
    consume that are NOT yet discharged — centred on the APPROXIMATE coset orbit-shift
    (`hstep`).  Everything else in the Route-2 argument is verified infrastructure; this is
    the sole remaining mathematical content.

    Fields:
    * `numIter`, `Fa`/`Fi`, `bad_delta`, `init_a`/`init_i` — the QPE-orbit stage data
      (coset/ideal per-stage maps + per-stage wrap sets + laid-out initial states);
    * `hdecomp_a`/`hdecomp_i` — the QPE STAGE-DECOMPOSITION: each final state is the orbit
      composite (mechanical, `uc_eval_QPE`; carried here, discharged in CP1);
    * `hstep` — **THE APPROXIMATE ORBIT-SHIFT**: each oracle stage preserves the off-bad
      EmbedAgree, accumulating its wrap set `bad_delta k` (the off-bad / runway-coarsening
      content); phase-local stages take `bad_delta k = ∅`;
    * `hinit` — the initial embedding (the coset circuit starts coset-embedded, empty bad);
    * `hmarg` — E_phys preserves the ideal's per-outcome readout marginal (the
      canonical-residue isometry, `PhysEmbedMarginal.physCosetEmbed_isometry`);
    * `h_ideal` — the ideal Shor success bound (`P_ideal`, proven via
      `windowedModNMul_shor_correct`, supplied as a hypothesis);
    * `h_coset_wrap`/`h_embed_wrap` — the accumulated wrap Born mass `≤ ε` on both sides
      (`CosetWrapAccumulation.totalWrapMass_le`). -/
structure ApproxCosetOrbitShift (a r N m n anc : Nat)
    (f_coset f_ideal : Nat → BaseUCom (n + anc))
    (E_phys : QState (2 ^ m * 2 ^ n * 2 ^ anc) → QState (2 ^ m * 2 ^ n * 2 ^ anc))
    (ε P_ideal : ℝ) where
  numIter : Nat
  Fa : Nat → QState (2 ^ m * 2 ^ n * 2 ^ anc) → QState (2 ^ m * 2 ^ n * 2 ^ anc)
  Fi : Nat → QState (2 ^ m * 2 ^ n * 2 ^ anc) → QState (2 ^ m * 2 ^ n * 2 ^ anc)
  bad_delta : Nat → Finset (Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m))
  init_a : QState (2 ^ m * 2 ^ n * 2 ^ anc)
  init_i : QState (2 ^ m * 2 ^ n * 2 ^ anc)
  hdecomp_a : Shor_final_state m n anc f_coset = orbitState Fa init_a numIter
  hdecomp_i : Shor_final_state m n anc f_ideal = orbitState Fi init_i numIter
  hstep : ∀ (k : Nat) (s_a s_i : QState (2 ^ m * 2 ^ n * 2 ^ anc))
      (B : Finset (Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m))),
      EmbedAgreeOff (shorDvd m n anc) s_a s_i E_phys B →
      EmbedAgreeOff (shorDvd m n anc) (Fa k s_a) (Fi k s_i) E_phys (B ∪ bad_delta k)
  hinit : EmbedAgreeOff (shorDvd m n anc) init_a init_i E_phys ∅
  hmarg : ∀ (x : Fin (2 ^ m)),
      prob_partial_meas (basis_vector (2 ^ m) x.val) (E_phys (Shor_final_state m n anc f_ideal))
        = prob_partial_meas (basis_vector (2 ^ m) x.val) (Shor_final_state m n anc f_ideal)
  h_ideal : probability_of_success a r N m n anc f_ideal ≥ P_ideal
  h_coset_wrap :
      (∑ x : Fin (2 ^ m), ∑ y ∈ (Finset.range numIter).biUnion bad_delta,
          Complex.normSq (Shor_final_state m n anc f_coset
            (jointIdx (shorDvd m n anc) x y) 0)) ≤ ε
  h_embed_wrap :
      (∑ x : Fin (2 ^ m), ∑ y ∈ (Finset.range numIter).biUnion bad_delta,
          Complex.normSq ((E_phys (Shor_final_state m n anc f_ideal))
            (jointIdx (shorDvd m n anc) x y) 0)) ≤ ε

/-- **THE CONSOLIDATED CONDITIONAL FINAL THEOREM.**  Given the single frontier
    `ApproxCosetOrbitShift` (with deviation `ε`), the Route-2 coset Shor family succeeds
    with probability `≥ P_ideal − 2ε`.  Proven purely by chaining the verified engines:
    `orbit_final_embedAgree` lifts the per-oracle off-bad EmbedAgree (`hstep`) through the
    whole QPE orbit to a final-state EmbedAgree; `coset_shor_succeeds_embed` turns that +
    the marginal preservation + the wrap bounds into the success bound.  No part of this
    theorem assumes the approximate orbit-shift's PROOF — only its stated interface. -/
theorem coset_route2_success_conditional
    (a r N m n anc : Nat) (f_coset f_ideal : Nat → BaseUCom (n + anc))
    (E_phys : QState (2 ^ m * 2 ^ n * 2 ^ anc) → QState (2 ^ m * 2 ^ n * 2 ^ anc))
    (ε P_ideal : ℝ)
    (h : ApproxCosetOrbitShift a r N m n anc f_coset f_ideal E_phys ε P_ideal) :
    probability_of_success a r N m n anc f_coset ≥ P_ideal - 2 * ε := by
  -- Lift the per-oracle off-bad EmbedAgree through the orbit to a final-state EmbedAgree.
  have hagree :=
    orbit_final_embedAgree (shorDvd m n anc) E_phys h.Fa h.Fi h.bad_delta h.init_a h.init_i
      (Shor_final_state m n anc f_coset) (Shor_final_state m n anc f_ideal) h.numIter
      h.hstep h.hinit h.hdecomp_a h.hdecomp_i
  -- Feed the EmbedAgree + marginal preservation + wrap bounds to the success capstone.
  exact coset_shor_succeeds_embed a r N m n anc f_coset f_ideal
    (E_phys (Shor_final_state m n anc f_ideal)) ε P_ideal h.h_ideal
    (fun _ => (Finset.range h.numIter).biUnion h.bad_delta) h.hmarg
    (fun x y hy => hagree x y hy) h.h_coset_wrap h.h_embed_wrap

end FormalRV.Shor.CosetRoute2Consolidated
