/-
  Ancilla-freshness soundness under composition (Obligation C, CLOSED).

  Part 1 -- state-equivalence machinery: `lifecycleEquivalent` /
  `state_equivalent` collapse {Free, Dirty} while keeping Live distinct;
  `stateNormalized` is preserved by `setLifecycle` and `runFreshness`;
  lookup lemmas go through the Bool-predicate bridge.

  Part 2 -- composition: `runFreshness_append`, the success-preserving
  one-sided equivalence forms, `ancilla_freshness_ok_seqSchedules`, the
  n-fold replicate version, and body extraction from
  `symbolic_rep_strict_ok` giving the headline
  `symbolic_rep_implies_expanded_block_ancilla_freshness_ok` for
  arbitrary n.

  The two parts share `match`-generated auxiliary definitions, so they
  must live in ONE file (Lean matcher identity is per-module; `rw`
  against a `match` pattern from another module does not fire).
  No `sorry`, no custom `axiom`.
-/

import FormalRV.System.Artifacts.LayeredArtifactInterface
import FormalRV.System.Artifacts.CompressedRepeat.ShiftInvariance

set_option maxRecDepth 8000

namespace FormalRV.System.CompressedRepeatSoundness

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.AdderSystem
open FormalRV.System.LayeredArtifactInterface

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.AdderSystem
open FormalRV.System.LayeredArtifactInterface

/-! ## §11. Obligation (C) — ancilla-freshness across
       repeated blocks via state-equivalence

    The body passes `ancilla_freshness_ok` when started from
    the empty state (= all Free).  After one body finishes,
    measured sites are `Dirty`, not `Free`.  For the next
    copy, `Free` and `Dirty` should be interchangeable
    because an explicit-site `RequestFreshAncilla` only
    rejects `Live` sites.  We make this rigorous via a
    state-equivalence relation:

      `state_equivalent s1 s2 := ∀ site,
         lifecycleEquivalent (lifecycleOf s1 site)
                             (lifecycleOf s2 site) = true`

    `lifecycleEquivalent` collapses {Free, Dirty} into one
    class while keeping Live distinct.

    Key compatibility lemmas:
      * the Live-mask is constant under state-equivalence
        (only Live vs non-Live matters to `freshnessStep`).
      * `setLifecycle` preserves equivalence pointwise.
      * `freshnessStep` preserves equivalence — both
        succeed-with-equivalent or both fail.
      * `runFreshness` preserves equivalence by induction.
      * `noDanglingLive` ⇒ equivalent to `[]`.

    Final theorem chain:
      `ancilla_freshness_ok_seqSchedules` →
      `ancilla_freshness_ok_seqMany_replicate` →
      `ancilla_freshness_ok_repeated_atom_expand` →
      `symbolic_rep_implies_expanded_ancilla_freshness_ok`. -/

/-! ### §11.a Lifecycle equivalence -/

/-- Collapse `Free` and `Dirty` into one class; `Live` is
    its own class.  Both directions need to map. -/
def lifecycleEquivalent (a b : SiteLifecycle) : Bool :=
  match a, b with
  | .Live, .Live => true
  | .Live, _     => false
  | _, .Live     => false
  | _, _         => true

/-- State equivalence: pointwise lifecycle equivalence at
    every site. -/
def state_equivalent
    (s1 s2 : List (Nat × SiteLifecycle)) : Prop :=
  ∀ site : Nat,
    lifecycleEquivalent (lifecycleOf s1 site) (lifecycleOf s2 site) = true

theorem state_equivalent_refl (s : List (Nat × SiteLifecycle)) :
    state_equivalent s s := by
  intro site
  cases lifecycleOf s site <;> rfl

theorem state_equivalent_symm
    {s1 s2 : List (Nat × SiteLifecycle)}
    (h : state_equivalent s1 s2) : state_equivalent s2 s1 := by
  intro site
  have heq := h site
  unfold lifecycleEquivalent at heq ⊢
  cases hk1 : lifecycleOf s1 site
    <;> cases hk2 : lifecycleOf s2 site
    <;> rw [hk1, hk2] at heq
    <;> first | rfl | exact absurd heq (by decide)

/-- Live status is preserved both ways under state
    equivalence. -/
theorem state_equivalent_live_iff
    {s1 s2 : List (Nat × SiteLifecycle)} (site : Nat)
    (h : state_equivalent s1 s2) :
    (lifecycleOf s1 site = SiteLifecycle.Live)
      ↔ (lifecycleOf s2 site = SiteLifecycle.Live) := by
  have heq := h site
  unfold lifecycleEquivalent at heq
  constructor
  · intro h1
    cases hk2 : lifecycleOf s2 site with
    | Live => rfl
    | Free => simp only [h1, hk2] at heq; exact absurd heq (by decide)
    | Dirty => simp only [h1, hk2] at heq; exact absurd heq (by decide)
  · intro h2
    cases hk1 : lifecycleOf s1 site with
    | Live => rfl
    | Free => simp only [h2, hk1] at heq; exact absurd heq (by decide)
    | Dirty => simp only [h2, hk1] at heq; exact absurd heq (by decide)

/-- Live site decision predicate is the same under equivalent
    states. -/
theorem isLive_eq_under_state_equivalent
    {s1 s2 : List (Nat × SiteLifecycle)} (site : Nat)
    (h : state_equivalent s1 s2) :
    (match lifecycleOf s1 site with | .Live => true | _ => false)
      = (match lifecycleOf s2 site with | .Live => true | _ => false) := by
  by_cases h1 : lifecycleOf s1 site = SiteLifecycle.Live
  · have h2 : lifecycleOf s2 site = SiteLifecycle.Live :=
      (state_equivalent_live_iff site h).mp h1
    rw [h1, h2]
  · have h2 : lifecycleOf s2 site ≠ SiteLifecycle.Live := fun hL =>
      h1 ((state_equivalent_live_iff site h).mpr hL)
    cases hk1 : lifecycleOf s1 site with
    | Live => exact absurd hk1 h1
    | Free =>
        cases hk2 : lifecycleOf s2 site with
        | Live => exact absurd hk2 h2
        | Free => rfl
        | Dirty => rfl
    | Dirty =>
        cases hk2 : lifecycleOf s2 site with
        | Live => exact absurd hk2 h2
        | Free => rfl
        | Dirty => rfl


/-! ### §11.b `stateNormalized` predicate -/

/-- A lifecycle state is *normalized* if no two entries share
    the same site identifier.  `runFreshness` starting from
    `[]` is expected to preserve this invariant because
    every `setLifecycle` first filters out all entries with
    the target site. -/
def stateNormalized (s : List (Nat × SiteLifecycle)) : Prop :=
  s.Pairwise (fun a b => a.1 ≠ b.1)

theorem stateNormalized_nil :
    stateNormalized ([] : List (Nat × SiteLifecycle)) :=
  List.Pairwise.nil

/-! ### §11.c Boundary theorem (forward direction)

    `noDanglingLive s = true` implies `state_equivalent s []`.
    This direction does NOT require stateNormalized — it just
    propagates the "no Live entry" fact through `lifecycleOf`. -/

theorem lifecycleOf_nil (site : Nat) :
    lifecycleOf ([] : List (Nat × SiteLifecycle)) site = SiteLifecycle.Free :=
  rfl

theorem noDanglingLive_implies_state_equivalent_empty
    (s : List (Nat × SiteLifecycle))
    (h : noDanglingLive s = true) :
    state_equivalent s [] := by
  intro site
  rw [lifecycleOf_nil]
  -- Show lifecycleOf s site ≠ Live, then conclude.
  have h_not_live : lifecycleOf s site ≠ SiteLifecycle.Live := by
    intro hL
    unfold lifecycleOf at hL
    cases hfind : s.find? (fun p => decide (p.1 = site)) with
    | none => rw [hfind] at hL; simp at hL
    | some p =>
        rw [hfind] at hL
        simp at hL
        have hmem : p ∈ s := List.mem_of_find?_eq_some hfind
        unfold noDanglingLive at h
        rw [List.all_eq_true] at h
        have hp := h p hmem
        rw [hL] at hp
        simp at hp
  cases hk : lifecycleOf s site with
  | Live => exact absurd hk h_not_live
  | Free => rfl
  | Dirty => rfl

/-! ### §11.d `setLifecycle` lookup lemmas

    We bridge through a Bool-predicate helper `dropSite` +
    `setLifecycleBool` that uses `!decide (p.1 = site)`
    instead of the original `¬ decide (p.1 = site)`.  The two
    are equal pointwise as Bool functions and so produce
    equal filter results, but the explicit Bool form
    cooperates with `List.filter` / `List.find?` /
    `List.mem_filter` simp lemmas. -/

/-- `s.filter` with an explicit Bool predicate that drops
    every entry whose first coord equals `site`. -/
def dropSite (s : List (Nat × SiteLifecycle)) (site : Nat) : List (Nat × SiteLifecycle) :=
  s.filter (fun p => !decide (p.1 = site))

/-- Bool-predicate variant of `setLifecycle`. -/
def setLifecycleBool (s : List (Nat × SiteLifecycle)) (site : Nat)
    (lc : SiteLifecycle) : List (Nat × SiteLifecycle) :=
  dropSite s site ++ [(site, lc)]

/-- `setLifecycle` and `setLifecycleBool` produce the same
    list because `¬ decide (p.1 = site)` (as a Bool via
    coercion) equals `!decide (p.1 = site)`. -/
theorem setLifecycle_eq_setLifecycleBool
    (s : List (Nat × SiteLifecycle)) (site : Nat) (lc : SiteLifecycle) :
    setLifecycle s site lc = setLifecycleBool s site lc := by
  unfold setLifecycle setLifecycleBool dropSite
  simp

/-! #### §11.d.1 Membership lemmas on `dropSite` -/

theorem mem_dropSite_iff
    {s : List (Nat × SiteLifecycle)} {site : Nat}
    {p : Nat × SiteLifecycle} :
    p ∈ dropSite s site ↔ p ∈ s ∧ p.1 ≠ site := by
  unfold dropSite
  rw [List.mem_filter]
  constructor
  · intro ⟨hmem, hpred⟩
    refine ⟨hmem, ?_⟩
    simp at hpred
    exact hpred
  · intro ⟨hmem, hne⟩
    refine ⟨hmem, ?_⟩
    simp [hne]

theorem not_mem_dropSite_same
    {s : List (Nat × SiteLifecycle)} {site : Nat} :
    ∀ p ∈ dropSite s site, p.1 ≠ site := by
  intro p hp
  exact (mem_dropSite_iff.mp hp).2

/-! #### §11.d.2 Lookup lemmas on `setLifecycleBool` -/

private theorem find?_dropSite_eq_none
    (s : List (Nat × SiteLifecycle)) (site : Nat) :
    (dropSite s site).find? (fun p => decide (p.1 = site)) = none := by
  rw [List.find?_eq_none]
  intro p hp
  simp
  exact not_mem_dropSite_same p hp

theorem lifecycleOf_setLifecycleBool_same
    (s : List (Nat × SiteLifecycle)) (site : Nat) (lc : SiteLifecycle) :
    lifecycleOf (setLifecycleBool s site lc) site = lc := by
  unfold lifecycleOf setLifecycleBool
  rw [List.find?_append, find?_dropSite_eq_none]
  simp [List.find?_cons]

private theorem find?_dropSite_other
    (s : List (Nat × SiteLifecycle)) (site site' : Nat) (hne : site' ≠ site) :
    (dropSite s site).find? (fun p => decide (p.1 = site'))
      = s.find? (fun p => decide (p.1 = site')) := by
  unfold dropSite
  rw [List.find?_filter]
  -- Now: s.find? (fun a => !decide(a.1=site) && decide(a.1=site')) = s.find? (=site').
  -- Show the predicates equal pointwise under hne (using site'≠site).
  congr 1
  funext p
  by_cases hp : p.1 = site
  · -- p.1 = site, so !decide(p.1=site) = false, and decide(p.1=site') = false (site' ≠ site).
    have h1 : (!decide (p.1 = site)) = false := by simp [hp]
    have h2 : decide (p.1 = site') = false := by
      simp
      intro h
      exact hne (h.symm.trans hp)
    rw [h1, h2]
    rfl
  · -- p.1 ≠ site, so !decide(p.1=site) = true; combined reduces to decide(p.1=site').
    have h1 : (!decide (p.1 = site)) = true := by simp [hp]
    rw [h1]
    simp

theorem lifecycleOf_setLifecycleBool_other
    (s : List (Nat × SiteLifecycle)) (site site' : Nat) (lc : SiteLifecycle)
    (hne : site' ≠ site) :
    lifecycleOf (setLifecycleBool s site lc) site' = lifecycleOf s site' := by
  unfold lifecycleOf setLifecycleBool
  rw [List.find?_append, find?_dropSite_other s site site' hne]
  -- [(site, lc)].find? (p.1 = site') = none since site ≠ site'.
  have h_singleton : ([(site, lc)] : List (Nat × SiteLifecycle)).find?
                       (fun p => decide (p.1 = site')) = none := by
    have hne_sym : site ≠ site' := fun h => hne h.symm
    simp [List.find?_cons, hne_sym]
  rw [h_singleton]
  simp

/-! #### §11.d.3 Original `setLifecycle` lookup lemmas

    Transfer via `setLifecycle_eq_setLifecycleBool`. -/

theorem lifecycleOf_setLifecycle_same
    (s : List (Nat × SiteLifecycle)) (site : Nat) (lc : SiteLifecycle) :
    lifecycleOf (setLifecycle s site lc) site = lc := by
  rw [setLifecycle_eq_setLifecycleBool]
  exact lifecycleOf_setLifecycleBool_same s site lc

theorem lifecycleOf_setLifecycle_other
    (s : List (Nat × SiteLifecycle)) (site site' : Nat) (lc : SiteLifecycle)
    (hne : site' ≠ site) :
    lifecycleOf (setLifecycle s site lc) site' = lifecycleOf s site' := by
  rw [setLifecycle_eq_setLifecycleBool]
  exact lifecycleOf_setLifecycleBool_other s site site' lc hne

/-! ### §11.e `stateNormalized` preservation by `dropSite` /
       `setLifecycle` -/

theorem stateNormalized_dropSite
    {s : List (Nat × SiteLifecycle)} (h : stateNormalized s)
    (site : Nat) :
    stateNormalized (dropSite s site) := by
  unfold stateNormalized dropSite at *
  induction s with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
      simp only [List.filter_cons]
      cases hpa : (!decide (a.1 = site)) with
      | false => simp; exact ih (List.Pairwise.of_cons h)
      | true =>
          simp [hpa]
          refine ⟨?_, ih (List.Pairwise.of_cons h)⟩
          intro a_1 b hmem _
          exact List.rel_of_pairwise_cons h hmem

theorem stateNormalized_setLifecycleBool
    {s : List (Nat × SiteLifecycle)} (h : stateNormalized s)
    (site : Nat) (lc : SiteLifecycle) :
    stateNormalized (setLifecycleBool s site lc) := by
  unfold setLifecycleBool stateNormalized
  rw [List.pairwise_append]
  refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
  · exact stateNormalized_dropSite h site
  · intro a ha b hb
    rw [List.mem_singleton] at hb
    have ha_ne : a.1 ≠ site := not_mem_dropSite_same a ha
    subst hb
    exact ha_ne

theorem stateNormalized_setLifecycle
    {s : List (Nat × SiteLifecycle)} (h : stateNormalized s)
    (site : Nat) (lc : SiteLifecycle) :
    stateNormalized (setLifecycle s site lc) := by
  rw [setLifecycle_eq_setLifecycleBool]
  exact stateNormalized_setLifecycleBool h site lc

/-! ### §11.f `freshnessStep` / `runFreshness` preservation -/

/-- A successful `freshnessStep` either leaves the state
    unchanged or applies a single `setLifecycle`.  This
    factors away the SysCallKind enumeration so downstream
    proofs (preservation, equivalence) reduce to two cases. -/
theorem freshnessStep_result_form
    (model : AncillaModel) (state : List (Nat × SiteLifecycle))
    (sc : SysCall) (state' : List (Nat × SiteLifecycle))
    (hStep : freshnessStep model state sc = some state') :
    state' = state ∨ ∃ site lc, state' = setLifecycle state site lc := by
  cases hk : sc.kind with
  | Gate1q q g =>
      have hf : freshnessStep model state sc = some state := by
        unfold freshnessStep; rw [hk]
      rw [hf] at hStep
      injection hStep with he
      left; exact he.symm
  | TransitQubit q c =>
      have hf : freshnessStep model state sc = some state := by
        unfold freshnessStep; rw [hk]
      rw [hf] at hStep
      injection hStep with he
      left; exact he.symm
  | RequestMagicState f =>
      have hf : freshnessStep model state sc = some state := by
        unfold freshnessStep; rw [hk]
      rw [hf] at hStep
      injection hStep with he
      left; exact he.symm
  | DecodeSyndrome r =>
      have hf : freshnessStep model state sc = some state := by
        unfold freshnessStep; rw [hk]
      rw [hf] at hStep
      injection hStep with he
      left; exact he.symm
  | PauliFrameUpdate c =>
      have hf : freshnessStep model state sc = some state := by
        unfold freshnessStep; rw [hk]
      rw [hf] at hStep
      injection hStep with he
      left; exact he.symm
  | Gate2q q1 q2 g =>
      have hf : freshnessStep model state sc
              = (let q1_ok := if siteInAncillaModel model q1 then
                                match lifecycleOf state q1 with
                                | .Live => true | _ => false
                              else true
                 let q2_ok := if siteInAncillaModel model q2 then
                                match lifecycleOf state q2 with
                                | .Live => true | _ => false
                              else true
                 if q1_ok && q2_ok then some state else none) := by
        unfold freshnessStep; rw [hk]; rfl
      rw [hf] at hStep
      by_cases hcond :
          ((if siteInAncillaModel model q1 then
                match lifecycleOf state q1 with | .Live => true | _ => false
              else true) &&
            (if siteInAncillaModel model q2 then
                match lifecycleOf state q2 with | .Live => true | _ => false
              else true)) = true
      · rw [if_pos hcond] at hStep
        injection hStep with he
        left; exact he.symm
      · rw [if_neg hcond] at hStep
        exact absurd hStep (by simp)
  | Measure q b =>
      have hf : freshnessStep model state sc
              = (if siteInAncillaModel model q then
                    match lifecycleOf state q with
                    | .Live => some (setLifecycle state q SiteLifecycle.Dirty)
                    | _     => none
                  else some state) := by
        unfold freshnessStep; rw [hk]; rfl
      rw [hf] at hStep
      by_cases hin : siteInAncillaModel model q = true
      · rw [if_pos hin] at hStep
        cases hL : lifecycleOf state q with
        | Live =>
            rw [hL] at hStep
            injection hStep with he
            right; refine ⟨q, SiteLifecycle.Dirty, ?_⟩; exact he.symm
        | Free => rw [hL] at hStep; exact absurd hStep (by simp)
        | Dirty => rw [hL] at hStep; exact absurd hStep (by simp)
      · rw [if_neg hin] at hStep
        injection hStep with he
        left; exact he.symm
  | RequestFreshAncilla site =>
      have hf : freshnessStep model state sc
              = (if siteInAncillaModel model site then
                    match lifecycleOf state site with
                    | .Live => none
                    | _     => some (setLifecycle state site SiteLifecycle.Live)
                  else some state) := by
        unfold freshnessStep; rw [hk]; rfl
      rw [hf] at hStep
      by_cases hin : siteInAncillaModel model site = true
      · rw [if_pos hin] at hStep
        cases hL : lifecycleOf state site with
        | Live => rw [hL] at hStep; exact absurd hStep (by simp)
        | Free =>
            rw [hL] at hStep
            injection hStep with he
            right; refine ⟨site, SiteLifecycle.Live, ?_⟩; exact he.symm
        | Dirty =>
            rw [hL] at hStep
            injection hStep with he
            right; refine ⟨site, SiteLifecycle.Live, ?_⟩; exact he.symm
      · rw [if_neg hin] at hStep
        injection hStep with he
        left; exact he.symm

theorem freshnessStep_preserves_stateNormalized
    (model : AncillaModel) (state : List (Nat × SiteLifecycle))
    (sc : SysCall) (state' : List (Nat × SiteLifecycle))
    (hNorm : stateNormalized state)
    (hStep : freshnessStep model state sc = some state') :
    stateNormalized state' := by
  rcases freshnessStep_result_form model state sc state' hStep with
    heq | ⟨site, lc, heq⟩
  · subst heq; exact hNorm
  · subst heq; exact stateNormalized_setLifecycle hNorm site lc

theorem runFreshness_preserves_stateNormalized
    (model : AncillaModel) (sched : List SysCall)
    (state : List (Nat × SiteLifecycle))
    (state' : List (Nat × SiteLifecycle))
    (hNorm : stateNormalized state)
    (hRun : runFreshness model state sched = some state') :
    stateNormalized state' := by
  induction sched generalizing state with
  | nil =>
      simp [runFreshness] at hRun
      subst hRun
      exact hNorm
  | cons sc rest ih =>
      simp only [runFreshness] at hRun
      cases hstep : freshnessStep model state sc with
      | none => rw [hstep] at hRun; simp at hRun
      | some state1 =>
          rw [hstep] at hRun
          simp at hRun
          have hNorm1 := freshnessStep_preserves_stateNormalized
                          model state sc state1 hNorm hstep
          exact ih state1 hNorm1 hRun

/-! ### §11.f.helpers — `state_equivalent_set_same`

    Pulled up from §11.h so it is in scope for the
    state-equivalence chain below. -/

theorem state_equivalent_set_same
    {s1 s2 : List (Nat × SiteLifecycle)}
    (h : state_equivalent s1 s2)
    (site : Nat) (lc : SiteLifecycle) :
    state_equivalent
        (setLifecycle s1 site lc) (setLifecycle s2 site lc) := by
  intro site'
  by_cases hsite : site' = site
  · subst hsite
    rw [lifecycleOf_setLifecycle_same, lifecycleOf_setLifecycle_same]
    cases lc <;> rfl
  · rw [lifecycleOf_setLifecycle_other _ _ _ _ hsite,
        lifecycleOf_setLifecycle_other _ _ _ _ hsite]
    exact h site'

/-! ### §11.f.eq `freshnessStep` and `runFreshness` state-equivalence

    For each SysCall kind, freshnessStep takes the same path
    under state-equivalent inputs (because the conditions
    depend only on Live-status, preserved under
    state_equivalent).  When both calls succeed, the
    resulting states are again state-equivalent.

    We mirror the structure of `freshnessStep_result_form`:
    case-split on `sc.kind`, compute `freshnessStep` to its
    explicit body, and align both states' branches. -/

theorem freshnessStep_state_equivalent
    (model : AncillaModel) (sc : SysCall)
    (s1 s2 s1' s2' : List (Nat × SiteLifecycle))
    (hEq : state_equivalent s1 s2)
    (h1 : freshnessStep model s1 sc = some s1')
    (h2 : freshnessStep model s2 sc = some s2') :
    state_equivalent s1' s2' := by
  cases hk : sc.kind with
  | Gate1q q g =>
      have hf1 : freshnessStep model s1 sc = some s1 := by
        unfold freshnessStep; rw [hk]
      have hf2 : freshnessStep model s2 sc = some s2 := by
        unfold freshnessStep; rw [hk]
      rw [hf1] at h1; rw [hf2] at h2
      injection h1 with he1; injection h2 with he2
      subst he1; subst he2; exact hEq
  | TransitQubit q c =>
      have hf1 : freshnessStep model s1 sc = some s1 := by
        unfold freshnessStep; rw [hk]
      have hf2 : freshnessStep model s2 sc = some s2 := by
        unfold freshnessStep; rw [hk]
      rw [hf1] at h1; rw [hf2] at h2
      injection h1 with he1; injection h2 with he2
      subst he1; subst he2; exact hEq
  | RequestMagicState f =>
      have hf1 : freshnessStep model s1 sc = some s1 := by
        unfold freshnessStep; rw [hk]
      have hf2 : freshnessStep model s2 sc = some s2 := by
        unfold freshnessStep; rw [hk]
      rw [hf1] at h1; rw [hf2] at h2
      injection h1 with he1; injection h2 with he2
      subst he1; subst he2; exact hEq
  | DecodeSyndrome r =>
      have hf1 : freshnessStep model s1 sc = some s1 := by
        unfold freshnessStep; rw [hk]
      have hf2 : freshnessStep model s2 sc = some s2 := by
        unfold freshnessStep; rw [hk]
      rw [hf1] at h1; rw [hf2] at h2
      injection h1 with he1; injection h2 with he2
      subst he1; subst he2; exact hEq
  | PauliFrameUpdate c =>
      have hf1 : freshnessStep model s1 sc = some s1 := by
        unfold freshnessStep; rw [hk]
      have hf2 : freshnessStep model s2 sc = some s2 := by
        unfold freshnessStep; rw [hk]
      rw [hf1] at h1; rw [hf2] at h2
      injection h1 with he1; injection h2 with he2
      subst he1; subst he2; exact hEq
  | Gate2q q1 q2 g =>
      -- The condition (q1_ok && q2_ok) is the same for s1 and s2 by
      -- Live-status preservation; both go same branch.
      have hf1 : freshnessStep model s1 sc
              = (let q1_ok := if siteInAncillaModel model q1 then
                                match lifecycleOf s1 q1 with
                                | .Live => true | _ => false
                              else true
                 let q2_ok := if siteInAncillaModel model q2 then
                                match lifecycleOf s1 q2 with
                                | .Live => true | _ => false
                              else true
                 if q1_ok && q2_ok then some s1 else none) := by
        unfold freshnessStep; rw [hk]; rfl
      have hf2 : freshnessStep model s2 sc
              = (let q1_ok := if siteInAncillaModel model q1 then
                                match lifecycleOf s2 q1 with
                                | .Live => true | _ => false
                              else true
                 let q2_ok := if siteInAncillaModel model q2 then
                                match lifecycleOf s2 q2 with
                                | .Live => true | _ => false
                              else true
                 if q1_ok && q2_ok then some s2 else none) := by
        unfold freshnessStep; rw [hk]; rfl
      -- Use Live-status preservation to align the conditions.
      have q1_iff := isLive_eq_under_state_equivalent q1 hEq
      have q2_iff := isLive_eq_under_state_equivalent q2 hEq
      rw [hf1] at h1; rw [hf2] at h2
      -- Now h1 and h2 have if-then-else with conditions that match
      -- after rewriting via q1_iff, q2_iff.
      by_cases hcond :
          ((if siteInAncillaModel model q1 then
                match lifecycleOf s1 q1 with | .Live => true | _ => false
              else true) &&
            (if siteInAncillaModel model q2 then
                match lifecycleOf s1 q2 with | .Live => true | _ => false
              else true)) = true
      · rw [if_pos hcond] at h1
        -- For h2, rewrite using q1_iff, q2_iff to use s1's lifecycleOf, then apply hcond.
        have hcond2 :
            ((if siteInAncillaModel model q1 then
                  match lifecycleOf s2 q1 with | .Live => true | _ => false
                else true) &&
              (if siteInAncillaModel model q2 then
                  match lifecycleOf s2 q2 with | .Live => true | _ => false
                else true)) = true := by
          rw [← q1_iff, ← q2_iff]; exact hcond
        rw [if_pos hcond2] at h2
        injection h1 with he1; injection h2 with he2
        subst he1; subst he2; exact hEq
      · rw [if_neg hcond] at h1
        exact absurd h1 (by simp)
  | Measure q b =>
      have hf1 : freshnessStep model s1 sc
              = (if siteInAncillaModel model q then
                    match lifecycleOf s1 q with
                    | .Live => some (setLifecycle s1 q SiteLifecycle.Dirty)
                    | _     => none
                  else some s1) := by
        unfold freshnessStep; rw [hk]; rfl
      have hf2 : freshnessStep model s2 sc
              = (if siteInAncillaModel model q then
                    match lifecycleOf s2 q with
                    | .Live => some (setLifecycle s2 q SiteLifecycle.Dirty)
                    | _     => none
                  else some s2) := by
        unfold freshnessStep; rw [hk]; rfl
      rw [hf1] at h1; rw [hf2] at h2
      by_cases hin : siteInAncillaModel model q = true
      · rw [if_pos hin] at h1 h2
        by_cases hL1 : lifecycleOf s1 q = SiteLifecycle.Live
        · have hL2 : lifecycleOf s2 q = SiteLifecycle.Live :=
            (state_equivalent_live_iff q hEq).mp hL1
          rw [hL1] at h1; rw [hL2] at h2
          injection h1 with he1; injection h2 with he2
          subst he1; subst he2
          exact state_equivalent_set_same hEq q SiteLifecycle.Dirty
        · -- non-Live: derive contradiction
          cases hL1k : lifecycleOf s1 q with
          | Live => exact absurd hL1k hL1
          | Free => rw [hL1k] at h1; exact absurd h1 (by simp)
          | Dirty => rw [hL1k] at h1; exact absurd h1 (by simp)
      · rw [if_neg hin] at h1 h2
        injection h1 with he1; injection h2 with he2
        subst he1; subst he2; exact hEq
  | RequestFreshAncilla site =>
      have hf1 : freshnessStep model s1 sc
              = (if siteInAncillaModel model site then
                    match lifecycleOf s1 site with
                    | .Live => none
                    | _     => some (setLifecycle s1 site SiteLifecycle.Live)
                  else some s1) := by
        unfold freshnessStep; rw [hk]; rfl
      have hf2 : freshnessStep model s2 sc
              = (if siteInAncillaModel model site then
                    match lifecycleOf s2 site with
                    | .Live => none
                    | _     => some (setLifecycle s2 site SiteLifecycle.Live)
                  else some s2) := by
        unfold freshnessStep; rw [hk]; rfl
      rw [hf1] at h1; rw [hf2] at h2
      by_cases hin : siteInAncillaModel model site = true
      · rw [if_pos hin] at h1 h2
        by_cases hL1 : lifecycleOf s1 site = SiteLifecycle.Live
        · rw [hL1] at h1; exact absurd h1 (by simp)
        · have hL2 : lifecycleOf s2 site ≠ SiteLifecycle.Live := fun hL =>
            hL1 ((state_equivalent_live_iff site hEq).mpr hL)
          cases hL1k : lifecycleOf s1 site with
          | Live => exact absurd hL1k hL1
          | Free =>
              cases hL2k : lifecycleOf s2 site with
              | Live => exact absurd hL2k hL2
              | Free =>
                  rw [hL1k] at h1; rw [hL2k] at h2
                  injection h1 with he1; injection h2 with he2
                  subst he1; subst he2
                  exact state_equivalent_set_same hEq site SiteLifecycle.Live
              | Dirty =>
                  rw [hL1k] at h1; rw [hL2k] at h2
                  injection h1 with he1; injection h2 with he2
                  subst he1; subst he2
                  exact state_equivalent_set_same hEq site SiteLifecycle.Live
          | Dirty =>
              cases hL2k : lifecycleOf s2 site with
              | Live => exact absurd hL2k hL2
              | Free =>
                  rw [hL1k] at h1; rw [hL2k] at h2
                  injection h1 with he1; injection h2 with he2
                  subst he1; subst he2
                  exact state_equivalent_set_same hEq site SiteLifecycle.Live
              | Dirty =>
                  rw [hL1k] at h1; rw [hL2k] at h2
                  injection h1 with he1; injection h2 with he2
                  subst he1; subst he2
                  exact state_equivalent_set_same hEq site SiteLifecycle.Live
      · rw [if_neg hin] at h1 h2
        injection h1 with he1; injection h2 with he2
        subst he1; subst he2; exact hEq

theorem runFreshness_state_equivalent
    (model : AncillaModel) (sched : List SysCall)
    (s1 s2 s1' s2' : List (Nat × SiteLifecycle))
    (hEq : state_equivalent s1 s2)
    (h1 : runFreshness model s1 sched = some s1')
    (h2 : runFreshness model s2 sched = some s2') :
    state_equivalent s1' s2' := by
  induction sched generalizing s1 s2 with
  | nil =>
      simp [runFreshness] at h1 h2
      subst h1; subst h2; exact hEq
  | cons sc rest ih =>
      simp only [runFreshness] at h1 h2
      cases hstep1 : freshnessStep model s1 sc with
      | none => rw [hstep1] at h1; simp at h1
      | some t1 =>
          rw [hstep1] at h1; simp at h1
          cases hstep2 : freshnessStep model s2 sc with
          | none => rw [hstep2] at h2; simp at h2
          | some t2 =>
              rw [hstep2] at h2; simp at h2
              have hEq' := freshnessStep_state_equivalent
                            model sc s1 s2 t1 t2 hEq hstep1 hstep2
              exact ih t1 t2 hEq' h1 h2

/-! ### §11.g Reverse boundary direction -/

theorem lifecycleOf_eq_of_mem_normalized
    {s : List (Nat × SiteLifecycle)} (hnorm : stateNormalized s)
    {p : Nat × SiteLifecycle} (hp : p ∈ s) :
    lifecycleOf s p.1 = p.2 := by
  unfold lifecycleOf
  have hfind : s.find? (fun q => decide (q.1 = p.1)) = some p := by
    induction s with
    | nil => simp at hp
    | cons q rest ih =>
        rcases List.mem_cons.mp hp with hpeq | hpmem
        · subst hpeq
          simp [List.find?_cons]
        · unfold stateNormalized at hnorm
          have hq_ne : q.1 ≠ p.1 := List.rel_of_pairwise_cons hnorm hpmem
          have hq_dec : decide (q.1 = p.1) = false := by simp [hq_ne]
          simp [List.find?_cons, hq_dec]
          have hnorm_rest : stateNormalized rest := by
            unfold stateNormalized
            exact List.Pairwise.of_cons hnorm
          exact ih hnorm_rest hpmem
  rw [hfind]

theorem state_equivalent_empty_implies_noDanglingLive
    (s : List (Nat × SiteLifecycle))
    (h : state_equivalent s []) (hnorm : stateNormalized s) :
    noDanglingLive s = true := by
  unfold noDanglingLive
  rw [List.all_eq_true]
  intro p hp
  cases hL : p.2 with
  | Live =>
      exfalso
      have hlive : lifecycleOf s p.1 = SiteLifecycle.Live := by
        rw [lifecycleOf_eq_of_mem_normalized hnorm hp, hL]
      have : lifecycleOf ([] : List (Nat × SiteLifecycle)) p.1 = SiteLifecycle.Live :=
        (state_equivalent_live_iff p.1 h).mp hlive
      rw [lifecycleOf_nil] at this
      simp at this
  | Free => rfl
  | Dirty => rfl

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.AdderSystem
open FormalRV.System.LayeredArtifactInterface


/-! ## §12. Obligation (C) headline for repeated schedule blocks

    Hardware-generic terminology: `CompressedSchedule.atom` is
    the implementation-level constructor for a **leaf schedule
    block**.  It is NOT a claim that the block is a hardware-
    atomic operation — it can represent any cross-layer
    verified schedule block (a PPM block, lattice-surgery
    gadget, neutral-atom movement schedule, ion-trap shuttling
    block, superconducting routing block, factory/decoder
    service block, etc.).  In theorem names and comments below
    we use `block` / `leaf` / `schedule block` / `repeated
    block`. -/

/-! ### §12.a `state_equivalent` transitivity -/

theorem state_equivalent_trans
    {s1 s2 s3 : List (Nat × SiteLifecycle)}
    (h12 : state_equivalent s1 s2) (h23 : state_equivalent s2 s3) :
    state_equivalent s1 s3 := by
  intro site
  have h1 := h12 site
  have h2 := h23 site
  unfold lifecycleEquivalent at h1 h2 ⊢
  cases hk1 : lifecycleOf s1 site
    <;> cases hk2 : lifecycleOf s2 site
    <;> cases hk3 : lifecycleOf s3 site
    <;> rw [hk1, hk2] at h1
    <;> rw [hk2, hk3] at h2
    <;> first | rfl | exact absurd h1 (by decide) | exact absurd h2 (by decide)

/-! ### §12.b `runFreshness_append` -/

theorem runFreshness_append
    (model : AncillaModel) (state : List (Nat × SiteLifecycle))
    (xs ys : List SysCall) :
    runFreshness model state (xs ++ ys)
      = (match runFreshness model state xs with
         | none => none
         | some state' => runFreshness model state' ys) := by
  induction xs generalizing state with
  | nil => rfl
  | cons sc rest ih =>
      have h1 : runFreshness model state ((sc :: rest) ++ ys)
            = match freshnessStep model state sc with
              | none => none
              | some state' => runFreshness model state' (rest ++ ys) := rfl
      have h2 : runFreshness model state (sc :: rest)
            = match freshnessStep model state sc with
              | none => none
              | some state' => runFreshness model state' rest := rfl
      rw [h1, h2]
      cases hstep : freshnessStep model state sc with
      | none => rfl
      | some state1 => exact ih state1

/-! ### §12.b.2 Success-preservation of `runFreshness` under
       `state_equivalent`

    Stronger one-sided form of `runFreshness_state_equivalent`:
    given a successful run from `s2`, a state-equivalent run
    from `s1` also succeeds, with a state-equivalent
    result.  Needed in the seqSchedules proof to rule out the
    `runFreshness model s_xs ys = none` branch. -/

theorem freshnessStep_state_equivalent_some_form
    (model : AncillaModel) (sc : SysCall)
    (s1 s2 t2 : List (Nat × SiteLifecycle))
    (hEq : state_equivalent s1 s2)
    (h2 : freshnessStep model s2 sc = some t2) :
    ∃ t1, freshnessStep model s1 sc = some t1 ∧ state_equivalent t1 t2 := by
  cases hk : sc.kind with
  | Gate1q q g =>
      have hf1 : freshnessStep model s1 sc = some s1 := by
        unfold freshnessStep; rw [hk]
      have hf2 : freshnessStep model s2 sc = some s2 := by
        unfold freshnessStep; rw [hk]
      rw [hf2] at h2; injection h2 with he2; subst he2
      exact ⟨s1, hf1, hEq⟩
  | TransitQubit q c =>
      have hf1 : freshnessStep model s1 sc = some s1 := by
        unfold freshnessStep; rw [hk]
      have hf2 : freshnessStep model s2 sc = some s2 := by
        unfold freshnessStep; rw [hk]
      rw [hf2] at h2; injection h2 with he2; subst he2
      exact ⟨s1, hf1, hEq⟩
  | RequestMagicState f =>
      have hf1 : freshnessStep model s1 sc = some s1 := by
        unfold freshnessStep; rw [hk]
      have hf2 : freshnessStep model s2 sc = some s2 := by
        unfold freshnessStep; rw [hk]
      rw [hf2] at h2; injection h2 with he2; subst he2
      exact ⟨s1, hf1, hEq⟩
  | DecodeSyndrome r =>
      have hf1 : freshnessStep model s1 sc = some s1 := by
        unfold freshnessStep; rw [hk]
      have hf2 : freshnessStep model s2 sc = some s2 := by
        unfold freshnessStep; rw [hk]
      rw [hf2] at h2; injection h2 with he2; subst he2
      exact ⟨s1, hf1, hEq⟩
  | PauliFrameUpdate c =>
      have hf1 : freshnessStep model s1 sc = some s1 := by
        unfold freshnessStep; rw [hk]
      have hf2 : freshnessStep model s2 sc = some s2 := by
        unfold freshnessStep; rw [hk]
      rw [hf2] at h2; injection h2 with he2; subst he2
      exact ⟨s1, hf1, hEq⟩
  | Gate2q q1 q2 g =>
      have hf1 : freshnessStep model s1 sc
              = (let q1_ok := if siteInAncillaModel model q1 then
                                match lifecycleOf s1 q1 with
                                | .Live => true | _ => false
                              else true
                 let q2_ok := if siteInAncillaModel model q2 then
                                match lifecycleOf s1 q2 with
                                | .Live => true | _ => false
                              else true
                 if q1_ok && q2_ok then some s1 else none) := by
        unfold freshnessStep; rw [hk]; rfl
      have hf2 : freshnessStep model s2 sc
              = (let q1_ok := if siteInAncillaModel model q1 then
                                match lifecycleOf s2 q1 with
                                | .Live => true | _ => false
                              else true
                 let q2_ok := if siteInAncillaModel model q2 then
                                match lifecycleOf s2 q2 with
                                | .Live => true | _ => false
                              else true
                 if q1_ok && q2_ok then some s2 else none) := by
        unfold freshnessStep; rw [hk]; rfl
      have q1_iff := isLive_eq_under_state_equivalent q1 hEq
      have q2_iff := isLive_eq_under_state_equivalent q2 hEq
      rw [hf2] at h2
      by_cases hcond :
          ((if siteInAncillaModel model q1 then
                match lifecycleOf s2 q1 with | .Live => true | _ => false
              else true) &&
            (if siteInAncillaModel model q2 then
                match lifecycleOf s2 q2 with | .Live => true | _ => false
              else true)) = true
      · rw [if_pos hcond] at h2
        injection h2 with he2; subst he2
        -- Derive matching condition for s1
        have hcond1 :
            ((if siteInAncillaModel model q1 then
                  match lifecycleOf s1 q1 with | .Live => true | _ => false
                else true) &&
              (if siteInAncillaModel model q2 then
                  match lifecycleOf s1 q2 with | .Live => true | _ => false
                else true)) = true := by
          rw [q1_iff, q2_iff]; exact hcond
        rw [hf1, if_pos hcond1]
        exact ⟨s1, rfl, hEq⟩
      · rw [if_neg hcond] at h2; exact absurd h2 (by simp)
  | Measure q b =>
      have hf1 : freshnessStep model s1 sc
              = (if siteInAncillaModel model q then
                    match lifecycleOf s1 q with
                    | .Live => some (setLifecycle s1 q SiteLifecycle.Dirty)
                    | _     => none
                  else some s1) := by
        unfold freshnessStep; rw [hk]; rfl
      have hf2 : freshnessStep model s2 sc
              = (if siteInAncillaModel model q then
                    match lifecycleOf s2 q with
                    | .Live => some (setLifecycle s2 q SiteLifecycle.Dirty)
                    | _     => none
                  else some s2) := by
        unfold freshnessStep; rw [hk]; rfl
      rw [hf2] at h2
      by_cases hin : siteInAncillaModel model q = true
      · rw [if_pos hin] at h2
        cases hL2 : lifecycleOf s2 q with
        | Live =>
            rw [hL2] at h2; injection h2 with he2; subst he2
            have hL1 : lifecycleOf s1 q = SiteLifecycle.Live :=
              (state_equivalent_live_iff q hEq).mpr hL2
            rw [hf1, if_pos hin, hL1]
            exact ⟨setLifecycle s1 q SiteLifecycle.Dirty, rfl,
                   state_equivalent_set_same hEq q SiteLifecycle.Dirty⟩
        | Free => rw [hL2] at h2; exact absurd h2 (by simp)
        | Dirty => rw [hL2] at h2; exact absurd h2 (by simp)
      · rw [if_neg hin] at h2
        injection h2 with he2; subst he2
        rw [hf1, if_neg hin]
        exact ⟨s1, rfl, hEq⟩
  | RequestFreshAncilla site =>
      have hf1 : freshnessStep model s1 sc
              = (if siteInAncillaModel model site then
                    match lifecycleOf s1 site with
                    | .Live => none
                    | _     => some (setLifecycle s1 site SiteLifecycle.Live)
                  else some s1) := by
        unfold freshnessStep; rw [hk]; rfl
      have hf2 : freshnessStep model s2 sc
              = (if siteInAncillaModel model site then
                    match lifecycleOf s2 site with
                    | .Live => none
                    | _     => some (setLifecycle s2 site SiteLifecycle.Live)
                  else some s2) := by
        unfold freshnessStep; rw [hk]; rfl
      rw [hf2] at h2
      by_cases hin : siteInAncillaModel model site = true
      · rw [if_pos hin] at h2
        cases hL2 : lifecycleOf s2 site with
        | Live => rw [hL2] at h2; exact absurd h2 (by simp)
        | Free =>
            rw [hL2] at h2; injection h2 with he2; subst he2
            have hL1 : lifecycleOf s1 site ≠ SiteLifecycle.Live := fun hL =>
              (by rw [(state_equivalent_live_iff site hEq).mp hL] at hL2 ; exact
                  SiteLifecycle.noConfusion hL2 :
                False)
            rw [hf1, if_pos hin]
            cases hL1k : lifecycleOf s1 site with
            | Live => exact absurd hL1k hL1
            | Free =>
                exact ⟨setLifecycle s1 site SiteLifecycle.Live, rfl,
                       state_equivalent_set_same hEq site SiteLifecycle.Live⟩
            | Dirty =>
                exact ⟨setLifecycle s1 site SiteLifecycle.Live, rfl,
                       state_equivalent_set_same hEq site SiteLifecycle.Live⟩
        | Dirty =>
            rw [hL2] at h2; injection h2 with he2; subst he2
            have hL1 : lifecycleOf s1 site ≠ SiteLifecycle.Live := fun hL =>
              (by rw [(state_equivalent_live_iff site hEq).mp hL] at hL2 ; exact
                  SiteLifecycle.noConfusion hL2 :
                False)
            rw [hf1, if_pos hin]
            cases hL1k : lifecycleOf s1 site with
            | Live => exact absurd hL1k hL1
            | Free =>
                exact ⟨setLifecycle s1 site SiteLifecycle.Live, rfl,
                       state_equivalent_set_same hEq site SiteLifecycle.Live⟩
            | Dirty =>
                exact ⟨setLifecycle s1 site SiteLifecycle.Live, rfl,
                       state_equivalent_set_same hEq site SiteLifecycle.Live⟩
      · rw [if_neg hin] at h2
        injection h2 with he2; subst he2
        rw [hf1, if_neg hin]
        exact ⟨s1, rfl, hEq⟩

theorem runFreshness_state_equivalent_some_form
    (model : AncillaModel) (sched : List SysCall)
    (s1 s2 s2' : List (Nat × SiteLifecycle))
    (hEq : state_equivalent s1 s2)
    (h2 : runFreshness model s2 sched = some s2') :
    ∃ s1', runFreshness model s1 sched = some s1' ∧ state_equivalent s1' s2' := by
  induction sched generalizing s1 s2 with
  | nil =>
      simp [runFreshness] at h2
      subst h2
      refine ⟨s1, ?_, hEq⟩
      simp [runFreshness]
  | cons sc rest ih =>
      simp only [runFreshness] at h2
      cases hstep2 : freshnessStep model s2 sc with
      | none => rw [hstep2] at h2; simp at h2
      | some t2 =>
          rw [hstep2] at h2
          dsimp only at h2
          obtain ⟨t1, hstep1, hEq_t⟩ :=
            freshnessStep_state_equivalent_some_form model sc s1 s2 t2 hEq hstep2
          obtain ⟨s1', hrun1, hEq_s⟩ := ih t1 t2 hEq_t h2
          refine ⟨s1', ?_, hEq_s⟩
          simp only [runFreshness, hstep1]
          exact hrun1

/-! ### §12.c Freshness preservation under `seqSchedules`

    `seqSchedules xs ys = xs ++ shiftSchedule (W xs) ys`.
    The freshness check is shift-invariant by
    `runFreshness_shiftSchedule`, so we essentially compose
    walking xs (which leaves a clean / no-dangling-Live state)
    with walking ys from that state (which equals walking ys
    from `[]` up to state-equivalence).  Concluding
    no-dangling-Live for the composition uses normalization +
    reverse-boundary. -/

theorem ancilla_freshness_ok_seqSchedules
    (model : AncillaModel) (xs ys : List SysCall)
    (hxs : ancilla_freshness_ok model xs = true)
    (hys : ancilla_freshness_ok model ys = true) :
    ancilla_freshness_ok model (seqSchedules xs ys) = true := by
  unfold seqSchedules
  unfold ancilla_freshness_ok at *
  -- Step 1: extract s_xs from hxs
  cases hrun_xs : runFreshness model [] xs with
  | none => rw [hrun_xs] at hxs; simp at hxs
  | some s_xs =>
      rw [hrun_xs] at hxs
      simp at hxs
      -- hxs: noDanglingLive s_xs = true
      cases hrun_ys : runFreshness model [] ys with
      | none => rw [hrun_ys] at hys; simp at hys
      | some s_ys =>
          rw [hrun_ys] at hys
          simp at hys
          -- hys: noDanglingLive s_ys = true
          rw [runFreshness_append, hrun_xs]
          dsimp only
          rw [runFreshness_shiftSchedule]
          have hequiv_xs_nil : state_equivalent s_xs [] :=
            noDanglingLive_implies_state_equivalent_empty s_xs hxs
          -- Use success-preservation: since s_xs ~ [] and runFreshness from [] succeeds,
          -- runFreshness from s_xs also succeeds with equivalent result.
          obtain ⟨s_xs_ys, hrun_xys, hequiv_xys_sys⟩ :=
            runFreshness_state_equivalent_some_form model ys s_xs [] s_ys
              hequiv_xs_nil hrun_ys
          rw [hrun_xys]
          dsimp only
          -- Goal: noDanglingLive s_xs_ys = true.
          -- s_ys ~ [] (since noDanglingLive s_ys)
          have hequiv_sys_nil : state_equivalent s_ys [] :=
            noDanglingLive_implies_state_equivalent_empty s_ys hys
          -- By transitivity, s_xs_ys ~ []
          have hequiv_xys_nil : state_equivalent s_xs_ys [] :=
            state_equivalent_trans hequiv_xys_sys hequiv_sys_nil
          -- s_xs_ys is normalized (chain through runFreshness)
          have hnorm_sxs : stateNormalized s_xs :=
            runFreshness_preserves_stateNormalized model xs [] s_xs
              stateNormalized_nil hrun_xs
          have hnorm_xys : stateNormalized s_xs_ys :=
            runFreshness_preserves_stateNormalized model ys s_xs s_xs_ys
              hnorm_sxs hrun_xys
          exact state_equivalent_empty_implies_noDanglingLive s_xs_ys
                  hequiv_xys_nil hnorm_xys

/-! ### §12.d Freshness over `seqMany` of replicated block -/

theorem ancilla_freshness_ok_seqMany_replicate_block
    (model : AncillaModel) (block : List SysCall) (n : Nat)
    (hblock : ancilla_freshness_ok model block = true) :
    ancilla_freshness_ok model
        (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero =>
      show ancilla_freshness_ok model [] = true
      simp [ancilla_freshness_ok, runFreshness, noDanglingLive]
  | succ k ih =>
      show ancilla_freshness_ok model
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact ancilla_freshness_ok_seqSchedules model block _ hblock ih

/-! ### §12.e Freshness over `(rep n (atom block)).expand`

    Note: `CompressedSchedule.atom` is only the current
    implementation-level constructor name for a leaf schedule
    block.  It is NOT a claim that the schedule is a
    hardware-atomic operation.  The block can represent any
    cross-layer verified schedule block (PPM, lattice surgery,
    neutral-atom movement, ion shuttling, superconducting
    routing, factory/decoder service, etc.). -/

theorem ancilla_freshness_ok_repeated_block_expand
    (model : AncillaModel) (block : List SysCall) (n : Nat)
    (hblock : ancilla_freshness_ok model block = true) :
    ancilla_freshness_ok model
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact ancilla_freshness_ok_seqMany_replicate_block model block n hblock

/-! ### §12.f Obligation-C headline

    The body extraction `symbolic_rep_ok_implies_body_ancilla_freshness_ok`
    is defined later in the file; the headline theorem
    combining it with §12.e is added in §12.g (right after
    the extraction lemma) to keep declaration order linear. -/


/-! ### §11.k Symbolic-repeat extraction theorems

    Even though the parametric repeat-soundness for ancilla
    freshness is gated on normalization, we CAN extract the
    body-freshness fact from the strict bundle.  This gives
    the chain
      symbolic_rep_strict_ok models body n = true
      → ancilla_freshness_ok models.ancillaModel body = true
    which becomes the headline once the
    `ancilla_freshness_ok_seqMany_replicate` theorem closes. -/

theorem symbolic_rep_ok_implies_body_ancilla_freshness_ok
    (models : SystemModels) (body : List SysCall) (n : Nat)
    (h : symbolic_rep_strict_ok models body n = true) :
    ancilla_freshness_ok models.ancillaModel body = true := by
  have hbody : all_invariants_strict_with_slot_capacity_and_freshness_ok
      models.arch models.opCap models.slotCap models.ancillaModel
      body
      models.t_react_us models.window_us models.max_per_window = true :=
    symbolic_rep_ok_implies_body_ok models body n h
  unfold all_invariants_strict_with_slot_capacity_and_freshness_ok at hbody
  simp only [Bool.and_eq_true] at hbody
  exact hbody.2

/-! ### §12.g Obligation-C headline

    Symbolic-repeat acceptance ⇒ expanded freshness for any
    leaf schedule block.

    Note: `CompressedSchedule.atom` is the implementation
    constructor for a leaf schedule block; the block itself
    can be any cross-layer verified schedule (PPM, lattice
    surgery, neutral-atom movement, ion shuttling,
    superconducting routing, factory/decoder service, etc.). -/

theorem symbolic_rep_implies_expanded_block_ancilla_freshness_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    ancilla_freshness_ok models.ancillaModel
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true :=
  ancilla_freshness_ok_repeated_block_expand models.ancillaModel block n
    (symbolic_rep_ok_implies_body_ancilla_freshness_ok models block n hSym)

end FormalRV.System.CompressedRepeatSoundness
