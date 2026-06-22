/-
  Parametric symbolic-repeat soundness (Obligations A/B/C).

  `symbolic_rep_strict_ok` is reps-independent by design: it checks
  the body once, never `n` copies.  This file proves that design
  sound: acceptance implies the EXPANDED n-fold schedule passes the
  strict bundle, for arbitrary `n`.  Contents: per-conjunct body
  extraction from `symbolic_rep_strict_ok`, expanded-form headlines
  for every strict-bundle conjunct, the combined theorem
  `symbolic_rep_implies_expanded_block_strict_ok`, and the
  self-contained certificate `symbolic_rep_strict_ok_within`
  (strict bundle + `scheduleWithinWallclock`) with its soundness
  theorem and the paper-facing alias
  `hardware_generic_repeated_block_strict_soundness`.  Hardware-generic:
  `CompressedSchedule.atom` is a leaf schedule block of any backend,
  not a hardware-atomic operation.  No `sorry`, no custom `axiom`.
-/

import FormalRV.System.Artifacts.LayeredArtifactInterface
import FormalRV.System.Artifacts.CompressedRepeat.ShiftInvariance
import FormalRV.System.Artifacts.CompressedRepeat.FeedbackAfterDecode
import FormalRV.System.Artifacts.CompressedRepeat.FreshnessSoundness
import FormalRV.System.Artifacts.CompressedRepeat.ExclusivitySeq
import FormalRV.System.Artifacts.CompressedRepeat.CapacitySeq
import FormalRV.System.Artifacts.CompressedRepeat.InvariantChains

namespace FormalRV.System.CompressedRepeatSoundness

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.AdderSystem
open FormalRV.System.LayeredArtifactInterface

/-! ### §13.b Symbolic-repeat body-level extraction theorems

    Each extraction pulls one body-level A-conjunct out of
    `symbolic_rep_strict_ok` acceptance; the headline theorems
    below (§13.b.5–.12) chain them through the per-invariant
    repeat lemmas of the other CompressedRepeat pieces to the
    expanded form. -/

theorem symbolic_rep_ok_implies_body_exclusivity_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    exclusivity_ok block = true := by
  have hbody := symbolic_rep_ok_implies_body_ok models block n hSym
  unfold all_invariants_strict_with_slot_capacity_and_freshness_ok
         all_invariants_strict_with_slot_capacity_ok
         all_invariants_strict_ok
         all_invariants_with_factory_ports_ok at hbody
  simp only [Bool.and_eq_true] at hbody
  -- Conjuncts: (capacity_in_arch ∧ capacity_per_cycle ∧ exclusivity ∧ factory_exclusivity
  --             ∧ feedback_latency ∧ decoder_react ∧ window_throughput
  --             ∧ operation_capacity) ∧ feedback_after_decode) ∧ slot_capacity) ∧ ancilla_freshness
  -- exclusivity_ok is the 3rd conjunct in all_invariants_with_factory_ports_ok.
  exact hbody.1.1.1.1.1.1.1.1.2

theorem symbolic_rep_ok_implies_body_factory_exclusivity_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    factory_exclusivity_ok block = true := by
  have hbody := symbolic_rep_ok_implies_body_ok models block n hSym
  unfold all_invariants_strict_with_slot_capacity_and_freshness_ok
         all_invariants_strict_with_slot_capacity_ok
         all_invariants_strict_ok
         all_invariants_with_factory_ports_ok at hbody
  simp only [Bool.and_eq_true] at hbody
  exact hbody.1.1.1.1.1.1.1.2

theorem symbolic_rep_ok_implies_body_operation_capacity_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    operation_capacity_ok models.opCap block = true := by
  have hbody := symbolic_rep_ok_implies_body_ok models block n hSym
  unfold all_invariants_strict_with_slot_capacity_and_freshness_ok
         all_invariants_strict_with_slot_capacity_ok
         all_invariants_strict_ok at hbody
  simp only [Bool.and_eq_true] at hbody
  exact hbody.1.1.1.2

theorem symbolic_rep_ok_implies_body_slot_capacity_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    slot_capacity_ok models.slotCap block = true := by
  have hbody := symbolic_rep_ok_implies_body_ok models block n hSym
  unfold all_invariants_strict_with_slot_capacity_and_freshness_ok
         all_invariants_strict_with_slot_capacity_ok at hbody
  simp only [Bool.and_eq_true] at hbody
  exact hbody.1.2

/-! ### §13.b.5 Headline: symbolic acceptance ⇒ expanded
       `exclusivity_ok`.

    Chains the §13.a parametric chain through the body-level
    extraction `symbolic_rep_ok_implies_body_exclusivity_ok`.
    The `scheduleWithinWallclock block` hypothesis is a
    structural input — the strict bundle alone does not
    enforce strict-positive duration `begin_us < end_us`. -/

theorem symbolic_rep_implies_expanded_block_exclusivity_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true)
    (hwithin : scheduleWithinWallclock block = true) :
    exclusivity_ok
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true :=
  exclusivity_ok_repeated_block_expand block n
    (symbolic_rep_ok_implies_body_exclusivity_ok models block n hSym)
    hwithin

/-! ### §13.b.6 Headline: symbolic acceptance ⇒ expanded
       `factory_exclusivity_ok`.

    Chains the §13.a.9–§13.a.14 factory-exclusivity chain
    through the body-level extraction
    `symbolic_rep_ok_implies_body_factory_exclusivity_ok`.
    Same `scheduleWithinWallclock block` structural input as
    the exclusivity headline. -/

theorem symbolic_rep_implies_expanded_block_factory_exclusivity_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true)
    (hwithin : scheduleWithinWallclock block = true) :
    factory_exclusivity_ok
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true :=
  factory_exclusivity_ok_repeated_block_expand block n
    (symbolic_rep_ok_implies_body_factory_exclusivity_ok models block n hSym)
    hwithin

/-! ### §13.b.7 Headline: symbolic acceptance ⇒ expanded
       `operation_capacity_ok`.

    Chains the §13.a.15–§13.a.21 operation-capacity chain
    through the body-level extraction
    `symbolic_rep_ok_implies_body_operation_capacity_ok`.
    Same `scheduleWithinWallclock block` structural input as
    the exclusivity / factory-exclusivity headlines. -/

theorem symbolic_rep_implies_expanded_block_operation_capacity_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true)
    (hwithin : scheduleWithinWallclock block = true) :
    operation_capacity_ok models.opCap
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true :=
  operation_capacity_ok_repeated_block_expand models.opCap block n
    (symbolic_rep_ok_implies_body_operation_capacity_ok models block n hSym)
    hwithin

/-! ### §13.b.8 Headline: symbolic acceptance ⇒ expanded
       `slot_capacity_ok`.

    Chains the §13.a.22–§13.a.29 slot-capacity chain
    through the body-level extraction
    `symbolic_rep_ok_implies_body_slot_capacity_ok`.
    Same `scheduleWithinWallclock block` structural input as
    the other three A-conjunct headlines. -/

theorem symbolic_rep_implies_expanded_block_slot_capacity_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true)
    (hwithin : scheduleWithinWallclock block = true) :
    slot_capacity_ok models.slotCap
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true :=
  slot_capacity_ok_repeated_block_expand models.slotCap block n
    (symbolic_rep_ok_implies_body_slot_capacity_ok models block n hSym)
    hwithin

/-! ### §13.b.9 Combined-strict headline.

    Conjunction of all four Obligation-A headlines plus the
    already-closed Obligation-B and Obligation-C headlines.
    Each conjunct is a previously-closed `symbolic_rep_strict_ok
    ⇒ expanded predicate = true` lemma; this theorem only
    asserts their joint truth on a single block / `n` pair, so
    the proof is structural conjunction assembly.

    Hypothesis discipline:
    * `hSym : symbolic_rep_strict_ok models block n = true`
      — strict-bundle acceptance on the leaf schedule block.
    * `hwithin : scheduleWithinWallclock block = true` — the
      same hardware-generic structural input required by the
      four A-conjunct headlines (strict positivity of every
      block SysCall duration).  The B / C headlines do not
      consume this hypothesis. -/

theorem symbolic_rep_implies_expanded_block_combined_strict_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true)
    (hwithin : scheduleWithinWallclock block = true) :
    exclusivity_ok
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true
    ∧ factory_exclusivity_ok
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true
    ∧ operation_capacity_ok models.opCap
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true
    ∧ slot_capacity_ok models.slotCap
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true
    ∧ feedback_after_decode_ok
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true
    ∧ ancilla_freshness_ok models.ancillaModel
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact symbolic_rep_implies_expanded_block_exclusivity_ok
      models block n hSym hwithin
  · exact symbolic_rep_implies_expanded_block_factory_exclusivity_ok
      models block n hSym hwithin
  · exact symbolic_rep_implies_expanded_block_operation_capacity_ok
      models block n hSym hwithin
  · exact symbolic_rep_implies_expanded_block_slot_capacity_ok
      models block n hSym hwithin
  · exact symbolic_rep_implies_expanded_feedback_after_decode_ok
      models block n hSym
  · exact symbolic_rep_implies_expanded_block_ancilla_freshness_ok
      models block n hSym

/-! ### §13.b.10 Body extraction for the remaining strict-bundle
       conjuncts.

    Each extraction pulls one Bool out of the bundle via
    `symbolic_rep_ok_implies_body_ok`.  Mirrors the existing
    extraction theorems for `exclusivity_ok`, etc.  Listed in
    bundle-conjunct order so the navigation pattern is
    uniform. -/

theorem symbolic_rep_ok_implies_body_capacity_in_arch_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    capacity_in_arch_ok models.arch block = true := by
  have hbody := symbolic_rep_ok_implies_body_ok models block n hSym
  unfold all_invariants_strict_with_slot_capacity_and_freshness_ok
         all_invariants_strict_with_slot_capacity_ok
         all_invariants_strict_ok
         all_invariants_with_factory_ports_ok at hbody
  simp only [Bool.and_eq_true] at hbody
  exact hbody.1.1.1.1.1.1.1.1.1.1

theorem symbolic_rep_ok_implies_body_capacity_per_cycle_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    capacity_per_cycle_ok models.arch block = true := by
  have hbody := symbolic_rep_ok_implies_body_ok models block n hSym
  unfold all_invariants_strict_with_slot_capacity_and_freshness_ok
         all_invariants_strict_with_slot_capacity_ok
         all_invariants_strict_ok
         all_invariants_with_factory_ports_ok at hbody
  simp only [Bool.and_eq_true] at hbody
  exact hbody.1.1.1.1.1.1.1.1.1.2

theorem symbolic_rep_ok_implies_body_feedback_latency_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    feedback_latency_ok models.arch.t_cycle_us block = true := by
  have hbody := symbolic_rep_ok_implies_body_ok models block n hSym
  unfold all_invariants_strict_with_slot_capacity_and_freshness_ok
         all_invariants_strict_with_slot_capacity_ok
         all_invariants_strict_ok
         all_invariants_with_factory_ports_ok at hbody
  simp only [Bool.and_eq_true] at hbody
  exact hbody.1.1.1.1.1.1.2

theorem symbolic_rep_ok_implies_body_decoder_react_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    decoder_react_ok models.t_react_us block = true := by
  have hbody := symbolic_rep_ok_implies_body_ok models block n hSym
  unfold all_invariants_strict_with_slot_capacity_and_freshness_ok
         all_invariants_strict_with_slot_capacity_ok
         all_invariants_strict_ok
         all_invariants_with_factory_ports_ok at hbody
  simp only [Bool.and_eq_true] at hbody
  exact hbody.1.1.1.1.1.2

theorem symbolic_rep_ok_implies_body_no_magic
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    (block.filter (fun sc => kindIsMagicReq sc.kind)).length = 0 := by
  have hclean := symbolic_rep_ok_implies_body_boundary_clean models block n hSym
  unfold repeat_boundary_clean at hclean
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hclean
  exact hclean.2

/-! ### §13.b.11 Symbolic-repeat headlines for the per-syscall
       and sampled-time A-conjuncts not previously headlined. -/

theorem symbolic_rep_implies_expanded_block_capacity_in_arch_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    capacity_in_arch_ok models.arch
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true :=
  capacity_in_arch_ok_repeated_block_expand models.arch block n
    (symbolic_rep_ok_implies_body_capacity_in_arch_ok models block n hSym)

theorem symbolic_rep_implies_expanded_block_capacity_per_cycle_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true)
    (hwithin : scheduleWithinWallclock block = true) :
    capacity_per_cycle_ok models.arch
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true :=
  capacity_per_cycle_ok_repeated_block_expand models.arch block n
    (symbolic_rep_ok_implies_body_capacity_per_cycle_ok models block n hSym)
    hwithin

theorem symbolic_rep_implies_expanded_block_feedback_latency_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    feedback_latency_ok models.arch.t_cycle_us
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true :=
  feedback_latency_ok_repeated_block_expand models.arch.t_cycle_us block n
    (symbolic_rep_ok_implies_body_feedback_latency_ok models block n hSym)

theorem symbolic_rep_implies_expanded_block_decoder_react_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    decoder_react_ok models.t_react_us
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true :=
  decoder_react_ok_repeated_block_expand models.t_react_us block n
    (symbolic_rep_ok_implies_body_decoder_react_ok models block n hSym)

theorem symbolic_rep_implies_expanded_block_window_throughput_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true) :
    window_throughput_ok
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand
        models.window_us models.max_per_window = true :=
  window_throughput_ok_of_no_magic _ _ _
    (magic_count_repeated_block_expand block n
      (symbolic_rep_ok_implies_body_no_magic models block n hSym))

/-! ### §13.b.12 First major combined symbolic-repeat
       strict-bundle theorem.

    `CompressedSchedule.atom` is the current constructor name
    for a compressed leaf schedule block.  The theorem is
    hardware-generic: the block may represent a PPM block,
    lattice-surgery gadget, neutral-atom movement schedule,
    superconducting routing block, ion-trap shuttling block,
    factory/decoder service block, or any other verified
    system-level schedule block. -/

theorem symbolic_rep_implies_expanded_block_strict_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hSym : symbolic_rep_strict_ok models block n = true)
    (hwithin : scheduleWithinWallclock block = true) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch
        models.opCap
        models.slotCap
        models.ancillaModel
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand
        models.t_react_us
        models.window_us
        models.max_per_window = true := by
  unfold all_invariants_strict_with_slot_capacity_and_freshness_ok
         all_invariants_strict_with_slot_capacity_ok
         all_invariants_strict_ok
         all_invariants_with_factory_ports_ok
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact symbolic_rep_implies_expanded_block_capacity_in_arch_ok
      models block n hSym
  · exact symbolic_rep_implies_expanded_block_capacity_per_cycle_ok
      models block n hSym hwithin
  · exact symbolic_rep_implies_expanded_block_exclusivity_ok
      models block n hSym hwithin
  · exact symbolic_rep_implies_expanded_block_factory_exclusivity_ok
      models block n hSym hwithin
  · exact symbolic_rep_implies_expanded_block_feedback_latency_ok
      models block n hSym
  · exact symbolic_rep_implies_expanded_block_decoder_react_ok
      models block n hSym
  · exact symbolic_rep_implies_expanded_block_window_throughput_ok
      models block n hSym
  · exact symbolic_rep_implies_expanded_block_operation_capacity_ok
      models block n hSym hwithin
  · exact symbolic_rep_implies_expanded_feedback_after_decode_ok
      models block n hSym
  · exact symbolic_rep_implies_expanded_block_slot_capacity_ok
      models block n hSym hwithin
  · exact symbolic_rep_implies_expanded_block_ancilla_freshness_ok
      models block n hSym

/-! ### §13.b.13 Self-contained symbolic-repeat certificate.

    `symbolic_rep_strict_ok` does NOT internally enforce
    `scheduleWithinWallclock body` (it enforces only the strict
    invariant bundle plus `repeat_boundary_clean`, the latter
    requiring `0 < scheduleWallclockUs body` and zero magic
    requests).  Five Obligation-A conjuncts
    (`capacity_per_cycle_ok`, `exclusivity_ok`,
    `factory_exclusivity_ok`, `operation_capacity_ok`,
    `slot_capacity_ok`) consume `scheduleWithinWallclock body`
    as a structural hypothesis — every compiler-emitted block
    satisfies it, but the strict bundle does not derive it.

    We close the gap with a self-contained certificate
    predicate that adds the within-wallclock check.  Existing
    `symbolic_rep_strict_ok` remains untouched. -/

def symbolic_rep_strict_ok_within
    (models : SystemModels) (block : List SysCall) (n : Nat) : Bool :=
  symbolic_rep_strict_ok models block n
  && scheduleWithinWallclock block

theorem symbolic_rep_strict_ok_within_implies_symbolic_rep_strict_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hCert : symbolic_rep_strict_ok_within models block n = true) :
    symbolic_rep_strict_ok models block n = true := by
  unfold symbolic_rep_strict_ok_within at hCert
  exact (Bool.and_eq_true _ _).mp hCert |>.1

theorem symbolic_rep_strict_ok_within_implies_scheduleWithinWallclock
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hCert : symbolic_rep_strict_ok_within models block n = true) :
    scheduleWithinWallclock block = true := by
  unfold symbolic_rep_strict_ok_within at hCert
  exact (Bool.and_eq_true _ _).mp hCert |>.2

/-! ### §13.b.14 Clean combined symbolic-repeat strict-bundle
       theorem.

    `CompressedSchedule.atom` is the implementation-level
    constructor for a compressed leaf schedule block.  The
    theorem is hardware-generic: the block may represent a PPM
    block, lattice-surgery gadget, neutral-atom routing
    schedule, superconducting routing block, ion-trap shuttling
    block, factory/decoder service block, or any other verified
    system-level schedule block. -/

theorem symbolic_rep_strict_ok_within_implies_expanded_block_strict_ok
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hCert : symbolic_rep_strict_ok_within models block n = true) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch
        models.opCap
        models.slotCap
        models.ancillaModel
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand
        models.t_react_us
        models.window_us
        models.max_per_window = true :=
  symbolic_rep_implies_expanded_block_strict_ok models block n
    (symbolic_rep_strict_ok_within_implies_symbolic_rep_strict_ok
      models block n hCert)
    (symbolic_rep_strict_ok_within_implies_scheduleWithinWallclock
      models block n hCert)

/-- Paper-facing alias for §13.b.14.

    The certificate check `symbolic_rep_strict_ok_within` is
    reps-independent by design: it checks the block once;
    this theorem is the soundness of that design for the
    expanded n-fold schedule.

    `CompressedSchedule.atom` is the implementation-level
    constructor for a compressed leaf schedule block.  The
    theorem is hardware-generic: the block may represent a PPM
    block, lattice-surgery gadget, neutral-atom routing
    schedule, superconducting routing block, ion-trap shuttling
    block, factory/decoder service block, or any other verified
    system-level schedule block. -/
theorem hardware_generic_repeated_block_strict_soundness
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hCert : symbolic_rep_strict_ok_within models block n = true) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch
        models.opCap
        models.slotCap
        models.ancillaModel
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand
        models.t_react_us
        models.window_us
        models.max_per_window = true :=
  symbolic_rep_strict_ok_within_implies_expanded_block_strict_ok
    models block n hCert

end FormalRV.System.CompressedRepeatSoundness
