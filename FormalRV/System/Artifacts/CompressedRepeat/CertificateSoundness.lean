/-
  Recursive compressed-schedule certificate and its soundness.

  `compressed_schedule_strict_certificate_ok` accepts `atom` leaves
  (strict bundle + within-wallclock + no-magic), `rep n (atom _)`
  (via `symbolic_rep_strict_ok_within`), and `seq` of supported
  children; `par` and nested `rep` are conservatively rejected.  The
  mutual soundness theorem carries strict bundle + within-wallclock +
  no-magic through `seqSchedules`; the general entry point is
  `compressed_schedule_strict_soundness` (consumed by
  PPM/QECBridge/LayeredPPMQECInterface).  No `sorry`, no custom
  `axiom`.
-/

import FormalRV.System.Artifacts.LayeredArtifactInterface
import FormalRV.System.Artifacts.CompressedRepeat.ShiftInvariance
import FormalRV.System.Artifacts.CompressedRepeat.FeedbackAfterDecode
import FormalRV.System.Artifacts.CompressedRepeat.FreshnessSoundness
import FormalRV.System.Artifacts.CompressedRepeat.ExclusivitySeq
import FormalRV.System.Artifacts.CompressedRepeat.CapacitySeq
import FormalRV.System.Artifacts.CompressedRepeat.InvariantChains
import FormalRV.System.Artifacts.CompressedRepeat.SymbolicRepeatSoundness

namespace FormalRV.System.CompressedRepeatSoundness

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.AdderSystem
open FormalRV.System.LayeredArtifactInterface

/-! ## §13.D1 Hardware-generic compressed-schedule certificate.

    `CompressedSchedule` has four constructors:

      * `atom : List SysCall → CompressedSchedule` —
        a leaf schedule block.
      * `seq  : List CompressedSchedule → CompressedSchedule` —
        sequential composition of children.
      * `par  : List CompressedSchedule → CompressedSchedule` —
        parallel composition of children.
      * `rep  : Nat → CompressedSchedule → CompressedSchedule` —
        repeated composition of one child.

    `CompressedSchedule.atom` is the implementation-level
    constructor for a compressed leaf schedule block; the
    block itself is hardware-generic — it may represent a PPM
    block, lattice-surgery gadget, neutral-atom routing
    schedule, superconducting routing block, ion-trap shuttling
    block, factory/decoder service block, or any other verified
    system-level schedule block.

    This tick lands the FIRST version of a recursive
    certificate predicate.  Two shapes are accepted:

      * `atom block` — a leaf passes iff it directly satisfies
        the strict bundle AND `scheduleWithinWallclock`.
      * `rep n (atom block)` — a repeated leaf passes iff
        `symbolic_rep_strict_ok_within` accepts the body.

    All other shapes are conservatively rejected (return
    `false`).  Parallel composition is intentionally
    conservative until we add cross-resource/capacity
    certificates; sequential composition with bookkeeping is
    similarly deferred to a later tick. -/

mutual
  def compressed_schedule_strict_certificate_ok
      (models : SystemModels) : CompressedSchedule → Bool
    | .atom block =>
        all_invariants_strict_with_slot_capacity_and_freshness_ok
            models.arch models.opCap models.slotCap models.ancillaModel block
            models.t_react_us models.window_us models.max_per_window
          && scheduleWithinWallclock block
          && decide ((block.filter (fun sc => kindIsMagicReq sc.kind)).length = 0)
    | .rep n body =>
        match body with
        | .atom block => symbolic_rep_strict_ok_within models block n
        | _           => false
    | .seq children =>
        compressed_schedule_strict_certificate_ok_list models children
    | .par _ => false

  def compressed_schedule_strict_certificate_ok_list
      (models : SystemModels) : List CompressedSchedule → Bool
    | []        => true
    | c :: rest =>
        compressed_schedule_strict_certificate_ok models c
          && compressed_schedule_strict_certificate_ok_list models rest
end

/-! ### §13.D1.a Compatibility lemma for repeated leaf
       schedule blocks. -/

theorem compressed_schedule_cert_repeated_leaf_eq_symbolic_rep_strict_ok_within
    (models : SystemModels) (block : List SysCall) (n : Nat) :
    compressed_schedule_strict_certificate_ok models
        (CompressedSchedule.rep n (CompressedSchedule.atom block))
      = symbolic_rep_strict_ok_within models block n := rfl

theorem compressed_schedule_cert_repeated_leaf_of_symbolic_rep_strict_ok_within
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (h : symbolic_rep_strict_ok_within models block n = true) :
    compressed_schedule_strict_certificate_ok models
        (CompressedSchedule.rep n (CompressedSchedule.atom block)) = true := by
  rw [compressed_schedule_cert_repeated_leaf_eq_symbolic_rep_strict_ok_within]
  exact h

/-! ### §13.D1.b Compatibility lemma for leaf schedule blocks.

    The leaf certificate now bundles three facts on the block:
    the strict invariant bundle, within-wallclock, and the
    no-magic-request structural condition (mirroring
    `repeat_safe_block_ok`'s boundary-clean conjunct).  The
    no-magic conjunct lets the seq-composition strict-bundle
    theorem discharge `window_throughput_ok` vacuously across
    the boundary. -/

theorem compressed_schedule_cert_leaf_eq_strict_within_and_no_magic
    (models : SystemModels) (block : List SysCall) :
    compressed_schedule_strict_certificate_ok models
        (CompressedSchedule.atom block)
      = (all_invariants_strict_with_slot_capacity_and_freshness_ok
            models.arch models.opCap models.slotCap models.ancillaModel block
            models.t_react_us models.window_us models.max_per_window
         && scheduleWithinWallclock block
         && decide ((block.filter (fun sc => kindIsMagicReq sc.kind)).length = 0))
      := rfl

/-! ### §13.D1.c First general soundness theorem — repeated
       leaf schedule blocks via the new certificate. -/

theorem compressed_schedule_strict_soundness_repeated_leaf
    (models : SystemModels) (block : List SysCall) (n : Nat)
    (hCert :
      compressed_schedule_strict_certificate_ok models
          (CompressedSchedule.rep n (CompressedSchedule.atom block)) = true) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch
        models.opCap
        models.slotCap
        models.ancillaModel
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand
        models.t_react_us
        models.window_us
        models.max_per_window = true := by
  rw [compressed_schedule_cert_repeated_leaf_eq_symbolic_rep_strict_ok_within]
    at hCert
  exact symbolic_rep_strict_ok_within_implies_expanded_block_strict_ok
    models block n hCert

/-! ### §13.D1.d Leaf-schedule-block soundness via the new
       certificate.

    The strict-bundle conjunct of the leaf certificate is the
    first of three.  Extract it; `(.atom block).expand = block`. -/

theorem compressed_schedule_strict_soundness_leaf
    (models : SystemModels) (block : List SysCall)
    (hCert :
      compressed_schedule_strict_certificate_ok models
          (CompressedSchedule.atom block) = true) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch
        models.opCap
        models.slotCap
        models.ancillaModel
        (CompressedSchedule.atom block).expand
        models.t_react_us
        models.window_us
        models.max_per_window = true := by
  rw [compressed_schedule_cert_leaf_eq_strict_within_and_no_magic] at hCert
  rw [expand_atom]
  simp only [Bool.and_eq_true] at hCert
  exact hCert.1.1

/-! ## §13.D2 Sequential composition support for compressed
       schedules.

    To extend the compressed-schedule certificate to
    `.seq children`, we need preservation of the strict
    invariant bundle under `seqSchedules`.  This in turn
    requires:

      * `scheduleWithinWallclock` preservation under
        `seqSchedules`;
      * No-magic preservation under `seqSchedules` (used to
        discharge `window_throughput_ok` vacuously across the
        boundary).

    Parallel composition is still conservatively rejected
    (the `.par _` arm of the certificate returns `false`)
    until we add cross-resource/capacity certificates. -/

/-! ### §13.D2.a `foldl`-max helpers + `end_us ≤ wallclock`
       characterization. -/

private theorem foldl_max_end_us_ge_acc
    (xs : List SysCall) (acc : Nat) :
    acc ≤ xs.foldl (fun a s => Nat.max a s.end_us) acc := by
  induction xs generalizing acc with
  | nil => exact Nat.le_refl _
  | cons x rest ih =>
      show acc ≤ rest.foldl _ (Nat.max acc x.end_us)
      exact Nat.le_trans (Nat.le_max_left _ _) (ih (Nat.max acc x.end_us))

private theorem foldl_max_end_us_ge_of_mem
    (xs : List SysCall) (sc : SysCall) (h : sc ∈ xs) (acc : Nat) :
    sc.end_us ≤ xs.foldl (fun a s => Nat.max a s.end_us) acc := by
  induction xs generalizing acc with
  | nil => exact absurd h (List.not_mem_nil)
  | cons x rest ih =>
      rw [List.mem_cons] at h
      rcases h with heq | hrest
      · subst heq
        show sc.end_us ≤ rest.foldl _ (Nat.max acc sc.end_us)
        exact Nat.le_trans (Nat.le_max_right _ _)
          (foldl_max_end_us_ge_acc rest (Nat.max acc sc.end_us))
      · exact ih hrest _

theorem end_us_le_scheduleWallclockUs
    (xs : List SysCall) (sc : SysCall) (h : sc ∈ xs) :
    sc.end_us ≤ scheduleWallclockUs xs :=
  foldl_max_end_us_ge_of_mem xs sc h 0

/-! ### §13.D2.b `scheduleWithinWallclock` preservation. -/

theorem scheduleWithinWallclock_seqSchedules
    (xs ys : List SysCall)
    (hxs : scheduleWithinWallclock xs = true)
    (hys : scheduleWithinWallclock ys = true) :
    scheduleWithinWallclock (seqSchedules xs ys) = true := by
  show scheduleWithinWallclock (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  unfold scheduleWithinWallclock
  rw [List.all_append, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- For sc ∈ xs.
    rw [List.all_eq_true]
    intro sc hsc
    have h_pos : sc.begin_us < sc.end_us :=
      scheduleWithinWallclock_begin_lt_end xs sc hsc hxs
    have h_le : sc.end_us
        ≤ scheduleWallclockUs (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) :=
      end_us_le_scheduleWallclockUs _ sc
        (List.mem_append.mpr (Or.inl hsc))
    simp [h_pos, h_le]
  · -- For sc ∈ shiftSchedule W ys.
    rw [List.all_eq_true]
    intro sc hsc
    unfold shiftSchedule at hsc
    rw [List.mem_map] at hsc
    obtain ⟨sc', hsc'_mem, hsc'_eq⟩ := hsc
    have h_pos_orig : sc'.begin_us < sc'.end_us :=
      scheduleWithinWallclock_begin_lt_end ys sc' hsc'_mem hys
    have h_pos : sc.begin_us < sc.end_us := by
      subst hsc'_eq
      show sc'.begin_us + scheduleWallclockUs xs
          < sc'.end_us + scheduleWallclockUs xs
      omega
    have h_le : sc.end_us
        ≤ scheduleWallclockUs (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) :=
      end_us_le_scheduleWallclockUs _ sc
        (List.mem_append.mpr (Or.inr (by
          unfold shiftSchedule
          exact List.mem_map.mpr ⟨sc', hsc'_mem, hsc'_eq⟩)))
    simp [h_pos, h_le]

theorem scheduleWithinWallclock_seqMany_replicate_block
    (block : List SysCall) (n : Nat)
    (hblock : scheduleWithinWallclock block = true) :
    scheduleWithinWallclock (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show scheduleWithinWallclock
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact scheduleWithinWallclock_seqSchedules block _ hblock ih

theorem scheduleWithinWallclock_repeated_block_expand
    (block : List SysCall) (n : Nat)
    (hblock : scheduleWithinWallclock block = true) :
    scheduleWithinWallclock
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact scheduleWithinWallclock_seqMany_replicate_block block n hblock

/-! ### §13.D2.c No-magic preservation and
       `window_throughput_ok` seqSchedules. -/

theorem magic_count_seqSchedules (xs ys : List SysCall) :
    ((seqSchedules xs ys).filter (fun sc => kindIsMagicReq sc.kind)).length
      = (xs.filter (fun sc => kindIsMagicReq sc.kind)).length
        + (ys.filter (fun sc => kindIsMagicReq sc.kind)).length := by
  show (((xs ++ shiftSchedule (scheduleWallclockUs xs) ys)).filter _).length = _
  rw [magic_count_append, magic_count_shiftSchedule]

theorem window_throughput_ok_seqSchedules_of_no_magic
    (xs ys : List SysCall) (window_us max_per_window : Nat)
    (hxs : (xs.filter (fun sc => kindIsMagicReq sc.kind)).length = 0)
    (hys : (ys.filter (fun sc => kindIsMagicReq sc.kind)).length = 0) :
    window_throughput_ok (seqSchedules xs ys) window_us max_per_window = true := by
  apply window_throughput_ok_of_no_magic
  rw [magic_count_seqSchedules, hxs, hys]

/-! ### §13.D2.d Strict-bundle theorem for sequential
       composition.

    Combines:
    * the eleven per-conjunct `_seqSchedules` lemmas closed
      in §10 and §13.a;
    * the no-magic hypotheses on both halves (used to
      discharge `window_throughput_ok` vacuously). -/

theorem all_invariants_strict_with_slot_capacity_and_freshness_ok_seqSchedules
    (models : SystemModels) (xs ys : List SysCall)
    (hxs :
      all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch models.opCap models.slotCap models.ancillaModel xs
        models.t_react_us models.window_us models.max_per_window = true)
    (hys :
      all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch models.opCap models.slotCap models.ancillaModel ys
        models.t_react_us models.window_us models.max_per_window = true)
    (hwithin_xs : scheduleWithinWallclock xs = true)
    (hnoMagic_xs :
      (xs.filter (fun sc => kindIsMagicReq sc.kind)).length = 0)
    (hnoMagic_ys :
      (ys.filter (fun sc => kindIsMagicReq sc.kind)).length = 0) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch models.opCap models.slotCap models.ancillaModel
        (seqSchedules xs ys)
        models.t_react_us models.window_us models.max_per_window = true := by
  unfold all_invariants_strict_with_slot_capacity_and_freshness_ok
         all_invariants_strict_with_slot_capacity_ok
         all_invariants_strict_ok
         all_invariants_with_factory_ports_ok at hxs hys ⊢
  simp only [Bool.and_eq_true] at hxs hys
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact capacity_in_arch_ok_seqSchedules _ xs ys hxs.1.1.1.1.1.1.1.1.1.1
      hys.1.1.1.1.1.1.1.1.1.1
  · exact capacity_per_cycle_ok_seqSchedules _ xs ys hxs.1.1.1.1.1.1.1.1.1.2
      hys.1.1.1.1.1.1.1.1.1.2 hwithin_xs
  · exact exclusivity_ok_seqSchedules xs ys hxs.1.1.1.1.1.1.1.1.2
      hys.1.1.1.1.1.1.1.1.2 hwithin_xs
  · exact factory_exclusivity_ok_seqSchedules xs ys hxs.1.1.1.1.1.1.1.2
      hys.1.1.1.1.1.1.1.2 hwithin_xs
  · exact feedback_latency_ok_seqSchedules _ xs ys hxs.1.1.1.1.1.1.2
      hys.1.1.1.1.1.1.2
  · exact decoder_react_ok_seqSchedules _ xs ys hxs.1.1.1.1.1.2
      hys.1.1.1.1.1.2
  · exact window_throughput_ok_seqSchedules_of_no_magic xs ys _ _
      hnoMagic_xs hnoMagic_ys
  · exact operation_capacity_ok_seqSchedules _ xs ys hxs.1.1.1.2
      hys.1.1.1.2 hwithin_xs
  · exact feedback_after_decode_ok_seqSchedules xs ys hxs.1.1.2 hys.1.1.2
  · exact slot_capacity_ok_seqSchedules _ xs ys hxs.1.2 hys.1.2 hwithin_xs
  · exact ancilla_freshness_ok_seqSchedules _ xs ys hxs.2 hys.2

/-! ### §13.D2.e Helpers for `(.seq _).expand`. -/

theorem expand_seq_cons (c : CompressedSchedule) (rest : List CompressedSchedule) :
    (CompressedSchedule.seq (c :: rest)).expand
      = seqSchedules c.expand (CompressedSchedule.seq rest).expand := by
  simp [CompressedSchedule.expand, seqManySchedules]

/-- Strict bundle is trivially true on the empty schedule. -/
theorem strict_bundle_empty (models : SystemModels) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch models.opCap models.slotCap models.ancillaModel
        []
        models.t_react_us models.window_us models.max_per_window = true := by
  unfold all_invariants_strict_with_slot_capacity_and_freshness_ok
         all_invariants_strict_with_slot_capacity_ok
         all_invariants_strict_ok
         all_invariants_with_factory_ports_ok
  rfl

theorem scheduleWithinWallclock_empty :
    scheduleWithinWallclock ([] : List SysCall) = true := rfl

theorem magic_count_empty :
    (([] : List SysCall).filter (fun sc => kindIsMagicReq sc.kind)).length = 0 :=
  rfl

/-! ### §13.D2.f Recursive soundness: certificate ⇒ strict
       bundle, within-wallclock, AND no-magic on the
       expansion.

    Key recursive theorem.  The three-way conjunction is
    necessary so the seq induction can use all three on each
    child to compose with the next prefix.

    Proved as a `mutual` pair matching the mutual structure
    of `compressed_schedule_strict_certificate_ok` and its
    list helper. -/

mutual
  theorem compressed_schedule_cert_sound_and_within_and_no_magic
      (models : SystemModels) (cs : CompressedSchedule)
      (hCert : compressed_schedule_strict_certificate_ok models cs = true) :
      all_invariants_strict_with_slot_capacity_and_freshness_ok
          models.arch models.opCap models.slotCap models.ancillaModel
          cs.expand
          models.t_react_us models.window_us models.max_per_window = true
        ∧ scheduleWithinWallclock cs.expand = true
        ∧ (cs.expand.filter (fun sc => kindIsMagicReq sc.kind)).length = 0 := by
    cases cs with
    | atom block =>
        rw [compressed_schedule_cert_leaf_eq_strict_within_and_no_magic] at hCert
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hCert
        rw [expand_atom]
        exact ⟨hCert.1.1, hCert.1.2, hCert.2⟩
    | rep n body =>
        cases body with
        | atom block =>
            have hCertW :
                symbolic_rep_strict_ok_within models block n = true := by
              rw [← compressed_schedule_cert_repeated_leaf_eq_symbolic_rep_strict_ok_within]
              exact hCert
            refine ⟨?_, ?_, ?_⟩
            · exact symbolic_rep_strict_ok_within_implies_expanded_block_strict_ok
                models block n hCertW
            · exact scheduleWithinWallclock_repeated_block_expand block n
                (symbolic_rep_strict_ok_within_implies_scheduleWithinWallclock
                  models block n hCertW)
            · exact magic_count_repeated_block_expand block n
                (symbolic_rep_ok_implies_body_no_magic models block n
                  (symbolic_rep_strict_ok_within_implies_symbolic_rep_strict_ok
                    models block n hCertW))
        | seq _ => simp [compressed_schedule_strict_certificate_ok] at hCert
        | par _ => simp [compressed_schedule_strict_certificate_ok] at hCert
        | rep _ _ => simp [compressed_schedule_strict_certificate_ok] at hCert
    | seq children =>
        have hCertList :
            compressed_schedule_strict_certificate_ok_list models children = true :=
          hCert
        exact compressed_schedule_cert_list_sound_and_within_and_no_magic
          models children hCertList
    | par _ => simp [compressed_schedule_strict_certificate_ok] at hCert

  theorem compressed_schedule_cert_list_sound_and_within_and_no_magic
      (models : SystemModels) (children : List CompressedSchedule)
      (hCert :
        compressed_schedule_strict_certificate_ok_list models children = true) :
      all_invariants_strict_with_slot_capacity_and_freshness_ok
          models.arch models.opCap models.slotCap models.ancillaModel
          (CompressedSchedule.seq children).expand
          models.t_react_us models.window_us models.max_per_window = true
        ∧ scheduleWithinWallclock (CompressedSchedule.seq children).expand = true
        ∧ ((CompressedSchedule.seq children).expand.filter
              (fun sc => kindIsMagicReq sc.kind)).length = 0 := by
    cases children with
    | nil =>
        rw [expand_seq_nil]
        exact ⟨strict_bundle_empty models, scheduleWithinWallclock_empty,
               magic_count_empty⟩
    | cons c rest =>
        have hCert_unfolded :
            (compressed_schedule_strict_certificate_ok models c
              && compressed_schedule_strict_certificate_ok_list models rest)
              = true := hCert
        rw [Bool.and_eq_true] at hCert_unfolded
        obtain ⟨hCert_c, hCert_rest⟩ := hCert_unfolded
        have hc :=
          compressed_schedule_cert_sound_and_within_and_no_magic models c hCert_c
        have hrest :=
          compressed_schedule_cert_list_sound_and_within_and_no_magic
            models rest hCert_rest
        obtain ⟨hc_strict, hc_within, hc_noMagic⟩ := hc
        obtain ⟨hrest_strict, hrest_within, hrest_noMagic⟩ := hrest
        rw [expand_seq_cons]
        refine ⟨?_, ?_, ?_⟩
        · exact all_invariants_strict_with_slot_capacity_and_freshness_ok_seqSchedules
            models c.expand _ hc_strict hrest_strict hc_within hc_noMagic
            hrest_noMagic
        · exact scheduleWithinWallclock_seqSchedules c.expand _
            hc_within hrest_within
        · rw [magic_count_seqSchedules, hc_noMagic, hrest_noMagic]
end

/-! ### §13.D2.g Seq soundness theorem. -/

theorem compressed_schedule_strict_soundness_seq
    (models : SystemModels) (children : List CompressedSchedule)
    (hCert :
      compressed_schedule_strict_certificate_ok models
          (CompressedSchedule.seq children) = true) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch
        models.opCap
        models.slotCap
        models.ancillaModel
        (CompressedSchedule.seq children).expand
        models.t_react_us
        models.window_us
        models.max_per_window = true :=
  (compressed_schedule_cert_sound_and_within_and_no_magic models
      (CompressedSchedule.seq children) hCert).1

/-! ### §13.D2.g General soundness theorem.

    A single entry point for the strict-bundle conclusion on
    the expansion of any compressed schedule whose certificate
    passes — covers atom, rep n atom, and seq of supported
    children.  par and the unsupported rep variants are
    rejected at the certificate level. -/

theorem compressed_schedule_strict_soundness
    (models : SystemModels) (cs : CompressedSchedule)
    (hCert : compressed_schedule_strict_certificate_ok models cs = true) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch
        models.opCap
        models.slotCap
        models.ancillaModel
        cs.expand
        models.t_react_us
        models.window_us
        models.max_per_window = true :=
  (compressed_schedule_cert_sound_and_within_and_no_magic models cs hCert).1

end FormalRV.System.CompressedRepeatSoundness
