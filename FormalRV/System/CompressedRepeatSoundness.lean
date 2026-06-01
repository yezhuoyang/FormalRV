/-
  FormalRV.Framework.CompressedRepeatSoundness — foundational
  shift / repetition lemmas toward parametric symbolic-repeat
  soundness.

  ## Goal

  Push toward

      symbolic_rep_strict_ok models body n = true
        →
      all_invariants_strict_with_slot_capacity_and_freshness_ok
          ... (rep n (atom body)).expand ... = true

  by establishing the foundational shift / repetition lemmas
  each strict-bundle conjunct needs.

  ## What this tick closes

    (§1) Pure-`rfl` shift lemmas: `kind`, `begin_us`,
         `end_us`, `syscall_acts_on`,
         `syscall_factory_claims` are all `rfl`-preserved
         (or shifted in the obvious way).

    (§2-§4) Shift invariance of the per-call invariants
         that depend only on `kind` and `end_us - begin_us`:
         `capacity_in_arch_ok`, `feedback_latency_ok`,
         `decoder_react_ok`.

    (§5) Ancilla-freshness shift invariance — the freshness
         state machine reads only `sc.kind`.  Closed
         parametrically.

    (§6) No-magic-count preservation under shift.

    (§7) `kindIs*` predicates are shift-invariant.

    (§8) Concrete repeat examples: `n=10` cross-check via
         expansion + `native_decide`; `n=1_000_000` symbolic
         check via the previous tick's
         `symbolic_rep_strict_ok` (NO expansion).

  ## What this tick does NOT close

  The PARAMETRIC theorem
  `symbolic_rep_strict_ok_implies_expanded_strict_ok` for
  arbitrary `n` is NOT proven this tick.  The remaining
  obligation is split into two genuinely harder pieces:

    (A) **Sequential composition** on `seqSchedules xs ys`
        for `exclusivity_ok`, `capacity_per_cycle_ok`,
        `operation_capacity_ok`, `slot_capacity_ok`,
        `factory_exclusivity_ok`.  These all rely on
        argument-window disjointness (a SysCall in `xs`
        ends at `≤ scheduleWallclockUs xs` and a SysCall in
        the shifted `ys` begins at `≥ scheduleWallclockUs xs`,
        so the half-open intervals are disjoint and pairwise
        checks pass).  Each lemma is a small bounded
        argument but the proof is long because the
        pairwise checkers use `List.range n .all (fun i =>
        List.range n .all ...)` over indices.

    (B) **Feedback-after-decode** under
        `seqSchedules`.  The inner `.any` references the
        whole combined list, so the shift-invariance proof
        requires a helper lemma that the inner condition is
        ≤-preserved under uniform `+dt`.

    (C) **Ancilla-freshness state-monotonicity** across the
        boundary.  Each copy's first `RequestFreshAncilla`
        starts from a state in which the previous copy left
        the ancilla sites `Dirty`; the body was validated
        from `Free`.  The `next free site` rule treats
        `Free` and `Dirty` identically, so the trajectory
        is the same — but formalising this requires a
        state-equivalence lemma on `runFreshness`.

  Each obligation is well-scoped; the parametric theorem
  follows by conjunction once all three pieces close.

  No `sorry`.  No custom `axiom`.
-/

import FormalRV.System.LayeredArtifactInterface

namespace FormalRV.Framework.CompressedRepeatSoundness

open FormalRV.Framework
open FormalRV.Framework.Architecture
open FormalRV.Framework.ScheduleInv
open FormalRV.Framework.LatticeSurgeryPPMContract
open FormalRV.Framework.SurgeryGadgetToSysCalls
open FormalRV.Framework.SystemInvariantStrengthening
open FormalRV.Framework.AdderSystem
open FormalRV.Framework.LayeredArtifactInterface

/-! ## §1. Basic shift lemmas (pure `rfl`) -/

@[simp] theorem shiftSysCall_kind (dt : Nat) (sc : SysCall) :
    (shiftSysCall dt sc).kind = sc.kind := rfl

@[simp] theorem shiftSysCall_begin (dt : Nat) (sc : SysCall) :
    (shiftSysCall dt sc).begin_us = sc.begin_us + dt := rfl

@[simp] theorem shiftSysCall_end (dt : Nat) (sc : SysCall) :
    (shiftSysCall dt sc).end_us = sc.end_us + dt := rfl

theorem shiftSysCall_duration (dt : Nat) (sc : SysCall) :
    (shiftSysCall dt sc).end_us - (shiftSysCall dt sc).begin_us
      = sc.end_us - sc.begin_us := by
  simp; omega

theorem syscall_acts_on_shiftSysCall (dt : Nat) (sc : SysCall) :
    syscall_acts_on (shiftSysCall dt sc) = syscall_acts_on sc := rfl

theorem syscall_factory_claims_shiftSysCall (dt : Nat) (sc : SysCall) :
    syscall_factory_claims (shiftSysCall dt sc) = syscall_factory_claims sc := rfl

@[simp] theorem shiftSchedule_nil (dt : Nat) :
    shiftSchedule dt ([] : List SysCall) = [] := rfl

@[simp] theorem shiftSchedule_cons (dt : Nat) (sc : SysCall) (rest : List SysCall) :
    shiftSchedule dt (sc :: rest)
      = shiftSysCall dt sc :: shiftSchedule dt rest := rfl

/-! ## §2. Capacity-in-arch shift invariance -/

theorem capacity_in_arch_ok_shiftSchedule
    (arch : ZonedArch) (dt : Nat) (xs : List SysCall) :
    capacity_in_arch_ok arch (shiftSchedule dt xs)
      = capacity_in_arch_ok arch xs := by
  induction xs with
  | nil => rfl
  | cons sc rest ih =>
    unfold capacity_in_arch_ok at *
    simp [List.all_cons, syscall_acts_on_shiftSysCall, ih]

theorem capacity_in_arch_ok_shiftSchedule_of_ok
    (arch : ZonedArch) (dt : Nat) (xs : List SysCall)
    (h : capacity_in_arch_ok arch xs = true) :
    capacity_in_arch_ok arch (shiftSchedule dt xs) = true := by
  rw [capacity_in_arch_ok_shiftSchedule]; exact h

/-! ## §3. Feedback-latency shift invariance

    The check examines `end_us - begin_us`, which is
    shift-invariant by `shiftSysCall_duration`. -/

theorem feedback_latency_ok_shiftSchedule
    (t_cycle_us dt : Nat) (xs : List SysCall) :
    feedback_latency_ok t_cycle_us (shiftSchedule dt xs)
      = feedback_latency_ok t_cycle_us xs := by
  unfold feedback_latency_ok shiftSchedule
  rw [List.all_map]
  congr 1
  funext sc
  show (match (shiftSysCall dt sc).kind with
        | .PauliFrameUpdate _ =>
            decide ((shiftSysCall dt sc).end_us
                      - (shiftSysCall dt sc).begin_us ≤ t_cycle_us)
        | _ => true)
     = (match sc.kind with
        | .PauliFrameUpdate _ =>
            decide (sc.end_us - sc.begin_us ≤ t_cycle_us)
        | _ => true)
  rw [shiftSysCall_kind]
  cases sc.kind with
  | PauliFrameUpdate _ =>
      simp only [shiftSysCall_end, shiftSysCall_begin]
      have h : (sc.end_us + dt) - (sc.begin_us + dt)
             = sc.end_us - sc.begin_us := by omega
      simp only [h]
  | _ => rfl

theorem feedback_latency_ok_shiftSchedule_of_ok
    (t_cycle_us dt : Nat) (xs : List SysCall)
    (h : feedback_latency_ok t_cycle_us xs = true) :
    feedback_latency_ok t_cycle_us (shiftSchedule dt xs) = true := by
  rw [feedback_latency_ok_shiftSchedule]; exact h

/-! ## §4. Decoder-react shift invariance -/

theorem decoder_react_ok_shiftSchedule
    (t_react_us dt : Nat) (xs : List SysCall) :
    decoder_react_ok t_react_us (shiftSchedule dt xs)
      = decoder_react_ok t_react_us xs := by
  unfold decoder_react_ok shiftSchedule
  rw [List.all_map]
  congr 1
  funext sc
  show (match (shiftSysCall dt sc).kind with
        | .DecodeSyndrome _ =>
            decide ((shiftSysCall dt sc).end_us
                      - (shiftSysCall dt sc).begin_us ≤ t_react_us)
        | _ => true)
     = (match sc.kind with
        | .DecodeSyndrome _ =>
            decide (sc.end_us - sc.begin_us ≤ t_react_us)
        | _ => true)
  rw [shiftSysCall_kind]
  cases sc.kind with
  | DecodeSyndrome _ =>
      simp only [shiftSysCall_end, shiftSysCall_begin]
      have h : (sc.end_us + dt) - (sc.begin_us + dt)
             = sc.end_us - sc.begin_us := by omega
      simp only [h]
  | _ => rfl

theorem decoder_react_ok_shiftSchedule_of_ok
    (t_react_us dt : Nat) (xs : List SysCall)
    (h : decoder_react_ok t_react_us xs = true) :
    decoder_react_ok t_react_us (shiftSchedule dt xs) = true := by
  rw [decoder_react_ok_shiftSchedule]; exact h

/-! ## §5. Ancilla-freshness shift invariance

    `freshnessStep` reads only `sc.kind`; shift preserves
    `kind`.  By induction, the whole walk produces the same
    `Option state` regardless of any `+dt`. -/

theorem freshnessStep_shiftSysCall
    (model : AncillaModel) (state : List (Nat × SiteLifecycle))
    (dt : Nat) (sc : SysCall) :
    freshnessStep model state (shiftSysCall dt sc)
      = freshnessStep model state sc := by
  unfold freshnessStep
  rw [shiftSysCall_kind]

theorem runFreshness_shiftSchedule
    (model : AncillaModel) (state : List (Nat × SiteLifecycle))
    (dt : Nat) (xs : List SysCall) :
    runFreshness model state (shiftSchedule dt xs)
      = runFreshness model state xs := by
  induction xs generalizing state with
  | nil => rfl
  | cons sc rest ih =>
    show runFreshness model state
            (shiftSysCall dt sc :: shiftSchedule dt rest)
       = runFreshness model state (sc :: rest)
    unfold runFreshness
    rw [freshnessStep_shiftSysCall]
    cases freshnessStep model state sc with
    | none      => rfl
    | some st'  => exact ih st'

theorem ancilla_freshness_ok_shiftSchedule
    (model : AncillaModel) (dt : Nat) (xs : List SysCall) :
    ancilla_freshness_ok model (shiftSchedule dt xs)
      = ancilla_freshness_ok model xs := by
  unfold ancilla_freshness_ok
  rw [runFreshness_shiftSchedule]

theorem ancilla_freshness_ok_shiftSchedule_of_ok
    (model : AncillaModel) (dt : Nat) (xs : List SysCall)
    (h : ancilla_freshness_ok model xs = true) :
    ancilla_freshness_ok model (shiftSchedule dt xs) = true := by
  rw [ancilla_freshness_ok_shiftSchedule]; exact h

/-! ## §6. `kindIs*` predicate shift invariance + no-magic
       preservation -/

theorem kindIsMagicReq_shiftSysCall (dt : Nat) (sc : SysCall) :
    kindIsMagicReq (shiftSysCall dt sc).kind = kindIsMagicReq sc.kind := by
  rw [shiftSysCall_kind]

theorem kindIsGate2q_shiftSysCall (dt : Nat) (sc : SysCall) :
    kindIsGate2q (shiftSysCall dt sc).kind = kindIsGate2q sc.kind := by
  rw [shiftSysCall_kind]

theorem kindIsMeasure_shiftSysCall (dt : Nat) (sc : SysCall) :
    kindIsMeasure (shiftSysCall dt sc).kind = kindIsMeasure sc.kind := by
  rw [shiftSysCall_kind]

theorem kindIsDecode_shiftSysCall (dt : Nat) (sc : SysCall) :
    kindIsDecode (shiftSysCall dt sc).kind = kindIsDecode sc.kind := by
  rw [shiftSysCall_kind]

theorem kindIsFeedback_shiftSysCall (dt : Nat) (sc : SysCall) :
    kindIsFeedback (shiftSysCall dt sc).kind = kindIsFeedback sc.kind := by
  rw [shiftSysCall_kind]

theorem kindIsFreshAnc_shiftSysCall (dt : Nat) (sc : SysCall) :
    kindIsFreshAnc (shiftSysCall dt sc).kind = kindIsFreshAnc sc.kind := by
  rw [shiftSysCall_kind]

theorem magic_count_shiftSchedule (dt : Nat) (xs : List SysCall) :
    ((shiftSchedule dt xs).filter (fun sc => kindIsMagicReq sc.kind)).length
      = (xs.filter (fun sc => kindIsMagicReq sc.kind)).length := by
  induction xs with
  | nil => rfl
  | cons sc rest ih =>
    simp only [shiftSchedule_cons, List.filter_cons]
    rw [shiftSysCall_kind]
    by_cases h : kindIsMagicReq sc.kind = true
    · simp [h, ih]
    · simp [h, ih]

theorem no_magic_shiftSchedule
    (dt : Nat) (xs : List SysCall)
    (h : (xs.filter fun sc => kindIsMagicReq sc.kind).length = 0) :
    ((shiftSchedule dt xs).filter fun sc => kindIsMagicReq sc.kind).length = 0 := by
  rw [magic_count_shiftSchedule]; exact h

/-! ## §7. Headline concrete instances (no parametric soundness
       theorem in this tick) -/

/-- `n=10` cross-check via expansion + `native_decide`.  This
    confirms that the strict bundle accepts the EXPANDED
    repeated schedule for a moderately large `n`, grounding
    the symbolic checker against the existing
    expansion-based check. -/
theorem adder_n1_repeated_10_expanded_strict_ok :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        adder_n1_system_models.arch
        adder_n1_system_models.opCap
        adder_n1_system_models.slotCap
        adder_n1_system_models.ancillaModel
        (CompressedSchedule.rep 10 (CompressedSchedule.atom adder_n1_syscalls)).expand
        adder_n1_system_models.t_react_us
        adder_n1_system_models.window_us
        adder_n1_system_models.max_per_window = true := by
  native_decide

/-- **Headline scalability**: `n=1_000_000` symbolic check
    via `symbolic_rep_strict_ok`.  The check is `O(|body|)`,
    independent of `n` — Lean does NOT materialise 1,000,000
    SysCall copies. -/
theorem adder_n1_repeated_1000000_symbolic_ok :
    symbolic_rep_strict_ok
        adder_n1_system_models adder_n1_syscalls 1000000 = true := by
  native_decide

/-- Symbolic wallclock for `rep 1_000_000`: `1_000_000 × 48 =
    48_000_000` µs.  Computed by `CompressedResourceSummary.scale`. -/
theorem adder_n1_repeated_1000000_resource_wallclock :
    (CompressedSchedule.rep 1000000
        (CompressedSchedule.atom adder_n1_syscalls)).resource.wallclock_us
      = 48000000 := by
  native_decide

/-- Symbolic Gate2q count for `rep 1_000_000`: `1_000_000 × 18
    = 18_000_000`. -/
theorem adder_n1_repeated_1000000_resource_gate2q :
    (CompressedSchedule.rep 1000000
        (CompressedSchedule.atom adder_n1_syscalls)).resource.gate2q_count
      = 18000000 := by
  native_decide

/-- Symbolic SysCall count for `rep 1_000_000`: `1_000_000 ×
    48 = 48_000_000`. -/
theorem adder_n1_repeated_1000000_resource_syscall_count :
    (CompressedSchedule.rep 1000000
        (CompressedSchedule.atom adder_n1_syscalls)).resource.syscall_count
      = 48000000 := by
  native_decide

/-! ## §9. Obligation (A) — sequential composition

    `seqSchedules xs ys = xs ++ shiftSchedule (W xs) ys`.

    The four invariants in this obligation are
    `exclusivity_ok`, `factory_exclusivity_ok`,
    `operation_capacity_ok`, `slot_capacity_ok`.

    All four follow from the same structural property:
    **time-window disjointness** between any SysCall in `xs`
    (which ends at `≤ W xs`) and any SysCall in the shifted
    `ys` (which begins at `≥ W xs`).  Their pairwise /
    sampling-based checks can then be discharged: cross-pair
    intervals don't overlap, and same-block pairs are
    inherited from each block's individual validity.

    ### Status this tick

    Parametrically proved:
      * `scheduleWithinWallclock` + member-end-bound
        corollary;
      * `intervals_overlap_shift_same` (uniform-shift
        invariance);
      * `intervals_overlap_disjoint_when_le` (sufficient
        condition by `a_hi ≤ b_lo`);
      * `cross_pair_no_overlap` — the cross-block pair
        non-overlap result.

    Concretely proved (via `native_decide`):
      * `adder_seq2_exclusivity_ok`;
      * `adder_seq2_factory_exclusivity_ok`;
      * `adder_seq2_operation_capacity_ok`;
      * `adder_seq2_slot_capacity_ok`;
      * `adder_seq3_all_pairwise_capacity_ok` (the four
        conjuncts together on a 144-SysCall composition).

    The parametric `exclusivity_ok_seqSchedules` etc. require
    an index-based induction over `List.range n` for the
    pairwise check; that proof is bounded in size but
    long.  Documented in the §8 status block as the
    remaining work for Obligation (A). -/

/-! ### §9.a Schedule-within-wallclock condition -/

/-- A schedule is "within-wallclock" if every SysCall has
    `begin_us < end_us` and `end_us ≤ scheduleWallclockUs xs`.

    The strict inequality `begin_us < end_us` excludes
    zero-duration SysCalls; all compiler-emitted schedules
    satisfy this (durations are positive integers). -/
def scheduleWithinWallclock (xs : List SysCall) : Bool :=
  xs.all fun sc =>
    decide (sc.begin_us < sc.end_us)
    && decide (sc.end_us ≤ scheduleWallclockUs xs)

theorem adder_n1_scheduleWithinWallclock :
    scheduleWithinWallclock adder_n1_syscalls = true := by native_decide

/-- Membership consequence: any SysCall in a within-wallclock
    schedule has `end_us ≤ scheduleWallclockUs xs`. -/
theorem scheduleWithinWallclock_end_le
    (xs : List SysCall) (sc : SysCall)
    (hmem : sc ∈ xs) (h : scheduleWithinWallclock xs = true) :
    sc.end_us ≤ scheduleWallclockUs xs := by
  unfold scheduleWithinWallclock at h
  rw [List.all_eq_true] at h
  have hsc := h sc hmem
  simp [Bool.and_eq_true] at hsc
  exact hsc.2

theorem scheduleWithinWallclock_begin_lt_end
    (xs : List SysCall) (sc : SysCall)
    (hmem : sc ∈ xs) (h : scheduleWithinWallclock xs = true) :
    sc.begin_us < sc.end_us := by
  unfold scheduleWithinWallclock at h
  rw [List.all_eq_true] at h
  have hsc := h sc hmem
  simp [Bool.and_eq_true] at hsc
  exact hsc.1

/-! ### §9.b Shifted second block begins at or after the
       first block's wallclock -/

theorem shifted_begin_ge_offset
    (dt : Nat) (ys : List SysCall) (sc : SysCall)
    (hmem : sc ∈ shiftSchedule dt ys) :
    dt ≤ sc.begin_us := by
  unfold shiftSchedule at hmem
  rw [List.mem_map] at hmem
  obtain ⟨sc', _, hsc⟩ := hmem
  subst hsc
  show dt ≤ sc'.begin_us + dt
  omega

/-! ### §9.c Interval-overlap reasoning -/

/-- `intervals_overlap` is invariant under uniform shift. -/
theorem intervals_overlap_shift_same
    (a_lo a_hi b_lo b_hi dt : Nat) :
    intervals_overlap (a_lo + dt) (a_hi + dt) (b_lo + dt) (b_hi + dt)
      = intervals_overlap a_lo a_hi b_lo b_hi := by
  unfold intervals_overlap
  have h1 : decide (a_lo + dt < b_hi + dt) = decide (a_lo < b_hi) := by
    have : (a_lo + dt < b_hi + dt) ↔ (a_lo < b_hi) := by omega
    simp [this]
  have h2 : decide (b_lo + dt < a_hi + dt) = decide (b_lo < a_hi) := by
    have : (b_lo + dt < a_hi + dt) ↔ (b_lo < a_hi) := by omega
    simp [this]
  rw [h1, h2]

/-- If `a_hi ≤ b_lo`, the half-open intervals
    `[a_lo, a_hi)` and `[b_lo, b_hi)` do not overlap. -/
theorem intervals_overlap_disjoint_when_le
    (a_lo a_hi b_lo b_hi : Nat) (h : a_hi ≤ b_lo) :
    intervals_overlap a_lo a_hi b_lo b_hi = false := by
  unfold intervals_overlap
  have : ¬ (b_lo < a_hi) := by omega
  simp [this]

/-! ### §9.d Cross-pair non-overlap -/

theorem cross_pair_no_overlap
    (xs ys : List SysCall)
    (sc₁ sc₂ : SysCall)
    (h₁ : sc₁ ∈ xs)
    (h₂ : sc₂ ∈ shiftSchedule (scheduleWallclockUs xs) ys)
    (hwithin : scheduleWithinWallclock xs = true) :
    intervals_overlap sc₁.begin_us sc₁.end_us sc₂.begin_us sc₂.end_us = false := by
  have h_end : sc₁.end_us ≤ scheduleWallclockUs xs :=
    scheduleWithinWallclock_end_le xs sc₁ h₁ hwithin
  have h_begin : scheduleWallclockUs xs ≤ sc₂.begin_us :=
    shifted_begin_ge_offset _ ys sc₂ h₂
  have : sc₁.end_us ≤ sc₂.begin_us := by omega
  exact intervals_overlap_disjoint_when_le _ _ _ _ this

/-! ### §9.e Concrete adder seq2 examples for all four
       pairwise / capacity invariants -/

/-- The composition `seqSchedules adder adder` is 96 SysCalls,
    96 µs wallclock. -/
private def adder_seq2 : List SysCall :=
  seqSchedules adder_n1_syscalls adder_n1_syscalls

theorem adder_seq2_length : adder_seq2.length = 96 := by native_decide

theorem adder_seq2_wallclock : scheduleWallclockUs adder_seq2 = 96 := by native_decide

theorem adder_seq2_exclusivity_ok :
    exclusivity_ok adder_seq2 = true := by native_decide

theorem adder_seq2_factory_exclusivity_ok :
    factory_exclusivity_ok adder_seq2 = true := by native_decide

theorem adder_seq2_operation_capacity_ok :
    operation_capacity_ok
        adder_n1_system_models.opCap adder_seq2 = true := by native_decide

theorem adder_seq2_slot_capacity_ok :
    slot_capacity_ok
        adder_n1_system_models.slotCap adder_seq2 = true := by native_decide

/-- **Combined Obligation-A status for adder seq2** (concrete
    instance, not parametric).  All four pairwise / capacity
    invariants hold on `seqSchedules adder adder`. -/
theorem adder_seq2_obligation_A_ok :
    exclusivity_ok adder_seq2 = true
    ∧ factory_exclusivity_ok adder_seq2 = true
    ∧ operation_capacity_ok adder_n1_system_models.opCap adder_seq2 = true
    ∧ slot_capacity_ok adder_n1_system_models.slotCap adder_seq2 = true :=
  ⟨ adder_seq2_exclusivity_ok
  , adder_seq2_factory_exclusivity_ok
  , adder_seq2_operation_capacity_ok
  , adder_seq2_slot_capacity_ok ⟩

/-! ### §9.f Concrete adder seq3 example (144 SysCalls) -/

private def adder_seq3 : List SysCall :=
  seqManySchedules
    [adder_n1_syscalls, adder_n1_syscalls, adder_n1_syscalls]

theorem adder_seq3_length : adder_seq3.length = 144 := by native_decide

theorem adder_seq3_wallclock : scheduleWallclockUs adder_seq3 = 144 := by native_decide

theorem adder_seq3_obligation_A_ok :
    exclusivity_ok adder_seq3 = true
    ∧ factory_exclusivity_ok adder_seq3 = true
    ∧ operation_capacity_ok adder_n1_system_models.opCap adder_seq3 = true
    ∧ slot_capacity_ok adder_n1_system_models.slotCap adder_seq3 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## §10. Obligation (B) — feedback-after-decode under
       shift, append, sequence, and repeat

    The existing `feedback_after_decode_ok` checker uses an
    inner `.any` over the WHOLE schedule:

      sched.all fun sc => match sc.kind with
        | PauliFrameUpdate cid =>
            sched.any fun sc' => match sc'.kind with
              | DecodeSyndrome rid =>
                  decide (rid = cid) && decide (sc'.end_us ≤ sc.begin_us)
              | _ => false
        | _ => true

    This makes parametric proofs harder than for the other
    invariants.  We work around the self-reference by
    introducing a small helper predicate
    `decode_matches_feedback` and proving its preservation
    under uniform shift / append, then lifting to
    `feedback_after_decode_ok`. -/

/-! ### §10.a Helper predicate -/

/-- Does the SysCall `d` count as a decoder match for a
    `PauliFrameUpdate cid` whose `begin_us` is `b`?  Returns
    `true` iff `d.kind = DecodeSyndrome cid` and `d.end_us ≤
    b`.

    This factors the inner-`.any` body of
    `feedback_after_decode_ok`, eliminating the
    self-reference. -/
def decode_matches_feedback (cid b : Nat) (d : SysCall) : Bool :=
  match d.kind with
  | .DecodeSyndrome rid =>
      decide (rid = cid) && decide (d.end_us ≤ b)
  | _ => false

/-! ### §10.b Shift preservation of `decode_matches_feedback` -/

/-- Uniform shift on both the candidate decoder `d` and the
    feedback begin-time `b` preserves matching. -/
theorem decode_matches_feedback_shift_same
    (cid b dt : Nat) (d : SysCall) :
    decode_matches_feedback cid (b + dt) (shiftSysCall dt d)
      = decode_matches_feedback cid b d := by
  unfold decode_matches_feedback
  rw [shiftSysCall_kind]
  cases d.kind with
  | DecodeSyndrome _ =>
      simp only [shiftSysCall_end]
      have h : (d.end_us + dt ≤ b + dt) = (d.end_us ≤ b) := by
        apply propext; omega
      simp only [h]
  | _ => rfl

/-! ### §10.c `List.any` preservation under shift -/

/-- The existence of a decoder match under uniform shift is
    preserved. -/
theorem any_decode_matches_feedback_shift_same
    (cid b dt : Nat) (xs : List SysCall) :
    (shiftSchedule dt xs).any (decode_matches_feedback cid (b + dt))
      = xs.any (decode_matches_feedback cid b) := by
  induction xs with
  | nil => rfl
  | cons d rest ih =>
    simp only [shiftSchedule_cons, List.any_cons]
    rw [decode_matches_feedback_shift_same]
    rw [ih]

/-! ### §10.d `feedback_after_decode_ok` shift invariance

    Reformulate `feedback_after_decode_ok` using the helper
    `decode_matches_feedback`, then conclude by shift
    invariance of the helper. -/

theorem feedback_after_decode_ok_via_helper (sched : List SysCall) :
    feedback_after_decode_ok sched
      = sched.all fun sc => match sc.kind with
          | .PauliFrameUpdate cid =>
              sched.any (decode_matches_feedback cid sc.begin_us)
          | _ => true := rfl

theorem feedback_after_decode_ok_shiftSchedule
    (dt : Nat) (xs : List SysCall) :
    feedback_after_decode_ok (shiftSchedule dt xs)
      = feedback_after_decode_ok xs := by
  unfold feedback_after_decode_ok shiftSchedule
  rw [List.all_map]
  congr 1
  funext sc
  show (match (shiftSysCall dt sc).kind with
        | .PauliFrameUpdate cid =>
            (xs.map (shiftSysCall dt)).any
              (decode_matches_feedback cid (shiftSysCall dt sc).begin_us)
        | _ => true)
     = (match sc.kind with
        | .PauliFrameUpdate cid =>
            xs.any (decode_matches_feedback cid sc.begin_us)
        | _ => true)
  rw [shiftSysCall_kind]
  cases sc.kind with
  | PauliFrameUpdate cid =>
      simp only [shiftSysCall_begin]
      have key : (xs.map (shiftSysCall dt)).any
                    (decode_matches_feedback cid (sc.begin_us + dt))
               = xs.any (decode_matches_feedback cid sc.begin_us) := by
        show (shiftSchedule dt xs).any _ = _
        exact any_decode_matches_feedback_shift_same cid sc.begin_us dt xs
      rw [key]
  | _ => rfl

theorem feedback_after_decode_ok_shiftSchedule_of_ok
    (dt : Nat) (xs : List SysCall)
    (h : feedback_after_decode_ok xs = true) :
    feedback_after_decode_ok (shiftSchedule dt xs) = true := by
  rw [feedback_after_decode_ok_shiftSchedule]; exact h

/-! ### §10.e Append monotonicity

    A feedback in `xs` whose witness lives in `xs` still has
    that witness in `xs ++ ys`; same for `ys`.  Because the
    inner `.any` searches the WHOLE schedule, prepending or
    appending extra SysCalls cannot destroy existential
    witnesses. -/

/-- A `.any` is monotone under `++`: if the original list
    contains a witness, the appended list also contains
    one. -/
theorem List_any_append_left
    {α : Type _} (xs ys : List α) (p : α → Bool)
    (h : xs.any p = true) :
    (xs ++ ys).any p = true := by
  rw [List.any_append]
  simp [h]

theorem List_any_append_right
    {α : Type _} (xs ys : List α) (p : α → Bool)
    (h : ys.any p = true) :
    (xs ++ ys).any p = true := by
  rw [List.any_append]
  simp [h]

/-- The main append theorem for feedback-after-decode. -/
theorem feedback_after_decode_ok_append
    (xs ys : List SysCall)
    (hxs : feedback_after_decode_ok xs = true)
    (hys : feedback_after_decode_ok ys = true) :
    feedback_after_decode_ok (xs ++ ys) = true := by
  unfold feedback_after_decode_ok at *
  rw [List.all_eq_true]
  intro sc hmem
  -- Only `PauliFrameUpdate cid` requires a witness; all other
  -- kinds reduce the outer match to `true`.
  cases hk : sc.kind with
  | PauliFrameUpdate cid =>
      rw [List.mem_append] at hmem
      -- After `cases`, the outer match reduces to its
      -- `PauliFrameUpdate cid` branch.  Use `show` to force
      -- the reduction.
      show (xs ++ ys).any (fun sc' =>
              match sc'.kind with
              | .DecodeSyndrome rid =>
                  decide (rid = cid) && decide (sc'.end_us ≤ sc.begin_us)
              | _ => false) = true
      cases hmem with
      | inl h_xs =>
          rw [List.all_eq_true] at hxs
          have hsc := hxs sc h_xs
          rw [hk] at hsc
          have hsc' : xs.any (fun sc' =>
                          match sc'.kind with
                          | .DecodeSyndrome rid =>
                              decide (rid = cid) && decide (sc'.end_us ≤ sc.begin_us)
                          | _ => false) = true := hsc
          exact List_any_append_left xs ys _ hsc'
      | inr h_ys =>
          rw [List.all_eq_true] at hys
          have hsc := hys sc h_ys
          rw [hk] at hsc
          have hsc' : ys.any (fun sc' =>
                          match sc'.kind with
                          | .DecodeSyndrome rid =>
                              decide (rid = cid) && decide (sc'.end_us ≤ sc.begin_us)
                          | _ => false) = true := hsc
          exact List_any_append_right xs ys _ hsc'
  | _ => rfl

/-! ### §10.f `feedback_after_decode_ok` over `seqSchedules` -/

theorem feedback_after_decode_ok_seqSchedules
    (xs ys : List SysCall)
    (hxs : feedback_after_decode_ok xs = true)
    (hys : feedback_after_decode_ok ys = true) :
    feedback_after_decode_ok (seqSchedules xs ys) = true := by
  unfold seqSchedules
  exact feedback_after_decode_ok_append xs (shiftSchedule (scheduleWallclockUs xs) ys)
    hxs
    (feedback_after_decode_ok_shiftSchedule_of_ok _ ys hys)

/-! ### §10.g Repeated atom expansion -/

/-- `feedback_after_decode_ok` survives sequential
    composition of `n` identical bodies via
    `seqManySchedules (List.replicate n body)`.  By induction
    on `n`. -/
theorem feedback_after_decode_ok_seqMany_replicate
    (body : List SysCall) (n : Nat)
    (hbody : feedback_after_decode_ok body = true) :
    feedback_after_decode_ok
        (seqManySchedules (List.replicate n body)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show feedback_after_decode_ok
            (seqSchedules body (seqManySchedules (List.replicate k body))) = true
      exact feedback_after_decode_ok_seqSchedules body _ hbody ih

/-- Reduction lemma: `(rep n (atom body)).expand` equals
    `seqManySchedules (List.replicate n body)`.  The
    `CompressedSchedule.expand` recursor uses well-founded
    recursion, so we go via `simp` rather than `rfl`. -/
theorem rep_atom_expand_eq (body : List SysCall) (n : Nat) :
    (CompressedSchedule.rep n (CompressedSchedule.atom body)).expand
      = seqManySchedules (List.replicate n body) := by
  simp [CompressedSchedule.expand]

/-- Headline: `feedback_after_decode_ok` on the EXPANDED form
    of `rep n (atom body)`. -/
theorem feedback_after_decode_ok_repeated_atom_expand
    (body : List SysCall) (n : Nat)
    (hbody : feedback_after_decode_ok body = true) :
    feedback_after_decode_ok
        (CompressedSchedule.rep n (CompressedSchedule.atom body)).expand = true := by
  rw [rep_atom_expand_eq]
  exact feedback_after_decode_ok_seqMany_replicate body n hbody

/-! ### §10.h Symbolic-repeat extraction theorems -/

/-- Symbolic-repeat acceptance implies the body passes
    `feedback_after_decode_ok` (extracted from the strict
    bundle inside `symbolic_rep_strict_ok`). -/
theorem symbolic_rep_ok_implies_body_feedback_after_decode_ok
    (models : SystemModels) (body : List SysCall) (n : Nat)
    (h : symbolic_rep_strict_ok models body n = true) :
    feedback_after_decode_ok body = true := by
  have hbody : all_invariants_strict_with_slot_capacity_and_freshness_ok
      models.arch models.opCap models.slotCap models.ancillaModel
      body
      models.t_react_us models.window_us models.max_per_window = true :=
    symbolic_rep_ok_implies_body_ok models body n h
  unfold all_invariants_strict_with_slot_capacity_and_freshness_ok
         all_invariants_strict_with_slot_capacity_ok
         all_invariants_strict_ok at hbody
  -- Extract the feedback_after_decode_ok conjunct from the 5-way conjunction
  simp only [Bool.and_eq_true] at hbody
  exact hbody.1.1.2

/-- **Headline Obligation-B theorem.** -/
theorem symbolic_rep_implies_expanded_feedback_after_decode_ok
    (models : SystemModels) (body : List SysCall) (n : Nat)
    (h : symbolic_rep_strict_ok models body n = true) :
    feedback_after_decode_ok
        (CompressedSchedule.rep n (CompressedSchedule.atom body)).expand = true :=
  feedback_after_decode_ok_repeated_atom_expand body n
    (symbolic_rep_ok_implies_body_feedback_after_decode_ok models body n h)

/-! ### §10.i Concrete regression examples -/

/-- Direct check: `rep 100 adder` expanded passes the
    feedback-after-decode invariant. -/
theorem adder_repeated_100_feedback_after_decode_ok :
    feedback_after_decode_ok
        (CompressedSchedule.rep 100 (CompressedSchedule.atom adder_n1_syscalls)).expand
      = true :=
  feedback_after_decode_ok_repeated_atom_expand adder_n1_syscalls 100
    (by native_decide)

/-- A bad body: `PauliFrameUpdate 0` at `[0, 1)` BEFORE the
    matching `DecodeSyndrome 0` at `[10, 11)` (the review's
    counterexample, restated locally to avoid namespace
    cycles). -/
def feedback_bad_body_for_repeat : List SysCall :=
  [ { kind := SysCallKind.PauliFrameUpdate 0
      begin_us := 0, end_us := 1 }
  , { kind := SysCallKind.DecodeSyndrome 0
      begin_us := 10, end_us := 11 } ]

theorem feedback_bad_body_fails_feedback_check :
    feedback_after_decode_ok feedback_bad_body_for_repeat = false := by
  native_decide

theorem feedback_bad_body_repeat_symbolic_rejected :
    symbolic_rep_strict_ok
        adder_n1_system_models feedback_bad_body_for_repeat 10 = false := by
  native_decide

/-! ## §11. Obligation (C) — ancilla-freshness across
       repeated blocks via state-equivalence

    The body passes `ancilla_freshness_ok` when started from
    the empty state (= all Free).  After one body finishes,
    measured sites are `Dirty`, not `Free`.  For the next
    copy, `Free` and `Dirty` should be interchangeable
    because `findFreeOrDirtyInZone` only excludes `Live`
    sites.  We make this rigorous via a state-equivalence
    relation:

      `state_equivalent s1 s2 := ∀ site,
         lifecycleEquivalent (lifecycleOf s1 site)
                             (lifecycleOf s2 site) = true`

    `lifecycleEquivalent` collapses {Free, Dirty} into one
    class while keeping Live distinct.

    Key compatibility lemmas:
      * `findFreeOrDirtyInZone` is constant under
        state-equivalence (only the Live-mask matters).
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

/-! ### §11.b `setLifecycle` lifecycle lookup lemmas -/

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
  | RequestFreshAncilla z =>
      have hf : freshnessStep model state sc
              = (match findAncillaZone model z with
                  | none => some state
                  | some zoneSpec =>
                      match findFreeOrDirtyInZone state zoneSpec with
                      | some site => some (setLifecycle state site SiteLifecycle.Live)
                      | none      => none) := by
        unfold freshnessStep; rw [hk]; rfl
      rw [hf] at hStep
      cases hZ : findAncillaZone model z with
      | none =>
          rw [hZ] at hStep
          dsimp only at hStep
          injection hStep with he
          left; exact he.symm
      | some zoneSpec =>
          rw [hZ] at hStep
          dsimp only at hStep
          cases hF : findFreeOrDirtyInZone state zoneSpec with
          | none =>
              rw [hF] at hStep
              dsimp only at hStep
              exact absurd hStep (by simp)
          | some site =>
              rw [hF] at hStep
              dsimp only at hStep
              injection hStep with he
              right; refine ⟨site, SiteLifecycle.Live, ?_⟩; exact he.symm

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

/-! ### §11.f.helpers — `state_equivalent_set_same` and
       `findFreeOrDirtyInZone_state_equivalent`

    Pulled up from §11.h / §11.d so they're in scope for the
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

theorem findFreeOrDirtyInZone_state_equivalent
    {s1 s2 : List (Nat × SiteLifecycle)}
    (h : state_equivalent s1 s2) (z : AncillaZoneSpec) :
    findFreeOrDirtyInZone s1 z = findFreeOrDirtyInZone s2 z := by
  unfold findFreeOrDirtyInZone
  congr 1
  funext site
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

/-! ### §11.f.eq `freshnessStep` and `runFreshness` state-equivalence

    For each SysCall kind, freshnessStep takes the same path
    under state-equivalent inputs (because the conditions
    depend on Live-status / findFreeOrDirtyInZone, both
    preserved under state_equivalent).  When both calls
    succeed, the resulting states are again state-equivalent.

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
  | RequestFreshAncilla z =>
      have hf1 : freshnessStep model s1 sc
              = (match findAncillaZone model z with
                  | none => some s1
                  | some zoneSpec =>
                      match findFreeOrDirtyInZone s1 zoneSpec with
                      | some site => some (setLifecycle s1 site SiteLifecycle.Live)
                      | none      => none) := by
        unfold freshnessStep; rw [hk]; rfl
      have hf2 : freshnessStep model s2 sc
              = (match findAncillaZone model z with
                  | none => some s2
                  | some zoneSpec =>
                      match findFreeOrDirtyInZone s2 zoneSpec with
                      | some site => some (setLifecycle s2 site SiteLifecycle.Live)
                      | none      => none) := by
        unfold freshnessStep; rw [hk]; rfl
      rw [hf1] at h1; rw [hf2] at h2
      cases hZ : findAncillaZone model z with
      | none =>
          rw [hZ] at h1 h2
          dsimp only at h1 h2
          injection h1 with he1; injection h2 with he2
          subst he1; subst he2; exact hEq
      | some zoneSpec =>
          rw [hZ] at h1 h2
          dsimp only at h1 h2
          have hFsame := findFreeOrDirtyInZone_state_equivalent hEq zoneSpec
          cases hF1 : findFreeOrDirtyInZone s1 zoneSpec with
          | none =>
              rw [hF1] at h1
              dsimp only at h1
              exact absurd h1 (by simp)
          | some site =>
              have hF2 : findFreeOrDirtyInZone s2 zoneSpec = some site := by
                rw [← hFsame]; exact hF1
              rw [hF1] at h1; rw [hF2] at h2
              dsimp only at h1 h2
              injection h1 with he1; injection h2 with he2
              subst he1; subst he2
              exact state_equivalent_set_same hEq site SiteLifecycle.Live

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

/-! ### §11.h-d (moved up) — `state_equivalent_set_same` and
       `findFreeOrDirtyInZone_state_equivalent` are now
       declared before `freshnessStep_state_equivalent` so
       they're in scope. -/

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
  | RequestFreshAncilla z =>
      have hf1 : freshnessStep model s1 sc
              = (match findAncillaZone model z with
                  | none => some s1
                  | some zoneSpec =>
                      match findFreeOrDirtyInZone s1 zoneSpec with
                      | some site => some (setLifecycle s1 site SiteLifecycle.Live)
                      | none      => none) := by
        unfold freshnessStep; rw [hk]; rfl
      have hf2 : freshnessStep model s2 sc
              = (match findAncillaZone model z with
                  | none => some s2
                  | some zoneSpec =>
                      match findFreeOrDirtyInZone s2 zoneSpec with
                      | some site => some (setLifecycle s2 site SiteLifecycle.Live)
                      | none      => none) := by
        unfold freshnessStep; rw [hk]; rfl
      rw [hf2] at h2
      cases hZ : findAncillaZone model z with
      | none =>
          rw [hZ] at h2
          dsimp only at h2
          injection h2 with he2; subst he2
          rw [hf1, hZ]
          exact ⟨s1, rfl, hEq⟩
      | some zoneSpec =>
          rw [hZ] at h2
          dsimp only at h2
          have hFsame := findFreeOrDirtyInZone_state_equivalent hEq zoneSpec
          cases hF2 : findFreeOrDirtyInZone s2 zoneSpec with
          | none =>
              rw [hF2] at h2; dsimp only at h2; exact absurd h2 (by simp)
          | some site =>
              rw [hF2] at h2; dsimp only at h2
              injection h2 with he2; subst he2
              have hF1 : findFreeOrDirtyInZone s1 zoneSpec = some site := by
                rw [hFsame]; exact hF2
              rw [hf1, hZ]
              dsimp only
              rw [hF1]
              exact ⟨setLifecycle s1 site SiteLifecycle.Live, rfl,
                     state_equivalent_set_same hEq site SiteLifecycle.Live⟩

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

/-! ### §11.e Blockers for the full state-equivalence chain

    The remaining lemmas needed to close Obligation (C)
    parametrically are:

      `freshnessStep_state_equivalent`:
        ∀ model sc s1 s2, state_equivalent s1 s2 →
          both runs of freshnessStep agree (both fail OR
          both succeed with equivalent results).
        Blocker: `cases` requires enumerating all 8
        `SysCallKind` constructors; the proof is bounded but
        long, especially for Gate2q (cross-product of
        `siteInAncillaModel` × `Live`-status on both q1, q2).

      `runFreshness_state_equivalent`:
        Lifts the per-step preservation by induction on the
        schedule.

      `noDanglingLive_implies_state_equivalent_empty`:
        Requires showing that if no entry has `Live`, then
        `lifecycleOf s site ≠ Live` for all `site`.  This
        requires `List.find?_mem` (or
        `List.mem_of_find?_eq_some`) which is in Lean 4 core
        / mathlib but the precise name varies.

      Final reverse direction:
        `state_equivalent s [] ∧ stateNormalized s →
          noDanglingLive s`
        — requires the **state-normalization invariant** for
        `runFreshness`'s outputs (no duplicate first-coords),
        a List.Nodup-style chain.

    Each lemma is bounded but combined they form a sizeable
    proof obligation.  We isolate them here, keep the
    composable framework lemmas above (`refl`, `symm`,
    `live_iff`, `set_same`, `findFreeOrDirtyInZone_*`), and
    rely on `native_decide` for the concrete adder
    regressions in §11.f. -/

/-! ### §11.f Concrete adder regressions for Obligation C -/

/-! ### §11.g Bonus: concrete additional regressions -/

/-- Direct check: the EXPANDED `rep 3 adder` schedule (144
    SysCalls) still passes the ancilla-freshness check.
    Closed by `native_decide` on the expansion (the
    parametric chain would close this for arbitrary `n`
    once the normalization invariants are added). -/
theorem adder_repeated_3_ancilla_freshness_ok :
    ancilla_freshness_ok
        adder_n1_system_models.ancillaModel
        (CompressedSchedule.rep 3 (CompressedSchedule.atom adder_n1_syscalls)).expand
      = true := by
  native_decide

/-- Direct check at `n = 10` (480 SysCalls). -/
theorem adder_repeated_10_ancilla_freshness_ok :
    ancilla_freshness_ok
        adder_n1_system_models.ancillaModel
        (CompressedSchedule.rep 10 (CompressedSchedule.atom adder_n1_syscalls)).expand
      = true := by
  native_decide

/-- A bad body: Gate2q on ancilla site 100 before any
    `RequestFreshAncilla` (the review's freshness violator
    shape).  Body fails ancilla-freshness ⇒ strict bundle
    fails ⇒ symbolic_rep_strict_ok rejects. -/
def freshness_bad_body_for_repeat : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 100 0, begin_us := 0, end_us := 1 } ]

theorem freshness_bad_body_fails_freshness_check :
    ancilla_freshness_ok
        adder_n1_system_models.ancillaModel freshness_bad_body_for_repeat = false := by
  native_decide

theorem freshness_bad_body_repeat_symbolic_rejected :
    symbolic_rep_strict_ok
        adder_n1_system_models freshness_bad_body_for_repeat 10 = false := by
  native_decide

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

/-! ## §13. Obligation (A) — pairwise / resource-capacity
       invariants under sequential composition and repeated
       hardware-generic schedule blocks

    Hardware-generic terminology: `block` / `leaf schedule
    block` / `repeated block`.  `CompressedSchedule.atom` is
    only the implementation-level constructor name for a
    compressed leaf schedule block; it does NOT denote a
    hardware-atomic operation. -/

/-! ### §13.a `shiftSchedule_length` helper -/

theorem shiftSchedule_length (dt : Nat) (xs : List SysCall) :
    (shiftSchedule dt xs).length = xs.length := by
  unfold shiftSchedule
  exact List.length_map _

/-! ### §13.a.2 `shiftSchedule_getElem?` -/

theorem shiftSchedule_getElem? (dt : Nat) (xs : List SysCall) (i : Nat) :
    (shiftSchedule dt xs)[i]? = Option.map (shiftSysCall dt) (xs[i]?) := by
  unfold shiftSchedule
  exact List.getElem?_map

/-! ### §13.a.3 Shift invariance of the exclusivity pair check.

    For each `(i, j)`, the pair check on `shiftSchedule dt xs`
    yields the same Bool as the pair check on `xs`.  The
    `intervals_overlap` invariance under uniform shift and
    `syscall_acts_on (shiftSysCall ...)` = `syscall_acts_on
    ...` make this a pointwise rewrite. -/

private theorem exclusivity_pair_eq_shift
    (dt : Nat) (xs : List SysCall) (i j : Nat) :
    (match (shiftSchedule dt xs)[i]?, (shiftSchedule dt xs)[j]? with
     | some s_i, some s_j =>
         if intervals_overlap s_i.begin_us s_i.end_us
                              s_j.begin_us s_j.end_us = true then
           atoms_disjoint (syscall_acts_on s_i) (syscall_acts_on s_j)
         else true
     | _, _ => true)
      = (match xs[i]?, xs[j]? with
         | some s_i, some s_j =>
             if intervals_overlap s_i.begin_us s_i.end_us
                                  s_j.begin_us s_j.end_us = true then
               atoms_disjoint (syscall_acts_on s_i) (syscall_acts_on s_j)
             else true
         | _, _ => true) := by
  rw [shiftSchedule_getElem?, shiftSchedule_getElem?]
  cases hxi : xs[i]? with
  | none => rfl
  | some s_i =>
    cases hxj : xs[j]? with
    | none => rfl
    | some s_j =>
      simp only [Option.map_some]
      have hb_i : (shiftSysCall dt s_i).begin_us = s_i.begin_us + dt := rfl
      have he_i : (shiftSysCall dt s_i).end_us   = s_i.end_us   + dt := rfl
      have hb_j : (shiftSysCall dt s_j).begin_us = s_j.begin_us + dt := rfl
      have he_j : (shiftSysCall dt s_j).end_us   = s_j.end_us   + dt := rfl
      rw [hb_i, he_i, hb_j, he_j]
      rw [intervals_overlap_shift_same]
      rw [syscall_acts_on_shiftSysCall, syscall_acts_on_shiftSysCall]

/-! ### §13.a.4 `exclusivity_ok` is shift-invariant. -/

theorem exclusivity_ok_shiftSchedule_eq (dt : Nat) (xs : List SysCall) :
    exclusivity_ok (shiftSchedule dt xs) = exclusivity_ok xs := by
  unfold exclusivity_ok
  rw [shiftSchedule_length]
  refine congrArg (List.range xs.length).all ?_
  funext i
  refine congrArg (List.range xs.length).all ?_
  funext j
  by_cases hij : i < j
  · have h_ij : decide (i < j) = true := decide_eq_true hij
    simp only [h_ij, if_true]
    exact exclusivity_pair_eq_shift dt xs i j
  · have h_ij : decide (i < j) = false := decide_eq_false hij
    simp only [h_ij]
    rfl

/-! ### §13.a.5 Pair-check abstraction.

    To prove `exclusivity_ok_seqSchedules`, we factor the inner
    `match L[i]?, L[j]?` block out as `excl_pair_check L i j`
    and bridge it both ways to the `(List.range
    L.length).all` style of `exclusivity_ok`. -/

private def excl_pair_check (L : List SysCall) (i j : Nat) : Bool :=
  match L[i]?, L[j]? with
  | some s_i, some s_j =>
      if intervals_overlap s_i.begin_us s_i.end_us
                           s_j.begin_us s_j.end_us = true then
        atoms_disjoint (syscall_acts_on s_i) (syscall_acts_on s_j)
      else true
  | _, _ => true

private theorem exclusivity_ok_of_pair_check (L : List SysCall)
    (h : ∀ i j, i < j → j < L.length → excl_pair_check L i j = true) :
    exclusivity_ok L = true := by
  unfold exclusivity_ok
  rw [List.all_eq_true]
  intro i hi_mem
  rw [List.mem_range] at hi_mem
  rw [List.all_eq_true]
  intro j hj_mem
  rw [List.mem_range] at hj_mem
  by_cases hij : i < j
  · simp only [decide_eq_true hij, ite_true]
    exact h i j hij hj_mem
  · simp only [decide_eq_false hij]
    rfl

private theorem excl_pair_check_of_exclusivity_ok (L : List SysCall)
    (hL : exclusivity_ok L = true) (i j : Nat) (hij : i < j) (hj : j < L.length) :
    excl_pair_check L i j = true := by
  unfold exclusivity_ok at hL
  rw [List.all_eq_true] at hL
  have hi_lt : i < L.length := Nat.lt_trans hij hj
  have hi_mem : i ∈ List.range L.length := List.mem_range.mpr hi_lt
  have hj_mem : j ∈ List.range L.length := List.mem_range.mpr hj
  have h1 := hL i hi_mem
  rw [List.all_eq_true] at h1
  have h2 := h1 j hj_mem
  simp only [decide_eq_true hij, ite_true] at h2
  exact h2

private theorem excl_pair_check_shiftSchedule
    (dt : Nat) (L : List SysCall) (i j : Nat) :
    excl_pair_check (shiftSchedule dt L) i j = excl_pair_check L i j := by
  unfold excl_pair_check
  exact exclusivity_pair_eq_shift dt L i j

/-! ### §13.a.6 `exclusivity_ok_seqSchedules`.

    Sequential composition preserves exclusivity, provided
    each piece is exclusive AND the first piece is
    within-wallclock (so the cross-block half-open intervals
    are disjoint). -/

theorem exclusivity_ok_seqSchedules
    (xs ys : List SysCall)
    (hxs : exclusivity_ok xs = true)
    (hys : exclusivity_ok ys = true)
    (hwithin : scheduleWithinWallclock xs = true) :
    exclusivity_ok (seqSchedules xs ys) = true := by
  show exclusivity_ok (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  apply exclusivity_ok_of_pair_check
  intro i j hij hj_lt
  have hLen :
      (xs ++ shiftSchedule (scheduleWallclockUs xs) ys).length
        = xs.length + ys.length := by
    rw [List.length_append, shiftSchedule_length]
  rw [hLen] at hj_lt
  by_cases hj_xs : j < xs.length
  · -- Same block (xs)
    have hi_xs : i < xs.length := Nat.lt_trans hij hj_xs
    have hL_i :
        (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)[i]? = xs[i]? :=
      List.getElem?_append_left hi_xs
    have hL_j :
        (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)[j]? = xs[j]? :=
      List.getElem?_append_left hj_xs
    have hxs_pair := excl_pair_check_of_exclusivity_ok xs hxs i j hij hj_xs
    unfold excl_pair_check
    rw [hL_i, hL_j]
    unfold excl_pair_check at hxs_pair
    exact hxs_pair
  · have hj_xs : xs.length ≤ j := Nat.le_of_not_lt hj_xs
    by_cases hi_xs : i < xs.length
    · -- Cross block: i < xs.length ≤ j
      have hL_i :
          (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)[i]? = xs[i]? :=
        List.getElem?_append_left hi_xs
      have hL_j :
          (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)[j]?
            = (shiftSchedule (scheduleWallclockUs xs) ys)[j - xs.length]? :=
        List.getElem?_append_right hj_xs
      unfold excl_pair_check
      rw [hL_i, hL_j]
      cases hxi : xs[i]? with
      | none => rfl
      | some s_i =>
        cases hsy : (shiftSchedule (scheduleWallclockUs xs) ys)[j - xs.length]? with
        | none => rfl
        | some s_j =>
          have h_mem_i : s_i ∈ xs := List.mem_of_getElem? hxi
          have h_mem_j : s_j ∈ shiftSchedule (scheduleWallclockUs xs) ys :=
            List.mem_of_getElem? hsy
          have h_no_ov :
              intervals_overlap s_i.begin_us s_i.end_us
                                  s_j.begin_us s_j.end_us = false :=
            cross_pair_no_overlap xs ys s_i s_j h_mem_i h_mem_j hwithin
          simp [h_no_ov]
    · -- Same block (shifted ys): xs.length ≤ i ≤ j
      have hi_xs : xs.length ≤ i := Nat.le_of_not_lt hi_xs
      have hL_i :
          (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)[i]?
            = (shiftSchedule (scheduleWallclockUs xs) ys)[i - xs.length]? :=
        List.getElem?_append_right hi_xs
      have hL_j :
          (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)[j]?
            = (shiftSchedule (scheduleWallclockUs xs) ys)[j - xs.length]? :=
        List.getElem?_append_right hj_xs
      have hij' : i - xs.length < j - xs.length := by omega
      have hj' : j - xs.length < ys.length := by omega
      have hys_pair :
          excl_pair_check (shiftSchedule (scheduleWallclockUs xs) ys)
              (i - xs.length) (j - xs.length) = true := by
        rw [excl_pair_check_shiftSchedule]
        exact excl_pair_check_of_exclusivity_ok ys hys (i - xs.length) (j - xs.length)
          hij' hj'
      unfold excl_pair_check
      rw [hL_i, hL_j]
      unfold excl_pair_check at hys_pair
      exact hys_pair

/-! ### §13.a.7 Repeated-block exclusivity. -/

/-- `exclusivity_ok` survives sequential composition of `n`
    identical blocks via `seqManySchedules (List.replicate n
    block)`, provided the block is within-wallclock and
    exclusive on its own.  By induction on `n`. -/
theorem exclusivity_ok_seqMany_replicate_block
    (block : List SysCall) (n : Nat)
    (hblock : exclusivity_ok block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    exclusivity_ok (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show exclusivity_ok
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact exclusivity_ok_seqSchedules block _ hblock ih hwithin

/-! ### §13.a.8 Expanded-form headline for `exclusivity_ok`.

    `CompressedSchedule.rep n (atom block) .expand` reduces to
    `seqManySchedules (List.replicate n block)`, so the
    above lemma applies directly. -/

theorem exclusivity_ok_repeated_block_expand
    (block : List SysCall) (n : Nat)
    (hblock : exclusivity_ok block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    exclusivity_ok
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact exclusivity_ok_seqMany_replicate_block block n hblock hwithin

/-! ### §13.a.9 Pair-check shift invariance for factory exclusivity.

    Mirrors §13.a.3 but on `syscall_factory_claims` instead of
    `syscall_acts_on`.  The same `intervals_overlap_shift_same`
    + index-access rewrite applies; the factory-claims component
    is `rfl`-preserved by `shiftSysCall`. -/

private theorem factory_exclusivity_pair_eq_shift
    (dt : Nat) (xs : List SysCall) (i j : Nat) :
    (match (shiftSchedule dt xs)[i]?, (shiftSchedule dt xs)[j]? with
     | some s_i, some s_j =>
         if intervals_overlap s_i.begin_us s_i.end_us
                              s_j.begin_us s_j.end_us = true then
           atoms_disjoint (syscall_factory_claims s_i)
                          (syscall_factory_claims s_j)
         else true
     | _, _ => true)
      = (match xs[i]?, xs[j]? with
         | some s_i, some s_j =>
             if intervals_overlap s_i.begin_us s_i.end_us
                                  s_j.begin_us s_j.end_us = true then
               atoms_disjoint (syscall_factory_claims s_i)
                              (syscall_factory_claims s_j)
             else true
         | _, _ => true) := by
  rw [shiftSchedule_getElem?, shiftSchedule_getElem?]
  cases hxi : xs[i]? with
  | none => rfl
  | some s_i =>
    cases hxj : xs[j]? with
    | none => rfl
    | some s_j =>
      simp only [Option.map_some]
      have hb_i : (shiftSysCall dt s_i).begin_us = s_i.begin_us + dt := rfl
      have he_i : (shiftSysCall dt s_i).end_us   = s_i.end_us   + dt := rfl
      have hb_j : (shiftSysCall dt s_j).begin_us = s_j.begin_us + dt := rfl
      have he_j : (shiftSysCall dt s_j).end_us   = s_j.end_us   + dt := rfl
      rw [hb_i, he_i, hb_j, he_j]
      rw [intervals_overlap_shift_same]
      rw [syscall_factory_claims_shiftSysCall, syscall_factory_claims_shiftSysCall]

/-! ### §13.a.10 `factory_exclusivity_ok` is shift-invariant. -/

theorem factory_exclusivity_ok_shiftSchedule_eq (dt : Nat) (xs : List SysCall) :
    factory_exclusivity_ok (shiftSchedule dt xs) = factory_exclusivity_ok xs := by
  unfold factory_exclusivity_ok
  rw [shiftSchedule_length]
  refine congrArg (List.range xs.length).all ?_
  funext i
  refine congrArg (List.range xs.length).all ?_
  funext j
  by_cases hij : i < j
  · have h_ij : decide (i < j) = true := decide_eq_true hij
    simp only [h_ij, if_true]
    exact factory_exclusivity_pair_eq_shift dt xs i j
  · have h_ij : decide (i < j) = false := decide_eq_false hij
    simp only [h_ij]
    rfl

/-! ### §13.a.11 Pair-check abstraction for factory exclusivity.

    Mirrors §13.a.5 — factor the inner `match` block out as a
    `factory_excl_pair_check` Bool and bridge both ways to
    `factory_exclusivity_ok`. -/

private def factory_excl_pair_check (L : List SysCall) (i j : Nat) : Bool :=
  match L[i]?, L[j]? with
  | some s_i, some s_j =>
      if intervals_overlap s_i.begin_us s_i.end_us
                           s_j.begin_us s_j.end_us = true then
        atoms_disjoint (syscall_factory_claims s_i)
                       (syscall_factory_claims s_j)
      else true
  | _, _ => true

private theorem factory_exclusivity_ok_of_pair_check (L : List SysCall)
    (h : ∀ i j, i < j → j < L.length → factory_excl_pair_check L i j = true) :
    factory_exclusivity_ok L = true := by
  unfold factory_exclusivity_ok
  rw [List.all_eq_true]
  intro i hi_mem
  rw [List.mem_range] at hi_mem
  rw [List.all_eq_true]
  intro j hj_mem
  rw [List.mem_range] at hj_mem
  by_cases hij : i < j
  · simp only [decide_eq_true hij, ite_true]
    exact h i j hij hj_mem
  · simp only [decide_eq_false hij]
    rfl

private theorem factory_excl_pair_check_of_factory_exclusivity_ok
    (L : List SysCall) (hL : factory_exclusivity_ok L = true)
    (i j : Nat) (hij : i < j) (hj : j < L.length) :
    factory_excl_pair_check L i j = true := by
  unfold factory_exclusivity_ok at hL
  rw [List.all_eq_true] at hL
  have hi_lt : i < L.length := Nat.lt_trans hij hj
  have hi_mem : i ∈ List.range L.length := List.mem_range.mpr hi_lt
  have hj_mem : j ∈ List.range L.length := List.mem_range.mpr hj
  have h1 := hL i hi_mem
  rw [List.all_eq_true] at h1
  have h2 := h1 j hj_mem
  simp only [decide_eq_true hij, ite_true] at h2
  exact h2

private theorem factory_excl_pair_check_shiftSchedule
    (dt : Nat) (L : List SysCall) (i j : Nat) :
    factory_excl_pair_check (shiftSchedule dt L) i j
      = factory_excl_pair_check L i j := by
  unfold factory_excl_pair_check
  exact factory_exclusivity_pair_eq_shift dt L i j

/-! ### §13.a.12 `factory_exclusivity_ok_seqSchedules`.

    Sequential composition preserves factory exclusivity,
    provided each piece is factory-exclusive AND the first
    piece is within-wallclock. -/

theorem factory_exclusivity_ok_seqSchedules
    (xs ys : List SysCall)
    (hxs : factory_exclusivity_ok xs = true)
    (hys : factory_exclusivity_ok ys = true)
    (hwithin : scheduleWithinWallclock xs = true) :
    factory_exclusivity_ok (seqSchedules xs ys) = true := by
  show factory_exclusivity_ok (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  apply factory_exclusivity_ok_of_pair_check
  intro i j hij hj_lt
  have hLen :
      (xs ++ shiftSchedule (scheduleWallclockUs xs) ys).length
        = xs.length + ys.length := by
    rw [List.length_append, shiftSchedule_length]
  rw [hLen] at hj_lt
  by_cases hj_xs : j < xs.length
  · -- Same block (xs)
    have hi_xs : i < xs.length := Nat.lt_trans hij hj_xs
    have hL_i :
        (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)[i]? = xs[i]? :=
      List.getElem?_append_left hi_xs
    have hL_j :
        (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)[j]? = xs[j]? :=
      List.getElem?_append_left hj_xs
    have hxs_pair :=
      factory_excl_pair_check_of_factory_exclusivity_ok xs hxs i j hij hj_xs
    unfold factory_excl_pair_check
    rw [hL_i, hL_j]
    unfold factory_excl_pair_check at hxs_pair
    exact hxs_pair
  · have hj_xs : xs.length ≤ j := Nat.le_of_not_lt hj_xs
    by_cases hi_xs : i < xs.length
    · -- Cross block: i < xs.length ≤ j
      have hL_i :
          (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)[i]? = xs[i]? :=
        List.getElem?_append_left hi_xs
      have hL_j :
          (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)[j]?
            = (shiftSchedule (scheduleWallclockUs xs) ys)[j - xs.length]? :=
        List.getElem?_append_right hj_xs
      unfold factory_excl_pair_check
      rw [hL_i, hL_j]
      cases hxi : xs[i]? with
      | none => rfl
      | some s_i =>
        cases hsy : (shiftSchedule (scheduleWallclockUs xs) ys)[j - xs.length]? with
        | none => rfl
        | some s_j =>
          have h_mem_i : s_i ∈ xs := List.mem_of_getElem? hxi
          have h_mem_j : s_j ∈ shiftSchedule (scheduleWallclockUs xs) ys :=
            List.mem_of_getElem? hsy
          have h_no_ov :
              intervals_overlap s_i.begin_us s_i.end_us
                                  s_j.begin_us s_j.end_us = false :=
            cross_pair_no_overlap xs ys s_i s_j h_mem_i h_mem_j hwithin
          simp [h_no_ov]
    · -- Same block (shifted ys): xs.length ≤ i ≤ j
      have hi_xs : xs.length ≤ i := Nat.le_of_not_lt hi_xs
      have hL_i :
          (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)[i]?
            = (shiftSchedule (scheduleWallclockUs xs) ys)[i - xs.length]? :=
        List.getElem?_append_right hi_xs
      have hL_j :
          (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)[j]?
            = (shiftSchedule (scheduleWallclockUs xs) ys)[j - xs.length]? :=
        List.getElem?_append_right hj_xs
      have hij' : i - xs.length < j - xs.length := by omega
      have hj' : j - xs.length < ys.length := by omega
      have hys_pair :
          factory_excl_pair_check (shiftSchedule (scheduleWallclockUs xs) ys)
              (i - xs.length) (j - xs.length) = true := by
        rw [factory_excl_pair_check_shiftSchedule]
        exact factory_excl_pair_check_of_factory_exclusivity_ok ys hys
          (i - xs.length) (j - xs.length) hij' hj'
      unfold factory_excl_pair_check
      rw [hL_i, hL_j]
      unfold factory_excl_pair_check at hys_pair
      exact hys_pair

/-! ### §13.a.13 Repeated-block factory exclusivity. -/

theorem factory_exclusivity_ok_seqMany_replicate_block
    (block : List SysCall) (n : Nat)
    (hblock : factory_exclusivity_ok block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    factory_exclusivity_ok (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show factory_exclusivity_ok
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact factory_exclusivity_ok_seqSchedules block _ hblock ih hwithin

/-! ### §13.a.14 Expanded-form headline for `factory_exclusivity_ok`. -/

theorem factory_exclusivity_ok_repeated_block_expand
    (block : List SysCall) (n : Nat)
    (hblock : factory_exclusivity_ok block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    factory_exclusivity_ok
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact factory_exclusivity_ok_seqMany_replicate_block block n hblock hwithin

/-! ### §13.a.15 `countActiveKindAt` helpers

    The sampled-time A-conjuncts (`operation_capacity_ok`,
    `slot_capacity_ok`) build on `countActiveKindAt`.  Three
    helpers are enough to handle sequential composition:

      * count distributes over `++`;
      * shifting the schedule shifts the active count's argument;
      * at times outside a block's wallclock window the count
        is zero. -/

theorem countActiveKindAt_append
    (pred : SysCallKind → Bool) (t : Nat) (xs ys : List SysCall) :
    countActiveKindAt pred t (xs ++ ys)
      = countActiveKindAt pred t xs + countActiveKindAt pred t ys := by
  unfold countActiveKindAt
  rw [List.filter_append, List.length_append]

theorem countActiveKindAt_shiftSchedule
    (pred : SysCallKind → Bool) (t dt : Nat) (xs : List SysCall) :
    countActiveKindAt pred (t + dt) (shiftSchedule dt xs)
      = countActiveKindAt pred t xs := by
  unfold countActiveKindAt shiftSchedule
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro sc _
  simp only [Function.comp]
  rw [shiftSysCall_kind]
  unfold syscallActiveAt
  rw [shiftSysCall_begin, shiftSysCall_end]
  have h1 : decide (sc.begin_us + dt ≤ t + dt) = decide (sc.begin_us ≤ t) := by
    have : (sc.begin_us + dt ≤ t + dt) ↔ (sc.begin_us ≤ t) := by omega
    simp [this]
  have h2 : decide (t + dt < sc.end_us + dt) = decide (t < sc.end_us) := by
    have : (t + dt < sc.end_us + dt) ↔ (t < sc.end_us) := by omega
    simp [this]
  rw [h1, h2]

theorem countActiveKindAt_eq_zero_of_within_wallclock_at_or_after
    (pred : SysCallKind → Bool) (t : Nat) (xs : List SysCall)
    (hwithin : scheduleWithinWallclock xs = true)
    (h : scheduleWallclockUs xs ≤ t) :
    countActiveKindAt pred t xs = 0 := by
  unfold countActiveKindAt
  rw [List.length_eq_zero_iff]
  rw [List.filter_eq_nil_iff]
  intro sc hsc
  have h_end_le : sc.end_us ≤ scheduleWallclockUs xs :=
    scheduleWithinWallclock_end_le xs sc hsc hwithin
  unfold syscallActiveAt
  have h_not : ¬ (t < sc.end_us) := by omega
  simp [h_not]

theorem countActiveKindAt_shiftSchedule_eq_zero_before_offset
    (pred : SysCallKind → Bool) (t dt : Nat) (ys : List SysCall)
    (h : t < dt) :
    countActiveKindAt pred t (shiftSchedule dt ys) = 0 := by
  unfold countActiveKindAt
  rw [List.length_eq_zero_iff]
  rw [List.filter_eq_nil_iff]
  intro sc hsc
  have h_begin : dt ≤ sc.begin_us := shifted_begin_ge_offset dt ys sc hsc
  unfold syscallActiveAt
  have h_not : ¬ (sc.begin_us ≤ t) := by omega
  simp [h_not]

/-! ### §13.a.16 Per-time operation-capacity check abstraction

    Bool function that runs the conjunction of all eight kind
    capacity checks at a single time `t` against schedule `L`.
    `operation_capacity_ok` is exactly this function `.all`-ed
    over the schedule's sample times. -/

private def op_cap_check_at (opCap : OperationCapacityModel)
    (L : List SysCall) (t : Nat) : Bool :=
  decide (countActiveKindAt kindIsGate1q t L ≤ opCap.max_gate1q_active)
  && decide (countActiveKindAt kindIsGate2q t L ≤ opCap.max_gate2q_active)
  && decide (countActiveKindAt kindIsMeasure t L ≤ opCap.max_measure_active)
  && decide (countActiveKindAt kindIsDecode t L ≤ opCap.max_decode_active)
  && decide (countActiveKindAt kindIsFeedback t L ≤ opCap.max_feedback_active)
  && decide (countActiveKindAt kindIsMagicReq t L ≤ opCap.max_magic_req_active)
  && decide (countActiveKindAt kindIsFreshAnc t L ≤ opCap.max_fresh_ancilla_active)
  && decide (countActiveKindAt kindIsTransit t L ≤ opCap.max_transit_active)

private theorem operation_capacity_ok_eq
    (opCap : OperationCapacityModel) (L : List SysCall) :
    operation_capacity_ok opCap L
      = (scheduleEventTimes L).all (op_cap_check_at opCap L) := rfl

/-- If every count in `L'` is ≤ the corresponding count in `L`,
    then `L'`'s per-time check passes whenever `L`'s does. -/
private theorem op_cap_check_at_mono
    (opCap : OperationCapacityModel) (L L' : List SysCall) (t : Nat)
    (h1 : countActiveKindAt kindIsGate1q t L' ≤ countActiveKindAt kindIsGate1q t L)
    (h2 : countActiveKindAt kindIsGate2q t L' ≤ countActiveKindAt kindIsGate2q t L)
    (h3 : countActiveKindAt kindIsMeasure t L' ≤ countActiveKindAt kindIsMeasure t L)
    (h4 : countActiveKindAt kindIsDecode t L' ≤ countActiveKindAt kindIsDecode t L)
    (h5 : countActiveKindAt kindIsFeedback t L' ≤ countActiveKindAt kindIsFeedback t L)
    (h6 : countActiveKindAt kindIsMagicReq t L' ≤ countActiveKindAt kindIsMagicReq t L)
    (h7 : countActiveKindAt kindIsFreshAnc t L' ≤ countActiveKindAt kindIsFreshAnc t L)
    (h8 : countActiveKindAt kindIsTransit t L' ≤ countActiveKindAt kindIsTransit t L)
    (hL : op_cap_check_at opCap L t = true) :
    op_cap_check_at opCap L' t = true := by
  unfold op_cap_check_at at hL ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hL ⊢
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
    first
      | exact Nat.le_trans h1 hL.1.1.1.1.1.1.1
      | exact Nat.le_trans h2 hL.1.1.1.1.1.1.2
      | exact Nat.le_trans h3 hL.1.1.1.1.1.2
      | exact Nat.le_trans h4 hL.1.1.1.1.2
      | exact Nat.le_trans h5 hL.1.1.1.2
      | exact Nat.le_trans h6 hL.1.1.2
      | exact Nat.le_trans h7 hL.1.2
      | exact Nat.le_trans h8 hL.2

/-! ### §13.a.17 Shift invariance of `op_cap_check_at`. -/

private theorem op_cap_check_at_shiftSchedule
    (opCap : OperationCapacityModel) (xs : List SysCall) (t dt : Nat) :
    op_cap_check_at opCap (shiftSchedule dt xs) (t + dt)
      = op_cap_check_at opCap xs t := by
  unfold op_cap_check_at
  rw [countActiveKindAt_shiftSchedule, countActiveKindAt_shiftSchedule,
      countActiveKindAt_shiftSchedule, countActiveKindAt_shiftSchedule,
      countActiveKindAt_shiftSchedule, countActiveKindAt_shiftSchedule,
      countActiveKindAt_shiftSchedule, countActiveKindAt_shiftSchedule]

/-! ### §13.a.18 `operation_capacity_ok_shiftSchedule_eq`. -/

theorem operation_capacity_ok_shiftSchedule_eq
    (opCap : OperationCapacityModel) (dt : Nat) (xs : List SysCall) :
    operation_capacity_ok opCap (shiftSchedule dt xs)
      = operation_capacity_ok opCap xs := by
  rw [operation_capacity_ok_eq, operation_capacity_ok_eq]
  show ((shiftSchedule dt xs).map (·.begin_us)).all _
      = (xs.map (·.begin_us)).all _
  -- shifted event times = xs.map (·.begin_us + dt)
  have h_evt :
      (shiftSchedule dt xs).map (·.begin_us)
        = xs.map (fun sc => sc.begin_us + dt) := by
    unfold shiftSchedule
    rw [List.map_map]
    rfl
  rw [h_evt]
  rw [List.all_map, List.all_map]
  congr 1
  funext sc
  show op_cap_check_at opCap (shiftSchedule dt xs) (sc.begin_us + dt)
      = op_cap_check_at opCap xs sc.begin_us
  exact op_cap_check_at_shiftSchedule opCap xs sc.begin_us dt

/-! ### §13.a.19 `operation_capacity_ok_seqSchedules`. -/

theorem operation_capacity_ok_seqSchedules
    (opCap : OperationCapacityModel) (xs ys : List SysCall)
    (hxs : operation_capacity_ok opCap xs = true)
    (hys : operation_capacity_ok opCap ys = true)
    (hwithin : scheduleWithinWallclock xs = true) :
    operation_capacity_ok opCap (seqSchedules xs ys) = true := by
  show operation_capacity_ok opCap (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  rw [operation_capacity_ok_eq]
  show (scheduleEventTimes (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)).all _ = true
  have h_evt :
      scheduleEventTimes (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
        = xs.map (·.begin_us)
          ++ ys.map (fun sc => sc.begin_us + scheduleWallclockUs xs) := by
    show ((xs ++ shiftSchedule (scheduleWallclockUs xs) ys).map _) = _
    rw [List.map_append]
    congr 1
    unfold shiftSchedule
    rw [List.map_map]
    rfl
  rw [h_evt, List.all_append, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- Pre-W sample times: each t = sc.begin_us for sc ∈ xs, so t < W.
    rw [List.all_map]
    rw [List.all_eq_true]
    intro sc hsc
    have h_end : sc.end_us ≤ scheduleWallclockUs xs :=
      scheduleWithinWallclock_end_le xs sc hsc hwithin
    have h_begin_lt : sc.begin_us < sc.end_us :=
      scheduleWithinWallclock_begin_lt_end xs sc hsc hwithin
    have h_t_lt_W : sc.begin_us < scheduleWallclockUs xs := by omega
    -- counts in (xs ++ shifted ys) at sc.begin_us = counts in xs (since shifted ys has none here)
    have h_count_zero_each :
        ∀ pred, countActiveKindAt pred sc.begin_us
                  (shiftSchedule (scheduleWallclockUs xs) ys) = 0 :=
      fun pred =>
        countActiveKindAt_shiftSchedule_eq_zero_before_offset pred sc.begin_us
          (scheduleWallclockUs xs) ys h_t_lt_W
    have h_count_eq :
        ∀ pred, countActiveKindAt pred sc.begin_us
                  (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
                = countActiveKindAt pred sc.begin_us xs := by
      intro pred
      rw [countActiveKindAt_append, h_count_zero_each pred, Nat.add_zero]
    -- extract the per-time check at sc.begin_us from hxs
    have hxs_at :
        op_cap_check_at opCap xs sc.begin_us = true := by
      have hmem : sc.begin_us ∈ scheduleEventTimes xs :=
        List.mem_map.mpr ⟨sc, hsc, rfl⟩
      exact (List.all_eq_true.mp hxs) sc.begin_us hmem
    simp only [Function.comp]
    unfold op_cap_check_at
    simp only [h_count_eq]
    unfold op_cap_check_at at hxs_at
    exact hxs_at
  · -- Post-W sample times: each t' = sc.begin_us + W for sc ∈ ys, so t' ≥ W.
    rw [List.all_map]
    rw [List.all_eq_true]
    intro sc hsc
    have h_t_ge_W : scheduleWallclockUs xs ≤ sc.begin_us + scheduleWallclockUs xs := by omega
    -- counts in (xs ++ shifted ys) at sc.begin_us + W = counts in shifted ys (since xs has none here)
    have h_count_zero_each_xs :
        ∀ pred, countActiveKindAt pred (sc.begin_us + scheduleWallclockUs xs) xs = 0 :=
      fun pred =>
        countActiveKindAt_eq_zero_of_within_wallclock_at_or_after pred
          (sc.begin_us + scheduleWallclockUs xs) xs hwithin h_t_ge_W
    have h_count_eq :
        ∀ pred, countActiveKindAt pred (sc.begin_us + scheduleWallclockUs xs)
                  (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
                = countActiveKindAt pred sc.begin_us ys := by
      intro pred
      rw [countActiveKindAt_append, h_count_zero_each_xs pred, Nat.zero_add]
      exact countActiveKindAt_shiftSchedule pred sc.begin_us (scheduleWallclockUs xs) ys
    -- extract the per-time check at sc.begin_us from hys
    have hys_at :
        op_cap_check_at opCap ys sc.begin_us = true := by
      have hmem : sc.begin_us ∈ scheduleEventTimes ys :=
        List.mem_map.mpr ⟨sc, hsc, rfl⟩
      exact (List.all_eq_true.mp hys) sc.begin_us hmem
    simp only [Function.comp]
    unfold op_cap_check_at
    simp only [h_count_eq]
    unfold op_cap_check_at at hys_at
    exact hys_at

/-! ### §13.a.20 Repeated-block operation capacity. -/

theorem operation_capacity_ok_seqMany_replicate_block
    (opCap : OperationCapacityModel) (block : List SysCall) (n : Nat)
    (hblock : operation_capacity_ok opCap block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    operation_capacity_ok opCap (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show operation_capacity_ok opCap
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact operation_capacity_ok_seqSchedules opCap block _ hblock ih hwithin

/-! ### §13.a.21 Expanded-form headline for `operation_capacity_ok`. -/

theorem operation_capacity_ok_repeated_block_expand
    (opCap : OperationCapacityModel) (block : List SysCall) (n : Nat)
    (hblock : operation_capacity_ok opCap block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    operation_capacity_ok opCap
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact operation_capacity_ok_seqMany_replicate_block opCap block n hblock hwithin

/-! ### §13.a.22 `activeSitesAt` helpers.

    The sampled-time `slot_capacity_ok` checker builds on
    `activeSitesAt t sched`, the list of site claims by SysCalls
    active at time `t`.  Same four helpers as `countActiveKindAt`:
    append distribution, shift compensation, and the two
    out-of-window zero-list facts. -/

theorem activeSitesAt_append (t : Nat) (xs ys : List SysCall) :
    activeSitesAt t (xs ++ ys)
      = activeSitesAt t xs ++ activeSitesAt t ys := by
  unfold activeSitesAt
  rw [List.filter_append, List.flatMap_append]

theorem activeSitesAt_shiftSchedule (t dt : Nat) (xs : List SysCall) :
    activeSitesAt (t + dt) (shiftSchedule dt xs) = activeSitesAt t xs := by
  unfold activeSitesAt shiftSchedule
  rw [List.filter_map, List.flatMap_map]
  congr 1
  apply List.filter_congr
  intro sc _
  simp only [Function.comp]
  unfold syscallActiveAt
  rw [shiftSysCall_begin, shiftSysCall_end]
  have h1 : decide (sc.begin_us + dt ≤ t + dt) = decide (sc.begin_us ≤ t) := by
    have : (sc.begin_us + dt ≤ t + dt) ↔ (sc.begin_us ≤ t) := by omega
    simp [this]
  have h2 : decide (t + dt < sc.end_us + dt) = decide (t < sc.end_us) := by
    have : (t + dt < sc.end_us + dt) ↔ (t < sc.end_us) := by omega
    simp [this]
  rw [h1, h2]

theorem activeSitesAt_eq_nil_of_within_wallclock_at_or_after
    (t : Nat) (xs : List SysCall)
    (hwithin : scheduleWithinWallclock xs = true)
    (h : scheduleWallclockUs xs ≤ t) :
    activeSitesAt t xs = [] := by
  unfold activeSitesAt
  have hfilter : xs.filter (syscallActiveAt t) = [] := by
    rw [List.filter_eq_nil_iff]
    intro sc hsc
    have h_end_le : sc.end_us ≤ scheduleWallclockUs xs :=
      scheduleWithinWallclock_end_le xs sc hsc hwithin
    unfold syscallActiveAt
    have h_not : ¬ (t < sc.end_us) := by omega
    simp [h_not]
  rw [hfilter]
  rfl

theorem activeSitesAt_shiftSchedule_eq_nil_before_offset
    (t dt : Nat) (ys : List SysCall) (h : t < dt) :
    activeSitesAt t (shiftSchedule dt ys) = [] := by
  unfold activeSitesAt
  have hfilter : (shiftSchedule dt ys).filter (syscallActiveAt t) = [] := by
    rw [List.filter_eq_nil_iff]
    intro sc hsc
    have h_begin : dt ≤ sc.begin_us := shifted_begin_ge_offset dt ys sc hsc
    unfold syscallActiveAt
    have h_not : ¬ (sc.begin_us ≤ t) := by omega
    simp [h_not]
  rw [hfilter]
  rfl

/-! ### §13.a.23 `activeSiteCountInZoneAt` helpers.

    Derived from the `activeSitesAt` helpers via `.filter
    (siteInZoneSpec · z) |>.length`. -/

theorem activeSiteCountInZoneAt_append
    (z : ZoneCapacitySpec) (t : Nat) (xs ys : List SysCall) :
    activeSiteCountInZoneAt z t (xs ++ ys)
      = activeSiteCountInZoneAt z t xs + activeSiteCountInZoneAt z t ys := by
  unfold activeSiteCountInZoneAt
  rw [activeSitesAt_append, List.filter_append, List.length_append]

theorem activeSiteCountInZoneAt_shiftSchedule
    (z : ZoneCapacitySpec) (t dt : Nat) (xs : List SysCall) :
    activeSiteCountInZoneAt z (t + dt) (shiftSchedule dt xs)
      = activeSiteCountInZoneAt z t xs := by
  unfold activeSiteCountInZoneAt
  rw [activeSitesAt_shiftSchedule]

theorem activeSiteCountInZoneAt_eq_zero_of_within_wallclock_at_or_after
    (z : ZoneCapacitySpec) (t : Nat) (xs : List SysCall)
    (hwithin : scheduleWithinWallclock xs = true)
    (h : scheduleWallclockUs xs ≤ t) :
    activeSiteCountInZoneAt z t xs = 0 := by
  unfold activeSiteCountInZoneAt
  rw [activeSitesAt_eq_nil_of_within_wallclock_at_or_after t xs hwithin h]
  rfl

theorem activeSiteCountInZoneAt_shiftSchedule_eq_zero_before_offset
    (z : ZoneCapacitySpec) (t dt : Nat) (ys : List SysCall)
    (h : t < dt) :
    activeSiteCountInZoneAt z t (shiftSchedule dt ys) = 0 := by
  unfold activeSiteCountInZoneAt
  rw [activeSitesAt_shiftSchedule_eq_nil_before_offset t dt ys h]
  rfl

/-! ### §13.a.24 Per-time slot-capacity check abstraction. -/

private def slot_cap_check_at (slotCap : SlotCapacityModel)
    (L : List SysCall) (t : Nat) : Bool :=
  slotCap.zones.all fun z =>
    decide (activeSiteCountInZoneAt z t L ≤ z.slot_capacity)

private theorem slot_capacity_ok_eq
    (slotCap : SlotCapacityModel) (L : List SysCall) :
    slot_capacity_ok slotCap L
      = (scheduleEventTimes L).all (slot_cap_check_at slotCap L) := rfl

/-! ### §13.a.25 Shift invariance of `slot_cap_check_at`. -/

private theorem slot_cap_check_at_shiftSchedule
    (slotCap : SlotCapacityModel) (xs : List SysCall) (t dt : Nat) :
    slot_cap_check_at slotCap (shiftSchedule dt xs) (t + dt)
      = slot_cap_check_at slotCap xs t := by
  unfold slot_cap_check_at
  refine List.all_congr rfl ?_
  intro z
  rw [activeSiteCountInZoneAt_shiftSchedule]

/-! ### §13.a.26 `slot_capacity_ok_shiftSchedule_eq`. -/

theorem slot_capacity_ok_shiftSchedule_eq
    (slotCap : SlotCapacityModel) (dt : Nat) (xs : List SysCall) :
    slot_capacity_ok slotCap (shiftSchedule dt xs)
      = slot_capacity_ok slotCap xs := by
  rw [slot_capacity_ok_eq, slot_capacity_ok_eq]
  show ((shiftSchedule dt xs).map (·.begin_us)).all _
      = (xs.map (·.begin_us)).all _
  have h_evt :
      (shiftSchedule dt xs).map (·.begin_us)
        = xs.map (fun sc => sc.begin_us + dt) := by
    unfold shiftSchedule
    rw [List.map_map]
    rfl
  rw [h_evt]
  rw [List.all_map, List.all_map]
  congr 1
  funext sc
  show slot_cap_check_at slotCap (shiftSchedule dt xs) (sc.begin_us + dt)
      = slot_cap_check_at slotCap xs sc.begin_us
  exact slot_cap_check_at_shiftSchedule slotCap xs sc.begin_us dt

/-! ### §13.a.27 `slot_capacity_ok_seqSchedules`. -/

theorem slot_capacity_ok_seqSchedules
    (slotCap : SlotCapacityModel) (xs ys : List SysCall)
    (hxs : slot_capacity_ok slotCap xs = true)
    (hys : slot_capacity_ok slotCap ys = true)
    (hwithin : scheduleWithinWallclock xs = true) :
    slot_capacity_ok slotCap (seqSchedules xs ys) = true := by
  show slot_capacity_ok slotCap (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  rw [slot_capacity_ok_eq]
  show (scheduleEventTimes (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)).all _ = true
  have h_evt :
      scheduleEventTimes (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
        = xs.map (·.begin_us)
          ++ ys.map (fun sc => sc.begin_us + scheduleWallclockUs xs) := by
    show ((xs ++ shiftSchedule (scheduleWallclockUs xs) ys).map _) = _
    rw [List.map_append]
    congr 1
    unfold shiftSchedule
    rw [List.map_map]
    rfl
  rw [h_evt, List.all_append, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- Pre-W sample times.
    rw [List.all_map]
    rw [List.all_eq_true]
    intro sc hsc
    have h_end : sc.end_us ≤ scheduleWallclockUs xs :=
      scheduleWithinWallclock_end_le xs sc hsc hwithin
    have h_begin_lt : sc.begin_us < sc.end_us :=
      scheduleWithinWallclock_begin_lt_end xs sc hsc hwithin
    have h_t_lt_W : sc.begin_us < scheduleWallclockUs xs := by omega
    have h_count_eq :
        ∀ z, activeSiteCountInZoneAt z sc.begin_us
                  (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
                = activeSiteCountInZoneAt z sc.begin_us xs := by
      intro z
      rw [activeSiteCountInZoneAt_append,
          activeSiteCountInZoneAt_shiftSchedule_eq_zero_before_offset z
            sc.begin_us (scheduleWallclockUs xs) ys h_t_lt_W,
          Nat.add_zero]
    have hxs_at : slot_cap_check_at slotCap xs sc.begin_us = true := by
      have hmem : sc.begin_us ∈ scheduleEventTimes xs :=
        List.mem_map.mpr ⟨sc, hsc, rfl⟩
      exact (List.all_eq_true.mp hxs) sc.begin_us hmem
    simp only [Function.comp]
    unfold slot_cap_check_at
    rw [List.all_eq_true]
    intro z hz
    rw [h_count_eq z]
    unfold slot_cap_check_at at hxs_at
    exact (List.all_eq_true.mp hxs_at) z hz
  · -- Post-W sample times.
    rw [List.all_map]
    rw [List.all_eq_true]
    intro sc hsc
    have h_t_ge_W :
        scheduleWallclockUs xs ≤ sc.begin_us + scheduleWallclockUs xs := by omega
    have h_count_eq :
        ∀ z, activeSiteCountInZoneAt z (sc.begin_us + scheduleWallclockUs xs)
                  (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
                = activeSiteCountInZoneAt z sc.begin_us ys := by
      intro z
      rw [activeSiteCountInZoneAt_append,
          activeSiteCountInZoneAt_eq_zero_of_within_wallclock_at_or_after z
            (sc.begin_us + scheduleWallclockUs xs) xs hwithin h_t_ge_W,
          Nat.zero_add]
      exact activeSiteCountInZoneAt_shiftSchedule z sc.begin_us
        (scheduleWallclockUs xs) ys
    have hys_at : slot_cap_check_at slotCap ys sc.begin_us = true := by
      have hmem : sc.begin_us ∈ scheduleEventTimes ys :=
        List.mem_map.mpr ⟨sc, hsc, rfl⟩
      exact (List.all_eq_true.mp hys) sc.begin_us hmem
    simp only [Function.comp]
    unfold slot_cap_check_at
    rw [List.all_eq_true]
    intro z hz
    rw [h_count_eq z]
    unfold slot_cap_check_at at hys_at
    exact (List.all_eq_true.mp hys_at) z hz

/-! ### §13.a.28 Repeated-block slot capacity. -/

theorem slot_capacity_ok_seqMany_replicate_block
    (slotCap : SlotCapacityModel) (block : List SysCall) (n : Nat)
    (hblock : slot_capacity_ok slotCap block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    slot_capacity_ok slotCap (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show slot_capacity_ok slotCap
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact slot_capacity_ok_seqSchedules slotCap block _ hblock ih hwithin

/-! ### §13.a.29 Expanded-form headline for `slot_capacity_ok`. -/

theorem slot_capacity_ok_repeated_block_expand
    (slotCap : SlotCapacityModel) (block : List SysCall) (n : Nat)
    (hblock : slot_capacity_ok slotCap block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    slot_capacity_ok slotCap
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact slot_capacity_ok_seqMany_replicate_block slotCap block n hblock hwithin

/-! ### §13.a.30 `capacity_in_arch_ok` chain.

    Per-syscall predicate.  The shift-equality lemma in §2
    plus `List.all_append` give an immediate full chain. -/

theorem capacity_in_arch_ok_seqSchedules
    (arch : ZonedArch) (xs ys : List SysCall)
    (hxs : capacity_in_arch_ok arch xs = true)
    (hys : capacity_in_arch_ok arch ys = true) :
    capacity_in_arch_ok arch (seqSchedules xs ys) = true := by
  show capacity_in_arch_ok arch (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  unfold capacity_in_arch_ok
  rw [List.all_append]
  rw [show xs.all _ = capacity_in_arch_ok arch xs from rfl,
      show (shiftSchedule (scheduleWallclockUs xs) ys).all _
            = capacity_in_arch_ok arch (shiftSchedule (scheduleWallclockUs xs) ys) from rfl]
  rw [capacity_in_arch_ok_shiftSchedule]
  simp [hxs, hys]

theorem capacity_in_arch_ok_seqMany_replicate_block
    (arch : ZonedArch) (block : List SysCall) (n : Nat)
    (hblock : capacity_in_arch_ok arch block = true) :
    capacity_in_arch_ok arch
        (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show capacity_in_arch_ok arch
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact capacity_in_arch_ok_seqSchedules arch block _ hblock ih

theorem capacity_in_arch_ok_repeated_block_expand
    (arch : ZonedArch) (block : List SysCall) (n : Nat)
    (hblock : capacity_in_arch_ok arch block = true) :
    capacity_in_arch_ok arch
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact capacity_in_arch_ok_seqMany_replicate_block arch block n hblock

/-! ### §13.a.31 `feedback_latency_ok` chain.

    Per-syscall predicate; shift-equality in §3. -/

theorem feedback_latency_ok_seqSchedules
    (t_cycle_us : Nat) (xs ys : List SysCall)
    (hxs : feedback_latency_ok t_cycle_us xs = true)
    (hys : feedback_latency_ok t_cycle_us ys = true) :
    feedback_latency_ok t_cycle_us (seqSchedules xs ys) = true := by
  show feedback_latency_ok t_cycle_us
        (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  unfold feedback_latency_ok
  rw [List.all_append]
  rw [show xs.all _ = feedback_latency_ok t_cycle_us xs from rfl,
      show (shiftSchedule (scheduleWallclockUs xs) ys).all _
            = feedback_latency_ok t_cycle_us
                (shiftSchedule (scheduleWallclockUs xs) ys) from rfl]
  rw [feedback_latency_ok_shiftSchedule]
  simp [hxs, hys]

theorem feedback_latency_ok_seqMany_replicate_block
    (t_cycle_us : Nat) (block : List SysCall) (n : Nat)
    (hblock : feedback_latency_ok t_cycle_us block = true) :
    feedback_latency_ok t_cycle_us
        (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show feedback_latency_ok t_cycle_us
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact feedback_latency_ok_seqSchedules t_cycle_us block _ hblock ih

theorem feedback_latency_ok_repeated_block_expand
    (t_cycle_us : Nat) (block : List SysCall) (n : Nat)
    (hblock : feedback_latency_ok t_cycle_us block = true) :
    feedback_latency_ok t_cycle_us
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact feedback_latency_ok_seqMany_replicate_block t_cycle_us block n hblock

/-! ### §13.a.32 `decoder_react_ok` chain.

    Per-syscall predicate; shift-equality in §4. -/

theorem decoder_react_ok_seqSchedules
    (t_react_us : Nat) (xs ys : List SysCall)
    (hxs : decoder_react_ok t_react_us xs = true)
    (hys : decoder_react_ok t_react_us ys = true) :
    decoder_react_ok t_react_us (seqSchedules xs ys) = true := by
  show decoder_react_ok t_react_us
        (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  unfold decoder_react_ok
  rw [List.all_append]
  rw [show xs.all _ = decoder_react_ok t_react_us xs from rfl,
      show (shiftSchedule (scheduleWallclockUs xs) ys).all _
            = decoder_react_ok t_react_us
                (shiftSchedule (scheduleWallclockUs xs) ys) from rfl]
  rw [decoder_react_ok_shiftSchedule]
  simp [hxs, hys]

theorem decoder_react_ok_seqMany_replicate_block
    (t_react_us : Nat) (block : List SysCall) (n : Nat)
    (hblock : decoder_react_ok t_react_us block = true) :
    decoder_react_ok t_react_us
        (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show decoder_react_ok t_react_us
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact decoder_react_ok_seqSchedules t_react_us block _ hblock ih

theorem decoder_react_ok_repeated_block_expand
    (t_react_us : Nat) (block : List SysCall) (n : Nat)
    (hblock : decoder_react_ok t_react_us block = true) :
    decoder_react_ok t_react_us
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact decoder_react_ok_seqMany_replicate_block t_react_us block n hblock

/-! ### §13.a.33 `window_throughput_ok` chain — vacuous on
       magic-free bodies.

    `repeat_safe_block_ok` requires the body to contain NO
    `RequestMagicState` syscalls.  Append and shift both
    preserve "zero magic SysCalls", so the expanded block is
    also magic-free.  The `window_throughput_ok` filter then
    yields the empty list and `[].all _ = true`. -/

theorem magic_count_append (xs ys : List SysCall) :
    ((xs ++ ys).filter (fun sc => kindIsMagicReq sc.kind)).length
      = (xs.filter (fun sc => kindIsMagicReq sc.kind)).length
        + (ys.filter (fun sc => kindIsMagicReq sc.kind)).length := by
  rw [List.filter_append, List.length_append]

theorem magic_count_seqMany_replicate
    (block : List SysCall) (n : Nat)
    (h : (block.filter (fun sc => kindIsMagicReq sc.kind)).length = 0) :
    ((seqManySchedules (List.replicate n block)).filter
        (fun sc => kindIsMagicReq sc.kind)).length = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show ((seqSchedules block
              (seqManySchedules (List.replicate k block))).filter _).length = 0
      show ((block ++ shiftSchedule (scheduleWallclockUs block)
              (seqManySchedules (List.replicate k block))).filter _).length = 0
      rw [magic_count_append, magic_count_shiftSchedule, h, ih]

theorem magic_count_repeated_block_expand
    (block : List SysCall) (n : Nat)
    (h : (block.filter (fun sc => kindIsMagicReq sc.kind)).length = 0) :
    (((CompressedSchedule.rep n (CompressedSchedule.atom block)).expand).filter
        (fun sc => kindIsMagicReq sc.kind)).length = 0 := by
  rw [rep_atom_expand_eq]
  exact magic_count_seqMany_replicate block n h

theorem window_throughput_ok_of_no_magic
    (sched : List SysCall) (window_us max_per_window : Nat)
    (h : (sched.filter (fun sc => kindIsMagicReq sc.kind)).length = 0) :
    window_throughput_ok sched window_us max_per_window = true := by
  have hfilter :
      (sched.filter (fun sc =>
        match sc.kind with
        | .RequestMagicState _ => true
        | _                    => false)) = [] :=
    List.length_eq_zero_iff.mp h
  show ((sched.filter (fun sc =>
            match sc.kind with
            | .RequestMagicState _ => true
            | _                    => false)).map (·.begin_us)).all
          (fun t0 =>
            decide (magicReq_count_in_window sched t0 window_us ≤ max_per_window))
        = true
  rw [hfilter]
  rfl

/-! ### §13.a.34 `capacity_per_cycle_ok` chain.

    Sampled-time check with zone-load counts.  Same structure
    as `slot_capacity_ok` (uses `activeSitesAt` and a per-zone
    filter+count), but iterates over `arch.zones` (List
    ArchZone) with `z.contains_atom` and `z.capacity`. -/

private def cap_per_cycle_check_at
    (arch : ZonedArch) (L : List SysCall) (t : Nat) : Bool :=
  arch.zones.all (fun z =>
    decide (((activeSitesAt t L).filter z.contains_atom).length ≤ z.capacity))

private theorem capacity_per_cycle_ok_eq
    (arch : ZonedArch) (L : List SysCall) :
    capacity_per_cycle_ok arch L
      = (scheduleEventTimes L).all (cap_per_cycle_check_at arch L) := rfl

private theorem cap_per_cycle_check_at_shiftSchedule
    (arch : ZonedArch) (xs : List SysCall) (t dt : Nat) :
    cap_per_cycle_check_at arch (shiftSchedule dt xs) (t + dt)
      = cap_per_cycle_check_at arch xs t := by
  unfold cap_per_cycle_check_at
  refine List.all_congr rfl ?_
  intro z
  rw [activeSitesAt_shiftSchedule]

theorem capacity_per_cycle_ok_shiftSchedule_eq
    (arch : ZonedArch) (dt : Nat) (xs : List SysCall) :
    capacity_per_cycle_ok arch (shiftSchedule dt xs)
      = capacity_per_cycle_ok arch xs := by
  rw [capacity_per_cycle_ok_eq, capacity_per_cycle_ok_eq]
  show ((shiftSchedule dt xs).map (·.begin_us)).all _
      = (xs.map (·.begin_us)).all _
  have h_evt :
      (shiftSchedule dt xs).map (·.begin_us)
        = xs.map (fun sc => sc.begin_us + dt) := by
    unfold shiftSchedule
    rw [List.map_map]
    rfl
  rw [h_evt, List.all_map, List.all_map]
  congr 1
  funext sc
  show cap_per_cycle_check_at arch (shiftSchedule dt xs) (sc.begin_us + dt)
      = cap_per_cycle_check_at arch xs sc.begin_us
  exact cap_per_cycle_check_at_shiftSchedule arch xs sc.begin_us dt

theorem capacity_per_cycle_ok_seqSchedules
    (arch : ZonedArch) (xs ys : List SysCall)
    (hxs : capacity_per_cycle_ok arch xs = true)
    (hys : capacity_per_cycle_ok arch ys = true)
    (hwithin : scheduleWithinWallclock xs = true) :
    capacity_per_cycle_ok arch (seqSchedules xs ys) = true := by
  show capacity_per_cycle_ok arch
        (xs ++ shiftSchedule (scheduleWallclockUs xs) ys) = true
  rw [capacity_per_cycle_ok_eq]
  show (scheduleEventTimes
          (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)).all _ = true
  have h_evt :
      scheduleEventTimes (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
        = xs.map (·.begin_us)
          ++ ys.map (fun sc => sc.begin_us + scheduleWallclockUs xs) := by
    show ((xs ++ shiftSchedule (scheduleWallclockUs xs) ys).map _) = _
    rw [List.map_append]
    congr 1
    unfold shiftSchedule
    rw [List.map_map]
    rfl
  rw [h_evt, List.all_append, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- Pre-W sample times.
    rw [List.all_map]
    rw [List.all_eq_true]
    intro sc hsc
    have h_end : sc.end_us ≤ scheduleWallclockUs xs :=
      scheduleWithinWallclock_end_le xs sc hsc hwithin
    have h_begin_lt : sc.begin_us < sc.end_us :=
      scheduleWithinWallclock_begin_lt_end xs sc hsc hwithin
    have h_t_lt_W : sc.begin_us < scheduleWallclockUs xs := by omega
    have h_active_eq :
        activeSitesAt sc.begin_us
              (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
            = activeSitesAt sc.begin_us xs := by
      rw [activeSitesAt_append,
          activeSitesAt_shiftSchedule_eq_nil_before_offset sc.begin_us
            (scheduleWallclockUs xs) ys h_t_lt_W,
          List.append_nil]
    have hxs_at : cap_per_cycle_check_at arch xs sc.begin_us = true := by
      have hmem : sc.begin_us ∈ scheduleEventTimes xs :=
        List.mem_map.mpr ⟨sc, hsc, rfl⟩
      rw [capacity_per_cycle_ok_eq] at hxs
      exact (List.all_eq_true.mp hxs) sc.begin_us hmem
    simp only [Function.comp]
    unfold cap_per_cycle_check_at
    rw [List.all_eq_true]
    intro z hz
    rw [h_active_eq]
    unfold cap_per_cycle_check_at at hxs_at
    exact (List.all_eq_true.mp hxs_at) z hz
  · -- Post-W sample times.
    rw [List.all_map]
    rw [List.all_eq_true]
    intro sc hsc
    have h_t_ge_W :
        scheduleWallclockUs xs ≤ sc.begin_us + scheduleWallclockUs xs := by omega
    have h_active_eq :
        activeSitesAt (sc.begin_us + scheduleWallclockUs xs)
              (xs ++ shiftSchedule (scheduleWallclockUs xs) ys)
            = activeSitesAt sc.begin_us ys := by
      rw [activeSitesAt_append,
          activeSitesAt_eq_nil_of_within_wallclock_at_or_after
            (sc.begin_us + scheduleWallclockUs xs) xs hwithin h_t_ge_W,
          List.nil_append]
      exact activeSitesAt_shiftSchedule sc.begin_us
        (scheduleWallclockUs xs) ys
    have hys_at : cap_per_cycle_check_at arch ys sc.begin_us = true := by
      have hmem : sc.begin_us ∈ scheduleEventTimes ys :=
        List.mem_map.mpr ⟨sc, hsc, rfl⟩
      rw [capacity_per_cycle_ok_eq] at hys
      exact (List.all_eq_true.mp hys) sc.begin_us hmem
    simp only [Function.comp]
    unfold cap_per_cycle_check_at
    rw [List.all_eq_true]
    intro z hz
    rw [h_active_eq]
    unfold cap_per_cycle_check_at at hys_at
    exact (List.all_eq_true.mp hys_at) z hz

theorem capacity_per_cycle_ok_seqMany_replicate_block
    (arch : ZonedArch) (block : List SysCall) (n : Nat)
    (hblock : capacity_per_cycle_ok arch block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    capacity_per_cycle_ok arch
        (seqManySchedules (List.replicate n block)) = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show capacity_per_cycle_ok arch
            (seqSchedules block (seqManySchedules (List.replicate k block))) = true
      exact capacity_per_cycle_ok_seqSchedules arch block _ hblock ih hwithin

theorem capacity_per_cycle_ok_repeated_block_expand
    (arch : ZonedArch) (block : List SysCall) (n : Nat)
    (hblock : capacity_per_cycle_ok arch block = true)
    (hwithin : scheduleWithinWallclock block = true) :
    capacity_per_cycle_ok arch
        (CompressedSchedule.rep n (CompressedSchedule.atom block)).expand = true := by
  rw [rep_atom_expand_eq]
  exact capacity_per_cycle_ok_seqMany_replicate_block arch block n hblock hwithin

/-! ### §13.b Symbolic-repeat body-level extraction theorems

    Even when the per-conjunct seqSchedules / repeated /
    expand chain is not yet closed parametrically (see §13.c
    for documented blockers), we CAN extract the body-level
    fact for each A-conjunct from `symbolic_rep_strict_ok`.
    These extractions are part of the eventual headline
    chain. -/

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

/-! ### §13.c Parametric `seqSchedules` and repeated-block
       lemmas for A-conjuncts — PARTIAL

    Status (this tick):
    * `exclusivity_ok` — full parametric chain CLOSED in
      §13.a.5–§13.a.8 and headline in §13.b.5.
    * `factory_exclusivity_ok` — full parametric chain CLOSED
      in §13.a.9–§13.a.14 and headline in §13.b.6.
      Requires hardware-generic input
      `scheduleWithinWallclock block` (strict positivity of
      every block's SysCall durations).
    * `operation_capacity_ok` — full parametric chain CLOSED
      in §13.a.15–§13.a.21 and headline in §13.b.7.
      Uses sampled-time decomposition rather than pair check:
      `countActiveKindAt_append`, `countActiveKindAt_shiftSchedule`,
      and out-of-window zero-count helpers.
    * `slot_capacity_ok` — full parametric chain CLOSED in
      §13.a.22–§13.a.29 and headline in §13.b.8.  Mirrors the
      operation-capacity chain through `activeSitesAt` /
      `activeSiteCountInZoneAt` helpers (append distribution,
      shift compensation, out-of-window zero-list facts).

    All four Obligation-A parametric chains are now closed.
    The combined-strict headline fusing the four A-headlines
    plus the Obligation-B and Obligation-C headlines is
    `symbolic_rep_implies_expanded_block_combined_strict_ok`
    in §13.b.9.  No further work is required at this layer of
    the bundle.

    The four A-conjuncts (`exclusivity_ok`,
    `factory_exclusivity_ok`, `operation_capacity_ok`,
    `slot_capacity_ok`) are all defined via either:

      * pairwise check `(List.range n).all (fun i =>
        (List.range n).all (fun j => if i < j then ... else
        true))` — for `exclusivity_ok` and
        `factory_exclusivity_ok`;

      * sampled-time check `scheduleEventTimes
        sched .all (fun t => ... countActiveKindAt t sched
        ≤ cap ...)` — for `operation_capacity_ok` and
        `slot_capacity_ok`.

    Both styles use `List.range`-indexed `.all` with
    index-keyed `sched[i]?` access, which requires careful
    parametric proofs:

      (i)  Reduce each pairwise check after `shiftSchedule`
           to the original check via `intervals_overlap_shift_same`,
           `syscall_acts_on_shiftSysCall`,
           `syscall_factory_claims_shiftSysCall`, and a
           `List.getElem?_map` lemma threading `Option.map
           (shiftSysCall dt)` through index access.

      (ii) For `seqSchedules`, decompose pairs into
           same-block / cross-block; cross-block pairs use
           `cross_pair_no_overlap` (already proven), and
           same-block pairs are inherited from `hxs`/`hys`
           after suitable index reindexing
           (`(xs ++ ys)[i]? = if i < xs.length then xs[i]?
           else ys[i - xs.length]?`).

      (iii) For sampled-time checks, partition
            `scheduleEventTimes (xs ++ shifted ys)` into times
            `< W xs` (from `xs`) and times `≥ W xs` (from
            shifted ys), and show the active sets at each
            sample come from the respective block only — by
            `cross_pair_no_overlap` and
            `scheduleWithinWallclock`.

    Each piece is bounded mechanically but the index/range
    plumbing is substantial.  Concrete adder seq2/seq3
    instances are already verified by `native_decide` in §9.e
    / §9.f.

    Documented next steps for closing the parametric chain:

      Step 1: prove `shiftSchedule_getElem?` :
        `(shiftSchedule dt xs)[i]? = (xs[i]?).map (shiftSysCall dt)`.
      Step 2: prove `exclusivity_ok_shiftSchedule` using
        intervals_overlap_shift_same + syscall_acts_on_shiftSysCall.
      Step 3: prove `exclusivity_ok_seqSchedules` by index
        decomposition using `cross_pair_no_overlap`.
      Step 4: lift to `exclusivity_ok_seqMany_replicate_block`
        and `exclusivity_ok_repeated_block_expand` by induction.
      Step 5: chain through `symbolic_rep_ok_implies_body_exclusivity_ok`
        to get the headline.

    Repeat for `factory_exclusivity_ok` (replace
    `syscall_acts_on` with `syscall_factory_claims`).

    For `operation_capacity_ok` and `slot_capacity_ok`,
    same plan but with sampled-time decomposition. -/

/-! ### §13.d Concrete adder-block A-conjuncts via `native_decide`

    Already proven in §9.e:

      `adder_seq2_exclusivity_ok`
      `adder_seq2_factory_exclusivity_ok`
      `adder_seq2_operation_capacity_ok`
      `adder_seq2_slot_capacity_ok`
      `adder_seq2_obligation_A_ok` (combined)

    And in §9.f for `seq3` (144 SysCalls).  These remain
    valid concrete witnesses for moderate `n`. -/

/-! ## §8. Status

    Closed parametric theorems (depend only on `propext` /
    `Quot.sound` etc.):

      shiftSysCall_kind, shiftSysCall_begin, shiftSysCall_end,
      shiftSysCall_duration,
      syscall_acts_on_shiftSysCall,
      syscall_factory_claims_shiftSysCall,
      shiftSchedule_nil, shiftSchedule_cons,
      capacity_in_arch_ok_shiftSchedule (+ _of_ok),
      feedback_latency_ok_shiftSchedule (+ _of_ok),
      decoder_react_ok_shiftSchedule (+ _of_ok),
      freshnessStep_shiftSysCall,
      runFreshness_shiftSchedule,
      ancilla_freshness_ok_shiftSchedule (+ _of_ok),
      kindIs*_shiftSysCall (Gate2q, Measure, Decode, Feedback,
                            MagicReq, FreshAnc),
      magic_count_shiftSchedule,
      no_magic_shiftSchedule.

    Closed concrete instances (via `native_decide`):

      adder_n1_repeated_10_expanded_strict_ok,
      adder_n1_repeated_1000000_symbolic_ok,
      adder_n1_repeated_1000000_resource_wallclock,
      adder_n1_repeated_1000000_resource_gate2q,
      adder_n1_repeated_1000000_resource_syscall_count.

    Remaining for the FULL parametric theorem
    `symbolic_rep_strict_ok_implies_expanded_strict_ok`:

      (A) Sequential composition lemmas on `seqSchedules`:
          - `exclusivity_ok_seqSchedules` (pairwise check
            survives non-overlapping windows);
          - `capacity_per_cycle_ok_seqSchedules`;
          - `operation_capacity_ok_seqSchedules`;
          - `slot_capacity_ok_seqSchedules`;
          - `factory_exclusivity_ok_seqSchedules` (vacuous
            under no-magic).

      (B) `feedback_after_decode_ok_seqSchedules` — the
          inner `.any` self-reference requires a custom
          induction.

      (C) Ancilla-freshness state-monotonicity at the
          boundary — body's trajectory from "all Dirty"
          equals its trajectory from "all Free" when the
          `RequestFreshAncilla` "next free site" rule is
          used.  Stateful `runFreshness` equivalence lemma.

    Each obligation is well-scoped and bounded in size.
    None requires new axioms or schema changes.
-/

end FormalRV.Framework.CompressedRepeatSoundness
