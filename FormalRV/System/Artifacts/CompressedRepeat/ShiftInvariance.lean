/-
  Shift/append invariance core for SysCall schedules.

  §1–§6: `shiftSysCall` / `shiftSchedule` preserve `kind`, duration,
  `syscall_acts_on`, `syscall_factory_claims`; the per-call
  strict-bundle conjuncts (`capacity_in_arch_ok`,
  `feedback_latency_ok`, `decoder_react_ok`, `ancilla_freshness_ok`)
  and magic counts are invariant under uniform time shift.

  §9.a–d: the sequential-composition window basics.  A block is
  `scheduleWithinWallclock` when every SysCall has positive duration
  and ends by the block's wallclock (§9.a); the shifted second block
  of a `seqSchedules` then begins at or after the first block's
  wallclock (`shifted_begin_ge_offset`, §9.b); with the
  interval-overlap lemmas (§9.c) this yields `cross_pair_no_overlap`
  (§9.d) — no SysCall of the first block overlaps any SysCall of the
  shifted second block.  This is the geometric fact behind every
  pairwise/capacity repeat chain in the CompressedRepeat split.

  Finally, `rep_atom_expand_eq : (rep n (atom b)).expand =
  seqManySchedules (List.replicate n b)` reduces compressed repeats
  to sequential composition.  Foundation for the rest of the
  CompressedRepeat split.  No `sorry`, no custom `axiom`.
-/

import FormalRV.System.Artifacts.LayeredArtifactInterface

namespace FormalRV.System.CompressedRepeatSoundness

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.AdderSystem
open FormalRV.System.LayeredArtifactInterface

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

/-- Reduction lemma: `(rep n (atom body)).expand` equals
    `seqManySchedules (List.replicate n body)`.  The
    `CompressedSchedule.expand` recursor uses well-founded
    recursion, so we go via `simp` rather than `rfl`. -/
theorem rep_atom_expand_eq (body : List SysCall) (n : Nat) :
    (CompressedSchedule.rep n (CompressedSchedule.atom body)).expand
      = seqManySchedules (List.replicate n body) := by
  simp [CompressedSchedule.expand]

end FormalRV.System.CompressedRepeatSoundness
