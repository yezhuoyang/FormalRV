/-
  `feedback_after_decode_ok` under composition (Obligation B).

  The self-referential inner `.any` is factored through
  `decode_matches_feedback`; the check is shift-invariant, monotone
  under `++`, preserved by `seqSchedules` and by n-fold repeat of a
  block.  Headline: `symbolic_rep_implies_expanded_feedback_after_decode_ok`
  — symbolic-repeat acceptance implies the EXPANDED schedule passes the
  feedback check, for arbitrary n.  No `sorry`, no custom `axiom`.
-/

import FormalRV.System.Artifacts.LayeredArtifactInterface
import FormalRV.System.Artifacts.CompressedRepeat.ShiftInvariance

namespace FormalRV.System.CompressedRepeatSoundness

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.AdderSystem
open FormalRV.System.LayeredArtifactInterface

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

    Once the schedule argument is named, the inner `.any` body
    of `feedback_after_decode_ok` IS
    `decode_matches_feedback cid sc.begin_us` (forced by `show`
    inside the proof), so shift invariance follows from
    `any_decode_matches_feedback_shift_same`. -/

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

/-- **Headline Obligation-B theorem.**  The symbolic check
    `symbolic_rep_strict_ok` is reps-independent by design (it
    checks the body once); this theorem supplies the soundness
    leg: acceptance implies the EXPANDED n-fold schedule passes
    `feedback_after_decode_ok`, for arbitrary `n`. -/
theorem symbolic_rep_implies_expanded_feedback_after_decode_ok
    (models : SystemModels) (body : List SysCall) (n : Nat)
    (h : symbolic_rep_strict_ok models body n = true) :
    feedback_after_decode_ok
        (CompressedSchedule.rep n (CompressedSchedule.atom body)).expand = true :=
  feedback_after_decode_ok_repeated_atom_expand body n
    (symbolic_rep_ok_implies_body_feedback_after_decode_ok models body n h)

end FormalRV.System.CompressedRepeatSoundness
