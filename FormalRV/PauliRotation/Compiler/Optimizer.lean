/-
  FormalRV.PauliRotation.Compiler.Optimizer
  ────────────────────────────────
  **THE CERTIFICATE-CHECKED OPTIMIZER INTERFACE.**

  An optimizer — heuristic, hand-written, or EXTERNAL AND UNTRUSTED — does
  not need to be verified.  It needs to EMIT A TRACE: a list of rule
  applications, each naming a position in the flat rotation sequence.  The
  executable checker `applyTrace` replays the trace, re-checking every
  side condition (commutation, angle class, canonicity), and ONE soundness
  theorem says the replay preserves the sequence's denotation EXACTLY:

      applyTrace n t rs = some rs'  →  seqDenote n rs = seqDenote n rs'

  The rule set is complete for Litinski reorganization:

      swap      — exchange adjacent rotations with commuting axes
      push      — DELAY a ±π/4 Clifford past an anticommuting rotation
                  (axis ↦ `mulF`, sign in `neg` — `Rot.pushedBy`)
      pushHalf  — delay a ±π/2 Pauli rotation (angle sign flips)
      cancel    — adjacent inverse rotations vanish
      merge     — adjacent equal rotations fuse to the doubled angle
      mergePi   — two adjacent equal π rotations vanish ((−1)² = 1)

  All checks are decidable and the boundedness invariant (canonical axes
  within width) is PRESERVED by every rule (`mulF_sorted`/`mulF_width`
  cover the push), so traces compose.  Schedule the checked output with
  `scheduleList` (or the K-bounded `scheduleListK`) and the existing
  capstones carry optimized programs end-to-end.
-/
import FormalRV.PauliRotation.Compiler.PushRules
import FormalRV.PauliRotation.Compiler.Rules
import FormalRV.PauliRotation.Compiler.Scheduler
import FormalRV.PauliRotation.Correctness.Assembly
import FormalRV.PauliRotation.Compiler.SchedulerK

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-! ## §1. The boundedness invariant (decidable). -/

/-- Every axis canonical and within width `n`. -/
def rotsBoundedB (n : Nat) (rs : List Rot) : Bool :=
  rs.all (fun r =>
    sortedStrict r.axis && decide (PauliProduct.width r.axis ≤ n))

theorem rotsBoundedB_cons {n : Nat} {r : Rot} {rs : List Rot}
    (h : rotsBoundedB n (r :: rs) = true) :
    (sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ n)
      ∧ rotsBoundedB n rs = true := by
  simp only [rotsBoundedB, List.all_cons, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  exact ⟨h.1, h.2⟩

theorem rotsBoundedB_cons_intro {n : Nat} {r : Rot} {rs : List Rot}
    (hr : sortedStrict r.axis = true) (hw : PauliProduct.width r.axis ≤ n)
    (h : rotsBoundedB n rs = true) : rotsBoundedB n (r :: rs) = true := by
  simp only [rotsBoundedB, List.all_cons, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  exact ⟨⟨hr, hw⟩, h⟩

/-! ## §2. The local rules (head of the list). -/

/-- One optimizer rule, naming the position it fires at. -/
inductive RuleApp where
  /-- Exchange the rotations at positions `i, i+1` (axes must commute). -/
  | swap (i : Nat)
  /-- Delay the ±π/4 Clifford at position `i` past the anticommuting
  rotation at `i+1` (which becomes `pushedBy`). -/
  | push (i : Nat)
  /-- Delay the ±π/2 Pauli rotation at position `i` (the rotation at `i+1`
  flips its angle sign). -/
  | pushHalf (i : Nat)
  /-- Cancel the adjacent inverse pair at positions `i, i+1`. -/
  | cancel (i : Nat)
  /-- Fuse the adjacent equal pair at positions `i, i+1` into the doubled
  angle. -/
  | merge (i : Nat)
  /-- Two adjacent equal π rotations vanish. -/
  | mergePi (i : Nat)
  deriving Repr, DecidableEq

/-- Apply one rule at the HEAD of the sequence (all side conditions
re-checked). -/
def applyHead : RuleApp → List Rot → Option (List Rot)
  | .swap _, r :: s :: rest =>
      if commF s.axis r.axis then some (s :: r :: rest) else none
  | .push _, r :: s :: rest =>
      if r.angle == .piQuarter && !(commF r.axis s.axis)
      then some (r.pushedBy s :: r :: rest) else none
  | .pushHalf _, r :: s :: rest =>
      if r.angle == .piHalf && !(commF r.axis s.axis)
      then some (Rot.pushedByHalf s :: r :: rest) else none
  | .cancel _, r :: s :: rest =>
      if s == r.inv then some rest else none
  | .merge _, r :: s :: rest =>
      match r.angle.doubled with
      | some b => if s == r then some ({ r with angle := b } :: rest) else none
      | none   => none
  | .mergePi _, r :: s :: rest =>
      if r.angle == .pi && s == r then some rest else none
  | _, _ => none

/-- Apply a rule at its named position. -/
def applyRule (a : RuleApp) : List Rot → Option (List Rot) :=
  go (pos a)
where
  pos : RuleApp → Nat
    | .swap i | .push i | .pushHalf i | .cancel i | .merge i | .mergePi i => i
  go : Nat → List Rot → Option (List Rot)
    | 0, rs => applyHead a rs
    | k + 1, r :: rs => (go k rs).map (r :: ·)
    | _ + 1, [] => none

/-- **The executable certificate checker**: replay a trace. -/
def applyTrace : List RuleApp → List Rot → Option (List Rot)
  | [], rs => some rs
  | a :: t, rs => (applyRule a rs).bind (applyTrace t)

/-! ## §3. Soundness of the head rules. -/

/-- Merging two equal rotations at the `Rot` level. -/
private theorem denote_merge_rot (n : Nat) (r : Rot) {b : RAngle}
    (hb : r.angle.doubled = some b) :
    Rot.denote n r * Rot.denote n r
      = Rot.denote n { r with angle := b } := by
  rw [Rot.denote_mul_same_axis n r r rfl]
  show rotOf (r.theta + r.theta) (axisMat n r.axis)
      = rotOf (Rot.theta { r with angle := b }) (axisMat n r.axis)
  congr 1
  have hv := RAngle.doubled_val hb
  show r.theta + r.theta
      = if r.neg then -(RAngle.val b) else RAngle.val b
  rw [show r.theta = if r.neg then -r.angle.val else r.angle.val from rfl]
  cases r.neg <;> simp <;> rw [hv] <;> ring

private theorem rotOf_two_pi {d : Type*} [DecidableEq d]
    (M : Matrix d d ℂ) : rotOf (2 * Real.pi) M = 1 := by
  unfold rotOf
  rw [Real.cos_two_pi, Real.sin_two_pi]
  simp

private theorem rotOf_neg_two_pi {d : Type*} [DecidableEq d]
    (M : Matrix d d ℂ) : rotOf (-(2 * Real.pi)) M = 1 := by
  unfold rotOf
  rw [Real.cos_neg, Real.sin_neg, Real.cos_two_pi, Real.sin_two_pi]
  simp

/-- Two equal π rotations vanish at the `Rot` level. -/
private theorem denote_merge_pi (n : Nat) (r : Rot) (hr : r.angle = .pi) :
    Rot.denote n r * Rot.denote n r = 1 := by
  rw [Rot.denote_mul_same_axis n r r rfl]
  have hθ : r.theta = if r.neg then -Real.pi else Real.pi := by
    rw [show r.theta = if r.neg then -r.angle.val else r.angle.val from rfl,
        hr]
    rfl
  cases hneg : r.neg <;> rw [hθ, hneg]
  · rw [if_neg (by simp),
        show Real.pi + Real.pi = 2 * Real.pi from by ring]
    exact rotOf_two_pi _
  · rw [if_pos rfl,
        show -Real.pi + -Real.pi = -(2 * Real.pi) from by ring]
    exact rotOf_neg_two_pi _

/-- **Head-rule soundness + invariant preservation.** -/
theorem applyHead_sound (n : Nat) (a : RuleApp) (rs rs' : List Rot)
    (hb : rotsBoundedB n rs = true)
    (h : applyHead a rs = some rs') :
    seqDenote n rs = seqDenote n rs' ∧ rotsBoundedB n rs' = true := by
  match a, rs with
  | .swap _, r :: s :: rest =>
      simp only [applyHead] at h
      split at h
      next hc =>
        injection h with h
        subst h
        obtain ⟨hr, hbt⟩ := rotsBoundedB_cons hb
        obtain ⟨hs, hbr⟩ := rotsBoundedB_cons hbt
        constructor
        · show seqDenote n rest * Rot.denote n s * Rot.denote n r
              = seqDenote n rest * Rot.denote n r * Rot.denote n s
          rw [Matrix.mul_assoc, Matrix.mul_assoc,
              (Rot.denote_swap n r s hs.1 hs.2 hc)]
        · exact rotsBoundedB_cons_intro hs.1 hs.2
            (rotsBoundedB_cons_intro hr.1 hr.2 hbr)
      next => exact absurd h (by simp)
  | .push _, r :: s :: rest =>
      simp only [applyHead] at h
      split at h
      next hc =>
        injection h with h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
        obtain ⟨hr, hbt⟩ := rotsBoundedB_cons hb
        obtain ⟨hs, hbr⟩ := rotsBoundedB_cons hbt
        have hpush := Rot.denote_push_delay n r s hc.1 hr.1 hr.2 hs.1 hc.2
        constructor
        · show seqDenote n rest * Rot.denote n s * Rot.denote n r
              = seqDenote n rest * Rot.denote n r
                  * Rot.denote n (r.pushedBy s)
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hpush]
        · refine rotsBoundedB_cons_intro
            (mulF_sorted r.axis s.axis hr.1 hs.1)
            (Nat.le_trans (mulF_width r.axis s.axis) (max_le hr.2 hs.2))
            (rotsBoundedB_cons_intro hr.1 hr.2 hbr)
      next => exact absurd h (by simp)
  | .pushHalf _, r :: s :: rest =>
      simp only [applyHead] at h
      split at h
      next hc =>
        injection h with h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
        obtain ⟨hr, hbt⟩ := rotsBoundedB_cons hb
        obtain ⟨hs, hbr⟩ := rotsBoundedB_cons hbt
        have hpush := Rot.denote_push_half_delay n r s hc.1 hr.1 hr.2 hc.2
        constructor
        · show seqDenote n rest * Rot.denote n s * Rot.denote n r
              = seqDenote n rest * Rot.denote n r
                  * Rot.denote n (Rot.pushedByHalf s)
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hpush]
        · exact rotsBoundedB_cons_intro hs.1 hs.2
            (rotsBoundedB_cons_intro hr.1 hr.2 hbr)
      next => exact absurd h (by simp)
  | .cancel _, r :: s :: rest =>
      simp only [applyHead] at h
      split at h
      next hc =>
        injection h with h
        subst h
        simp only [beq_iff_eq] at hc
        subst hc
        obtain ⟨hr, hbt⟩ := rotsBoundedB_cons hb
        obtain ⟨_, hbr⟩ := rotsBoundedB_cons hbt
        constructor
        · show seqDenote n rest * Rot.denote n r.inv * Rot.denote n r
              = seqDenote n rest
          rw [Matrix.mul_assoc, Rot.denote_inv_mul, Matrix.mul_one]
        · exact hbr
      next => exact absurd h (by simp)
  | .merge _, r :: s :: rest =>
      simp only [applyHead] at h
      cases hdb : r.angle.doubled with
      | none =>
          simp only [hdb] at h
          exact absurd h (by simp)
      | some b =>
          simp only [hdb] at h
          split at h
          next hc =>
            injection h with h
            subst h
            simp only [beq_iff_eq] at hc
            subst hc
            obtain ⟨hr, hbt⟩ := rotsBoundedB_cons hb
            obtain ⟨_, hbr⟩ := rotsBoundedB_cons hbt
            constructor
            · show seqDenote n rest * Rot.denote n s * Rot.denote n s
                  = seqDenote n rest * Rot.denote n { s with angle := b }
              rw [Matrix.mul_assoc, denote_merge_rot n s hdb]
            · exact rotsBoundedB_cons_intro hr.1 hr.2 hbr
          next => exact absurd h (by simp)
  | .mergePi _, r :: s :: rest =>
      simp only [applyHead] at h
      split at h
      next hc =>
        injection h with h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨hpi, hsr⟩ := hc
        subst hsr
        obtain ⟨_, hbt⟩ := rotsBoundedB_cons hb
        obtain ⟨_, hbr⟩ := rotsBoundedB_cons hbt
        constructor
        · show seqDenote n rest * Rot.denote n s * Rot.denote n s
              = seqDenote n rest
          rw [Matrix.mul_assoc, denote_merge_pi n s hpi, Matrix.mul_one]
        · exact hbr
      next => exact absurd h (by simp)

/-! ## §4. Soundness of positioned and traced application. -/

theorem applyRule_go_sound (n : Nat) (a : RuleApp) :
    ∀ (k : Nat) (rs rs' : List Rot),
      rotsBoundedB n rs = true →
      applyRule.go a k rs = some rs' →
      seqDenote n rs = seqDenote n rs' ∧ rotsBoundedB n rs' = true
  | 0, rs, rs', hb, h => applyHead_sound n a rs rs' hb h
  | k + 1, r :: rs, rs', hb, h => by
      simp only [applyRule.go, Option.map_eq_some_iff] at h
      obtain ⟨ys, hgo, hys⟩ := h
      subst hys
      obtain ⟨hr, hbt⟩ := rotsBoundedB_cons hb
      obtain ⟨hd, hbd⟩ := applyRule_go_sound n a k rs ys hbt hgo
      constructor
      · show seqDenote n rs * Rot.denote n r = seqDenote n ys * Rot.denote n r
        rw [hd]
      · exact rotsBoundedB_cons_intro hr.1 hr.2 hbd

/-- **One-rule soundness**: a successful application preserves the
denotation exactly and keeps the sequence bounded. -/
theorem applyRule_sound (n : Nat) (a : RuleApp) (rs rs' : List Rot)
    (hb : rotsBoundedB n rs = true)
    (h : applyRule a rs = some rs') :
    seqDenote n rs = seqDenote n rs' ∧ rotsBoundedB n rs' = true :=
  applyRule_go_sound n a (applyRule.pos a) rs rs' hb h

/-- **THE CERTIFICATE THEOREM**: replaying ANY accepted trace preserves the
flat sequence's denotation EXACTLY (and boundedness).  An optimizer needs
no verification — only a trace the checker accepts. -/
theorem applyTrace_sound (n : Nat) :
    ∀ (t : List RuleApp) (rs rs' : List Rot),
      rotsBoundedB n rs = true →
      applyTrace t rs = some rs' →
      seqDenote n rs = seqDenote n rs' ∧ rotsBoundedB n rs' = true
  | [], rs, rs', hb, h => by
      injection h with h
      subst h
      exact ⟨rfl, hb⟩
  | a :: t, rs, rs', hb, h => by
      simp only [applyTrace, Option.bind_eq_some_iff] at h
      obtain ⟨ys, ha, ht⟩ := h
      obtain ⟨hd1, hb1⟩ := applyRule_sound n a rs ys hb ha
      obtain ⟨hd2, hb2⟩ := applyTrace_sound n t ys rs' hb1 ht
      exact ⟨hd1.trans hd2, hb2⟩

/-! ## §5. End-to-end: certified-optimized gadget compilation. -/

open FormalRV.Resource in
/-- Boundedness of the compiled gadget sequence (discharges the checker's
input invariant from `gateRots_bounded`). -/
theorem gateRots_boundedB (g : FormalRV.Framework.Gate) (n : Nat)
    (hops : opsOK g = true) (hw : Resource.width g ≤ n) :
    rotsBoundedB n (gateRots g) = true := by
  unfold rotsBoundedB
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨hs, hwid⟩ := gateRots_bounded g hops r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hs, Nat.le_trans hwid hw⟩

open FormalRV.Resource in
/-- **THE OPTIMIZED-COMPILATION CAPSTONE**: take ANY gadget, optimize its
rotation sequence with ANY untrusted optimizer, check the trace, schedule
the result — the layered program still implements the gadget's Boolean
semantics up to its global phase. -/
theorem optimized_schedule_applyNat (n : Nat) (g : FormalRV.Framework.Gate)
    (hops : opsOK g = true) (hw : Resource.width g ≤ n)
    (t : List RuleApp) (rs' : List Rot)
    (hcheck : applyTrace t (gateRots g) = some rs') :
    RotProg.denote n (scheduleList rs')
      = gphase g • applyMat n g := by
  obtain ⟨hd, hb⟩ := applyTrace_sound n t (gateRots g) rs'
    (gateRots_boundedB g n hops hw) hcheck
  have hb' : ∀ r ∈ rs', sortedStrict r.axis = true
      ∧ PauliProduct.width r.axis ≤ n := by
    intro r hr
    have := (List.all_eq_true.mp hb) r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  rw [scheduleList_denote n rs' hb', ← hd, gateRots_denote_applyNat n g hops hw]

open FormalRV.Resource in
/-- **THE HARDWARE-BOUNDED OPTIMIZED CAPSTONE**: certified-optimize ANY
gadget's rotation sequence, compile it with the K-bounded scheduler — the
layered program respects the hardware cap (every layer ≤ K) AND still
implements the gadget's Boolean semantics up to its global phase. -/
theorem optimized_scheduleK_applyNat (K n : Nat) (hK : 1 ≤ K)
    (g : FormalRV.Framework.Gate)
    (hops : opsOK g = true) (hw : Resource.width g ≤ n)
    (t : List RuleApp) (rs' : List Rot)
    (hcheck : applyTrace t (gateRots g) = some rs') :
    RotProg.denote n (scheduleListK K rs') = gphase g • applyMat n g
      ∧ layersLE K (scheduleListK K rs') = true := by
  obtain ⟨hd, hb⟩ := applyTrace_sound n t (gateRots g) rs'
    (gateRots_boundedB g n hops hw) hcheck
  have hb' : ∀ r ∈ rs', sortedStrict r.axis = true
      ∧ PauliProduct.width r.axis ≤ n := by
    intro r hr
    have := (List.all_eq_true.mp hb) r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  refine ⟨?_, scheduleListK_layers K hK rs'⟩
  rw [scheduleListK_denote K n rs' hb', ← hd,
      gateRots_denote_applyNat n g hops hw]

end FormalRV.PauliRotation
