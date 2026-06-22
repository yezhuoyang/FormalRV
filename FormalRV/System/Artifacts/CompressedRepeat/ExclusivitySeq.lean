/-
  Obligation A, pairwise checks (CLOSED): `exclusivity_ok` and
  `factory_exclusivity_ok` under shift, `seqSchedules`, n-fold
  replicate, and expanded repeat.

  Both chains use the pair-check abstraction (`excl_pair_check`,
  `factory_excl_pair_check`), `shiftSchedule_getElem?` index threading,
  same-block/cross-block index decomposition, and
  `cross_pair_no_overlap` for the cross-boundary pairs.  The
  `scheduleWithinWallclock` hypothesis (strict-positive durations) is
  the structural input.  No `sorry`, no custom `axiom`.
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

end FormalRV.System.CompressedRepeatSoundness
