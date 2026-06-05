import FormalRV.Shor.MainAlgorithm.ContinuedFractionBridge.CFAuxDepthMatching

namespace FormalRV.SQIRPort

/-- **ℝ-version of `cf_of_div_succ_step`** (added 2026-05-24): the (n+1)-th
stream entry of `GenContFract.of (o/m : ℝ)` equals the n-th of
`GenContFract.of (m/(o%m) : ℝ)`. Same proof as the ℚ version. -/
theorem cf_of_div_succ_step_R (o m n : Nat) (_h_mod_pos : 0 < o % m) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.get? (n+1) =
      (GenContFract.of (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))).s.get? n := by
  rw [GenContFract.of_s_succ]
  congr 2
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]

/-- **Terminated at 0 when `o % m = 0`** (added 2026-05-24): when the
remainder is 0 (including the m = 0 case, where o % 0 = o ≠ 0 doesn't
hold but v = 0/0 = 0 ℝ still gives terminated), mathlib's CF for v = o/m
terminates at step 0. Extracted from the inline proof in
`eucl_iter_match_stream`. -/
theorem terminated_at_0_when_mod_zero (o m : Nat) (h_om : o % m = 0) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0 := by
  rw [GenContFract.terminatedAt_iff_s_none]
  have h_fract_eq : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) = 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod, h_om]
    simp
  have h_stream_none : GenContFract.IntFractPair.stream
      (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 1 = none :=
    GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero (n := 0) rfl h_fract_eq
  rw [GenContFract.of_s_head_aux, h_stream_none]
  rfl

/-- **Converse base case** (added 2026-05-24): when mathlib's CF terminates
at step 0 for v=o/m with m > 0, then o%m = 0.

This is the j=0 base case of the eventual `eucl_terminated_of_mathlib_terminated`
helper. Direct from `nondiv_of_not_terminated_zero`'s contrapositive. -/
theorem mod_zero_of_terminated_at_0 (o m : Nat) (_h_m_pos : 0 < m)
    (h_term : (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0) :
    o % m = 0 := by
  by_contra h_om_ne
  -- nondiv_of_not_terminated_zero: ¬ Terminated at 0 → o%m ≠ 0.
  -- We have Terminated at 0 and want o%m = 0.
  -- The lemma's contrapositive (o%m = 0 → Terminated at 0) goes the wrong way.
  -- Need direct proof: Terminated at 0 → fract v = 0 → o%m = 0.
  apply h_om_ne
  -- Goal: o % m = 0.
  -- From Terminated at 0: s.get? 0 = none → stream 1 = none → fract v = 0 → o%m = 0.
  rw [GenContFract.terminatedAt_iff_s_none] at h_term
  rw [GenContFract.of_s_head_aux] at h_term
  -- h_term : Option.bind (stream v 1) ... = none
  -- So stream v 1 = none.
  have h_stream_1 : GenContFract.IntFractPair.stream
      (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 1 = none := by
    rcases h_eq : GenContFract.IntFractPair.stream
        (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 1 with _ | ifp
    · rfl
    · rw [h_eq] at h_term; exact absurd h_term (by simp)
  -- stream 1 = none → fract v = 0.
  rw [GenContFract.IntFractPair.succ_nth_stream_eq_none_iff] at h_stream_1
  -- h_stream_1 : stream 0 = none ∨ ∃ ifp, stream 0 = some ifp ∧ ifp.fr = 0
  rcases h_stream_1 with h_s0_none | ⟨ifp, h_s0, h_fr⟩
  · -- stream 0 = none: impossible (stream 0 is always some).
    have : GenContFract.IntFractPair.stream
        (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 0 =
        some (GenContFract.IntFractPair.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) := rfl
    rw [this] at h_s0_none
    exact absurd h_s0_none (by simp)
  · -- stream 0 = some ifp, ifp.fr = 0.
    -- stream 0 = some {b=⌊v⌋, fr=fract v}, so ifp.fr = fract v = 0.
    have h_s0_val : GenContFract.IntFractPair.stream
        (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 0 =
        some (GenContFract.IntFractPair.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) := rfl
    rw [h_s0_val] at h_s0
    have h_ifp_eq : ifp = GenContFract.IntFractPair.of
        (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) := by
      exact (Option.some_inj.mp h_s0).symm
    rw [h_ifp_eq] at h_fr
    -- h_fr : (intFractPair.of v).fr = 0 = fract v = 0.
    have h_fr_eq : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) = 0 := h_fr
    rw [Int.fract_div_natCast_eq_div_natCast_mod] at h_fr_eq
    -- h_fr_eq : (o % m : ℝ) / (m : ℝ) = 0
    have h_m_ne : ((m : Nat) : ℝ) ≠ 0 := by
      exact_mod_cast _h_m_pos.ne'
    have : ((o % m : Nat) : ℝ) = 0 := by
      field_simp at h_fr_eq
      linarith
    exact_mod_cast this

/-- **Converse direction: mathlib-terminated → Euclidean-terminated** (added
2026-05-24): when mathlib's CF terminates at step j for v=o/m (m > 0),
cf_aux's Euclidean iteration has hit `.2 = 0` by step j+1.

Proof: induction on j. Base via `mod_zero_of_terminated_at_0`. Succ uses
`cf_of_div_succ_step_R` to shift mathlib's view + IH at (m, o%m). -/
theorem eucl_terminated_of_mathlib_terminated (o m : Nat) (h_m_pos : 0 < m)
    (j : Nat) (h_term : (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt j) :
    (euclidean_iter (j+1) o m).2 = 0 := by
  induction j generalizing o m with
  | zero =>
    have h_om : o % m = 0 := mod_zero_of_terminated_at_0 o m h_m_pos h_term
    show (if m = 0 then (o, m) else euclidean_iter 0 m (o % m)).2 = 0
    rw [if_neg h_m_pos.ne']
    exact h_om
  | succ j' ih =>
    by_cases h_om : o % m = 0
    · -- o%m = 0: mathlib already terminated at 0, so euclidean_iter 1 hits 0.
      -- Use stability to extend.
      have h_eucl_1 : (euclidean_iter 1 o m).2 = 0 := by
        show (if m = 0 then (o, m) else euclidean_iter 0 m (o % m)).2 = 0
        rw [if_neg h_m_pos.ne']
        exact h_om
      have h_assoc : j' + 2 = 1 + (j' + 1) := by ring
      rw [h_assoc]
      exact eucl_iter_stable 1 o m (j' + 1) h_eucl_1
    · -- o%m > 0: shift via cf_of_div_succ_step_R + apply IH at (m, o%m).
      have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
      have h_term' : (GenContFract.of (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))).TerminatedAt j' := by
        rw [GenContFract.terminatedAt_iff_s_none] at h_term ⊢
        rw [← cf_of_div_succ_step_R o m j' h_om_pos]
        exact h_term
      have h_ih := ih m (o % m) h_om_pos h_term'
      -- h_ih : (euclidean_iter (j'+1) m (o%m)).2 = 0
      -- Need: (euclidean_iter (j'+2) o m).2 = 0
      have h_assoc : j' + 2 = (j' + 1) + 1 := by ring
      rw [h_assoc]
      show (if m = 0 then (o, m) else euclidean_iter (j' + 1) m (o % m)).2 = 0
      rw [if_neg h_m_pos.ne']
      exact h_ih

/-- **Mathlib-terminated ↔ Euclidean-terminated bridge** (added 2026-05-24):
when cf_aux's Euclidean iteration hits `.2 = 0` at step `j+1`, mathlib's
CF stream for `v = o/m` terminates at step `j`. This is the last piece
needed to close the terminated-case bridge in `TODO_non_div_terminated_stable`.

Proof: induction on `j`. The base case uses `terminated_at_0_when_mod_zero`.
The succ case shifts via `cf_of_div_succ_step_R` and applies IH at the
shifted Euclidean state. -/
theorem mathlib_terminated_of_eucl_terminated (o m : Nat) (h_m_pos : 0 < m)
    (j : Nat) (h_eucl : (euclidean_iter (j+1) o m).2 = 0) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt j := by
  induction j generalizing o m with
  | zero =>
    -- h_eucl : (euclidean_iter 1 o m).2 = (m, o%m).2 = o%m = 0 (since m > 0)
    have h_eucl_unfold : euclidean_iter 1 o m = (m, o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter 0 m (o%m)) = _
      rw [if_neg h_m_pos.ne']; rfl
    rw [h_eucl_unfold] at h_eucl
    -- h_eucl : o % m = 0
    exact terminated_at_0_when_mod_zero o m h_eucl
  | succ j' ih =>
    -- h_eucl : (euclidean_iter (j'+2) o m).2 = 0
    have h_assoc : j' + 2 = (j' + 1) + 1 := by ring
    rw [h_assoc] at h_eucl
    have h_unfold : euclidean_iter ((j' + 1) + 1) o m = euclidean_iter (j' + 1) m (o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter (j' + 1) m (o % m)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_unfold] at h_eucl
    -- h_eucl : (euclidean_iter (j'+1) m (o%m)).2 = 0
    by_cases h_om : o % m = 0
    · -- o%m = 0: TerminatedAt 0 + terminated_stable.
      have h_term_0 : (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0 :=
        terminated_at_0_when_mod_zero o m h_om
      exact GenContFract.terminated_stable (by omega : 0 ≤ j' + 1) h_term_0
    · -- o%m > 0: shift via cf_of_div_succ_step_R + apply IH.
      have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
      have h_ih := ih m (o % m) h_om_pos h_eucl
      -- h_ih : TerminatedAt j' for v' = m/(o%m).
      -- Want: TerminatedAt (j'+1) for v = o/m. Bridge via cf_of_div_succ_step_R.
      rw [GenContFract.terminatedAt_iff_s_none] at h_ih ⊢
      rw [cf_of_div_succ_step_R o m j' h_om_pos]
      exact h_ih

end FormalRV.SQIRPort
