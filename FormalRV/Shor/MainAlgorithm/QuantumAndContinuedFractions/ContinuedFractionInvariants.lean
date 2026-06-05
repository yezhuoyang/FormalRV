import FormalRV.Shor.MainAlgorithm.QuantumAndContinuedFractions.OrderAndContinuedFractionDefs

namespace FormalRV.SQIRPort

/-- **cf_aux_full's "step at end" expression** (added 2026-05-24): when the
Euclidean iteration hasn't terminated at step N (i.e., `.2 > 0`), one extra
iteration `cf_aux_full (N+1)` equals applying ONE cf_aux step to the output
of `cf_aux_full N`. The step's `a = oN/mN` where `(oN, mN) = euclidean_iter N o m`.

This is the "peel from end" lemma needed to extend bridges past the
non-terminated boundary in the terminated case of TODO_non_div_terminated_stable. -/
theorem cf_aux_full_succ_step :
    ∀ (N o m p_prev p_curr q_prev q_curr : Nat),
      0 < (euclidean_iter N o m).2 →
      cf_aux_full (N + 1) o m p_prev p_curr q_prev q_curr =
        let s := cf_aux_full N o m p_prev p_curr q_prev q_curr
        let oN := (euclidean_iter N o m).1
        let mN := (euclidean_iter N o m).2
        (s.2.1, (oN / mN) * s.2.1 + s.1, s.2.2.2, (oN / mN) * s.2.2.2 + s.2.2.1) := by
  intro N
  induction N with
  | zero =>
    intros o m p_prev p_curr q_prev q_curr h_eucl_pos
    -- h_eucl_pos : 0 < (eucl_iter 0 o m).2 = m. So m > 0.
    have h_m_pos : 0 < m := h_eucl_pos
    -- cf_aux_full 1 o m S = step S (since m > 0).
    -- cf_aux_full 0 o m S = S. step-at-end of S using (eucl_iter 0 o m) = (o, m).
    show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
          else cf_aux_full 0 m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                       q_curr ((o / m) * q_curr + q_prev))
        = (p_curr, (o / m) * p_curr + p_prev, q_curr, (o / m) * q_curr + q_prev)
    rw [if_neg h_m_pos.ne']
    rfl
  | succ N' ih =>
    intros o m p_prev p_curr q_prev q_curr h_eucl_pos
    -- h_eucl_pos : (eucl_iter (N'+1) o m).2 > 0.
    -- Need: m > 0 (else eucl_iter would be (o, m) with .2 = m).
    have h_m_pos : 0 < m := by
      by_contra h_m_zero
      push_neg at h_m_zero
      interval_cases m
      simp [euclidean_iter] at h_eucl_pos
    -- Unfold (eucl_iter (N'+1) o m) using m > 0.
    have h_eucl_shift : euclidean_iter (N' + 1) o m = euclidean_iter N' m (o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter N' m (o % m)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_eucl_shift] at h_eucl_pos
    -- h_eucl_pos : (eucl_iter N' m (o%m)).2 > 0.
    -- Apply IH at (m, o%m).
    have h_ih := ih m (o % m) p_curr ((o / m) * p_curr + p_prev)
                    q_curr ((o / m) * q_curr + q_prev) h_eucl_pos
    -- Unfold LHS via cf_aux_full's recursion.
    show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
          else cf_aux_full (N' + 1) m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                              q_curr ((o / m) * q_curr + q_prev))
        = _
    rw [if_neg h_m_pos.ne']
    -- Now LHS = cf_aux_full (N'+1) m (o%m) (mutated state).
    -- By IH: this = step-at-end of cf_aux_full N' m (o%m) (mutated state).
    rw [h_ih]
    -- Unfold RHS's cf_aux_full N+1 = cf_aux_full (N'+1+1) using its def at top level.
    -- Actually RHS = step-at-end of cf_aux_full (N'+1) o m S. And cf_aux_full (N'+1) o m S
    -- = cf_aux_full N' m (o%m) (mutated). So RHS step-at-end is on cf_aux_full N' m (o%m) (mutated).
    -- The (eucl_iter (N'+1) o m) = (eucl_iter N' m (o%m)) by h_eucl_shift. Same a value.
    show (let s := cf_aux_full N' m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                            q_curr ((o / m) * q_curr + q_prev)
          let oN := (euclidean_iter N' m (o % m)).1
          let mN := (euclidean_iter N' m (o % m)).2
          (s.2.1, oN / mN * s.2.1 + s.1, s.2.2.2, oN / mN * s.2.2.2 + s.2.2.1))
        = (let s := cf_aux_full (N' + 1) o m p_prev p_curr q_prev q_curr
           let oN := (euclidean_iter (N' + 1) o m).1
           let mN := (euclidean_iter (N' + 1) o m).2
           (s.2.1, oN / mN * s.2.1 + s.1, s.2.2.2, oN / mN * s.2.2.2 + s.2.2.1))
    -- Both sides have the same structure. Show that cf_aux_full N' m (o%m) (mutated)
    -- = cf_aux_full (N'+1) o m S, and the eucl_iters match by h_eucl_shift.
    have h_unfold : cf_aux_full (N' + 1) o m p_prev p_curr q_prev q_curr
        = cf_aux_full N' m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                   q_curr ((o / m) * q_curr + q_prev) := by
      show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
            else cf_aux_full N' m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                          q_curr ((o / m) * q_curr + q_prev)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_unfold]
    rw [h_eucl_shift]

/-- **cf_aux_full's output is invariant under extra depth, post-termination**
(added 2026-05-24): if there exists `j ≤ N` with `(euclidean_iter j o m).2 = 0`
(cf_aux's Euclidean reaches termination within `N` steps), then adding one
more depth (`N+1`) doesn't change the output.

Proof by induction on N, exploiting that cf_aux's `m = 0` guard returns the
state regardless of remaining depth. The IH at the shifted `(m, o%m)` state
uses the Euclidean shift: if j ≥ 1, then `(euclidean_iter j o m).2 = 0`
implies `(euclidean_iter (j-1) m (o%m)).2 = 0`. -/
theorem cf_aux_full_depth_invariant :
    ∀ N o m p_prev p_curr q_prev q_curr,
      (∃ j, j ≤ N ∧ (euclidean_iter j o m).2 = 0) →
      cf_aux_full (N + 1) o m p_prev p_curr q_prev q_curr
        = cf_aux_full N o m p_prev p_curr q_prev q_curr := by
  intro N
  induction N with
  | zero =>
    -- Condition: ∃ j ≤ 0 with (eucl_iter j o m).2 = 0 → j = 0 → m = 0.
    rintro o m p_prev p_curr q_prev q_curr ⟨j, h_le, h_eq⟩
    have h_j : j = 0 := by omega
    subst h_j
    -- h_eq : (eucl_iter 0 o m).2 = m = 0.
    have h_m : m = 0 := h_eq
    subst h_m
    -- cf_aux_full 1 o 0 = cf_aux_full 0 o 0 = state.
    show (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr) else _)
        = (p_prev, p_curr, q_prev, q_curr)
    rfl
  | succ N' ih =>
    rintro o m p_prev p_curr q_prev q_curr ⟨j, h_le, h_eq⟩
    by_cases h_m : m = 0
    · subst h_m
      -- m = 0: both sides return state via the m=0 guard.
      show (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr) else _)
          = (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr) else _)
      rfl
    · -- m > 0: unfold both sides, apply IH at (m, o%m, mutated state).
      have h_m_pos : 0 < m := Nat.pos_of_ne_zero h_m
      -- Derive condition for IH at (m, o%m): ∃ j' ≤ N', (eucl_iter j' m (o%m)).2 = 0.
      have h_j_pos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h_j0 | h_jp
        · subst h_j0
          -- h_eq : (eucl_iter 0 o m).2 = m = 0. Contradicts m > 0.
          exact absurd h_eq h_m
        · exact h_jp
      have h_eucl_shift : (euclidean_iter (j - 1) m (o % m)).2 = 0 := by
        have h_unfold : euclidean_iter j o m = euclidean_iter (j - 1) m (o % m) := by
          have h_j_eq : j = (j - 1) + 1 := by omega
          conv_lhs => rw [h_j_eq]
          show (if m = 0 then (o, m) else euclidean_iter (j - 1) m (o % m))
              = euclidean_iter (j - 1) m (o % m)
          rw [if_neg h_m]
        rw [h_unfold] at h_eq
        exact h_eq
      have h_ih_cond : ∃ j', j' ≤ N' ∧ (euclidean_iter j' m (o % m)).2 = 0 :=
        ⟨j - 1, by omega, h_eucl_shift⟩
      -- Unfold both sides.
      show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
            else cf_aux_full (N' + 1) m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                   q_curr ((o / m) * q_curr + q_prev))
          = (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
             else cf_aux_full N' m (o % m) p_curr ((o / m) * p_curr + p_prev)
                                   q_curr ((o / m) * q_curr + q_prev))
      rw [if_neg h_m, if_neg h_m]
      exact ih m (o % m) p_curr ((o / m) * p_curr + p_prev)
              q_curr ((o / m) * q_curr + q_prev) h_ih_cond

/-- **Euclidean iteration is monotone-terminating** (added 2026-05-24):
once `(euclidean_iter j o m).2 = 0` (cf_aux's m_arg hit 0 at step j),
the iteration stays terminated at all subsequent steps `j + k`. Proven by
induction on `j` with universal quantification over `o` and `m` (allowing
the inductive hypothesis to apply to the shifted state `(m, o%m)`). -/
theorem eucl_iter_stable :
    ∀ (j : Nat) (o m k : Nat),
      (euclidean_iter j o m).2 = 0 → (euclidean_iter (j + k) o m).2 = 0 := by
  intro j
  induction j with
  | zero =>
    intros o m k h
    -- h : (euclidean_iter 0 o m).2 = m = 0
    have h_m : m = 0 := h
    subst h_m
    -- Need: (euclidean_iter k o 0).2 = 0
    induction k with
    | zero => rfl
    | succ k' _ =>
      show (if (0 : Nat) = 0 then (o, 0) else _).2 = 0
      rfl
  | succ j' ih =>
    intros o m k h
    by_cases h_m : m = 0
    · -- m = 0: subst and recurse.
      subst h_m
      induction k with
      | zero => exact h
      | succ k' _ =>
        show (if (0 : Nat) = 0 then (o, 0) else _).2 = 0
        rfl
    · -- m > 0: unfold via the (n+1) pattern at both ends, apply ih.
      have h_unfold_lhs : euclidean_iter (j' + 1) o m = euclidean_iter j' m (o % m) := by
        show (if m = 0 then (o, m) else euclidean_iter j' m (o % m)) = _
        rw [if_neg h_m]
      rw [h_unfold_lhs] at h
      -- h : (euclidean_iter j' m (o%m)).2 = 0
      have h_succ : (euclidean_iter (j' + k) m (o % m)).2 = 0 := ih m (o % m) k h
      -- Target: (euclidean_iter (j' + 1 + k) o m).2 = 0
      have h_assoc : j' + 1 + k = (j' + k) + 1 := by ring
      rw [h_assoc]
      show (if m = 0 then (o, m) else euclidean_iter (j' + k) m (o % m)).2 = 0
      rw [if_neg h_m]
      exact h_succ

/-- **Structural insight for the joint induction succ case** (Phase 3
r_found_1, documentation tick 76):

The cf_aux_full recursion `(p_prev, p_curr) → (p_curr, a · p_curr + p_prev)`
EXACTLY mirrors mathlib's `conts_recurrence`:
`conts (n+2) = ⟨b · (conts (n+1)).a + a · (conts n).a, ...⟩` with `a = 1`
for SimpContFract.of (i.e., `GenContFract.of`).

The matching: cf_aux's `a` parameter at iteration k = mathlib's `b_k`
(the k-th partial denominator). cf_aux's state (p_prev, p_curr, q_prev,
q_curr) at iteration k = mathlib's (conts(k-1), conts(k)) for v = original
o/m.

**To make the joint induction work**, the invariant needs to be stated in
the most general form: for ANY state and ANY Euclidean shift of the
inputs, cf_aux's K-step result matches mathlib's contsAux applied K times
from the corresponding mathlib starting state. This is the form that
makes induction on K succeed.

**Formalization is multi-tick**: requires (a) stating the predicate
"cf_aux state matches mathlib at offset k for v" precisely, (b) proving
this predicate is preserved under one cf_aux_full step, (c) showing the
initial state (0, 1, 1, 0) at (o, m) matches mathlib at offset "before
the first step", which after one cf_aux iteration becomes offset 0. -/
def cf_aux_general_invariant_intent : Prop := True  -- design docs

/-- **Derive `o % m ≠ 0` from non-termination at step 0** (Phase 3
r_found_1 base case prep, added 2026-05-24 tick 73): when
`GenContFract.of (o/m)` is not terminated at step 0 (i.e., the stream
hasn't ended), the fractional part is non-zero, which for `v = o/m`
means `o % m ≠ 0`. -/
theorem nondiv_of_not_terminated_zero (o m : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0) :
    o % m ≠ 0 := by
  intro h_mod
  apply h_not_term
  rw [GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none]
  have h_stream_0 : GenContFract.IntFractPair.stream
      (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 0
      = some (GenContFract.IntFractPair.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) := rfl
  apply GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero h_stream_0
  show Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) = 0
  rw [Int.fract_div_natCast_eq_div_natCast_mod, h_mod]
  simp

-- (cf_aux_full_matches_mathlib_zero moved later — depends on mathlib_*_eq_* defs.)
-- (The old scaffold `TODO_cf_aux_full_matches_mathlib` was deleted 2026-05-24 —
--  superseded by the proven `cf_aux_full_matches_mathlib_strong` after the
--  general bridge invariant landed.)

end FormalRV.SQIRPort
