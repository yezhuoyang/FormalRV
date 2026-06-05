import FormalRV.Shor.MainAlgorithm.ContinuedFractionBridge.MathlibOFPostStepAndDenominators

namespace FormalRV.SQIRPort

/-- **n=0 base case of the joint state-tracking invariant** (Phase 3
r_found_1, added 2026-05-24 tick 73): when `m > 0` and the CF isn't
terminated at step 0, cf_aux_full's depth-2 state matches mathlib's
(nums 0, nums 1, dens 0, dens 1). Combines `cf_aux_full_2_nondiv` (LHS
explicit value) with the four mathlib step-0/step-1 helpers. -/
theorem cf_aux_full_matches_mathlib_zero (o m : Nat) (h_m_pos : 0 < m)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0) :
    (GenContFract.of ((o : ℝ) / m)).nums 0 = (((cf_aux_full 2 o m 0 1 1 0).1 : Nat) : ℝ) ∧
    (GenContFract.of ((o : ℝ) / m)).nums 1 = (((cf_aux_full 2 o m 0 1 1 0).2.1 : Nat) : ℝ) ∧
    (GenContFract.of ((o : ℝ) / m)).dens 0 = (((cf_aux_full 2 o m 0 1 1 0).2.2.1 : Nat) : ℝ) ∧
    (GenContFract.of ((o : ℝ) / m)).dens 1 = (((cf_aux_full 2 o m 0 1 1 0).2.2.2 : Nat) : ℝ) := by
  have h_mod : o % m ≠ 0 := nondiv_of_not_terminated_zero o m h_not_term
  have h_cast : ((o : ℝ) / m) = (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) := by push_cast; rfl
  rw [cf_aux_full_2_nondiv o m h_m_pos h_mod]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_cast]; exact mathlib_nums_zero_eq o m h_m_pos
  · rw [h_cast]; exact mathlib_nums_one_eq_nondiv o m h_m_pos h_mod
  · rw [h_cast, mathlib_dens_zero_eq]; simp
  · rw [h_cast]; exact mathlib_dens_one_eq_nondiv o m h_m_pos h_mod

/-- **Parametric general bridge invariant** (Phase 3 r_found_1, added
2026-05-24 by direction "focus on Legendre_ContinuedFraction sorries"):
The CRUX of the cf_aux ↔ mathlib bridge.

For any `n`, any current cf_aux Euclidean state `(o, m)` (with `m > 0`),
and any initial cf_aux_full state `(p_prev, p_curr, q_prev, q_curr)`
matching mathlib's `contsAux` at indices `(K, K+1)` for some `v0`, and
provided the Euclidean iteration of `(o, m)` produces the right partial
denominators `b_K, b_{K+1}, ...` of `v0`'s continued fraction, then after
`n` cf_aux steps the state matches mathlib's `contsAux` at `(K+n, K+n+1)`.

This is the GENERAL form that subsumes the specific-initial-state versions.
The succ case proof uses `contsAux_recurrence` (mathlib) and `cf_aux_succ_pos`
(local) — they have STRUCTURALLY identical recurrences modulo a Nat ↔ ℝ cast.

Succ case is the SINGLE remaining cf_aux ↔ mathlib structural sorry. -/
theorem cf_aux_full_general_match
    (n : Nat) (o m : Nat) (h_m_pos : 0 < m)
    (v0 : ℝ) (K : Nat)
    (p_prev p_curr q_prev q_curr : Nat)
    (h_state :
      ((p_prev : ℝ) = ((GenContFract.of v0).contsAux K).a) ∧
      ((p_curr : ℝ) = ((GenContFract.of v0).contsAux (K+1)).a) ∧
      ((q_prev : ℝ) = ((GenContFract.of v0).contsAux K).b) ∧
      ((q_curr : ℝ) = ((GenContFract.of v0).contsAux (K+1)).b))
    (_h_eucl : ∀ i : ℕ, ¬ (GenContFract.of v0).TerminatedAt (K + i) →
      (GenContFract.of v0).s.get? (K + i) =
        some ⟨1, (((euclidean_iter i o m).1 / (euclidean_iter i o m).2 : Nat) : ℝ)⟩)
    (_h_not_term : ¬ (GenContFract.of v0).TerminatedAt (K + n)) :
    (((cf_aux_full n o m p_prev p_curr q_prev q_curr).1 : Nat) : ℝ)
        = ((GenContFract.of v0).contsAux (K + n)).a ∧
    (((cf_aux_full n o m p_prev p_curr q_prev q_curr).2.1 : Nat) : ℝ)
        = ((GenContFract.of v0).contsAux (K + n + 1)).a ∧
    (((cf_aux_full n o m p_prev p_curr q_prev q_curr).2.2.1 : Nat) : ℝ)
        = ((GenContFract.of v0).contsAux (K + n)).b ∧
    (((cf_aux_full n o m p_prev p_curr q_prev q_curr).2.2.2 : Nat) : ℝ)
        = ((GenContFract.of v0).contsAux (K + n + 1)).b := by
  induction n generalizing o m p_prev p_curr q_prev q_curr K with
  | zero =>
    -- n=0: cf_aux_full 0 returns the initial state directly; h_state matches.
    simp only [cf_aux_full, Nat.add_zero]
    exact ⟨h_state.1, h_state.2.1, h_state.2.2.1, h_state.2.2.2⟩
  | succ k ih =>
    -- Step 1: Unfold cf_aux_full (k+1) o m (...) using m > 0.
    rw [show cf_aux_full (k+1) o m p_prev p_curr q_prev q_curr
          = cf_aux_full k m (o%m) p_curr ((o/m)*p_curr + p_prev)
                                  q_curr ((o/m)*q_curr + q_prev) from by
      show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
            else cf_aux_full k m (o%m) p_curr ((o/m)*p_curr + p_prev)
                                       q_curr ((o/m)*q_curr + q_prev)) = _
      rw [if_neg h_m_pos.ne']]
    -- Step 2: Case split on o%m. If 0, mathlib terminates at K+1 contradicting
    -- h_not_term at K+k+1 ≥ K+1 (assuming k can be anything; but we still need
    -- to prove this rigorously, hence the sub-sorry). If > 0, apply IH at k
    -- with shifted parameters.
    by_cases h_om : o % m = 0
    · -- o%m = 0: derive contradiction.
      -- Strategy: case split on Terminated at (K+1).
      -- - If Terminated: by terminated_stable + K+1 ≤ K+(k+1), contradicts h_not_term.
      -- - If ¬ Terminated: h_eucl @ 1 forces s.get? (K+1) = some ⟨1, m/0 = 0⟩.
      --   But mathlib's IntFractPair.one_le_succ_nth_stream_b says b ≥ 1. Contradiction.
      exfalso
      by_cases h_term_K1 : (GenContFract.of v0).TerminatedAt (K + 1)
      · -- Case 1: Terminated at K+1 → Terminated at K+(k+1) by stable → contradicts h_not_term.
        apply _h_not_term
        exact GenContFract.terminated_stable (by omega : K + 1 ≤ K + (k + 1)) h_term_K1
      · -- Case 2: ¬ Terminated at K+1 → derive impossible stream value.
        have h_eucl_1 := _h_eucl 1 (by
          show ¬ (GenContFract.of v0).TerminatedAt (K + 1)
          have : K + 1 = K + 1 := rfl
          exact h_term_K1)
        -- h_eucl_1 : s.get? (K+1) = some ⟨1, ((euclidean_iter 1 o m).1 / .2 : Nat) : ℝ⟩.
        -- With o%m = 0 and m > 0: euclidean_iter 1 o m = (m, 0), quotient = m/0 = 0.
        have h_iter_1 : euclidean_iter 1 o m = (m, 0) := by
          show (if m = 0 then (o, m) else euclidean_iter 0 m (o%m)) = _
          rw [if_neg h_m_pos.ne', h_om]
          rfl
        rw [h_iter_1] at h_eucl_1
        simp at h_eucl_1
        -- h_eucl_1 : s.get? (K+1) = some ⟨1, 0⟩.
        -- Extract: ∃ ifp, stream v0 (K+2) = some ifp ∧ ↑ifp.b = 0.
        obtain ⟨ifp, h_stream, h_b_eq⟩ :=
          GenContFract.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some h_eucl_1
        -- h_b_eq : (↑ifp.b : ℝ) = (⟨1, 0⟩ : GenContFract.Pair ℝ).b
        simp only [show ((⟨1, 0⟩ : GenContFract.Pair ℝ).b) = (0 : ℝ) from rfl] at h_b_eq
        have h_ifp_b_zero : ifp.b = 0 := by exact_mod_cast h_b_eq
        -- Mathlib: stream v (n+1) = some ifp → 1 ≤ ifp.b. Contradiction.
        have h_one_le := GenContFract.IntFractPair.one_le_succ_nth_stream_b h_stream
        omega
    · -- o%m > 0: apply IH with new (o', m') := (m, o%m), K' := K+1.
      have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
      -- Step (a): get s.get? K from h_eucl at i=0.
      have h_K_lt : K ≤ K + (k+1) := by omega
      have h_not_term_K : ¬ (GenContFract.of v0).TerminatedAt K := fun h =>
        _h_not_term (GenContFract.terminated_stable h_K_lt h)
      have h_eucl_0 := _h_eucl 0 h_not_term_K
      -- Simplify euclidean_iter 0 o m = (o, m).
      have h_iter_0 : euclidean_iter 0 o m = (o, m) := rfl
      rw [Nat.add_zero, h_iter_0] at h_eucl_0
      -- h_eucl_0 : s.get? K = some ⟨1, ((o/m : Nat) : ℝ)⟩
      -- Step (b): compute contsAux (K+2) via contsAux_recurrence with gp := ⟨1, o/m⟩.
      have h_contsAux_K : (GenContFract.of v0).contsAux K = ⟨(p_prev : ℝ), (q_prev : ℝ)⟩ :=
        GenContFract.Pair.mk.injEq .. |>.mpr ⟨h_state.1.symm, h_state.2.2.1.symm⟩
      have h_contsAux_K1 : (GenContFract.of v0).contsAux (K + 1) =
          ⟨(p_curr : ℝ), (q_curr : ℝ)⟩ :=
        GenContFract.Pair.mk.injEq .. |>.mpr ⟨h_state.2.1.symm, h_state.2.2.2.symm⟩
      have h_contsAux_K2 := GenContFract.contsAux_recurrence
        (g := GenContFract.of v0) (n := K) h_eucl_0 h_contsAux_K h_contsAux_K1
      -- h_contsAux_K2 : contsAux (K+2) = ⟨(o/m)·p_curr + 1·p_prev, (o/m)·q_curr + 1·q_prev⟩
      -- Step (c): build h_eucl' for new (m, o%m) at K+1, via h_eucl@(i+1).
      have h_eucl' : ∀ i : ℕ, ¬ (GenContFract.of v0).TerminatedAt (K + 1 + i) →
          (GenContFract.of v0).s.get? (K + 1 + i) =
            some ⟨1, (((euclidean_iter i m (o%m)).1 / (euclidean_iter i m (o%m)).2 : Nat) : ℝ)⟩ := by
        intros i h_nt
        have h_shift : K + 1 + i = K + (i + 1) := by ring
        rw [h_shift] at h_nt ⊢
        have h := _h_eucl (i+1) h_nt
        -- euclidean_iter (i+1) o m = euclidean_iter i m (o%m) (since m > 0).
        have h_iter_shift : euclidean_iter (i+1) o m = euclidean_iter i m (o%m) := by
          show (if m = 0 then (o, m) else euclidean_iter i m (o%m)) = euclidean_iter i m (o%m)
          rw [if_neg h_m_pos.ne']
        rw [h_iter_shift] at h
        exact h
      -- Step (d): build h_not_term' at K+1+k = K+(k+1).
      have h_not_term' : ¬ (GenContFract.of v0).TerminatedAt (K + 1 + k) := by
        have : K + 1 + k = K + (k + 1) := by ring
        rw [this]; exact _h_not_term
      -- Step (e): build h_state' for new state.
      have h_state' :
          (((p_curr : Nat) : ℝ) = ((GenContFract.of v0).contsAux (K+1)).a) ∧
          ((((o/m)*p_curr + p_prev : Nat) : ℝ) = ((GenContFract.of v0).contsAux (K+1+1)).a) ∧
          (((q_curr : Nat) : ℝ) = ((GenContFract.of v0).contsAux (K+1)).b) ∧
          ((((o/m)*q_curr + q_prev : Nat) : ℝ) = ((GenContFract.of v0).contsAux (K+1+1)).b) := by
        refine ⟨h_state.2.1, ?_, h_state.2.2.2, ?_⟩
        · -- ((o/m)*p_curr + p_prev : Nat) : ℝ = contsAux (K+2) .a
          have : K + 1 + 1 = K + 2 := by ring
          rw [this, h_contsAux_K2]
          push_cast; ring
        · -- ((o/m)*q_curr + q_prev : Nat) : ℝ = contsAux (K+2) .b
          have : K + 1 + 1 = K + 2 := by ring
          rw [this, h_contsAux_K2]
          push_cast; ring
      -- Apply IH.
      have h_apply :=
        ih m (o%m) h_om_pos (K+1) p_curr ((o/m)*p_curr + p_prev) q_curr ((o/m)*q_curr + q_prev)
            h_state' h_eucl' h_not_term'
      -- Goal: cf_aux_full k m (o%m) ... matches contsAux at (K+(k+1), K+(k+1)+1).
      -- IH gives matching at (K+1+k, K+1+k+1). Just rewrite K+(k+1) → K+1+k.
      have h_idx : K + (k + 1) = K + 1 + k := by ring
      rw [h_idx]
      exact h_apply

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

/-- **Eucl iter ↔ mathlib stream correspondence** (added 2026-05-24):
For `v = o/m` with `m > 0`, mathlib's `s.get? i = some ⟨1, x⟩` where
`x = quotient of the (i+1)-th Euclidean iterate of (o, m)`. By induction
on i using `cf_of_div_succ_step_R` and the i=0 case from `of_s_head` +
floor computations.

This is the `h_eucl` hypothesis the general lemma needs, computed for the
specific case where v0 = o/m and the cf_aux call uses (m, o%m) as initial
Euclidean state. -/
theorem eucl_iter_match_stream (o m : Nat) (h_m_pos : 0 < m) (i : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt i) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.get? i =
      some ⟨1, (((euclidean_iter (i+1) o m).1 / (euclidean_iter (i+1) o m).2 : Nat) : ℝ)⟩ := by
  induction i generalizing o m with
  | zero =>
    -- Base case: s.get? 0 = some ⟨1, ⌊1/Int.fract v⌋⟩ via of_s_head.
    -- ¬ Terminated at 0 → o%m ≠ 0 → fract v ≠ 0 → use of_s_head.
    have h_om : o % m ≠ 0 := nondiv_of_not_terminated_zero o m h_not_term
    have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
    have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
    have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) ≠ 0 := by
      rw [Int.fract_div_natCast_eq_div_natCast_mod]
      have h_num_pos : (0 : ℝ) < ((o % m : Nat) : ℝ) := by exact_mod_cast h_om_pos
      positivity
    have h_head := GenContFract.of_s_head (K := ℝ)
      (v := (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))) h_fract_ne
    -- h_head : s.head = some ⟨1, ⌊(Int.fract v)⁻¹⌋⟩
    rw [show (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.get? 0
         = (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.head from rfl,
        h_head]
    congr 2
    -- Goal: ⌊(Int.fract (o/m))⁻¹⌋ = ((euclidean_iter 1 o m).1 / .2 : Nat) : ℝ
    have h_iter_1 : (euclidean_iter 1 o m) = (m, o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter 0 m (o%m)) = _
      rw [if_neg h_m_pos.ne']; rfl
    rw [h_iter_1]
    -- Goal: ↑⌊(Int.fract (o/m))⁻¹⌋ = ((m / (o%m) : Nat) : ℝ)
    rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
    -- Goal: ↑⌊(m : ℝ) / (o%m : ℝ)⌋ = ((m / (o%m) : Nat) : ℝ)
    have h_eq : (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))
              = ((((m : Nat) : ℚ) / ((o % m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
    rw [h_eq, Rat.floor_cast, Rat.floor_natCast_div_natCast]
    push_cast; rfl
  | succ j ih =>
    -- Inductive case: use cf_of_div_succ_step_R to shift to (m, o%m), apply IH.
    -- Need ¬ Terminated at j+1 for v=o/m. By stream_succ_eq_none_iff, if Terminated at 0
    -- (o%m = 0), then Terminated at j+1 too. So ¬ Terminated at j+1 → o%m ≠ 0.
    have h_om : o % m ≠ 0 := by
      intro h
      apply h_not_term
      apply GenContFract.terminated_stable (by omega : 0 ≤ j + 1)
      -- Show TerminatedAt 0 for v=o/m when o%m = 0.
      rw [GenContFract.terminatedAt_iff_s_none]
      -- s.get? 0 = none. Use of_s_head_aux + stream_eq_none_of_fr_eq_zero.
      have h_fract_eq : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) = 0 := by
        rw [Int.fract_div_natCast_eq_div_natCast_mod, h]
        simp
      have h_stream_none : GenContFract.IntFractPair.stream
          (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 1 = none :=
        GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero (n := 0) rfl h_fract_eq
      rw [GenContFract.of_s_head_aux, h_stream_none]
      rfl
    have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
    -- Shift: s.get? (j+1) for o/m = s.get? j for m/(o%m).
    rw [cf_of_div_succ_step_R o m j h_om_pos]
    -- Apply IH at (m, o%m) at index j.
    have h_not_term_shifted :
        ¬ (GenContFract.of (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))).TerminatedAt j := by
      intro h_term
      apply h_not_term
      -- TerminatedAt at j+1 for o/m ↔ s.get? (j+1) for o/m = none.
      rw [GenContFract.terminatedAt_iff_s_none] at h_term ⊢
      rw [cf_of_div_succ_step_R o m j h_om_pos]
      exact h_term
    have h_ih := ih m (o%m) h_om_pos h_not_term_shifted
    rw [h_ih]
    congr 2
    -- Goal: euclidean_iter (j+1) m (o%m) = euclidean_iter (j+2) o m.
    have h_shift : euclidean_iter (j+2) o m = euclidean_iter (j+1) m (o%m) := by
      show (if m = 0 then (o, m) else euclidean_iter (j+1) m (o%m)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_shift]

/-- **`cf_aux_full_matches_mathlib_strong`** (Phase 3 r_found_1, added
2026-05-24 via bridge-consolidation tick): cf_aux_full's depth-(n+2) output
on `(o, m, 0, 1, 1, 0)` matches mathlib's `(nums n, nums (n+1), dens n,
dens (n+1))` for `v = o/m`.

Hypothesis: `¬ Terminated at (n+1)` (stronger than the weaker variant — this
makes the proof go through cleanly via the general lemma without needing
case analysis on whether matlibs's CF terminates exactly at n+1).

Proof: peel off Stage A's first cf_aux step (uses m > 0); state matches
`contsAux 0/1` for v = o/m; apply `cf_aux_full_general_match` at K=0, depth
n+1, with `eucl_iter_match_stream` providing h_eucl. -/
theorem cf_aux_full_matches_mathlib_strong (o m : Nat) (h_m_pos : 0 < m)
    (n : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt (n+1)) :
    (((cf_aux_full (n+2) o m 0 1 1 0).1 : Nat) : ℝ) =
        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (n+1)).a ∧
    (((cf_aux_full (n+2) o m 0 1 1 0).2.1 : Nat) : ℝ) =
        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (n+2)).a ∧
    (((cf_aux_full (n+2) o m 0 1 1 0).2.2.1 : Nat) : ℝ) =
        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (n+1)).b ∧
    (((cf_aux_full (n+2) o m 0 1 1 0).2.2.2 : Nat) : ℝ) =
        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (n+2)).b := by
  -- Stage A peel: cf_aux_full (n+2) o m 0 1 1 0 = cf_aux_full (n+1) m (o%m) 1 (o/m) 0 1.
  have h_peel : cf_aux_full (n+2) o m 0 1 1 0
      = cf_aux_full (n+1) m (o%m) 1 (o/m) 0 1 := by
    show (if m = 0 then _ else cf_aux_full (n+1) m (o%m) 1 ((o/m)*1+0) 0 ((o/m)*0+1)) = _
    rw [if_neg h_m_pos.ne']
    simp [Nat.mul_zero, Nat.mul_one]
  rw [h_peel]
  -- Apply general lemma. v0 := o/m, K := 0, (o', m') := (m, o%m), n' := n+1.
  -- Need: m' = o%m > 0. Derive from ¬ Terminated at (n+1) → ¬ Terminated at 0 → o%m > 0.
  have h_not_term_0 : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0 :=
    fun h => h_not_term (GenContFract.terminated_stable (by omega : 0 ≤ n+1) h)
  have h_om : o % m ≠ 0 := nondiv_of_not_terminated_zero o m h_not_term_0
  have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
  -- Build h_state: initial state (1, o/m, 0, 1) matches contsAux 0/1 for v=o/m.
  have h_zero_contsAux : ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 0).a = 1 ∧
                        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 0).b = 0 := by
    rw [GenContFract.zeroth_contAux_eq_one_zero]; exact ⟨rfl, rfl⟩
  -- contsAux 1 = ⟨h, 1⟩ where h = ⌊v⌋ = o/m (Nat-div).
  have h_one_contsAux_a : ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).a
                          = ((o / m : Nat) : ℝ) := by
    -- Use nth_cont_eq_succ_nth_contAux + zeroth_num_eq_h equivalent reasoning.
    -- Actually mathlib_nums_zero_eq gives nums 0 = o/m as ℝ.
    have := mathlib_nums_zero_eq o m h_m_pos
    -- nums 0 = (g.contsAux 1).a (by definitions). So we can rewrite.
    show ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).a
       = ((o / m : Nat) : ℝ)
    rw [show ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).a
         = (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).nums 0 from rfl]
    exact this
  have h_one_contsAux_b : ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).b
                          = 1 := by
    show ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).b = 1
    rw [show ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).b
         = (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).dens 0 from rfl]
    exact GenContFract.zeroth_den_eq_one
  have h_state :
      (((1 : Nat) : ℝ) = ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 0).a) ∧
      ((((o/m : Nat) : ℝ)) = ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (0+1)).a) ∧
      (((0 : Nat) : ℝ) = ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 0).b) ∧
      (((1 : Nat) : ℝ) = ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (0+1)).b) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_zero_contsAux.1]; push_cast; rfl
    · rw [h_one_contsAux_a]
    · rw [h_zero_contsAux.2]; push_cast; rfl
    · rw [h_one_contsAux_b]; push_cast; rfl
  -- Build h_eucl: at iter i ¬ Terminated at i → s.get? i = some ⟨1, eucl_iter i m (o%m)⟩.
  have h_eucl : ∀ i : ℕ,
      ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt (0 + i) →
      (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.get? (0 + i) =
        some ⟨1, (((euclidean_iter i m (o%m)).1 / (euclidean_iter i m (o%m)).2 : Nat) : ℝ)⟩ := by
    intros i h_nt
    rw [Nat.zero_add] at h_nt ⊢
    rw [eucl_iter_match_stream o m h_m_pos i h_nt]
    -- Goal: some ⟨1, ↑((euclidean_iter (i+1) o m).1/.2)⟩ = some ⟨1, ↑((euclidean_iter i m (o%m)).1/.2)⟩
    have h_shift : euclidean_iter (i+1) o m = euclidean_iter i m (o%m) := by
      show (if m = 0 then (o, m) else euclidean_iter i m (o%m))
          = euclidean_iter i m (o%m)
      rw [if_neg h_m_pos.ne']
    rw [h_shift]
  -- Apply general lemma.
  have h_not_term' : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt (0 + (n+1)) := by
    rw [Nat.zero_add]; exact h_not_term
  have h_general := cf_aux_full_general_match (n+1) m (o%m) h_om_pos
    (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 0 1 (o/m) 0 1 h_state h_eucl h_not_term'
  -- h_general's RHS uses index `0 + (n+1)` and `0 + (n+1) + 1`. Simplify.
  rw [Nat.zero_add] at h_general
  exact h_general

end FormalRV.SQIRPort
