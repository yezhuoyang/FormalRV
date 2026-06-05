import FormalRV.Shor.MainAlgorithm.ContinuedFractionBridge.MathlibDenominators


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

end FormalRV.SQIRPort
