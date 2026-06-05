import FormalRV.Shor.MainAlgorithm.ContinuedFractionBridge.EuclideanTerminationEquivalence

namespace FormalRV.SQIRPort

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
