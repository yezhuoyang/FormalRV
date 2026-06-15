/-
  FormalRV.Arithmetic.RippleCarryAdder.DecideWitnesses.ReverseFramesAndHeadline
  BACKBONE (part 4/4): per-step + cascade reverse frame conditions, the
  cascade-equals-first-reverse-on-low lemmas, THE headline j=0 / j=1 cases
  (`gidney_classical_action_with_reverse_target_0/_1`), and the
  propagation-reverse-at-target reduces-to-interior-reverse assembly lemma.
  Builds on `ReverseStepScaffold`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.DecideWitnesses.ReverseStepScaffold

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-! ### Per-step reverse cascade frame conditions (Iter 200, 2026-05-13)

    Each per-step reverse touches a fixed set of positions:
    - `gidney_first_bit_reverse_post_state` modifies {t_1, r_1, c_0}.
    - `gidney_interior_bit_reverse_post_state i` modifies {t_{i+1}, r_{i+1}, c_i}.
    - `gidney_last_bit_reverse_post_state i` modifies only {c_i}.

    Key frame: `target_idx 0` is NEVER touched by any per-step reverse
    (provided i ≥ 1 for last/interior). This means the post-full-reverse
    `target_0` equals the post-final-CX `target_0` = `a_0 ⊕ b_0` =
    `sum_0` (since c_0 math = 0). This is the trivial half of the
    headline (target_0 = sum_0). -/

/-- **First-bit reverse preserves target_0** (Iter 200).
    The first-bit reverse modifies {t_1, r_1, c_0}; not target_idx 0
    (= position 1, distinct from target_idx 1 = position 4). -/
theorem gidney_first_bit_reverse_preserves_target_0 (f : Nat → Bool) :
    gidney_first_bit_reverse_post_state f (target_idx 0) = f (target_idx 0) := by
  have h_t0_t1 : target_idx 0 ≠ target_idx 1 := by unfold target_idx; omega
  have h_t0_r1 : target_idx 0 ≠ read_idx 1 := by unfold target_idx read_idx; omega
  have h_t0_c0 : target_idx 0 ≠ carry_idx 0 := by unfold target_idx carry_idx; omega
  unfold gidney_first_bit_reverse_post_state
  rw [update_neq _ _ _ _ h_t0_c0, update_neq _ _ _ _ h_t0_r1,
      update_neq _ _ _ _ h_t0_t1]

/-- **Interior-bit reverse preserves target_0** for `i ≥ 1`. The
    interior reverse at i modifies {t_{i+1}, r_{i+1}, c_i, c_i};
    target_0 is distinct from all of these for i ≥ 1. -/
theorem gidney_interior_bit_reverse_preserves_target_0
    (i : Nat) (hi : 0 < i) (f : Nat → Bool) :
    gidney_interior_bit_reverse_post_state i f (target_idx 0) = f (target_idx 0) := by
  have h_t0_ti1 : target_idx 0 ≠ target_idx (i + 1) := by unfold target_idx; omega
  have h_t0_ri1 : target_idx 0 ≠ read_idx (i + 1) := by unfold target_idx read_idx; omega
  have h_t0_ci  : target_idx 0 ≠ carry_idx i := by unfold target_idx carry_idx; omega
  unfold gidney_interior_bit_reverse_post_state
  rw [update_neq _ _ _ _ h_t0_ci, update_neq _ _ _ _ h_t0_ci,
      update_neq _ _ _ _ h_t0_ri1, update_neq _ _ _ _ h_t0_ti1]

/-- **Last-bit reverse preserves target_0** for `i ≥ 1`. -/
theorem gidney_last_bit_reverse_preserves_target_0
    (i : Nat) (hi : 0 < i) (f : Nat → Bool) :
    gidney_last_bit_reverse_post_state i f (target_idx 0) = f (target_idx 0) := by
  have h_t0_ci : target_idx 0 ≠ carry_idx i := by unfold target_idx carry_idx; omega
  unfold gidney_last_bit_reverse_post_state
  rw [update_neq _ _ _ _ h_t0_ci, update_neq _ _ _ _ h_t0_ci]

/-- **Propagation reverse cascade preserves target_0**. By induction
    on `K` over the propagation_reverse_post_state def (which only
    invokes first/interior reverses, all of which preserve target_0). -/
theorem gidney_propagation_reverse_preserves_target_0
    (K : Nat) (f : Nat → Bool) :
    gidney_propagation_reverse_post_state K f (target_idx 0) = f (target_idx 0) := by
  induction K generalizing f with
  | zero => rfl
  | succ k ih =>
      match k with
      | 0 => exact gidney_first_bit_reverse_preserves_target_0 f
      | m + 1 =>
          show gidney_propagation_reverse_post_state (m + 1)
                (gidney_interior_bit_reverse_post_state (m + 1) f) (target_idx 0)
              = f (target_idx 0)
          rw [ih]
          exact gidney_interior_bit_reverse_preserves_target_0 (m + 1) (by omega) f

/-- **Full reverse cascade preserves target_0**. For `n ≥ 2`, the full
    reverse cascade applies last_reverse(n-1) + propagation_reverse(n-1);
    both preserve target_0. -/
theorem gidney_full_reverse_preserves_target_0 (n : Nat) (f : Nat → Bool) :
    gidney_full_reverse_post_state n f (target_idx 0) = f (target_idx 0) := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | m + 2 =>
      show gidney_propagation_reverse_post_state (m + 1)
            (gidney_last_bit_reverse_post_state (m + 1) f) (target_idx 0)
          = f (target_idx 0)
      rw [gidney_propagation_reverse_preserves_target_0,
          gidney_last_bit_reverse_preserves_target_0 (m + 1) (by omega) f]

/-- **Interior-bit reverse frame condition** (Iter 206). Positions
    other than {c_i, r_{i+1}, t_{i+1}} are unchanged. Generic frame
    analog of Iter 173's forward interior-step frame. -/
theorem gidney_interior_bit_reverse_post_state_preserves_outside
    (i : Nat) (f : Nat → Bool) (q : Nat)
    (h_ci : q ≠ carry_idx i)
    (h_ri1 : q ≠ read_idx (i + 1))
    (h_ti1 : q ≠ target_idx (i + 1)) :
    gidney_interior_bit_reverse_post_state i f q = f q := by
  unfold gidney_interior_bit_reverse_post_state
  rw [update_neq _ _ _ _ h_ci, update_neq _ _ _ _ h_ci,
      update_neq _ _ _ _ h_ri1, update_neq _ _ _ _ h_ti1]

/-- **Interior-bit reverse preserves low positions** (Iter 206). For
    i ≥ 1 and q < 5, the interior reverse modifies indices ≥ 5 only. -/
theorem gidney_interior_bit_reverse_preserves_low
    (i : Nat) (hi : 0 < i) (q : Nat) (hq : q < 5) (f : Nat → Bool) :
    gidney_interior_bit_reverse_post_state i f q = f q :=
  gidney_interior_bit_reverse_post_state_preserves_outside i f q
    (by unfold carry_idx; omega)
    (by unfold read_idx; omega)
    (by unfold target_idx; omega)

/-- **First-bit reverse depends only on inputs at low positions**
    (Iter 206). For q < 5, the first-bit reverse's output at q is
    determined by the input's values at positions {0, 1, 2, 3, 4}.
    Therefore if g and h agree on those positions, first_rev g and
    first_rev h agree at q. -/
theorem gidney_first_bit_reverse_low_dependence
    (g h : Nat → Bool) (q : Nat) (hq : q < 5)
    (h_eq : ∀ p, p < 5 → g p = h p) :
    gidney_first_bit_reverse_post_state g q
    = gidney_first_bit_reverse_post_state h q := by
  -- Case-split on q ∈ {0, 1, 2, 3, 4}.
  unfold gidney_first_bit_reverse_post_state
  have h_g0 := h_eq 0 (by omega)
  have h_g1 := h_eq 1 (by omega)
  have h_g2 := h_eq 2 (by omega)
  have h_g3 := h_eq 3 (by omega)
  have h_g4 := h_eq 4 (by omega)
  rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 from by omega)
    with hq0 | hq0 | hq0 | hq0 | hq0 <;>
    subst hq0 <;>
    simp [Function.update_apply, h_g0, h_g1, h_g2, h_g3, h_g4,
          show carry_idx 0 = 2 from rfl, show read_idx 0 = 0 from rfl,
          show target_idx 0 = 1 from rfl,
          show read_idx 1 = 3 from rfl, show target_idx 1 = 4 from rfl]

/-- **Last-bit reverse frame condition** (Iter 203). Positions other
    than `carry_idx i` are unchanged. -/
theorem gidney_last_bit_reverse_post_state_preserves_outside
    (i : Nat) (f : Nat → Bool) (q : Nat) (h_q : q ≠ carry_idx i) :
    gidney_last_bit_reverse_post_state i f q = f q := by
  unfold gidney_last_bit_reverse_post_state
  rw [update_neq _ _ _ _ h_q, update_neq _ _ _ _ h_q]

/-- **Last-reverse target/read frame** (2026-05-14 tick, anchors the
    cascade-induction k=0 → k=1 step). The last-bit reverse modifies
    ONLY `carry_idx i` (see def line 2637), so it's the identity on
    every `target_idx j` and `read_idx j`.

    The frame holds universally (for ALL i, j) because the qubit
    layout `read_j = 3j`, `target_j = 3j + 1`, `carry_j = 3j + 2`
    gives disjoint mod-3 residues — `target_idx j ≠ carry_idx i`
    and `read_idx j ≠ carry_idx i` for any (i, j). No `j < n` bound
    needed.

    This is the matching frame for the outer cascade's first step
    (`last_reverse(n-1)` in `gidney_full_reverse_post_state`). Once
    the cascade-induction proof factors through `propagation_reverse`,
    this lemma transfers the post-final-CX target/read state across
    the last-reverse layer unchanged. -/
theorem Gidney.last_reverse_target_read_frame
    (i j : Nat) (f : Nat → Bool) :
    gidney_last_bit_reverse_post_state i f (target_idx j) = f (target_idx j)
    ∧ gidney_last_bit_reverse_post_state i f (read_idx j) = f (read_idx j) := by
  refine ⟨?_, ?_⟩
  · apply gidney_last_bit_reverse_post_state_preserves_outside
    unfold target_idx carry_idx; omega
  · apply gidney_last_bit_reverse_post_state_preserves_outside
    unfold read_idx carry_idx; omega

/-- **`reverse_step_invariant` transfers across last-reverse**
    (2026-05-14 tick). Since `last_reverse(i)` only modifies
    `carry_idx i` (per `last_reverse_target_read_frame`), every
    target/read claim in `reverse_step_invariant k n a b f` is
    preserved when `f` is replaced by `last_bit_reverse i f`.

    This is the structural lemma that lets the outer cascade
    `gidney_full_reverse_post_state` factor through last_reverse:
    if we can establish `inv_n` after the propagation_reverse
    cascade alone (starting from `last_reverse(n-1) post_final_cx`),
    this lemma's NOT what we need; rather, it's the dual — if
    `inv_k` already held BEFORE last_reverse, it still holds AFTER.
    Useful as a frame helper in the cascade-induction proof. -/
theorem Gidney.reverse_step_invariant_preserved_by_last_reverse
    (k n a b i : Nat) (f : Nat → Bool)
    (h : Gidney.reverse_step_invariant k n a b f) :
    Gidney.reverse_step_invariant k n a b
      (gidney_last_bit_reverse_post_state i f) := by
  intro j h_lo h_hi
  obtain ⟨h_t, h_r⟩ := h j h_lo h_hi
  obtain ⟨h_frame_t, h_frame_r⟩ := Gidney.last_reverse_target_read_frame i j f
  refine ⟨?_, ?_⟩
  · rw [h_frame_t, h_t]
  · rw [h_frame_r, h_r]

/-- **K=0 trivial preservation**: `propagation_reverse(0)` is
    definitionally the identity (see def line 4334), so any
    invariant on `f` carries directly to `propagation_reverse(0) f`.
    `:= h` by reduction. -/
theorem Gidney.reverse_step_invariant_preserved_by_propagation_reverse_zero
    (k n a b : Nat) (f : Nat → Bool)
    (h : Gidney.reverse_step_invariant k n a b f) :
    Gidney.reverse_step_invariant k n a b
      (gidney_propagation_reverse_post_state 0 f) := h

/-- **Parametric propagation-cascade target for `inv_K`** (SORRIED,
    2026-05-14 tick — scaffolding the cascade-induction core).

    For register width `n ≥ 2`, the propagation_reverse cascade
    starting from the post-final-CX state produces a state
    satisfying `Gidney.reverse_step_invariant K n a b` for the
    matching K. This is the substantive induction target.

    **Proof strategy** (next 2-3 ticks):
    Induct on K. For each K → K+1 step:
    - Position j = n-K-1 (newly added): use
      `gidney_propagation_reverse_at_target_eq_interior_reverse`
      (line 5364) to reduce `propagation_reverse(K+1) at target_j`
      to `interior_reverse(j-1) g at target_j`, then apply Iter 201
      (`gidney_interior_bit_reverse_computes_sum`) with the
      `post_forward_final_cx_invariant` carry/read hypotheses.
    - Positions j > n-K-1 (already correct, by ih): use
      `gidney_propagation_reverse_preserves_target_above` (line 5316)
      as the frame.

    The j = 1 case (K = n - 1) needs first_bit_reverse handling
    via `gidney_propagation_reverse_eq_first_rev_low` (line 5116) +
    Iter 194's `gidney_first_bit_reverse_preserves`. Target_0 is
    handled by `gidney_propagation_reverse_preserves_target_0`
    (line 4966), combined with the pre-cascade fact that target_0
    = sum_0 after final-CX (since c_0 = 0). -/
-- **REVIEW FINDING (2026-05-14 14:23 tick — MCP-assisted recon).**
-- This K-parametric theorem is UNPROVABLE FOR INTERMEDIATE K. The
-- predicate `reverse_step_invariant K n a b` has range `j ∈ [n-K, n-1]`
-- (grows downward from n-1 as K increases). But the cascade
-- `propagation_reverse(K) input` corrects positions `j ∈ [1, K]`
-- (grows upward from 1 as K increases). The ranges coincide ONLY at
-- the endpoint K = n - 1, where both equal `[1, n-1]`.
--
-- Concrete counterexample: for n=4, K=1, the predicate requires
-- target_3 = sum_3 after propagation_reverse(1) input. But
-- propagation_reverse(1) = first_bit_reverse, which only modifies
-- positions {target_1, read_1, carry_0} — target_3 stays at input's
-- value a_3 ⊕ b_3 ≠ sum_3 unless c_3 = 0.
--
-- The K=0 base case below is provable (vacuous) but the succ case
-- is FALSE for K < n-1. Keep the K=0 base as review data; the right
-- statement is the direct `_n_minus_1_after_propagation_reverse`
-- below (no K-induction; case-split on j with the parametric lemmas).
theorem Gidney.reverse_step_invariant_K_holds_after_propagation_reverse_K_zero_only
    (n a b : Nat) (_hn : 1 < n) (input : Nat → Bool) :
    Gidney.reverse_step_invariant 0 n a b
      (gidney_propagation_reverse_post_state 0 input) :=
  Gidney.reverse_step_invariant_zero n a b input

-- NOTE: `Gidney.reverse_step_invariant_n_minus_1_after_propagation_reverse`
-- (the direct non-K-inductive cascade target) was moved further down
-- in this file (to after `gidney_propagation_reverse_at_target_eq_interior_reverse`)
-- to resolve forward-reference issues. See line ~5630 area.

/-- **Last-bit reverse preserves the low-position frame** (Iter 203,
    2026-05-13). For i ≥ 1, the last-bit reverse only modifies
    `carry_idx i = 3i + 2 ≥ 5`. Positions 0..4 (= read_0, target_0,
    carry_0, read_1, target_1) are all preserved. -/
theorem gidney_last_bit_reverse_preserves_low
    (i : Nat) (hi : 0 < i) (q : Nat) (hq : q < 5) (f : Nat → Bool) :
    gidney_last_bit_reverse_post_state i f q = f q := by
  have h_q_ne_ci : q ≠ carry_idx i := by unfold carry_idx; omega
  exact gidney_last_bit_reverse_post_state_preserves_outside i f q h_q_ne_ci

/-- **Propagation reverse cascade equals first reverse on low positions**
    (Iter 206). For K ≥ 1 and q < 5, propagation_reverse(K) g equals
    first_reverse g at q. -/
theorem gidney_propagation_reverse_eq_first_rev_low
    (K : Nat) (hK : 0 < K) (g : Nat → Bool) (q : Nat) (hq : q < 5) :
    gidney_propagation_reverse_post_state K g q
    = gidney_first_bit_reverse_post_state g q := by
  induction K generalizing g with
  | zero => omega
  | succ m ih =>
      match m with
      | 0 => rfl
      | p + 1 =>
          show gidney_propagation_reverse_post_state (p + 1)
                (gidney_interior_bit_reverse_post_state (p + 1) g) q
              = gidney_first_bit_reverse_post_state g q
          rw [ih (by omega)]
          apply gidney_first_bit_reverse_low_dependence
          · exact hq
          · intro p' hp'
            exact gidney_interior_bit_reverse_preserves_low (p + 1) (by omega) p' hp' g

/-- **Full reverse cascade equals first reverse on low positions**
    (Iter 206). For n ≥ 2 and q < 5, full_reverse(n) f equals
    first_reverse f at q. -/
theorem gidney_full_reverse_eq_first_rev_low
    (n : Nat) (hn : 1 < n) (f : Nat → Bool) (q : Nat) (hq : q < 5) :
    gidney_full_reverse_post_state n f q
    = gidney_first_bit_reverse_post_state f q := by
  match n with
  | 0 => omega
  | 1 => omega
  | m + 2 =>
      show gidney_propagation_reverse_post_state (m + 1)
            (gidney_last_bit_reverse_post_state (m + 1) f) q
          = gidney_first_bit_reverse_post_state f q
      rw [gidney_propagation_reverse_eq_first_rev_low (m + 1) (by omega) _ q hq]
      apply gidney_first_bit_reverse_low_dependence
      · exact hq
      · intro p' hp'
        exact gidney_last_bit_reverse_preserves_low (m + 1) (by omega) p' hp' f

/- (Removed `gidney_classical_action_with_reverse_n2_target_1`: the n=2-only
   j=1 case, superseded by the n-parametric `gidney_classical_action_with_reverse_target_1`
   in `RippleCarryAdderPropagationReverse.lean`; it had no remaining consumers.) -/

/-- **Headline j=0 case PROVEN parametrically** (Iter 202, 2026-05-13).
    For any n ≥ 2 and valid a, b, the j=0 case of
    `TODO_gidney_classical_action_with_reverse` holds: target_0 after
    full forward + final-CX + reverse = `adder_sum_bit_classical a b 0`.

    Composes:
    - Iter 200's `gidney_full_reverse_preserves_target_0` (target_0
      unchanged by full reverse cascade).
    - Iter 189's `Gidney.post_forward_final_cx_invariant_holds`
      (post-CX target_0 = a_0 ⊕ b_0).
    - Iter 163's `Adder.testBit_add_zero` ((a+b).testBit 0 = a_0 ⊕ b_0). -/
theorem gidney_classical_action_with_reverse_target_0
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    gidney_full_reverse_post_state n
      (gidney_final_cx_cascade_post_state n
        (gidney_forward_faithful_full_post_state n (adder_input_F n a b)))
      (target_idx 0)
    = adder_sum_bit_classical a b 0 := by
  -- target_0 unchanged by reverse (Iter 200); post-CX target_0 = a_0 ⊕ b_0 (Iter 189);
  -- then a_0 ⊕ b_0 = (a + b).testBit 0 (Iter 163).
  rw [gidney_full_reverse_preserves_target_0,
      (Gidney.post_forward_final_cx_invariant_holds n a b hn ha hb 0 (by omega)).2.2]
  unfold adder_sum_bit_classical
  rw [Adder.testBit_add_zero]

/-- **Headline j=1 case PROVEN parametrically over n** (Iter 207, 2026-05-13).
    Uses Iter 206's `gidney_full_reverse_eq_first_rev_low` to reduce the
    full reverse cascade at target_idx 1 (= 4 < 5) to just first_reverse,
    then applies Iter 194 with hypotheses verified from Iter 189's invariant. -/
theorem gidney_classical_action_with_reverse_target_1
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    gidney_full_reverse_post_state n
      (gidney_final_cx_cascade_post_state n
        (gidney_forward_faithful_full_post_state n (adder_input_F n a b)))
      (target_idx 1)
    = adder_sum_bit_classical a b 1 := by
  rw [gidney_full_reverse_eq_first_rev_low n hn _ (target_idx 1)
        (by unfold target_idx; omega)]
  set f := gidney_final_cx_cascade_post_state n
            (gidney_forward_faithful_full_post_state n (adder_input_F n a b))
  have h_inv : Gidney.post_forward_final_cx_invariant n a b f :=
    Gidney.post_forward_final_cx_invariant_holds n a b hn ha hb
  rw [(gidney_first_bit_reverse_preserves a b f
        (by rw [(h_inv 0 (by omega)).2.1]; simp [Adder.carry])
        (h_inv 0 (by omega)).2.2 (h_inv 0 (by omega)).1
        (h_inv 1 (by omega)).2.1 (h_inv 1 (by omega)).2.2).2.2]
  -- XOR cleanup via Iter 199's sumfb_eq_testBit_add + 8-case Bool bash.
  unfold adder_sum_bit_classical
  rw [← Adder.sumfb_eq_testBit_add]
  unfold Adder.sumfb
  dsimp only
  cases a.testBit 1 <;> cases b.testBit 1 <;>
    cases (Adder.carry false 1 a.testBit b.testBit) <;> rfl

/-- **First-bit reverse preserves target_j for j ≥ 2** (Iter 209).
    Modifies {c_0, r_1, t_1}; for j ≥ 2, target_idx j = 3j+1 ≥ 7 > 4. -/
theorem gidney_first_bit_reverse_preserves_target_above
    (j : Nat) (hj : 1 < j) (f : Nat → Bool) :
    gidney_first_bit_reverse_post_state f (target_idx j) = f (target_idx j) := by
  have h_t1 : target_idx j ≠ target_idx 1 := by unfold target_idx; omega
  have h_r1 : target_idx j ≠ read_idx 1 := by unfold target_idx read_idx; omega
  have h_c0 : target_idx j ≠ carry_idx 0 := by unfold target_idx carry_idx; omega
  unfold gidney_first_bit_reverse_post_state
  rw [update_neq _ _ _ _ h_c0, update_neq _ _ _ _ h_r1, update_neq _ _ _ _ h_t1]

/-- **First-bit reverse preserves read_j for j > 1** (2026-05-14 tick,
    read-side analog of `_preserves_target_above`). Modifies
    {t_1, r_1, c_0}; for j > 1, read_idx j = 3j ≠ any of those. -/
theorem gidney_first_bit_reverse_preserves_read_above
    (j : Nat) (hj : 1 < j) (f : Nat → Bool) :
    gidney_first_bit_reverse_post_state f (read_idx j) = f (read_idx j) := by
  have h_t1 : read_idx j ≠ target_idx 1 := by unfold read_idx target_idx; omega
  have h_r1 : read_idx j ≠ read_idx 1 := by unfold read_idx; omega
  have h_c0 : read_idx j ≠ carry_idx 0 := by unfold read_idx carry_idx; omega
  unfold gidney_first_bit_reverse_post_state
  rw [update_neq _ _ _ _ h_c0, update_neq _ _ _ _ h_r1, update_neq _ _ _ _ h_t1]

/-- **Interior-bit reverse preserves target_j for j > i+1** (Iter 209).
    Modifies {c_i, r_{i+1}, t_{i+1}}; for j > i+1, target_idx j = 3j+1 >
    3(i+1)+1 = t_{i+1}. -/
theorem gidney_interior_bit_reverse_preserves_target_above
    (i j : Nat) (hij : i + 1 < j) (f : Nat → Bool) :
    gidney_interior_bit_reverse_post_state i f (target_idx j) = f (target_idx j) := by
  have h_t : target_idx j ≠ target_idx (i + 1) := by unfold target_idx; omega
  have h_r : target_idx j ≠ read_idx (i + 1) := by unfold target_idx read_idx; omega
  have h_c : target_idx j ≠ carry_idx i := by unfold target_idx carry_idx; omega
  exact gidney_interior_bit_reverse_post_state_preserves_outside i f _ h_c h_r h_t

/-- **Interior-bit reverse preserves read_j for j > i+1** (2026-05-14
    tick, read-side analog). Same proof structure as the target
    version with read_idx in place of target_idx. -/
theorem gidney_interior_bit_reverse_preserves_read_above
    (i j : Nat) (hij : i + 1 < j) (f : Nat → Bool) :
    gidney_interior_bit_reverse_post_state i f (read_idx j) = f (read_idx j) := by
  have h_t : read_idx j ≠ target_idx (i + 1) := by unfold read_idx target_idx; omega
  have h_r : read_idx j ≠ read_idx (i + 1) := by unfold read_idx; omega
  have h_c : read_idx j ≠ carry_idx i := by unfold read_idx carry_idx; omega
  exact gidney_interior_bit_reverse_post_state_preserves_outside i f _ h_c h_r h_t

/-- **Propagation reverse preserves target_j for j > K** (Iter 209). For
    K ≥ 0 and j > K, propagation_reverse(K) preserves target_idx j. By
    induction on K. -/
theorem gidney_propagation_reverse_preserves_target_above
    (K j : Nat) (hjK : K < j) (f : Nat → Bool) :
    gidney_propagation_reverse_post_state K f (target_idx j) = f (target_idx j) := by
  induction K generalizing f with
  | zero => rfl
  | succ m ih =>
      match m with
      | 0 =>
          -- K=1 = first_reverse. j > 1.
          show gidney_first_bit_reverse_post_state f (target_idx j) = f (target_idx j)
          exact gidney_first_bit_reverse_preserves_target_above j (by omega) f
      | p + 1 =>
          show gidney_propagation_reverse_post_state (p + 1)
                (gidney_interior_bit_reverse_post_state (p + 1) f) (target_idx j)
              = f (target_idx j)
          rw [ih (by omega)]
          -- Goal: interior_reverse(p+1) f (target_idx j) = f (target_idx j).
          exact gidney_interior_bit_reverse_preserves_target_above (p + 1) j (by omega) f

/-- **Propagation reverse preserves read_j for j > K** (2026-05-14
    tick, read-side analog of `_preserves_target_above` at line 5404).
    Same induction-on-K structure with `read_idx` in place of
    `target_idx`. -/
theorem gidney_propagation_reverse_preserves_read_above
    (K j : Nat) (hjK : K < j) (f : Nat → Bool) :
    gidney_propagation_reverse_post_state K f (read_idx j) = f (read_idx j) := by
  induction K generalizing f with
  | zero => rfl
  | succ m ih =>
      match m with
      | 0 =>
          show gidney_first_bit_reverse_post_state f (read_idx j) = f (read_idx j)
          exact gidney_first_bit_reverse_preserves_read_above j (by omega) f
      | p + 1 =>
          show gidney_propagation_reverse_post_state (p + 1)
                (gidney_interior_bit_reverse_post_state (p + 1) f) (read_idx j)
              = f (read_idx j)
          rw [ih (by omega)]
          exact gidney_interior_bit_reverse_preserves_read_above (p + 1) j (by omega) f

/-- **Interior reverse at target_(i+1) only depends on inputs at
    {t_{i+1}, c_i}** (Iter 211). If g and h agree at those two
    positions, then interior_reverse(i) g and interior_reverse(i) h
    agree at target_(i+1). -/
theorem gidney_interior_bit_reverse_at_target_low_dependence
    (i : Nat) (hi : 0 < i) (g h : Nat → Bool)
    (h_t : g (target_idx (i + 1)) = h (target_idx (i + 1)))
    (h_c : g (carry_idx i) = h (carry_idx i)) :
    gidney_interior_bit_reverse_post_state i g (target_idx (i + 1))
    = gidney_interior_bit_reverse_post_state i h (target_idx (i + 1)) := by
  rw [(gidney_interior_bit_reverse_post_state_in_bits i hi g).2.2,
      (gidney_interior_bit_reverse_post_state_in_bits i hi h).2.2,
      h_t, h_c]

/-- **Interior reverse at read_(i+1) only depends on inputs at
    {r_{i+1}, c_i}** (2026-05-14 tick). Read-side analog of
    `_at_target_low_dependence`. Same proof structure with `.2.1`
    (read component of Iter 195's `_in_bits` triple) instead of
    `.2.2`. -/
theorem gidney_interior_bit_reverse_at_read_low_dependence
    (i : Nat) (hi : 0 < i) (g h : Nat → Bool)
    (h_r : g (read_idx (i + 1)) = h (read_idx (i + 1)))
    (h_c : g (carry_idx i) = h (carry_idx i)) :
    gidney_interior_bit_reverse_post_state i g (read_idx (i + 1))
    = gidney_interior_bit_reverse_post_state i h (read_idx (i + 1)) := by
  rw [(gidney_interior_bit_reverse_post_state_in_bits i hi g).2.1,
      (gidney_interior_bit_reverse_post_state_in_bits i hi h).2.1,
      h_r, h_c]

/-- **Propagation reverse at target_j reduces to interior_reverse(j-1)**
    (Iter 211). For j ∈ [2, K], propagation_reverse(K) g (target_idx j)
    equals interior_reverse(j-1) g (target_idx j). The cascade
    reduces to a single per-step.

    Proof: induction on K.
    - K=1: vacuous (j ∈ [2, 1] is empty).
    - K=m+2: propagation_reverse(m+2) g = propagation_reverse(m+1) (interior_reverse(m+1) g).
      - Subcase j = m+2: interior_reverse(m+1) computes target_j; later cascade
        preserves it (Iter 209's preserves_target_above with j > m+1).
      - Subcase j ≤ m+1: by IH, propagation_reverse(m+1) (...) (target_j) =
        interior_reverse(j-1) (interior_reverse(m+1) g) (target_j). And
        interior_reverse(m+1) preserves t_j and c_{j-1} (both ≤ 3j+1 ≤ 3(m+1)+1
        < 3(m+1)+2), so by at_target_low_dependence, this equals
        interior_reverse(j-1) g (target_j). -/
theorem gidney_propagation_reverse_at_target_eq_interior_reverse
    (K j : Nat) (hj : 1 < j) (hjK : j ≤ K) (g : Nat → Bool) :
    gidney_propagation_reverse_post_state K g (target_idx j)
    = gidney_interior_bit_reverse_post_state (j - 1) g (target_idx j) := by
  induction K generalizing g with
  | zero => omega
  | succ m ih =>
      match m with
      | 0 => omega  -- K=1, j ≤ 1 contradicts hj : 1 < j.
      | p + 1 =>
          show gidney_propagation_reverse_post_state (p + 1)
                (gidney_interior_bit_reverse_post_state (p + 1) g) (target_idx j)
              = gidney_interior_bit_reverse_post_state (j - 1) g (target_idx j)
          by_cases hjm : j = p + 2
          · -- Subcase j = m+2 = p+2.
            subst hjm
            rw [gidney_propagation_reverse_preserves_target_above (p + 1) (p + 2)
                  (by omega) _, show (p + 2) - 1 = p + 1 from by omega]
          · -- Subcase j ≤ p+1; use IH then at_target_low_dependence.
            have hjeq : (j - 1) + 1 = j := by omega
            rw [ih (by omega)]
            have key := gidney_interior_bit_reverse_at_target_low_dependence (j - 1)
              (by omega) (gidney_interior_bit_reverse_post_state (p + 1) g) g
              (hjeq ▸ gidney_interior_bit_reverse_post_state_preserves_outside
                (p + 1) g (target_idx j)
                (by unfold target_idx carry_idx; omega)
                (by unfold target_idx read_idx; omega)
                (by unfold target_idx; omega))
              (gidney_interior_bit_reverse_post_state_preserves_outside
                (p + 1) g (carry_idx (j - 1))
                (by unfold carry_idx; omega)
                (by unfold carry_idx read_idx; omega)
                (by unfold carry_idx target_idx; omega))
            simpa [hjeq] using key

end FormalRV.BQAlgo
