/-
  FormalRV.Arithmetic.RippleCarryAdder.DecideWitnesses.ReverseStepScaffold
  Part 3/4: the step-indexed `reverse_step_invariant` scaffolding (zero base,
  n-iff bridge, apply/weaken, abstract succ engine) and the per-step
  interior-reverse-computes-one-sum-bit lemma. Builds on `FinalCXLayer`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.DecideWitnesses.FinalCXLayer

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-- **Base case of the cascade induction**: when `k = 0`, the
    step-indexed invariant is vacuously true because the quantifier
    range `n - 0 ≤ j ∧ j < n` simplifies to `n ≤ j ∧ j < n`, which
    is unsatisfiable. No assumption on `post` is needed.

    This is the starting point for the inductive proof of
    `TODO_post_full_reverse_invariant_holds` — the parametric
    `reverse_step_invariant k n a b _` will be lifted from k=0
    up to k=n via a `_succ` step that uses Iter 194 (first-bit
    reverse) + Iter 195 (interior `in_bits`) + Iter 201
    (interior `computes_sum`) + the cascade-frame property. -/
theorem Gidney.reverse_step_invariant_zero (n a b : Nat) (post : Nat → Bool) :
    Gidney.reverse_step_invariant 0 n a b post := by
  intro j h₁ h₂
  exfalso
  omega

/-- **k=n bridge** to the original `Gidney.post_full_reverse_invariant`:
    when the step index equals the register width, the step-indexed
    predicate's quantifier range `n - n ≤ j ∧ j < n` simplifies to
    `0 ≤ j ∧ j < n`, which is the same range as the post-full-reverse
    invariant.

    This is the closing composition step for
    `TODO_post_full_reverse_invariant_holds`: once a `_succ` lemma
    lifts the predicate from k=0 up to k=n, this iff turns
    `reverse_step_invariant n _ _ _ _` into the goal. -/
theorem Gidney.reverse_step_invariant_n_iff_post_full_reverse_invariant
    (n a b : Nat) (post : Nat → Bool) :
    Gidney.reverse_step_invariant n n a b post ↔
      Gidney.post_full_reverse_invariant n a b post := by
  unfold Gidney.reverse_step_invariant Gidney.post_full_reverse_invariant
  constructor
  · intro h j hj
    exact h j (by omega) hj
  · intro h j _ hj
    exact h j hj

/-- **Specialization-at-j helper**: given the step-indexed predicate
    and witnesses that position `j` is in its quantifier range,
    extract the (target, read) correctness pair at `j`. A trivial
    1-line application of the predicate; named for readability in
    downstream cascade-induction proofs that need to invoke the
    invariant at a specific position. -/
theorem Gidney.reverse_step_invariant_apply
    (k n a b j : Nat) (post : Nat → Bool)
    (h_inv : Gidney.reverse_step_invariant k n a b post)
    (h_lo : n - k ≤ j) (h_hi : j < n) :
    post (target_idx j) = adder_sum_bit_classical a b j ∧
      post (read_idx j) = a.testBit j :=
  h_inv j h_lo h_hi

/-- **Weakening**: a larger step index strengthens the invariant
    (covers more positions), so `inv_{k+1} → inv_k`. Useful when a
    cascade-induction proof has established the strong form and
    needs to extract a weaker one for a sub-case. Direct from the
    definition: `n - (k+1) ≤ j` implies `n - k ≤ j` via `omega`. -/
theorem Gidney.reverse_step_invariant_weaken
    (k n a b : Nat) (post : Nat → Bool)
    (h : Gidney.reverse_step_invariant (k + 1) n a b post) :
    Gidney.reverse_step_invariant k n a b post := by
  intro j h_lo h_hi
  exact h j (by omega) h_hi

/-- **Abstract `_succ` step**: lift the step-indexed invariant from
    `k` to `k+1` given (a) the new step's correctness at position
    `n - k - 1` (target and read both get their final values),
    and (b) a frame condition saying the new step doesn't disturb
    positions `j ∈ [n - k, n - 1]` that were already correct.

    This is the abstract induction engine for
    `TODO_post_full_reverse_invariant_holds`. To instantiate it on
    a specific cascade step (last_reverse, interior_reverse, or
    first_bit_reverse), supply the matching correctness +
    frame lemmas from Iter 194 / 195 / 200 / 201.

    Proof: case-split on whether `j` is the newly-added position
    `n - k - 1` (then use the step-correctness hypotheses) or one
    of the already-correct positions `j ≥ n - k` (then use ih +
    frame). -/
-- ### Recon finding (2026-05-14 13:41 tick) — cascade-step / invariant mismatch
--
-- Reading the actual cascade definitions reveals that the step-indexed
-- invariant `reverse_step_invariant k` (covers `j ∈ [n-k, n-1]`) does
-- NOT correspond 1-to-1 with `gidney_full_reverse_post_state`'s
-- execution steps. Specifically, examining
-- `gidney_last_bit_reverse_post_state i` (line 2637) shows it modifies
-- ONLY `carry_idx i` — it does NOT set target_i = sum_i. The first
-- "step" of the full cascade is a no-op for the target/read invariant.
--
-- Cascade execution order (for register width `n`, n ≥ 2):
--   1. last_reverse(n-1)           — touches carry_{n-1} only
--   2. interior_reverse(n-2)       — sets target_{n-1} = sum_{n-1}
--   3. interior_reverse(n-3)       — sets target_{n-2} = sum_{n-2}
--   ...
--   n-1. interior_reverse(1)       — sets target_2 = sum_2
--   n.   first_bit_reverse         — sets target_1 = sum_1
--   (target_0 = sum_0 set earlier by final-CX, not the reverse cascade.)
--
-- So the right inductive object is `gidney_propagation_reverse_post_state`
-- (line 4334), not the outer `gidney_full_reverse_post_state`. The outer
-- cascade is just `propagation_reverse ∘ last_reverse`, and last_reverse
-- is a target/read frame (it doesn't touch them) — see Iter 200's
-- `gidney_last_bit_reverse_preserves_target_0` (line 4914) as one
-- matching frame lemma. The full set of frame conditions for last_reverse
-- on target/read needs to be assembled (or the existing
-- `gidney_last_bit_reverse_post_state_preserves_outside` at line 5004
-- may suffice with appropriate index inequalities).
--
-- Implication for the cascade induction:
--   - Reformulate the parametric theorem to factor through the
--     propagation_reverse cascade: prove
--     `reverse_step_invariant n n a b (propagation_reverse_post_state
--     (n-1) (last_reverse_post_state (n-1) post_final_cx))`
--     by first applying a last_reverse target/read frame
--     lemma and then inducting on the propagation chain.
--   - The `_succ_via_step_property` engine still applies for each
--     propagation step (k=1 first instantiated via interior_reverse(n-2),
--     k=n-1 via first_bit_reverse). Target_0 needs separate handling
--     (set by final-CX, preserved by every reverse step — Iter 200
--     frame lemmas cover this).

theorem Gidney.reverse_step_invariant_succ_via_step_property
    (k n a b : Nat) (post post' : Nat → Bool)
    (ih : Gidney.reverse_step_invariant k n a b post)
    (_hk : k < n)
    (h_step_target :
      post' (target_idx (n - k - 1)) = adder_sum_bit_classical a b (n - k - 1))
    (h_step_read :
      post' (read_idx (n - k - 1)) = a.testBit (n - k - 1))
    (h_frame_target : ∀ j, n - k ≤ j → j < n →
                        post' (target_idx j) = post (target_idx j))
    (h_frame_read : ∀ j, n - k ≤ j → j < n →
                      post' (read_idx j) = post (read_idx j)) :
    Gidney.reverse_step_invariant (k + 1) n a b post' := by
  intro j h_lo h_hi
  by_cases h_eq : j = n - k - 1
  · exact h_eq ▸ ⟨h_step_target, h_step_read⟩
  · have h_lo' : n - k ≤ j := by omega
    have ⟨h_t, h_r⟩ := ih j h_lo' h_hi
    exact ⟨(h_frame_target j h_lo' h_hi).trans h_t, (h_frame_read j h_lo' h_hi).trans h_r⟩

/-! ### Per-step reverse computes one sum bit (Iter 201, 2026-05-13)

    KEY INSIGHT: when interior_reverse(j) fires in the reverse cascade
    on a state still satisfying `post_forward_final_cx_invariant` at
    positions {c_j, r_{j+1}, t_{j+1}}, it computes `target_{j+1} = sum_{j+1}`.

    This works because the reverse cascade processes positions
    TOP-DOWN. When interior_reverse(j) fires, all earlier reverses
    (last_reverse(n-1), interior_reverse(n-2), ..., interior_reverse(j+1))
    only modified positions ≥ j+1's carry/read/target — NOT the
    {c_j, r_{j+1}, t_{j+1}} that interior_reverse(j) needs. So the
    post-CX invariant still holds at those positions when this step fires.

    Together with Iter 194's first-bit-reverse-preserves (covers j=1)
    and Iter 200's target_0 frame (j=0), this gives complete coverage
    of the headline `target_j = sum_j` for j ∈ [0, n-1]. -/

/-- **Interior-bit reverse computes one sum bit** (PROVEN, Iter 201):
    given a state `f` whose values at {c_j, r_{j+1}, t_{j+1}} match the
    post-forward+final-CX invariant, applying `interior_reverse(j)`
    produces `target_{j+1} = sum_{j+1}`.

    XOR identity: `(a_{j+1} ⊕ b_{j+1}) ⊕ c_{j+1} = sum_{j+1}` (since
    `sumfb false a b (j+1) = c_{j+1} ⊕ a_{j+1} ⊕ b_{j+1}`). Proof
    composes Iter 195's `gidney_interior_bit_reverse_post_state_in_bits`
    with Iter 199's `Adder.sumfb_eq_testBit_add`. -/
theorem gidney_interior_bit_reverse_computes_sum
    (j a b : Nat) (hj : 0 < j) (f : Nat → Bool)
    (h_cj : f (carry_idx j) = Adder.carry false (j + 1) a.testBit b.testBit)
    (h_tj1 : f (target_idx (j + 1))
              = xor (a.testBit (j + 1)) (b.testBit (j + 1))) :
    let post := gidney_interior_bit_reverse_post_state j f
    post (target_idx (j + 1)) = adder_sum_bit_classical a b (j + 1) := by
  -- Apply Iter 195's in_bits to get post(t_{j+1}) = f(t_{j+1}) ⊕ f(c_j).
  have h := (gidney_interior_bit_reverse_post_state_in_bits j hj f).2.2
  show gidney_interior_bit_reverse_post_state j f (target_idx (j + 1)) = _
  rw [h, h_tj1, h_cj]
  -- Goal: xor (xor a_{j+1} b_{j+1}) c_{j+1} = adder_sum_bit_classical a b (j+1)
  -- = (a+b).testBit (j+1) = sumfb false ab (j+1) = xor (xor c_{j+1} a_{j+1}) b_{j+1}.
  unfold adder_sum_bit_classical
  rw [← Adder.sumfb_eq_testBit_add]
  unfold Adder.sumfb
  -- Goal: xor (xor a_{j+1} b_{j+1}) c_{j+1} = xor (xor c_{j+1} a_{j+1}) b_{j+1}
  -- XOR commutativity/associativity: 8-case Bool bash. dsimp first to
  -- beta-reduce (fun k => x.testBit k) (j+1) on RHS.
  dsimp only
  cases a.testBit (j + 1) <;> cases b.testBit (j + 1) <;>
    cases (Adder.carry false (j + 1) a.testBit b.testBit) <;> rfl

end FormalRV.BQAlgo
