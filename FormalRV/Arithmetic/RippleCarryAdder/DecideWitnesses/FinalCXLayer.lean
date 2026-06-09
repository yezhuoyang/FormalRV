/-
  FormalRV.Arithmetic.RippleCarryAdder.DecideWitnesses.FinalCXLayer
  Part 2/4: final-CX cascade frame/action lemmas, `Gidney.post_forward_final_cx_invariant_holds`,
  the no-reverse false-conjecture negations, and the reverse-direction in-bits +
  first-bit-reverse classical-action lemmas. Builds on `ForwardInvariant`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.DecideWitnesses.ForwardInvariant

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-! ### Final-CX cascade frame conditions + action (Iter 184, 2026-05-13)

    The final-CX cascade applies `target_j ⊕= read_j` for j ∈ 0..n-1.
    Three structural properties needed to compose with the
    propagation+last-bit invariant to prove `post_forward_final_cx_invariant`:

    1. Carry positions are unchanged (frame).
    2. Read positions are unchanged (frame).
    3. Target_j gets XOR'd with read_j for j < n (action).

    All three are proven by induction on n with `update_neq` + omega
    on the modulo-3 index distinctness. -/

/-- **Frame condition: final-CX cascade preserves carry positions.**
    For any depth n and any k, the cascade doesn't touch carry_k. -/
theorem gidney_final_cx_cascade_preserves_carry
    (n k : Nat) (f : Nat → Bool) :
    gidney_final_cx_cascade_post_state n f (carry_idx k) = f (carry_idx k) := by
  induction n with
  | zero => rfl
  | succ m ih =>
      show (update (gidney_final_cx_cascade_post_state m f) (target_idx m)
            (xor _ _)) (carry_idx k) = f (carry_idx k)
      have h_ne : carry_idx k ≠ target_idx m := by
        unfold carry_idx target_idx; omega
      rw [update_neq _ _ _ _ h_ne]
      exact ih

/-- **Frame condition: final-CX cascade preserves read positions.**
    For any depth n and any k, the cascade doesn't touch read_k. -/
theorem gidney_final_cx_cascade_preserves_read
    (n k : Nat) (f : Nat → Bool) :
    gidney_final_cx_cascade_post_state n f (read_idx k) = f (read_idx k) := by
  induction n with
  | zero => rfl
  | succ m ih =>
      show (update (gidney_final_cx_cascade_post_state m f) (target_idx m)
            (xor _ _)) (read_idx k) = f (read_idx k)
      have h_ne : read_idx k ≠ target_idx m := by
        unfold read_idx target_idx; omega
      rw [update_neq _ _ _ _ h_ne]
      exact ih

/-- **Frame condition: final-CX cascade preserves target_j for j ≥ n.**
    Target positions at or above the cascade depth are untouched. -/
theorem gidney_final_cx_cascade_target_outside
    (n j : Nat) (hj : n ≤ j) (f : Nat → Bool) :
    gidney_final_cx_cascade_post_state n f (target_idx j) = f (target_idx j) := by
  induction n with
  | zero => rfl
  | succ m ih =>
      show (update (gidney_final_cx_cascade_post_state m f) (target_idx m)
            (xor _ _)) (target_idx j) = f (target_idx j)
      have h_ne : target_idx j ≠ target_idx m := by
        unfold target_idx; omega
      rw [update_neq _ _ _ _ h_ne]
      exact ih (by omega)

/-- **Action of final-CX cascade on target_j for j < n**: the post-state
    XORs the input's read_j into target_j. -/
theorem gidney_final_cx_cascade_target_action
    (n j : Nat) (hj : j < n) (f : Nat → Bool) :
    gidney_final_cx_cascade_post_state n f (target_idx j)
      = xor (f (target_idx j)) (f (read_idx j)) := by
  induction n with
  | zero => omega
  | succ m ih =>
      show (update (gidney_final_cx_cascade_post_state m f) (target_idx m)
            (xor (gidney_final_cx_cascade_post_state m f (target_idx m))
                 (gidney_final_cx_cascade_post_state m f (read_idx m))))
            (target_idx j)
          = xor (f (target_idx j)) (f (read_idx j))
      by_cases hjm : j = m
      · subst hjm
        rw [update_eq,
            gidney_final_cx_cascade_preserves_read _ _ f,
            gidney_final_cx_cascade_target_outside _ _ (le_refl _) f]
      · have h_ne : target_idx j ≠ target_idx m := by
          unfold target_idx; omega
        rw [update_neq _ _ _ _ h_ne]
        exact ih (by omega)

/-- **Parametric `post_forward_final_cx_invariant_holds`** (Iter 189,
    2026-05-13). For any n ≥ 2 with valid bounds, applying
    `gidney_final_cx_cascade_post_state n` to the post-forward state
    `gidney_forward_faithful_full_post_state n (adder_input_F n a b)`
    yields a state satisfying `Gidney.post_forward_final_cx_invariant`.

    **This is THE parametric provable end-state theorem at the
    forward + final-CX layer**, per Iter 182's review finding.
    Composes Iter 188's `post_last_bit_invariant_holds` with
    Iter 184's 4 final-CX structural lemmas:
    - **carry_j**: `final_cx_cascade_preserves_carry` + Iter 188 →
      `c_{j+1}`. ✓
    - **read_j**: `final_cx_cascade_preserves_read` + Iter 188 →
      `a_j ⊕ c_j`. ✓
    - **target_j**: `final_cx_cascade_target_action` (j < n) →
      `f(t_j) ⊕ f(r_j)`. From Iter 188: `f(t_j) = b_j ⊕ c_j`,
      `f(r_j) = a_j ⊕ c_j`. So target_j post-CX = `(b_j ⊕ c_j) ⊕
      (a_j ⊕ c_j) = a_j ⊕ b_j`. The c_j contributions cancel — this
      is exactly Iter 182's review finding made parametric. ✓

    The remaining gap to the headline `gidney_classical_action`:
    target_j is `a_j ⊕ b_j` here, but `sum_j = a_j ⊕ b_j ⊕ c_j`.
    The reverse cascade (separate, awaits Iter 191+ + John's QUESTIONS.md
    #1 approval) re-XORs c_j into target_j to produce sum_j. -/
theorem Gidney.post_forward_final_cx_invariant_holds (n a b : Nat)
    (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    Gidney.post_forward_final_cx_invariant n a b
      (gidney_final_cx_cascade_post_state n
        (gidney_forward_faithful_full_post_state n (adder_input_F n a b))) := by
  have h_lb := Gidney.post_last_bit_invariant_holds n a b hn ha hb
  -- h_lb : ∀ j, j < n → 3 conjuncts about (forward state) at c_j, r_j, t_j.
  intro j hj
  refine ⟨?_, ?_, ?_⟩
  · -- carry_j: final-CX preserves carry; from h_lb, forward(c_j) = c_{j+1}.
    rw [gidney_final_cx_cascade_preserves_carry n j _]
    exact (h_lb j hj).1
  · -- read_j: final-CX preserves read; from h_lb, forward(r_j) = a_j ⊕ c_j.
    rw [gidney_final_cx_cascade_preserves_read n j _]
    exact (h_lb j hj).2.1
  · -- target_j: final-CX action gives forward(t_j) ⊕ forward(r_j); from h_lb,
    -- = (b_j ⊕ c_j) ⊕ (a_j ⊕ c_j) = a_j ⊕ b_j.
    rw [gidney_final_cx_cascade_target_action n j hj _]
    rw [(h_lb j hj).2.2, (h_lb j hj).2.1]
    -- Goal: xor (xor (b_j) c_j) (xor (a_j) c_j) = xor (a_j) (b_j)
    -- Generalize c_j to a free Bool var and case-bash.
    generalize Adder.carry false j a.testBit b.testBit = c
    cases a.testBit j <;> cases b.testBit j <;> cases c <;> rfl

/-- **Phase A end-to-end review finding (negation, proven 2026-05-22)**:
    the conjecture *"the Gidney adder's forward + final-CX cascade alone
    (no reverse cascade) computes the classical sum"* is FALSE.

    HISTORY: this slot used to hold a sorried theorem named
    `TODO_gidney_classical_action` asserting the (false) positive form.
    Iter 182 (2026-05-13) supplied a machine-checked counterexample at
    (n=2, a=1, b=1) — see `gidney_classical_action_unprovable_at_1_plus_1`
    below — proving that the positive form was unprovable as stated.
    The corrected headline `gidney_classical_action_with_reverse`
    (proven at line ~5709) is the canonical semantic-correctness theorem.

    The honest record of the review finding lives here as a proven
    negation theorem (no sorry): the universally-quantified positive
    conjecture is impossible because it fails at the specific witness
    (n=2, a=1, b=1, i=1). -/
theorem gidney_classical_action_without_reverse_is_false :
    ¬ (∀ (n a b : Nat), 0 < n → a < 2^n → b < 2^n →
        ∀ i, i < n →
          gidney_final_cx_cascade_post_state n
            (gidney_forward_faithful_full_post_state n (adder_input_F n a b))
            (target_idx i)
          = adder_sum_bit_classical a b i) := by
  intro h
  have := h 2 1 1 (by decide) (by decide) (by decide) 1 (by decide)
  revert this
  decide

/-- **REVIEW FINDING (Iter 182, 2026-05-13)**: machine-checked
    counterexample establishing that `TODO_gidney_classical_action`
    is UNPROVABLE as currently stated.

    For the instance `(n=2, a=1, b=1)` (all hypotheses satisfied:
    `0 < 2`, `1 < 4`, `1 < 4`), the conclusion `∀ i, i < 2,
    forward+final-CX(target_i) = (a+b).testBit i` fails at `i=1`:
    - Forward+final-CX on `adder_input_F 2 1 1` yields target_1 = 0
      (decide-witnessed at lines ~2395-2404 via `inputF_1_plus_1`).
    - `(1+1).testBit 1 = 2.testBit 1 = 1`.
    - 0 ≠ 1. ∎

    The forward + final-CX cascade produces `target_j = a_j ⊕ b_j`
    for `j ≥ 1` (the two `c_j` contributions from forward propagation
    cancel via the final-CX `t_j ⊕= r_j`). But the classical sum is
    `sum_j = a_j ⊕ b_j ⊕ c_j`, which is OFF by `c_j` whenever
    `c_j = 1`.

    **The full Gidney adder requires the REVERSE cascade.** Its
    per-step `CX(c_{j-1}, t_j)` re-XORs `c_j` into target_j, fixing
    the gap. Hence the headline theorem should be:
    ```
    gidney_forward_faithful_full_reverse_post_state n
      (gidney_final_cx_cascade_post_state n
        (gidney_forward_faithful_full_post_state n (adder_input_F n a b)))
      (target_idx i) = adder_sum_bit_classical a b i
    ```
    (i.e., forward + final-CX + REVERSE, applied left-to-right.)

    See QUESTIONS.md (entry 2026-05-13 #1) for the proposed
    theorem-statement fix awaiting John's approval. -/
theorem gidney_classical_action_unprovable_at_1_plus_1 :
    ¬ (∀ i, i < 2 →
        gidney_final_cx_cascade_post_state 2
          (gidney_forward_faithful_full_post_state 2 (adder_input_F 2 1 1))
          (target_idx i)
        = adder_sum_bit_classical 1 1 i) := by
  intro h
  have h1 := h 1 (by decide)
  revert h1
  decide

/-- **Decide-witness for full reverse on (n=2, a=1, b=1)** (Iter 191).
    Confirms that applying the reverse cascade to the post-final-CX
    state of (1+1) restores `target_1 = 1 = sum_1`, fixing the
    Iter 182 counterexample. The reverse cascade DOES compute the
    sum bits — Iter 106's older comment was wrong. -/
example :
    let post := gidney_full_reverse_post_state 2
                  (gidney_final_cx_cascade_post_state 2
                    (gidney_forward_faithful_full_post_state 2 (adder_input_F 2 1 1)))
    post (target_idx 0) = adder_sum_bit_classical 1 1 0
    ∧ post (target_idx 1) = adder_sum_bit_classical 1 1 1 := by decide

/-- **Decide-witness on (n=3, a=3, b=1)** (Iter 191). Multi-bit. -/
example :
    let post := gidney_full_reverse_post_state 3
                  (gidney_final_cx_cascade_post_state 3
                    (gidney_forward_faithful_full_post_state 3 (adder_input_F 3 3 1)))
    post (target_idx 0) = adder_sum_bit_classical 3 1 0
    ∧ post (target_idx 1) = adder_sum_bit_classical 3 1 1
    ∧ post (target_idx 2) = adder_sum_bit_classical 3 1 2 := by decide

/-- **Interior-bit reverse in-bits structural lemma (PROVEN, Iter 195,
    2026-05-13)**. Analog of Iter 167's `gidney_interior_bit_post_state_in_bits`
    for the reverse direction. Captures the pure structural action of
    `gidney_interior_bit_reverse_post_state i` on an arbitrary input
    `f` (no input invariant assumed).

    Computed by walking the 4 chained updates of the def:
    - **post(c_i)** = `(f(c_i) ⊕ f(c_{i-1})) ⊕ (f(r_i) ∧ f(t_i))`.
      Outermost update (gate 4: CCX undo) adds `(r_i ∧ t_i)` to the
      previous c_i value, which itself was modified by gate 3
      (chain CX) to be `f(c_i) ⊕ f(c_{i-1})`.
    - **post(r_{i+1})** = `f(r_{i+1}) ⊕ f(c_i)` (gate 2 propagates
      original c_i back through r_{i+1}).
    - **post(t_{i+1})** = `f(t_{i+1}) ⊕ f(c_i)` (gate 1 propagates
      back through t_{i+1}). -/
theorem gidney_interior_bit_reverse_post_state_in_bits
    (i : Nat) (hi : 0 < i) (f : Nat → Bool) :
    (gidney_interior_bit_reverse_post_state i f) (carry_idx i)
      = xor (xor (f (carry_idx i)) (f (carry_idx (i - 1))))
            (f (read_idx i) && f (target_idx i))
    ∧ (gidney_interior_bit_reverse_post_state i f) (read_idx (i + 1))
        = xor (f (read_idx (i + 1))) (f (carry_idx i))
    ∧ (gidney_interior_bit_reverse_post_state i f) (target_idx (i + 1))
        = xor (f (target_idx (i + 1))) (f (carry_idx i)) := by
  -- Index inequalities for the def's 4 update sites: t_{i+1}, r_{i+1}, c_i, c_i.
  have h_ri1_ti1 : read_idx (i + 1) ≠ target_idx (i + 1) := by
    unfold read_idx target_idx; omega
  have h_ci_ti1 : carry_idx i ≠ target_idx (i + 1) := by
    unfold carry_idx target_idx; omega
  have h_ci_ri1 : carry_idx i ≠ read_idx (i + 1) := by
    unfold carry_idx read_idx; omega
  have h_cim1_ci : carry_idx (i - 1) ≠ carry_idx i := by
    unfold carry_idx; omega
  have h_cim1_ri1 : carry_idx (i - 1) ≠ read_idx (i + 1) := by
    unfold carry_idx read_idx; omega
  have h_cim1_ti1 : carry_idx (i - 1) ≠ target_idx (i + 1) := by
    unfold carry_idx target_idx; omega
  have h_ri_ci : read_idx i ≠ carry_idx i := by
    unfold read_idx carry_idx; omega
  have h_ri_ri1 : read_idx i ≠ read_idx (i + 1) := by
    unfold read_idx; omega
  have h_ri_ti1 : read_idx i ≠ target_idx (i + 1) := by
    unfold read_idx target_idx; omega
  have h_ti_ci : target_idx i ≠ carry_idx i := by
    unfold target_idx carry_idx; omega
  have h_ti_ri1 : target_idx i ≠ read_idx (i + 1) := by
    unfold target_idx read_idx; omega
  have h_ti_ti1 : target_idx i ≠ target_idx (i + 1) := by
    unfold target_idx; omega
  unfold gidney_interior_bit_reverse_post_state
  refine ⟨?_, ?_, ?_⟩
  · -- post(c_i): outer + f₃ both at c_i → 2x update_eq.
    -- Then unwrap f₂(c_i), f₁(c_i), f₂(c_{i-1}), f₁(c_{i-1}), f₃(r_i)→f₂(r_i)→f₁(r_i),
    -- and f₃(t_i)→f₂(t_i)→f₁(t_i).
    rw [update_eq, update_eq,
        update_neq _ _ _ _ h_ci_ri1, update_neq _ _ _ _ h_ci_ti1,
        update_neq _ _ _ _ h_cim1_ri1, update_neq _ _ _ _ h_cim1_ti1,
        update_neq _ _ _ _ h_ri_ci, update_neq _ _ _ _ h_ri_ri1,
        update_neq _ _ _ _ h_ri_ti1,
        update_neq _ _ _ _ h_ti_ci, update_neq _ _ _ _ h_ti_ri1,
        update_neq _ _ _ _ h_ti_ti1]
  · -- post(r_{i+1}): outer at c_i ≠ r_{i+1}, f₃ at c_i ≠ r_{i+1}, f₂ at r_{i+1} hit.
    rw [update_neq _ _ _ _ h_ci_ri1.symm, update_neq _ _ _ _ h_ci_ri1.symm,
        update_eq, update_neq _ _ _ _ h_ri1_ti1, update_neq _ _ _ _ h_ci_ti1]
  · -- post(t_{i+1}): outer at c_i ≠ t_{i+1}, f₃ at c_i ≠ t_{i+1},
    -- f₂ at r_{i+1} ≠ t_{i+1}, f₁ at t_{i+1} hit.
    rw [update_neq _ _ _ _ h_ci_ti1.symm, update_neq _ _ _ _ h_ci_ti1.symm,
        update_neq _ _ _ _ h_ri1_ti1.symm, update_eq]

/-- **Last-bit reverse in-bits structural lemma (PROVEN, Iter 195,
    2026-05-13)**. Analog of Iter 169's `gidney_last_bit_post_state_in_bits`
    for the reverse direction.

    The last-bit-reverse has only 2 gates (no propagation), so it
    only modifies `c_i`:
    - **post(c_i)** = `(f(c_i) ⊕ f(c_{i-1})) ⊕ (f(r_i) ∧ f(t_i))`. -/
theorem gidney_last_bit_reverse_post_state_in_bits
    (i : Nat) (hi : 0 < i) (f : Nat → Bool) :
    (gidney_last_bit_reverse_post_state i f) (carry_idx i)
      = xor (xor (f (carry_idx i)) (f (carry_idx (i - 1))))
            (f (read_idx i) && f (target_idx i)) := by
  have h_cim1_ci : carry_idx (i - 1) ≠ carry_idx i := by
    unfold carry_idx; omega
  have h_ri_ci : read_idx i ≠ carry_idx i := by
    unfold read_idx carry_idx; omega
  have h_ti_ci : target_idx i ≠ carry_idx i := by
    unfold target_idx carry_idx; omega
  unfold gidney_last_bit_reverse_post_state
  -- 2 chained updates, both at c_i. After 2x update_eq, the f₁(c_i) reduces
  -- to xor (f c_i) (f c_{i-1}), and f₁(r_i)/f₁(t_i) need update_neq.
  rw [update_eq, update_eq,
      update_neq _ _ _ _ h_ri_ci, update_neq _ _ _ _ h_ti_ci]

/-- **First-bit reverse classical-action lemma (PROVEN, Iter 193,
    2026-05-13)**. Analog of Iter 165's `gidney_first_bit_preserves`
    for the reverse direction.

    Given a state `f` matching the post-forward-final-CX invariant at
    positions {r_0, t_0, c_0, r_1, t_1}, applying
    `gidney_first_bit_reverse_post_state` produces:
    - **post(c_0) = a_0** (a "dirty carry" — restored to a_0, NOT to
      false. This is consistent with Iter 106's older "dirty carries"
      observation in the file's reverse smoke tests.)
    - **post(r_1) = a_1** (carry XOR'd out, restored to input).
    - **post(t_1) = sum_1 = a_1 ⊕ b_1 ⊕ c_1** — the SUM BIT. The
      reverse cascade's first step XORs c_1 into target_1, completing
      the sum that the forward+final-CX had pending.

    This is the CRITICAL semantic step that fixes the Iter 182 review
    finding: the reverse re-XORs the math carry (which the qubit c_0
    holds post-forward) into target_1.

    The dirty post(c_0) = a_0 calculation:
      post(c_0) = c_1 ⊕ (r_0 ∧ t_0)
              = (a_0 ∧ b_0) ⊕ (a_0 ∧ (a_0 ⊕ b_0))
              = (a_0 ∧ b_0) ⊕ (a_0 ∧ ¬b_0)
              = a_0 ∧ (b_0 ⊕ ¬b_0)
              = a_0 ∧ true = a_0.   ∎ -/
theorem gidney_first_bit_reverse_preserves
    (a b : Nat) (f : Nat → Bool)
    (h_r0 : f (read_idx 0) = a.testBit 0)
    (h_t0 : f (target_idx 0) = xor (a.testBit 0) (b.testBit 0))
    (h_c0 : f (carry_idx 0) = Adder.carry false 1 a.testBit b.testBit)
    (h_r1 : f (read_idx 1)
              = xor (a.testBit 1) (Adder.carry false 1 a.testBit b.testBit))
    (h_t1 : f (target_idx 1) = xor (a.testBit 1) (b.testBit 1)) :
    let post := gidney_first_bit_reverse_post_state f
    post (carry_idx 0) = a.testBit 0
    ∧ post (read_idx 1) = a.testBit 1
    ∧ post (target_idx 1)
        = xor (xor (a.testBit 1) (b.testBit 1))
              (Adder.carry false 1 a.testBit b.testBit) := by
  -- Index inequalities. The def's 3 updates are at: t_1, r_1, c_0.
  -- All other positions need update_neq vs these 3.
  have h_t1_c0 : target_idx 1 ≠ carry_idx 0 := by unfold target_idx carry_idx; omega
  have h_t1_r1 : target_idx 1 ≠ read_idx 1 := by unfold target_idx read_idx; omega
  have h_r1_c0 : read_idx 1 ≠ carry_idx 0 := by unfold read_idx carry_idx; omega
  have h_r0_r1 : read_idx 0 ≠ read_idx 1 := by unfold read_idx; omega
  have h_r0_t1 : read_idx 0 ≠ target_idx 1 := by unfold read_idx target_idx; omega
  have h_t0_r1 : target_idx 0 ≠ read_idx 1 := by unfold target_idx read_idx; omega
  have h_t0_t1 : target_idx 0 ≠ target_idx 1 := by unfold target_idx; omega
  unfold gidney_first_bit_reverse_post_state
  refine ⟨?_, ?_, ?_⟩
  · -- post(c_0): outer update at c_0 hits → update_eq. Then traverse f₂, f₁ at c_0, r_0, t_0.
    rw [update_eq,
        update_neq _ _ _ _ h_r1_c0.symm,    -- f₂(c_0) = f₁(c_0)  (update at r_1)
        update_neq _ _ _ _ h_t1_c0.symm,    -- f₁(c_0) = f(c_0)   (update at t_1)
        update_neq _ _ _ _ h_r0_r1,         -- f₂(r_0) = f₁(r_0)  (update at r_1, query r_0)
        update_neq _ _ _ _ h_r0_t1,         -- f₁(r_0) = f(r_0)   (update at t_1, query r_0)
        update_neq _ _ _ _ h_t0_r1,         -- f₂(t_0) = f₁(t_0)  (update at r_1, query t_0)
        update_neq _ _ _ _ h_t0_t1,         -- f₁(t_0) = f(t_0)   (update at t_1, query t_0)
        h_c0, h_r0, h_t0]
    -- Goal: c_1 ⊕ (a_0 ∧ (a_0 ⊕ b_0)) = a_0.  c_1 = Adder.carry false 1 a b = a_0 ∧ b_0.
    unfold Adder.carry
    cases a.testBit 0 <;> cases b.testBit 0 <;> rfl
  · -- post(r_1): outer update at c_0 queried at r_1 → update_neq with r_1 ≠ c_0.
    rw [update_neq _ _ _ _ h_r1_c0,         -- outer: queried r_1, update at c_0
        update_eq,                              -- f₂(r_1) = value at r_1 update
        update_neq _ _ _ _ h_t1_r1.symm,     -- f₁(r_1) = f(r_1) (update at t_1, query r_1)
        update_neq _ _ _ _ h_t1_c0.symm,     -- f₁(c_0) = f(c_0) (update at t_1, query c_0)
        h_r1, h_c0]
    -- Goal: (a_1 ⊕ c_1) ⊕ c_1 = a_1.
    cases a.testBit 1 <;>
      cases (Adder.carry false 1 a.testBit b.testBit) <;> rfl
  · -- post(t_1): outer at c_0 query t_1 → update_neq (h_t1_c0). Then f₂ at t_1 → update_neq (h_t1_r1). f₁ at t_1 → update_eq.
    rw [update_neq _ _ _ _ h_t1_c0,         -- outer: t_1 vs c_0
        update_neq _ _ _ _ h_t1_r1,         -- f₂ at t_1: update at r_1, neq
        update_eq,                              -- f₁ at t_1: update at t_1, eq
        h_t1, h_c0]

/-- **Decide-witness for `gidney_first_bit_reverse_preserves` on
    (a=1, b=1)** (Iter 193). Validates the lemma statement holds
    for the post-forward+final-CX state of the (1+1) instance. -/
example :
    let f := gidney_final_cx_cascade_post_state 2
              (gidney_forward_faithful_full_post_state 2 (adder_input_F 2 1 1))
    let post := gidney_first_bit_reverse_post_state f
    post (carry_idx 0) = (1 : Nat).testBit 0
    ∧ post (read_idx 1) = (1 : Nat).testBit 1
    ∧ post (target_idx 1)
        = xor (xor ((1 : Nat).testBit 1) ((1 : Nat).testBit 1))
              (Adder.carry false 1 (1 : Nat).testBit (1 : Nat).testBit) := by
  decide

/-- **Decide-witness on (a=3, b=1) at n=3** (Iter 193). Multi-bit. -/
example :
    let f := gidney_final_cx_cascade_post_state 3
              (gidney_forward_faithful_full_post_state 3 (adder_input_F 3 3 1))
    let post := gidney_first_bit_reverse_post_state f
    post (carry_idx 0) = (3 : Nat).testBit 0
    ∧ post (read_idx 1) = (3 : Nat).testBit 1
    ∧ post (target_idx 1)
        = xor (xor ((3 : Nat).testBit 1) ((1 : Nat).testBit 1))
              (Adder.carry false 1 (3 : Nat).testBit (1 : Nat).testBit) := by
  decide

/- **PROPOSED RESTATED HEADLINE** (Iter 191, 2026-05-13; Iter 213
   SUPERSEDED). The parametric semantic-correctness theorem with
   the REVERSE cascade included, fixing the Iter 182 review finding
   (the existing `TODO_gidney_classical_action` is unprovable as stated).

   **Status (Iter 213)**: SUPERSEDED by `gidney_classical_action_with_reverse_assembled`
   + `gidney_classical_action_with_reverse` (final, derived) at the end
   of this file. Both are FULLY PROVEN parametrically. The original
   `TODO_gidney_classical_action_with_reverse` sorried theorem at this
   location has been removed; see the proven version at end of file.

   Originally sorried; the proof structure now decomposes via
   `assembled`'s case-split on i ∈ {0, 1, ≥ 2}. -/

/-- **Decide-witness on (n=2, a=1, b=1)** (Iter 197). Validates the
    richer Iter 197 invariant on the Iter 182 counterexample case. -/
example :
    Gidney.post_full_reverse_invariant 2 1 1
      (gidney_full_reverse_post_state 2
        (gidney_final_cx_cascade_post_state 2
          (gidney_forward_faithful_full_post_state 2 (adder_input_F 2 1 1)))) := by
  intro j hj
  match j, hj with
  | 0, _ => refine ⟨?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_⟩ <;> decide
  | _ + 2, h => omega

/-- **Decide-witness on (n=3, a=3, b=1)** (Iter 197). Multi-bit. -/
example :
    Gidney.post_full_reverse_invariant 3 3 1
      (gidney_full_reverse_post_state 3
        (gidney_final_cx_cascade_post_state 3
          (gidney_forward_faithful_full_post_state 3 (adder_input_F 3 3 1)))) := by
  intro j hj
  match j, hj with
  | 0, _ => refine ⟨?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_⟩ <;> decide
  | 2, _ => refine ⟨?_, ?_⟩ <;> decide
  | _ + 3, h => omega

/-- **Smoke decide-witness at k=n=2, (a,b) = (1,1)** (the
    Iter 182 counterexample case). When the step index equals
    the register width, the predicate covers every j and matches
    the witnessed `post_full_reverse_invariant` at line 4615. -/
example :
    Gidney.reverse_step_invariant 2 2 1 1
      (gidney_full_reverse_post_state 2
        (gidney_final_cx_cascade_post_state 2
          (gidney_forward_faithful_full_post_state 2 (adder_input_F 2 1 1)))) := by
  intro j _ hj
  match j, hj with
  | 0, _ => refine ⟨?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_⟩ <;> decide
  | _ + 2, h => omega

end FormalRV.BQAlgo
