import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Audit.Common.PaperClaims
import FormalRV.PPM.GidneyAND
import Mathlib.Tactic.IntervalCases
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderDefinitions
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderRSA2048Resource

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-- **Decide-witness on (n=2, a=1, b=0)** (Iter 187). No-carry case. -/
example :
    Gidney.post_last_bit_invariant 2 1 0
      (gidney_forward_faithful_full_post_state 2 (adder_input_F 2 1 0)) := by
  intro j hj
  match j, hj with
  | 0, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | _ + 2, h => omega

/-- **Decide-witness on (n=3, a=3, b=1)** (Iter 187). Multi-bit
    carry. -/
example :
    Gidney.post_last_bit_invariant 3 3 1
      (gidney_forward_faithful_full_post_state 3 (adder_input_F 3 3 1)) := by
  intro j hj
  match j, hj with
  | 0, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 2, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | _ + 3, h => omega

/-- **Parametric `post_last_bit_invariant_holds`** (Iter 188,
    2026-05-13). For any n ≥ 2 with valid bounds, applying the full
    forward cascade to `adder_input_F n a b` produces a state
    satisfying `Gidney.post_last_bit_invariant`.

    Proof strategy: destructure n = m+2, unfold via the recursive
    def's third clause to `gidney_last_bit_post_state (m+1) ∘
    gidney_propagation_post_state (m+1)`. Apply Iter 179's
    `propagation_step_invariant_holds (m+1)` for the inner state,
    extract the 4 facts at positions {c_m, c_{m+1}, r_{m+1}, t_{m+1}}.
    Apply Iter 171's `gidney_last_bit_preserves` to get post(c_{m+1})
    = c_{m+2}. For each j and each conjunct: split on j = m+1 carry
    case (use preserves) vs frame case (use Iter 173's last-bit frame
    + the propagation invariant clause, which always reduces to the
    propagated branch since j ≤ m+1 for all j < m+2). -/
theorem Gidney.post_last_bit_invariant_holds (n a b : Nat)
    (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    Gidney.post_last_bit_invariant n a b
      (gidney_forward_faithful_full_post_state n (adder_input_F n a b)) := by
  -- Destructure n = m + 2 to match the recursive def's third clause.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  show Gidney.post_last_bit_invariant (m + 2) a b
        (gidney_last_bit_post_state (m + 1)
          (gidney_propagation_post_state (m + 1) (adder_input_F (m + 2) a b)))
  -- Get propagation invariant at k = m + 1.
  have hkn : m + 1 < m + 2 := by omega
  have hn' : 1 < m + 2 := by omega
  have h_prop := Gidney.propagation_step_invariant_holds (m + 1) (m + 2) a b hkn hn' ha hb
  set f_prev := gidney_propagation_post_state (m + 1) (adder_input_F (m + 2) a b)
    with hf_prev
  -- Extract 4 facts from h_prop.
  have h_cm : f_prev (carry_idx m)
              = Adder.carry false (m + 1) a.testBit b.testBit := by
    rw [(h_prop m (by omega)).1]
    have : m < m + 1 := by omega
    simp [this]
  have h_ci : f_prev (carry_idx (m + 1)) = false := by
    rw [(h_prop (m + 1) hkn).1]
    have : ¬ (m + 1 < m + 1) := by omega
    simp [this]
  have h_ri : f_prev (read_idx (m + 1))
              = xor (a.testBit (m + 1)) (Adder.carry false (m + 1) a.testBit b.testBit) := by
    rw [(h_prop (m + 1) hkn).2.1]
    simp
  have h_ti : f_prev (target_idx (m + 1))
              = xor (b.testBit (m + 1)) (Adder.carry false (m + 1) a.testBit b.testBit) := by
    rw [(h_prop (m + 1) hkn).2.2]
    simp
  -- Apply Iter 171's gidney_last_bit_preserves at i = m + 1.
  have hi : 0 < m + 1 := by omega
  have h_lb_carry : (gidney_last_bit_post_state (m + 1) f_prev) (carry_idx (m + 1))
                    = Adder.carry false (m + 2) a.testBit b.testBit := by
    have h_cim1 : f_prev (carry_idx ((m + 1) - 1))
                  = Adder.carry false (m + 1) a.testBit b.testBit := by
      have h_eq : (m + 1) - 1 = m := by omega
      rw [h_eq]; exact h_cm
    exact gidney_last_bit_preserves (m + 1) a b hi f_prev h_ri h_ti h_cim1 h_ci
  -- Now prove the post_last_bit_invariant for each j < m + 2.
  intro j hj
  refine ⟨?_, ?_, ?_⟩
  · -- carry_j: split on j = m+1 (preserves) vs j ≠ m+1 (frame + IH)
    by_cases hjk : j = m + 1
    · subst hjk
      exact h_lb_carry
    · have h_cj_ne : carry_idx j ≠ carry_idx (m + 1) := by
        unfold carry_idx; omega
      rw [gidney_last_bit_post_state_preserves_outside _ _ _ h_cj_ne]
      rw [(h_prop j (by omega)).1]
      have h_lt : j < m + 1 := by omega
      simp [h_lt]
  · -- read_j: frame (read_j ≠ carry_{m+1} always) + IH (j ≤ m+1 always)
    have h_rj_ne : read_idx j ≠ carry_idx (m + 1) := by
      unfold read_idx carry_idx; omega
    rw [gidney_last_bit_post_state_preserves_outside _ _ _ h_rj_ne]
    rw [(h_prop j (by omega)).2.1]
    have h_le : j ≤ m + 1 := by omega
    simp [h_le]
  · -- target_j: same structure as read_j
    have h_tj_ne : target_idx j ≠ carry_idx (m + 1) := by
      unfold target_idx carry_idx; omega
    rw [gidney_last_bit_post_state_preserves_outside _ _ _ h_tj_ne]
    rw [(h_prop j (by omega)).2.2]
    have h_le : j ≤ m + 1 := by omega
    simp [h_le]

/-- **Decide-witness for the post-forward-final-CX invariant on
    (n=2, a=1, b=1)** (Iter 183). Validates the invariant on the
    instance where the original `TODO_gidney_classical_action` fails
    (per Iter 182 counterexample) — confirming the invariant matches
    the actual classical action. -/
example :
    Gidney.post_forward_final_cx_invariant 2 1 1
      (gidney_final_cx_cascade_post_state 2
        (gidney_forward_faithful_full_post_state 2 (adder_input_F 2 1 1))) := by
  intro j hj
  match j, hj with
  | 0, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | _ + 2, h => omega

/-- **Decide-witness on (n=2, a=1, b=0)** (Iter 183). The case where
    no carry is generated (c_1 = 0), so target_1 = a_1 ⊕ b_1 = 0
    happens to equal sum_1 = 0. -/
example :
    Gidney.post_forward_final_cx_invariant 2 1 0
      (gidney_final_cx_cascade_post_state 2
        (gidney_forward_faithful_full_post_state 2 (adder_input_F 2 1 0))) := by
  intro j hj
  match j, hj with
  | 0, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | _ + 2, h => omega

/-- **Decide-witness on (n=3, a=3, b=1)** (Iter 183). Multi-bit
    carry propagation. 3+1 = 4 = 100. Invariant predicts:
    target_0 = a_0 ⊕ b_0 = 0, target_1 = a_1 ⊕ b_1 = 1,
    target_2 = a_2 ⊕ b_2 = 0. Sum bits: 0, 0, 1. So target_1 differs
    from sum_1 (1 vs 0), and target_2 differs from sum_2 (0 vs 1).
    The invariant correctly captures the actual post-state. -/
example :
    Gidney.post_forward_final_cx_invariant 3 3 1
      (gidney_final_cx_cascade_post_state 3
        (gidney_forward_faithful_full_post_state 3 (adder_input_F 3 3 1))) := by
  intro j hj
  match j, hj with
  | 0, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 2, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | _ + 3, h => omega

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

/-- **Headline j=1 case for n=2** (Iter 205 PROVEN parametrically over
    a, b for n=2). Composes:
    - n=2 def unfolding: `full_reverse(2) f = first_reverse (last_reverse(1) f)`.
    - Iter 203's `gidney_last_bit_reverse_preserves_low` (positions 0-4
      unchanged by last_reverse(1)).
    - Iter 189's `post_forward_final_cx_invariant_holds` (post-CX values).
    - Iter 194's `gidney_first_bit_reverse_preserves` (target_1 = sum_1).
    - Iter 199's `Adder.sumfb_eq_testBit_add` (XOR identity). -/
theorem gidney_classical_action_with_reverse_n2_target_1 (a b : Nat)
    (ha : a < 4) (hb : b < 4) :
    gidney_full_reverse_post_state 2
      (gidney_final_cx_cascade_post_state 2
        (gidney_forward_faithful_full_post_state 2 (adder_input_F 2 a b)))
      (target_idx 1)
    = adder_sum_bit_classical a b 1 := by
  -- Set f0 first, then derive h_inv (so h_inv uses f0 form).
  set f0 := gidney_final_cx_cascade_post_state 2
              (gidney_forward_faithful_full_post_state 2 (adder_input_F 2 a b))
              with hf0
  have h_inv : Gidney.post_forward_final_cx_invariant 2 a b f0 :=
    Gidney.post_forward_final_cx_invariant_holds 2 a b
      (by decide) (by simpa) (by simpa)
  set f1 := gidney_last_bit_reverse_post_state 1 f0 with hf1
  -- Verify Iter 194's hypotheses for f1 at positions {0, 1, 2, 3, 4}.
  have h_r0 : f1 (read_idx 0) = a.testBit 0 := by
    show gidney_last_bit_reverse_post_state 1 f0 (read_idx 0) = _
    rw [gidney_last_bit_reverse_preserves_low 1 (by omega) _
          (by unfold read_idx; omega) f0]
    rw [(h_inv 0 (by omega)).2.1]
    simp [Adder.carry]
  have h_t0 : f1 (target_idx 0) = xor (a.testBit 0) (b.testBit 0) := by
    show gidney_last_bit_reverse_post_state 1 f0 (target_idx 0) = _
    rw [gidney_last_bit_reverse_preserves_low 1 (by omega) _
          (by unfold target_idx; omega) f0]
    exact (h_inv 0 (by omega)).2.2
  have h_c0 : f1 (carry_idx 0) = Adder.carry false 1 a.testBit b.testBit := by
    show gidney_last_bit_reverse_post_state 1 f0 (carry_idx 0) = _
    rw [gidney_last_bit_reverse_preserves_low 1 (by omega) _
          (by unfold carry_idx; omega) f0]
    exact (h_inv 0 (by omega)).1
  have h_r1 : f1 (read_idx 1)
              = xor (a.testBit 1) (Adder.carry false 1 a.testBit b.testBit) := by
    show gidney_last_bit_reverse_post_state 1 f0 (read_idx 1) = _
    rw [gidney_last_bit_reverse_preserves_low 1 (by omega) _
          (by unfold read_idx; omega) f0]
    exact (h_inv 1 (by omega)).2.1
  have h_t1 : f1 (target_idx 1) = xor (a.testBit 1) (b.testBit 1) := by
    show gidney_last_bit_reverse_post_state 1 f0 (target_idx 1) = _
    rw [gidney_last_bit_reverse_preserves_low 1 (by omega) _
          (by unfold target_idx; omega) f0]
    exact (h_inv 1 (by omega)).2.2
  -- Apply Iter 194's first_bit_reverse_preserves on f1.
  have h_fr := gidney_first_bit_reverse_preserves a b f1 h_r0 h_t0 h_c0 h_r1 h_t1
  -- full_reverse(2) f0 = first_reverse (last_reverse(1) f0) = first_reverse f1.
  show gidney_first_bit_reverse_post_state f1 (target_idx 1) = adder_sum_bit_classical a b 1
  rw [h_fr.2.2]
  -- Goal: xor (xor a_1 b_1) c_1 = adder_sum_bit_classical a b 1.
  unfold adder_sum_bit_classical
  rw [← Adder.sumfb_eq_testBit_add]
  unfold Adder.sumfb
  -- Goal: xor (xor a_1 b_1) c_1 = xor (xor c_1 a_1) b_1. XOR commute.
  dsimp only
  cases a.testBit 1 <;> cases b.testBit 1 <;>
    cases (Adder.carry false 1 a.testBit b.testBit) <;> rfl

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
