/-
  FormalRV.Arithmetic.RippleCarryAdder.ClassicalBridge.InputEval
  Part 3/4: `adder_input_F` position-evaluation lemmas, the k=0 cascade base
  case, and the last-bit bit-extraction helper. Builds on `SumfbTestBit`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.ClassicalBridge.SumfbTestBit

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-! ### Per-bit-step preservation lemma skeletons (Iter 160, 2026-05-13)

    Per the proof decomposition in AutoScript/goal.md, the
    SQIR-style induction over n requires per-bit-step preservation
    lemmas. Three step types (first / interior / last), each takes
    a step-i invariant + the corresponding gate-step's classical
    action (`gidney_first_bit_post_state`, etc.) and produces the
    step-(i+1) invariant.

    This tick STATES the three preservation lemmas as named
    placeholders. Future ticks prove each (likely via case analysis
    on `a_i`, `b_i`, `c_i` — each `Bool` has 2 values, so 8 inner
    cases per step type, decide-able once unfolded).

    These follow SQIR's MAJseq'_correct induction structure:
    base case = first-bit-step preservation (analog of MAJ at i=0);
    inductive step = interior-bit preservation (analog of MAJ at i+1).
    Last-bit step is the n=n termination, no analog needed in SQIR
    because Cuccaro is uniform. -/

/-- **Preliminary lemma** (partial — bottom 3 positions only):
    `adder_input_F n a b` evaluates as expected at qubit indices
    0, 1, 2 (positions handled by the first-bit step). -/
theorem adder_input_F_at_bottom (n a b : Nat) :
    adder_input_F n a b 2 = false := rfl

/-- **`adder_input_F` at `read_idx j`**: evaluates to
    `a.testBit j` when `j < n`. -/
theorem adder_input_F_at_read_idx
    (n a b j : Nat) (hj : j < n) :
    adder_input_F n a b (read_idx j) = a.testBit j := by
  have h_mod : (read_idx j) % 3 = 0 := by unfold read_idx; omega
  have h_div : (read_idx j) / 3 = j := by unfold read_idx; omega
  show (match (read_idx j) % 3 with
        | 0 => decide ((read_idx j) / 3 < n) && a.testBit ((read_idx j) / 3)
        | 1 => decide ((read_idx j) / 3 < n) && b.testBit ((read_idx j) / 3)
        | _ => false) = a.testBit j
  rw [h_mod, h_div]
  simp [hj]

/-- **`adder_input_F` at `target_idx j`**: evaluates to
    `b.testBit j` when `j < n`. -/
theorem adder_input_F_at_target_idx
    (n a b j : Nat) (hj : j < n) :
    adder_input_F n a b (target_idx j) = b.testBit j := by
  have h_mod : (target_idx j) % 3 = 1 := by unfold target_idx; omega
  have h_div : (target_idx j) / 3 = j := by unfold target_idx; omega
  show (match (target_idx j) % 3 with
        | 0 => decide ((target_idx j) / 3 < n) && a.testBit ((target_idx j) / 3)
        | 1 => decide ((target_idx j) / 3 < n) && b.testBit ((target_idx j) / 3)
        | _ => false) = b.testBit j
  rw [h_mod, h_div]
  simp [hj]

/-- **`adder_input_F` at `carry_idx j`**: always `false` (carry
    register starts clean). No bound on `j` needed. -/
theorem adder_input_F_at_carry_idx
    (n a b j : Nat) :
    adder_input_F n a b (carry_idx j) = false := by
  have h_mod : (carry_idx j) % 3 = 2 := by unfold carry_idx; omega
  show (match (carry_idx j) % 3 with
        | 0 => decide ((carry_idx j) / 3 < n) && a.testBit ((carry_idx j) / 3)
        | 1 => decide ((carry_idx j) / 3 < n) && b.testBit ((carry_idx j) / 3)
        | _ => false) = false
  rw [h_mod]

/-- **`adder_input_F` evaluation at the 5 first-bit-step positions**
    (Iter 165). Closes the gap between `adder_input_F n a b` (which
    is parameterized by Nat `n a b`) and `(a.testBit 0, b.testBit 0,
    false, a.testBit 1, b.testBit 1)` (which is pure Bool).

    The hypothesis `hn : 1 < n` is needed for positions 3 and 4
    (where `k / 3 = 1`, so `decide (1 < n) = true` is required to
    reduce the `decide` guard).

    Together with `gidney_first_bit_post_state_in_bits` (Iter 164),
    this unblocks the proof of `TODO_gidney_first_bit_preserves`. -/
theorem adder_input_F_at_first_bit_positions
    (n a b : Nat) (hn : 1 < n) :
    adder_input_F n a b 0 = a.testBit 0
    ∧ adder_input_F n a b 1 = b.testBit 0
    ∧ adder_input_F n a b 2 = false
    ∧ adder_input_F n a b 3 = a.testBit 1
    ∧ adder_input_F n a b 4 = b.testBit 1 := by
  have h0 : (0 : Nat) < n := by omega
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · -- adder_input_F at 0: match 0%3=0, so `decide (0<n) && a.testBit 0`
    show (decide (0 < n) && a.testBit 0) = a.testBit 0
    simp [h0]
  · show (decide (0 < n) && b.testBit 0) = b.testBit 0
    simp [h0]
  · show (decide (1 < n) && a.testBit 1) = a.testBit 1
    simp [hn]
  · show (decide (1 < n) && b.testBit 1) = b.testBit 1
    simp [hn]

/-- **Base case k=0 of the cascade induction** (Iter 176, PROVEN).
    The invariant `Gidney.propagation_step_invariant 0 n a b`
    holds for the input `adder_input_F n a b`.

    `propagation_post_state 0 f = f`, so this reduces to showing
    `adder_input_F` has the right values at all positions. Uses
    the 3 evaluation lemmas above. -/
theorem Gidney.propagation_step_invariant_base_k0
    (n a b : Nat) (_ha : a < 2^n) (_hb : b < 2^n) :
    Gidney.propagation_step_invariant 0 n a b
      (gidney_propagation_post_state 0 (adder_input_F n a b)) := by
  show Gidney.propagation_step_invariant 0 n a b (adder_input_F n a b)
  intro j hj
  refine ⟨?_, ?_, ?_⟩
  · rw [adder_input_F_at_carry_idx]
    simp  -- j < 0 is false
  · rw [adder_input_F_at_read_idx _ _ _ _ hj]
    by_cases hj0 : j ≤ 0
    · have : j = 0 := by omega
      subst this
      simp [Adder.carry]
    · simp [hj0]
  · rw [adder_input_F_at_target_idx _ _ _ _ hj]
    by_cases hj0 : j ≤ 0
    · have : j = 0 := by omega
      subst this
      simp [Adder.carry]
    · simp [hj0]

-- Gidney.propagation_step_invariant_k1 moved to after
-- gidney_first_bit_preserves below (forward-reference fix).

/-- **Last-bit smoke-test** (Iter 169): apply `gidney_last_bit_post_state` at
    i=1 to the post-first-bit state of `inputF_1_plus_1` (2-bit adder).
    Expected: carry_1 = MAJ(0, 0, 1) = 0 (chain CX cancels CCX write).

    Note: `gidney_last_bit_post_state` was originally defined at
    line 1081 (Iter 67). This tick adds the bit-extraction lemma. -/
example :
    let pre := gidney_first_bit_post_state inputF_1_plus_1
    let post := gidney_last_bit_post_state 1 pre
    post (carry_idx 1) = false
    := by decide

/-- **Bit-extraction helper for last-bit step** (Iter 169).
    Mirrors Iter 164 (first-bit) and Iter 167 (interior). Last
    step has only 2 gates; single conjunct (only carry_i is
    touched). -/
theorem gidney_last_bit_post_state_in_bits
    (i : Nat) (hi : 0 < i) (f : Nat → Bool)
    (h_cinit : f (carry_idx i) = false) :
    (gidney_last_bit_post_state i f) (carry_idx i)
      = xor (f (read_idx i) && f (target_idx i)) (f (carry_idx (i - 1))) := by
  have h_cim1_ci : carry_idx (i - 1) ≠ carry_idx i := by
    unfold carry_idx; omega
  unfold gidney_last_bit_post_state
  -- 2 updates: gate 1 (CCX writes c_i), gate 2 (chain CX adds c_{i-1}).
  rw [update_eq,                              -- f₂ at c_i = (f₁ at c_i) ⊕ (f₁ at c_{i-1})
      update_eq,                              -- f₁ at c_i = f(c_i) ⊕ (f(r_i) ∧ f(t_i))
      update_neq _ _ _ _ h_cim1_ci,         -- f₁ at c_{i-1} = f at c_{i-1}
      h_cinit]
  simp

end FormalRV.BQAlgo
