/-
  FormalRV.Arithmetic.RippleCarryAdder.DecideWitnesses.ForwardInvariant
  Part 1/4: forward-cascade decide smoke-witnesses and the parametric
  `Gidney.post_last_bit_invariant_holds`. Supporting lemmas; the reverse
  headline backbone is `ReverseFramesAndHeadline`.
-/
import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Framework.PaperClaims
import FormalRV.PPM.Magic.GidneyAND
import Mathlib.Tactic.IntervalCases
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderDef
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderClassicalBridge

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

end FormalRV.BQAlgo
