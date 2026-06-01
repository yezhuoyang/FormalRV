/-
  FormalRV.BQAlgo.CuccaroSQIRDirtyFlag — dirty-flag SQIR-style
  modular-add-constant target theorem.

  Tick 58: prove the dirty-flag mod-N candidate computes
  `(x + c) % N` under the precondition `2*N ≤ 2^bits`.

  Structure of the proof:
  1. Arithmetic theorem: for x, c < N and 2*N ≤ 2^bits, the expression
     `(x + c + (if decide (N ≤ x+c) then 2^bits - N else 0)) % 2^bits`
     equals `(x + c) % N`.
  2. Function-level equality bridge: post-addConst state on
     `cuccaro_input_F q_start false 0 x` equals
     `cuccaro_input_F q_start false 0 (x+c)` (when `x+c < 2^bits`).
  3. The dirty-flag target theorem by composing the above with
     compareConst's flag theorem and conditionalSub's target_decode.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRCondAdd

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Deliverable A — Arithmetic theorem for dirty-flag modular reduction. -/

/-- **HEADLINE Deliverable A — dirty-flag modular reduction arithmetic.**
For `x, c < N` and `2*N ≤ 2^bits`,
`(x + c + (if decide (N ≤ x+c) then 2^bits - N else 0)) % 2^bits = (x + c) % N`. -/
theorem sqir_dirty_modadd_arith
    (bits N x c : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    (x + c + (if decide (N ≤ x + c) then 2^bits - N else 0)) % 2^bits
      = (x + c) % N := by
  by_cases h : N ≤ x + c
  · -- Underflow case: x + c ∈ [N, 2N).
    rw [if_pos (by simp [h] : decide (N ≤ x + c) = true)]
    have h_xc_ub : x + c < 2 * N := by omega
    have h_eq : x + c + (2^bits - N) = (x + c - N) + 2^bits := by omega
    rw [h_eq, Nat.add_mod_right]
    have h_lt : x + c - N < 2^bits := by omega
    rw [Nat.mod_eq_of_lt h_lt]
    -- (x + c) % N = x + c - N when N ≤ x+c < 2N.
    have h_xcN : (x + c) % N = x + c - N := by
      conv_lhs => rw [show x + c = N + (x + c - N) from by omega]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : x + c - N < N)]
    rw [h_xcN]
  · -- No underflow: x + c < N.
    push_neg at h
    rw [if_neg (by simp [Nat.not_le.mpr h] : ¬ decide (N ≤ x + c) = true)]
    have h_xc_lt : x + c < 2^bits := by omega
    rw [Nat.add_zero]
    rw [Nat.mod_eq_of_lt h_xc_lt]
    rw [Nat.mod_eq_of_lt h]

/-! ## Deliverable B — Function-level equality: post-addConst state. -/

/-- **HEADLINE — post-addConst function equality.**  Applying
`cuccaro_addConstGate bits q_start c` to `cuccaro_input_F q_start false 0 x`
gives `cuccaro_input_F q_start false 0 (x+c)` as a function, provided
`x + c < 2^bits`. -/
theorem cuccaro_addConstGate_output_eq_cuccaro_input_F
    (bits q_start c x : Nat) (hbits : 1 ≤ bits)
    (hc : c < 2^bits) (hx : x < 2^bits) (h_sum : x + c < 2^bits) :
    Gate.applyNat (cuccaro_addConstGate bits q_start c)
        (cuccaro_input_F q_start false 0 x)
      = cuccaro_input_F q_start false 0 (x + c) := by
  funext q
  -- Helper: compute applyNat addConst at q via prepare+adder+prepare frame.
  by_cases h_q_below : q < q_start
  · -- q < q_start.  addConst frames; both inputs give false.
    show Gate.applyNat (seq (cuccaro_prepareConstRead bits q_start c)
            (seq (cuccaro_n_bit_adder_full bits q_start)
                 (cuccaro_prepareConstRead bits q_start c)))
          (cuccaro_input_F q_start false 0 x) q = _
    simp only [Gate.applyNat_seq]
    rw [cuccaro_prepareConstRead_at_other bits q_start c q
        (by intros j _ heq; omega)]
    rw [cuccaro_n_bit_adder_full_frame_below bits q_start _ q h_q_below]
    rw [cuccaro_prepareConstRead_at_other bits q_start c q
        (by intros j _ heq; omega)]
    -- LHS = input at q = cuccaro_input_F at q.
    -- For q < q_start, both cuccaro_input_F give false.
    unfold cuccaro_input_F
    rw [if_pos h_q_below, if_pos h_q_below]
  · push_neg at h_q_below
    by_cases h_q_zero : q = q_start
    · -- q = q_start (carry-in).
      rw [h_q_zero]
      rw [cuccaro_addConstGate_carry_in_bit bits q_start c x]
      exact (cuccaro_input_F_at_c_in q_start false 0 (x + c)).symm
    · by_cases h_q_above : q_start + 2 * bits + 1 ≤ q
      · -- q above workspace.
        show Gate.applyNat (seq (cuccaro_prepareConstRead bits q_start c)
                (seq (cuccaro_n_bit_adder_full bits q_start)
                     (cuccaro_prepareConstRead bits q_start c)))
              (cuccaro_input_F q_start false 0 x) q = _
        simp only [Gate.applyNat_seq]
        rw [cuccaro_prepareConstRead_at_other bits q_start c q
            (by intros j _ heq; omega)]
        rw [cuccaro_n_bit_adder_full_frame_above bits q_start _ q h_q_above]
        rw [cuccaro_prepareConstRead_at_other bits q_start c q
            (by intros j _ heq; omega)]
        -- Both cuccaro_input_F at q ≥ q_start + 2*bits + 1: false.
        unfold cuccaro_input_F
        rw [if_neg (Nat.not_lt.mpr h_q_below), if_neg (Nat.not_lt.mpr h_q_below)]
        have hi_ne_zero : q - q_start ≠ 0 := by omega
        rw [if_neg hi_ne_zero, if_neg hi_ne_zero]
        by_cases h_odd : (q - q_start) % 2 = 1
        · rw [if_pos h_odd, if_pos h_odd]
          have h_idx : (q - q_start - 1) / 2 ≥ bits := by omega
          have h_x_bit : x.testBit ((q - q_start - 1) / 2) = false := by
            apply Nat.testBit_lt_two_pow
            exact Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) h_idx)
          have h_xc_bit : (x + c).testBit ((q - q_start - 1) / 2) = false := by
            apply Nat.testBit_lt_two_pow
            exact Nat.lt_of_lt_of_le h_sum (Nat.pow_le_pow_right (by omega) h_idx)
          rw [h_x_bit, h_xc_bit]
        · rw [if_neg h_odd, if_neg h_odd]
      · -- q in workspace [q_start + 1, q_start + 2*bits + 1).
        push_neg at h_q_above
        by_cases h_odd : (q - q_start) % 2 = 1
        · -- target position: q = q_start + 2*j + 1 for some j < bits.
          have hj_exists : ∃ j, j < bits ∧ q = q_start + 2 * j + 1 := by
            refine ⟨(q - q_start - 1) / 2, ?_, ?_⟩
            · omega
            · omega
          obtain ⟨j, hj, hq_eq⟩ := hj_exists
          rw [hq_eq]
          rw [cuccaro_addConstGate_target_bit bits q_start c x j hj hc]
          rw [cuccaro_input_F_at_b q_start j false 0 (x + c)]
        · -- read or top-a position.
          have hj_exists : ∃ j, q = q_start + 2 * j + 2 ∧ j < bits := by
            refine ⟨(q - q_start - 2) / 2, ?_, ?_⟩
            · omega
            · omega
          obtain ⟨j, hq_eq, hj⟩ := hj_exists
          rw [hq_eq]
          rw [cuccaro_addConstGate_read_bit bits q_start c x j hj]
          rw [cuccaro_input_F_at_a q_start j false 0 (x + c)]
          simp [Nat.zero_testBit]

/-! ## Tick 59 — Deliverable A: post-add state with external flag.

Combines `cuccaro_addConstGate_commute_update_outside_workspace`
(Tick 57) with the function equality (this file) to derive the
post-add state on an `update`-form input. -/

/-- **HEADLINE Deliverable A — post-add state with external flag.** -/
theorem sqir_dirty_modadd_after_add_state_eq
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (cuccaro_addConstGate bits q_start c)
        (update (cuccaro_input_F q_start false 0 x) flagPos false)
      = update (cuccaro_input_F q_start false 0 (x + c)) flagPos false := by
  rw [cuccaro_addConstGate_commute_update_outside_workspace bits q_start c flagPos false
        (cuccaro_input_F q_start false 0 x) hflag_out]
  congr 1
  apply cuccaro_addConstGate_output_eq_cuccaro_input_F
  · exact hbits
  · omega  -- c < 2^bits
  · omega  -- x < 2^bits
  · omega  -- x + c < 2^bits

/-! ## Tick 59 — Frame for compareConst at outside positions. -/

/-- **`sqir_style_compareConst_candidate` frame at positions outside
workspace ∪ {flagPos}.**

Layer order after `simp [applyNat_seq]` (outermost first):
prepare₂ → maj_inv → CX → maj → prepare₁.  We strip from the outside in. -/
theorem sqir_style_compareConst_candidate_frame_outside
    (bits q_start N flagPos : Nat) (f : Nat → Bool)
    (q : Nat) (h_q_ne_flagPos : q ≠ flagPos)
    (h_q_outside : q < q_start ∨ q_start + 2 * bits + 1 ≤ q) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos) f q = f q := by
  show Gate.applyNat
      (seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (cuccaro_prepareConstRead bits q_start (2^bits - N))))))
      f q = _
  simp only [Gate.applyNat_seq]
  -- Build the "q is not a read position" hypothesis once.
  have h_q_not_read : ∀ j, j < bits → q ≠ q_start + 2 * j + 2 := by
    intros j _ heq
    rcases h_q_outside with hl | hr
    · omega
    · omega
  -- Strip outermost: prepare₂.
  rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) q h_q_not_read]
  -- Strip maj_inv.
  rcases h_q_outside with h_q_below | h_q_above
  · rw [cuccaro_maj_chain_inv_frame_below bits q_start _ q h_q_below]
    -- Strip CX at q ≠ flagPos.
    rw [Gate.applyNat_CX]
    rw [update_neq _ _ _ _ h_q_ne_flagPos]
    -- Strip maj_chain.
    rw [cuccaro_maj_chain_frame_below bits q_start _ q h_q_below]
    -- Strip prepare₁.
    exact cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) q h_q_not_read f
  · rw [cuccaro_maj_chain_inv_frame_above bits q_start _ q h_q_above]
    rw [Gate.applyNat_CX]
    rw [update_neq _ _ _ _ h_q_ne_flagPos]
    rw [cuccaro_maj_chain_frame_above bits q_start _ q h_q_above]
    exact cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) q h_q_not_read f

/-! ## Tick 59 — Deliverable B: post-compare state. -/

/-- **HEADLINE Deliverable B — post-compare state with external flag.** -/
theorem sqir_dirty_modadd_after_compare_state_eq
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (update (cuccaro_input_F q_start false 0 (x + c)) flagPos false)
      = update (cuccaro_input_F q_start false 0 (x + c)) flagPos (decide (N ≤ x + c)) := by
  -- update at flagPos with false is no-op (input is already false there).
  have h_input_at_flagPos : cuccaro_input_F q_start false 0 (x + c) flagPos = false := by
    apply cuccaro_input_F_above_eq_false q_start bits (x + c) flagPos h_flag_above
    omega
  have h_input_eq : update (cuccaro_input_F q_start false 0 (x + c)) flagPos false
                  = cuccaro_input_F q_start false 0 (x + c) := by
    funext q
    by_cases hq : q = flagPos
    · rw [hq, update_eq]; exact h_input_at_flagPos.symm
    · rw [update_neq _ _ _ _ hq]
  rw [h_input_eq]
  funext q
  by_cases hq : q = flagPos
  · rw [hq, update_eq]
    exact sqir_style_compareConst_candidate_flag bits q_start N (x + c) flagPos
      hN_pos hN (by omega) h_flag_above
  · rw [update_neq _ _ _ _ hq]
    by_cases h_q_workspace : q_start ≤ q ∧ q < q_start + 2 * bits + 1
    · exact sqir_style_compareConst_candidate_workspace_restored_at bits q_start N flagPos
        _ h_flag_above q h_q_workspace.1 h_q_workspace.2
    · push_neg at h_q_workspace
      have h_q_outside : q < q_start ∨ q_start + 2 * bits + 1 ≤ q := by
        by_cases h : q < q_start
        · left; exact h
        · push_neg at h
          right; exact h_q_workspace h
      exact sqir_style_compareConst_candidate_frame_outside bits q_start N flagPos
        _ q hq h_q_outside

/-! ## Tick 59 — Deliverables C+D: dirty-flag target theorem. -/

/-- **HEADLINE Deliverable D — dirty-flag mod-N target decode.** -/
theorem sqir_style_modAddConst_dirtyFlag_target_decode
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false))
      = (x + c) % N := by
  -- Unfold candidate.
  show cuccaro_target_val bits q_start
      (Gate.applyNat
        (seq (cuccaro_addConstGate bits q_start c)
              (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                   (sqir_conditionalSubConstGate bits q_start N flagPos)))
        (update (cuccaro_input_F q_start false 0 x) flagPos false)) = _
  simp only [Gate.applyNat_seq]
  -- Apply Deliverables A and B to simplify the state.
  have hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos :=
    Or.inr h_flag_above
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct h_flag_above]
  -- Now apply conditionalSub target_decode.
  rw [sqir_conditionalSubConstGate_target_decode bits q_start N (x + c) flagPos
        (decide (N ≤ x + c)) hbits hN_pos hN (by omega : x + c < 2^bits)
        h_flag_distinct hflag_out]
  -- Apply arithmetic.
  exact sqir_dirty_modadd_arith bits N x c hN_pos hN hN2 hx hc

/-! ## Tick 60 — Workspace theorem for the dirty-flag candidate.

After the candidate, the read register and carry-in are restored to
zero, and the flag holds `decide (N ≤ x + c)`.  These follow by
composing Tick 59 Deliverables A and B with the SQIR-style
conditionalAdd's workspace/flag lemmas (with `K := 2^bits - N`). -/

/-- **HEADLINE Deliverable A — read register restored after the
dirty-flag candidate.** -/
theorem sqir_style_modAddConst_dirtyFlag_read_decode
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_read_val bits q_start
        (Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false))
      = 0 := by
  show cuccaro_read_val bits q_start
      (Gate.applyNat
        (seq (cuccaro_addConstGate bits q_start c)
              (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                   (sqir_conditionalSubConstGate bits q_start N flagPos)))
        (update (cuccaro_input_F q_start false 0 x) flagPos false)) = _
  simp only [Gate.applyNat_seq]
  have hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos :=
    Or.inr h_flag_above
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct h_flag_above]
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_read_decode bits q_start (2^bits - N) (x + c) flagPos
      (decide (N ≤ x + c)) hbits (by omega) (by omega) h_flag_distinct hflag_out

/-- **HEADLINE Deliverable A (continued) — carry-in restored.** -/
theorem sqir_style_modAddConst_dirtyFlag_carry_in_restored
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos false) q_start
      = false := by
  show Gate.applyNat
      (seq (cuccaro_addConstGate bits q_start c)
            (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                 (sqir_conditionalSubConstGate bits q_start N flagPos)))
      (update (cuccaro_input_F q_start false 0 x) flagPos false) q_start = _
  simp only [Gate.applyNat_seq]
  have hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos :=
    Or.inr h_flag_above
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct h_flag_above]
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_carry_in_restored bits q_start (2^bits - N) (x + c) flagPos
      (decide (N ≤ x + c)) hbits (by omega) (by omega) h_flag_distinct hflag_out

/-- **HEADLINE Deliverable A (continued) — flag holds `decide (N ≤ x + c)`.**
The flag is DIRTY: it stores the comparison result, not the input
`false`.  Naming the field `dirtyFlag` is mandatory; do not advertise
this as clean modular addition. -/
theorem sqir_style_modAddConst_dirtyFlag_flag_value
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos
      = decide (N ≤ x + c) := by
  show Gate.applyNat
      (seq (cuccaro_addConstGate bits q_start c)
            (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                 (sqir_conditionalSubConstGate bits q_start N flagPos)))
      (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos = _
  simp only [Gate.applyNat_seq]
  have hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos :=
    Or.inr h_flag_above
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct h_flag_above]
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_flag_preserved bits q_start (2^bits - N) (x + c) flagPos
      (decide (N ≤ x + c)) h_flag_distinct hflag_out

/-! ## Tick 60 — Deliverable B: WellTyped at SQIR-faithful dimension. -/

/-- **HEADLINE Deliverable B — WellTyped at the SQIR-faithful dimension
`sqir_modmult_rev_anc bits = 3 * bits + 11`.** -/
theorem sqir_style_modAddConst_dirtyFlag_candidate_wellTyped_sqir_dim
    (bits q_start N c flagPos : Nat) (hbits : 1 ≤ bits)
    (h_workspace : q_start + 2 * bits + 1 ≤ sqir_modmult_rev_anc bits)
    (h_flag : flagPos < sqir_modmult_rev_anc bits)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_distinct_top : flagPos ≠ q_start + 2 * bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos) :=
  sqir_style_modAddConst_dirtyFlag_candidate_wellTyped bits q_start N c flagPos
    (sqir_modmult_rev_anc bits) h_workspace h_flag h_flag_distinct h_flag_distinct_top

/-! ## Tick 60 — Deliverable C: clean-except-flag bundle. -/

/-- **HEADLINE Deliverable C — packaged dirty-flag mod-N add bundle.**
Provides WellTyped, target decode, read restored, carry restored,
and the dirty flag value, all under the dirty-flag precondition set
(2*N ≤ 2^bits, x < N, c < N, flagPos above workspace). -/
theorem sqir_style_modAddConst_dirtyFlag_clean_except_flag
    (bits q_start N c x flagPos dim : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.WellTyped dim
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
            (update (cuccaro_input_F q_start false 0 x) flagPos false))
        = (x + c) % N
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
            (update (cuccaro_input_F q_start false 0 x) flagPos false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false) q_start
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos
        = decide (N ≤ x + c) := by
  have h_flag_distinct_top : flagPos ≠ q_start + 2 * bits := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact sqir_style_modAddConst_dirtyFlag_candidate_wellTyped bits q_start N c flagPos dim
      h_workspace h_flag h_flag_distinct h_flag_distinct_top
  · exact sqir_style_modAddConst_dirtyFlag_target_decode bits q_start N c x flagPos
      hbits hN_pos hN hN2 hx hc h_flag_distinct h_flag_above
  · exact sqir_style_modAddConst_dirtyFlag_read_decode bits q_start N c x flagPos
      hbits hN_pos hN hN2 hx hc h_flag_distinct h_flag_above
  · exact sqir_style_modAddConst_dirtyFlag_carry_in_restored bits q_start N c x flagPos
      hbits hN_pos hN hN2 hx hc h_flag_distinct h_flag_above
  · exact sqir_style_modAddConst_dirtyFlag_flag_value bits q_start N c x flagPos
      hbits hN_pos hN hN2 hx hc h_flag_distinct h_flag_above

/-! ## Tick 60 — Deliverable D: SQIR-layout WellTyped specialization.

The SQIR-exact layout uses `q_start = 2`, `flagPos = 1`, and the
SQIR-faithful dimension `sqir_modmult_rev_anc bits = 3 * bits + 11`.
This layout places the flag BELOW the workspace.  We can prove
WellTyped at this layout directly — but the semantic theorems
(target_decode, workspace) currently require `h_flag_above`, since
the SQIR-style comparator's flag theorem was set up with flag above
workspace.  Extending the semantic theorems to handle below-workspace
flag is deferred to a later tick (it requires adapting
`sqir_style_compareConst_candidate_flag` and the corresponding
workspace_restored / frame_outside lemmas).  See the "Honesty
disclosures" section below. -/

/-- **Deliverable D (partial) — WellTyped at the exact SQIR layout
`q_start = 2, flagPos = 1, dim = sqir_modmult_rev_anc bits`.** -/
theorem sqir_style_modAddConst_dirtyFlag_candidate_wellTyped_sqir_layout
    (bits N c : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1) := by
  apply sqir_style_modAddConst_dirtyFlag_candidate_wellTyped bits 2 N c 1
    (sqir_modmult_rev_anc bits)
  · unfold sqir_modmult_rev_anc; omega
  · unfold sqir_modmult_rev_anc; omega
  · intros i _; omega
  · omega

/-! ## Tick 60 — Deliverable E: sizing relation from `BasicSetting`.

`BasicSetting` (Shor.lean §3) provides `N < 2^n ≤ 2 * N`.  The dirty-
flag mod-N add requires `2 * N ≤ 2^bits`.  Choosing `bits := n + 1`
yields `2 * N ≤ 2^(n + 1)` directly from `N < 2^n`.  Trying to use
`bits = n` does NOT work, since `2^n ≤ 2 * N` runs the wrong way. -/

/-- **HEADLINE Deliverable E — sizing relation: `BasicSetting a r N m n`
implies `2 * N ≤ 2^(n + 1)`.**

Reading: Shor's data register width is `n` bits; the dirty-flag
modular adder must be instantiated at `bits := n + 1` (one extra
bit) so that intermediate `x + c` cannot overflow before the
comparator sees the top carry.  This matches SQIR's `n + 1`-bit
workspace per modular addition. -/
theorem BasicSetting_twoN_le_pow_succ
    (a r N m n : Nat)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n) :
    2 * N ≤ 2 ^ (n + 1) := by
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨_, _, _, hN_lt, _⟩ := h_basic
  have h2 : 2 * N < 2 ^ (n + 1) := by
    calc 2 * N < 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]; ring
  omega

/-! ## Tick 61 — Below-workspace flag generalizations + SQIR-exact layout.

The semantic theorems landed in Ticks 59–60 require
`h_flag_above : q_start + 2*bits + 1 ≤ flagPos`.  The SQIR-exact
layout has `q_start = 2, flagPos = 1`, putting the flag BELOW
workspace.  We provide `_general` variants that accept the
disjunction, then `_sqir_layout` corollaries. -/

/-- Helper: `cuccaro_input_F q_start false 0 x` evaluates to `false`
at any position outside the workspace `[q_start, q_start + 2*bits]`. -/
theorem cuccaro_input_F_at_outside_eq_false
    (q_start bits x flagPos : Nat)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hx : x < 2^bits) :
    cuccaro_input_F q_start false 0 x flagPos = false := by
  rcases hflag_out with h | h
  · unfold cuccaro_input_F
    rw [if_pos h]
  · exact cuccaro_input_F_above_eq_false q_start bits x flagPos h hx

/-- **Generalized flag-copy theorem.**  For any `flagPos` outside the
workspace (below OR above), the SQIR-style comparator candidate outputs
`decide (N ≤ x)` at `flagPos`. -/
theorem sqir_style_compareConst_candidate_flag_general
    (bits q_start N x flagPos : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (cuccaro_input_F q_start false 0 x) flagPos
      = decide (N ≤ x) := by
  rcases hflag_out with h_below | h_above
  · -- Below-workspace flag.  Mirror the existing above-case proof with `_below` frames.
    show Gate.applyNat
        (seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
              (seq (cuccaro_maj_chain bits q_start)
                   (seq (Gate.CX (q_start + 2 * bits) flagPos)
                        (seq (cuccaro_maj_chain_inv bits q_start)
                             (cuccaro_prepareConstRead bits q_start (2^bits - N))))))
        (cuccaro_input_F q_start false 0 x) flagPos = _
    simp only [Gate.applyNat_seq]
    have h_flagPos_not_read : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2 := by
      intros j _ heq; omega
    rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) flagPos h_flagPos_not_read]
    rw [cuccaro_maj_chain_inv_frame_below bits q_start _ flagPos h_below]
    simp only [Gate.applyNat_CX, update_eq]
    have h_flag_state : Gate.applyNat (cuccaro_maj_chain bits q_start)
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N))
          (cuccaro_input_F q_start false 0 x)) flagPos = false := by
      rw [cuccaro_maj_chain_frame_below bits q_start _ flagPos h_below]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) flagPos h_flagPos_not_read]
      unfold cuccaro_input_F
      rw [if_pos h_below]
    rw [h_flag_state]
    simp only [Bool.false_xor]
    have h_carry := cuccaro_compareConstForward_top_carry bits q_start N x hN_pos hN hx
    unfold cuccaro_compareConstForwardGate at h_carry
    simp only [Gate.applyNat_seq] at h_carry
    exact h_carry
  · exact sqir_style_compareConst_candidate_flag bits q_start N x flagPos
      hN_pos hN hx h_above

/-- **Generalized workspace restoration (at-position).**  At any
workspace position, the SQIR-style comparator candidate restores
the input value, for any `flagPos` outside workspace. -/
theorem sqir_style_compareConst_candidate_workspace_restored_at_general
    (bits q_start N flagPos : Nat) (f : Nat → Bool)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (q : Nat) (hq_lower : q_start ≤ q) (hq_upper : q < q_start + 2 * bits + 1) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos) f q
      = f q := by
  show Gate.applyNat
      (seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (cuccaro_prepareConstRead bits q_start (2^bits - N))))))
      f q = _
  simp only [Gate.applyNat_seq, Gate.applyNat_CX]
  by_cases hq_read : ∃ i, i < bits ∧ q = q_start + 2 * i + 2
  · obtain ⟨i, hi, hq_eq⟩ := hq_read
    rw [hq_eq]
    rw [cuccaro_prepareConstRead_at_read bits q_start (2^bits - N) i hi]
    rw [cuccaro_maj_chain_inv_commute_update_outside_workspace
          bits q_start flagPos _ _ hflag_out
          (q_start + 2 * i + 2) (by omega) (by omega)]
    rw [show Gate.applyNat (cuccaro_maj_chain_inv bits q_start)
          (Gate.applyNat (cuccaro_maj_chain bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f))
          (q_start + 2 * i + 2)
          = Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f
              (q_start + 2 * i + 2) from ?_]
    · rw [cuccaro_prepareConstRead_at_read bits q_start (2^bits - N) i hi]
      cases f (q_start + 2 * i + 2) <;> cases (2^bits - N).testBit i <;> rfl
    · rw [cuccaro_maj_chain_inv_after_chain_eq_id bits q_start
          (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f)]
  · push_neg at hq_read
    have h_not_read : ∀ i, i < bits → q ≠ q_start + 2 * i + 2 := by
      intros i hi h_eq
      exact hq_read i hi h_eq
    rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) q h_not_read]
    rw [cuccaro_maj_chain_inv_commute_update_outside_workspace
          bits q_start flagPos _ _ hflag_out q hq_lower hq_upper]
    rw [show Gate.applyNat (cuccaro_maj_chain_inv bits q_start)
          (Gate.applyNat (cuccaro_maj_chain bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f)) q
          = Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f q from ?_]
    · rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) q h_not_read]
    · rw [cuccaro_maj_chain_inv_after_chain_eq_id bits q_start
          (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f)]

/-- **Generalized compare-state equality** (Tick 59 Deliverable B,
relaxed to `hflag_out`). -/
theorem sqir_dirty_modadd_after_compare_state_eq_general
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (update (cuccaro_input_F q_start false 0 (x + c)) flagPos false)
      = update (cuccaro_input_F q_start false 0 (x + c))
              flagPos (decide (N ≤ x + c)) := by
  have h_input_at_flagPos : cuccaro_input_F q_start false 0 (x + c) flagPos = false :=
    cuccaro_input_F_at_outside_eq_false q_start bits (x + c) flagPos hflag_out (by omega)
  have h_input_eq : update (cuccaro_input_F q_start false 0 (x + c)) flagPos false
                  = cuccaro_input_F q_start false 0 (x + c) := by
    funext q
    by_cases hq : q = flagPos
    · rw [hq, update_eq]; exact h_input_at_flagPos.symm
    · rw [update_neq _ _ _ _ hq]
  rw [h_input_eq]
  funext q
  by_cases hq : q = flagPos
  · rw [hq, update_eq]
    exact sqir_style_compareConst_candidate_flag_general bits q_start N (x + c) flagPos
      hN_pos hN (by omega) hflag_out
  · rw [update_neq _ _ _ _ hq]
    by_cases h_q_workspace : q_start ≤ q ∧ q < q_start + 2 * bits + 1
    · exact sqir_style_compareConst_candidate_workspace_restored_at_general bits q_start N
        flagPos _ hflag_out q h_q_workspace.1 h_q_workspace.2
    · push_neg at h_q_workspace
      have h_q_outside : q < q_start ∨ q_start + 2 * bits + 1 ≤ q := by
        by_cases h : q < q_start
        · left; exact h
        · push_neg at h
          right; exact h_q_workspace h
      exact sqir_style_compareConst_candidate_frame_outside bits q_start N flagPos
        _ q hq h_q_outside

/-- **Generalized dirty-flag mod-N add target decode** (Tick 59 D,
relaxed to `hflag_out`). -/
theorem sqir_style_modAddConst_dirtyFlag_target_decode_general
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false))
      = (x + c) % N := by
  show cuccaro_target_val bits q_start
      (Gate.applyNat
        (seq (cuccaro_addConstGate bits q_start c)
              (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                   (sqir_conditionalSubConstGate bits q_start N flagPos)))
        (update (cuccaro_input_F q_start false 0 x) flagPos false)) = _
  simp only [Gate.applyNat_seq]
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq_general bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  rw [sqir_conditionalSubConstGate_target_decode bits q_start N (x + c) flagPos
        (decide (N ≤ x + c)) hbits hN_pos hN (by omega : x + c < 2^bits)
        h_flag_distinct hflag_out]
  exact sqir_dirty_modadd_arith bits N x c hN_pos hN hN2 hx hc

/-- **Generalized workspace conjuncts** (Tick 60 A, relaxed to `hflag_out`). -/
theorem sqir_style_modAddConst_dirtyFlag_read_decode_general
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_read_val bits q_start
        (Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false))
      = 0 := by
  show cuccaro_read_val bits q_start
      (Gate.applyNat
        (seq (cuccaro_addConstGate bits q_start c)
              (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                   (sqir_conditionalSubConstGate bits q_start N flagPos)))
        (update (cuccaro_input_F q_start false 0 x) flagPos false)) = _
  simp only [Gate.applyNat_seq]
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq_general bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_read_decode bits q_start (2^bits - N) (x + c) flagPos
      (decide (N ≤ x + c)) hbits (by omega) (by omega) h_flag_distinct hflag_out

theorem sqir_style_modAddConst_dirtyFlag_carry_in_restored_general
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos false) q_start
      = false := by
  show Gate.applyNat
      (seq (cuccaro_addConstGate bits q_start c)
            (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                 (sqir_conditionalSubConstGate bits q_start N flagPos)))
      (update (cuccaro_input_F q_start false 0 x) flagPos false) q_start = _
  simp only [Gate.applyNat_seq]
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq_general bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_carry_in_restored bits q_start (2^bits - N) (x + c) flagPos
      (decide (N ≤ x + c)) hbits (by omega) (by omega) h_flag_distinct hflag_out

theorem sqir_style_modAddConst_dirtyFlag_flag_value_general
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos
      = decide (N ≤ x + c) := by
  show Gate.applyNat
      (seq (cuccaro_addConstGate bits q_start c)
            (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                 (sqir_conditionalSubConstGate bits q_start N flagPos)))
      (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos = _
  simp only [Gate.applyNat_seq]
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq_general bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_flag_preserved bits q_start (2^bits - N) (x + c) flagPos
      (decide (N ≤ x + c)) h_flag_distinct hflag_out

/-- **Generalized clean-except-flag bundle** (Tick 60 C, relaxed to
`hflag_out`).  Supports both above- AND below-workspace flag. -/
theorem sqir_style_modAddConst_dirtyFlag_clean_except_flag_general
    (bits q_start N c x flagPos dim : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.WellTyped dim
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
            (update (cuccaro_input_F q_start false 0 x) flagPos false))
        = (x + c) % N
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
            (update (cuccaro_input_F q_start false 0 x) flagPos false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false) q_start
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos
        = decide (N ≤ x + c) := by
  have h_flag_distinct_top : flagPos ≠ q_start + 2 * bits := by
    rcases hflag_out with hl | hr
    · omega
    · omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact sqir_style_modAddConst_dirtyFlag_candidate_wellTyped bits q_start N c flagPos dim
      h_workspace h_flag h_flag_distinct h_flag_distinct_top
  · exact sqir_style_modAddConst_dirtyFlag_target_decode_general bits q_start N c x flagPos
      hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out
  · exact sqir_style_modAddConst_dirtyFlag_read_decode_general bits q_start N c x flagPos
      hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out
  · exact sqir_style_modAddConst_dirtyFlag_carry_in_restored_general bits q_start N c x flagPos
      hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out
  · exact sqir_style_modAddConst_dirtyFlag_flag_value_general bits q_start N c x flagPos
      hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out

/-! ## Tick 61 — SQIR-exact-layout specializations.

`q_start = 2`, `flagPos = 1`, dimension `sqir_modmult_rev_anc bits =
3 * bits + 11`. -/

/-- **Deliverable A — SQIR-layout comparator flag-copy.** -/
theorem sqir_style_compareConst_candidate_flag_sqir_layout
    (bits N x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
        (cuccaro_input_F 2 false 0 x) 1
      = decide (N ≤ x) :=
  sqir_style_compareConst_candidate_flag_general bits 2 N x 1
    hN_pos hN hx (Or.inl (by omega))

/-- **Deliverable B — SQIR-layout clean comparator bundle.** -/
theorem sqir_style_compareConst_candidate_clean_sqir_layout
    (bits N x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_compareConst_candidate bits 2 N 1)
    ∧ Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
          (cuccaro_input_F 2 false 0 x) 1
        = decide (N ≤ x)
    ∧ (∀ i, i < bits →
        Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
          (cuccaro_input_F 2 false 0 x) (2 + 2 * i + 2)
          = false)
    ∧ (∀ i, i < bits →
        Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
          (cuccaro_input_F 2 false 0 x) (2 + 2 * i + 1)
          = x.testBit i)
    ∧ Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
          (cuccaro_input_F 2 false 0 x) (2 + 2 * bits) = false := by
  have hflag_out : (1 : Nat) < 2 ∨ 2 + 2 * bits + 1 ≤ 1 := Or.inl (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- WellTyped at SQIR dim.
    apply sqir_style_compareConst_candidate_wellTyped bits 2 N 1
      (sqir_modmult_rev_anc bits)
    · unfold sqir_modmult_rev_anc; omega
    · unfold sqir_modmult_rev_anc; omega
    · omega
  · exact sqir_style_compareConst_candidate_flag_sqir_layout bits N x hbits hN_pos hN hx
  · -- read register restored: at (2 + 2*i + 2), workspace_restored_at_general gives input,
    -- and cuccaro_input_F at a-position with a=0 is false.
    intro i hi
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 N 1
        (cuccaro_input_F 2 false 0 x) hflag_out (2 + 2 * i + 2) (by omega) (by omega)]
    rw [cuccaro_input_F_at_a 2 i false 0 x]
    simp [Nat.zero_testBit]
  · -- target register restored: at (2 + 2*i + 1), workspace + input bit.
    intro i hi
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 N 1
        (cuccaro_input_F 2 false 0 x) hflag_out (2 + 2 * i + 1) (by omega) (by omega)]
    exact cuccaro_input_F_at_b 2 i false 0 x
  · -- top carry restored: 2 + 2*bits is q_start + 2*(bits-1) + 2 → a.testBit (bits-1) = 0.
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 N 1
        (cuccaro_input_F 2 false 0 x) hflag_out (2 + 2 * bits) (by omega) (by omega)]
    have h_eq : 2 + 2 * bits = 2 + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 x]
    simp [Nat.zero_testBit]

/-- **Deliverable C — SQIR-layout dirty-flag mod-N add target decode.** -/
theorem sqir_style_modAddConst_dirtyFlag_target_decode_sqir_layout
    (bits N c x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    cuccaro_target_val bits 2
        (Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false))
      = (x + c) % N :=
  sqir_style_modAddConst_dirtyFlag_target_decode_general bits 2 N c x 1
    hbits hN_pos hN hN2 hx hc (by intros i _; omega) (Or.inl (by omega))

/-- **Deliverable D — SQIR-layout dirty-flag mod-N add clean-except-flag bundle.** -/
theorem sqir_style_modAddConst_dirtyFlag_clean_except_flag_sqir_layout
    (bits N c x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = (x + c) % N
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 2
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 1
        = decide (N ≤ x + c) := by
  apply sqir_style_modAddConst_dirtyFlag_clean_except_flag_general bits 2 N c x 1
      (sqir_modmult_rev_anc bits) hbits hN_pos hN hN2 hx hc
  · unfold sqir_modmult_rev_anc; omega
  · unfold sqir_modmult_rev_anc; omega
  · intros i _; omega
  · exact Or.inl (by omega)

/-- **Deliverable E — BasicSetting-based SQIR-layout corollary.**
Combines the SQIR-layout bundle with the sizing relation from
`BasicSetting`.  Instantiates `bits := n + 1` as the canonical
workspace width per `BasicSetting_twoN_le_pow_succ`. -/
theorem sqir_style_modAddConst_dirtyFlag_clean_except_flag_from_BasicSetting
    (a r N m n c x : Nat)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (hx : x < N) (hc : c < N) :
    Gate.WellTyped (sqir_modmult_rev_anc (n + 1))
        (sqir_style_modAddConst_dirtyFlag_candidate (n + 1) 2 N c 1)
    ∧ cuccaro_target_val (n + 1) 2
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate (n + 1) 2 N c 1)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = (x + c) % N
    ∧ cuccaro_read_val (n + 1) 2
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate (n + 1) 2 N c 1)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate (n + 1) 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 2
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate (n + 1) 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 1
        = decide (N ≤ x + c) := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have hN_le : N ≤ 2 ^ (n + 1) := by
    have : N ≤ 2 * N := by omega
    omega
  exact sqir_style_modAddConst_dirtyFlag_clean_except_flag_sqir_layout (n + 1) N c x
    (by omega) hN_pos hN_le hN2 hx hc

/-! ## Tick 62 — Flag-uncomputation infrastructure.

The Tick 61 SQIR-layout bundle exposes a dirty flag holding
`decide (N ≤ x + c)`.  To clean it, we observe an arithmetic identity:

  For `0 < c`, `x < N`, `c < N`, `0 < N`:
    `decide (c ≤ (x + c) % N) = ! decide (N ≤ x + c)`.

So running `compareConst(c)` on the post-dirty-flag state would XOR
`decide (c ≤ (x+c) % N) = ! decide (N ≤ x+c)` into the flag, giving
`decide (N ≤ x+c) XOR ! decide (N ≤ x+c) = true`.  A subsequent
`X(flagPos)` flips this to `false`, restoring the flag.

We prove (Task 1) the comparator's general flag-XOR semantics, the
arithmetic identity, and define the clean candidate.  Full flag
restoration is deferred to Tick 63 because composing the XOR semantics
with the dirty-flag bundle requires a function-level state equality
that we don't yet have (the existing dirty-flag bundle only exposes
DECODED workspace properties, not bit-level state equality).

The c = 0 case is special: the dirty flag is already `false` after
`dirtyFlag(c=0)`, so cleanup is trivially identity — but the current
clean candidate over-cleans it.  We carry the precondition `0 < c`
for the clean candidate. -/

/-- Helper for the XOR flag theorem: the inner `(prepare; maj)` block
at `q_start + 2*bits` (top carry) equals `decide (N ≤ x)` even when
the input has an outside `update` at `flagPos`. -/
private lemma prepareMaj_at_top_eq_after_update
    (bits q_start N x flagPos : Nat) (flag : Bool)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (cuccaro_maj_chain bits q_start)
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N))
          (update (cuccaro_input_F q_start false 0 x) flagPos flag))
        (q_start + 2 * bits)
      = decide (N ≤ x) := by
  rw [cuccaro_prepareConstRead_commute_update_outside_workspace bits q_start (2^bits - N)
        flagPos flag _ hflag_out]
  rw [cuccaro_maj_chain_commute_update_outside_workspace bits q_start flagPos flag _ hflag_out]
  have h_ne : q_start + 2 * bits ≠ flagPos := by
    rcases hflag_out with hl | hr
    · omega
    · omega
  rw [update_neq _ _ _ _ h_ne]
  have h_carry := cuccaro_compareConstForward_top_carry bits q_start N x hN_pos hN hx
  unfold cuccaro_compareConstForwardGate at h_carry
  simp only [Gate.applyNat_seq] at h_carry
  exact h_carry

/-- **HEADLINE Task 1 — comparator flag-XOR semantics.**  For any
initial flag value `flag`, the SQIR-style comparator at `flagPos`
returns `flag XOR decide (N ≤ x)`.  This is the key polarity result
needed for any flag-uncomputation construction. -/
theorem sqir_style_compareConst_candidate_flag_xor
    (bits q_start N x flagPos : Nat) (flag : Bool)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos flag) flagPos
      = xor flag (decide (N ≤ x)) := by
  show Gate.applyNat
      (seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (cuccaro_prepareConstRead bits q_start (2^bits - N))))))
      (update (cuccaro_input_F q_start false 0 x) flagPos flag) flagPos = _
  simp only [Gate.applyNat_seq]
  have h_flagPos_not_read : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2 := by
    intros j _ heq; rcases hflag_out with hl | hr <;> omega
  rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) flagPos h_flagPos_not_read]
  -- The "state at flagPos" (before CX, through maj_chain ∘ prepare₁) is `flag`.
  have h_flag_state :
      Gate.applyNat (cuccaro_maj_chain bits q_start)
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N))
          (update (cuccaro_input_F q_start false 0 x) flagPos flag)) flagPos = flag := by
    rcases hflag_out with h_below | h_above
    · rw [cuccaro_maj_chain_frame_below bits q_start _ flagPos h_below]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) flagPos h_flagPos_not_read]
      exact update_eq _ _ _
    · rw [cuccaro_maj_chain_frame_above bits q_start _ flagPos h_above]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) flagPos h_flagPos_not_read]
      exact update_eq _ _ _
  -- Top-carry value (= state at q_start + 2*bits) before CX = decide (N ≤ x).
  have h_top_state := prepareMaj_at_top_eq_after_update bits q_start N x flagPos flag
    hN_pos hN hx hflag_out
  -- Strip maj_inv (frame at flagPos), then CX.
  rcases hflag_out with h_below | h_above
  · rw [cuccaro_maj_chain_inv_frame_below bits q_start _ flagPos h_below]
    simp only [Gate.applyNat_CX, update_eq]
    rw [h_flag_state, h_top_state]
  · rw [cuccaro_maj_chain_inv_frame_above bits q_start _ flagPos h_above]
    simp only [Gate.applyNat_CX, update_eq]
    rw [h_flag_state, h_top_state]

/-- **SQIR-layout corollary of Task 1.** -/
theorem sqir_style_compareConst_candidate_flag_xor_sqir_layout
    (bits N x : Nat) (flag : Bool) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
        (update (cuccaro_input_F 2 false 0 x) 1 flag) 1
      = xor flag (decide (N ≤ x)) :=
  sqir_style_compareConst_candidate_flag_xor bits 2 N x 1 flag
    hN_pos hN hx (Or.inl (by omega))

/-! ## Tick 62 — Arithmetic identity for flag uncomputation. -/

/-- **HEADLINE — arithmetic identity for clean candidate.**  For
`0 < c`, `x < N`, `c < N`, the comparator's result on the reduced
target `(x+c) % N` is precisely the negation of the dirty flag. -/
theorem decide_c_le_xc_mod_N_eq_not_decide_N_le_xc
    (N x c : Nat) (hN_pos : 0 < N) (hc_pos : 0 < c)
    (hx : x < N) (hc : c < N) :
    decide (c ≤ (x + c) % N) = ! decide (N ≤ x + c) := by
  by_cases h : N ≤ x + c
  · -- Case x + c ≥ N: (x+c) % N = x + c - N, and x+c-N < c iff x < N (true).
    have h_lt : x + c < 2 * N := by omega
    have h_xc_lt_2N : x + c - N < N := by omega
    have h_mod : (x + c) % N = x + c - N := by
      rw [Nat.mod_eq_sub_mod h]
      exact Nat.mod_eq_of_lt h_xc_lt_2N
    rw [h_mod]
    -- c ≤ x+c-N iff N ≤ x.  But x < N, so c ≤ x+c-N is FALSE.
    have h_xc_sub_lt_c : x + c - N < c := by omega
    simp [h, Nat.not_le.mpr h_xc_sub_lt_c]
  · -- Case x + c < N: (x+c) % N = x + c, and c ≤ x+c is TRUE.
    push_neg at h
    have h_mod : (x + c) % N = x + c := Nat.mod_eq_of_lt h
    rw [h_mod]
    have h_c_le_xc : c ≤ x + c := by omega
    simp [Nat.not_le.mpr h, h_c_le_xc]

/-! ## Tick 62 — Clean modular-add candidate definition. -/

/-- **Clean modular add-constant candidate** for `0 < c < N`.

Structure: dirty-flag candidate ; compareConst(c) ; X(flagPos).
The compareConst(c) XORs `decide(c ≤ (x+c) % N) = ¬decide(N ≤ x+c)`
into the flag, then X negates.  Net flag effect:
  `flag → ¬(flag XOR decide(N ≤ x+c) XOR ¬decide(N ≤ x+c))
        = ¬(flag XOR true)
        = flag`,
so the flag is restored.  The cleanup also re-touches the target /
read / carry workspace, but by the comparator's workspace_restored
property these end up at the same values as the dirty-flag stage.

**Caveat on `c = 0`:** `compareConst(0)` cannot be implemented in
`bits` bits because `K = 2^bits` overflows the read register.  For
`c = 0` the modular add is the identity and the dirty flag is
already `false`; the clean candidate is correct only for `0 < c`.
A wrapper that dispatches `c = 0` to identity is straightforward
but introduces a conditional gate structure (deferred). -/
def sqir_style_modAddConst_clean_candidate
    (bits q_start N c flagPos : Nat) : Gate :=
  seq (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
      (seq (sqir_style_compareConst_candidate bits q_start c flagPos)
           (Gate.X flagPos))

/-! ## Status note (Tick 62).

Landed (all kernel-clean):
- `sqir_style_compareConst_candidate_flag_xor` — comparator
  flag-XOR semantics for arbitrary initial flag.
- `sqir_style_compareConst_candidate_flag_xor_sqir_layout` —
  SQIR-layout corollary.
- `decide_c_le_xc_mod_N_eq_not_decide_N_le_xc` — the arithmetic
  identity making the cleanup XOR cancel.
- `sqir_style_modAddConst_clean_candidate` — clean-candidate
  definition for `0 < c < N`.

Empirical validation (Python, `scripts/check_sqir_modadder21_flag_uncompute.py`):
clean candidate passes target/read/carry/flag tests for all
`(bits, N, c, x)` with `bits ∈ {1..5}, 0 < N, 2N ≤ 2^bits, 0 < c < N,
x < N`.  Fails (as expected) for `c = 0` because
`compareConst(0)` is not implementable in the `bits` register.

**Not yet landed (deferred to Tick 63 — Phase 2 finalization):**
- `sqir_style_modAddConst_clean_candidate_flag_restored` (full flag
  restoration).  Blocker: composing the XOR semantics with the
  dirty-flag stage requires a function-level state equality
  `applyNat dirtyFlag (update cuccaro_input_F flagPos false)
  = update (cuccaro_input_F false 0 ((x+c)%N)) flagPos (decide(N ≤ x+c))`.
  The existing dirty-flag bundle exposes DECODED workspace properties
  only (cuccaro_read_val = 0, cuccaro_target_val = (x+c)%N), not
  per-position bit values.  Closing this requires bit-level workspace
  theorems for the dirty-flag candidate.

**SQIR `modadder21` faithfulness:** the Coq sequence uses
`bcx 1 ; swapper02 ; bcinv comparator01 ; swapper02` instead of our
`compareConst(c) ; X`.  Empirically the two cleanup mechanisms
agree for all tested cases (`0 < c < N`).  Full Coq-faithful port
including `swapper02` and `bcinv` is deferred unless it becomes
necessary for the next layer.

**Original SQIR placeholder axioms NOT YET CLOSED.**  This tick
makes incremental progress toward Phase 2 finalization.  The
clean-flag mod-N add is the immediate next milestone.

### Next tick should
1. **Bit-level workspace theorems for `sqir_style_modAddConst_dirtyFlag_candidate`** —
   per-position bit values at target/read/carry positions.
2. **Post-dirtyFlag state equality** — combine with bit-level
   workspace + frame_outside to get the full function-level state.
3. **Flag restoration for `sqir_style_modAddConst_clean_candidate`** —
   compose Task 1's XOR theorem with the state equality and the
   arithmetic identity.
4. **Workspace restoration for the clean candidate** — show
   compareConst's workspace-restored property holds after the
   composition, so target/read/carry stay at the dirty-flag values.
5. **Clean modular add bundle** — WellTyped + target = (x+c)%N
   + workspace restored + flag = false.
6. **Optional**: c = 0 wrapper. -/

/-! ## Tick 63 — Bit-level dirty-flag workspace + state equality + flag restoration.

These theorems close the Tick 62 blocker by establishing
per-position state-correctness facts for the dirty-flag candidate,
combining them into a function-level state equality, and using that
equality to prove clean-flag restoration. -/

/-- Helper: `prepare(0)` is identity. -/
private lemma cuccaro_prepareConstRead_zero_eq_id_fun
    (bits q_start : Nat) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_prepareConstRead bits q_start 0) f = f := by
  funext q
  by_cases hq_read : ∃ i, i < bits ∧ q = q_start + 2 * i + 2
  · obtain ⟨i, hi, hq_eq⟩ := hq_read
    rw [hq_eq, cuccaro_prepareConstRead_at_read bits q_start 0 i hi]
    simp [Nat.zero_testBit]
  · push_neg at hq_read
    exact cuccaro_prepareConstRead_at_other bits q_start 0 q (fun i hi h => hq_read i hi h) f

/-- Helper: on any input, `addConstGate(0)` agrees with the full adder. -/
private lemma cuccaro_addConstGate_zero_eq_full_adder_fun
    (bits q_start : Nat) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_addConstGate bits q_start 0) f
      = Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) f := by
  show Gate.applyNat
      (seq (cuccaro_prepareConstRead bits q_start 0)
            (seq (cuccaro_n_bit_adder_full bits q_start)
                 (cuccaro_prepareConstRead bits q_start 0)))
      f = _
  simp only [Gate.applyNat_seq]
  rw [cuccaro_prepareConstRead_zero_eq_id_fun, cuccaro_prepareConstRead_zero_eq_id_fun]

/-- **HEADLINE Deliverable A — dirty-flag target bit theorem.**  At each
target position `q_start + 2*i + 1` for `i < bits`, the dirty-flag
candidate's output bit equals `((x + c) % N).testBit i`. -/
theorem sqir_style_modAddConst_dirtyFlag_target_bit
    (bits q_start N c x flagPos i : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N) (hi : i < bits)
    (h_flag_distinct : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos false)
        (q_start + 2 * i + 1)
      = ((x + c) % N).testBit i := by
  show Gate.applyNat
      (seq (cuccaro_addConstGate bits q_start c)
            (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                 (sqir_conditionalSubConstGate bits q_start N flagPos)))
      _ _ = _
  simp only [Gate.applyNat_seq]
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq_general bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  unfold sqir_conditionalSubConstGate
  have h_ne : q_start + 2 * i + 1 ≠ flagPos := by
    rcases hflag_out with hl | hr
    · omega
    · omega
  by_cases h_flag : N ≤ x + c
  · -- True case: conditional sub fires (= addConstGate(2^bits - N)).
    have h_decide : decide (N ≤ x + c) = true := by simp [h_flag]
    have h_input_flag :
        (update (cuccaro_input_F q_start false 0 (x + c)) flagPos (decide (N ≤ x + c))) flagPos
          = true := by rw [update_eq, h_decide]
    rw [sqir_conditionalAddConstGate_apply_true_fun bits q_start (2^bits - N) flagPos
          _ h_flag_distinct h_input_flag hflag_out]
    rw [cuccaro_addConstGate_commute_update_outside_workspace bits q_start (2^bits - N)
          flagPos _ _ hflag_out]
    rw [update_neq _ _ _ _ h_ne]
    rw [cuccaro_addConstGate_target_bit bits q_start (2^bits - N) (x + c) i hi (by omega)]
    have h_mod : (x + c) % N = x + c - N := by
      rw [Nat.mod_eq_sub_mod h_flag]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_mod]
    have h_eq : x + c + (2 ^ bits - N) = 2 ^ bits + (x + c - N) := by omega
    rw [h_eq]
    exact Nat.testBit_two_pow_add_gt hi (x + c - N)
  · -- False case: conditional sub is full adder (read register is 0).
    push_neg at h_flag
    have h_decide : decide (N ≤ x + c) = false := by simp [Nat.not_le.mpr h_flag]
    have h_input_flag :
        (update (cuccaro_input_F q_start false 0 (x + c)) flagPos (decide (N ≤ x + c))) flagPos
          = false := by rw [update_eq, h_decide]
    rw [sqir_conditionalAddConstGate_apply_false_fun bits q_start (2^bits - N) flagPos
          _ h_flag_distinct h_input_flag hflag_out]
    rw [cuccaro_n_bit_adder_full_commute_update_outside_workspace bits q_start
          flagPos _ _ hflag_out]
    rw [update_neq _ _ _ _ h_ne]
    rw [← cuccaro_addConstGate_zero_eq_full_adder_fun]
    rw [cuccaro_addConstGate_target_bit bits q_start 0 (x + c) i hi (by positivity)]
    have h_mod : (x + c) % N = x + c := Nat.mod_eq_of_lt h_flag
    rw [h_mod, Nat.add_zero]

/-- **HEADLINE Deliverable B — dirty-flag read bit theorem.**  At each
read position `q_start + 2*i + 2` for `i < bits`, the dirty-flag
candidate's output bit is `false`. -/
theorem sqir_style_modAddConst_dirtyFlag_read_bit
    (bits q_start N c x flagPos i : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N) (hi : i < bits)
    (h_flag_distinct : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos false)
        (q_start + 2 * i + 2)
      = false := by
  show Gate.applyNat
      (seq (cuccaro_addConstGate bits q_start c)
            (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                 (sqir_conditionalSubConstGate bits q_start N flagPos)))
      _ _ = _
  simp only [Gate.applyNat_seq]
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq_general bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  unfold sqir_conditionalSubConstGate
  have h_ne : q_start + 2 * i + 2 ≠ flagPos := fun heq => h_flag_distinct i hi heq.symm
  by_cases h_flag : N ≤ x + c
  · have h_decide : decide (N ≤ x + c) = true := by simp [h_flag]
    have h_input_flag :
        (update (cuccaro_input_F q_start false 0 (x + c)) flagPos (decide (N ≤ x + c))) flagPos
          = true := by rw [update_eq, h_decide]
    rw [sqir_conditionalAddConstGate_apply_true_fun bits q_start (2^bits - N) flagPos
          _ h_flag_distinct h_input_flag hflag_out]
    rw [cuccaro_addConstGate_commute_update_outside_workspace bits q_start (2^bits - N)
          flagPos _ _ hflag_out]
    rw [update_neq _ _ _ _ h_ne]
    exact cuccaro_addConstGate_read_bit bits q_start (2^bits - N) (x + c) i hi
  · push_neg at h_flag
    have h_decide : decide (N ≤ x + c) = false := by simp [Nat.not_le.mpr h_flag]
    have h_input_flag :
        (update (cuccaro_input_F q_start false 0 (x + c)) flagPos (decide (N ≤ x + c))) flagPos
          = false := by rw [update_eq, h_decide]
    rw [sqir_conditionalAddConstGate_apply_false_fun bits q_start (2^bits - N) flagPos
          _ h_flag_distinct h_input_flag hflag_out]
    rw [cuccaro_n_bit_adder_full_commute_update_outside_workspace bits q_start
          flagPos _ _ hflag_out]
    rw [update_neq _ _ _ _ h_ne]
    rw [← cuccaro_addConstGate_zero_eq_full_adder_fun]
    exact cuccaro_addConstGate_read_bit bits q_start 0 (x + c) i hi

/-- Frame: dirty-flag candidate preserves values at positions outside
workspace ∪ {flagPos}. -/
theorem sqir_style_modAddConst_dirtyFlag_frame_outside
    (bits q_start N c flagPos : Nat) (f : Nat → Bool)
    (h_flag_distinct : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (q : Nat) (h_q_ne_flagPos : q ≠ flagPos)
    (h_q_outside : q < q_start ∨ q_start + 2 * bits + 1 ≤ q) :
    Gate.applyNat (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos) f q
      = f q := by
  show Gate.applyNat
      (seq (cuccaro_addConstGate bits q_start c)
            (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                 (sqir_conditionalSubConstGate bits q_start N flagPos)))
      f q = _
  simp only [Gate.applyNat_seq]
  have h_q_not_read : ∀ j, j < bits → q ≠ q_start + 2 * j + 2 := by
    intros j _ heq
    rcases h_q_outside with hl | hr
    · omega
    · omega
  -- Strip layers from outside-in: conditionalSub → compareConst → addConst.
  -- Step 1: conditionalSub at q outside (≠ flagPos) = identity.
  have h_condSub_outer : Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos)
        (Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
          (Gate.applyNat (cuccaro_addConstGate bits q_start c) f)) q
      = Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
          (Gate.applyNat (cuccaro_addConstGate bits q_start c) f) q := by
    unfold sqir_conditionalSubConstGate sqir_conditionalAddConstGate
    show Gate.applyNat
        (seq (sqir_prepareMaskedConstRead bits q_start (2^bits - N) flagPos)
              (seq (cuccaro_n_bit_adder_full bits q_start)
                   (sqir_prepareMaskedConstRead bits q_start (2^bits - N) flagPos)))
        _ q = _
    simp only [Gate.applyNat_seq]
    rw [sqir_prepareMaskedConstRead_at_other bits q_start (2^bits - N) flagPos q h_q_not_read]
    rcases h_q_outside with h_below | h_above
    · rw [cuccaro_n_bit_adder_full_frame_below bits q_start _ q h_below]
      rw [sqir_prepareMaskedConstRead_at_other bits q_start (2^bits - N) flagPos q h_q_not_read]
    · rw [cuccaro_n_bit_adder_full_frame_above bits q_start _ q h_above]
      rw [sqir_prepareMaskedConstRead_at_other bits q_start (2^bits - N) flagPos q h_q_not_read]
  rw [h_condSub_outer]
  -- Step 2: compareConst at q outside (≠ flagPos) = identity.
  rw [sqir_style_compareConst_candidate_frame_outside bits q_start N flagPos _ q
        h_q_ne_flagPos h_q_outside]
  -- Step 3: addConst at q outside = identity.
  show Gate.applyNat
      (seq (cuccaro_prepareConstRead bits q_start c)
            (seq (cuccaro_n_bit_adder_full bits q_start)
                 (cuccaro_prepareConstRead bits q_start c))) f q = _
  simp only [Gate.applyNat_seq]
  rw [cuccaro_prepareConstRead_at_other bits q_start c q h_q_not_read]
  rcases h_q_outside with h_below | h_above
  · rw [cuccaro_n_bit_adder_full_frame_below bits q_start _ q h_below]
    rw [cuccaro_prepareConstRead_at_other bits q_start c q h_q_not_read]
  · rw [cuccaro_n_bit_adder_full_frame_above bits q_start _ q h_above]
    rw [cuccaro_prepareConstRead_at_other bits q_start c q h_q_not_read]

/-- **HEADLINE Deliverable C — dirty-flag state equality.**  As a
function, the post-dirty-flag state equals
`update (cuccaro_input_F false 0 ((x+c) % N)) flagPos (decide(N ≤ x+c))`.
-/
theorem sqir_style_modAddConst_dirtyFlag_state_eq
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos false)
      = update (cuccaro_input_F q_start false 0 ((x + c) % N))
              flagPos (decide (N ≤ x + c)) := by
  funext q
  have h_xc_mod_N_lt : (x + c) % N < 2 ^ bits := Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  by_cases hq_flag : q = flagPos
  · -- flagPos: use Tick 60 flag_value (general).
    rw [hq_flag, update_eq]
    exact sqir_style_modAddConst_dirtyFlag_flag_value_general bits q_start N c x flagPos
      hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out
  · rw [update_neq _ _ _ _ hq_flag]
    by_cases hq_ws : q_start ≤ q ∧ q < q_start + 2 * bits + 1
    · -- q in workspace: case analysis on q's role.
      obtain ⟨hq_ge, hq_lt⟩ := hq_ws
      by_cases hq_b : ∃ i, i < bits ∧ q = q_start + 2 * i + 1
      · obtain ⟨i, hi, hq_eq⟩ := hq_b
        rw [hq_eq]
        rw [sqir_style_modAddConst_dirtyFlag_target_bit bits q_start N c x flagPos i
              hbits hN_pos hN hN2 hx hc hi h_flag_distinct hflag_out]
        exact (cuccaro_input_F_at_b q_start i false 0 ((x + c) % N)).symm
      · push_neg at hq_b
        by_cases hq_a : ∃ i, i < bits ∧ q = q_start + 2 * i + 2
        · obtain ⟨i, hi, hq_eq⟩ := hq_a
          rw [hq_eq]
          rw [sqir_style_modAddConst_dirtyFlag_read_bit bits q_start N c x flagPos i
                hbits hN_pos hN hN2 hx hc hi h_flag_distinct hflag_out]
          rw [cuccaro_input_F_at_a q_start i false 0 ((x + c) % N)]
          simp [Nat.zero_testBit]
        · push_neg at hq_a
          -- q is in workspace but not target/read. Must be q_start (carry_in).
          have h_q_eq : q = q_start := by
            -- q ∈ [q_start, q_start + 2*bits], not q_start+2i+1, not q_start+2i+2.
            -- The only position left is q_start.
            -- For q > q_start: q - q_start ≥ 1. If q - q_start = 2k+1: q = q_start + 2k+1, hq_b k contradicts. If q - q_start = 2k+2: q = q_start + 2k+2, hq_a k contradicts.
            by_contra h_ne
            have h_gt : q_start < q := by omega
            have h_diff : 1 ≤ q - q_start := by omega
            have h_diff_lt : q - q_start ≤ 2 * bits := by omega
            -- q - q_start is in [1, 2*bits].
            set d := q - q_start with hd_def
            have hd_pos : 1 ≤ d := h_diff
            have hd_le : d ≤ 2 * bits := h_diff_lt
            have h_q : q = q_start + d := by omega
            -- Either d is odd or even.
            by_cases h_odd : d % 2 = 1
            · -- d = 2k+1 for some k. q = q_start + 2k + 1.
              have ⟨k, hk⟩ : ∃ k, d = 2 * k + 1 := ⟨d / 2, by omega⟩
              have hk_lt : k < bits := by omega
              exact hq_b k hk_lt (by omega)
            · -- d is even, d ≥ 2.
              have hd_even : d % 2 = 0 := by omega
              have ⟨k, hk⟩ : ∃ k, d = 2 * k + 2 := ⟨(d - 2) / 2, by omega⟩
              have hk_lt : k < bits := by omega
              exact hq_a k hk_lt (by omega)
          rw [h_q_eq]
          rw [sqir_style_modAddConst_dirtyFlag_carry_in_restored_general bits q_start N c x flagPos
                hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
          exact (cuccaro_input_F_at_c_in q_start false 0 ((x + c) % N)).symm
    · -- q outside workspace, q ≠ flagPos.
      push_neg at hq_ws
      have h_q_outside : q < q_start ∨ q_start + 2 * bits + 1 ≤ q := by
        by_cases h : q < q_start
        · left; exact h
        · push_neg at h
          right; exact hq_ws h
      rw [sqir_style_modAddConst_dirtyFlag_frame_outside bits q_start N c flagPos _
            h_flag_distinct hflag_out q hq_flag h_q_outside]
      rw [show (update (cuccaro_input_F q_start false 0 x) flagPos false) q
          = cuccaro_input_F q_start false 0 x q from update_neq _ _ _ _ hq_flag]
      rw [cuccaro_input_F_at_outside_eq_false q_start bits x q h_q_outside (by omega)]
      exact (cuccaro_input_F_at_outside_eq_false q_start bits ((x + c) % N) q h_q_outside
        h_xc_mod_N_lt).symm

/-- **HEADLINE Deliverable D — clean-candidate flag restoration.**  At
`flagPos`, the clean candidate restores the input flag value `false`. -/
theorem sqir_style_modAddConst_clean_candidate_flag_restored
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N) :
    Gate.applyNat
        (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
        (update (cuccaro_input_F 2 false 0 x) 1 false) 1
      = false := by
  show Gate.applyNat
      (seq (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
            (seq (sqir_style_compareConst_candidate bits 2 c 1)
                 (Gate.X 1)))
      _ _ = _
  simp only [Gate.applyNat_seq]
  have hflag_out : (1 : Nat) < 2 ∨ 2 + 2 * bits + 1 ≤ 1 := Or.inl (by omega)
  have h_flag_distinct : ∀ j, j < bits → (1 : Nat) ≠ 2 + 2 * j + 2 := by
    intros j _; omega
  -- Use state equality to substitute the post-dirty-flag state.
  rw [sqir_style_modAddConst_dirtyFlag_state_eq bits 2 N c x 1
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  have h_xc_mod_N_lt : (x + c) % N < 2 ^ bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  -- Strip the outermost X(1) gate at position 1.
  rw [Gate.applyNat_X]
  rw [update_eq]
  -- Goal: ! (applyNat compareConst(c) (update _ 1 (decide (N ≤ x+c))) 1) = false.
  -- Apply XOR theorem.
  rw [sqir_style_compareConst_candidate_flag_xor bits 2 c ((x + c) % N) 1
        (decide (N ≤ x + c)) hc_pos (by omega : c ≤ 2 ^ bits) h_xc_mod_N_lt hflag_out]
  -- Goal: ! (xor (decide (N ≤ x+c)) (decide (c ≤ (x+c) % N))) = false.
  rw [decide_c_le_xc_mod_N_eq_not_decide_N_le_xc N x c hN_pos hc_pos hx hc]
  -- Goal: ! (xor (decide (N ≤ x+c)) (! decide (N ≤ x+c))) = false.
  cases decide (N ≤ x + c) <;> rfl

/-- **R7d^xxix-L-3.9′ DELIVERABLE: q_start-parametric clean candidate
target preservation.**

q_start-parametric port of
`sqir_style_modAddConst_clean_candidate_target_decode`.  Replaces the
hard-coded layout `q_start = 2`, `flagPos = 1` with free parameters
and the standard outside-workspace hypotheses.

The decoded target after the clean candidate equals `(x + c) % N`,
regardless of where the workspace and flag sit.

Dependencies (all already q_start-parametric):
- `sqir_style_modAddConst_dirtyFlag_state_eq` (CuccaroSQIRDirtyFlag.lean:1378);
- `cuccaro_target_val_eq_sum_when_bits_match` (CuccaroDecoded.lean:102);
- `sqir_style_compareConst_candidate_workspace_restored_at_general`
  (CuccaroSQIRDirtyFlag.lean:568);
- `cuccaro_input_F_at_b` (CuccaroCorrectness.lean:240). -/
theorem sqir_style_modAddConst_clean_candidate_target_decode_qstart
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_style_modAddConst_clean_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false))
      = (x + c) % N := by
  show cuccaro_target_val bits q_start
      (Gate.applyNat
        (seq (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
              (seq (sqir_style_compareConst_candidate bits q_start c flagPos)
                   (Gate.X flagPos))) _) = _
  simp only [Gate.applyNat_seq]
  have h_flag_distinct : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2 := by
    intros j _ heq
    rcases hflag_out with hl | hr
    · omega
    · omega
  rw [sqir_style_modAddConst_dirtyFlag_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  have h_xc_mod_N_lt : (x + c) % N < 2 ^ bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  have h_eq : cuccaro_target_val bits q_start
      (Gate.applyNat (Gate.X flagPos)
        (Gate.applyNat (sqir_style_compareConst_candidate bits q_start c flagPos)
          (update (cuccaro_input_F q_start false 0 ((x + c) % N)) flagPos
            (decide (N ≤ x + c)))))
    = (x + c) % N % 2^bits := by
    apply cuccaro_target_val_eq_sum_when_bits_match
    intro i hi
    -- Decoder reads target register at odd offsets (q_start + 2*i + 1).
    -- X(flagPos) at q_start + 2*i + 1 ≠ flagPos because flagPos is outside
    -- workspace while q_start + 2*i + 1 ∈ [q_start, q_start + 2*bits + 1).
    have h_target_ne_flag : (q_start + 2 * i + 1 : Nat) ≠ flagPos := by
      rcases hflag_out with hl | hr
      · omega
      · omega
    rw [Gate.applyNat_X]
    rw [update_neq _ _ _ _ h_target_ne_flag]
    -- compareConst at workspace position = identity (workspace_restored).
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits q_start c flagPos _
          hflag_out (q_start + 2 * i + 1) (by omega) (by omega)]
    rw [update_neq _ _ _ _ h_target_ne_flag]
    exact cuccaro_input_F_at_b q_start i false 0 ((x + c) % N)
  rw [h_eq]
  exact Nat.mod_eq_of_lt h_xc_mod_N_lt

/-- **HEADLINE Deliverable E — clean candidate target preservation.**
The clean candidate's decoded target equals `(x + c) % N`. -/
theorem sqir_style_modAddConst_clean_candidate_target_decode
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N) :
    cuccaro_target_val bits 2
        (Gate.applyNat
          (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false))
      = (x + c) % N := by
  show cuccaro_target_val bits 2
      (Gate.applyNat
        (seq (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
              (seq (sqir_style_compareConst_candidate bits 2 c 1)
                   (Gate.X 1))) _) = _
  simp only [Gate.applyNat_seq]
  have hflag_out : (1 : Nat) < 2 ∨ 2 + 2 * bits + 1 ≤ 1 := Or.inl (by omega)
  have h_flag_distinct : ∀ j, j < bits → (1 : Nat) ≠ 2 + 2 * j + 2 := fun j _ => by omega
  rw [sqir_style_modAddConst_dirtyFlag_state_eq bits 2 N c x 1
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  -- Goal: target_val of (applyNat (X 1) (applyNat compareConst(c) (update (cuccaro_input_F ((x+c)%N)) 1 (decide)))) = (x+c) % N.
  have h_xc_mod_N_lt : (x + c) % N < 2 ^ bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  have h_eq : cuccaro_target_val bits 2
      (Gate.applyNat (Gate.X 1)
        (Gate.applyNat (sqir_style_compareConst_candidate bits 2 c 1)
          (update (cuccaro_input_F 2 false 0 ((x + c) % N)) 1 (decide (N ≤ x + c)))))
    = (x + c) % N % 2^bits := by
    apply cuccaro_target_val_eq_sum_when_bits_match
    intro i hi
    -- X(1) at q_start + 2*i + 1 = 2 + 2*i + 1 ≥ 3 ≠ 1 → no-op.
    rw [Gate.applyNat_X]
    rw [update_neq _ _ _ _ (by omega : (2 + 2 * i + 1 : Nat) ≠ 1)]
    -- compareConst at workspace position = identity (workspace_restored).
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 c 1 _
          hflag_out (2 + 2 * i + 1) (by omega) (by omega)]
    -- update at 1 ≠ 2 + 2*i + 1.
    rw [update_neq _ _ _ _ (by omega : (2 + 2 * i + 1 : Nat) ≠ 1)]
    exact cuccaro_input_F_at_b 2 i false 0 ((x + c) % N)
  rw [h_eq]
  exact Nat.mod_eq_of_lt h_xc_mod_N_lt

/-- **HEADLINE Deliverable F — clean candidate full bundle.**
WellTyped + target = (x+c)%N + read restored + top-carry restored + flag restored. -/
theorem sqir_style_modAddConst_clean_candidate_clean
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = (x + c) % N
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 1
        = false := by
  have hflag_out : (1 : Nat) < 2 ∨ 2 + 2 * bits + 1 ≤ 1 := Or.inl (by omega)
  have h_flag_distinct : ∀ j, j < bits → (1 : Nat) ≠ 2 + 2 * j + 2 := fun j _ => by omega
  have h_xc_mod_N_lt : (x + c) % N < 2 ^ bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- WellTyped: clean candidate = seq dirtyFlag (seq compareConst (X 1)).
    show Gate.WellTyped (sqir_modmult_rev_anc bits)
        (seq (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
              (seq (sqir_style_compareConst_candidate bits 2 c 1)
                   (Gate.X 1)))
    refine ⟨?_, ?_, ?_⟩
    · exact sqir_style_modAddConst_dirtyFlag_candidate_wellTyped_sqir_layout bits N c hbits
    · apply sqir_style_compareConst_candidate_wellTyped bits 2 c 1
        (sqir_modmult_rev_anc bits)
      · unfold sqir_modmult_rev_anc; omega
      · unfold sqir_modmult_rev_anc; omega
      · omega
    · show 1 < sqir_modmult_rev_anc bits
      unfold sqir_modmult_rev_anc; omega
  · exact sqir_style_modAddConst_clean_candidate_target_decode bits N c x
      hbits hN_pos hN hN2 hc_pos hc hx
  · -- read = 0.  Same structure as target_decode, but at read positions.
    show cuccaro_read_val bits 2
        (Gate.applyNat
          (seq (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
                (seq (sqir_style_compareConst_candidate bits 2 c 1)
                     (Gate.X 1))) _) = _
    simp only [Gate.applyNat_seq]
    rw [sqir_style_modAddConst_dirtyFlag_state_eq bits 2 N c x 1
          hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
    have h_eq : cuccaro_read_val bits 2
        (Gate.applyNat (Gate.X 1)
          (Gate.applyNat (sqir_style_compareConst_candidate bits 2 c 1)
            (update (cuccaro_input_F 2 false 0 ((x + c) % N)) 1 (decide (N ≤ x + c)))))
      = 0 % 2^bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      rw [Gate.applyNat_X]
      rw [update_neq _ _ _ _ (by omega : (2 + 2 * i + 2 : Nat) ≠ 1)]
      rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 c 1 _
            hflag_out (2 + 2 * i + 2) (by omega) (by omega)]
      rw [update_neq _ _ _ _ (by omega : (2 + 2 * i + 2 : Nat) ≠ 1)]
      rw [cuccaro_input_F_at_a 2 i false 0 ((x + c) % N)]
    rw [h_eq]
    simp
  · -- top carry at 2 + 2*bits = false.  Use workspace_restored.
    show Gate.applyNat
        (seq (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
              (seq (sqir_style_compareConst_candidate bits 2 c 1)
                   (Gate.X 1))) _ _ = _
    simp only [Gate.applyNat_seq]
    rw [sqir_style_modAddConst_dirtyFlag_state_eq bits 2 N c x 1
          hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
    rw [Gate.applyNat_X]
    rw [update_neq _ _ _ _ (by omega : (2 + 2 * bits : Nat) ≠ 1)]
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 c 1 _
          hflag_out (2 + 2 * bits) (by omega) (by omega)]
    rw [update_neq _ _ _ _ (by omega : (2 + 2 * bits : Nat) ≠ 1)]
    -- cuccaro_input_F at 2 + 2*bits = 2 + 2*(bits-1) + 2 = a.testBit (bits-1) with a = 0 = false.
    have h_eq : (2 : Nat) + 2 * bits = 2 + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 ((x + c) % N)]
    simp [Nat.zero_testBit]
  · exact sqir_style_modAddConst_clean_candidate_flag_restored bits N c x
      hbits hN_pos hN hN2 hc_pos hc hx

/-! ## Tick 64 — Total clean SQIR mod-add-constant wrapper (including c = 0). -/

/-- **Deliverable A — total clean modular add-constant gate.**

Wraps the clean candidate (which requires `0 < c`) so that the `c = 0`
case dispatches to the identity gate.  This is the official clean
mod-add-constant primitive at the SQIR-faithful layout `q_start = 2,
flagPos = 1, dim = sqir_modmult_rev_anc bits`. -/
def sqir_style_modAddConst_clean_gate (bits N c : Nat) : Gate :=
  if c = 0 then Gate.I else sqir_style_modAddConst_clean_candidate bits 2 N c 1

/-! ## Tick 64 — c = 0 identity case. -/

/-- The wrapper at `c = 0` reduces to `Gate.I`. -/
theorem sqir_style_modAddConst_clean_gate_zero_eq
    (bits N : Nat) :
    sqir_style_modAddConst_clean_gate bits N 0 = Gate.I := by
  unfold sqir_style_modAddConst_clean_gate; simp

/-- **Deliverable B — c = 0 bundle.**  At `c = 0` the gate is the
identity, so all 5 conjuncts (WellTyped + target = x + read = 0 +
top carry = false + flag = false) reduce to facts about the input
encoding. -/
theorem sqir_style_modAddConst_clean_gate_zero_clean
    (bits N x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_modAddConst_clean_gate bits N 0)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_gate bits N 0)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = x
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_gate bits N 0)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_gate bits N 0)
          (update (cuccaro_input_F 2 false 0 x) 1 false) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_gate bits N 0)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 1
        = false := by
  rw [sqir_style_modAddConst_clean_gate_zero_eq]
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Gate.WellTyped at I = 0 < dim.
    show Gate.WellTyped (sqir_modmult_rev_anc bits) Gate.I
    show 0 < sqir_modmult_rev_anc bits
    unfold sqir_modmult_rev_anc; omega
  · -- target_val = x.
    show cuccaro_target_val bits 2
        (Gate.applyNat Gate.I (update (cuccaro_input_F 2 false 0 x) 1 false)) = x
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_target_val bits 2
          (update (cuccaro_input_F 2 false 0 x) 1 false) = x % 2 ^ bits := by
      apply cuccaro_target_val_eq_sum_when_bits_match
      intro i hi
      rw [update_neq _ _ _ _ (by omega : (2 + 2 * i + 1 : Nat) ≠ 1)]
      exact cuccaro_input_F_at_b 2 i false 0 x
    rw [h_eq]
    exact Nat.mod_eq_of_lt h_x_lt
  · -- read_val = 0.
    show cuccaro_read_val bits 2
        (Gate.applyNat Gate.I (update (cuccaro_input_F 2 false 0 x) 1 false)) = 0
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_read_val bits 2
          (update (cuccaro_input_F 2 false 0 x) 1 false) = 0 % 2 ^ bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      rw [update_neq _ _ _ _ (by omega : (2 + 2 * i + 2 : Nat) ≠ 1)]
      rw [cuccaro_input_F_at_a 2 i false 0 x]
    rw [h_eq]
    simp
  · -- top carry at 2 + 2*bits = false.
    rw [Gate.applyNat_I]
    rw [update_neq _ _ _ _ (by omega : (2 + 2 * bits : Nat) ≠ 1)]
    have h_eq : (2 : Nat) + 2 * bits = 2 + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 x]
    exact Nat.zero_testBit _
  · -- flag at 1 = false (update_eq).
    rw [Gate.applyNat_I]
    exact update_eq _ _ _

/-! ## Tick 64 — Deliverable C: total clean theorem. -/

/-- **HEADLINE Deliverable C — total clean modular add-constant theorem.**

For all `c < N` (including `c = 0`), the wrapper's output satisfies:
WellTyped + target = `(x+c) % N` + read = 0 + top carry = false +
flag = false. -/
theorem sqir_style_modAddConst_clean_gate_clean
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_modAddConst_clean_gate bits N c)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_gate bits N c)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = (x + c) % N
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_gate bits N c)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_gate bits N c)
          (update (cuccaro_input_F 2 false 0 x) 1 false) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_gate bits N c)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 1
        = false := by
  by_cases hc0 : c = 0
  · -- c = 0 case: target = x = (x + 0) % N.
    subst hc0
    have ⟨h_wt, h_tgt, h_rd, h_tc, h_fl⟩ :=
      sqir_style_modAddConst_clean_gate_zero_clean bits N x hbits hN_pos hN hx
    refine ⟨h_wt, ?_, h_rd, h_tc, h_fl⟩
    rw [h_tgt]
    -- x = (x + 0) % N
    rw [Nat.add_zero]
    exact (Nat.mod_eq_of_lt hx).symm
  · -- 0 < c case: dispatch to the clean candidate's bundle.
    have hc_pos : 0 < c := Nat.pos_of_ne_zero hc0
    have h_unfold : sqir_style_modAddConst_clean_gate bits N c
        = sqir_style_modAddConst_clean_candidate bits 2 N c 1 := by
      unfold sqir_style_modAddConst_clean_gate
      simp [hc0]
    rw [h_unfold]
    exact sqir_style_modAddConst_clean_candidate_clean bits N c x
      hbits hN_pos hN hN2 hc_pos hc hx

/-! ## Tick 64 — Deliverable D: `BasicSetting`-derived wrapper. -/

/-- **HEADLINE Deliverable D — BasicSetting-derived total clean
mod-add-constant theorem.**  At `bits := n + 1`, the SQIR-faithful
sizing `2*N ≤ 2^(n+1)` follows from `BasicSetting`, removing the
explicit `hN`, `hN2`, `hN_pos` preconditions. -/
theorem sqir_style_modAddConst_clean_gate_clean_from_BasicSetting
    (a r N m n c x : Nat)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (hc : c < N) (hx : x < N) :
    Gate.WellTyped (sqir_modmult_rev_anc (n + 1))
        (sqir_style_modAddConst_clean_gate (n + 1) N c)
    ∧ cuccaro_target_val (n + 1) 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_gate (n + 1) N c)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = (x + c) % N
    ∧ cuccaro_read_val (n + 1) 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_gate (n + 1) N c)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_gate (n + 1) N c)
          (update (cuccaro_input_F 2 false 0 x) 1 false) (2 + 2 * (n + 1))
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_gate (n + 1) N c)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 1
        = false := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have hN_le : N ≤ 2 ^ (n + 1) := by omega
  exact sqir_style_modAddConst_clean_gate_clean (n + 1) N c x
    (by omega : 1 ≤ n + 1) hN_pos hN_le hN2 hc hx

/-! ## Tick 64 — Deliverable E: controlled-modadd route analysis.

The clean modular add-constant gate (Deliverables A–D) is now total
over `c ∈ [0, N)` at the SQIR-faithful layout.  Phase 3 of the
modarith-to-modexp plan is **controlled modular addition** — needed
by the modular multiplier, which iterates over bits of the
multiplicand.

**Important warning (per Tick 64 directive):** do not assume
"control the whole clean modadd gate" works mechanically.  Two
routes to consider:

**Route 1 — Port SQIR's `bygatectrl` infrastructure.**

In Coq SQIR, `bygatectrl 1 g` builds a controlled version of `g`
gate-by-gate.  Each CX becomes CCX, each X becomes CX, etc.  Our
`Gate` IR (`I`, `X`, `CX`, `CCX`, `seq`) does not have a 4-qubit
gate, so any `CCX` inside the inner gate cannot be controlled
directly.  Inside the clean candidate, `CCX` appears (e.g., inside
`cuccaro_MAJ`).  Naive `bygatectrl` would require a 4-input gate
or an additional ancilla qubit.

**Route 2 — Build controlled mod-add-constant by masking the
constant.**

The clean candidate's first stage is `addConstGate(c)`, which adds
the constant `c` to the target.  If we replace this with a *masked*
add-constant — where the prepared `c` is XORed with the control bit
— then:
  - control = false ⇒ the masked-prepared read register is `0`, so
    addConstGate has no effect on the target (just runs the
    cuccaro adder with `a = 0`, which is identity at the target).
  - control = true ⇒ the masked-prepared read register is `c`, so
    addConstGate adds `c`.

The subsequent compareConst, conditionalSub, and flag-uncomputation
stages must also be control-aware.  Naively running them
unconditionally would give:
  - control = false: target unchanged = `x`.  Then compareConst
    computes `decide(N ≤ x) = false` (since `x < N`), so the flag
    XOR is no-op.  conditionalSub with flag = false is identity.
    Then the cleanup compareConst(c) computes `decide(c ≤ x)`,
    which is `false` iff `x < c`.  The `X(1)` flip then negates a
    bit that may or may not have been changed.  This DOES NOT
    cleanly handle the `control = false` case.

The cleanest path is therefore:

**Route 3 (selected for Tick 65) — Wrap the entire clean modadd
gate with a `bygatectrl`-style construction that controls every
gate operation by `control`.**  Since our IR has `CCX` but no
4-input gate, the strategy is:
  - `I` controlled by `ctrl` → `I`.
  - `X(q)` controlled by `ctrl` → `CX(ctrl, q)`.
  - `CX(c, t)` controlled by `ctrl` → `CCX(ctrl, c, t)`.
  - `CCX(a, b, c)` controlled by `ctrl` → would need 4-input; this
    is the structural problem.

The CCX gates inside the cuccaro_MAJ chain are the blocker.  Two
sub-options:
  (a) Use one ancilla `aux` qubit to decompose `controlled-CCX`:
      `CCX(ctrl, c, t)` becomes a Toffoli cascade through `aux`.
  (b) Replace the entire clean modular adder with a structurally
      different design (e.g., port SQIR's `modadder21` directly
      with control wired in at the masked-prepare level).

We will pursue option (b) for Tick 65 — masking the constant
via CX from `control` is structurally simpler and avoids the
auxiliary qubit.  The `compareConst` and conditional sub stages
must then be examined for whether their CCX content survives the
masking.

**Pending Tick 65 questions** (will be added to QUESTIONS.md):
  - Does masking `c` to `0` when `control = false` make the
    cleanup XOR + `X(1)` correctly identity?
  - Or must we ALSO mask `N` (in the comparator) by `control`?
    The cleanup uses `compareConst(c) ; X(1)`; if `c` is masked,
    `c = 0` would fire the broken `compareConst(0)` case (the
    `K = 2^bits` overflow).  We may need an additional guard. -/

/-! ## Tick 65 — Controlled SQIR modular add-constant: design + Task 3 + definitions.

**Route selected (per Python simulation, `scripts/check_sqir_controlled_modadd.py`):**
Route B — control-aware masked constants.  Candidate B (full-control)
passes all `bits ∈ {1..4}, 0 < N ≤ 2^bits / 2, 0 < c < N, x < N,
control ∈ {false, true}` test cases.  Candidate A (naive — control only
stage 1) FAILS for `control = false, c > 0` because the unconditional
cleanup `compareConst(c) ; X(1)` dirties the flag.  Candidate C
(Candidate B with `c = 0` wrapper) also passes, extending to `c = 0`.

**Controlled construction** (5 stages):
  1. `sqir_conditionalAddConstGate(bits, q_start, c, controlIdx)` — adds
     `c` to target iff `controlIdx`.
  2. `sqir_style_compareConst_candidate(bits, q_start, N, flagPos)` —
     UNCONDITIONAL: flag XOR `decide(N ≤ target)`.
  3. `sqir_conditionalSubConstGate(bits, q_start, N, flagPos)` —
     conditional on flag.
  4. `sqir_controlledCompareConst(bits, q_start, c, controlIdx, flagPos)` —
     masked cleanup; control-aware.
  5. `Gate.CX controlIdx flagPos` — control-aware flag flip.

When `control = false`:
- Stage 1 is identity (masked prepare ↔ K=0, full adder on `read = 0` =
  identity at target).
- Stage 2 sets flag := decide(N ≤ x) = false (since `x < N`).
- Stage 3 is identity (flag = false).
- Stage 4 is identity (masked prepare ↔ K=0; compareConst on read=0
  gives top_carry = decide(target ≥ 2^bits) = false; no flag change).
- Stage 5 (CX with control=false) is identity.
- Net: target = x, flag = false, controlIdx preserved. ✓

When `control = true`:
- Stage 1 = `addConstGate(c)` (via `apply_true_fun`).
- Stages 2-3 = unconditional dirtyFlag's compareConst(N) and conditionalSub(N).
- Stage 4 = `compareConst(c)` (masked prepare with control=true = unmasked).
- Stage 5 (CX with control=true) = `X(flagPos)`.
- Net = Tick 63 `clean_candidate`'s chain: target = (x+c) % N, flag = false. ✓
-/

/-! ## Tick 65 Task 3 — controlled add-mod-2^bits theorem (alias).

The existing `sqir_conditionalAddConstGate_target_decode` already
provides this; we re-expose it under the controlled-add semantic
name. -/

/-- **HEADLINE Task 3 — controlled add-mod-2^bits target decode.** -/
theorem sqir_controlledAddConstPow2_target_decode
    (bits q_start c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_conditionalAddConstGate bits q_start c controlIdx)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control))
      = (x + (if control then c else 0)) % 2^bits :=
  sqir_conditionalAddConstGate_target_decode bits q_start c x controlIdx control
    hbits hc hx h_control_distinct h_control_out

/-! ## Tick 65 — Definitions: controlled compareConst, candidate, wrapper. -/

/-- **Controlled compareConst** — masked-prepare variant of
`sqir_style_compareConst_candidate`.  When `controlIdx = false`,
identity at every position; when `controlIdx = true`, equivalent to
`sqir_style_compareConst_candidate bits q_start c flagPos`. -/
def sqir_controlledCompareConst
    (bits q_start c controlIdx flagPos : Nat) : Gate :=
  seq (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)
      (seq (cuccaro_maj_chain bits q_start)
           (seq (Gate.CX (q_start + 2 * bits) flagPos)
                (seq (cuccaro_maj_chain_inv bits q_start)
                     (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx))))

/-- **Controlled SQIR-style mod-N add-constant candidate** for `0 < c`. -/
def sqir_style_controlledModAddConst_candidate
    (bits q_start N c controlIdx flagPos : Nat) : Gate :=
  seq (sqir_conditionalAddConstGate bits q_start c controlIdx)
      (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
           (seq (sqir_conditionalSubConstGate bits q_start N flagPos)
                (seq (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
                     (Gate.CX controlIdx flagPos))))

/-- **Total controlled SQIR mod-N add-constant** wrapper handling `c = 0`. -/
def sqir_style_controlledModAddConst_gate
    (bits q_start N c controlIdx flagPos : Nat) : Gate :=
  if c = 0 then Gate.I
  else sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos

/-! ## Status note (Tick 65 part 1).

Landed (kernel-clean):
- Definition of `sqir_controlledCompareConst`.
- Definition of `sqir_style_controlledModAddConst_candidate`.
- Definition of `sqir_style_controlledModAddConst_gate` (total wrapper).
- Task 3 alias `sqir_controlledAddConstPow2_target_decode`.

**Not landed this tick** (Tick 66 work — explicitly deferred):
- `sqir_style_controlledModAddConst_*_target_decode` for the candidate
  (the per-control target value theorem).
- Full clean bundle (WellTyped + target + workspace + flag + control).
- BasicSetting-derived specialization.

Reason for deferral: the semantic theorems require chain-reduction
through 5 controlled stages with case-split on `control`.  Tick 65's
deliverable focus per directive is "first semantic theorem" — and
Task 3 provides one (the controlled add-mod-2^bits target decode),
empirically validating the controlled add primitive that drives
stage 1.  Simulation (Task 2) provides empirical validation of the
full controlled candidate; Tick 66 will land the formal semantic
theorems following the design now confirmed.

**Simulation result** (`scripts/check_sqir_controlled_modadd.py`):
- Candidate B (controlled stages 1, 4, 5): PASSES 380/380 for
  `bits ∈ {1..4}, 0 < N ≤ 2^bits/2, 0 < c < N, x < N`.
- Candidate C (B + c=0 wrapper): PASSES 480/480 over the same range
  with `c ∈ [0, N)`.
- Candidate A (naive — control only stage 1): FAILS (95 fails for
  `control = false` due to spurious flag from the unconditional
  cleanup). -/

/-! ## Tick 66 — Controlled SQIR mod-N add semantic correctness.

This tick proves the target_decode theorem (Deliverable C) for the
controlled mod-N add candidate by case-splitting on `control`, plus
the total wrapper target_decode (Deliverable F) and a BasicSetting-
derived specialization (Deliverable G).

The full clean bundle (Deliverables A, B, D, E with workspace/flag
conjuncts) is deferred to Tick 67 — the position-level chain
analysis through all 5 controlled stages for read/carry/flag
positions is substantial enough to merit its own tick. -/

/-- **Helper — `ctrlCompare` reduces to `compareConst(c)` when
`state[controlIdx] = true`.**  Function-level equality. -/
theorem sqir_controlledCompareConst_at_control_true_eq_unmasked_fun
    (bits q_start c controlIdx flagPos : Nat) (g : Nat → Bool)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (h_control_ne_flag : controlIdx ≠ flagPos)
    (h_control_true : g controlIdx = true) :
    Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos) g
      = Gate.applyNat (sqir_style_compareConst_candidate bits q_start c flagPos) g := by
  show Gate.applyNat
      (seq (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx))))) g
    = Gate.applyNat
        (seq (cuccaro_prepareConstRead bits q_start (2^bits - c))
              (seq (cuccaro_maj_chain bits q_start)
                   (seq (Gate.CX (q_start + 2 * bits) flagPos)
                        (seq (cuccaro_maj_chain_inv bits q_start)
                             (cuccaro_prepareConstRead bits q_start (2^bits - c)))))) g
  simp only [Gate.applyNat_seq]
  -- Inner-most masked prepare → unmasked (state at controlIdx = true).
  rw [sqir_prepareMaskedConstRead_eq_unmasked_fun bits q_start (2^bits - c) controlIdx g
        h_control_distinct h_control_true]
  -- Outer masked prepare → unmasked.  Need state at controlIdx after the
  -- inner stages = true.  The inner stages (prepare, maj_chain, CX, maj_chain_inv)
  -- all preserve controlIdx because it's outside workspace and ≠ flagPos.
  have h_inner_ctrl_preserved :
      Gate.applyNat (cuccaro_maj_chain_inv bits q_start)
        (Gate.applyNat (Gate.CX (q_start + 2 * bits) flagPos)
          (Gate.applyNat (cuccaro_maj_chain bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - c)) g))) controlIdx
        = true := by
    rcases h_control_out with h_below | h_above
    · rw [cuccaro_maj_chain_inv_frame_below bits q_start _ controlIdx h_below]
      rw [Gate.applyNat_CX, update_neq _ _ _ _ h_control_ne_flag]
      rw [cuccaro_maj_chain_frame_below bits q_start _ controlIdx h_below]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - c) controlIdx
            h_control_distinct]
      exact h_control_true
    · rw [cuccaro_maj_chain_inv_frame_above bits q_start _ controlIdx h_above]
      rw [Gate.applyNat_CX, update_neq _ _ _ _ h_control_ne_flag]
      rw [cuccaro_maj_chain_frame_above bits q_start _ controlIdx h_above]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - c) controlIdx
            h_control_distinct]
      exact h_control_true
  rw [sqir_prepareMaskedConstRead_eq_unmasked_fun bits q_start (2^bits - c) controlIdx _
        h_control_distinct h_inner_ctrl_preserved]

/-! ## Tick 66 — Total wrapper c = 0 case (partial Deliverable F). -/

/-- **Total wrapper at c = 0 reduces to `Gate.I`.** -/
theorem sqir_style_controlledModAddConst_gate_zero_eq
    (bits N controlIdx : Nat) :
    sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1 = Gate.I := by
  unfold sqir_style_controlledModAddConst_gate; simp

/-- **HEADLINE partial Deliverable F — c = 0 bundle for the controlled
modular add-constant wrapper.** -/
theorem sqir_style_controlledModAddConst_gate_zero_clean
    (bits N x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = x
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) 1
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx
        = control := by
  rw [sqir_style_controlledModAddConst_gate_zero_eq]
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Gate.WellTyped (sqir_modmult_rev_anc bits) Gate.I
    show 0 < sqir_modmult_rev_anc bits
    unfold sqir_modmult_rev_anc; omega
  · -- target_val = x.
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_target_val bits 2
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) = x % 2 ^ bits := by
      apply cuccaro_target_val_eq_sum_when_bits_match
      intro i hi
      have h_ne : (2 + 2 * i + 1 : Nat) ≠ controlIdx := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      rw [update_neq _ _ _ _ h_ne]
      exact cuccaro_input_F_at_b 2 i false 0 x
    rw [h_eq]
    exact Nat.mod_eq_of_lt h_x_lt
  · -- read_val = 0.
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_read_val bits 2
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) = 0 % 2 ^ bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      have h_ne : (2 + 2 * i + 2 : Nat) ≠ controlIdx := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      rw [update_neq _ _ _ _ h_ne]
      rw [cuccaro_input_F_at_a 2 i false 0 x]
    rw [h_eq]
    simp
  · -- top carry at 2 + 2*bits.
    rw [Gate.applyNat_I]
    have h_ne : (2 + 2 * bits : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    have h_eq : (2 : Nat) + 2 * bits = 2 + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 x]
    exact Nat.zero_testBit _
  · -- flag at 1.
    rw [Gate.applyNat_I]
    rw [update_neq _ _ _ _ hcontrol_ne_flag.symm]
    -- cuccaro_input_F at 1 = false (since 1 < q_start = 2).
    unfold cuccaro_input_F
    rw [if_pos (by omega : (1 : Nat) < 2)]
  · -- controlIdx = control.
    rw [Gate.applyNat_I]
    exact update_eq _ _ _

/-! ## Tick 67 — Closing the controlled mod-N add chain.

Stage helpers to compose into the full controlled candidate's
semantic theorem. -/

/-- **Deliverable B — CX with control = false is identity.** -/
theorem Gate.applyNat_CX_at_control_false_eq_id_fun
    (control target : Nat) (f : Nat → Bool) (h : f control = false) :
    Gate.applyNat (Gate.CX control target) f = f := by
  funext q
  rw [Gate.applyNat_CX, h, Bool.xor_false]
  by_cases hq : q = target
  · rw [hq, update_eq]
  · rw [update_neq _ _ _ _ hq]

/-- **Deliverable B — CX with control = true equals X(target).** -/
theorem Gate.applyNat_CX_at_control_true_eq_X_fun
    (control target : Nat) (f : Nat → Bool) (h : f control = true) :
    Gate.applyNat (Gate.CX control target) f = Gate.applyNat (Gate.X target) f := by
  rw [Gate.applyNat_CX, Gate.applyNat_X, h]
  congr 1
  cases f target <;> rfl

/-- **Helper — maj_chain on `cuccaro_input_F` with `a = 0` has top carry = false.**
Derived from `cuccaro_compareConstForward_top_carry` with `N = 2^bits`
(reducing the prepare to identity). -/
theorem cuccaro_maj_chain_top_carry_on_input_F_zero_a
    (bits q_start x : Nat) (hbits : 1 ≤ bits) (hx : x < 2^bits) :
    Gate.applyNat (cuccaro_maj_chain bits q_start)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * bits) = false := by
  have h_pos : 0 < (2 : Nat)^bits := Nat.two_pow_pos bits
  have h := cuccaro_compareConstForward_top_carry bits q_start (2^bits) x h_pos
              (le_refl _) hx
  unfold cuccaro_compareConstForwardGate at h
  simp only [Gate.applyNat_seq] at h
  have h_K : (2 : Nat)^bits - 2^bits = 0 := by omega
  rw [h_K] at h
  rw [cuccaro_prepareConstRead_zero_eq_id_fun] at h
  simp [Nat.not_le.mpr hx] at h
  exact h

/-- **Deliverable A — controlled comparator at control = false is identity
on `cuccaro_input_F`-shaped input.** -/
theorem sqir_controlledCompareConst_at_control_false_on_input_F_eq_id_fun
    (bits q_start c controlIdx flagPos x : Nat)
    (hbits : 1 ≤ bits) (hx : x < 2^bits)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (h_control_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
        (update (cuccaro_input_F q_start false 0 x) controlIdx false)
      = update (cuccaro_input_F q_start false 0 x) controlIdx false := by
  set F := cuccaro_input_F q_start false 0 x with hF_def
  show Gate.applyNat
      (seq (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)))))
      (update F controlIdx false)
    = update F controlIdx false
  simp only [Gate.applyNat_seq]
  -- Stage 1: masked prepare with ctrl=false → identity.
  have h_input_ctrl : (update F controlIdx false) controlIdx = false := update_eq _ _ _
  rw [sqir_prepareMaskedConstRead_eq_id_fun bits q_start (2^bits - c) controlIdx
        (update F controlIdx false) h_control_distinct h_input_ctrl]
  -- Stage 3 (CX): need state at top = false.
  -- State entering CX = applyNat maj_chain (update F controlIdx false).
  have h_top_state : Gate.applyNat (cuccaro_maj_chain bits q_start)
        (update F controlIdx false) (q_start + 2 * bits) = false := by
    rw [cuccaro_maj_chain_commute_update_outside_workspace bits q_start controlIdx false F
          h_control_out]
    have h_ne : q_start + 2 * bits ≠ controlIdx := by
      rcases h_control_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    exact cuccaro_maj_chain_top_carry_on_input_F_zero_a bits q_start x hbits hx
  -- CX is identity (xor with false → no change).
  rw [Gate.applyNat_CX_at_control_false_eq_id_fun (q_start + 2 * bits) flagPos _ h_top_state]
  -- Stage 4: maj_chain_inv ∘ maj_chain = id.
  rw [cuccaro_maj_chain_inv_after_chain_eq_id bits q_start (update F controlIdx false)]
  -- Stage 5: masked prepare with state[ctrl] = false (still true after the no-op chain).
  rw [sqir_prepareMaskedConstRead_eq_id_fun bits q_start (2^bits - c) controlIdx
        (update F controlIdx false) h_control_distinct h_input_ctrl]

/-! ## Tick 68 — Compose controlled mod-N add chain. -/

/-- **Deliverable A — uncontrolled comparator identity on `cuccaro_input_F`
when `x < N`.**  Since `decide(N ≤ x) = false`, the comparator XORs false
into flagPos (no change), and workspace + outside positions are preserved. -/
theorem sqir_style_compareConst_candidate_on_input_F_x_lt_N_eq_id_fun
    (bits N x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N) :
    Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
        (cuccaro_input_F 2 false 0 x)
      = cuccaro_input_F 2 false 0 x := by
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have hflag_out : (1 : Nat) < 2 ∨ 2 + 2 * bits + 1 ≤ 1 := Or.inl (by omega)
  funext q
  by_cases hq_flag : q = 1
  · rw [hq_flag]
    rw [sqir_style_compareConst_candidate_flag_general bits 2 N x 1
          hN_pos hN h_x_lt hflag_out]
    have h_F1 : cuccaro_input_F 2 false 0 x 1 = false := by
      unfold cuccaro_input_F; rw [if_pos (by omega : (1 : Nat) < 2)]
    rw [h_F1]
    exact decide_eq_false (Nat.not_le.mpr hx)
  · by_cases hq_ws : 2 ≤ q ∧ q < 2 + 2 * bits + 1
    · exact sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 N 1
        _ hflag_out q hq_ws.1 hq_ws.2
    · push_neg at hq_ws
      have h_q_outside : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := by
        by_cases h : q < 2
        · left; exact h
        · push_neg at h; right; exact hq_ws h
      exact sqir_style_compareConst_candidate_frame_outside bits 2 N 1
        _ q hq_flag h_q_outside

/-! ## Tick 68 — Stage helpers on `cuccaro_input_F` directly (with bridging). -/

/-- **Helper — `cuccaro_input_F` at `controlIdx` outside workspace is `false`.** -/
theorem cuccaro_input_F_at_controlIdx_outside_eq_false
    (bits x controlIdx : Nat) (hx : x < 2^bits)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx) :
    cuccaro_input_F 2 false 0 x controlIdx = false :=
  cuccaro_input_F_at_outside_eq_false 2 bits x controlIdx hcontrol_out hx

/-- **Helper — `update F controlIdx false = F` when F at controlIdx is false.** -/
theorem update_input_F_controlIdx_false_eq_F
    (bits x controlIdx : Nat) (hx : x < 2^bits)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx) :
    update (cuccaro_input_F 2 false 0 x) controlIdx false
      = cuccaro_input_F 2 false 0 x := by
  funext q
  by_cases hq : q = controlIdx
  · rw [hq, update_eq]
    exact (cuccaro_input_F_at_controlIdx_outside_eq_false bits x controlIdx hx hcontrol_out).symm
  · rw [update_neq _ _ _ _ hq]

/-! ## Tick 68 — Deliverable C: control=false candidate state_eq. -/

/-- **HEADLINE Deliverable C — control = false state equality for the
controlled mod-N add candidate.** -/
theorem sqir_style_controlledModAddConst_candidate_control_false_state_eq
    (bits N c x controlIdx : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
        (update (cuccaro_input_F 2 false 0 x) controlIdx false)
      = update (cuccaro_input_F 2 false 0 x) controlIdx false := by
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have h_F_at_ctrl : cuccaro_input_F 2 false 0 x controlIdx = false :=
    cuccaro_input_F_at_controlIdx_outside_eq_false bits x controlIdx h_x_lt hcontrol_out
  have h_input_eq : update (cuccaro_input_F 2 false 0 x) controlIdx false
                  = cuccaro_input_F 2 false 0 x :=
    update_input_F_controlIdx_false_eq_F bits x controlIdx h_x_lt hcontrol_out
  rw [h_input_eq]
  -- Now: applyNat candidate F = F.
  show Gate.applyNat
      (seq (sqir_conditionalAddConstGate bits 2 c controlIdx)
            (seq (sqir_style_compareConst_candidate bits 2 N 1)
                 (seq (sqir_conditionalSubConstGate bits 2 N 1)
                      (seq (sqir_controlledCompareConst bits 2 c controlIdx 1)
                           (Gate.CX controlIdx 1)))))
      (cuccaro_input_F 2 false 0 x) = _
  simp only [Gate.applyNat_seq]
  -- Hypothesis on controlIdx not being a read position.
  have h_control_distinct : ∀ i, i < bits → controlIdx ≠ 2 + 2 * i + 2 := by
    intros i _ heq
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  -- Stage 1: condAdd with input[controlIdx]=false → full_adder → identity on F.
  have h_stage1 : Gate.applyNat (sqir_conditionalAddConstGate bits 2 c controlIdx)
        (cuccaro_input_F 2 false 0 x) = cuccaro_input_F 2 false 0 x := by
    rw [sqir_conditionalAddConstGate_apply_false_fun bits 2 c controlIdx
          (cuccaro_input_F 2 false 0 x) h_control_distinct h_F_at_ctrl hcontrol_out]
    rw [← cuccaro_addConstGate_zero_eq_full_adder_fun]
    have h_pos : 0 < (2 : Nat)^bits := Nat.two_pow_pos bits
    rw [cuccaro_addConstGate_output_eq_cuccaro_input_F bits 2 0 x hbits h_pos h_x_lt
          (by omega : x + 0 < 2^bits)]
    simp [Nat.add_zero]
  rw [h_stage1]
  -- Stage 2: compareConst F = F (for x < N).
  rw [sqir_style_compareConst_candidate_on_input_F_x_lt_N_eq_id_fun bits N x hbits hN_pos hN hx]
  -- Stage 3: condSub with input[1]=false → full_adder → identity on F.
  have h_F_at_1 : cuccaro_input_F 2 false 0 x 1 = false := by
    unfold cuccaro_input_F; rw [if_pos (by omega : (1 : Nat) < 2)]
  have h_flag_distinct : ∀ i, i < bits → (1 : Nat) ≠ 2 + 2 * i + 2 := fun i _ => by omega
  have h_flag_out : (1 : Nat) < 2 ∨ 2 + 2 * bits + 1 ≤ 1 := Or.inl (by omega)
  have h_stage3 : Gate.applyNat (sqir_conditionalSubConstGate bits 2 N 1)
        (cuccaro_input_F 2 false 0 x) = cuccaro_input_F 2 false 0 x := by
    unfold sqir_conditionalSubConstGate
    rw [sqir_conditionalAddConstGate_apply_false_fun bits 2 (2^bits - N) 1
          (cuccaro_input_F 2 false 0 x) h_flag_distinct h_F_at_1 h_flag_out]
    rw [← cuccaro_addConstGate_zero_eq_full_adder_fun]
    have h_pos : 0 < (2 : Nat)^bits := Nat.two_pow_pos bits
    rw [cuccaro_addConstGate_output_eq_cuccaro_input_F bits 2 0 x hbits h_pos h_x_lt
          (by omega : x + 0 < 2^bits)]
    simp [Nat.add_zero]
  rw [h_stage3]
  -- Stage 4: ctrlCompare with input[controlIdx]=false → identity on F.
  -- Use Tick 67's theorem, bridging F ↔ update F controlIdx false.
  have h_stage4 : Gate.applyNat (sqir_controlledCompareConst bits 2 c controlIdx 1)
        (cuccaro_input_F 2 false 0 x) = cuccaro_input_F 2 false 0 x := by
    rw [show cuccaro_input_F 2 false 0 x
        = update (cuccaro_input_F 2 false 0 x) controlIdx false from h_input_eq.symm]
    exact sqir_controlledCompareConst_at_control_false_on_input_F_eq_id_fun
      bits 2 c controlIdx 1 x hbits h_x_lt h_control_distinct hcontrol_out
      (fun h => hcontrol_ne_flag h)
  rw [h_stage4]
  -- Stage 5: CX(controlIdx, 1) with state[controlIdx]=false → identity.
  exact Gate.applyNat_CX_at_control_false_eq_id_fun controlIdx 1
    (cuccaro_input_F 2 false 0 x) h_F_at_ctrl

/-! ## Tick 68 — Control = false target / workspace consequences. -/

/-- **Control=false target decode = x.** -/
theorem sqir_style_controlledModAddConst_candidate_target_decode_control_false
    (bits N c x controlIdx : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    cuccaro_target_val bits 2
        (Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx false))
      = x := by
  rw [sqir_style_controlledModAddConst_candidate_control_false_state_eq
        bits N c x controlIdx hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag]
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have h_eq : cuccaro_target_val bits 2
        (update (cuccaro_input_F 2 false 0 x) controlIdx false) = x % 2 ^ bits := by
    apply cuccaro_target_val_eq_sum_when_bits_match
    intro i hi
    have h_ne : (2 + 2 * i + 1 : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    exact cuccaro_input_F_at_b 2 i false 0 x
  rw [h_eq]
  exact Nat.mod_eq_of_lt h_x_lt

/-! ## Phase R7d^xxix-L-3.6′ — q_start-parametric ports

The five q_start-parametric ports below mirror the corresponding
q_start = 2 / flagPos = 1 helpers above. They unlock the
Architecture D selected-add no-op proofs by providing the
control = false target-decode at the shifted layout.

The proofs are mechanical parameter-substituted copies; all
subordinate lemmas were already q_start-parametric (we verified
this during R7d^xxix-L-3.6′ planning). -/

/-- **q_start-parametric variant** of
`cuccaro_input_F_at_controlIdx_outside_eq_false`. Same fact, fully
parametric. -/
theorem cuccaro_input_F_at_controlIdx_outside_eq_false_qstart
    (q_start bits x controlIdx : Nat) (hx : x < 2^bits)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    cuccaro_input_F q_start false 0 x controlIdx = false :=
  cuccaro_input_F_at_outside_eq_false q_start bits x controlIdx hcontrol_out hx

/-- **q_start-parametric variant** of `update_input_F_controlIdx_false_eq_F`. -/
theorem update_input_F_controlIdx_false_eq_F_qstart
    (q_start bits x controlIdx : Nat) (hx : x < 2^bits)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    update (cuccaro_input_F q_start false 0 x) controlIdx false
      = cuccaro_input_F q_start false 0 x := by
  funext q
  by_cases hq : q = controlIdx
  · rw [hq, update_eq]
    exact (cuccaro_input_F_at_controlIdx_outside_eq_false_qstart q_start bits x controlIdx hx
      hcontrol_out).symm
  · rw [update_neq _ _ _ _ hq]

/-- **q_start-parametric variant** of
`sqir_style_compareConst_candidate_on_input_F_x_lt_N_eq_id_fun`.
Adds an explicit `hflag_out` hypothesis so `flagPos` can be at any
outside-workspace position. -/
theorem sqir_style_compareConst_candidate_on_input_F_x_lt_N_eq_id_fun_qstart
    (bits q_start N flagPos x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (cuccaro_input_F q_start false 0 x)
      = cuccaro_input_F q_start false 0 x := by
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  funext q
  by_cases hq_flag : q = flagPos
  · rw [hq_flag]
    rw [sqir_style_compareConst_candidate_flag_general bits q_start N x flagPos
          hN_pos hN h_x_lt hflag_out]
    have h_F_at_flag : cuccaro_input_F q_start false 0 x flagPos = false :=
      cuccaro_input_F_at_controlIdx_outside_eq_false_qstart q_start bits x flagPos h_x_lt
        hflag_out
    rw [h_F_at_flag]
    exact decide_eq_false (Nat.not_le.mpr hx)
  · by_cases hq_ws : q_start ≤ q ∧ q < q_start + 2 * bits + 1
    · exact sqir_style_compareConst_candidate_workspace_restored_at_general bits q_start N flagPos
        _ hflag_out q hq_ws.1 hq_ws.2
    · push_neg at hq_ws
      have h_q_outside : q < q_start ∨ q_start + 2 * bits + 1 ≤ q := by
        by_cases h : q < q_start
        · left; exact h
        · push_neg at h; right; exact hq_ws h
      exact sqir_style_compareConst_candidate_frame_outside bits q_start N flagPos
        _ q hq_flag h_q_outside

/-- **q_start-parametric variant** of
`sqir_style_controlledModAddConst_candidate_control_false_state_eq`.
When the control is false, the controlled mod-add candidate is the
identity on the appropriate base state. Parametric in both
`q_start` and `flagPos`. -/
theorem sqir_style_controlledModAddConst_candidate_control_false_state_eq_qstart
    (bits q_start N c x controlIdx flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
        (update (cuccaro_input_F q_start false 0 x) controlIdx false)
      = update (cuccaro_input_F q_start false 0 x) controlIdx false := by
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have h_F_at_ctrl : cuccaro_input_F q_start false 0 x controlIdx = false :=
    cuccaro_input_F_at_controlIdx_outside_eq_false_qstart q_start bits x controlIdx h_x_lt
      hcontrol_out
  have h_input_eq : update (cuccaro_input_F q_start false 0 x) controlIdx false
                  = cuccaro_input_F q_start false 0 x :=
    update_input_F_controlIdx_false_eq_F_qstart q_start bits x controlIdx h_x_lt hcontrol_out
  rw [h_input_eq]
  show Gate.applyNat
      (seq (sqir_conditionalAddConstGate bits q_start c controlIdx)
            (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                 (seq (sqir_conditionalSubConstGate bits q_start N flagPos)
                      (seq (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
                           (Gate.CX controlIdx flagPos)))))
      (cuccaro_input_F q_start false 0 x) = _
  simp only [Gate.applyNat_seq]
  have h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2 := by
    intros i _ heq
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  -- Stage 1: condAdd with control=false → full_adder → identity on F.
  have h_stage1 : Gate.applyNat (sqir_conditionalAddConstGate bits q_start c controlIdx)
        (cuccaro_input_F q_start false 0 x) = cuccaro_input_F q_start false 0 x := by
    rw [sqir_conditionalAddConstGate_apply_false_fun bits q_start c controlIdx
          (cuccaro_input_F q_start false 0 x) h_control_distinct h_F_at_ctrl hcontrol_out]
    rw [← cuccaro_addConstGate_zero_eq_full_adder_fun]
    have h_pos : 0 < (2 : Nat)^bits := Nat.two_pow_pos bits
    rw [cuccaro_addConstGate_output_eq_cuccaro_input_F bits q_start 0 x hbits h_pos h_x_lt
          (by omega : x + 0 < 2^bits)]
    simp [Nat.add_zero]
  rw [h_stage1]
  -- Stage 2: compareConst F = F (for x < N).
  rw [sqir_style_compareConst_candidate_on_input_F_x_lt_N_eq_id_fun_qstart bits q_start N flagPos
        x hbits hN_pos hN hx hflag_out]
  -- Stage 3: condSub with flag input = false → identity on F.
  have h_F_at_flag : cuccaro_input_F q_start false 0 x flagPos = false :=
    cuccaro_input_F_at_controlIdx_outside_eq_false_qstart q_start bits x flagPos h_x_lt hflag_out
  have h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2 := by
    intros i _ heq
    rcases hflag_out with hl | hr
    · omega
    · omega
  have h_stage3 : Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos)
        (cuccaro_input_F q_start false 0 x) = cuccaro_input_F q_start false 0 x := by
    unfold sqir_conditionalSubConstGate
    rw [sqir_conditionalAddConstGate_apply_false_fun bits q_start (2^bits - N) flagPos
          (cuccaro_input_F q_start false 0 x) h_flag_distinct h_F_at_flag hflag_out]
    rw [← cuccaro_addConstGate_zero_eq_full_adder_fun]
    have h_pos : 0 < (2 : Nat)^bits := Nat.two_pow_pos bits
    rw [cuccaro_addConstGate_output_eq_cuccaro_input_F bits q_start 0 x hbits h_pos h_x_lt
          (by omega : x + 0 < 2^bits)]
    simp [Nat.add_zero]
  rw [h_stage3]
  -- Stage 4: ctrlCompare with state[controlIdx]=false → identity on F.
  have h_stage4 : Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
        (cuccaro_input_F q_start false 0 x) = cuccaro_input_F q_start false 0 x := by
    rw [show cuccaro_input_F q_start false 0 x
        = update (cuccaro_input_F q_start false 0 x) controlIdx false from h_input_eq.symm]
    exact sqir_controlledCompareConst_at_control_false_on_input_F_eq_id_fun
      bits q_start c controlIdx flagPos x hbits h_x_lt h_control_distinct hcontrol_out
      hcontrol_ne_flag
  rw [h_stage4]
  -- Stage 5: CX(controlIdx, flagPos) with state[controlIdx]=false → identity.
  exact Gate.applyNat_CX_at_control_false_eq_id_fun controlIdx flagPos
    (cuccaro_input_F q_start false 0 x) h_F_at_ctrl

/-- **PRIMARY L-3.6′ DELIVERABLE: q_start-parametric control = false
target-decode.** The candidate controlled mod-add gate, applied to the
zero-accumulator Cuccaro base with the control bit set to false,
decodes to `x` at the target. Parametric in both `q_start` and
`flagPos`. -/
theorem sqir_style_controlledModAddConst_candidate_target_decode_control_false_qstart
    (bits q_start N c x controlIdx flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false))
      = x := by
  rw [sqir_style_controlledModAddConst_candidate_control_false_state_eq_qstart
        bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag]
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have h_eq : cuccaro_target_val bits q_start
        (update (cuccaro_input_F q_start false 0 x) controlIdx false) = x % 2 ^ bits := by
    apply cuccaro_target_val_eq_sum_when_bits_match
    intro i hi
    have h_ne : (q_start + 2 * i + 1 : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    exact cuccaro_input_F_at_b q_start i false 0 x
  rw [h_eq]
  exact Nat.mod_eq_of_lt h_x_lt

/-- **R7d^xxix-L-3.7′ DELIVERABLE: q_start-parametric control=false
workspace bundle (4-conjunct).**

Mirrors `sqir_style_controlledModAddConst_candidate_workspace_control_false`
but parametric in `q_start` and `flagPos`.  Both `controlIdx` and
`flagPos` must lie OUTSIDE the Cuccaro workspace
`[q_start, q_start + 2 * bits + 1)` and be distinct.

After the candidate gate applied to `(update F controlIdx false)`:
1. `cuccaro_read_val bits q_start` of the output = 0;
2. position `q_start + 2 * bits` (top carry) = false;
3. position `flagPos` = false;
4. position `controlIdx` = false.

Closes via the already-landed
`sqir_style_controlledModAddConst_candidate_control_false_state_eq_qstart`. -/
theorem sqir_style_controlledModAddConst_candidate_workspace_control_false_qstart
    (bits q_start N c x controlIdx flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) flagPos
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) controlIdx
        = false := by
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  rw [sqir_style_controlledModAddConst_candidate_control_false_state_eq_qstart
        bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- read = 0.
    have h_eq : cuccaro_read_val bits q_start
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) = 0 % 2 ^ bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      have h_ne : (q_start + 2 * i + 2 : Nat) ≠ controlIdx := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      rw [update_neq _ _ _ _ h_ne]
      rw [cuccaro_input_F_at_a q_start i false 0 x]
    rw [h_eq]; simp
  · -- top carry = false.
    have h_ne : (q_start + 2 * bits : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    have h_eq : q_start + 2 * bits = q_start + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a q_start (bits - 1) false 0 x]
    exact Nat.zero_testBit _
  · -- flag = false.
    rw [update_neq _ _ _ _ hcontrol_ne_flag.symm]
    exact cuccaro_input_F_at_outside_eq_false q_start bits x flagPos hflag_out h_x_lt
  · -- controlIdx = false.
    exact update_eq _ _ _

/-- **R7d^xxix-L-3.8′ DELIVERABLE: q_start-parametric control=false
clean bundle.**

Bundles the already-proved q_start-parametric facts for
`sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx
flagPos` applied to `(update F controlIdx false)`:

1. `Gate.WellTyped dim` of the candidate gate.
2. target decoded value = `x` (no-op on the target).
3. read register = 0.
4. top carry position (`q_start + 2 * bits`) = false.
5. `flagPos` = false.
6. `controlIdx` = false.

Parametric in `q_start`, `flagPos`, `controlIdx`, AND the ambient
dimension `dim`.  Wrapper over:
- `sqir_style_controlledModAddConst_candidate_target_decode_control_false_qstart`,
- `sqir_style_controlledModAddConst_candidate_workspace_control_false_qstart`,
- the five existing q_start-parametric WellTyped sub-lemmas
  (`sqir_conditionalAddConstGate_wellTyped`,
  `sqir_style_compareConst_candidate_wellTyped`,
  `sqir_conditionalSubConstGate_wellTyped`,
  `cuccaro_maj_chain_wellTyped`,
  `cuccaro_maj_chain_inv_wellTyped`,
  `sqir_prepareMaskedConstRead_wellTyped`).

No new infrastructure introduced; control=true direction NOT touched. -/
theorem sqir_style_controlledModAddConst_candidate_clean_control_false_qstart
    (bits q_start N c x dim controlIdx flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_control_lt_dim : controlIdx < dim)
    (h_flag_lt_dim : flagPos < dim) :
    Gate.WellTyped dim
        (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx false))
        = x
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) flagPos
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) controlIdx
        = false := by
  have h_target :=
    sqir_style_controlledModAddConst_candidate_target_decode_control_false_qstart
      bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
      hcontrol_out hflag_out hcontrol_ne_flag
  obtain ⟨h_rd, h_tc, h_fl, h_ctrl⟩ :=
    sqir_style_controlledModAddConst_candidate_workspace_control_false_qstart
      bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
      hcontrol_out hflag_out hcontrol_ne_flag
  refine ⟨?_, h_target, h_rd, h_tc, h_fl, h_ctrl⟩
  -- WellTyped: 5-stage proof mirroring the hard-coded `_candidate_clean`
  -- but with q_start and flagPos free.
  show Gate.WellTyped dim
      (seq (sqir_conditionalAddConstGate bits q_start c controlIdx)
            (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                 (seq (sqir_conditionalSubConstGate bits q_start N flagPos)
                      (seq (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
                           (Gate.CX controlIdx flagPos)))))
  have h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2 := by
    intros i _ heq
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  have h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2 := by
    intros i _ heq
    rcases hflag_out with hl | hr
    · omega
    · omega
  have h_top_lt_dim : q_start + 2 * bits < dim := by omega
  have h_top_ne_flag : (q_start + 2 * bits : Nat) ≠ flagPos := by
    rcases hflag_out with hl | hr
    · omega
    · omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact sqir_conditionalAddConstGate_wellTyped bits q_start c controlIdx dim
      h_workspace h_control_lt_dim h_control_distinct
  · exact sqir_style_compareConst_candidate_wellTyped bits q_start N flagPos dim
      h_workspace h_flag_lt_dim (Ne.symm h_top_ne_flag)
  · exact sqir_conditionalSubConstGate_wellTyped bits q_start N flagPos dim
      h_workspace h_flag_lt_dim h_flag_distinct
  · -- WellTyped for `sqir_controlledCompareConst` (5-stage subseq).
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact sqir_prepareMaskedConstRead_wellTyped bits q_start (2^bits - c) controlIdx
        dim h_workspace h_control_lt_dim h_control_distinct
    · exact cuccaro_maj_chain_wellTyped bits q_start dim h_workspace
    · -- CX (q_start + 2 * bits) flagPos wellTyped.
      exact ⟨h_top_lt_dim, h_flag_lt_dim, h_top_ne_flag⟩
    · exact cuccaro_maj_chain_inv_wellTyped bits q_start dim h_workspace
    · exact sqir_prepareMaskedConstRead_wellTyped bits q_start (2^bits - c) controlIdx
        dim h_workspace h_control_lt_dim h_control_distinct
  · -- CX controlIdx flagPos wellTyped.
    exact ⟨h_control_lt_dim, h_flag_lt_dim, hcontrol_ne_flag⟩

/-- **Control=false bundle (4-conjunct):** read = 0, top carry = false,
flag = false, controlIdx = false. -/
theorem sqir_style_controlledModAddConst_candidate_workspace_control_false
    (bits N c x controlIdx : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    cuccaro_read_val bits 2
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx false) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx false) 1
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx false) controlIdx
        = false := by
  rw [sqir_style_controlledModAddConst_candidate_control_false_state_eq
        bits N c x controlIdx hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- read = 0.
    have h_eq : cuccaro_read_val bits 2
          (update (cuccaro_input_F 2 false 0 x) controlIdx false) = 0 % 2 ^ bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      have h_ne : (2 + 2 * i + 2 : Nat) ≠ controlIdx := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      rw [update_neq _ _ _ _ h_ne]
      rw [cuccaro_input_F_at_a 2 i false 0 x]
    rw [h_eq]; simp
  · -- top carry = false.
    have h_ne : (2 + 2 * bits : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    have h_eq : (2 : Nat) + 2 * bits = 2 + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 x]
    exact Nat.zero_testBit _
  · -- flag at 1 = false.
    rw [update_neq _ _ _ _ hcontrol_ne_flag.symm]
    unfold cuccaro_input_F
    rw [if_pos (by omega : (1 : Nat) < 2)]
  · -- controlIdx = false.
    exact update_eq _ _ _

/-! ## Tick 69 — Control preservation helpers + control=true work. -/

/-- **Deliverable A — addConstGate preserves any outside-workspace position.** -/
theorem cuccaro_addConstGate_preserves_outside_workspace_at
    (bits q_start c controlIdx : Nat) (g : Nat → Bool)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    Gate.applyNat (cuccaro_addConstGate bits q_start c) g controlIdx = g controlIdx := by
  have h_self : update g controlIdx (g controlIdx) = g := update_self g controlIdx
  conv_lhs => rw [← h_self]
  exact cuccaro_addConstGate_preserves_outside_workspace bits q_start c controlIdx
    (g controlIdx) g h_control_out

/-- **Deliverable C — conditionalAddConstGate preserves outside-workspace
position (when distinct from read positions and flag position).** -/
theorem sqir_conditionalAddConstGate_preserves_outside
    (bits q_start c flagPos controlIdx : Nat) (g : Nat → Bool)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    Gate.applyNat (sqir_conditionalAddConstGate bits q_start c flagPos) g controlIdx
      = g controlIdx := by
  show Gate.applyNat
      (seq (sqir_prepareMaskedConstRead bits q_start c flagPos)
            (seq (cuccaro_n_bit_adder_full bits q_start)
                 (sqir_prepareMaskedConstRead bits q_start c flagPos))) g controlIdx = _
  simp only [Gate.applyNat_seq]
  rw [sqir_prepareMaskedConstRead_at_other bits q_start c flagPos controlIdx
        h_control_distinct]
  rcases h_control_out with h_below | h_above
  · rw [cuccaro_n_bit_adder_full_frame_below bits q_start _ controlIdx h_below]
    exact sqir_prepareMaskedConstRead_at_other bits q_start c flagPos controlIdx
      h_control_distinct g
  · rw [cuccaro_n_bit_adder_full_frame_above bits q_start _ controlIdx h_above]
    exact sqir_prepareMaskedConstRead_at_other bits q_start c flagPos controlIdx
      h_control_distinct g

/-- **conditionalSubConstGate preserves outside-workspace position.** -/
theorem sqir_conditionalSubConstGate_preserves_outside
    (bits q_start N flagPos controlIdx : Nat) (g : Nat → Bool)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) g controlIdx
      = g controlIdx := by
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_preserves_outside bits q_start (2^bits - N)
    flagPos controlIdx g h_control_distinct h_control_out

/-- **`sqir_controlledCompareConst` preserves outside-workspace position
(when distinct from read positions and flagPos).** -/
theorem sqir_controlledCompareConst_preserves_control_outside
    (bits q_start c controlIdx flagPos : Nat) (g : Nat → Bool)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (h_control_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos) g controlIdx
      = g controlIdx := by
  show Gate.applyNat
      (seq (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)))))
      g controlIdx = _
  simp only [Gate.applyNat_seq]
  rw [sqir_prepareMaskedConstRead_at_other bits q_start (2^bits - c) controlIdx
        controlIdx h_control_distinct]
  rcases h_control_out with h_below | h_above
  · rw [cuccaro_maj_chain_inv_frame_below bits q_start _ controlIdx h_below]
    rw [Gate.applyNat_CX, update_neq _ _ _ _ h_control_ne_flag]
    rw [cuccaro_maj_chain_frame_below bits q_start _ controlIdx h_below]
    exact sqir_prepareMaskedConstRead_at_other bits q_start (2^bits - c) controlIdx
      controlIdx h_control_distinct g
  · rw [cuccaro_maj_chain_inv_frame_above bits q_start _ controlIdx h_above]
    rw [Gate.applyNat_CX, update_neq _ _ _ _ h_control_ne_flag]
    rw [cuccaro_maj_chain_frame_above bits q_start _ controlIdx h_above]
    exact sqir_prepareMaskedConstRead_at_other bits q_start (2^bits - c) controlIdx
      controlIdx h_control_distinct g

/-- **Partial Deliverable D — control bit is preserved through the controlled
mod-N add candidate.** -/
theorem sqir_style_controlledModAddConst_candidate_preserves_control
    (bits N c x controlIdx : Nat) (control : Bool)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
        (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx
      = control := by
  have h_control_distinct : ∀ i, i < bits → controlIdx ≠ 2 + 2 * i + 2 := by
    intros i _ heq
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  show Gate.applyNat
      (seq (sqir_conditionalAddConstGate bits 2 c controlIdx)
            (seq (sqir_style_compareConst_candidate bits 2 N 1)
                 (seq (sqir_conditionalSubConstGate bits 2 N 1)
                      (seq (sqir_controlledCompareConst bits 2 c controlIdx 1)
                           (Gate.CX controlIdx 1)))))
      _ controlIdx = _
  simp only [Gate.applyNat_seq]
  -- Stage 5 (CX controlIdx 1): controlIdx ≠ 1 → CX doesn't modify controlIdx.
  rw [Gate.applyNat_CX, update_neq _ _ _ _ hcontrol_ne_flag]
  -- Stage 4 (ctrlCompare): preserves controlIdx.
  rw [sqir_controlledCompareConst_preserves_control_outside bits 2 c controlIdx 1
        _ h_control_distinct hcontrol_out hcontrol_ne_flag]
  -- Stage 3 (condSub): preserves controlIdx.
  rw [sqir_conditionalSubConstGate_preserves_outside bits 2 N 1 controlIdx
        _ h_control_distinct hcontrol_out]
  -- Stage 2 (compareConst N): preserves controlIdx via frame_outside.
  rw [sqir_style_compareConst_candidate_frame_outside bits 2 N 1 _ controlIdx
        hcontrol_ne_flag hcontrol_out]
  -- Stage 1 (condAdd c controlIdx): the controlled add preserves its own flagPos = controlIdx.
  exact sqir_conditionalAddConstGate_flag_preserved bits 2 c x controlIdx control
    h_control_distinct hcontrol_out

/-! ## Tick 70 — X/CX commute helpers for locality (Deliverable A precursors).

The full clean_candidate locality requires per-stage commute lemmas
(addConst, compareConst, condSub, compareConst, X).  This tick lands
the easy two (X, CX); the compareConst and conditionalAdd commutes
plus the full clean_candidate locality + state_eq for control=true
are deferred to Tick 71. -/

/-- **X commute with update at outside position.** -/
theorem Gate.applyNat_X_commute_update_outside_fun
    (target controlIdx : Nat) (v : Bool) (f : Nat → Bool) (h : controlIdx ≠ target) :
    Gate.applyNat (Gate.X target) (update f controlIdx v)
      = update (Gate.applyNat (Gate.X target) f) controlIdx v := by
  simp only [Gate.applyNat_X]
  rw [update_neq _ _ _ _ (fun heq => h heq.symm)]
  exact (update_comm f target controlIdx (! f target) v (fun heq => h heq.symm)).symm

/-- **CX commute with update at outside position (≠ control and ≠ target).** -/
theorem Gate.applyNat_CX_commute_update_outside_fun
    (control target controlIdx : Nat) (v : Bool) (f : Nat → Bool)
    (h_ne_control : controlIdx ≠ control) (h_ne_target : controlIdx ≠ target) :
    Gate.applyNat (Gate.CX control target) (update f controlIdx v)
      = update (Gate.applyNat (Gate.CX control target) f) controlIdx v := by
  simp only [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ (fun heq => h_ne_target heq.symm)]
  rw [update_neq _ _ _ _ (fun heq => h_ne_control heq.symm)]
  exact (update_comm f target controlIdx _ v (fun heq => h_ne_target heq.symm)).symm

/-! ## Tick 71 — Locality stack for controlled mod-N add. -/

/-- **Deliverable A — masked prepare commutes with `update` at outside position.** -/
theorem sqir_prepareMaskedConstRead_commute_update_outside_workspace
    (bits q_start N flagPos controlIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) (update f controlIdx v)
      = update (Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f)
              controlIdx v := by
  induction bits generalizing f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat
        (seq (sqir_prepareMaskedConstRead k q_start N flagPos)
              (cond (N.testBit k) (Gate.CX flagPos (q_start + 2 * k + 2)) Gate.I))
        (update f controlIdx v)
      = update (Gate.applyNat
                  (seq (sqir_prepareMaskedConstRead k q_start N flagPos)
                        (cond (N.testBit k) (Gate.CX flagPos (q_start + 2 * k + 2)) Gate.I))
                  f) controlIdx v
    simp only [Gate.applyNat_seq]
    have h_ctrl_out_k : controlIdx < q_start ∨ q_start + 2 * k + 1 ≤ controlIdx := by
      rcases hcontrol_out with hl | hr
      · left; exact hl
      · right; omega
    rw [ih f h_ctrl_out_k]
    cases h_c : N.testBit k with
    | false =>
      simp only [cond_false, Gate.applyNat_I]
    | true =>
      simp only [cond_true]
      have h_ctrl_ne_read : controlIdx ≠ q_start + 2 * k + 2 := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      exact Gate.applyNat_CX_commute_update_outside_fun flagPos (q_start + 2 * k + 2)
        controlIdx v _ hcontrol_ne_flag h_ctrl_ne_read

/-- **Function-level commute for `cuccaro_maj_chain_inv`.**  Lifts the
existing position-level theorem to a function equality. -/
theorem cuccaro_maj_chain_inv_commute_update_outside_workspace_fun
    (bits q_start flagPos : Nat) (v : Bool) (f : Nat → Bool)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (cuccaro_maj_chain_inv bits q_start) (update f flagPos v)
      = update (Gate.applyNat (cuccaro_maj_chain_inv bits q_start) f) flagPos v := by
  funext p
  by_cases hp_in_workspace : q_start ≤ p ∧ p < q_start + 2 * bits + 1
  · have h := cuccaro_maj_chain_inv_commute_update_outside_workspace bits q_start flagPos v f
      hflag_out p hp_in_workspace.1 hp_in_workspace.2
    rw [h]
    have hp_ne_flag : p ≠ flagPos := by
      rcases hflag_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ hp_ne_flag]
  · push_neg at hp_in_workspace
    have hp_outside : p < q_start ∨ q_start + 2 * bits + 1 ≤ p := by
      by_cases h : p < q_start
      · left; exact h
      · push_neg at h; right; exact hp_in_workspace h
    rcases hp_outside with hp_below | hp_above
    · rw [cuccaro_maj_chain_inv_frame_below bits q_start (update f flagPos v) p hp_below]
      by_cases hp_flag : p = flagPos
      · rw [hp_flag, update_eq, update_eq]
      · rw [update_neq _ _ _ _ hp_flag, update_neq _ _ _ _ hp_flag]
        exact (cuccaro_maj_chain_inv_frame_below bits q_start f p hp_below).symm
    · rw [cuccaro_maj_chain_inv_frame_above bits q_start (update f flagPos v) p hp_above]
      by_cases hp_flag : p = flagPos
      · rw [hp_flag, update_eq, update_eq]
      · rw [update_neq _ _ _ _ hp_flag, update_neq _ _ _ _ hp_flag]
        exact (cuccaro_maj_chain_inv_frame_above bits q_start f p hp_above).symm

/-- **Deliverable B — comparator commutes with `update` at outside position.** -/
theorem sqir_style_compareConst_candidate_commute_update_outside_fun
    (bits q_start N flagPos controlIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (update f controlIdx v)
      = update (Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos) f)
              controlIdx v := by
  unfold sqir_style_compareConst_candidate
  simp only [Gate.applyNat_seq]
  have h_ctrl_ne_top : controlIdx ≠ q_start + 2 * bits := by
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  rw [cuccaro_prepareConstRead_commute_update_outside_workspace bits q_start (2^bits - N)
        controlIdx v f hcontrol_out]
  rw [cuccaro_maj_chain_commute_update_outside_workspace bits q_start controlIdx v _ hcontrol_out]
  rw [Gate.applyNat_CX_commute_update_outside_fun (q_start + 2 * bits) flagPos controlIdx v _
        h_ctrl_ne_top hcontrol_ne_flag]
  rw [cuccaro_maj_chain_inv_commute_update_outside_workspace_fun bits q_start controlIdx v _
        hcontrol_out]
  rw [cuccaro_prepareConstRead_commute_update_outside_workspace bits q_start (2^bits - N)
        controlIdx v _ hcontrol_out]

/-- **Deliverable C — conditionalAdd commutes with `update` at outside position.** -/
theorem sqir_conditionalAddConstGate_commute_update_outside_fun
    (bits q_start N flagPos controlIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos) (update f controlIdx v)
      = update (Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos) f)
              controlIdx v := by
  unfold sqir_conditionalAddConstGate
  simp only [Gate.applyNat_seq]
  rw [sqir_prepareMaskedConstRead_commute_update_outside_workspace bits q_start N flagPos
        controlIdx v f hcontrol_out hcontrol_ne_flag]
  rw [cuccaro_n_bit_adder_full_commute_update_outside_workspace bits q_start controlIdx v _
        hcontrol_out]
  rw [sqir_prepareMaskedConstRead_commute_update_outside_workspace bits q_start N flagPos
        controlIdx v _ hcontrol_out hcontrol_ne_flag]

/-- **Deliverable C — conditionalSub commutes with `update` at outside position.** -/
theorem sqir_conditionalSubConstGate_commute_update_outside_fun
    (bits q_start N flagPos controlIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) (update f controlIdx v)
      = update (Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f)
              controlIdx v := by
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_commute_update_outside_fun bits q_start (2^bits - N)
    flagPos controlIdx v f hcontrol_out hcontrol_ne_flag

/-- **R7d^xxix-L-3.10′ helper: q_start-parametric clean modadd
candidate commutes with `update` at controlIdx outside workspace ∪
{flagPos}.**

q_start-parametric port of
`sqir_style_modAddConst_clean_candidate_commute_update_control_outside`.
All sub-deps already q_start-parametric:
- `cuccaro_addConstGate_commute_update_outside_workspace` (CuccaroSQIRCondAdd.lean:685);
- `sqir_style_compareConst_candidate_commute_update_outside_fun` (CuccaroSQIRDirtyFlag.lean:3132);
- `sqir_conditionalSubConstGate_commute_update_outside_fun` (:3174);
- `Gate.applyNat_X_commute_update_outside_fun` (:3039, generic). -/
theorem sqir_style_modAddConst_clean_candidate_commute_update_control_outside_qstart
    (bits q_start N c controlIdx flagPos : Nat) (v : Bool) (f : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_style_modAddConst_clean_candidate bits q_start N c flagPos)
        (update f controlIdx v)
      = update (Gate.applyNat (sqir_style_modAddConst_clean_candidate bits q_start N c flagPos) f)
              controlIdx v := by
  unfold sqir_style_modAddConst_clean_candidate sqir_style_modAddConst_dirtyFlag_candidate
  simp only [Gate.applyNat_seq]
  rw [cuccaro_addConstGate_commute_update_outside_workspace bits q_start c controlIdx v f
        hcontrol_out]
  rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits q_start N flagPos
        controlIdx v _ hcontrol_out hcontrol_ne_flag]
  rw [sqir_conditionalSubConstGate_commute_update_outside_fun bits q_start N flagPos
        controlIdx v _ hcontrol_out hcontrol_ne_flag]
  rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits q_start c flagPos
        controlIdx v _ hcontrol_out hcontrol_ne_flag]
  rw [Gate.applyNat_X_commute_update_outside_fun flagPos controlIdx v _ hcontrol_ne_flag]

/-- **R7d^xxix-L-3.10′ HEADLINE: q_start-parametric control=true
state equality for the controlled mod-N add candidate.**

q_start-parametric port of
`sqir_style_controlledModAddConst_candidate_control_true_state_eq`.
The 5-stage rewrite chain is mirrored with `2 → q_start`, `1 →
flagPos`, free `controlIdx`, with the standard outside-workspace
hypotheses on both `controlIdx` and `flagPos`, plus distinctness.

The state-equality lifts the controlled candidate's action (under
external control = true) to the uncontrolled clean candidate
applied to `cuccaro_input_F q_start false 0 x`, with the
`controlIdx` slot pinned to `true` on both sides.

Dependencies (all already q_start-parametric or just landed):
- `sqir_style_modAddConst_clean_candidate_commute_update_control_outside_qstart`
  (above, this tick);
- `sqir_conditionalAddConstGate_apply_true_fun` (CuccaroSQIRCondAdd.lean:379);
- `sqir_conditionalSubConstGate_preserves_outside` (:2951);
- `sqir_style_compareConst_candidate_frame_outside` (:175);
- `cuccaro_addConstGate_preserves_outside_workspace_at` (:2918);
- `sqir_controlledCompareConst_at_control_true_eq_unmasked_fun` (:2091);
- `Gate.applyNat_CX_at_control_true_eq_X_fun` (generic CX). -/
theorem sqir_style_controlledModAddConst_candidate_control_true_state_eq_qstart
    (bits q_start N c x controlIdx flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
        (update (cuccaro_input_F q_start false 0 x) controlIdx true)
      = update (Gate.applyNat
                  (sqir_style_modAddConst_clean_candidate bits q_start N c flagPos)
                  (update (cuccaro_input_F q_start false 0 x) flagPos false))
              controlIdx true := by
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have h_F_at_flag : cuccaro_input_F q_start false 0 x flagPos = false :=
    cuccaro_input_F_at_outside_eq_false q_start bits x flagPos hflag_out h_x_lt
  have h_F_flag_eq : update (cuccaro_input_F q_start false 0 x) flagPos false
                  = cuccaro_input_F q_start false 0 x := by
    funext q
    by_cases hq : q = flagPos
    · rw [hq, update_eq]; exact h_F_at_flag.symm
    · rw [update_neq _ _ _ _ hq]
  rw [h_F_flag_eq]
  rw [← sqir_style_modAddConst_clean_candidate_commute_update_control_outside_qstart bits q_start
        N c controlIdx flagPos true (cuccaro_input_F q_start false 0 x) hcontrol_out
        hcontrol_ne_flag]
  unfold sqir_style_controlledModAddConst_candidate sqir_style_modAddConst_clean_candidate
    sqir_style_modAddConst_dirtyFlag_candidate
  simp only [Gate.applyNat_seq]
  have h_input_ctrl :
      (update (cuccaro_input_F q_start false 0 x) controlIdx true) controlIdx = true :=
    update_eq _ _ _
  have h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2 := by
    intros i _ heq
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  rw [sqir_conditionalAddConstGate_apply_true_fun bits q_start c controlIdx
        (update (cuccaro_input_F q_start false 0 x) controlIdx true) h_control_distinct
        h_input_ctrl hcontrol_out]
  have h_state3_ctrl :
      Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos)
        (Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
          (Gate.applyNat (cuccaro_addConstGate bits q_start c)
            (update (cuccaro_input_F q_start false 0 x) controlIdx true))) controlIdx = true := by
    rw [sqir_conditionalSubConstGate_preserves_outside bits q_start N flagPos controlIdx _
          h_control_distinct hcontrol_out]
    rw [sqir_style_compareConst_candidate_frame_outside bits q_start N flagPos _ controlIdx
          hcontrol_ne_flag hcontrol_out]
    rw [cuccaro_addConstGate_preserves_outside_workspace_at bits q_start c controlIdx _
          hcontrol_out]
    exact h_input_ctrl
  rw [sqir_controlledCompareConst_at_control_true_eq_unmasked_fun bits q_start c controlIdx
        flagPos _ h_control_distinct hcontrol_out hcontrol_ne_flag h_state3_ctrl]
  have h_state4_ctrl :
      Gate.applyNat (sqir_style_compareConst_candidate bits q_start c flagPos)
        (Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos)
          (Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
            (Gate.applyNat (cuccaro_addConstGate bits q_start c)
              (update (cuccaro_input_F q_start false 0 x) controlIdx true)))) controlIdx = true := by
    rw [sqir_style_compareConst_candidate_frame_outside bits q_start c flagPos _ controlIdx
          hcontrol_ne_flag hcontrol_out]
    exact h_state3_ctrl
  rw [Gate.applyNat_CX_at_control_true_eq_X_fun controlIdx flagPos _ h_state4_ctrl]

/-- **HEADLINE Deliverable D — clean modadd candidate commutes with `update` at
controlIdx outside workspace ∪ {flagPos = 1}.** -/
theorem sqir_style_modAddConst_clean_candidate_commute_update_control_outside
    (bits N c controlIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.applyNat (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
        (update f controlIdx v)
      = update (Gate.applyNat (sqir_style_modAddConst_clean_candidate bits 2 N c 1) f)
              controlIdx v := by
  unfold sqir_style_modAddConst_clean_candidate sqir_style_modAddConst_dirtyFlag_candidate
  simp only [Gate.applyNat_seq]
  rw [cuccaro_addConstGate_commute_update_outside_workspace bits 2 c controlIdx v f hcontrol_out]
  rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits 2 N 1 controlIdx v _
        hcontrol_out hcontrol_ne_flag]
  rw [sqir_conditionalSubConstGate_commute_update_outside_fun bits 2 N 1 controlIdx v _
        hcontrol_out hcontrol_ne_flag]
  rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits 2 c 1 controlIdx v _
        hcontrol_out hcontrol_ne_flag]
  rw [Gate.applyNat_X_commute_update_outside_fun 1 controlIdx v _ hcontrol_ne_flag]

/-! ## Tick 72 — Control=true branch + combined theorems. -/

/-- **Helper — `cuccaro_target_val` is invariant under `update` at outside controlIdx.** -/
theorem cuccaro_target_val_update_outside_workspace
    (bits q_start controlIdx : Nat) (v : Bool) (Y : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    cuccaro_target_val bits q_start (update Y controlIdx v)
      = cuccaro_target_val bits q_start Y := by
  induction bits with
  | zero => rfl
  | succ k ih =>
    unfold cuccaro_target_val
    have h_ne : (q_start + 2 * k + 1 : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    have h_ih : controlIdx < q_start ∨ q_start + 2 * k + 1 ≤ controlIdx := by
      rcases hcontrol_out with hl | hr
      · left; exact hl
      · right; omega
    rw [ih h_ih]

/-- **Helper — `cuccaro_read_val` is invariant under `update` at outside controlIdx.** -/
theorem cuccaro_read_val_update_outside_workspace
    (bits q_start controlIdx : Nat) (v : Bool) (Y : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    cuccaro_read_val bits q_start (update Y controlIdx v)
      = cuccaro_read_val bits q_start Y := by
  induction bits with
  | zero => rfl
  | succ k ih =>
    unfold cuccaro_read_val
    have h_ne : (q_start + 2 * k + 2 : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    have h_ih : controlIdx < q_start ∨ q_start + 2 * k + 1 ≤ controlIdx := by
      rcases hcontrol_out with hl | hr
      · left; exact hl
      · right; omega
    rw [ih h_ih]

/-- **HEADLINE Deliverable A — control=true state equality for the controlled
mod-N add candidate.** -/
theorem sqir_style_controlledModAddConst_candidate_control_true_state_eq
    (bits N c x controlIdx : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
        (update (cuccaro_input_F 2 false 0 x) controlIdx true)
      = update (Gate.applyNat (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
                  (update (cuccaro_input_F 2 false 0 x) 1 false)) controlIdx true := by
  have h_F_at_1 : cuccaro_input_F 2 false 0 x 1 = false := by
    unfold cuccaro_input_F; rw [if_pos (by omega : (1 : Nat) < 2)]
  have h_F_1_eq : update (cuccaro_input_F 2 false 0 x) 1 false
                = cuccaro_input_F 2 false 0 x := by
    funext q
    by_cases hq : q = 1
    · rw [hq, update_eq]; exact h_F_at_1.symm
    · rw [update_neq _ _ _ _ hq]
  rw [h_F_1_eq]
  rw [← sqir_style_modAddConst_clean_candidate_commute_update_control_outside bits N c
        controlIdx true (cuccaro_input_F 2 false 0 x) hcontrol_out hcontrol_ne_flag]
  unfold sqir_style_controlledModAddConst_candidate sqir_style_modAddConst_clean_candidate
    sqir_style_modAddConst_dirtyFlag_candidate
  simp only [Gate.applyNat_seq]
  have h_input_ctrl : (update (cuccaro_input_F 2 false 0 x) controlIdx true) controlIdx = true :=
    update_eq _ _ _
  have h_control_distinct : ∀ i, i < bits → controlIdx ≠ 2 + 2 * i + 2 := by
    intros i _ heq
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  rw [sqir_conditionalAddConstGate_apply_true_fun bits 2 c controlIdx
        (update (cuccaro_input_F 2 false 0 x) controlIdx true) h_control_distinct
        h_input_ctrl hcontrol_out]
  have h_state3_ctrl :
      Gate.applyNat (sqir_conditionalSubConstGate bits 2 N 1)
        (Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
          (Gate.applyNat (cuccaro_addConstGate bits 2 c)
            (update (cuccaro_input_F 2 false 0 x) controlIdx true))) controlIdx = true := by
    rw [sqir_conditionalSubConstGate_preserves_outside bits 2 N 1 controlIdx _
          h_control_distinct hcontrol_out]
    rw [sqir_style_compareConst_candidate_frame_outside bits 2 N 1 _ controlIdx
          hcontrol_ne_flag hcontrol_out]
    rw [cuccaro_addConstGate_preserves_outside_workspace_at bits 2 c controlIdx _ hcontrol_out]
    exact h_input_ctrl
  rw [sqir_controlledCompareConst_at_control_true_eq_unmasked_fun bits 2 c controlIdx 1 _
        h_control_distinct hcontrol_out hcontrol_ne_flag h_state3_ctrl]
  have h_state4_ctrl :
      Gate.applyNat (sqir_style_compareConst_candidate bits 2 c 1)
        (Gate.applyNat (sqir_conditionalSubConstGate bits 2 N 1)
          (Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
            (Gate.applyNat (cuccaro_addConstGate bits 2 c)
              (update (cuccaro_input_F 2 false 0 x) controlIdx true)))) controlIdx = true := by
    rw [sqir_style_compareConst_candidate_frame_outside bits 2 c 1 _ controlIdx
          hcontrol_ne_flag hcontrol_out]
    exact h_state3_ctrl
  rw [Gate.applyNat_CX_at_control_true_eq_X_fun controlIdx 1 _ h_state4_ctrl]

/-- **R7d^xxix-L-3.11′ DELIVERABLE: q_start-parametric control=true
target decode.**

q_start-parametric port of
`sqir_style_controlledModAddConst_candidate_target_decode_control_true`.
Three-step thin consequence of the L-3.10′ state equality:
1. rewrite via `_control_true_state_eq_qstart` to expose the
   uncontrolled clean candidate applied to `cuccaro_input_F q_start`
   with the `controlIdx` slot wrapped in `update _ controlIdx true`;
2. strip the outer `update controlIdx true` via
   `cuccaro_target_val_update_outside_workspace` (controlIdx lies
   outside the workspace by hypothesis);
3. close with `_modAddConst_clean_candidate_target_decode_qstart`
   (L-3.9′). -/
theorem sqir_style_controlledModAddConst_candidate_target_decode_control_true_qstart
    (bits q_start N c x controlIdx flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx true))
      = (x + c) % N := by
  rw [sqir_style_controlledModAddConst_candidate_control_true_state_eq_qstart
        bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag]
  rw [cuccaro_target_val_update_outside_workspace bits q_start controlIdx true _ hcontrol_out]
  exact sqir_style_modAddConst_clean_candidate_target_decode_qstart
    bits q_start N c x flagPos hbits hN_pos hN hN2 hc_pos hc hx hflag_out

/-- **Deliverable B — control=true target decode.** -/
theorem sqir_style_controlledModAddConst_candidate_target_decode_control_true
    (bits N c x controlIdx : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx true))
      = (x + c) % N := by
  rw [sqir_style_controlledModAddConst_candidate_control_true_state_eq bits N c x controlIdx
        hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag]
  rw [cuccaro_target_val_update_outside_workspace bits 2 controlIdx true _ hcontrol_out]
  exact sqir_style_modAddConst_clean_candidate_target_decode bits N c x hbits hN_pos hN hN2
    hc_pos hc hx

/-- **R7d^xxix-L-3.12′ helper: q_start-parametric clean-candidate
flag restoration.**  At `flagPos`, the uncontrolled clean candidate
restores the flag to `false`.  Direct q_start port of
`sqir_style_modAddConst_clean_candidate_flag_restored` (line 1462). -/
theorem sqir_style_modAddConst_clean_candidate_flag_restored_qstart
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat
        (sqir_style_modAddConst_clean_candidate bits q_start N c flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos
      = false := by
  show Gate.applyNat
      (seq (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
            (seq (sqir_style_compareConst_candidate bits q_start c flagPos)
                 (Gate.X flagPos)))
      _ _ = _
  simp only [Gate.applyNat_seq]
  have h_flag_distinct : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2 := by
    intros j _ heq
    rcases hflag_out with hl | hr
    · omega
    · omega
  rw [sqir_style_modAddConst_dirtyFlag_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  have h_xc_mod_N_lt : (x + c) % N < 2 ^ bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  rw [Gate.applyNat_X]
  rw [update_eq]
  rw [sqir_style_compareConst_candidate_flag_xor bits q_start c ((x + c) % N) flagPos
        (decide (N ≤ x + c)) hc_pos (by omega : c ≤ 2 ^ bits) h_xc_mod_N_lt hflag_out]
  rw [decide_c_le_xc_mod_N_eq_not_decide_N_le_xc N x c hN_pos hc_pos hx hc]
  cases decide (N ≤ x + c) <;> rfl

/-- **R7d^xxix-L-3.12′ DELIVERABLE: q_start-parametric control=true
workspace bundle.**

4-conjunct workspace bundle when the external control bit is
`true`.  After applying the controlled mod-N add candidate to
`(update (cuccaro_input_F q_start false 0 x) controlIdx true)`:

1. `cuccaro_read_val` (read register) = 0;
2. position `q_start + 2 * bits` (top carry) = false;
3. position `flagPos` = false;
4. position `controlIdx` = true (preserved external control).

Proof strategy mirrors the hard-coded version (line 3481+) but uses
the L-3.10′ state-eq + inline read/top-carry computation +
`_flag_restored_qstart` (helper above). -/
theorem sqir_style_controlledModAddConst_candidate_workspace_control_true_qstart
    (bits q_start N c x controlIdx flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx true))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx true) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx true) flagPos
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx true) controlIdx
        = true := by
  rw [sqir_style_controlledModAddConst_candidate_control_true_state_eq_qstart
        bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag]
  have h_flag_distinct : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2 := by
    intros j _ heq
    rcases hflag_out with hl | hr
    · omega
    · omega
  have h_xc_mod_N_lt : (x + c) % N < 2 ^ bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- read = 0.
    rw [cuccaro_read_val_update_outside_workspace bits q_start controlIdx true _ hcontrol_out]
    show cuccaro_read_val bits q_start
        (Gate.applyNat
          (seq (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
                (seq (sqir_style_compareConst_candidate bits q_start c flagPos)
                     (Gate.X flagPos))) _) = 0
    simp only [Gate.applyNat_seq]
    rw [sqir_style_modAddConst_dirtyFlag_state_eq bits q_start N c x flagPos
          hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
    have h_eq : cuccaro_read_val bits q_start
        (Gate.applyNat (Gate.X flagPos)
          (Gate.applyNat (sqir_style_compareConst_candidate bits q_start c flagPos)
            (update (cuccaro_input_F q_start false 0 ((x + c) % N)) flagPos
              (decide (N ≤ x + c)))))
      = 0 % 2 ^ bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      have h_pos_ne_flag : (q_start + 2 * i + 2 : Nat) ≠ flagPos := by
        rcases hflag_out with hl | hr
        · omega
        · omega
      rw [Gate.applyNat_X]
      rw [update_neq _ _ _ _ h_pos_ne_flag]
      rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits q_start c flagPos _
            hflag_out (q_start + 2 * i + 2) (by omega) (by omega)]
      rw [update_neq _ _ _ _ h_pos_ne_flag]
      rw [cuccaro_input_F_at_a q_start i false 0 ((x + c) % N)]
    rw [h_eq]; simp
  · -- top carry at q_start + 2 * bits = false.
    have h_top_ne_ctrl : (q_start + 2 * bits : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_top_ne_ctrl]
    show Gate.applyNat
        (seq (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
              (seq (sqir_style_compareConst_candidate bits q_start c flagPos)
                   (Gate.X flagPos))) _ _ = _
    simp only [Gate.applyNat_seq]
    rw [sqir_style_modAddConst_dirtyFlag_state_eq bits q_start N c x flagPos
          hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
    have h_top_ne_flag : (q_start + 2 * bits : Nat) ≠ flagPos := by
      rcases hflag_out with hl | hr
      · omega
      · omega
    rw [Gate.applyNat_X]
    rw [update_neq _ _ _ _ h_top_ne_flag]
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits q_start c flagPos _
          hflag_out (q_start + 2 * bits) (by omega) (by omega)]
    rw [update_neq _ _ _ _ h_top_ne_flag]
    have h_eq : q_start + 2 * bits = q_start + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a q_start (bits - 1) false 0 ((x + c) % N)]
    simp [Nat.zero_testBit]
  · -- flag = false.
    rw [update_neq _ _ _ _ hcontrol_ne_flag.symm]
    exact sqir_style_modAddConst_clean_candidate_flag_restored_qstart bits q_start N c x flagPos
      hbits hN_pos hN hN2 hc_pos hc hx hflag_out
  · -- controlIdx = true.
    exact update_eq _ _ _

/-- **Deliverable C — control=true workspace bundle (4-conjunct).** -/
theorem sqir_style_controlledModAddConst_candidate_workspace_control_true
    (bits N c x controlIdx : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx true))
        = 0
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx true) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx true) 1
        = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx true) controlIdx
        = true := by
  rw [sqir_style_controlledModAddConst_candidate_control_true_state_eq bits N c x controlIdx
        hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag]
  obtain ⟨_, _, h_rd, h_tc, h_fl⟩ :=
    sqir_style_modAddConst_clean_candidate_clean bits N c x hbits hN_pos hN hN2 hc_pos hc hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cuccaro_read_val_update_outside_workspace bits 2 controlIdx true _ hcontrol_out]
    exact h_rd
  · have h_ne : (2 + 2 * bits : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    exact h_tc
  · rw [update_neq _ _ _ _ hcontrol_ne_flag.symm]
    exact h_fl
  · exact update_eq _ _ _

/-! ## Tick 72 — Combined theorems (case-split on control). -/

/-- **HEADLINE Deliverable D — combined controlled target decode.** -/
theorem sqir_style_controlledModAddConst_candidate_target_decode
    (bits N c x controlIdx : Nat) (control : Bool) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control))
      = if control then (x + c) % N else x := by
  cases control
  · simp only [Bool.false_eq_true, if_false]
    exact sqir_style_controlledModAddConst_candidate_target_decode_control_false bits N c x
      controlIdx hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag
  · simp only [if_true]
    exact sqir_style_controlledModAddConst_candidate_target_decode_control_true bits N c x
      controlIdx hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag

/-- **Deliverable E — combined workspace bundle.** -/
theorem sqir_style_controlledModAddConst_candidate_workspace
    (bits N c x controlIdx : Nat) (control : Bool) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = 0
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) 1
        = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx
        = control := by
  cases control
  · exact sqir_style_controlledModAddConst_candidate_workspace_control_false bits N c x
      controlIdx hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag
  · exact sqir_style_controlledModAddConst_candidate_workspace_control_true bits N c x
      controlIdx hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag

/-! ## Tick 72 — Candidate clean bundle and total wrapper. -/

/-- **R7d^xxix-L-3.13′ DELIVERABLE: q_start-parametric controlled
candidate clean bundle (combined over both control branches).**

6-conjunct bundle parametric in `q_start`, `flagPos`, `controlIdx`,
`dim`, and `control : Bool`:

1. `Gate.WellTyped dim` of the candidate gate;
2. target decode = `if control then (x + c) % N else x`;
3. read register = 0;
4. position `q_start + 2 * bits` (top carry) = false;
5. position `flagPos` = false;
6. position `controlIdx` = `control` (preserved external control).

Mechanical case-split on `control`: false branch fully delegated to
`_clean_control_false_qstart` (L-3.8′); true branch reuses
`_clean_control_false_qstart` only to extract the
control-independent `Gate.WellTyped`, then assembles the remaining
five conjuncts from `_target_decode_control_true_qstart` (L-3.11′)
and `_workspace_control_true_qstart` (L-3.12′).  No new
arithmetic. -/
theorem sqir_style_controlledModAddConst_candidate_clean_qstart
    (bits q_start N c x dim controlIdx flagPos : Nat) (control : Bool)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_control_lt_dim : controlIdx < dim)
    (h_flag_lt_dim : flagPos < dim) :
    Gate.WellTyped dim
        (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx control))
        = (if control then (x + c) % N else x)
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx control)) = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) flagPos
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) controlIdx
        = control := by
  cases control with
  | false =>
    obtain ⟨h_wt, h_tgt, h_rd, h_tc, h_fl, h_ctrl⟩ :=
      sqir_style_controlledModAddConst_candidate_clean_control_false_qstart
        bits q_start N c x dim controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag h_workspace h_control_lt_dim h_flag_lt_dim
    refine ⟨h_wt, ?_, h_rd, h_tc, h_fl, h_ctrl⟩
    show _ = x
    exact h_tgt
  | true =>
    obtain ⟨h_wt, _, _, _, _, _⟩ :=
      sqir_style_controlledModAddConst_candidate_clean_control_false_qstart
        bits q_start N c x dim controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag h_workspace h_control_lt_dim h_flag_lt_dim
    have h_tgt :=
      sqir_style_controlledModAddConst_candidate_target_decode_control_true_qstart
        bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag
    obtain ⟨h_rd, h_tc, h_fl, h_ctrl⟩ :=
      sqir_style_controlledModAddConst_candidate_workspace_control_true_qstart
        bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag
    refine ⟨h_wt, ?_, h_rd, h_tc, h_fl, h_ctrl⟩
    show _ = (x + c) % N
    exact h_tgt

/-- **Deliverable F — controlled candidate clean bundle for c > 0.** -/
theorem sqir_style_controlledModAddConst_candidate_clean
    (bits N c x controlIdx : Nat) (control : Bool) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1)
    (h_control_workspace_lt : controlIdx < sqir_modmult_rev_anc bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = (if control then (x + c) % N else x)
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control)) = 0
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) (2 + 2 * bits) = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) 1 = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx = control := by
  obtain ⟨h_rd, h_tc, h_fl, h_ctrl⟩ :=
    sqir_style_controlledModAddConst_candidate_workspace bits N c x controlIdx control hbits
      hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag
  refine ⟨?_, ?_, h_rd, h_tc, h_fl, h_ctrl⟩
  · -- WellTyped.
    show Gate.WellTyped (sqir_modmult_rev_anc bits)
        (seq (sqir_conditionalAddConstGate bits 2 c controlIdx)
              (seq (sqir_style_compareConst_candidate bits 2 N 1)
                   (seq (sqir_conditionalSubConstGate bits 2 N 1)
                        (seq (sqir_controlledCompareConst bits 2 c controlIdx 1)
                             (Gate.CX controlIdx 1)))))
    have h_control_distinct : ∀ i, i < bits → controlIdx ≠ 2 + 2 * i + 2 := by
      intros i _ heq
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    have h_flag_distinct : ∀ i, i < bits → (1 : Nat) ≠ 2 + 2 * i + 2 := fun i _ => by omega
    have h_workspace : (2 + 2 * bits + 1 : Nat) ≤ sqir_modmult_rev_anc bits := by
      unfold sqir_modmult_rev_anc; omega
    have h_flag_lt : (1 : Nat) < sqir_modmult_rev_anc bits := by
      unfold sqir_modmult_rev_anc; omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact sqir_conditionalAddConstGate_wellTyped bits 2 c controlIdx (sqir_modmult_rev_anc bits)
        h_workspace h_control_workspace_lt h_control_distinct
    · apply sqir_style_compareConst_candidate_wellTyped bits 2 N 1 (sqir_modmult_rev_anc bits)
        h_workspace h_flag_lt
      omega
    · exact sqir_conditionalSubConstGate_wellTyped bits 2 N 1 (sqir_modmult_rev_anc bits)
        h_workspace h_flag_lt h_flag_distinct
    · -- WellTyped for sqir_controlledCompareConst: same structure as compareConst.
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- prepare(c, controlIdx) wellTyped.
        exact sqir_prepareMaskedConstRead_wellTyped bits 2 (2^bits - c) controlIdx
          (sqir_modmult_rev_anc bits) h_workspace h_control_workspace_lt h_control_distinct
      · -- maj_chain wellTyped.
        exact cuccaro_maj_chain_wellTyped bits 2 (sqir_modmult_rev_anc bits) h_workspace
      · -- CX (q_start + 2 * bits) 1 wellTyped.
        refine ⟨?_, ?_, ?_⟩
        · unfold sqir_modmult_rev_anc; omega
        · exact h_flag_lt
        · omega
      · -- maj_chain_inv wellTyped.
        exact cuccaro_maj_chain_inv_wellTyped bits 2 (sqir_modmult_rev_anc bits) h_workspace
      · -- prepare wellTyped.
        exact sqir_prepareMaskedConstRead_wellTyped bits 2 (2^bits - c) controlIdx
          (sqir_modmult_rev_anc bits) h_workspace h_control_workspace_lt h_control_distinct
    · -- CX controlIdx 1 wellTyped.
      refine ⟨?_, ?_, ?_⟩
      · exact h_control_workspace_lt
      · exact h_flag_lt
      · exact hcontrol_ne_flag
  · exact sqir_style_controlledModAddConst_candidate_target_decode bits N c x controlIdx control
      hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag

/-- **R7d^xxix-L-3.14′ helper: q_start-parametric `c = 0` reduction.**
The total wrapper at `c = 0` is the identity gate, regardless of
`q_start`/`flagPos`/`controlIdx`. -/
theorem sqir_style_controlledModAddConst_gate_zero_eq_qstart
    (bits q_start N controlIdx flagPos : Nat) :
    sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos = Gate.I := by
  unfold sqir_style_controlledModAddConst_gate; simp

/-- **R7d^xxix-L-3.14′ helper: q_start-parametric `c = 0` clean
bundle.**  When `c = 0` the total wrapper is `Gate.I`, so all six
conjuncts reduce to facts about the input state.

Mirrors `sqir_style_controlledModAddConst_gate_zero_clean` (line
2150) with general `q_start`, `flagPos`, and free `dim`.  Uses
`cuccaro_input_F_at_outside_eq_false` for the flag conjunct
instead of the hard-coded `unfold + if_pos`. -/
theorem sqir_style_controlledModAddConst_gate_zero_clean_qstart
    (bits q_start N x dim controlIdx flagPos : Nat) (control : Bool)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim) :
    Gate.WellTyped dim
        (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx control))
        = x
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx control))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) flagPos
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) controlIdx
        = control := by
  rw [sqir_style_controlledModAddConst_gate_zero_eq_qstart]
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- WellTyped: Gate.I requires 0 < dim.
    show 0 < dim
    omega
  · -- target_val = x.
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_target_val bits q_start
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) = x % 2 ^ bits := by
      apply cuccaro_target_val_eq_sum_when_bits_match
      intro i hi
      have h_ne : (q_start + 2 * i + 1 : Nat) ≠ controlIdx := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      rw [update_neq _ _ _ _ h_ne]
      exact cuccaro_input_F_at_b q_start i false 0 x
    rw [h_eq]
    exact Nat.mod_eq_of_lt h_x_lt
  · -- read_val = 0.
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_read_val bits q_start
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) = 0 % 2 ^ bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      have h_ne : (q_start + 2 * i + 2 : Nat) ≠ controlIdx := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      rw [update_neq _ _ _ _ h_ne]
      rw [cuccaro_input_F_at_a q_start i false 0 x]
    rw [h_eq]
    simp
  · -- top carry at q_start + 2 * bits.
    rw [Gate.applyNat_I]
    have h_ne : (q_start + 2 * bits : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    have h_eq : q_start + 2 * bits = q_start + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a q_start (bits - 1) false 0 x]
    exact Nat.zero_testBit _
  · -- flagPos = false.
    rw [Gate.applyNat_I]
    rw [update_neq _ _ _ _ hcontrol_ne_flag.symm]
    exact cuccaro_input_F_at_outside_eq_false q_start bits x flagPos hflag_out h_x_lt
  · -- controlIdx = control.
    rw [Gate.applyNat_I]
    exact update_eq _ _ _

/-- **R7d^xxix-L-3.14′ DELIVERABLE: q_start-parametric total wrapper
clean theorem.**

Combines the `c = 0` case (delegated to
`_gate_zero_clean_qstart` above, with the target conjunct
re-massaged to match the headline's `if control then (x+c)%N else x`
shape at `c = 0`) and the `c > 0` case (delegated to the L-3.13′
`_candidate_clean_qstart`).

Mirrors `sqir_style_controlledModAddConst_gate_clean` (line 3871)
with general `q_start`, `flagPos`, `controlIdx`, and free `dim`. -/
theorem sqir_style_controlledModAddConst_gate_clean_qstart
    (bits q_start N c x dim controlIdx flagPos : Nat) (control : Bool)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_control_lt_dim : controlIdx < dim)
    (h_flag_lt_dim : flagPos < dim) :
    Gate.WellTyped dim
        (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx control))
        = (if control then (x + c) % N else x)
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx control)) = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) flagPos
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) controlIdx
        = control := by
  by_cases hc0 : c = 0
  · subst hc0
    obtain ⟨h_wt, h_tgt, h_rd, h_tc, h_fl, h_ctrl⟩ :=
      sqir_style_controlledModAddConst_gate_zero_clean_qstart bits q_start N x dim
        controlIdx flagPos control hbits hN_pos hN hx hcontrol_out hflag_out hcontrol_ne_flag
        h_workspace
    refine ⟨h_wt, ?_, h_rd, h_tc, h_fl, h_ctrl⟩
    rw [h_tgt]
    cases control
    · simp
    · simp; exact (Nat.mod_eq_of_lt hx).symm
  · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc0
    have h_unfold :
        sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos
          = sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos := by
      unfold sqir_style_controlledModAddConst_gate
      simp [hc0]
    rw [h_unfold]
    exact sqir_style_controlledModAddConst_candidate_clean_qstart bits q_start N c x dim
      controlIdx flagPos control hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hflag_out
      hcontrol_ne_flag h_workspace h_control_lt_dim h_flag_lt_dim

/-- **HEADLINE Deliverable G — total wrapper clean theorem.** -/
theorem sqir_style_controlledModAddConst_gate_clean
    (bits N c x controlIdx : Nat) (control : Bool) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1)
    (h_control_workspace_lt : controlIdx < sqir_modmult_rev_anc bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = (if control then (x + c) % N else x)
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control)) = 0
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) (2 + 2 * bits) = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) 1 = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx = control := by
  by_cases hc0 : c = 0
  · subst hc0
    obtain ⟨h_wt, h_tgt, h_rd, h_tc, h_fl, h_ctrl⟩ :=
      sqir_style_controlledModAddConst_gate_zero_clean bits N x controlIdx control hbits hN_pos
        hN hx hcontrol_out hcontrol_ne_flag
    refine ⟨h_wt, ?_, h_rd, h_tc, h_fl, h_ctrl⟩
    rw [h_tgt]
    cases control
    · simp
    · simp; exact (Nat.mod_eq_of_lt hx).symm
  · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc0
    have h_unfold : sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1
        = sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1 := by
      unfold sqir_style_controlledModAddConst_gate
      simp [hc0]
    rw [h_unfold]
    exact sqir_style_controlledModAddConst_candidate_clean bits N c x controlIdx control hbits
      hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag h_control_workspace_lt

/-- **HEADLINE Deliverable H — BasicSetting-derived total wrapper clean theorem.** -/
theorem sqir_style_controlledModAddConst_gate_clean_from_BasicSetting
    (a r N m n c x controlIdx : Nat) (control : Bool)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * (n + 1) + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1)
    (h_control_workspace_lt : controlIdx < sqir_modmult_rev_anc (n + 1)) :
    Gate.WellTyped (sqir_modmult_rev_anc (n + 1))
        (sqir_style_controlledModAddConst_gate (n + 1) 2 N c controlIdx 1)
    ∧ cuccaro_target_val (n + 1) 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate (n + 1) 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = (if control then (x + c) % N else x)
    ∧ cuccaro_read_val (n + 1) 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate (n + 1) 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control)) = 0
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate (n + 1) 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) (2 + 2 * (n + 1)) = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate (n + 1) 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) 1 = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate (n + 1) 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx = control := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have hN_le : N ≤ 2 ^ (n + 1) := by omega
  exact sqir_style_controlledModAddConst_gate_clean (n + 1) N c x controlIdx control
    (by omega : 1 ≤ n + 1) hN_pos hN_le hN2 hc hx hcontrol_out hcontrol_ne_flag
    h_control_workspace_lt

/-! ## Status note (Tick 60).

Landed in this tick (all kernel-clean except as noted):
- `sqir_style_modAddConst_dirtyFlag_read_decode` (Deliverable A.1).
- `sqir_style_modAddConst_dirtyFlag_carry_in_restored` (Deliverable A.2).
- `sqir_style_modAddConst_dirtyFlag_flag_value` (Deliverable A.3).
- `sqir_style_modAddConst_dirtyFlag_candidate_wellTyped_sqir_dim`
  (Deliverable B).
- `sqir_style_modAddConst_dirtyFlag_clean_except_flag` (Deliverable C):
  full 5-conjunct bundle.
- `sqir_style_modAddConst_dirtyFlag_candidate_wellTyped_sqir_layout`
  (Deliverable D, partial — WellTyped only).
- `BasicSetting_twoN_le_pow_succ` (Deliverable E): the sizing relation,
  expressed for `bits := n + 1`.

Honesty disclosures:
- **Flag remains dirty.** The bundle theorem name includes
  `clean_except_flag` and the 5th conjunct states the flag's value.
  This is NOT clean modular addition.
- **Semantic theorems require `h_flag_above`.**  The SQIR-style
  comparator's flag theorem was set up with the flag above workspace;
  extending to below-workspace flag (as in SQIR's exact layout with
  flagPos = 1 < q_start = 2) is deferred.  WellTyped at the SQIR-exact
  layout IS proved (Deliverable D, partial).
- **Sizing is `bits = n + 1`.** Deliverable E shows `2 * N ≤ 2^(n+1)`
  follows from `N < 2^n` (the upper half of `BasicSetting`).  The other
  half `2^n ≤ 2 * N` is NOT used by the modadd primitive; it constrains
  Shor's m-precision register, not the mod-N add's bit width.  Future
  Shor integration should instantiate `bits := n + 1`.
- **Original SQIR placeholder axioms NOT YET CLOSED.**
  `f_modmult_circuit`, `f_modmult_circuit_MMI`, and
  `f_modmult_circuit_uc_well_typed` remain untouched.

Next steps (Tick 61+):
1. Below-workspace flag adaptation for `compareConst`'s flag and
   workspace theorems — enables target_decode + workspace at the
   SQIR-exact layout (flagPos = 1 < q_start = 2).
2. Flag uncomputation design — the path from dirty-flag mod-N add to
   clean mod-N add.  Candidate: rerun the comparator on the final
   output `(x+c) % N` (which is `< N`), so the comparator returns
   `decide(N ≤ (x+c)%N) = false`, XORing the dirty flag back to false.
3. Controlled mod-N add (Phase 3 of the modarith-to-modexp plan). -/

end FormalRV.BQAlgo
