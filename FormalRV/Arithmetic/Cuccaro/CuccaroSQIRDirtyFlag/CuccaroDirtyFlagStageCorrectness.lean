import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRCondAdd
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroModularAddDefinitions

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
lemma prepareMaj_at_top_eq_after_update
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
lemma cuccaro_prepareConstRead_zero_eq_id_fun
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
lemma cuccaro_addConstGate_zero_eq_full_adder_fun
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

end FormalRV.BQAlgo
