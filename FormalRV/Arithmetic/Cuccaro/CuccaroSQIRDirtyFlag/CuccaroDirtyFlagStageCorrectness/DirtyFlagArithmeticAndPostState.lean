/- CuccaroDirtyFlagStageCorrectness — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
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


end FormalRV.BQAlgo
