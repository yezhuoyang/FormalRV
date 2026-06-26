/- CuccaroDirtyFlagStageCorrectness — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroDirtyFlagStageCorrectness.Part3

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

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
