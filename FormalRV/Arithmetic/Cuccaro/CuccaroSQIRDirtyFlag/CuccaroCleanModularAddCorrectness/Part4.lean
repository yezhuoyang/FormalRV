/- CuccaroCleanModularAddCorrectness — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroCleanModularAddCorrectness.Part3

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

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


end FormalRV.BQAlgo
