import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultEncoding
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSpec
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultQStart
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultFamily
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSizing

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

theorem sqir_mult_control_idx_outside_modadd_workspace
    (bits j : Nat) :
    sqir_mult_control_idx bits j < 2
      ∨ 2 + (2 * bits + 1) ≤ sqir_mult_control_idx bits j := by
  right
  unfold sqir_mult_control_idx
  omega

theorem sqir_mult_control_idx_ne_flag
    (bits j : Nat) :
    sqir_mult_control_idx bits j ≠ 1 := by
  unfold sqir_mult_control_idx
  omega

theorem sqir_mult_control_idx_ne_top_carry
    (bits j : Nat) :
    sqir_mult_control_idx bits j ≠ 2 + 2 * bits := by
  unfold sqir_mult_control_idx
  omega

theorem sqir_mult_control_idx_lt_sqir_dim
    (bits j : Nat) (hj : j < bits) :
    sqir_mult_control_idx bits j < sqir_modmult_rev_anc bits := by
  unfold sqir_mult_control_idx sqir_modmult_rev_anc
  omega

theorem sqir_mult_control_idx_outside_modadd_workspace_form
    (bits j : Nat) :
    sqir_mult_control_idx bits j < 2
      ∨ 2 + 2 * bits + 1 ≤ sqir_mult_control_idx bits j := by
  right
  unfold sqir_mult_control_idx
  omega

/-- Distinct multiplier bits map to distinct positions. -/
theorem sqir_mult_control_idx_injective
    (bits j j' : Nat) (h : sqir_mult_control_idx bits j = sqir_mult_control_idx bits j') :
    j = j' := by
  unfold sqir_mult_control_idx at h
  omega

/-- **Multiplier bit at `sqir_mult_control_idx bits j` is `m.testBit j`.** -/
theorem sqir_mult_input_control_bit
    (bits m acc j : Nat) (hj : j < bits) :
    sqir_mult_input_F bits m acc (sqir_mult_control_idx bits j) = m.testBit j := by
  unfold sqir_mult_input_F sqir_mult_control_idx
  have h1 : ¬ (2 + (2 * bits + 1) + j < 2 + 2 * bits + 1) := by omega
  rw [if_neg h1]
  have h2 : 2 + (2 * bits + 1) + j < 2 + 2 * bits + 1 + bits := by omega
  rw [if_pos h2]
  congr 1
  omega

/-- **Decoded target register equals `acc` (for `acc < 2^bits`).** -/
theorem sqir_mult_input_target_decode
    (bits m acc : Nat) (hacc : acc < 2 ^ bits) :
    cuccaro_target_val bits 2 (sqir_mult_input_F bits m acc) = acc := by
  have h_eq : cuccaro_target_val bits 2 (sqir_mult_input_F bits m acc) = acc % 2 ^ bits := by
    apply cuccaro_target_val_eq_sum_when_bits_match
    intro i hi
    unfold sqir_mult_input_F
    have h1 : 2 + 2 * i + 1 < 2 + 2 * bits + 1 := by omega
    rw [if_pos h1]
    exact cuccaro_input_F_at_b 2 i false 0 acc
  rw [h_eq]
  exact Nat.mod_eq_of_lt hacc

/-- **Decoded read register is 0.** -/
theorem sqir_mult_input_read_decode
    (bits m acc : Nat) :
    cuccaro_read_val bits 2 (sqir_mult_input_F bits m acc) = 0 := by
  have h_eq : cuccaro_read_val bits 2 (sqir_mult_input_F bits m acc) = 0 % 2 ^ bits := by
    apply cuccaro_read_val_eq_sum_when_bits_match
    intro i hi
    unfold sqir_mult_input_F
    have h1 : 2 + 2 * i + 2 < 2 + 2 * bits + 1 := by omega
    rw [if_pos h1]
    rw [cuccaro_input_F_at_a 2 i false 0 acc]
  rw [h_eq]
  simp

/-- **Flag bits are false.** -/
theorem sqir_mult_input_flag_0_false
    (bits m acc : Nat) :
    sqir_mult_input_F bits m acc 0 = false := by
  unfold sqir_mult_input_F
  rw [if_pos (by omega : (0 : Nat) < 2 + 2 * bits + 1)]
  unfold cuccaro_input_F
  rw [if_pos (by omega : (0 : Nat) < 2)]

theorem sqir_mult_input_flag_1_false
    (bits m acc : Nat) :
    sqir_mult_input_F bits m acc 1 = false := by
  unfold sqir_mult_input_F
  rw [if_pos (by omega : (1 : Nat) < 2 + 2 * bits + 1)]
  unfold cuccaro_input_F
  rw [if_pos (by omega : (1 : Nat) < 2)]

/-- **Top carry is false (when bits ≥ 1).**  The top carry position
`2 + 2*bits = 2 + 2*(bits-1) + 2` is the highest read register bit
in the Cuccaro encoding with `a = 0`. -/
theorem sqir_mult_input_top_carry_false
    (bits m acc : Nat) (hbits : 1 ≤ bits) :
    sqir_mult_input_F bits m acc (2 + 2 * bits) = false := by
  unfold sqir_mult_input_F
  rw [if_pos (by omega : (2 + 2 * bits : Nat) < 2 + 2 * bits + 1)]
  have h_eq : (2 + 2 * bits : Nat) = 2 + 2 * (bits - 1) + 2 := by omega
  rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 acc]
  exact Nat.zero_testBit _

theorem sqir_modmult_acc_spec_zero (N a m : Nat) :
    sqir_modmult_acc_spec N a m 0 = 0 := rfl

theorem sqir_modmult_acc_spec_succ_false
    (N a m k : Nat) (h : m.testBit k = false) :
    sqir_modmult_acc_spec N a m (k + 1) = sqir_modmult_acc_spec N a m k := by
  show (if m.testBit k then _ else sqir_modmult_acc_spec N a m k) = _
  simp [h]

theorem sqir_modmult_acc_spec_succ_true
    (N a m k : Nat) (h : m.testBit k = true) :
    sqir_modmult_acc_spec N a m (k + 1)
      = (sqir_modmult_acc_spec N a m k + (a * 2 ^ k) % N) % N := by
  show (if m.testBit k then (sqir_modmult_acc_spec N a m k + (a * 2 ^ k) % N) % N else _) = _
  simp [h]

/-- For `0 < N`, the accumulator after any prefix is in `[0, N)`. -/
theorem sqir_modmult_acc_spec_lt (N a m k : Nat) (hN_pos : 0 < N) :
    sqir_modmult_acc_spec N a m k < N := by
  induction k with
  | zero => exact hN_pos
  | succ n ih =>
    unfold sqir_modmult_acc_spec
    by_cases h : m.testBit n
    · rw [if_pos h]
      exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]
      exact ih

theorem sqir_modmult_prefix_gate_zero_eq_I
    (bits N a : Nat) :
    sqir_modmult_prefix_gate bits N a 0 = Gate.I := rfl

theorem sqir_modmult_prefix_gate_succ_eq
    (bits N a k : Nat) :
    sqir_modmult_prefix_gate bits N a (k + 1)
      = seq (sqir_modmult_prefix_gate bits N a k) (sqir_modmult_step_gate bits N a k) := rfl

/-! ## Tick 74 — Wrapper-level commute helpers. -/

/-- **Controlled compareConst commutes with update at outside position
distinct from the inner controlIdx and flagPos.** -/
theorem sqir_controlledCompareConst_commute_update_outside_fun
    (bits q_start c controlIdx flagPos updateIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hupdate_out : updateIdx < q_start ∨ q_start + 2 * bits + 1 ≤ updateIdx)
    (hupdate_ne_flag : updateIdx ≠ flagPos)
    (hupdate_ne_ctrl : updateIdx ≠ controlIdx) :
    Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
        (update f updateIdx v)
      = update (Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos) f)
              updateIdx v := by
  unfold sqir_controlledCompareConst
  simp only [Gate.applyNat_seq]
  have h_ctrl_ne_top : updateIdx ≠ q_start + 2 * bits := by
    rcases hupdate_out with hl | hr
    · omega
    · omega
  rw [sqir_prepareMaskedConstRead_commute_update_outside_workspace bits q_start (2^bits - c)
        controlIdx updateIdx v f hupdate_out hupdate_ne_ctrl]
  rw [cuccaro_maj_chain_commute_update_outside_workspace bits q_start updateIdx v _ hupdate_out]
  rw [Gate.applyNat_CX_commute_update_outside_fun (q_start + 2 * bits) flagPos updateIdx v _
        h_ctrl_ne_top hupdate_ne_flag]
  rw [cuccaro_maj_chain_inv_commute_update_outside_workspace_fun bits q_start updateIdx v _
        hupdate_out]
  rw [sqir_prepareMaskedConstRead_commute_update_outside_workspace bits q_start (2^bits - c)
        controlIdx updateIdx v _ hupdate_out hupdate_ne_ctrl]

/-- **Deliverable A — controlled modular add-constant gate commutes
with `update` at outside positions (distinct from flag and controlIdx).** -/
theorem sqir_style_controlledModAddConst_gate_commute_update_outside_fun
    (bits N c controlIdx updateIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hupdate_out : updateIdx < 2 ∨ 2 + (2 * bits + 1) ≤ updateIdx)
    (hupdate_ne_flag : updateIdx ≠ 1)
    (hupdate_ne_control : updateIdx ≠ controlIdx) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
        (update f updateIdx v)
      = update (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1) f)
              updateIdx v := by
  unfold sqir_style_controlledModAddConst_gate
  by_cases hc : c = 0
  · simp [hc, Gate.applyNat_I]
  · simp only [hc, if_false]
    unfold sqir_style_controlledModAddConst_candidate
    simp only [Gate.applyNat_seq]
    rw [sqir_conditionalAddConstGate_commute_update_outside_fun bits 2 c controlIdx updateIdx v f
          hupdate_out hupdate_ne_control]
    rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits 2 N 1 updateIdx v _
          hupdate_out hupdate_ne_flag]
    rw [sqir_conditionalSubConstGate_commute_update_outside_fun bits 2 N 1 updateIdx v _
          hupdate_out hupdate_ne_flag]
    rw [sqir_controlledCompareConst_commute_update_outside_fun bits 2 c controlIdx 1 updateIdx v _
          hupdate_out hupdate_ne_flag hupdate_ne_control]
    rw [Gate.applyNat_CX_commute_update_outside_fun controlIdx 1 updateIdx v _
          hupdate_ne_control hupdate_ne_flag]

/-- The j-th multiplier bit lies above the shifted Cuccaro workspace
`[q_start, q_start + 2 * bits + 1)`.  Port of
`sqir_mult_control_idx_outside_modadd_workspace_form` (line 63). -/
theorem sqir_mult_control_idx_outside_modadd_workspace_form_qstart
    (bits q_start j : Nat) :
    sqir_mult_control_idx_qstart bits q_start j < q_start
      ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start j := by
  right
  unfold sqir_mult_control_idx_qstart
  omega

/-- The j-th multiplier bit is distinct from any chosen `flagPos`
strictly below the shifted workspace.  Port of
`sqir_mult_control_idx_ne_flag` (line 45). -/
theorem sqir_mult_control_idx_ne_flag_qstart
    (bits q_start j flagPos : Nat) (h_flag_lt : flagPos < q_start) :
    sqir_mult_control_idx_qstart bits q_start j ≠ flagPos := by
  unfold sqir_mult_control_idx_qstart
  omega

/-- The j-th multiplier bit fits in a dimension that covers the
workspace plus the multiplier register.  Port of
`sqir_mult_control_idx_lt_sqir_dim` (line 57) generalised to a free
`dim` parameter. -/
theorem sqir_mult_control_idx_lt_dim_qstart
    (bits q_start j dim : Nat) (hj : j < bits)
    (h_dim : q_start + (2 * bits + 1) + bits ≤ dim) :
    sqir_mult_control_idx_qstart bits q_start j < dim := by
  unfold sqir_mult_control_idx_qstart
  omega

/-- Distinct multiplier bits map to distinct positions.  Port of
`sqir_mult_control_idx_injective` (line 72). -/
theorem sqir_mult_control_idx_injective_qstart
    (bits q_start j j' : Nat)
    (h : sqir_mult_control_idx_qstart bits q_start j
          = sqir_mult_control_idx_qstart bits q_start j') :
    j = j' := by
  unfold sqir_mult_control_idx_qstart at h
  omega

/-- The multiplier bit at `sqir_mult_control_idx_qstart bits q_start j`
is `m.testBit j`.  Port of `sqir_mult_input_control_bit` (line 103). -/
theorem sqir_mult_input_control_bit_qstart
    (bits q_start m acc j : Nat) (hj : j < bits) :
    sqir_mult_input_F_qstart bits q_start m acc
        (sqir_mult_control_idx_qstart bits q_start j) = m.testBit j := by
  unfold sqir_mult_input_F_qstart sqir_mult_control_idx_qstart
  have h1 : ¬ (q_start + (2 * bits + 1) + j < q_start + 2 * bits + 1) := by omega
  rw [if_neg h1]
  have h2 : q_start + (2 * bits + 1) + j < q_start + 2 * bits + 1 + bits := by omega
  rw [if_pos h2]
  congr 1
  omega

/-- q_start-parametric commute helper for the controlled mod-add gate.

Port of `sqir_style_controlledModAddConst_gate_commute_update_outside_fun`
(line 276): the gate commutes with an `update` at any position outside
its workspace and distinct from both `controlIdx` and `flagPos`.

All sub-helpers are already q_start-parametric:
- `sqir_conditionalAddConstGate_commute_update_outside_fun`
  (CuccaroSQIRDirtyFlag.lean:3157);
- `sqir_style_compareConst_candidate_commute_update_outside_fun` (:3132);
- `sqir_conditionalSubConstGate_commute_update_outside_fun` (:3174);
- `sqir_controlledCompareConst_commute_update_outside_fun` (this file:249);
- `Gate.applyNat_CX_commute_update_outside_fun` (CuccaroSQIRDirtyFlag.lean:3039). -/
theorem sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart
    (bits q_start N c controlIdx flagPos updateIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hupdate_out : updateIdx < q_start ∨ q_start + 2 * bits + 1 ≤ updateIdx)
    (hupdate_ne_flag : updateIdx ≠ flagPos)
    (hupdate_ne_control : updateIdx ≠ controlIdx) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
        (update f updateIdx v)
      = update (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
                                  controlIdx flagPos) f)
              updateIdx v := by
  unfold sqir_style_controlledModAddConst_gate
  by_cases hc : c = 0
  · simp [hc, Gate.applyNat_I]
  · simp only [hc, if_false]
    unfold sqir_style_controlledModAddConst_candidate
    simp only [Gate.applyNat_seq]
    rw [sqir_conditionalAddConstGate_commute_update_outside_fun bits q_start c controlIdx
          updateIdx v f hupdate_out hupdate_ne_control]
    rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits q_start N flagPos
          updateIdx v _ hupdate_out hupdate_ne_flag]
    rw [sqir_conditionalSubConstGate_commute_update_outside_fun bits q_start N flagPos
          updateIdx v _ hupdate_out hupdate_ne_flag]
    rw [sqir_controlledCompareConst_commute_update_outside_fun bits q_start c controlIdx flagPos
          updateIdx v _ hupdate_out hupdate_ne_flag hupdate_ne_control]
    rw [Gate.applyNat_CX_commute_update_outside_fun controlIdx flagPos updateIdx v _
          hupdate_ne_control hupdate_ne_flag]

/-- **`install_mult_bits_skip_j` at outside workspace.**  At any position
`q < 2 + 2 * bits + 1`, the installs don't touch `q` (they update only at
multiplier positions). -/
theorem install_mult_bits_skip_j_at_workspace_eq
    (bits m j num_bits : Nat) (f : Nat → Bool) (q : Nat)
    (hq : q < 2 + 2 * bits + 1) :
    install_mult_bits_skip_j bits m j num_bits f q = f q := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_eq : k = j
    · rw [if_pos h_eq]; exact ih
    · rw [if_neg h_eq]
      have h_ne : q ≠ sqir_mult_control_idx bits k := by
        have h_ctrl_ge : sqir_mult_control_idx bits k ≥ 2 + 2 * bits + 1 := by
          unfold sqir_mult_control_idx; omega
        omega
      rw [update_neq _ _ _ _ h_ne]
      exact ih

/-- **`install_mult_bits_skip_j` at multiplier position `k`** (`k < num_bits`,
`k ≠ j`): installs `m.testBit k`. -/
theorem install_mult_bits_skip_j_at_mult_k_eq
    (bits m j num_bits k : Nat) (f : Nat → Bool)
    (h_k_lt : k < num_bits) (h_k_ne_j : k ≠ j) :
    install_mult_bits_skip_j bits m j num_bits f (sqir_mult_control_idx bits k)
      = m.testBit k := by
  induction num_bits with
  | zero => omega
  | succ n ih =>
    unfold install_mult_bits_skip_j
    by_cases h_eq : n = j
    · rw [if_pos h_eq]
      -- After skip, recurse with smaller num_bits.  Need k < n.
      apply ih
      omega
    · rw [if_neg h_eq]
      by_cases h_kn : k = n
      · rw [h_kn, update_eq]
      · have h_ne : sqir_mult_control_idx bits k ≠ sqir_mult_control_idx bits n := by
          intro heq
          exact h_kn (sqir_mult_control_idx_injective bits k n heq)
        rw [update_neq _ _ _ _ h_ne]
        apply ih
        omega

/-- **`install_mult_bits_skip_j` at the skipped position `j`.**  Installs
never touch position `controlIdx_j` (always skipped), so the install
returns `f (controlIdx_j)`. -/
theorem install_mult_bits_skip_j_at_j_eq
    (bits m j num_bits : Nat) (f : Nat → Bool) :
    install_mult_bits_skip_j bits m j num_bits f (sqir_mult_control_idx bits j)
      = f (sqir_mult_control_idx bits j) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_ne : sqir_mult_control_idx bits j ≠ sqir_mult_control_idx bits k :=
        fun heq => h_kj (sqir_mult_control_idx_injective bits j k heq).symm
      rw [update_neq _ _ _ _ h_ne]
      exact ih

/-- **`install_mult_bits_skip_j` at outside-multiplier upper positions.**
For `q ≥ 2 + 2 * bits + 1 + bits` (above the multiplier register), installs
don't touch `q`. -/
theorem install_mult_bits_skip_j_at_above_eq
    (bits m j num_bits : Nat) (h_num_le : num_bits ≤ bits) (f : Nat → Bool) (q : Nat)
    (hq : q ≥ 2 + 2 * bits + 1 + bits) :
    install_mult_bits_skip_j bits m j num_bits f q = f q := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_eq : k = j
    · rw [if_pos h_eq]; exact ih (by omega)
    · rw [if_neg h_eq]
      have h_ne : q ≠ sqir_mult_control_idx bits k := by
        have h_ctrl_lt : sqir_mult_control_idx bits k < 2 + 2 * bits + 1 + bits := by
          unfold sqir_mult_control_idx; omega
        omega
      rw [update_neq _ _ _ _ h_ne]
      exact ih (by omega)

end FormalRV.BQAlgo
