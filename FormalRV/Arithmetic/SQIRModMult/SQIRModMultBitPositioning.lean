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

/-! ## Deliverable B — Bridge: `sqir_mult_input_F` as install over `F_j`. -/

/-- **`sqir_mult_input_F` decomposes as `install_mult_bits_skip_j` applied
to `update (cuccaro_input_F) controlIdx_j (m.testBit j)`.** -/
theorem sqir_mult_input_F_eq_install_with_j
    (bits m acc j : Nat) (hj : j < bits) (hacc : acc < 2 ^ bits) :
    sqir_mult_input_F bits m acc
      = install_mult_bits_skip_j bits m j bits
          (update (cuccaro_input_F 2 false 0 acc) (sqir_mult_control_idx bits j) (m.testBit j)) := by
  funext q
  by_cases hq_ws : q < 2 + 2 * bits + 1
  · -- q < workspace upper bound: both sides = cuccaro_input_F at q.
    rw [install_mult_bits_skip_j_at_workspace_eq bits m j bits _ q hq_ws]
    -- LHS: sqir_mult_input_F q = cuccaro_input_F at q.
    have h_lhs : sqir_mult_input_F bits m acc q = cuccaro_input_F 2 false 0 acc q := by
      unfold sqir_mult_input_F; rw [if_pos hq_ws]
    -- RHS: update F controlIdx_j _ at q = F at q (since q < controlIdx_j).
    have h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx bits j := by
      have : sqir_mult_control_idx bits j ≥ 2 + 2 * bits + 1 := by
        unfold sqir_mult_control_idx; omega
      omega
    rw [h_lhs, update_neq _ _ _ _ h_q_ne_ctrl_j]
  · push_neg at hq_ws
    -- q ≥ 2 + 2*bits + 1.
    by_cases hq_in_mult : q < 2 + 2 * bits + 1 + bits
    · -- q is in multiplier register.
      set k := q - (2 + 2 * bits + 1) with hk_def
      have hk_lt : k < bits := by omega
      have h_q_eq : q = sqir_mult_control_idx bits k := by
        unfold sqir_mult_control_idx; omega
      rw [h_q_eq]
      have h_lhs : sqir_mult_input_F bits m acc (sqir_mult_control_idx bits k)
                 = m.testBit k :=
        sqir_mult_input_control_bit bits m acc k hk_lt
      rw [h_lhs]
      by_cases h_kj : k = j
      · -- k = j: install skips, but F_j has the j-th update directly.
        rw [h_kj]
        rw [install_mult_bits_skip_j_at_j_eq bits m j bits _]
        rw [update_eq]
      · -- k ≠ j: install puts m.testBit k at controlIdx_k.
        rw [install_mult_bits_skip_j_at_mult_k_eq bits m j bits k _ hk_lt h_kj]
    · push_neg at hq_in_mult
      -- q ≥ 2 + 2*bits + 1 + bits.
      rw [install_mult_bits_skip_j_at_above_eq bits m j bits (le_refl _) _ q hq_in_mult]
      have h_lhs : sqir_mult_input_F bits m acc q = false := by
        unfold sqir_mult_input_F
        rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
        rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]
      have h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx bits j := by
        have : sqir_mult_control_idx bits j < 2 + 2 * bits + 1 + bits := by
          unfold sqir_mult_control_idx; omega
        omega
      rw [h_lhs, update_neq _ _ _ _ h_q_ne_ctrl_j]
      -- cuccaro_input_F at q (≥ 2 + 2*bits + 1) = false (q ≥ q_start + 2*bits + 1).
      exact (cuccaro_input_F_above_eq_false 2 bits acc q (by omega) hacc).symm

/-- q_start-parametric: install chain does not modify positions strictly
below `q_start + 2 * bits + 1`.  Port of
`install_mult_bits_skip_j_at_workspace_eq` (line 456). -/
theorem install_mult_bits_skip_j_at_workspace_eq_qstart
    (bits q_start m j num_bits : Nat) (f : Nat → Bool) (q : Nat)
    (hq : q < q_start + 2 * bits + 1) :
    install_mult_bits_skip_j_qstart bits q_start m j num_bits f q = f q := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_eq : k = j
    · rw [if_pos h_eq]; exact ih
    · rw [if_neg h_eq]
      have h_ne : q ≠ sqir_mult_control_idx_qstart bits q_start k := by
        have h_ctrl_ge :
            sqir_mult_control_idx_qstart bits q_start k ≥ q_start + 2 * bits + 1 := by
          unfold sqir_mult_control_idx_qstart; omega
        omega
      rw [update_neq _ _ _ _ h_ne]
      exact ih

/-- q_start-parametric: install chain at multiplier position `k`
(`k < num_bits`, `k ≠ j`) installs `m.testBit k`.  Port of
`install_mult_bits_skip_j_at_mult_k_eq` (line 476). -/
theorem install_mult_bits_skip_j_at_mult_k_eq_qstart
    (bits q_start m j num_bits k : Nat) (f : Nat → Bool)
    (h_k_lt : k < num_bits) (h_k_ne_j : k ≠ j) :
    install_mult_bits_skip_j_qstart bits q_start m j num_bits f
        (sqir_mult_control_idx_qstart bits q_start k) = m.testBit k := by
  induction num_bits with
  | zero => omega
  | succ n ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_eq : n = j
    · rw [if_pos h_eq]
      apply ih
      omega
    · rw [if_neg h_eq]
      by_cases h_kn : k = n
      · rw [h_kn, update_eq]
      · have h_ne :
            sqir_mult_control_idx_qstart bits q_start k
              ≠ sqir_mult_control_idx_qstart bits q_start n := by
          intro heq
          exact h_kn (sqir_mult_control_idx_injective_qstart bits q_start k n heq)
        rw [update_neq _ _ _ _ h_ne]
        apply ih
        omega

/-- q_start-parametric: install chain at the skipped position `j` is
preserved from the base state.  Port of
`install_mult_bits_skip_j_at_j_eq` (line 503). -/
theorem install_mult_bits_skip_j_at_j_eq_qstart
    (bits q_start m j num_bits : Nat) (f : Nat → Bool) :
    install_mult_bits_skip_j_qstart bits q_start m j num_bits f
        (sqir_mult_control_idx_qstart bits q_start j)
      = f (sqir_mult_control_idx_qstart bits q_start j) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_ne :
          sqir_mult_control_idx_qstart bits q_start j
            ≠ sqir_mult_control_idx_qstart bits q_start k :=
        fun heq => h_kj
          (sqir_mult_control_idx_injective_qstart bits q_start j k heq).symm
      rw [update_neq _ _ _ _ h_ne]
      exact ih

/-- q_start-parametric: install chain identity above the multiplier
register.  Port of `install_mult_bits_skip_j_at_above_eq` (line 522). -/
theorem install_mult_bits_skip_j_at_above_eq_qstart
    (bits q_start m j num_bits : Nat) (h_num_le : num_bits ≤ bits)
    (f : Nat → Bool) (q : Nat)
    (hq : q ≥ q_start + 2 * bits + 1 + bits) :
    install_mult_bits_skip_j_qstart bits q_start m j num_bits f q = f q := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_eq : k = j
    · rw [if_pos h_eq]; exact ih (by omega)
    · rw [if_neg h_eq]
      have h_ne : q ≠ sqir_mult_control_idx_qstart bits q_start k := by
        have h_ctrl_lt :
            sqir_mult_control_idx_qstart bits q_start k < q_start + 2 * bits + 1 + bits := by
          unfold sqir_mult_control_idx_qstart; omega
        omega
      rw [update_neq _ _ _ _ h_ne]
      exact ih (by omega)

/-- q_start-parametric bridge: `sqir_mult_input_F_qstart bits q_start m
acc` decomposes as `install_mult_bits_skip_j_qstart` applied to
`update (cuccaro_input_F q_start false 0 acc) (sqir_mult_control_idx_qstart
bits q_start j) (m.testBit j)`.  Port of
`sqir_mult_input_F_eq_install_with_j` (line 544). -/
theorem sqir_mult_input_F_eq_install_with_j_qstart
    (bits q_start m acc j : Nat) (hj : j < bits) (hacc : acc < 2 ^ bits) :
    sqir_mult_input_F_qstart bits q_start m acc
      = install_mult_bits_skip_j_qstart bits q_start m j bits
          (update (cuccaro_input_F q_start false 0 acc)
            (sqir_mult_control_idx_qstart bits q_start j) (m.testBit j)) := by
  funext q
  by_cases hq_ws : q < q_start + 2 * bits + 1
  · -- q below workspace upper bound: both sides equal `cuccaro_input_F` at q.
    rw [install_mult_bits_skip_j_at_workspace_eq_qstart bits q_start m j bits _ q hq_ws]
    have h_lhs : sqir_mult_input_F_qstart bits q_start m acc q
                = cuccaro_input_F q_start false 0 acc q := by
      unfold sqir_mult_input_F_qstart; rw [if_pos hq_ws]
    have h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx_qstart bits q_start j := by
      have : sqir_mult_control_idx_qstart bits q_start j ≥ q_start + 2 * bits + 1 := by
        unfold sqir_mult_control_idx_qstart; omega
      omega
    rw [h_lhs, update_neq _ _ _ _ h_q_ne_ctrl_j]
  · push_neg at hq_ws
    by_cases hq_in_mult : q < q_start + 2 * bits + 1 + bits
    · -- q is in multiplier register.
      set k := q - (q_start + 2 * bits + 1) with hk_def
      have hk_lt : k < bits := by omega
      have h_q_eq : q = sqir_mult_control_idx_qstart bits q_start k := by
        unfold sqir_mult_control_idx_qstart; omega
      rw [h_q_eq]
      have h_lhs : sqir_mult_input_F_qstart bits q_start m acc
                      (sqir_mult_control_idx_qstart bits q_start k)
                 = m.testBit k :=
        sqir_mult_input_control_bit_qstart bits q_start m acc k hk_lt
      rw [h_lhs]
      by_cases h_kj : k = j
      · -- k = j: install skips, but the base state has the j-th update.
        rw [h_kj]
        rw [install_mult_bits_skip_j_at_j_eq_qstart bits q_start m j bits _]
        rw [update_eq]
      · -- k ≠ j: install puts m.testBit k at controlIdx_k.
        rw [install_mult_bits_skip_j_at_mult_k_eq_qstart bits q_start m j bits k _
              hk_lt h_kj]
    · push_neg at hq_in_mult
      -- q ≥ q_start + 2*bits + 1 + bits.
      rw [install_mult_bits_skip_j_at_above_eq_qstart bits q_start m j bits (le_refl _) _ q
            hq_in_mult]
      have h_lhs : sqir_mult_input_F_qstart bits q_start m acc q = false := by
        unfold sqir_mult_input_F_qstart
        rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1)]
        rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1 + bits)]
      have h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx_qstart bits q_start j := by
        have : sqir_mult_control_idx_qstart bits q_start j < q_start + 2 * bits + 1 + bits := by
          unfold sqir_mult_control_idx_qstart; omega
        omega
      rw [h_lhs, update_neq _ _ _ _ h_q_ne_ctrl_j]
      exact (cuccaro_input_F_above_eq_false q_start bits acc q (by omega) hacc).symm

/-! ## Tick 74 — Deliverable C: One-step target decode. -/

/-- **`cuccaro_target_val` is invariant under installing multiplier bits
on the gate-applied state.**  Each installed update is at position
`controlIdx_k` (outside workspace), so by Deliverable A (commute with
update) + `cuccaro_target_val_update_outside_workspace`, the target
register's decoded value is unchanged. -/
theorem cuccaro_target_val_through_install_mult
    (bits m j N c : Nat) (num_bits : Nat) (f : Nat → Bool) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1)
          (install_mult_bits_skip_j bits m j num_bits f))
      = cuccaro_target_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1) f) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_kj : k = j
    · rw [if_pos h_kj]
      exact ih
    · rw [if_neg h_kj]
      -- Apply Deliverable A to commute the gate with the update at controlIdx_k.
      have h_out : sqir_mult_control_idx bits k < 2
            ∨ 2 + (2 * bits + 1) ≤ sqir_mult_control_idx bits k := by
        right; unfold sqir_mult_control_idx; omega
      have h_ne_flag : sqir_mult_control_idx bits k ≠ 1 := by
        unfold sqir_mult_control_idx; omega
      have h_ne_ctrl_j :
          sqir_mult_control_idx bits k ≠ sqir_mult_control_idx bits j :=
        fun heq => h_kj (sqir_mult_control_idx_injective bits k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N c
            (sqir_mult_control_idx bits j) (sqir_mult_control_idx bits k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [cuccaro_target_val_update_outside_workspace bits 2
            (sqir_mult_control_idx bits k) (m.testBit k) _ h_out]
      exact ih

/-- **Deliverable C — One-step modular-multiplier target decode.**

After applying `sqir_modmult_step_gate bits N a j` to
`sqir_mult_input_F bits m acc`, the decoded target register equals
`if m.testBit j then (acc + (a * 2^j) % N) % N else acc`. -/
theorem sqir_modmult_step_target_decode
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc))
      = if m.testBit j then (acc + (a * 2 ^ j) % N) % N else acc := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  -- Bridge sqir_mult_input_F to install over F_j (Deliverable B).
  rw [sqir_mult_input_F_eq_install_with_j bits m acc j hj hacc_lt]
  unfold sqir_modmult_step_gate
  -- Push gate through install (target_val invariant).
  rw [cuccaro_target_val_through_install_mult bits m j N ((a * 2^j) % N) bits]
  -- Apply gate_clean target_decode on F_j.
  have h_ctrl_out :
      sqir_mult_control_idx bits j < 2
        ∨ 2 + 2 * bits + 1 ≤ sqir_mult_control_idx bits j :=
    sqir_mult_control_idx_outside_modadd_workspace_form bits j
  have h_ctrl_ne_flag : sqir_mult_control_idx bits j ≠ 1 :=
    sqir_mult_control_idx_ne_flag bits j
  have h_ctrl_lt : sqir_mult_control_idx bits j < sqir_modmult_rev_anc bits :=
    sqir_mult_control_idx_lt_sqir_dim bits j hj
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  have ⟨_, h_tgt, _⟩ :=
    sqir_style_controlledModAddConst_gate_clean bits N ((a * 2^j) % N) acc
      (sqir_mult_control_idx bits j) (m.testBit j)
      hbits hN_pos hN hN2 hc_pos hacc h_ctrl_out h_ctrl_ne_flag h_ctrl_lt
  exact h_tgt

/-! ## R7d^xxix-L-3.15c — q_start-parametric target-through-install
       bridge + step target-decode headline.

q_start-parametric counterparts of `cuccaro_target_val_through_install_mult`
and the headline `sqir_modmult_step_target_decode`.  Uses the L-3.15a
infrastructure (control-index facts, commute helper) and the L-3.15b
install chain + bridge, plus the L-3.14′
`sqir_style_controlledModAddConst_gate_clean_qstart`.

This sub-tick closes the q_start chain at the modular-multiplier-step
target-decode layer.  Workspace preservation
(`sqir_modmult_step_workspace_qstart`) is intentionally deferred. -/

/-- q_start-parametric: installing multiplier bits (other than the
j-th) outside the Cuccaro workspace does not change the gate's decoded
target value.  Port of `cuccaro_target_val_through_install_mult`
(line 782). -/
theorem cuccaro_target_val_through_install_mult_qstart
    (bits q_start m j N c flagPos : Nat) (num_bits : Nat) (f : Nat → Bool)
    (h_flag_lt_qstart : flagPos < q_start) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos)
          (install_mult_bits_skip_j_qstart bits q_start m j num_bits f))
      = cuccaro_target_val bits q_start
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos) f) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_kj : k = j
    · rw [if_pos h_kj]
      exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx_qstart bits q_start k < q_start
            ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start k :=
        sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start k
      have h_ne_flag : sqir_mult_control_idx_qstart bits q_start k ≠ flagPos :=
        sqir_mult_control_idx_ne_flag_qstart bits q_start k flagPos h_flag_lt_qstart
      have h_ne_ctrl_j :
          sqir_mult_control_idx_qstart bits q_start k
            ≠ sqir_mult_control_idx_qstart bits q_start j :=
        fun heq => h_kj (sqir_mult_control_idx_injective_qstart bits q_start k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos
            (sqir_mult_control_idx_qstart bits q_start k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [cuccaro_target_val_update_outside_workspace bits q_start
            (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k) _ h_out]
      exact ih

/-- **R7d^xxix-L-3.15c HEADLINE: q_start-parametric one-step modular-
multiplier target decode.**

After applying `sqir_modmult_step_gate_qstart bits q_start N a j flagPos`
to `sqir_mult_input_F_qstart bits q_start m acc`, the decoded target
register equals `if m.testBit j then (acc + (a * 2^j) % N) % N else acc`.

Port of `sqir_modmult_step_target_decode` (line 820).  Uses the L-3.14′
`sqir_style_controlledModAddConst_gate_clean_qstart`, the L-3.15a
control-index facts, and the L-3.15b install bridge + this tick's
`_through_install_mult_qstart`.

The `flagPos < q_start` hypothesis matches the hard-coded `flagPos = 1
< 2 = q_start` case and ensures `flagPos` is distinct from every
multiplier-bit position. -/
theorem sqir_modmult_step_target_decode_qstart
    (bits q_start N a j m acc dim flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
          (sqir_mult_input_F_qstart bits q_start m acc))
      = if m.testBit j then (acc + (a * 2 ^ j) % N) % N else acc := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  -- Bridge sqir_mult_input_F_qstart to install over F_j (L-3.15b).
  rw [sqir_mult_input_F_eq_install_with_j_qstart bits q_start m acc j hj hacc_lt]
  unfold sqir_modmult_step_gate_qstart
  -- Push gate through install (this tick's bridge).
  rw [cuccaro_target_val_through_install_mult_qstart bits q_start m j N ((a * 2^j) % N)
        flagPos bits _ h_flag_lt_qstart]
  -- Apply L-3.14′ gate_clean_qstart on the j-th-installed F.
  have h_ctrl_out :
      sqir_mult_control_idx_qstart bits q_start j < q_start
        ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start j :=
    sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start j
  have h_flag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos :=
    Or.inl h_flag_lt_qstart
  have h_ctrl_ne_flag : sqir_mult_control_idx_qstart bits q_start j ≠ flagPos :=
    sqir_mult_control_idx_ne_flag_qstart bits q_start j flagPos h_flag_lt_qstart
  have h_ctrl_lt_dim : sqir_mult_control_idx_qstart bits q_start j < dim :=
    sqir_mult_control_idx_lt_dim_qstart bits q_start j dim hj h_dim_covers_mult
  have h_flag_lt_dim : flagPos < dim := by omega
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  have ⟨_, h_tgt, _⟩ :=
    sqir_style_controlledModAddConst_gate_clean_qstart bits q_start N ((a * 2^j) % N) acc dim
      (sqir_mult_control_idx_qstart bits q_start j) flagPos (m.testBit j)
      hbits hN_pos hN hN2 hc_pos hacc h_ctrl_out h_flag_out h_ctrl_ne_flag
      h_workspace h_ctrl_lt_dim h_flag_lt_dim
  exact h_tgt

/-! ## Tick 74 — Deliverable D: One-step workspace preservation. -/

/-- **Read register invariant through install.** -/
theorem cuccaro_read_val_through_install_mult
    (bits m j N c : Nat) (num_bits : Nat) (f : Nat → Bool) :
    cuccaro_read_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1)
          (install_mult_bits_skip_j bits m j num_bits f))
      = cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1) f) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx bits k < 2
            ∨ 2 + (2 * bits + 1) ≤ sqir_mult_control_idx bits k := by
        right; unfold sqir_mult_control_idx; omega
      have h_ne_flag : sqir_mult_control_idx bits k ≠ 1 := by
        unfold sqir_mult_control_idx; omega
      have h_ne_ctrl_j :
          sqir_mult_control_idx bits k ≠ sqir_mult_control_idx bits j :=
        fun heq => h_kj (sqir_mult_control_idx_injective bits k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N c
            (sqir_mult_control_idx bits j) (sqir_mult_control_idx bits k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [cuccaro_read_val_update_outside_workspace bits 2
            (sqir_mult_control_idx bits k) (m.testBit k) _ h_out]
      exact ih

/-- **Position-wise invariance through install at workspace positions.** -/
theorem applyNat_modmult_through_install_at_workspace
    (bits m j N c : Nat) (num_bits q : Nat) (f : Nat → Bool)
    (hq_ws : q < 2 + 2 * bits + 1) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1)
      (install_mult_bits_skip_j bits m j num_bits f) q
      = Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1) f q := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx bits k < 2
            ∨ 2 + (2 * bits + 1) ≤ sqir_mult_control_idx bits k := by
        right; unfold sqir_mult_control_idx; omega
      have h_ne_flag : sqir_mult_control_idx bits k ≠ 1 := by
        unfold sqir_mult_control_idx; omega
      have h_ne_ctrl_j :
          sqir_mult_control_idx bits k ≠ sqir_mult_control_idx bits j :=
        fun heq => h_kj (sqir_mult_control_idx_injective bits k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N c
            (sqir_mult_control_idx bits j) (sqir_mult_control_idx bits k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      have h_q_ne_ctrl_k : q ≠ sqir_mult_control_idx bits k := by
        unfold sqir_mult_control_idx; omega
      rw [update_neq _ _ _ _ h_q_ne_ctrl_k]
      exact ih

/-- **Position-wise invariance through install at the controlIdx_j position.** -/
theorem applyNat_modmult_through_install_at_j
    (bits m j N c : Nat) (num_bits : Nat) (f : Nat → Bool) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1)
      (install_mult_bits_skip_j bits m j num_bits f) (sqir_mult_control_idx bits j)
      = Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1) f (sqir_mult_control_idx bits j) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx bits k < 2
            ∨ 2 + (2 * bits + 1) ≤ sqir_mult_control_idx bits k := by
        right; unfold sqir_mult_control_idx; omega
      have h_ne_flag : sqir_mult_control_idx bits k ≠ 1 := by
        unfold sqir_mult_control_idx; omega
      have h_ne_ctrl_j :
          sqir_mult_control_idx bits k ≠ sqir_mult_control_idx bits j :=
        fun heq => h_kj (sqir_mult_control_idx_injective bits k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N c
            (sqir_mult_control_idx bits j) (sqir_mult_control_idx bits k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [update_neq _ _ _ _ (Ne.symm h_ne_ctrl_j)]
      exact ih

/-- **Deliverable D — One-step workspace preservation.**

After applying the step gate, the read register is 0, the top carry is
false, the flag bit is false, and the multiplier control bit `j` is
preserved as `m.testBit j`. -/
theorem sqir_modmult_step_workspace
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    cuccaro_read_val bits 2
        (Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc)) = 0
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) (2 + 2 * bits) = false
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) 1 = false
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) (sqir_mult_control_idx bits j) = m.testBit j := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  rw [sqir_mult_input_F_eq_install_with_j bits m acc j hj hacc_lt]
  unfold sqir_modmult_step_gate
  -- gate_clean facts on F_j.
  have h_ctrl_out :
      sqir_mult_control_idx bits j < 2
        ∨ 2 + 2 * bits + 1 ≤ sqir_mult_control_idx bits j :=
    sqir_mult_control_idx_outside_modadd_workspace_form bits j
  have h_ctrl_ne_flag : sqir_mult_control_idx bits j ≠ 1 :=
    sqir_mult_control_idx_ne_flag bits j
  have h_ctrl_lt : sqir_mult_control_idx bits j < sqir_modmult_rev_anc bits :=
    sqir_mult_control_idx_lt_sqir_dim bits j hj
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  have ⟨_, _, h_rd, h_tc, h_fl, h_ctrl⟩ :=
    sqir_style_controlledModAddConst_gate_clean bits N ((a * 2^j) % N) acc
      (sqir_mult_control_idx bits j) (m.testBit j)
      hbits hN_pos hN hN2 hc_pos hacc h_ctrl_out h_ctrl_ne_flag h_ctrl_lt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cuccaro_read_val_through_install_mult bits m j N ((a * 2^j) % N) bits]
    exact h_rd
  · rw [applyNat_modmult_through_install_at_workspace bits m j N ((a * 2^j) % N) bits
          (2 + 2 * bits) _ (by omega)]
    exact h_tc
  · rw [applyNat_modmult_through_install_at_workspace bits m j N ((a * 2^j) % N) bits
          1 _ (by omega)]
    exact h_fl
  · rw [applyNat_modmult_through_install_at_j bits m j N ((a * 2^j) % N) bits]
    exact h_ctrl

/-! ## R7d^xxix-L-3.15d — q_start-parametric step workspace
       preservation.

q_start-parametric counterparts of the three install-bridge helpers
(`cuccaro_read_val_through_install_mult`, `applyNat_modmult_through_install_at_workspace`,
`applyNat_modmult_through_install_at_j`) and the headline
`sqir_modmult_step_workspace`.  Mirrors the L-3.15c structure but on
workspace conjuncts (read register, top carry, flag, control-bit
preservation). -/

/-- q_start-parametric: installing multiplier bits (other than the
j-th) outside the Cuccaro workspace preserves the decoded read/workspace
value.  Port of `cuccaro_read_val_through_install_mult` (line 958). -/
theorem cuccaro_read_val_through_install_mult_qstart
    (bits q_start m j N c flagPos : Nat) (num_bits : Nat) (f : Nat → Bool)
    (h_flag_lt_qstart : flagPos < q_start) :
    cuccaro_read_val bits q_start
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos)
          (install_mult_bits_skip_j_qstart bits q_start m j num_bits f))
      = cuccaro_read_val bits q_start
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos) f) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx_qstart bits q_start k < q_start
            ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start k :=
        sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start k
      have h_ne_flag : sqir_mult_control_idx_qstart bits q_start k ≠ flagPos :=
        sqir_mult_control_idx_ne_flag_qstart bits q_start k flagPos h_flag_lt_qstart
      have h_ne_ctrl_j :
          sqir_mult_control_idx_qstart bits q_start k
            ≠ sqir_mult_control_idx_qstart bits q_start j :=
        fun heq => h_kj (sqir_mult_control_idx_injective_qstart bits q_start k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos
            (sqir_mult_control_idx_qstart bits q_start k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [cuccaro_read_val_update_outside_workspace bits q_start
            (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k) _ h_out]
      exact ih

/-- q_start-parametric: install chain commutes with the step gate at
any single workspace position `q < q_start + 2 * bits + 1`.  Port of
`applyNat_modmult_through_install_at_workspace` (line 990). -/
theorem applyNat_modmult_through_install_at_workspace_qstart
    (bits q_start m j N c flagPos : Nat) (num_bits q : Nat) (f : Nat → Bool)
    (h_flag_lt_qstart : flagPos < q_start)
    (hq_ws : q < q_start + 2 * bits + 1) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
        (sqir_mult_control_idx_qstart bits q_start j) flagPos)
      (install_mult_bits_skip_j_qstart bits q_start m j num_bits f) q
      = Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
        (sqir_mult_control_idx_qstart bits q_start j) flagPos) f q := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx_qstart bits q_start k < q_start
            ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start k :=
        sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start k
      have h_ne_flag : sqir_mult_control_idx_qstart bits q_start k ≠ flagPos :=
        sqir_mult_control_idx_ne_flag_qstart bits q_start k flagPos h_flag_lt_qstart
      have h_ne_ctrl_j :
          sqir_mult_control_idx_qstart bits q_start k
            ≠ sqir_mult_control_idx_qstart bits q_start j :=
        fun heq => h_kj (sqir_mult_control_idx_injective_qstart bits q_start k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos
            (sqir_mult_control_idx_qstart bits q_start k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      have h_q_ne_ctrl_k : q ≠ sqir_mult_control_idx_qstart bits q_start k := by
        unfold sqir_mult_control_idx_qstart; omega
      rw [update_neq _ _ _ _ h_q_ne_ctrl_k]
      exact ih

/-- q_start-parametric: install chain commutes with the step gate at
the j-th multiplier control position.  Port of
`applyNat_modmult_through_install_at_j` (line 1022). -/
theorem applyNat_modmult_through_install_at_j_qstart
    (bits q_start m j N c flagPos : Nat) (num_bits : Nat) (f : Nat → Bool)
    (h_flag_lt_qstart : flagPos < q_start) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
        (sqir_mult_control_idx_qstart bits q_start j) flagPos)
      (install_mult_bits_skip_j_qstart bits q_start m j num_bits f)
        (sqir_mult_control_idx_qstart bits q_start j)
      = Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
        (sqir_mult_control_idx_qstart bits q_start j) flagPos) f
          (sqir_mult_control_idx_qstart bits q_start j) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx_qstart bits q_start k < q_start
            ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start k :=
        sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start k
      have h_ne_flag : sqir_mult_control_idx_qstart bits q_start k ≠ flagPos :=
        sqir_mult_control_idx_ne_flag_qstart bits q_start k flagPos h_flag_lt_qstart
      have h_ne_ctrl_j :
          sqir_mult_control_idx_qstart bits q_start k
            ≠ sqir_mult_control_idx_qstart bits q_start j :=
        fun heq => h_kj (sqir_mult_control_idx_injective_qstart bits q_start k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos
            (sqir_mult_control_idx_qstart bits q_start k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [update_neq _ _ _ _ (Ne.symm h_ne_ctrl_j)]
      exact ih

/-- **R7d^xxix-L-3.15d HEADLINE: q_start-parametric one-step
modular-multiplier workspace preservation.**

After applying `sqir_modmult_step_gate_qstart` to
`sqir_mult_input_F_qstart`:
1. the read register decodes to 0;
2. the top carry position (`q_start + 2 * bits`) is `false`;
3. `flagPos` is `false`;
4. the j-th multiplier control position holds `m.testBit j`.

Port of `sqir_modmult_step_workspace` (line 1055). -/
theorem sqir_modmult_step_workspace_qstart
    (bits q_start N a j m acc dim flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_read_val bits q_start
        (Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
          (sqir_mult_input_F_qstart bits q_start m acc)) = 0
    ∧ Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
          (sqir_mult_input_F_qstart bits q_start m acc) (q_start + 2 * bits) = false
    ∧ Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
          (sqir_mult_input_F_qstart bits q_start m acc) flagPos = false
    ∧ Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
          (sqir_mult_input_F_qstart bits q_start m acc)
          (sqir_mult_control_idx_qstart bits q_start j) = m.testBit j := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  rw [sqir_mult_input_F_eq_install_with_j_qstart bits q_start m acc j hj hacc_lt]
  unfold sqir_modmult_step_gate_qstart
  have h_ctrl_out :
      sqir_mult_control_idx_qstart bits q_start j < q_start
        ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start j :=
    sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start j
  have h_flag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos :=
    Or.inl h_flag_lt_qstart
  have h_ctrl_ne_flag : sqir_mult_control_idx_qstart bits q_start j ≠ flagPos :=
    sqir_mult_control_idx_ne_flag_qstart bits q_start j flagPos h_flag_lt_qstart
  have h_ctrl_lt_dim : sqir_mult_control_idx_qstart bits q_start j < dim :=
    sqir_mult_control_idx_lt_dim_qstart bits q_start j dim hj h_dim_covers_mult
  have h_flag_lt_dim : flagPos < dim := by omega
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  have ⟨_, _, h_rd, h_tc, h_fl, h_ctrl⟩ :=
    sqir_style_controlledModAddConst_gate_clean_qstart bits q_start N ((a * 2^j) % N) acc dim
      (sqir_mult_control_idx_qstart bits q_start j) flagPos (m.testBit j)
      hbits hN_pos hN hN2 hc_pos hacc h_ctrl_out h_flag_out h_ctrl_ne_flag
      h_workspace h_ctrl_lt_dim h_flag_lt_dim
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cuccaro_read_val_through_install_mult_qstart bits q_start m j N ((a * 2^j) % N) flagPos
          bits _ h_flag_lt_qstart]
    exact h_rd
  · rw [applyNat_modmult_through_install_at_workspace_qstart bits q_start m j N ((a * 2^j) % N)
          flagPos bits (q_start + 2 * bits) _ h_flag_lt_qstart (by omega)]
    exact h_tc
  · rw [applyNat_modmult_through_install_at_workspace_qstart bits q_start m j N ((a * 2^j) % N)
          flagPos bits flagPos _ h_flag_lt_qstart (by omega)]
    exact h_fl
  · rw [applyNat_modmult_through_install_at_j_qstart bits q_start m j N ((a * 2^j) % N) flagPos
          bits _ h_flag_lt_qstart]
    exact h_ctrl

/-! ## R7d^xxix-L-3.15e.1 — q_start-parametric prefix/const-gate
       definitions + sub-q_start input-state mini-helpers.

Smallest piece of the L-3.15e decomposition: provides the recursive
`sqir_modmult_prefix_gate_qstart` and the `bits`-fold
`sqir_modmult_const_gate_qstart` (plus zero/succ unfold lemmas), and
ports the trivial input-state flag-position helpers
`sqir_mult_input_flag_0_false` / `_flag_1_false` to the q_start
input.  No new arithmetic; consumed by subsequent L-3.15e.* sub-ticks. -/

/-- q_start-parametric input flag-0 mini-helper.  At position 0 of
`sqir_mult_input_F_qstart`, the bit is `false`, provided position 0
is below the Cuccaro workspace start.  Port of
`sqir_mult_input_flag_0_false` (line 143). -/
theorem sqir_mult_input_flag_0_false_qstart
    (bits q_start m acc : Nat) (h_lt : 0 < q_start) :
    sqir_mult_input_F_qstart bits q_start m acc 0 = false := by
  unfold sqir_mult_input_F_qstart
  rw [if_pos (by omega : (0 : Nat) < q_start + 2 * bits + 1)]
  unfold cuccaro_input_F
  rw [if_pos h_lt]

/-- q_start-parametric input flag-1 mini-helper.  At position 1 of
`sqir_mult_input_F_qstart`, the bit is `false`, provided position 1
is below the Cuccaro workspace start.  Port of
`sqir_mult_input_flag_1_false` (line 151). -/
theorem sqir_mult_input_flag_1_false_qstart
    (bits q_start m acc : Nat) (h_lt : 1 < q_start) :
    sqir_mult_input_F_qstart bits q_start m acc 1 = false := by
  unfold sqir_mult_input_F_qstart
  rw [if_pos (by omega : (1 : Nat) < q_start + 2 * bits + 1)]
  unfold cuccaro_input_F
  rw [if_pos h_lt]

/-- q_start-parametric prefix gate at 0 windows is the identity. -/
theorem sqir_modmult_prefix_gate_qstart_zero_eq_I
    (bits q_start N a flagPos : Nat) :
    sqir_modmult_prefix_gate_qstart bits q_start N a flagPos 0 = Gate.I := rfl

/-- q_start-parametric prefix gate at `k + 1` windows. -/
theorem sqir_modmult_prefix_gate_qstart_succ_eq
    (bits q_start N a flagPos k : Nat) :
    sqir_modmult_prefix_gate_qstart bits q_start N a flagPos (k + 1)
      = seq (sqir_modmult_prefix_gate_qstart bits q_start N a flagPos k)
            (sqir_modmult_step_gate_qstart bits q_start N a k flagPos) := rfl

/-! ## R7d^xxix-L-3.15e.2 — q_start-parametric step-gate position
       helpers (above-layout / flag0 / carry-in restored).

Three position-level helpers needed by the eventual
`sqir_modmult_step_state_eq_qstart` proof.  The above-layout and
flag0 cases route through a shared `_step_at_untouched_pos_qstart`
helper; the carry-in case routes through the
`sqir_style_controlledModAddConst_gate` carry-in chain. -/

/-- q_start-parametric: step gate doesn't touch positions outside
its support.  At any `q` outside the workspace, distinct from
`flagPos` and the j-th multiplier control position, the gate's
output equals the input's value.  Port of
`sqir_modmult_step_at_untouched_pos` (line 1712). -/
theorem sqir_modmult_step_at_untouched_pos_qstart
    (bits q_start N a j flagPos m acc q : Nat) (hj : j < bits)
    (h_input : sqir_mult_input_F_qstart bits q_start m acc q = false)
    (h_q_out : q < q_start ∨ q_start + 2 * bits + 1 ≤ q)
    (h_q_ne_flag : q ≠ flagPos)
    (h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx_qstart bits q_start j) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc) q = false := by
  have h_in_eq : update (sqir_mult_input_F_qstart bits q_start m acc) q false
                = sqir_mult_input_F_qstart bits q_start m acc := by
    rw [show (false : Bool) = sqir_mult_input_F_qstart bits q_start m acc q from h_input.symm]
    exact update_self _ q
  unfold sqir_modmult_step_gate_qstart
  have h_commute := sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart
    bits q_start N ((a * 2^j) % N)
    (sqir_mult_control_idx_qstart bits q_start j) flagPos q false
    (sqir_mult_input_F_qstart bits q_start m acc)
    h_q_out h_q_ne_flag h_q_ne_ctrl_j
  rw [h_in_eq] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [update_eq] at h_at_q
  exact h_at_q

/-- q_start-parametric: step gate's output at flag-0 position is
`false`.  Port of `sqir_modmult_step_flag0_false` (line 1734). -/
theorem sqir_modmult_step_flag0_false_qstart
    (bits q_start N a j flagPos m acc : Nat) (hbits : 1 ≤ bits) (hj : j < bits)
    (h_qstart_ge_2 : 2 ≤ q_start)
    (h_flag_ne_0 : (0 : Nat) ≠ flagPos) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc) 0 = false := by
  apply sqir_modmult_step_at_untouched_pos_qstart bits q_start N a j flagPos m acc 0 hj
  · exact sqir_mult_input_flag_0_false_qstart bits q_start m acc (by omega)
  · exact Or.inl (by omega)
  · exact h_flag_ne_0
  · have h := sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start j
    intro h_eq; unfold sqir_mult_control_idx_qstart at h_eq; omega

/-- q_start-parametric: step gate's output above the multiplier
register (for `q ≥ q_start + 2 * bits + 1 + bits`) is `false`.  Port
of `sqir_modmult_step_above_layout_false` (line 1747). -/
theorem sqir_modmult_step_above_layout_false_qstart
    (bits q_start N a j flagPos m acc q : Nat) (hbits : 1 ≤ bits) (hj : j < bits)
    (hq : q ≥ q_start + 2 * bits + 1 + bits)
    (h_flag_lt_qstart : flagPos < q_start) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc) q = false := by
  apply sqir_modmult_step_at_untouched_pos_qstart bits q_start N a j flagPos m acc q hj
  · unfold sqir_mult_input_F_qstart
    rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1)]
    rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1 + bits)]
  · exact Or.inr (by omega)
  · intro heq; omega
  · intro h_eq
    have h := sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start j
    unfold sqir_mult_control_idx_qstart at h_eq
    omega

/-! ### Carry-in restored chain (port of CuccaroSQIRDirtyFlag.lean
clean-candidate carry-in + this file's controlled wrapper). -/

/-- q_start-parametric: the uncontrolled clean modular-add candidate
restores the carry-in to `false`.  Port of
`sqir_style_modAddConst_clean_candidate_carry_in_restored`
(line 1637). -/
theorem sqir_style_modAddConst_clean_candidate_carry_in_restored_qstart
    (bits q_start N c x flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_modAddConst_clean_candidate bits q_start N c flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos false) q_start = false := by
  show Gate.applyNat
      (seq (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
        (seq (sqir_style_compareConst_candidate bits q_start c flagPos) (Gate.X flagPos)))
      (update (cuccaro_input_F q_start false 0 x) flagPos false) q_start = false
  simp only [Gate.applyNat_seq, Gate.applyNat_X]
  have h_qs_ne_flag : (q_start : Nat) ≠ flagPos := by
    rcases hflag_out with hl | hr
    · omega
    · omega
  rw [update_neq _ _ _ _ h_qs_ne_flag]
  have h_qs_in_ws_lo : q_start ≤ q_start := le_refl _
  have h_qs_in_ws_hi : q_start < q_start + 2 * bits + 1 := by omega
  rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits q_start c flagPos
        _ hflag_out q_start h_qs_in_ws_lo h_qs_in_ws_hi]
  have h_flag_distinct : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2 := by
    intros j _ heq
    rcases hflag_out with hl | hr
    · omega
    · omega
  exact sqir_style_modAddConst_dirtyFlag_carry_in_restored_general bits q_start N c x flagPos
    hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out

/-- q_start-parametric: controlled candidate carry-in restored.
Dispatches on `control`.  Port of
`sqir_style_controlledModAddConst_candidate_carry_in_restored`
(line 1657). -/
theorem sqir_style_controlledModAddConst_candidate_carry_in_restored_qstart
    (bits q_start N c x controlIdx flagPos : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
        (update (cuccaro_input_F q_start false 0 x) controlIdx control) q_start = false := by
  have h_ctrl_ne_qs : controlIdx ≠ q_start := by
    rcases hcontrol_out with h | h
    · omega
    · omega
  cases control with
  | false =>
    rw [sqir_style_controlledModAddConst_candidate_control_false_state_eq_qstart
          bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
          hcontrol_out hflag_out hcontrol_ne_flag]
    rw [update_neq _ _ _ _ (Ne.symm h_ctrl_ne_qs)]
    exact cuccaro_input_F_at_c_in q_start false 0 x
  | true =>
    rw [sqir_style_controlledModAddConst_candidate_control_true_state_eq_qstart
          bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
          hcontrol_out hflag_out hcontrol_ne_flag]
    rw [update_neq _ _ _ _ (Ne.symm h_ctrl_ne_qs)]
    exact sqir_style_modAddConst_clean_candidate_carry_in_restored_qstart bits q_start N c x
      flagPos hbits hN_pos hN hN2 hc hx hflag_out

/-- q_start-parametric: wrapper-level controlled mod-add carry-in
restored.  Adds the `c = 0` identity case.  Port of
`sqir_style_controlledModAddConst_gate_carry_in_restored` (line 1684). -/
theorem sqir_style_controlledModAddConst_gate_carry_in_restored_qstart
    (bits q_start N c x controlIdx flagPos : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
        (update (cuccaro_input_F q_start false 0 x) controlIdx control) q_start = false := by
  unfold sqir_style_controlledModAddConst_gate
  have h_ctrl_ne_qs : controlIdx ≠ q_start := by
    rcases hcontrol_out with h | h
    · omega
    · omega
  by_cases hc0 : c = 0
  · simp only [hc0, if_true, Gate.applyNat_I]
    rw [update_neq _ _ _ _ (Ne.symm h_ctrl_ne_qs)]
    exact cuccaro_input_F_at_c_in q_start false 0 x
  · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc0
    simp only [hc0, if_false]
    exact sqir_style_controlledModAddConst_candidate_carry_in_restored_qstart bits q_start N c x
      controlIdx flagPos control hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hflag_out
      hcontrol_ne_flag

/-! ### Function-level commute of step gate with install (q_start). -/

/-- q_start-parametric: the controlled mod-add wrapper gate commutes
with the entire install stack.  Port of
`sqir_style_controlledModAddConst_gate_commute_install` (line 1362). -/
theorem sqir_style_controlledModAddConst_gate_commute_install_qstart
    (bits q_start m j N c flagPos num_bits : Nat) (f : Nat → Bool)
    (h_flag_lt_qstart : flagPos < q_start) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
        (sqir_mult_control_idx_qstart bits q_start j) flagPos)
      (install_mult_bits_skip_j_qstart bits q_start m j num_bits f)
      = install_mult_bits_skip_j_qstart bits q_start m j num_bits
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos) f) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    by_cases h_kj : k = j
    · have h_lhs_eq : install_mult_bits_skip_j_qstart bits q_start m j (k+1) f
                    = install_mult_bits_skip_j_qstart bits q_start m j k f := by
        show (if k = j then install_mult_bits_skip_j_qstart bits q_start m j k f
              else update (install_mult_bits_skip_j_qstart bits q_start m j k f)
                          (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k))
            = install_mult_bits_skip_j_qstart bits q_start m j k f
        rw [if_pos h_kj]
      have h_rhs_eq : install_mult_bits_skip_j_qstart bits q_start m j (k+1)
                      (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
                        (sqir_mult_control_idx_qstart bits q_start j) flagPos) f)
                    = install_mult_bits_skip_j_qstart bits q_start m j k
                      (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
                        (sqir_mult_control_idx_qstart bits q_start j) flagPos) f) := by
        show (if k = j
              then install_mult_bits_skip_j_qstart bits q_start m j k
                    (Gate.applyNat _ f)
              else update (install_mult_bits_skip_j_qstart bits q_start m j k
                            (Gate.applyNat _ f))
                          (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k))
            = install_mult_bits_skip_j_qstart bits q_start m j k
              (Gate.applyNat _ f)
        rw [if_pos h_kj]
      rw [h_lhs_eq, h_rhs_eq]
      exact ih
    · have h_out : sqir_mult_control_idx_qstart bits q_start k < q_start
            ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start k :=
        sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start k
      have h_ne_flag : sqir_mult_control_idx_qstart bits q_start k ≠ flagPos :=
        sqir_mult_control_idx_ne_flag_qstart bits q_start k flagPos h_flag_lt_qstart
      have h_ne_ctrl_j :
          sqir_mult_control_idx_qstart bits q_start k
            ≠ sqir_mult_control_idx_qstart bits q_start j :=
        fun heq => h_kj (sqir_mult_control_idx_injective_qstart bits q_start k j heq)
      have h_lhs_eq : install_mult_bits_skip_j_qstart bits q_start m j (k+1) f
                    = update (install_mult_bits_skip_j_qstart bits q_start m j k f)
                        (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k) := by
        show (if k = j then install_mult_bits_skip_j_qstart bits q_start m j k f
              else update (install_mult_bits_skip_j_qstart bits q_start m j k f)
                          (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k))
            = update (install_mult_bits_skip_j_qstart bits q_start m j k f)
                (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k)
        rw [if_neg h_kj]
      have h_rhs_eq : install_mult_bits_skip_j_qstart bits q_start m j (k+1)
                      (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
                        (sqir_mult_control_idx_qstart bits q_start j) flagPos) f)
                    = update (install_mult_bits_skip_j_qstart bits q_start m j k
                        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
                          (sqir_mult_control_idx_qstart bits q_start j) flagPos) f))
                        (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k) := by
        show (if k = j
              then install_mult_bits_skip_j_qstart bits q_start m j k (Gate.applyNat _ f)
              else update (install_mult_bits_skip_j_qstart bits q_start m j k (Gate.applyNat _ f))
                          (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k))
            = update (install_mult_bits_skip_j_qstart bits q_start m j k (Gate.applyNat _ f))
                (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k)
        rw [if_neg h_kj]
      rw [h_lhs_eq, h_rhs_eq]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos
            (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k)
            (install_mult_bits_skip_j_qstart bits q_start m j k f)
            h_out h_ne_flag h_ne_ctrl_j]
      rw [ih]

/-- q_start-parametric: step gate's output at the carry-in position
(`q_start`) is `false`.  Port of `sqir_modmult_step_carry_in_restored`
(line 1764). -/
theorem sqir_modmult_step_carry_in_restored_qstart
    (bits q_start N a j flagPos m acc : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N)
    (h_flag_lt_qstart : flagPos < q_start) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc) q_start = false := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  rw [sqir_mult_input_F_eq_install_with_j_qstart bits q_start m acc j hj hacc_lt]
  unfold sqir_modmult_step_gate_qstart
  rw [sqir_style_controlledModAddConst_gate_commute_install_qstart bits q_start m j N
        ((a * 2^j) % N) flagPos bits _ h_flag_lt_qstart]
  rw [install_mult_bits_skip_j_at_workspace_eq_qstart bits q_start m j bits _ q_start (by omega)]
  have h_ctrl_out :
      sqir_mult_control_idx_qstart bits q_start j < q_start
        ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start j :=
    sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start j
  have h_flag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos :=
    Or.inl h_flag_lt_qstart
  have h_ctrl_ne_flag : sqir_mult_control_idx_qstart bits q_start j ≠ flagPos :=
    sqir_mult_control_idx_ne_flag_qstart bits q_start j flagPos h_flag_lt_qstart
  exact sqir_style_controlledModAddConst_gate_carry_in_restored_qstart bits q_start N
    ((a * 2^j) % N) acc (sqir_mult_control_idx_qstart bits q_start j) flagPos (m.testBit j)
    hbits hN_pos hN hN2 (Nat.mod_lt _ hN_pos) hacc h_ctrl_out h_flag_out h_ctrl_ne_flag

end FormalRV.BQAlgo
