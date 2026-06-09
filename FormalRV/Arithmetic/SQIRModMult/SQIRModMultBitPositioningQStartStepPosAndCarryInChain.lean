import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultEncoding
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSpec
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultQStart
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultFamily
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSizing
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultBitPositioningQStartTargetAndWorkspacePorts

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
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
