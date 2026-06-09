import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultEncoding
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSpec
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultQStart
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultFamily
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSizing
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultBitPositioningInstallBridgeAndTargetDecode

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
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

end FormalRV.BQAlgo
