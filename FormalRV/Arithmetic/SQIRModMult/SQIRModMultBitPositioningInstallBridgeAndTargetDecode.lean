import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultEncoding
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSpec
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultQStart
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultFamily
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSizing
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultBitPositioningControlIdxAndCommute

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
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

end FormalRV.BQAlgo
