import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.ModMult.Internal.Encoding
import FormalRV.Arithmetic.ModMult.Internal.Spec
import FormalRV.Arithmetic.ModMult.Internal.QStart
import FormalRV.Arithmetic.ModMult.Internal.Family
import FormalRV.Arithmetic.ModMult.Internal.BitPositioning
import FormalRV.Arithmetic.ModMult.Internal.PrefixInvariant.OneStep

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
/-! ## Tick 76 — Carry-in restoration chain. -/

/-- **Clean candidate carry-in (`q_start = 2`) restored to `false`.**

Chains through `dirtyFlag → compareConst c → X(1)`:
- `dirtyFlag` restores carry-in via `dirtyFlag_carry_in_restored_general`.
- `compareConst c` preserves all workspace positions via
  `compareConst_candidate_workspace_restored_at_general`.
- `X(1)` doesn't touch position 2 (since 2 ≠ 1). -/
theorem style_modAddConst_clean_candidate_carry_in_restored
    (bits N c x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N) :
    Gate.applyNat (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
        (update (cuccaro_input_F 2 false 0 x) 1 false) 2 = false := by
  show Gate.applyNat
      (seq (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
        (seq (sqir_style_compareConst_candidate bits 2 c 1) (Gate.X 1)))
      (update (cuccaro_input_F 2 false 0 x) 1 false) 2 = false
  simp only [Gate.applyNat_seq, Gate.applyNat_X]
  rw [update_neq _ _ _ _ (by decide : (2 : Nat) ≠ 1)]
  rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 c 1
        _ (Or.inl (by omega)) 2 (by omega) (by omega)]
  exact sqir_style_modAddConst_dirtyFlag_carry_in_restored_general bits 2 N c x 1
    hbits hN_pos hN hN2 hx hc (fun j _ => by omega) (Or.inl (by omega))

/-- **Controlled candidate carry-in restored.** Dispatches on `control`:
- `control = false`: identity (via `control_false_state_eq`).
- `control = true`: chains through `clean_candidate_carry_in_restored`. -/
theorem style_controlledModAddConst_candidate_carry_in_restored
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
        (update (cuccaro_input_F 2 false 0 x) controlIdx control) 2 = false := by
  have h_ctrl_ne_2 : controlIdx ≠ 2 := by
    rcases hcontrol_out with h | h
    · omega
    · omega
  cases control with
  | false =>
    rw [sqir_style_controlledModAddConst_candidate_control_false_state_eq bits N c x controlIdx
          hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag]
    rw [update_neq _ _ _ _ (Ne.symm h_ctrl_ne_2)]
    exact cuccaro_input_F_at_c_in 2 false 0 x
  | true =>
    rw [sqir_style_controlledModAddConst_candidate_control_true_state_eq bits N c x controlIdx
          hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag]
    rw [update_neq _ _ _ _ (Ne.symm h_ctrl_ne_2)]
    exact style_modAddConst_clean_candidate_carry_in_restored bits N c x
      hbits hN_pos hN hN2 hc hx

/-- **Wrapper-level controlled mod-add carry-in restored.** Adds the
`c = 0` identity case to the candidate version. -/
theorem style_controlledModAddConst_gate_carry_in_restored
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
        (update (cuccaro_input_F 2 false 0 x) controlIdx control) 2 = false := by
  unfold sqir_style_controlledModAddConst_gate
  by_cases hc0 : c = 0
  · simp only [hc0, if_true, Gate.applyNat_I]
    have h_ctrl_ne_2 : controlIdx ≠ 2 := by
      rcases hcontrol_out with h | h
      · omega
      · omega
    rw [update_neq _ _ _ _ (Ne.symm h_ctrl_ne_2)]
    exact cuccaro_input_F_at_c_in 2 false 0 x
  · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc0
    simp only [hc0, if_false]
    exact style_controlledModAddConst_candidate_carry_in_restored bits N c x controlIdx control
      hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag

/-! ## Tick 76 — Step gate position-wise facts. -/

/-- **Generic helper — step gate doesn't touch positions outside its
support.**  At any `q` outside workspace, distinct from flag and
controlIdx_j, the gate's output equals the input's value (via
commute + update_self). -/
theorem modmult_step_at_untouched_pos
    (bits N a j m acc q : Nat) (hj : j < bits)
    (h_input : modmult_input_F bits m acc q = false)
    (h_q_out : q < 2 ∨ 2 + (2 * bits + 1) ≤ q)
    (h_q_ne_flag : q ≠ 1)
    (h_q_ne_ctrl_j : q ≠ mult_control_idx bits j) :
    Gate.applyNat (modmult_step_gate bits N a j)
        (modmult_input_F bits m acc) q = false := by
  have h_in_eq : update (modmult_input_F bits m acc) q false
                = modmult_input_F bits m acc := by
    rw [show (false : Bool) = modmult_input_F bits m acc q from h_input.symm]
    exact update_self _ q
  have h_commute := style_controlledModAddConst_gate_commute_update_outside_fun bits N
    ((a * 2^j) % N) (mult_control_idx bits j) q false (modmult_input_F bits m acc)
    h_q_out h_q_ne_flag h_q_ne_ctrl_j
  -- h_commute : applyNat (controlled gate) (update input q false) = update (applyNat (controlled gate) input) q false
  rw [h_in_eq] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [update_eq] at h_at_q
  exact h_at_q

/-- **Step gate's output at flag bit 0 is `false`.** -/
theorem modmult_step_flag0_false
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits) (hj : j < bits) :
    Gate.applyNat (modmult_step_gate bits N a j)
        (modmult_input_F bits m acc) 0 = false := by
  apply modmult_step_at_untouched_pos bits N a j m acc 0 hj
  · exact mult_input_flag_0_false bits m acc
  · exact Or.inl (by omega)
  · omega
  · have h := mult_control_idx_outside_modadd_workspace_form bits j
    intro h_eq; unfold mult_control_idx at h_eq; omega

/-- **Step gate's output above the multiplier register is `false`.**
For `q ≥ 2 + 2 * bits + 1 + bits`. -/
theorem modmult_step_above_layout_false
    (bits N a j m acc q : Nat) (hbits : 1 ≤ bits) (hj : j < bits)
    (hq : q ≥ 2 + 2 * bits + 1 + bits) :
    Gate.applyNat (modmult_step_gate bits N a j)
        (modmult_input_F bits m acc) q = false := by
  apply modmult_step_at_untouched_pos bits N a j m acc q hj
  · unfold modmult_input_F
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]
  · exact Or.inr (by omega)
  · omega
  · intro h_eq
    have h := mult_control_idx_outside_modadd_workspace_form bits j
    unfold mult_control_idx at h_eq
    omega

/-- **Step gate's output at carry-in (position 2) is `false`.** -/
theorem modmult_step_carry_in_restored
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    Gate.applyNat (modmult_step_gate bits N a j)
        (modmult_input_F bits m acc) 2 = false := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  rw [mult_input_F_eq_install_with_j bits m acc j hj hacc_lt]
  unfold modmult_step_gate
  rw [style_controlledModAddConst_gate_commute_install bits m j N
        ((a * 2^j) % N) bits _]
  rw [install_mult_bits_skip_j_at_workspace_eq bits m j bits _ 2 (by omega)]
  exact style_controlledModAddConst_gate_carry_in_restored bits N
    ((a * 2^j) % N) acc (mult_control_idx bits j) (m.testBit j)
    hbits hN_pos hN hN2 (Nat.mod_lt _ hN_pos) hacc
    (mult_control_idx_outside_modadd_workspace_form bits j)
    (mult_control_idx_ne_flag bits j)

/-- **Step gate's output at target bit `i` equals `acc'.testBit i`.**

Uses the per-bit converse `cuccaro_target_val_eq_implies_bits_match`
plus the Tick 74 `modmult_step_target_decode`. -/
theorem modmult_step_target_bit
    (bits N a j m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits) :
    Gate.applyNat (modmult_step_gate bits N a j)
        (modmult_input_F bits m acc) (2 + 2 * i + 1)
      = (if m.testBit j then (acc + (a * 2^j) % N) % N else acc).testBit i := by
  set acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc with hacc'_def
  have hacc'_lt_N : acc' < N := by
    rw [hacc'_def]
    by_cases h : m.testBit j
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact hacc
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  have h_tgt := modmult_step_target_decode bits N a j m acc hbits hN_pos hN hN2 hj hacc
  exact cuccaro_target_val_eq_implies_bits_match bits 2 acc' _ hacc'_lt h_tgt i hi

/-- **Step gate's output at read bit `i` is `false`.** -/
theorem modmult_step_read_bit
    (bits N a j m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits) :
    Gate.applyNat (modmult_step_gate bits N a j)
        (modmult_input_F bits m acc) (2 + 2 * i + 2) = false := by
  have h_rd := (modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc).1
  have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
  have := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd i hi
  rw [this, Nat.zero_testBit]

/-! ## R7d^xxix-L-3.15e.3 — q_start-parametric step-gate position
       helpers (target-bit / read-bit / all-control-bits preserved).

The three remaining per-position helpers needed by the eventual
`modmult_step_state_eq_qstart` proof.  Each is a thin port of
its hard-coded counterpart, consuming previously-closed L-3.15c/d/e
infrastructure plus the q_start-parametric decoders
`cuccaro_target_val_eq_implies_bits_match` and
`cuccaro_read_val_eq_implies_bits_match` (already q_start-parametric
above in this file). -/

/-- q_start-parametric: step gate's output at target/b-register
position `q_start + 2 * i + 1` decodes the i-th bit of the advanced
accumulator.  Port of `modmult_step_target_bit` (line 2063). -/
theorem modmult_step_target_bit_qstart
    (bits q_start N a j flagPos m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (modmult_step_gate_qstart bits q_start N a j flagPos)
        (mult_input_F_qstart bits q_start m acc) (q_start + 2 * i + 1)
      = (if m.testBit j then (acc + (a * 2^j) % N) % N else acc).testBit i := by
  set acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc with hacc'_def
  have hacc'_lt_N : acc' < N := by
    rw [hacc'_def]
    by_cases h : m.testBit j
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact hacc
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  have h_tgt := modmult_step_target_decode_qstart bits q_start N a j m acc dim flagPos
    hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart h_workspace h_dim_covers_mult
  exact cuccaro_target_val_eq_implies_bits_match bits q_start acc' _ hacc'_lt h_tgt i hi

/-- q_start-parametric: step gate's output at read/a-register
position `q_start + 2 * i + 2` is `false`.  Port of
`modmult_step_read_bit` (line 2161). -/
theorem modmult_step_read_bit_qstart
    (bits q_start N a j flagPos m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (modmult_step_gate_qstart bits q_start N a j flagPos)
        (mult_input_F_qstart bits q_start m acc) (q_start + 2 * i + 2) = false := by
  have h_rd := (modmult_step_workspace_qstart bits q_start N a j m acc dim flagPos
    hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart h_workspace h_dim_covers_mult).1
  have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
  have := cuccaro_read_val_eq_implies_bits_match bits q_start 0 _ h_zero_lt h_rd i hi
  rw [this, Nat.zero_testBit]

/-- q_start-parametric: step gate preserves every multiplier control
bit `k < bits` as `m.testBit k`.  Port of
`modmult_step_preserves_all_control_bits` (line 1717). -/
theorem modmult_step_preserves_all_control_bits_qstart
    (bits q_start N a m acc j k flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hj : j < bits) (hk : k < bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (modmult_step_gate_qstart bits q_start N a j flagPos)
        (mult_input_F_qstart bits q_start m acc)
          (mult_control_idx_qstart bits q_start k)
      = m.testBit k := by
  by_cases h_kj : k = j
  · rw [h_kj]
    have ⟨_, _, _, h_ctrl⟩ :=
      modmult_step_workspace_qstart bits q_start N a j m acc dim flagPos
        hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart h_workspace h_dim_covers_mult
    exact h_ctrl
  · have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
    rw [mult_input_F_eq_install_with_j_qstart bits q_start m acc j hj hacc_lt]
    unfold modmult_step_gate_qstart
    rw [style_controlledModAddConst_gate_commute_install_qstart bits q_start m j N
          ((a * 2^j) % N) flagPos bits _ h_flag_lt_qstart]
    exact install_mult_bits_skip_j_at_mult_k_eq_qstart bits q_start m j bits k _ hk h_kj

end FormalRV.BQAlgo
