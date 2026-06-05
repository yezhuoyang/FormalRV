import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultDefinitions
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultBitPositioning

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Tick 74 — Deliverable F: Prefix invariant starter. -/

/-- **Prefix invariant — base case (`k = 0`).**

The 0-step prefix gate is identity, so the target register is just the
encoded `acc = 0`. -/
theorem sqir_modmult_prefix_target_decode_zero
    (bits N a m : Nat) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_prefix_gate bits N a 0) (sqir_mult_input_F bits m 0))
      = sqir_modmult_acc_spec N a m 0 := by
  rw [sqir_modmult_acc_spec_zero, sqir_modmult_prefix_gate]
  rw [Gate.applyNat_I]
  exact sqir_mult_input_target_decode bits m 0 (Nat.two_pow_pos bits)

/-! ## Tick 75 — Deliverable A: All control bits preserved by one step. -/

/-- **Function-level commute of step gate with install.**

The controlled mod-add wrapper gate commutes with the entire install
stack, because each install update is at `controlIdx_k` for `k ≠ j`
(by construction of `install_mult_bits_skip_j`), which is outside the
gate's support. -/
theorem sqir_style_controlledModAddConst_gate_commute_install
    (bits m j N c num_bits : Nat) (f : Nat → Bool) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1)
      (install_mult_bits_skip_j bits m j num_bits f)
      = install_mult_bits_skip_j bits m j num_bits
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1) f) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    by_cases h_kj : k = j
    · have h_lhs_eq : install_mult_bits_skip_j bits m j (k+1) f
                    = install_mult_bits_skip_j bits m j k f := by
        show (if k = j then install_mult_bits_skip_j bits m j k f
              else update (install_mult_bits_skip_j bits m j k f)
                          (sqir_mult_control_idx bits k) (m.testBit k))
            = install_mult_bits_skip_j bits m j k f
        rw [if_pos h_kj]
      have h_rhs_eq : install_mult_bits_skip_j bits m j (k+1)
                      (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
                        (sqir_mult_control_idx bits j) 1) f)
                    = install_mult_bits_skip_j bits m j k
                      (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
                        (sqir_mult_control_idx bits j) 1) f) := by
        show (if k = j
              then install_mult_bits_skip_j bits m j k
                    (Gate.applyNat _ f)
              else update (install_mult_bits_skip_j bits m j k
                            (Gate.applyNat _ f))
                          (sqir_mult_control_idx bits k) (m.testBit k))
            = install_mult_bits_skip_j bits m j k
              (Gate.applyNat _ f)
        rw [if_pos h_kj]
      rw [h_lhs_eq, h_rhs_eq]
      exact ih
    · have h_out : sqir_mult_control_idx bits k < 2
            ∨ 2 + (2 * bits + 1) ≤ sqir_mult_control_idx bits k := by
        right; unfold sqir_mult_control_idx; omega
      have h_ne_flag : sqir_mult_control_idx bits k ≠ 1 := by
        unfold sqir_mult_control_idx; omega
      have h_ne_ctrl_j :
          sqir_mult_control_idx bits k ≠ sqir_mult_control_idx bits j :=
        fun heq => h_kj (sqir_mult_control_idx_injective bits k j heq)
      have h_lhs_eq : install_mult_bits_skip_j bits m j (k+1) f
                    = update (install_mult_bits_skip_j bits m j k f)
                        (sqir_mult_control_idx bits k) (m.testBit k) := by
        show (if k = j then install_mult_bits_skip_j bits m j k f
              else update (install_mult_bits_skip_j bits m j k f)
                          (sqir_mult_control_idx bits k) (m.testBit k))
            = update (install_mult_bits_skip_j bits m j k f)
                (sqir_mult_control_idx bits k) (m.testBit k)
        rw [if_neg h_kj]
      have h_rhs_eq : install_mult_bits_skip_j bits m j (k+1)
                      (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
                        (sqir_mult_control_idx bits j) 1) f)
                    = update (install_mult_bits_skip_j bits m j k
                        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
                          (sqir_mult_control_idx bits j) 1) f))
                        (sqir_mult_control_idx bits k) (m.testBit k) := by
        show (if k = j
              then install_mult_bits_skip_j bits m j k (Gate.applyNat _ f)
              else update (install_mult_bits_skip_j bits m j k (Gate.applyNat _ f))
                          (sqir_mult_control_idx bits k) (m.testBit k))
            = update (install_mult_bits_skip_j bits m j k (Gate.applyNat _ f))
                (sqir_mult_control_idx bits k) (m.testBit k)
        rw [if_neg h_kj]
      rw [h_lhs_eq, h_rhs_eq]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N c
            (sqir_mult_control_idx bits j) (sqir_mult_control_idx bits k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [ih]

/-- **Deliverable A — All control bits preserved by one step.**

The one-step gate `sqir_modmult_step_gate bits N a j` preserves every
multiplier control bit `k < bits` as `m.testBit k`.  This generalizes
Tick 74's Deliverable D from `k = j` to all `k < bits`. -/
theorem sqir_modmult_step_preserves_all_control_bits
    (bits N a m acc j k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hj : j < bits) (hk : k < bits) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) (sqir_mult_control_idx bits k)
      = m.testBit k := by
  by_cases h_kj : k = j
  · rw [h_kj]
    have ⟨_, _, _, h_ctrl⟩ :=
      sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc
    exact h_ctrl
  · have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
    rw [sqir_mult_input_F_eq_install_with_j bits m acc j hj hacc_lt]
    unfold sqir_modmult_step_gate
    rw [sqir_style_controlledModAddConst_gate_commute_install bits m j N
          ((a * 2^j) % N) bits _]
    exact install_mult_bits_skip_j_at_mult_k_eq bits m j bits k _ hk h_kj

/-! ## Tick 75 — Converse target/read-value extraction (utility). -/

/-- **Converse to `cuccaro_target_val_eq_sum_when_bits_match`.**

For `S < 2^bits`, if `cuccaro_target_val bits q_start f = S`, then each
target bit `i < bits` matches `S.testBit i`.  By uniqueness of binary
representation.  Useful for deducing per-bit info from a target_val
equality.

This is a forward-looking utility lemma; in Tick 75 it is not yet
consumed by `sqir_modmult_step_state_eq` (deferred to Tick 76). -/
theorem cuccaro_target_val_eq_implies_bits_match
    (bits q_start S : Nat) (f : Nat → Bool)
    (hS : S < 2^bits) (h : cuccaro_target_val bits q_start f = S) :
    ∀ i, i < bits → f (q_start + 2 * i + 1) = S.testBit i := by
  induction bits generalizing S with
  | zero => intros i hi; omega
  | succ n ih =>
    intro i hi
    have hTn_lt : cuccaro_target_val n q_start f < 2^n :=
      cuccaro_target_val_lt n q_start f
    have h_unfold : cuccaro_target_val n q_start f
                  + (if f (q_start + 2 * n + 1) then 2^n else 0) = S := h
    by_cases hi_eq : i = n
    · subst hi_eq
      by_cases hvn : f (q_start + 2 * i + 1) = true
      · rw [if_pos hvn] at h_unfold
        rw [hvn]
        have hS_eq : S = 2^i + cuccaro_target_val i q_start f := by omega
        rw [hS_eq, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hTn_lt]
        rfl
      · have hvn_f : f (q_start + 2 * i + 1) = false := by
          cases hh : f (q_start + 2 * i + 1)
          · rfl
          · exact absurd hh hvn
        rw [if_neg hvn] at h_unfold
        rw [hvn_f]
        have h_eq : S = cuccaro_target_val i q_start f := by omega
        rw [h_eq]
        exact (Nat.testBit_lt_two_pow hTn_lt).symm
    · have hi_lt_n : i < n := by omega
      have h_ih : f (q_start + 2 * i + 1) = (cuccaro_target_val n q_start f).testBit i :=
        ih (cuccaro_target_val n q_start f) hTn_lt rfl i hi_lt_n
      rw [h_ih]
      by_cases hvn : f (q_start + 2 * n + 1) = true
      · rw [if_pos hvn] at h_unfold
        have hS_eq : S = 2^n + cuccaro_target_val n q_start f := by omega
        rw [hS_eq, Nat.testBit_two_pow_add_gt hi_lt_n]
      · rw [if_neg hvn] at h_unfold
        have h_eq : S = cuccaro_target_val n q_start f := by omega
        rw [h_eq]

/-- **Converse to `cuccaro_read_val_eq_sum_when_bits_match`.** -/
theorem cuccaro_read_val_eq_implies_bits_match
    (bits q_start S : Nat) (f : Nat → Bool)
    (hS : S < 2^bits) (h : cuccaro_read_val bits q_start f = S) :
    ∀ i, i < bits → f (q_start + 2 * i + 2) = S.testBit i := by
  induction bits generalizing S with
  | zero => intros i hi; omega
  | succ n ih =>
    intro i hi
    have hTn_lt : cuccaro_read_val n q_start f < 2^n :=
      cuccaro_read_val_lt n q_start f
    have h_unfold : cuccaro_read_val n q_start f
                  + (if f (q_start + 2 * n + 2) then 2^n else 0) = S := h
    by_cases hi_eq : i = n
    · subst hi_eq
      by_cases hvn : f (q_start + 2 * i + 2) = true
      · rw [if_pos hvn] at h_unfold
        rw [hvn]
        have hS_eq : S = 2^i + cuccaro_read_val i q_start f := by omega
        rw [hS_eq, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hTn_lt]
        rfl
      · have hvn_f : f (q_start + 2 * i + 2) = false := by
          cases hh : f (q_start + 2 * i + 2)
          · rfl
          · exact absurd hh hvn
        rw [if_neg hvn] at h_unfold
        rw [hvn_f]
        have h_eq : S = cuccaro_read_val i q_start f := by omega
        rw [h_eq]
        exact (Nat.testBit_lt_two_pow hTn_lt).symm
    · have hi_lt_n : i < n := by omega
      have h_ih : f (q_start + 2 * i + 2) = (cuccaro_read_val n q_start f).testBit i :=
        ih (cuccaro_read_val n q_start f) hTn_lt rfl i hi_lt_n
      rw [h_ih]
      by_cases hvn : f (q_start + 2 * n + 2) = true
      · rw [if_pos hvn] at h_unfold
        have hS_eq : S = 2^n + cuccaro_read_val n q_start f := by omega
        rw [hS_eq, Nat.testBit_two_pow_add_gt hi_lt_n]
      · rw [if_neg hvn] at h_unfold
        have h_eq : S = cuccaro_read_val n q_start f := by omega
        rw [h_eq]

/-! ## Tick 75 — Deliverable B: One-step state-normal theorem. -/

/-- **Deliverable B — One-step state-normal theorem.**

Combines Tick 74's target decode + Tick 74 workspace preservation +
Deliverable A's all-control-bits preservation into a unified finite-
state characterization of the step gate's output. -/
theorem sqir_modmult_step_state_normal
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    let acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc)) = acc'
    ∧ cuccaro_read_val bits 2
        (Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc)) = 0
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) 1 = false
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) (2 + 2 * bits) = false
    ∧ ∀ k, k < bits →
        Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) (sqir_mult_control_idx bits k)
          = m.testBit k := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact sqir_modmult_step_target_decode bits N a j m acc hbits hN_pos hN hN2 hj hacc
  · have ⟨h_rd, _, _, _⟩ :=
      sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc
    exact h_rd
  · have ⟨_, _, h_fl, _⟩ :=
      sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc
    exact h_fl
  · have ⟨_, h_tc, _, _⟩ :=
      sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc
    exact h_tc
  · intro k hk
    exact sqir_modmult_step_preserves_all_control_bits bits N a m acc j k
      hbits hN_pos hN hN2 hacc hj hk

/-! ## Tick 75 — Deliverable E: Accumulator-spec equals modular product. -/

/-- **Strong recurrence form.** -/
theorem sqir_modmult_acc_spec_eq_mul_mod_pow
    (N a m k : Nat) (hN_pos : 0 < N) :
    sqir_modmult_acc_spec N a m k = (a * (m % 2^k)) % N := by
  induction k with
  | zero =>
    rw [sqir_modmult_acc_spec_zero]
    rw [pow_zero, Nat.mod_one, Nat.mul_zero, Nat.zero_mod]
  | succ n ih =>
    rw [nat_mod_two_pow_succ_eq m n]
    by_cases h_bit : m.testBit n = true
    · rw [sqir_modmult_acc_spec_succ_true N a m n h_bit]
      simp only [h_bit, if_true]
      rw [ih, Nat.mul_add, ← Nat.add_mod]
    · have h_bit_false : m.testBit n = false := by
        cases hh : m.testBit n
        · rfl
        · exact absurd hh h_bit
      rw [sqir_modmult_acc_spec_succ_false N a m n h_bit_false]
      rw [h_bit_false]
      simp only [Bool.false_eq_true, if_false, Nat.add_zero]
      exact ih

/-- **Deliverable E — Accumulator-spec equals modular product.**

For `m < 2^bits`, the bit-by-bit accumulator equals `(a * m) % N`. -/
theorem sqir_modmult_acc_spec_eq_mul_mod
    (bits N a m : Nat) (hN_pos : 0 < N) (hm : m < 2^bits) :
    sqir_modmult_acc_spec N a m bits = (a * m) % N := by
  rw [sqir_modmult_acc_spec_eq_mul_mod_pow N a m bits hN_pos]
  rw [Nat.mod_eq_of_lt hm]

/-! ## Tick 76 — Carry-in restoration chain. -/

/-- **Clean candidate carry-in (`q_start = 2`) restored to `false`.**

Chains through `dirtyFlag → compareConst c → X(1)`:
- `dirtyFlag` restores carry-in via `dirtyFlag_carry_in_restored_general`.
- `compareConst c` preserves all workspace positions via
  `compareConst_candidate_workspace_restored_at_general`.
- `X(1)` doesn't touch position 2 (since 2 ≠ 1). -/
theorem sqir_style_modAddConst_clean_candidate_carry_in_restored
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
theorem sqir_style_controlledModAddConst_candidate_carry_in_restored
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
    exact sqir_style_modAddConst_clean_candidate_carry_in_restored bits N c x
      hbits hN_pos hN hN2 hc hx

/-- **Wrapper-level controlled mod-add carry-in restored.** Adds the
`c = 0` identity case to the candidate version. -/
theorem sqir_style_controlledModAddConst_gate_carry_in_restored
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
    exact sqir_style_controlledModAddConst_candidate_carry_in_restored bits N c x controlIdx control
      hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag

/-! ## Tick 76 — Step gate position-wise facts. -/

/-- **Generic helper — step gate doesn't touch positions outside its
support.**  At any `q` outside workspace, distinct from flag and
controlIdx_j, the gate's output equals the input's value (via
commute + update_self). -/
theorem sqir_modmult_step_at_untouched_pos
    (bits N a j m acc q : Nat) (hj : j < bits)
    (h_input : sqir_mult_input_F bits m acc q = false)
    (h_q_out : q < 2 ∨ 2 + (2 * bits + 1) ≤ q)
    (h_q_ne_flag : q ≠ 1)
    (h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx bits j) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) q = false := by
  have h_in_eq : update (sqir_mult_input_F bits m acc) q false
                = sqir_mult_input_F bits m acc := by
    rw [show (false : Bool) = sqir_mult_input_F bits m acc q from h_input.symm]
    exact update_self _ q
  have h_commute := sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
    ((a * 2^j) % N) (sqir_mult_control_idx bits j) q false (sqir_mult_input_F bits m acc)
    h_q_out h_q_ne_flag h_q_ne_ctrl_j
  -- h_commute : applyNat (controlled gate) (update input q false) = update (applyNat (controlled gate) input) q false
  rw [h_in_eq] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [update_eq] at h_at_q
  exact h_at_q

/-- **Step gate's output at flag bit 0 is `false`.** -/
theorem sqir_modmult_step_flag0_false
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits) (hj : j < bits) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) 0 = false := by
  apply sqir_modmult_step_at_untouched_pos bits N a j m acc 0 hj
  · exact sqir_mult_input_flag_0_false bits m acc
  · exact Or.inl (by omega)
  · omega
  · have h := sqir_mult_control_idx_outside_modadd_workspace_form bits j
    intro h_eq; unfold sqir_mult_control_idx at h_eq; omega

/-- **Step gate's output above the multiplier register is `false`.**
For `q ≥ 2 + 2 * bits + 1 + bits`. -/
theorem sqir_modmult_step_above_layout_false
    (bits N a j m acc q : Nat) (hbits : 1 ≤ bits) (hj : j < bits)
    (hq : q ≥ 2 + 2 * bits + 1 + bits) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) q = false := by
  apply sqir_modmult_step_at_untouched_pos bits N a j m acc q hj
  · unfold sqir_mult_input_F
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]
  · exact Or.inr (by omega)
  · omega
  · intro h_eq
    have h := sqir_mult_control_idx_outside_modadd_workspace_form bits j
    unfold sqir_mult_control_idx at h_eq
    omega

/-- **Step gate's output at carry-in (position 2) is `false`.** -/
theorem sqir_modmult_step_carry_in_restored
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) 2 = false := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  rw [sqir_mult_input_F_eq_install_with_j bits m acc j hj hacc_lt]
  unfold sqir_modmult_step_gate
  rw [sqir_style_controlledModAddConst_gate_commute_install bits m j N
        ((a * 2^j) % N) bits _]
  rw [install_mult_bits_skip_j_at_workspace_eq bits m j bits _ 2 (by omega)]
  exact sqir_style_controlledModAddConst_gate_carry_in_restored bits N
    ((a * 2^j) % N) acc (sqir_mult_control_idx bits j) (m.testBit j)
    hbits hN_pos hN hN2 (Nat.mod_lt _ hN_pos) hacc
    (sqir_mult_control_idx_outside_modadd_workspace_form bits j)
    (sqir_mult_control_idx_ne_flag bits j)

/-- **Step gate's output at target bit `i` equals `acc'.testBit i`.**

Uses the per-bit converse `cuccaro_target_val_eq_implies_bits_match`
plus the Tick 74 `sqir_modmult_step_target_decode`. -/
theorem sqir_modmult_step_target_bit
    (bits N a j m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) (2 + 2 * i + 1)
      = (if m.testBit j then (acc + (a * 2^j) % N) % N else acc).testBit i := by
  set acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc with hacc'_def
  have hacc'_lt_N : acc' < N := by
    rw [hacc'_def]
    by_cases h : m.testBit j
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact hacc
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  have h_tgt := sqir_modmult_step_target_decode bits N a j m acc hbits hN_pos hN hN2 hj hacc
  exact cuccaro_target_val_eq_implies_bits_match bits 2 acc' _ hacc'_lt h_tgt i hi

/-- **Step gate's output at read bit `i` is `false`.** -/
theorem sqir_modmult_step_read_bit
    (bits N a j m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) (2 + 2 * i + 2) = false := by
  have h_rd := (sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc).1
  have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
  have := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd i hi
  rw [this, Nat.zero_testBit]

/-! ## R7d^xxix-L-3.15e.3 — q_start-parametric step-gate position
       helpers (target-bit / read-bit / all-control-bits preserved).

The three remaining per-position helpers needed by the eventual
`sqir_modmult_step_state_eq_qstart` proof.  Each is a thin port of
its hard-coded counterpart, consuming previously-closed L-3.15c/d/e
infrastructure plus the q_start-parametric decoders
`cuccaro_target_val_eq_implies_bits_match` and
`cuccaro_read_val_eq_implies_bits_match` (already q_start-parametric
above in this file). -/

/-- q_start-parametric: step gate's output at target/b-register
position `q_start + 2 * i + 1` decodes the i-th bit of the advanced
accumulator.  Port of `sqir_modmult_step_target_bit` (line 2063). -/
theorem sqir_modmult_step_target_bit_qstart
    (bits q_start N a j flagPos m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc) (q_start + 2 * i + 1)
      = (if m.testBit j then (acc + (a * 2^j) % N) % N else acc).testBit i := by
  set acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc with hacc'_def
  have hacc'_lt_N : acc' < N := by
    rw [hacc'_def]
    by_cases h : m.testBit j
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact hacc
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  have h_tgt := sqir_modmult_step_target_decode_qstart bits q_start N a j m acc dim flagPos
    hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart h_workspace h_dim_covers_mult
  exact cuccaro_target_val_eq_implies_bits_match bits q_start acc' _ hacc'_lt h_tgt i hi

/-- q_start-parametric: step gate's output at read/a-register
position `q_start + 2 * i + 2` is `false`.  Port of
`sqir_modmult_step_read_bit` (line 2161). -/
theorem sqir_modmult_step_read_bit_qstart
    (bits q_start N a j flagPos m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc) (q_start + 2 * i + 2) = false := by
  have h_rd := (sqir_modmult_step_workspace_qstart bits q_start N a j m acc dim flagPos
    hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart h_workspace h_dim_covers_mult).1
  have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
  have := cuccaro_read_val_eq_implies_bits_match bits q_start 0 _ h_zero_lt h_rd i hi
  rw [this, Nat.zero_testBit]

/-- q_start-parametric: step gate preserves every multiplier control
bit `k < bits` as `m.testBit k`.  Port of
`sqir_modmult_step_preserves_all_control_bits` (line 1717). -/
theorem sqir_modmult_step_preserves_all_control_bits_qstart
    (bits q_start N a m acc j k flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hj : j < bits) (hk : k < bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc)
          (sqir_mult_control_idx_qstart bits q_start k)
      = m.testBit k := by
  by_cases h_kj : k = j
  · rw [h_kj]
    have ⟨_, _, _, h_ctrl⟩ :=
      sqir_modmult_step_workspace_qstart bits q_start N a j m acc dim flagPos
        hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart h_workspace h_dim_covers_mult
    exact h_ctrl
  · have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
    rw [sqir_mult_input_F_eq_install_with_j_qstart bits q_start m acc j hj hacc_lt]
    unfold sqir_modmult_step_gate_qstart
    rw [sqir_style_controlledModAddConst_gate_commute_install_qstart bits q_start m j N
          ((a * 2^j) % N) flagPos bits _ h_flag_lt_qstart]
    exact install_mult_bits_skip_j_at_mult_k_eq_qstart bits q_start m j bits k _ hk h_kj

/-! ## Tick 76 — Deliverable D: One-step state equality. -/

/-- **Deliverable D — One-step state equality (function-level).**

After applying the step gate to `sqir_mult_input_F bits m acc`, the
state is exactly `sqir_mult_input_F bits m acc'` where
`acc' = if m.testBit j then (acc + (a*2^j)%N) % N else acc`. -/
theorem sqir_modmult_step_state_eq
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j) (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc) := by
  funext q
  set acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc with hacc'_def
  have hacc'_lt_N : acc' < N := by
    rw [hacc'_def]
    by_cases h : m.testBit j
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact hacc
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  -- Case split on q.
  by_cases hq_above : q ≥ 2 + 2 * bits + 1 + bits
  · -- Above-layout case.
    rw [sqir_modmult_step_above_layout_false bits N a j m acc q hbits hj hq_above]
    -- RHS: sqir_mult_input_F bits m acc' q = false (above layout).
    unfold sqir_mult_input_F
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]
  · push_neg at hq_above
    by_cases hq_in_mult : q ≥ 2 + 2 * bits + 1
    · -- Multiplier register.  q = sqir_mult_control_idx bits k where k = q - (2 + 2*bits + 1).
      set k := q - (2 + 2 * bits + 1) with hk_def
      have hk_lt : k < bits := by omega
      have hq_eq : q = sqir_mult_control_idx bits k := by
        unfold sqir_mult_control_idx; omega
      rw [hq_eq]
      rw [sqir_modmult_step_preserves_all_control_bits bits N a m acc j k
            hbits hN_pos hN hN2 hacc hj hk_lt]
      exact (sqir_mult_input_control_bit bits m acc' k hk_lt).symm
    · push_neg at hq_in_mult
      -- Workspace: q < 2 + 2*bits + 1.
      -- Sub-cases on q.
      by_cases hq_0 : q = 0
      · subst hq_0
        rw [sqir_modmult_step_flag0_false bits N a j m acc hbits hj]
        exact (sqir_mult_input_flag_0_false bits m acc').symm
      by_cases hq_1 : q = 1
      · subst hq_1
        have ⟨_, _, h_fl, _⟩ :=
          sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc
        rw [h_fl]
        exact (sqir_mult_input_flag_1_false bits m acc').symm
      by_cases hq_2 : q = 2
      · subst hq_2
        rw [sqir_modmult_step_carry_in_restored bits N a j m acc hbits hN_pos hN hN2 hj hacc]
        -- RHS: sqir_mult_input_F bits m acc' 2 = cuccaro_input_F at q_start = false.
        unfold sqir_mult_input_F
        rw [if_pos (by omega : (2 : Nat) < 2 + 2 * bits + 1)]
        exact (cuccaro_input_F_at_c_in 2 false 0 acc').symm
      -- q ≥ 3, q ≤ 2 + 2*bits.
      -- Determine parity of (q - 2): if (q - 2) is odd, target bit; if even, read bit.
      -- q - 2 ∈ [1, 2*bits].
      by_cases hq_top : q = 2 + 2 * bits
      · subst hq_top
        have ⟨_, h_tc, _, _⟩ :=
          sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc
        rw [h_tc]
        -- RHS: sqir_mult_input_F bits m acc' (2 + 2*bits)
        --    = cuccaro_input_F 2 false 0 acc' (2 + 2*bits).
        -- Using cuccaro_input_F_at_a with i = bits - 1: position 2 + 2*(bits-1) + 2 = 2 + 2*bits.
        -- Value = 0.testBit (bits - 1) = false.
        have h_eq : (2 + 2 * bits : Nat) = 2 + 2 * (bits - 1) + 2 := by omega
        unfold sqir_mult_input_F
        rw [if_pos (by omega : (2 + 2 * bits : Nat) < 2 + 2 * bits + 1)]
        rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 acc']
        exact (Nat.zero_testBit _).symm
      -- q ∈ [3, 2*bits + 1].  Parity dispatch.
      by_cases h_q_odd : q % 2 = 1
      · -- q odd: q = 2 + 2*i + 1 for i = (q-3)/2 < bits.
        have hi_lt : (q - 3) / 2 < bits := by omega
        have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
        rw [hq_eq]
        rw [sqir_modmult_step_target_bit bits N a j m acc ((q - 3) / 2)
              hbits hN_pos hN hN2 hj hacc hi_lt]
        unfold sqir_mult_input_F
        rw [if_pos (by omega : 2 + 2 * ((q - 3) / 2) + 1 < 2 + 2 * bits + 1)]
        exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc').symm
      · -- q even: q = 2 + 2*i + 2 for i = (q-4)/2 < bits.
        have h_q_even : q % 2 = 0 := by omega
        have hi_lt : (q - 4) / 2 < bits := by omega
        have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
        rw [hq_eq]
        rw [sqir_modmult_step_read_bit bits N a j m acc ((q - 4) / 2)
              hbits hN_pos hN hN2 hj hacc hi_lt]
        unfold sqir_mult_input_F
        rw [if_pos (by omega : 2 + 2 * ((q - 4) / 2) + 2 < 2 + 2 * bits + 1)]
        rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc']
        exact (Nat.zero_testBit _).symm

/-! ## R7d^xxix-L-3.15e.4 — q_start-parametric one-step state
       equality.

`funext q` case split mirrors the hard-coded `sqir_modmult_step_state_eq`
(line 2182) but generalised to free `q_start`, `flagPos`, and `dim`.

Case structure (after `funext q`):
- `q ≥ q_start + 2 * bits + 1 + bits` → above layout (`_step_above_layout_false_qstart`).
- `q_start + 2 * bits + 1 ≤ q` → multiplier register, indexed by
  `k = q - (q_start + 2 * bits + 1)` (`_step_preserves_all_control_bits_qstart`).
- `q < q_start` → workspace-below; split into `q = flagPos`
  (`_step_workspace_qstart` flag conjunct) and `q ≠ flagPos`
  (`_step_at_untouched_pos_qstart`).
- `q_start ≤ q < q_start + 2 * bits + 1` (Cuccaro workspace) → split into
  carry-in, top carry, target-bit (odd offset), read-bit (even offset). -/
theorem sqir_modmult_step_state_eq_qstart
    (bits q_start N a j flagPos m acc dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc)
      = sqir_mult_input_F_qstart bits q_start m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc) := by
  funext q
  set acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc with hacc'_def
  have hacc'_lt_N : acc' < N := by
    rw [hacc'_def]
    by_cases h : m.testBit j
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact hacc
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  by_cases hq_above : q ≥ q_start + 2 * bits + 1 + bits
  · -- Above layout.
    rw [sqir_modmult_step_above_layout_false_qstart bits q_start N a j flagPos m acc q
          hbits hj hq_above h_flag_lt_qstart]
    unfold sqir_mult_input_F_qstart
    rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1)]
    rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1 + bits)]
  · push_neg at hq_above
    by_cases hq_in_mult : q ≥ q_start + 2 * bits + 1
    · -- Multiplier register.
      set k := q - (q_start + 2 * bits + 1) with hk_def
      have hk_lt : k < bits := by omega
      have hq_eq : q = sqir_mult_control_idx_qstart bits q_start k := by
        unfold sqir_mult_control_idx_qstart; omega
      rw [hq_eq]
      rw [sqir_modmult_step_preserves_all_control_bits_qstart bits q_start N a m acc j k flagPos
            hbits hN_pos hN hN2 hacc hj hk_lt h_flag_lt_qstart dim h_workspace h_dim_covers_mult]
      exact (sqir_mult_input_control_bit_qstart bits q_start m acc' k hk_lt).symm
    · push_neg at hq_in_mult
      -- Workspace branch: q < q_start + 2 * bits + 1.
      by_cases hq_below : q < q_start
      · -- Below the Cuccaro workspace.
        by_cases hq_flag : q = flagPos
        · -- q = flagPos: use workspace_qstart flag conjunct.
          rw [hq_flag]
          have ⟨_, _, h_fl, _⟩ :=
            sqir_modmult_step_workspace_qstart bits q_start N a j m acc dim flagPos
              hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart h_workspace h_dim_covers_mult
          rw [h_fl]
          -- RHS: sqir_mult_input_F_qstart at flagPos = false (workspace branch, q < q_start).
          unfold sqir_mult_input_F_qstart
          rw [if_pos (by omega : flagPos < q_start + 2 * bits + 1)]
          unfold cuccaro_input_F
          rw [if_pos h_flag_lt_qstart]
        · -- q ≠ flagPos and q < q_start: use untouched_pos.
          have h_q_out : q < q_start ∨ q_start + 2 * bits + 1 ≤ q := Or.inl hq_below
          have h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx_qstart bits q_start j := by
            unfold sqir_mult_control_idx_qstart; omega
          have h_input_false : sqir_mult_input_F_qstart bits q_start m acc q = false := by
            unfold sqir_mult_input_F_qstart
            rw [if_pos (by omega : q < q_start + 2 * bits + 1)]
            unfold cuccaro_input_F
            rw [if_pos hq_below]
          rw [sqir_modmult_step_at_untouched_pos_qstart bits q_start N a j flagPos m acc q
                hj h_input_false h_q_out hq_flag h_q_ne_ctrl_j]
          -- RHS: sqir_mult_input_F_qstart at q (with acc') = false.
          unfold sqir_mult_input_F_qstart
          rw [if_pos (by omega : q < q_start + 2 * bits + 1)]
          unfold cuccaro_input_F
          rw [if_pos hq_below]
      · -- q ≥ q_start, q < q_start + 2 * bits + 1.  Cuccaro workspace.
        push_neg at hq_below
        by_cases hq_qs : q = q_start
        · -- carry-in.
          rw [hq_qs]
          rw [sqir_modmult_step_carry_in_restored_qstart bits q_start N a j flagPos m acc
                hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart]
          unfold sqir_mult_input_F_qstart
          rw [if_pos (by omega : q_start < q_start + 2 * bits + 1)]
          exact (cuccaro_input_F_at_c_in q_start false 0 acc').symm
        · by_cases hq_top : q = q_start + 2 * bits
          · -- top carry.
            rw [hq_top]
            have ⟨_, h_tc, _, _⟩ :=
              sqir_modmult_step_workspace_qstart bits q_start N a j m acc dim flagPos
                hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart h_workspace h_dim_covers_mult
            rw [h_tc]
            have h_eq : (q_start + 2 * bits : Nat) = q_start + 2 * (bits - 1) + 2 := by omega
            unfold sqir_mult_input_F_qstart
            rw [if_pos (by omega : (q_start + 2 * bits : Nat) < q_start + 2 * bits + 1)]
            rw [h_eq, cuccaro_input_F_at_a q_start (bits - 1) false 0 acc']
            exact (Nat.zero_testBit _).symm
          · -- q ∈ (q_start, q_start + 2*bits).  Parity dispatch on (q - q_start).
            by_cases h_q_odd : (q - q_start) % 2 = 1
            · -- Odd offset: q = q_start + 2*i + 1 with i = (q - q_start - 1) / 2.
              have hi_lt : (q - q_start - 1) / 2 < bits := by omega
              have hq_eq : q = q_start + 2 * ((q - q_start - 1) / 2) + 1 := by omega
              rw [hq_eq]
              rw [sqir_modmult_step_target_bit_qstart bits q_start N a j flagPos m acc
                    ((q - q_start - 1) / 2) hbits hN_pos hN hN2 hj hacc hi_lt
                    h_flag_lt_qstart dim h_workspace h_dim_covers_mult]
              unfold sqir_mult_input_F_qstart
              rw [if_pos (by omega : q_start + 2 * ((q - q_start - 1) / 2) + 1
                                      < q_start + 2 * bits + 1)]
              exact (cuccaro_input_F_at_b q_start ((q - q_start - 1) / 2) false 0 acc').symm
            · -- Even offset: q = q_start + 2*i + 2 with i = (q - q_start - 2) / 2.
              have h_q_even : (q - q_start) % 2 = 0 := by omega
              have hi_lt : (q - q_start - 2) / 2 < bits := by omega
              have hq_eq : q = q_start + 2 * ((q - q_start - 2) / 2) + 2 := by omega
              rw [hq_eq]
              rw [sqir_modmult_step_read_bit_qstart bits q_start N a j flagPos m acc
                    ((q - q_start - 2) / 2) hbits hN_pos hN hN2 hj hacc hi_lt
                    h_flag_lt_qstart dim h_workspace h_dim_covers_mult]
              unfold sqir_mult_input_F_qstart
              rw [if_pos (by omega : q_start + 2 * ((q - q_start - 2) / 2) + 2
                                      < q_start + 2 * bits + 1)]
              rw [cuccaro_input_F_at_a q_start ((q - q_start - 2) / 2) false 0 acc']
              exact (Nat.zero_testBit _).symm

/-! ## Tick 76 — Deliverables E/F: Prefix invariant + target decode. -/

/-- **Deliverable E — Prefix state equality.**

By induction on `k`, the prefix gate's output on `sqir_mult_input_F bits m 0`
equals `sqir_mult_input_F bits m (acc_spec ... k)`.  Uses
`sqir_modmult_step_state_eq` at each step + the accumulator recurrence. -/
theorem sqir_modmult_prefix_state_eq
    (bits N a m k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hk : k ≤ bits) :
    Gate.applyNat (sqir_modmult_prefix_gate bits N a k) (sqir_mult_input_F bits m 0)
      = sqir_mult_input_F bits m (sqir_modmult_acc_spec N a m k) := by
  induction k with
  | zero =>
    rw [sqir_modmult_prefix_gate, Gate.applyNat_I, sqir_modmult_acc_spec_zero]
  | succ n ih =>
    have hn_le : n ≤ bits := by omega
    have hn_lt : n < bits := by omega
    rw [sqir_modmult_prefix_gate_succ_eq, Gate.applyNat_seq]
    rw [ih hn_le]
    -- Now: applyNat (step n) (sqir_mult_input_F bits m (acc_spec n))
    --    = sqir_mult_input_F bits m (acc_spec (n+1))
    have hacc_lt_N : sqir_modmult_acc_spec N a m n < N :=
      sqir_modmult_acc_spec_lt N a m n hN_pos
    rw [sqir_modmult_step_state_eq bits N a n m (sqir_modmult_acc_spec N a m n)
          hbits hN_pos hN hN2 hn_lt hacc_lt_N]
    -- Both sides are def-eq via the `acc_spec` recurrence.
    rfl

/-- **Deliverable F — Prefix target decode (corollary of E).**

The decoded target after applying the prefix gate equals the
accumulator spec at `k`. -/
theorem sqir_modmult_prefix_target_decode
    (bits N a m k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hk : k ≤ bits) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_prefix_gate bits N a k) (sqir_mult_input_F bits m 0))
      = sqir_modmult_acc_spec N a m k := by
  rw [sqir_modmult_prefix_state_eq bits N a m k hbits hN_pos hN hN2 hk]
  have h_lt : sqir_modmult_acc_spec N a m k < 2 ^ bits :=
    Nat.lt_of_lt_of_le (sqir_modmult_acc_spec_lt N a m k hN_pos) hN
  exact sqir_mult_input_target_decode bits m (sqir_modmult_acc_spec N a m k) h_lt

/-! ## Tick 76 — Deliverable G: Full modular multiplier target theorem. -/

/-- **Deliverable G — Full modular multiplier target theorem.**

After applying `sqir_modmult_const_gate bits N a` to
`sqir_mult_input_F bits m 0`, the target register decodes to `(a*m) % N`. -/
theorem sqir_modmult_const_gate_target_decode
    (bits N a m : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hm : m < 2^bits) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0))
      = (a * m) % N := by
  unfold sqir_modmult_const_gate
  rw [sqir_modmult_prefix_target_decode bits N a m bits hbits hN_pos hN hN2 (le_refl _)]
  exact sqir_modmult_acc_spec_eq_mul_mod bits N a m hN_pos hm

/-! ## R7d^xxix-L-3.15e.5 — q_start-parametric multi-step
       constant-multiplier target decode (headline).

Final sub-tick of L-3.15e.  Composes:
- a one-line q_start port of `sqir_mult_input_target_decode` (line
  115) to read the initial accumulator from the encoded input state;
- a prefix state-equality (`_prefix_state_eq_qstart`) by induction on
  `k`, consuming the L-3.15e.4 `_step_state_eq_qstart` + the existing
  q_start-INDEPENDENT `sqir_modmult_acc_spec` recurrence;
- a prefix target-decode corollary (`_prefix_target_decode_qstart`);
- the headline `_const_gate_target_decode_qstart`, closed via the
  pre-existing q_start-independent `_acc_spec_eq_mul_mod`. -/

/-- q_start-parametric: decoded target of the initial input state
equals the accumulator value (assuming `acc < 2^bits`).  Port of
`sqir_mult_input_target_decode` (line 115). -/
theorem sqir_mult_input_target_decode_qstart
    (bits q_start m acc : Nat) (hacc : acc < 2 ^ bits) :
    cuccaro_target_val bits q_start (sqir_mult_input_F_qstart bits q_start m acc) = acc := by
  have h_eq : cuccaro_target_val bits q_start (sqir_mult_input_F_qstart bits q_start m acc)
                = acc % 2 ^ bits := by
    apply cuccaro_target_val_eq_sum_when_bits_match
    intro i hi
    unfold sqir_mult_input_F_qstart
    have h1 : q_start + 2 * i + 1 < q_start + 2 * bits + 1 := by omega
    rw [if_pos h1]
    exact cuccaro_input_F_at_b q_start i false 0 acc
  rw [h_eq]
  exact Nat.mod_eq_of_lt hacc

/-- q_start-parametric prefix state equality.  Port of
`sqir_modmult_prefix_state_eq` (line 2416). -/
theorem sqir_modmult_prefix_state_eq_qstart
    (bits q_start N a m k flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hk : k ≤ bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_prefix_gate_qstart bits q_start N a flagPos k)
        (sqir_mult_input_F_qstart bits q_start m 0)
      = sqir_mult_input_F_qstart bits q_start m (sqir_modmult_acc_spec N a m k) := by
  induction k with
  | zero =>
    rw [sqir_modmult_prefix_gate_qstart, Gate.applyNat_I, sqir_modmult_acc_spec_zero]
  | succ n ih =>
    have hn_le : n ≤ bits := by omega
    have hn_lt : n < bits := by omega
    rw [sqir_modmult_prefix_gate_qstart_succ_eq, Gate.applyNat_seq]
    rw [ih hn_le]
    have hacc_lt_N : sqir_modmult_acc_spec N a m n < N :=
      sqir_modmult_acc_spec_lt N a m n hN_pos
    rw [sqir_modmult_step_state_eq_qstart bits q_start N a n flagPos m
          (sqir_modmult_acc_spec N a m n) dim
          hbits hN_pos hN hN2 hn_lt hacc_lt_N h_flag_lt_qstart h_workspace h_dim_covers_mult]
    rfl

/-- q_start-parametric prefix target decode (corollary of prefix
state equality).  Port of `sqir_modmult_prefix_target_decode`
(line 2443). -/
theorem sqir_modmult_prefix_target_decode_qstart
    (bits q_start N a m k flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hk : k ≤ bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_modmult_prefix_gate_qstart bits q_start N a flagPos k)
          (sqir_mult_input_F_qstart bits q_start m 0))
      = sqir_modmult_acc_spec N a m k := by
  rw [sqir_modmult_prefix_state_eq_qstart bits q_start N a m k flagPos dim
        hbits hN_pos hN hN2 hk h_flag_lt_qstart h_workspace h_dim_covers_mult]
  have h_lt : sqir_modmult_acc_spec N a m k < 2 ^ bits :=
    Nat.lt_of_lt_of_le (sqir_modmult_acc_spec_lt N a m k hN_pos) hN
  exact sqir_mult_input_target_decode_qstart bits q_start m
    (sqir_modmult_acc_spec N a m k) h_lt

/-- **R7d^xxix-L-3.15e.5 HEADLINE: q_start-parametric full modular
multiplier target decode.**

After applying `sqir_modmult_const_gate_qstart bits q_start N a
flagPos` to `sqir_mult_input_F_qstart bits q_start m 0`, the target
register decodes to `(a * m) % N`.  Port of
`sqir_modmult_const_gate_target_decode` (line 2461). -/
theorem sqir_modmult_const_gate_target_decode_qstart
    (bits q_start N a m flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hm : m < 2^bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
          (sqir_mult_input_F_qstart bits q_start m 0))
      = (a * m) % N := by
  unfold sqir_modmult_const_gate_qstart
  rw [sqir_modmult_prefix_target_decode_qstart bits q_start N a m bits flagPos dim
        hbits hN_pos hN hN2 (le_refl _) h_flag_lt_qstart h_workspace h_dim_covers_mult]
  exact sqir_modmult_acc_spec_eq_mul_mod bits N a m hN_pos hm

/-! ## R7d^xxix-L-3.15f — q_start-parametric constant-multiplier
       workspace bundle.

After applying the q_start constant multiplier `sqir_modmult_const_gate_qstart`
to the initial input `sqir_mult_input_F_qstart bits q_start m 0`, the
non-target workspace positions are clean and the multiplier control
bits are preserved.  Mirrors the workspace conjuncts of the hard-coded
`sqir_modmult_const_gate_clean` (line 2629).

Strategy: instead of porting an explicit prefix-workspace induction
(the hard-coded version doesn't have one), reuse the just-landed
`sqir_modmult_prefix_state_eq_qstart` (L-3.15e.5) to reshape the
post-gate state into `sqir_mult_input_F_qstart bits q_start m
((a * m) % N)`, then read off each conjunct from the input-state
shape via small q_start ports of the existing input-state facts. -/

/-- q_start-parametric: `sqir_mult_input_F_qstart` at any position
strictly below `q_start` is `false`.  Generalises the hard-coded
`sqir_mult_input_flag_0_false` / `_flag_1_false` to any
flagPos < q_start. -/
theorem sqir_mult_input_at_below_qstart_eq_false_qstart
    (bits q_start m acc q : Nat) (hq : q < q_start) :
    sqir_mult_input_F_qstart bits q_start m acc q = false := by
  unfold sqir_mult_input_F_qstart
  rw [if_pos (by omega : q < q_start + 2 * bits + 1)]
  unfold cuccaro_input_F
  rw [if_pos hq]

/-- q_start-parametric: the read register of `sqir_mult_input_F_qstart`
is 0.  Port of `sqir_mult_input_read_decode` (line 129). -/
theorem sqir_mult_input_read_decode_qstart
    (bits q_start m acc : Nat) :
    cuccaro_read_val bits q_start (sqir_mult_input_F_qstart bits q_start m acc) = 0 := by
  have h_eq : cuccaro_read_val bits q_start (sqir_mult_input_F_qstart bits q_start m acc)
              = 0 % 2 ^ bits := by
    apply cuccaro_read_val_eq_sum_when_bits_match
    intro i hi
    unfold sqir_mult_input_F_qstart
    have h1 : q_start + 2 * i + 2 < q_start + 2 * bits + 1 := by omega
    rw [if_pos h1]
    rw [cuccaro_input_F_at_a q_start i false 0 acc]
  rw [h_eq]; simp

/-- q_start-parametric: the top-carry position `q_start + 2 * bits`
of `sqir_mult_input_F_qstart` is `false`.  Port of
`sqir_mult_input_top_carry_false` (line 162). -/
theorem sqir_mult_input_top_carry_false_qstart
    (bits q_start m acc : Nat) (hbits : 1 ≤ bits) :
    sqir_mult_input_F_qstart bits q_start m acc (q_start + 2 * bits) = false := by
  unfold sqir_mult_input_F_qstart
  rw [if_pos (by omega : (q_start + 2 * bits : Nat) < q_start + 2 * bits + 1)]
  have h_eq : (q_start + 2 * bits : Nat) = q_start + 2 * (bits - 1) + 2 := by omega
  rw [h_eq, cuccaro_input_F_at_a q_start (bits - 1) false 0 acc]
  exact Nat.zero_testBit _

/-- **R7d^xxix-L-3.15f HEADLINE: q_start-parametric constant-multiplier
workspace bundle.**

For the full multiplier `sqir_modmult_const_gate_qstart bits q_start N a
flagPos` applied to `sqir_mult_input_F_qstart bits q_start m 0`:
1. the read register decodes to 0;
2. the top carry position `q_start + 2 * bits` is `false`;
3. the dirty-flag position `flagPos` is `false`;
4. every multiplier control bit `k < bits` is preserved as `m.testBit k`.

Proof routes through `sqir_modmult_prefix_state_eq_qstart` (L-3.15e.5)
at `k = bits` + `sqir_modmult_acc_spec_eq_mul_mod` (q_start-independent)
to reshape the post-gate state, then reads each conjunct off the input
state shape.  Port of the workspace conjuncts of
`sqir_modmult_const_gate_clean` (line 2629). -/
theorem sqir_modmult_const_gate_workspace_qstart
    (bits q_start N a m flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hm : m < 2^bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_read_val bits q_start
          (Gate.applyNat (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
            (sqir_mult_input_F_qstart bits q_start m 0))
        = 0
    ∧ Gate.applyNat (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
          (sqir_mult_input_F_qstart bits q_start m 0) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
          (sqir_mult_input_F_qstart bits q_start m 0) flagPos
        = false
    ∧ ∀ k, k < bits →
        Gate.applyNat (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
          (sqir_mult_input_F_qstart bits q_start m 0)
          (sqir_mult_control_idx_qstart bits q_start k) = m.testBit k := by
  unfold sqir_modmult_const_gate_qstart
  rw [sqir_modmult_prefix_state_eq_qstart bits q_start N a m bits flagPos dim
        hbits hN_pos hN hN2 (le_refl _) h_flag_lt_qstart h_workspace h_dim_covers_mult]
  rw [sqir_modmult_acc_spec_eq_mul_mod bits N a m hN_pos hm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sqir_mult_input_read_decode_qstart bits q_start m ((a * m) % N)
  · exact sqir_mult_input_top_carry_false_qstart bits q_start m ((a * m) % N) hbits
  · exact sqir_mult_input_at_below_qstart_eq_false_qstart bits q_start m
      ((a * m) % N) flagPos h_flag_lt_qstart
  · intro k hk
    exact sqir_mult_input_control_bit_qstart bits q_start m ((a * m) % N) k hk

/-- **Deliverable G corollary — Full multiplier state equality.**

After the full multiplier, the state is `sqir_mult_input_F bits m ((a*m)%N)`. -/
theorem sqir_modmult_const_gate_state_eq
    (bits N a m : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hm : m < 2^bits) :
    Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0)
      = sqir_mult_input_F bits m ((a * m) % N) := by
  unfold sqir_modmult_const_gate
  rw [sqir_modmult_prefix_state_eq bits N a m bits hbits hN_pos hN hN2 (le_refl _)]
  rw [sqir_modmult_acc_spec_eq_mul_mod bits N a m hN_pos hm]

/-! ## Tick 76 — Deliverable H: Clean multiplier bundle. -/

/-- **Step gate is WellTyped at `sqir_modmult_rev_anc bits`.** -/
theorem sqir_modmult_step_gate_wellTyped
    (bits N a j : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (hj : j < bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits) (sqir_modmult_step_gate bits N a j) := by
  unfold sqir_modmult_step_gate
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  -- For acc = 0 (any value in [0, N)), use the WellTyped conjunct.
  have ⟨h_wt, _, _, _, _, _⟩ :=
    sqir_style_controlledModAddConst_gate_clean bits N ((a * 2^j) % N) 0
      (sqir_mult_control_idx bits j) false hbits hN_pos hN hN2 hc_pos hN_pos
      (sqir_mult_control_idx_outside_modadd_workspace_form bits j)
      (sqir_mult_control_idx_ne_flag bits j)
      (sqir_mult_control_idx_lt_sqir_dim bits j hj)
  exact h_wt

/-- **Prefix gate is WellTyped at `sqir_modmult_rev_anc bits`.** -/
theorem sqir_modmult_prefix_gate_wellTyped
    (bits N a k : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (hk : k ≤ bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits) (sqir_modmult_prefix_gate bits N a k) := by
  induction k with
  | zero =>
    rw [sqir_modmult_prefix_gate]
    show 0 < sqir_modmult_rev_anc bits
    unfold sqir_modmult_rev_anc; omega
  | succ n ih =>
    rw [sqir_modmult_prefix_gate_succ_eq]
    refine ⟨?_, ?_⟩
    · exact ih (by omega)
    · exact sqir_modmult_step_gate_wellTyped bits N a n hbits hN_pos hN hN2 (by omega)

/-- **Deliverable H — Clean modular-multiplier bundle.**

For the full multiplier gate `sqir_modmult_const_gate bits N a`:
- WellTyped at `sqir_modmult_rev_anc bits`.
- Target decoded to `(a * m) % N`.
- Read = 0.
- Flag bits 0, 1 = false.
- Top carry (position `2 + 2*bits`) = false.
- All multiplier control bits preserved as `m.testBit k`. -/
theorem sqir_modmult_const_gate_clean
    (bits N a m : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hm : m < 2^bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits) (sqir_modmult_const_gate bits N a)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0))
        = (a * m) % N
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0))
        = 0
    ∧ Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0) 0
        = false
    ∧ Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0) 1
        = false
    ∧ Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0)
          (2 + 2 * bits) = false
    ∧ ∀ k, k < bits →
        Gate.applyNat (sqir_modmult_const_gate bits N a)
          (sqir_mult_input_F bits m 0) (sqir_mult_control_idx bits k) = m.testBit k := by
  have h_state := sqir_modmult_const_gate_state_eq bits N a m hbits hN_pos hN hN2 hm
  have ham_lt : (a * m) % N < 2 ^ bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sqir_modmult_prefix_gate_wellTyped bits N a bits hbits hN_pos hN hN2 (le_refl _)
  · rw [h_state]; exact sqir_mult_input_target_decode bits m ((a * m) % N) ham_lt
  · rw [h_state]; exact sqir_mult_input_read_decode bits m ((a * m) % N)
  · rw [h_state]; exact sqir_mult_input_flag_0_false bits m ((a * m) % N)
  · rw [h_state]; exact sqir_mult_input_flag_1_false bits m ((a * m) % N)
  · rw [h_state]; exact sqir_mult_input_top_carry_false bits m ((a * m) % N) hbits
  · intro k hk
    rw [h_state]
    exact sqir_mult_input_control_bit bits m ((a * m) % N) k hk

/-! ## Tick 76 — Deliverable I: BasicSetting specialization. -/

/-- **Deliverable I — BasicSetting specialization of the full
multiplier clean bundle.**

For BasicSetting parameters (which give `N ≤ 2^(n+1)` and `2*N ≤ 2^(n+1)`),
the clean bundle holds at `bits = n + 1`. -/
theorem sqir_modmult_const_gate_clean_from_BasicSetting
    (a r N m n x_mult : Nat)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (hm : x_mult < 2^(n + 1)) :
    Gate.WellTyped (sqir_modmult_rev_anc (n + 1))
        (sqir_modmult_const_gate (n + 1) N a)
    ∧ cuccaro_target_val (n + 1) 2
          (Gate.applyNat (sqir_modmult_const_gate (n + 1) N a)
            (sqir_mult_input_F (n + 1) x_mult 0)) = (a * x_mult) % N
    ∧ cuccaro_read_val (n + 1) 2
          (Gate.applyNat (sqir_modmult_const_gate (n + 1) N a)
            (sqir_mult_input_F (n + 1) x_mult 0)) = 0
    ∧ Gate.applyNat (sqir_modmult_const_gate (n + 1) N a)
          (sqir_mult_input_F (n + 1) x_mult 0) 0 = false
    ∧ Gate.applyNat (sqir_modmult_const_gate (n + 1) N a)
          (sqir_mult_input_F (n + 1) x_mult 0) 1 = false
    ∧ Gate.applyNat (sqir_modmult_const_gate (n + 1) N a)
          (sqir_mult_input_F (n + 1) x_mult 0) (2 + 2 * (n + 1)) = false
    ∧ ∀ k, k < (n + 1) →
        Gate.applyNat (sqir_modmult_const_gate (n + 1) N a)
          (sqir_mult_input_F (n + 1) x_mult 0)
          (sqir_mult_control_idx (n + 1) k) = x_mult.testBit k := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have hN_le : N ≤ 2 ^ (n + 1) := by omega
  exact sqir_modmult_const_gate_clean (n + 1) N a x_mult
    (by omega : 1 ≤ n + 1) hN_pos hN_le hN2 hm

theorem sqir_modmult_acc_spec_from_zero (N a m acc : Nat) :
    sqir_modmult_acc_spec_from N a m acc 0 = acc := rfl

theorem sqir_modmult_acc_spec_from_succ_true
    (N a m acc k : Nat) (h : m.testBit k = true) :
    sqir_modmult_acc_spec_from N a m acc (k + 1)
      = (sqir_modmult_acc_spec_from N a m acc k + (a * 2 ^ k) % N) % N := by
  show (if m.testBit k then _ else _) = _; simp [h]

theorem sqir_modmult_acc_spec_from_succ_false
    (N a m acc k : Nat) (h : m.testBit k = false) :
    sqir_modmult_acc_spec_from N a m acc (k + 1)
      = sqir_modmult_acc_spec_from N a m acc k := by
  show (if m.testBit k then _ else _) = _; simp [h]

/-- For `0 < N`, the accumulator-from-start stays in `[0, N)` if `acc < N`. -/
theorem sqir_modmult_acc_spec_from_lt
    (N a m acc k : Nat) (hN_pos : 0 < N) (hacc : acc < N) :
    sqir_modmult_acc_spec_from N a m acc k < N := by
  induction k with
  | zero => exact hacc
  | succ n ih =>
    unfold sqir_modmult_acc_spec_from
    by_cases h : m.testBit n
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact ih

/-- **Closed form for `acc_spec_from`**: equals `(acc + a * (m % 2^k)) % N`
for `acc < N`. -/
theorem sqir_modmult_acc_spec_from_eq_mod_pow
    (N a m acc k : Nat) (hN_pos : 0 < N) (hacc : acc < N) :
    sqir_modmult_acc_spec_from N a m acc k = (acc + a * (m % 2^k)) % N := by
  induction k with
  | zero =>
    rw [sqir_modmult_acc_spec_from_zero, pow_zero, Nat.mod_one,
        Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hacc]
  | succ n ih =>
    rw [nat_mod_two_pow_succ_eq m n]
    by_cases h_bit : m.testBit n = true
    · rw [sqir_modmult_acc_spec_from_succ_true N a m acc n h_bit]
      simp only [h_bit, if_true]
      rw [ih, Nat.mul_add, ← Nat.add_mod, Nat.add_assoc]
    · have h_bit_false : m.testBit n = false := by
        cases hh : m.testBit n
        · rfl
        · exact absurd hh h_bit
      rw [sqir_modmult_acc_spec_from_succ_false N a m acc n h_bit_false]
      rw [h_bit_false]; simp only [Bool.false_eq_true, if_false, Nat.add_zero]
      exact ih

/-- For `m < 2^bits` and `acc < N`, the final accumulator equals
`(acc + a*m) % N`. -/
theorem sqir_modmult_acc_spec_from_eq_add_mul_mod
    (bits N a m acc : Nat) (hN_pos : 0 < N) (hacc : acc < N) (hm : m < 2^bits) :
    sqir_modmult_acc_spec_from N a m acc bits = (acc + a * m) % N := by
  rw [sqir_modmult_acc_spec_from_eq_mod_pow N a m acc bits hN_pos hacc]
  rw [Nat.mod_eq_of_lt hm]

/-- **Generalized prefix state equality** for arbitrary starting accumulator. -/
theorem sqir_modmult_prefix_state_eq_from
    (bits N a m acc k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hk : k ≤ bits) :
    Gate.applyNat (sqir_modmult_prefix_gate bits N a k) (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m (sqir_modmult_acc_spec_from N a m acc k) := by
  induction k with
  | zero =>
    rw [sqir_modmult_prefix_gate, Gate.applyNat_I, sqir_modmult_acc_spec_from_zero]
  | succ n ih =>
    have hn_le : n ≤ bits := by omega
    have hn_lt : n < bits := by omega
    rw [sqir_modmult_prefix_gate_succ_eq, Gate.applyNat_seq]
    rw [ih hn_le]
    have hacc_lt_N : sqir_modmult_acc_spec_from N a m acc n < N :=
      sqir_modmult_acc_spec_from_lt N a m acc n hN_pos hacc
    rw [sqir_modmult_step_state_eq bits N a n m (sqir_modmult_acc_spec_from N a m acc n)
          hbits hN_pos hN hN2 hn_lt hacc_lt_N]
    rfl

/-- **Generalized full multiplier state equality** for arbitrary
starting accumulator. -/
theorem sqir_modmult_const_gate_state_eq_from
    (bits N a m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hm : m < 2^bits) :
    Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m ((acc + a * m) % N) := by
  unfold sqir_modmult_const_gate
  rw [sqir_modmult_prefix_state_eq_from bits N a m acc bits hbits hN_pos hN hN2 hacc (le_refl _)]
  rw [sqir_modmult_acc_spec_from_eq_add_mul_mod bits N a m acc hN_pos hacc hm]

/-! ## R7d^xxix-L-3.15g — q_start-parametric in-place modular
       multiplier infrastructure (fallback Option 2).

The full in-place state-equality
`sqir_modmult_inplace_candidate_state_eq_qstart` requires porting
~7 swap-position helpers plus a ~100-line
`sqir_swap_acc_mult_apply_qstart`.  Total ~300 lines is too large
for a single tick.

This sub-tick lands the *prerequisite layer*:
- forward-compute generalised state-equality lifted to arbitrary
  starting accumulator (`sqir_modmult_const_gate_state_eq_from_qstart`
  and its prefix ancestor);
- q_start swap-register definitions
  (`sqir_target_idx_qstart`, `sqir_swap_acc_mult_aux_qstart`,
  `sqir_swap_acc_mult_qstart`) plus the trivial index-distinctness
  and recursion-unfold lemmas;
- the q_start in-place candidate definition
  (`sqir_modmult_inplace_candidate_qstart`).

The `acc_spec_from` arithmetic chain
(`sqir_modmult_acc_spec_from`, `_from_lt`, `_from_eq_add_mul_mod`)
is q_start-INDEPENDENT and reused as-is.

Deferred to L-3.15g.2:
- 5 swap-position case helpers
  (`_at_mult_out_range`, `_at_target_out_range`, `_at_target_in_range`,
  `_at_mult_in_range`, `_at_other`) ported to qstart;
- `sqir_swap_acc_mult_apply_qstart` (~100-line `funext q` case split);
- the headline `sqir_modmult_inplace_candidate_state_eq_qstart`. -/

/-- q_start-parametric: prefix state-eq generalised to an arbitrary
starting accumulator.  Port of `sqir_modmult_prefix_state_eq_from`.
Uses the q_start-INDEPENDENT `sqir_modmult_acc_spec_from` chain
plus the L-3.15e.4 `sqir_modmult_step_state_eq_qstart`. -/
theorem sqir_modmult_prefix_state_eq_from_qstart
    (bits q_start N a m acc k flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hk : k ≤ bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_prefix_gate_qstart bits q_start N a flagPos k)
        (sqir_mult_input_F_qstart bits q_start m acc)
      = sqir_mult_input_F_qstart bits q_start m
          (sqir_modmult_acc_spec_from N a m acc k) := by
  induction k with
  | zero =>
    rw [sqir_modmult_prefix_gate_qstart, Gate.applyNat_I,
        sqir_modmult_acc_spec_from_zero]
  | succ n ih =>
    have hn_le : n ≤ bits := by omega
    have hn_lt : n < bits := by omega
    rw [sqir_modmult_prefix_gate_qstart_succ_eq, Gate.applyNat_seq]
    rw [ih hn_le]
    have hacc_lt_N : sqir_modmult_acc_spec_from N a m acc n < N :=
      sqir_modmult_acc_spec_from_lt N a m acc n hN_pos hacc
    rw [sqir_modmult_step_state_eq_qstart bits q_start N a n flagPos m
          (sqir_modmult_acc_spec_from N a m acc n) dim
          hbits hN_pos hN hN2 hn_lt hacc_lt_N h_flag_lt_qstart h_workspace
          h_dim_covers_mult]
    rfl

/-- q_start-parametric: full multiplier state-eq generalised to an
arbitrary starting accumulator.  Port of
`sqir_modmult_const_gate_state_eq_from`. -/
theorem sqir_modmult_const_gate_state_eq_from_qstart
    (bits q_start N a m acc flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hm : m < 2^bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc)
      = sqir_mult_input_F_qstart bits q_start m ((acc + a * m) % N) := by
  unfold sqir_modmult_const_gate_qstart
  rw [sqir_modmult_prefix_state_eq_from_qstart bits q_start N a m acc bits flagPos dim
        hbits hN_pos hN hN2 hacc (le_refl _) h_flag_lt_qstart h_workspace
        h_dim_covers_mult]
  rw [sqir_modmult_acc_spec_from_eq_add_mul_mod bits N a m acc hN_pos hacc hm]

/-- Target index disjoint from multiplier control index. -/
theorem sqir_target_idx_ne_mult_control_idx_qstart
    (bits q_start i j : Nat) (hi : i < bits) :
    sqir_target_idx_qstart q_start i
      ≠ sqir_mult_control_idx_qstart bits q_start j := by
  unfold sqir_target_idx_qstart sqir_mult_control_idx_qstart
  omega

/-- Unfold lemma for `sqir_swap_acc_mult_aux_qstart`. -/
theorem sqir_swap_acc_mult_aux_qstart_succ_eq (bits q_start k : Nat) :
    sqir_swap_acc_mult_aux_qstart bits q_start (k + 1)
      = Gate.seq (sqir_swap_acc_mult_aux_qstart bits q_start k)
          (qubit_swap (sqir_target_idx_qstart q_start k)
                      (sqir_mult_control_idx_qstart bits q_start k)) := rfl

/-- Sanity helper: `sqir_target_idx_qstart` value. -/
theorem sqir_target_idx_qstart_value (q_start i : Nat) :
    sqir_target_idx_qstart q_start i = q_start + 2 * i + 1 := rfl

/-! ### Per-position behavior of `sqir_swap_acc_mult_aux_qstart` (L-3.15g.2). -/

/-- q_start port of `sqir_swap_acc_mult_aux_at_mult_out_range` (line 3097).
At a multiplier bit `i ≥ k`, swap output = input. -/
theorem sqir_swap_acc_mult_at_mult_out_range_qstart
    (bits q_start k i : Nat) (hk : k ≤ bits) (hi_ge : k ≤ i) (hi_bits : i < bits)
    (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux_qstart bits q_start k) f
        (sqir_mult_control_idx_qstart bits q_start i)
      = f (sqir_mult_control_idx_qstart bits q_start i) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [sqir_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    have h_i_ne_n : i ≠ n := by omega
    have h_ne_mult_n :
        sqir_mult_control_idx_qstart bits q_start i
          ≠ sqir_mult_control_idx_qstart bits q_start n := by
      intro heq
      exact h_i_ne_n (sqir_mult_control_idx_injective_qstart bits q_start i n heq)
    have h_ne_target_n :
        sqir_mult_control_idx_qstart bits q_start i
          ≠ sqir_target_idx_qstart q_start n :=
      (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n i hn_lt).symm
    rw [update_neq _ _ _ _ h_ne_mult_n]
    rw [update_neq _ _ _ _ h_ne_target_n]
    exact ih (by omega) (by omega)

end FormalRV.BQAlgo
