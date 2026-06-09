import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultEncoding
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSpec
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultQStart
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultFamily
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSizing
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

end FormalRV.BQAlgo
