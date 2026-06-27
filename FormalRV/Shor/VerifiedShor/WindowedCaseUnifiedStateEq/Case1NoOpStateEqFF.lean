/- WindowedCaseUnifiedStateEq — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.WindowedCaseUnifiedStateEq.Case1NoOpStateEqFT

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ## Phase R7d^xiv^c — case-1 no-op state_eq on (F, F) input

For non-firing input `b0 = false`, `b1 = false`, the case-1 gate
acts as the identity. After X1, b1 flips F → T. The CCX guard is
`false AND (!false) = false AND true = false`, so no fire. -/

/-- **Case-1 no-op state_eq on (F, F) input.** -/
theorem toyWindow2Case1Gate_state_eq_FF_noop
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false := by
  funext q
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  have h_flag_eq_zero : flagIdx = 0 := by omega
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)
                  b1Idx (!false) b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)
                  b1Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)
                  b1Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) b1Idx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) b1Idx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_eq]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
    have h_state_b1 :
        Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)) b1Idx
          = true := by
      rw [Gate.applyNat_CCX]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
      rw [Gate.applyNat_X]
      rw [FormalRV.Framework.update_eq]
      rw [FormalRV.Framework.update_eq]
      rfl
    set state := Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
                    (Gate.applyNat (Gate.X b1Idx)
                      (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false))
    have h_in_eq : update state b1Idx true = state := by
      funext p
      by_cases hp : p = b1Idx
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_state_b1.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    have h_commute :=
      style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true state
        h_b1_out h_b1_ne_one h_b1_ne_flag
    rw [h_in_eq] at h_commute
    have h_at := congr_fun h_commute b1Idx
    rw [FormalRV.Framework.update_eq] at h_at
    rw [h_at]
    rw [FormalRV.Framework.update_eq]
    rfl
  by_cases hq_b0 : q = b0Idx
  · rw [hq_b0]
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) b0Idx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) b0Idx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_eq]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_eq]
  by_cases hq_flag : q = flagIdx
  · rw [hq_flag]
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) flagIdx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) flagIdx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    have h_MA_b0 :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)))
          b0Idx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
      rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
            h_b0_ne_flag]
      rw [FormalRV.Framework.update_eq]
    have h_MA_b1 :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)))
          b1Idx = true := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_eq]
    have h_MA_flag :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)))
          flagIdx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
      rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
            h_b0_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
      exact ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
        bits N (tableValue a N 2 k 1) acc flagIdx false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_eq]
    rw [h_MA_b0, h_MA_b1, h_MA_flag]
    simp only [Bool.false_and, Bool.false_xor]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  have h_rhs :
      toyWindow2Case3Input acc b0Idx b1Idx false false q
        = cuccaro_input_F 2 false 0 acc q := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
  rw [h_rhs]
  by_cases hq_above : 2 + 2 * bits + 1 ≤ q
  · have h_q_ne_one : q ≠ 1 := fun h => by omega
    have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) q
        = cuccaro_input_F 2 false 0 acc q
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
    have h_q_val : cuccaro_input_F 2 false 0 acc q = false :=
      cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt
    have h_F_flag : (cuccaro_input_F 2 false 0 acc) flagIdx = false := by
      unfold cuccaro_input_F
      rw [if_pos h_flag_lo]
    have h_update_self : update (cuccaro_input_F 2 false 0 acc) flagIdx false
                      = cuccaro_input_F 2 false 0 acc := by
      funext p
      by_cases hp : p = flagIdx
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_F_flag.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    rw [h_update_self]
    have h_in_eq2 :
        update (cuccaro_input_F 2 false 0 acc) q false
          = cuccaro_input_F 2 false 0 acc := by
      funext p
      by_cases hp : p = q
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_q_val.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    have h_commute :=
      style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx q false
        (cuccaro_input_F 2 false 0 acc)
        h_q_out h_q_ne_one hq_flag
    rw [h_in_eq2] at h_commute
    have h_at_q := congr_fun h_commute q
    rw [FormalRV.Framework.update_eq] at h_at_q
    rw [h_at_q]
    exact h_q_val.symm
  push_neg at hq_above
  by_cases hq_2 : q = 2
  · subst hq_2
    have h_2_ne_b0 : (2 : Nat) ≠ b0Idx := by omega
    have h_2_ne_b1 : (2 : Nat) ≠ b1Idx := by omega
    have h_2_ne_flag : (2 : Nat) ≠ flagIdx := by omega
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) 2
        = cuccaro_input_F 2 false 0 acc 2
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
    rw [style_controlledModAddConst_gate_carry_in_restored bits N
      (tableValue a N 2 k 1) acc flagIdx false
      hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1]
    exact (cuccaro_input_F_at_c_in 2 false 0 acc).symm
  by_cases hq_1 : q = 1
  · subst hq_1
    have h_1_ne_flag : (1 : Nat) ≠ flagIdx := Ne.symm h_flag_ne_1
    have h_1_ne_b0 : (1 : Nat) ≠ b0Idx := by omega
    have h_1_ne_b1 : (1 : Nat) ≠ b1Idx := by omega
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) 1
        = cuccaro_input_F 2 false 0 acc 1
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
    have h_clean : Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits 2 N (tableValue a N 2 k 1) flagIdx 1)
        (update (cuccaro_input_F 2 false 0 acc) flagIdx false) 1 = false :=
      ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
        bits N (tableValue a N 2 k 1) acc flagIdx false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    have h_input : cuccaro_input_F 2 false 0 acc 1 = false := by
      unfold cuccaro_input_F
      rw [if_pos (by omega : (1 : Nat) < 2)]
    rw [h_input]
    exact h_clean
  by_cases hq_0 : q = 0
  · subst hq_0
    exact absurd h_flag_eq_zero.symm hq_flag
  by_cases h_q_odd : q % 2 = 1
  · have hi_lt : (q - 3) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
    rw [hq_eq]
    have h_correct := toyWindow2Case1Gate_correct bits N a k acc flagIdx b0Idx b1Idx
      false false hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_target_decode :
        cuccaro_target_val bits 2
            (Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
              (toyWindow2Case3Input acc b0Idx b1Idx false false)) = acc := by
      simpa using h_correct
    have h_bit := cuccaro_target_val_eq_implies_bits_match bits 2 acc _ hacc_lt
      h_target_decode ((q - 3) / 2) hi_lt
    rw [h_bit]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc).symm
  · have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    have h_rd := toyWindow2Case1Gate_readVal bits N a k acc flagIdx b0Idx b1Idx
      false false hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
    have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd ((q - 4) / 2) hi_lt
    rw [h_bit, Nat.zero_testBit]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc]
    exact (Nat.zero_testBit _).symm


end Windowed
end VerifiedShor
