/- WindowedCaseUnifiedStateEq — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.ToyWindow2CaseNoOpHelper

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-- The case-2 gate forces position 1 (Cuccaro internal flag) to `false`. -/
theorem toyWindow2Case2Gate_internalFlagFalse
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true) 1 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  have h_1_ne_flag : (1 : Nat) ≠ flagIdx := Ne.symm h_flag_ne_1
  have h_1_ne_b0 : (1 : Nat) ≠ b0Idx := by omega
  have h_1_ne_b1 : (1 : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) 1
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  rw [h_F0_b0]
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1),
        FormalRV.Framework.update_eq]
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_X1_b0, h_X1_b1, h_X1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
  exact ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 2) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-2 gate restores position 2 (carry-in) to `false`. -/
theorem toyWindow2Case2Gate_carryInRestored
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true) 2 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  have h_2_ne_flag : (2 : Nat) ≠ flagIdx := by omega
  have h_2_ne_b0 : (2 : Nat) ≠ b0Idx := by omega
  have h_2_ne_b1 : (2 : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) 2
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  rw [h_F0_b0]
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1),
        FormalRV.Framework.update_eq]
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_X1_b0, h_X1_b1, h_X1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
  exact style_controlledModAddConst_gate_carry_in_restored bits N
    (tableValue a N 2 k 2) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1

/-- Case-2 target-bit at position `2 + 2*i + 1` equals
`((acc + tableValue a N 2 k 2) % N).testBit i`. -/
theorem toyWindow2Case2Gate_targetBit
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true) (2 + 2 * i + 1)
      = ((acc + tableValue a N 2 k 2) % N).testBit i := by
  have h_correct := toyWindow2Case2Gate_correct bits N a k acc flagIdx b0Idx b1Idx
    false true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  have h_target_decode :
      cuccaro_target_val bits 2
          (Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
            (toyWindow2Case3Input acc b0Idx b1Idx false true))
        = (acc + tableValue a N 2 k 2) % N := by
    simpa using h_correct
  have h_acc'_lt_N : (acc + tableValue a N 2 k 2) % N < N := Nat.mod_lt _ hN_pos
  have h_acc'_lt : (acc + tableValue a N 2 k 2) % N < 2^bits :=
    Nat.lt_of_lt_of_le h_acc'_lt_N hN
  exact cuccaro_target_val_eq_implies_bits_match bits 2 _ _ h_acc'_lt
    h_target_decode i hi

/-- Case-2 read-bit at position `2 + 2*i + 2` equals `false`. -/
theorem toyWindow2Case2Gate_readBit
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true) (2 + 2 * i + 2)
      = false := by
  have h_rd := toyWindow2Case2Gate_readVal bits N a k acc flagIdx b0Idx b1Idx
    false true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
  have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd i hi
  rw [h_bit, Nat.zero_testBit]

/-- **Full state equality for the case-2 selected-add gate.**

When applied to `toyWindow2Case3Input acc b0Idx b1Idx false true`,
the case-2 gate produces
`toyWindow2Case3Input ((acc + tableValue a N 2 k 2) % N) b0Idx b1Idx
   false true`. Mirrors case-1 state_eq with b0Idx ↔ b1Idx swap. -/
theorem toyWindow2Case2Gate_state_eq
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input ((acc + tableValue a N 2 k 2) % N)
          b0Idx b1Idx false true := by
  funext q
  set acc' := (acc + tableValue a N 2 k 2) % N with hacc'_def
  have hacc'_lt_N : acc' < N := Nat.mod_lt _ hN_pos
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  have h_flag_eq_zero : flagIdx = 0 := by omega
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    rw [toyWindow2Case2Gate_preserves_b1Idx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  by_cases hq_b0 : q = b0Idx
  · rw [hq_b0]
    rw [toyWindow2Case2Gate_preserves_b0Idx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  by_cases hq_flag : q = flagIdx
  · rw [hq_flag]
    rw [toyWindow2Case2Gate_restores_flagIdx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  have h_rhs :
      toyWindow2Case3Input acc' b0Idx b1Idx false true q
        = cuccaro_input_F 2 false 0 acc' q := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
  rw [h_rhs]
  by_cases hq_above : 2 + 2 * bits + 1 ≤ q
  · rw [toyWindow2Case2Gate_aboveLayoutFalse bits N a k acc flagIdx b0Idx b1Idx q
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
          hq_above hq_b0 hq_b1 hq_flag]
    exact (cuccaro_input_F_above_eq_false 2 bits acc' q hq_above hacc'_lt).symm
  push_neg at hq_above
  by_cases hq_2 : q = 2
  · subst hq_2
    rw [toyWindow2Case2Gate_carryInRestored bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    exact (cuccaro_input_F_at_c_in 2 false 0 acc').symm
  by_cases hq_1 : q = 1
  · subst hq_1
    rw [toyWindow2Case2Gate_internalFlagFalse bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold cuccaro_input_F
    rw [if_pos (by omega : (1 : Nat) < 2)]
  by_cases hq_0 : q = 0
  · subst hq_0
    exact absurd h_flag_eq_zero.symm hq_flag
  by_cases h_q_odd : q % 2 = 1
  · have hi_lt : (q - 3) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
    rw [hq_eq]
    rw [toyWindow2Case2Gate_targetBit bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag ((q - 3) / 2) hi_lt]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc').symm
  · have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    rw [toyWindow2Case2Gate_readBit bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag ((q - 4) / 2) hi_lt]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc']
    exact (Nat.zero_testBit _).symm


end Windowed
end VerifiedShor
