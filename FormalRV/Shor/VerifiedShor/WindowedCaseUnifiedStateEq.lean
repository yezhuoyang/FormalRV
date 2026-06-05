import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.ToyWindow2CaseNoOpHelper

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
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
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
  exact sqir_style_controlledModAddConst_gate_carry_in_restored bits N
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

/-! ## Phase R7d^xiv^a — case-1 no-op state_eq on (T, T) input

For non-firing input `b0 = true`, `b1 = true`, the case-1 gate
acts as the identity on `toyWindow2Case3Input acc b0Idx b1Idx
true true`. This is the first of three concrete no-op lemmas
toward the unified case-1 state_eq. -/

/-- **Case-1 no-op state_eq on (T, T) input.**

When applied to `toyWindow2Case3Input acc b0Idx b1Idx true true`,
the case-1 gate produces exactly the same state. The case-1
firing condition `b0 ∧ ¬b1` is `true ∧ ¬true = false`, so the
gate behaves as identity. -/
theorem toyWindow2Case1Gate_state_eq_TT_noop
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
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input acc b0Idx b1Idx true true := by
  funext q
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  have h_flag_eq_zero : flagIdx = 0 := by omega
  -- Input read at b1Idx (for the X1 flip, computes to !true = false).
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  -- Post-X1 reads at b0Idx, b1Idx, flagIdx (input has b1=true → post-X1 has b1=false).
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)
                  b1Idx (!true) b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)
                  b1Idx (!true) b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)
                  b1Idx (!true) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- For (T, T), the inner CCX1 XOR computes false XOR (true AND false) = false.
  -- This means the C1 update at flagIdx is a no-op (value already false).
  -- After update_idem on b1Idx layers and reordering, the M's input is
  -- (update F b0Idx true) (b1Idx false) since the flagIdx update collapses.
  -- The M-state then equals the state' for both firing and noop cases at
  -- positions where M acts identity-like.
  -- Case on q = b1Idx.
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    -- Trace: X-flips give net no change to b1Idx. Output b1Idx = true (input value).
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b1Idx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b1Idx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_eq]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
    -- Show inner state at b1Idx = false.
    have h_state_b1 :
        Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)) b1Idx
          = false := by
      rw [Gate.applyNat_CCX]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
      rw [Gate.applyNat_X]
      rw [FormalRV.Framework.update_eq]
      rw [FormalRV.Framework.update_eq]
      rfl
    set state := Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
                    (Gate.applyNat (Gate.X b1Idx)
                      (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true))
    have h_in_eq : update state b1Idx false = state := by
      funext p
      by_cases hp : p = b1Idx
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_state_b1.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    have h_commute :=
      sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx false state
        h_b1_out h_b1_ne_one h_b1_ne_flag
    rw [h_in_eq] at h_commute
    have h_at := congr_fun h_commute b1Idx
    rw [FormalRV.Framework.update_eq] at h_at
    rw [h_at]
    -- Goal: !false = (update (update F b0Idx true) b1Idx true) b1Idx
    rw [FormalRV.Framework.update_eq]
    rfl
  by_cases hq_b0 : q = b0Idx
  · rw [hq_b0]
    -- Output b0Idx = true (input value).
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b0Idx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b0Idx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
    -- State pre-M: update (update (update (update F b0Idx T) b1Idx T) b1Idx F) flagIdx F.
    -- update_idem merges the b1Idx updates (T then F → just F).
    rw [FormalRV.Framework.update_idem]
    -- State: update (update (update F b0Idx T) b1Idx F) flagIdx F.
    -- Push flagIdx innermost via update_comm.
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    -- State: update (update (update F flagIdx F) b0Idx T) b1Idx F.
    -- Push b1Idx, b0Idx outside M.
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_eq]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_eq]
  by_cases hq_flag : q = flagIdx
  · rw [hq_flag]
    -- Output flagIdx = false (input value).
    -- For (T, T), C1's XOR = F XOR (T AND F) = F. So flagIdx updates are no-ops.
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) flagIdx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) flagIdx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    -- Three inner h_MA_* haves for M(C1(X1 input)) at b0Idx, b1Idx, flagIdx.
    -- For (T, T) input, these compute differently from firing case.
    have h_MA_b0 :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)))
          b0Idx = true := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
            h_b0_ne_flag]
      rw [FormalRV.Framework.update_eq]
    have h_MA_b1 :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)))
          b1Idx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_eq]
    have h_MA_flag :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)))
          flagIdx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
            h_b0_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
      exact ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
        bits N (tableValue a N 2 k 1) acc flagIdx false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    -- Now peel C2 and read at flagIdx.
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_eq]
    rw [h_MA_b0, h_MA_b1, h_MA_flag]
    simp only [Bool.and_false, Bool.false_xor]
    -- Goal: false = input flagIdx
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- Now q ≠ b0Idx, q ≠ b1Idx, q ≠ flagIdx.
  -- Simplify the RHS to cuccaro_input_F 2 false 0 acc q.
  have h_rhs :
      toyWindow2Case3Input acc b0Idx b1Idx true true q
        = cuccaro_input_F 2 false 0 acc q := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
  rw [h_rhs]
  -- Case on q ≥ 2 + 2*bits + 1 (above layout).
  by_cases hq_above : 2 + 2 * bits + 1 ≤ q
  · -- Above-layout: output = false = input.
    have h_q_ne_one : q ≠ 1 := fun h => by omega
    have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
    -- Trace through gate.
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) q
        = cuccaro_input_F 2 false 0 acc q
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
    -- M's output at q (above layout, ≠ flagIdx). Use commute trick.
    have h_input_q :
        (update (cuccaro_input_F 2 false 0 acc) flagIdx false) q
          = cuccaro_input_F 2 false 0 acc q := by
      rw [FormalRV.Framework.update_neq _ _ _ _ hq_flag]
    have h_q_val : cuccaro_input_F 2 false 0 acc q = false :=
      cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt
    -- The state going into M is update F flagIdx false. By update_self (F flagIdx = false),
    -- this equals F. So M is applied to F. Output at q = false (commute + cuccaro_input_F).
    -- Simpler: show update at flagIdx with false is no-op since F flagIdx = false.
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
    -- Now use commute trick at q for M on cuccaro_input_F.
    have h_in_eq2 :
        update (cuccaro_input_F 2 false 0 acc) q false
          = cuccaro_input_F 2 false 0 acc := by
      funext p
      by_cases hp : p = q
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_q_val.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    have h_commute :=
      sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx q false
        (cuccaro_input_F 2 false 0 acc)
        h_q_out h_q_ne_one hq_flag
    rw [h_in_eq2] at h_commute
    have h_at_q := congr_fun h_commute q
    rw [FormalRV.Framework.update_eq] at h_at_q
    rw [h_at_q]
    -- Goal: false = cuccaro_input_F 2 false 0 acc q
    exact h_q_val.symm
  push_neg at hq_above
  -- Case q = 2 (carry-in).
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
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) 2
        = cuccaro_input_F 2 false 0 acc 2
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
    -- Carry-in restored via SQIR theorem.
    rw [sqir_style_controlledModAddConst_gate_carry_in_restored bits N
      (tableValue a N 2 k 1) acc flagIdx false
      hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1]
    exact (cuccaro_input_F_at_c_in 2 false 0 acc).symm
  -- Case q = 1 (internal flag).
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
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) 1
        = cuccaro_input_F 2 false 0 acc 1
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
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
  · -- Target bit.
    have hi_lt : (q - 3) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
    rw [hq_eq]
    have h_correct := toyWindow2Case1Gate_correct bits N a k acc flagIdx b0Idx b1Idx
      true true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_target_decode :
        cuccaro_target_val bits 2
            (Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
              (toyWindow2Case3Input acc b0Idx b1Idx true true)) = acc := by
      simpa using h_correct
    have h_bit := cuccaro_target_val_eq_implies_bits_match bits 2 acc _ hacc_lt
      h_target_decode ((q - 3) / 2) hi_lt
    rw [h_bit]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc).symm
  · -- Read bit.
    have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    have h_rd := toyWindow2Case1Gate_readVal bits N a k acc flagIdx b0Idx b1Idx
      true true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
    have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd ((q - 4) / 2) hi_lt
    rw [h_bit, Nat.zero_testBit]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc]
    exact (Nat.zero_testBit _).symm

/-! ## Phase R7d^xiv^b — case-1 no-op state_eq on (F, T) input

For non-firing input `b0 = false`, `b1 = true`, the case-1 gate
acts as the identity. The CCX guard is `false AND ¬true = false`,
so the gate behaves as identity. Proof mirrors TT no-op with
substitutions `h_X1_b0 = false` and commute values updated. -/

/-- **Case-1 no-op state_eq on (F, T) input.** -/
theorem toyWindow2Case1Gate_state_eq_FT_noop
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
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input acc b0Idx b1Idx false true := by
  funext q
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  have h_flag_eq_zero : flagIdx = 0 := by omega
  -- Input read at b1Idx (for the X1 flip).
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  -- Post-X1 reads at b0Idx, b1Idx, flagIdx (input has b0=false, b1=true → post-X1 has b1=false).
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b1Idx (!true) b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b1Idx (!true) b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b1Idx (!true) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- For (F, T), CCX1 XOR = F XOR (F AND F) = F. Same no-op structure as TT.
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) b1Idx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) b1Idx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_eq]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
    have h_state_b1 :
        Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)) b1Idx
          = false := by
      rw [Gate.applyNat_CCX]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
      rw [Gate.applyNat_X]
      rw [FormalRV.Framework.update_eq]
      rw [FormalRV.Framework.update_eq]
      rfl
    set state := Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
                    (Gate.applyNat (Gate.X b1Idx)
                      (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true))
    have h_in_eq : update state b1Idx false = state := by
      funext p
      by_cases hp : p = b1Idx
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_state_b1.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    have h_commute :=
      sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx false state
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
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) b0Idx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) b0Idx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) flagIdx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) flagIdx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    have h_MA_b0 :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)))
          b0Idx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
            h_b0_ne_flag]
      rw [FormalRV.Framework.update_eq]
    have h_MA_b1 :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)))
          b1Idx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_eq]
    have h_MA_flag :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)))
          flagIdx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
            h_b0_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
      exact ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
        bits N (tableValue a N 2 k 1) acc flagIdx false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_eq]
    rw [h_MA_b0, h_MA_b1, h_MA_flag]
    simp only [Bool.and_false, Bool.false_and, Bool.false_xor]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  have h_rhs :
      toyWindow2Case3Input acc b0Idx b1Idx false true q
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
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) q
        = cuccaro_input_F 2 false 0 acc q
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
      sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) 2
        = cuccaro_input_F 2 false 0 acc 2
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
    rw [sqir_style_controlledModAddConst_gate_carry_in_restored bits N
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
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) 1
        = cuccaro_input_F 2 false 0 acc 1
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
      false true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_target_decode :
        cuccaro_target_val bits 2
            (Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
              (toyWindow2Case3Input acc b0Idx b1Idx false true)) = acc := by
      simpa using h_correct
    have h_bit := cuccaro_target_val_eq_implies_bits_match bits 2 acc _ hacc_lt
      h_target_decode ((q - 3) / 2) hi_lt
    rw [h_bit]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc).symm
  · have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    have h_rd := toyWindow2Case1Gate_readVal bits N a k acc flagIdx b0Idx b1Idx
      false true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
    have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd ((q - 4) / 2) hi_lt
    rw [h_bit, Nat.zero_testBit]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc]
    exact (Nat.zero_testBit _).symm

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
      sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
      sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
    rw [sqir_style_controlledModAddConst_gate_carry_in_restored bits N
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
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
