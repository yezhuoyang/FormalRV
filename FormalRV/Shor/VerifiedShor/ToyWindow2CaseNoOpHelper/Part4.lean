/- ToyWindow2CaseNoOpHelper — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.ToyWindow2CaseNoOpHelper.Part3

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ## Phase R7d^xii: case-2 per-position helpers + state equality

Case 2 (v=2, b0=false, b1=true) has X-flip normalization on **b0Idx**
(symmetric to case 1, which uses X-flip on b1Idx). The proofs mirror
case 1 with b0Idx ↔ b1Idx swap throughout and constant
`tableValue a N 2 k 2`. -/

/-- The case-2 gate leaves the Cuccaro read register at `0` after the
full sequence (independent of the window bits `b0`, `b1`).
Mirrors `toyWindow2Case1Gate_readVal` with b0Idx ↔ b1Idx swap. -/
theorem toyWindow2Case2Gate_readVal
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_read_val bits 2
        (Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = 0 := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change cuccaro_read_val bits 2
      (Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = 0
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b0Idx _ _ h_b0_out]
  rw [Gate.applyNat_CCX]
  rw [cuccaro_read_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  rw [h_F0_b0]
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b0Idx (!b0) b0Idx
        = !b0 := by
    rw [FormalRV.Framework.update_eq]
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b0Idx (!b0) b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1),
        FormalRV.Framework.update_eq]
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b0Idx (!b0) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.false_xor]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx (!b0) _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx b1 _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b0Idx (!b0) _ h_b0_out]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b1Idx b1 _ h_b1_out]
  exact ControlledModAdd.clean_readZero ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 2) acc flagIdx (!b0 && b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-2 gate's output is `false` at any position `q` above the
SQIR/Cuccaro layout (`q ≥ 2 + 2*bits + 1`), `q ∉ {b0Idx, b1Idx, flagIdx}`. -/
theorem toyWindow2Case2Gate_aboveLayoutFalse
    (bits N a k acc flagIdx b0Idx b1Idx q : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (hq_above : 2 + 2 * bits + 1 ≤ q)
    (hq_ne_b0 : q ≠ b0Idx) (hq_ne_b1 : q ≠ b1Idx) (hq_ne_flag : q ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true) q = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_q_ne_one : q ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) q
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b0]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  rw [h_F0_b0]
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1),
        FormalRV.Framework.update_eq]
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b0]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b1]
  have h_input_q :
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true) q = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_flag]
    exact cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt
  have h_in_eq :
      update (update (cuccaro_input_F 2 false 0 acc) flagIdx true) q false
        = update (cuccaro_input_F 2 false 0 acc) flagIdx true := by
    funext p
    by_cases hpq : p = q
    · subst hpq
      rw [FormalRV.Framework.update_eq]
      exact h_input_q.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hpq]
  have h_commute :=
    style_controlledModAddConst_gate_commute_update_outside_fun bits N
      (tableValue a N 2 k 2) flagIdx q false
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true)
      h_q_out h_q_ne_one hq_ne_flag
  rw [h_in_eq] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

/-- Case-2 preserves the value `false` at the X-flipped bit position
`b0Idx`. The X-flips give net `!(!false) = false`. -/
theorem toyWindow2Case2Gate_preserves_b0Idx
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
        (toyWindow2Case3Input acc b0Idx b1Idx false true) b0Idx = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) b0Idx
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_eq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
  have h_state_b0 :
      Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b0Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)) b0Idx
        = true := by
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_eq]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_eq]
    rfl
  set state := Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.applyNat (Gate.X b0Idx)
                    (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true))
    with hstate_def
  have h_in_eq : update state b0Idx true = state := by
    funext p
    by_cases hp : p = b0Idx
    · subst hp
      rw [FormalRV.Framework.update_eq]
      exact h_state_b0.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
  have h_commute :=
    style_controlledModAddConst_gate_commute_update_outside_fun bits N
      (tableValue a N 2 k 2) flagIdx b0Idx true state
      h_b0_out h_b0_ne_one h_b0_ne_flag
  rw [h_in_eq] at h_commute
  have h_at := congr_fun h_commute b0Idx
  rw [FormalRV.Framework.update_eq] at h_at
  rw [h_at]
  rfl

/-- Case-2 preserves the value `true` at the un-flipped bit position
`b1Idx`.  Adapts case-1's `_preserves_b0Idx` with b0Idx ↔ b1Idx swap. -/
theorem toyWindow2Case2Gate_preserves_b1Idx
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
        (toyWindow2Case3Input acc b0Idx b1Idx false true) b1Idx = true := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) b1Idx
      = true
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1)]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  rw [h_F0_b0]
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1),
        FormalRV.Framework.update_eq]
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1)]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_eq]

/-- Case-2 restores the external equality flag at `flagIdx` to `false`. -/
theorem toyWindow2Case2Gate_restores_flagIdx
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
        (toyWindow2Case3Input acc b0Idx b1Idx false true) flagIdx = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
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
  have h_MA_b0 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 2) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b0Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)))
        b0Idx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b0, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_eq]
  have h_MA_b1 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 2) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b0Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)))
        b1Idx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b0, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1)]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 2) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_eq]
  have h_MA_flag :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 2) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b0Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)))
        flagIdx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b0, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 2) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    exact ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
      bits N (tableValue a N 2 k 2) acc flagIdx true
      hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) flagIdx
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_eq]
  rw [h_MA_b0, h_MA_b1, h_MA_flag]
  decide


end Windowed
end VerifiedShor
