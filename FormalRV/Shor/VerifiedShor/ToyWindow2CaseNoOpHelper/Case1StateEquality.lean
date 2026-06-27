/- ToyWindow2CaseNoOpHelper — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.ToyWindow2CaseNoOpHelper.Case1PerPositionHelpers

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ### R7d^xi^c — remaining case-1 scalar helpers

Three helpers needed for the case-1 state_eq assembly:
- `_internalFlagFalse` (position 1, finishes through `clean_flagFalse`).
- `_carryInRestored` (position 2, finishes through
  `style_controlledModAddConst_gate_carry_in_restored`).
- `_restores_flagIdx` (flagIdx, three inner h_MA_* haves + outer
  C2 dispatch, mirrors case-3 with X1/X2 layers + `update_idem`). -/

/-- The case-1 gate forces the Cuccaro internal flag at position 1
to `false` after the full sequence. -/
theorem toyWindow2Case1Gate_internalFlagFalse
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
        (toyWindow2Case3Input acc b0Idx b1Idx true false) 1 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
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
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false) 1
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]
  rw [h_F0_b1]
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_X1_b0, h_X1_b1, h_X1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
  exact ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 1) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-1 gate restores the Cuccaro carry-in at position 2 to
`false` after the full sequence. -/
theorem toyWindow2Case1Gate_carryInRestored
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
        (toyWindow2Case3Input acc b0Idx b1Idx true false) 2 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  have h_2_ne_flag : (2 : Nat) ≠ flagIdx := by omega
  have h_2_ne_b0 : (2 : Nat) ≠ b0Idx := by omega
  have h_2_ne_b1 : (2 : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false) 2
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]
  rw [h_F0_b1]
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_X1_b0, h_X1_b1, h_X1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
  exact style_controlledModAddConst_gate_carry_in_restored bits N
    (tableValue a N 2 k 1) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1

/-- The case-1 gate restores the external equality flag at `flagIdx`
to its original value `false` after the full sequence.

Proof mirrors case-3's `_restores_flagIdx` with the addition of X1/X2
peelings and a single `update_idem` merge step. -/
theorem toyWindow2Case1Gate_restores_flagIdx
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
        (toyWindow2Case3Input acc b0Idx b1Idx true false) flagIdx = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  -- Input read at b1Idx (used to substitute the X1's !input b1Idx).
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]
  -- Post-X1 reads at b0Idx, b1Idx, flagIdx.
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- The three inner reads: M(C1(X1 input)) at b0Idx, b1Idx, flagIdx.
  have h_MA_b0 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 1) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b1Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)))
        b0Idx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_eq]
  have h_MA_b1 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 1) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b1Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)))
        b1Idx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
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
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)))
        flagIdx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    exact ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
      bits N (tableValue a N 2 k 1) acc flagIdx true
      hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
  -- Combine.
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false) flagIdx
      = false
  simp only [Gate.applyNat_seq]
  -- Peel X2 (writes b1Idx, flagIdx ≠ b1Idx → flagIdx-side).
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
  -- Peel C2: writes flagIdx with XOR.
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_eq]
  -- Substitute h_MA_b0, h_MA_b1, h_MA_flag.
  rw [h_MA_b0, h_MA_b1, h_MA_flag]
  decide

/-! ### R7d^xi^d — full state equality for case-1 gate

Funext-assembly theorem combining all 9 case-1 per-position helpers.
Mirrors `toyWindow2Case3Gate_state_eq` exactly: same case dispatch
order, same `cuccaro_input_F`-evaluation lemmas for the RHS. The
only differences from case 3:
- The input has `b1 = false` (case 1) instead of `b1 = true` (case 3).
- The accumulator update uses `tableValue a N 2 k 1`.
- At q = b1Idx the RHS reduces to `false` (instead of `true`). -/

/-- **Full state equality for the case-1 selected-add gate.**

When applied to `toyWindow2Case3Input acc b0Idx b1Idx true false`,
the case-1 gate produces exactly
`toyWindow2Case3Input ((acc + tableValue a N 2 k 1) % N) b0Idx b1Idx
   true false`.

The accumulator advances by `tableValue a N 2 k 1` (mod N), the
two window bits remain `true`/`false` respectively, the equality
flag is restored, and the entire SQIR/Cuccaro workspace is restored
to 0. -/
theorem toyWindow2Case1Gate_state_eq
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
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input ((acc + tableValue a N 2 k 1) % N)
          b0Idx b1Idx true false := by
  funext q
  set acc' := (acc + tableValue a N 2 k 1) % N with hacc'_def
  have hacc'_lt_N : acc' < N := Nat.mod_lt _ hN_pos
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  have h_flag_eq_zero : flagIdx = 0 := by omega
  -- Case on q = b1Idx.
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    rw [toyWindow2Case1Gate_preserves_b1Idx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  -- Case on q = b0Idx (q ≠ b1Idx).
  by_cases hq_b0 : q = b0Idx
  · rw [hq_b0]
    rw [toyWindow2Case1Gate_preserves_b0Idx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  -- Case on q = flagIdx (q ≠ b1Idx, q ≠ b0Idx).
  by_cases hq_flag : q = flagIdx
  · rw [hq_flag]
    rw [toyWindow2Case1Gate_restores_flagIdx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- Now q ≠ b0Idx, q ≠ b1Idx, q ≠ flagIdx.
  have h_rhs :
      toyWindow2Case3Input acc' b0Idx b1Idx true false q
        = cuccaro_input_F 2 false 0 acc' q := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
  rw [h_rhs]
  -- Case on q ≥ 2 + 2*bits + 1 (above layout).
  by_cases hq_above : 2 + 2 * bits + 1 ≤ q
  · rw [toyWindow2Case1Gate_aboveLayoutFalse bits N a k acc flagIdx b0Idx b1Idx q
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
          hq_above hq_b0 hq_b1 hq_flag]
    exact (cuccaro_input_F_above_eq_false 2 bits acc' q hq_above hacc'_lt).symm
  push_neg at hq_above
  -- Case q = 2 (carry-in).
  by_cases hq_2 : q = 2
  · subst hq_2
    rw [toyWindow2Case1Gate_carryInRestored bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    exact (cuccaro_input_F_at_c_in 2 false 0 acc').symm
  -- Case q = 1.
  by_cases hq_1 : q = 1
  · subst hq_1
    rw [toyWindow2Case1Gate_internalFlagFalse bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold cuccaro_input_F
    rw [if_pos (by omega : (1 : Nat) < 2)]
  -- Case q = 0: contradiction via flagIdx = 0 and q ≠ flagIdx.
  by_cases hq_0 : q = 0
  · subst hq_0
    exact absurd h_flag_eq_zero.symm hq_flag
  -- q ∈ [3, 2 + 2*bits].  Parity dispatch.
  by_cases h_q_odd : q % 2 = 1
  · -- Target bit.
    have hi_lt : (q - 3) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
    rw [hq_eq]
    rw [toyWindow2Case1Gate_targetBit bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag ((q - 3) / 2) hi_lt]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc').symm
  · -- Read bit.
    have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    rw [toyWindow2Case1Gate_readBit bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag ((q - 4) / 2) hi_lt]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc']
    exact (Nat.zero_testBit _).symm


end Windowed
end VerifiedShor
