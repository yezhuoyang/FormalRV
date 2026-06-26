/- ToyWindow2Case3StateEquality — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.ToyWindow2Case3StateEquality.Part3

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ### R7d^vii — scalar Cuccaro-workspace helpers for case-3 gate

These three per-position helpers prove that the case-3 toy gate
restores the internal Cuccaro-workspace scalar positions:

* Position 1 (Cuccaro dirty flag): `false`.
* Position 2 (Cuccaro carry-in): `false`.
* Position `2 + 2*bits` (top carry): `false`.

Each proof follows the same skeleton as `_preserves_b0Idx` /
`_preserves_b1Idx`, but the finishing rule is:
* `clean_flagFalse` for position 1.
* `style_controlledModAddConst_gate_carry_in_restored` for
  position 2 (the carry-in restore theorem is not in the R4b
  bundle, so we use the SQIR theorem directly — it's NOT in the
  forbidden list).
* `clean_topCarryFalse` for position `2 + 2*bits`. -/

/-- The case-3 gate restores the internal Cuccaro dirty flag at
position 1 to `false`. -/
theorem toyWindow2Case3Gate_internalFlagFalse
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) 1 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  have h_1_ne_flag : (1 : Nat) ≠ flagIdx := Ne.symm h_flag_ne_1
  have h_1_ne_b0 : (1 : Nat) ≠ b0Idx := by omega
  have h_1_ne_b1 : (1 : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) 1
      = false
  simp only [Gate.applyNat_seq]
  -- Peel outer CCX2 (writes at flagIdx; we read at 1, ≠ flagIdx).
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_flag]
  -- Peel inner CCX1.
  rw [Gate.applyNat_CCX]
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_input_b0, h_input_b1, h_input_flag]
  simp only [Bool.and_self, Bool.false_xor]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Push b1Idx outside mod-add.
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
  -- Push b0Idx outside mod-add.
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
  -- Apply clean_flagFalse on sqirCuccaroImpl with control = true.
  exact ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 3) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-3 gate restores the Cuccaro carry-in at position 2 to
`false`. -/
theorem toyWindow2Case3Gate_carryInRestored
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) 2 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  have h_2_ne_flag : (2 : Nat) ≠ flagIdx := by omega
  have h_2_ne_b0 : (2 : Nat) ≠ b0Idx := by omega
  have h_2_ne_b1 : (2 : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) 2
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_flag]
  rw [Gate.applyNat_CCX]
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_input_b0, h_input_b1, h_input_flag]
  simp only [Bool.and_self, Bool.false_xor]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
  -- Apply the SQIR carry_in_restored theorem (NOT in the forbidden list).
  exact style_controlledModAddConst_gate_carry_in_restored bits N
    (tableValue a N 2 k 3) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1

/-- The case-3 gate restores the Cuccaro top carry at position
`2 + 2*bits` to `false`. -/
theorem toyWindow2Case3Gate_topCarryFalse
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) (2 + 2 * bits) = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  have h_tc_ne_flag : (2 + 2 * bits : Nat) ≠ flagIdx := by omega
  have h_tc_ne_b0 : (2 + 2 * bits : Nat) ≠ b0Idx := by omega
  have h_tc_ne_b1 : (2 + 2 * bits : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) (2 + 2 * bits)
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_tc_ne_flag]
  rw [Gate.applyNat_CCX]
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_input_b0, h_input_b1, h_input_flag]
  simp only [Bool.and_self, Bool.false_xor]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_tc_ne_b1]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_tc_ne_b0]
  -- Apply clean_topCarryFalse on sqirCuccaroImpl with control = true.
  exact ControlledModAdd.clean_topCarryFalse ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 3) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-! ### R7d^viii: target-bit and read-bit extraction for case-3 gate

These per-position helpers extract individual target/read register bits
from the case-3 gate's output, via the converse decoder lemmas
`cuccaro_target_val_eq_implies_bits_match` and
`cuccaro_read_val_eq_implies_bits_match`.

For the target-bit helper we instantiate `toyWindow2Case3Gate_correct`
at `b0 = b1 = true` (case 3 firing condition) to get the
target_val decode equality, then apply the converse.

For the read-bit helper we first prove a `_readVal` companion (mirroring
`toyWindow2Case3Gate_correct` but routing through `clean_readZero`
instead of `clean_targetDecode`), then apply the converse at `S = 0`.

**No direct call to `sqir_style_controlledModAddConst_gate_clean`** —
the mod-add target/read are extracted through the R4b/R5b projections
`ControlledModAdd.clean_targetDecode` and `ControlledModAdd.clean_readZero`. -/

/-- The case-3 gate leaves the Cuccaro read register at `0` after the
full sequence (independent of the window bits `b0`, `b1`).

Proof mirrors `toyWindow2Case3Gate_correct` but uses
`cuccaro_read_val_update_outside_workspace` for the outside-workspace
invariance steps and `ControlledModAdd.clean_readZero` at the finish. -/
theorem toyWindow2Case3Gate_readVal
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
        (Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = 0 := by
  -- Auxiliary facts (mirror toyWindow2Case3Gate_correct).
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  -- Convert the gate to SQIR-form.
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change cuccaro_read_val bits 2
      (Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = 0
  simp only [Gate.applyNat_seq]
  -- Step 1: outer CCX is just an update at flagIdx, outside workspace.
  rw [Gate.applyNat_CCX]
  rw [cuccaro_read_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  -- Step 2: compute the inner CCX result.
  rw [Gate.applyNat_CCX]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_eq]
  have h_F0_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F0_b0, h_F0_b1, h_F0_flag]
  -- xor false (b0 && b1) = b0 && b1.
  simp only [Bool.false_xor]
  -- Step 3: reorder updates to bring flagIdx update closest to cuccaro_input_F.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Step 4: push b0Idx, b1Idx updates outside the mod-add.
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx b1 _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx b0 _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  -- Step 5: drop the outside-workspace updates from cuccaro_read_val.
  rw [cuccaro_read_val_update_outside_workspace bits 2 b1Idx b1 _ h_b1_out]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b0Idx b0 _ h_b0_out]
  -- Step 6: apply R4b/R5b clean_readZero.
  exact ControlledModAdd.clean_readZero ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 3) acc flagIdx (b0 && b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-3 gate's output at target-bit position `2 + 2*i + 1`
(for `i < bits`) equals the `i`-th bit of `(acc + tableValue a N 2 k 3) % N`.

Proof: instantiate `toyWindow2Case3Gate_correct` at `b0 = b1 = true`
(case 3 firing condition) to get the target_val decode equality, then
apply the converse decoder `cuccaro_target_val_eq_implies_bits_match`.

This is the bit-level analog of `modmult_step_target_bit`. -/
theorem toyWindow2Case3Gate_targetBit
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
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) (2 + 2 * i + 1)
      = ((acc + tableValue a N 2 k 3) % N).testBit i := by
  have h_correct := toyWindow2Case3Gate_correct bits N a k acc flagIdx b0Idx b1Idx
    true true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  -- h_correct: cuccaro_target_val ... = if true && true then ... else acc
  -- Reduce to: cuccaro_target_val ... = (acc + tableValue) % N.
  have h_target_decode :
      cuccaro_target_val bits 2
          (Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
            (toyWindow2Case3Input acc b0Idx b1Idx true true))
        = (acc + tableValue a N 2 k 3) % N := by
    simpa using h_correct
  -- Bound check for the converse.
  have h_acc'_lt_N : (acc + tableValue a N 2 k 3) % N < N := Nat.mod_lt _ hN_pos
  have h_acc'_lt : (acc + tableValue a N 2 k 3) % N < 2^bits :=
    Nat.lt_of_lt_of_le h_acc'_lt_N hN
  -- Apply the converse decoder.
  exact cuccaro_target_val_eq_implies_bits_match bits 2 _ _ h_acc'_lt
    h_target_decode i hi

/-- The case-3 gate's output at read-bit position `2 + 2*i + 2`
(for `i < bits`) equals `false`.

Proof: use `toyWindow2Case3Gate_readVal` to get the read_val = 0
equality, then apply the converse decoder
`cuccaro_read_val_eq_implies_bits_match` at `S = 0`; finish with
`Nat.zero_testBit`.

This is the bit-level analog of `modmult_step_read_bit`. -/
theorem toyWindow2Case3Gate_readBit
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
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) (2 + 2 * i + 2)
      = false := by
  have h_rd := toyWindow2Case3Gate_readVal bits N a k acc flagIdx b0Idx b1Idx
    true true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
  have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd i hi
  rw [h_bit, Nat.zero_testBit]


end Windowed
end VerifiedShor
