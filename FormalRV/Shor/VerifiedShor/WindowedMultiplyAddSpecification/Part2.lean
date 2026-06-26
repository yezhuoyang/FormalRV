/- WindowedMultiplyAddSpecification — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.WindowedMultiplyAddSpecification.Part1

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ## Phase R7d^xvi — case-2 TT no-op via reusable helpers

Validation of the R7d^xv abstraction toolkit. The case-2 gate
X-conjugates on b0Idx (rather than b1Idx like case 1). For TT
input, after the b0 X-normalization makes b0 internally false,
the CCX guard is `false ∧ true = false`, so the inner C1-M-C2
sequence is identity, and the outer X-flip restores. This proof
uses ALL FOUR reusable helpers (`ccx_guard_false_noop`,
`mod_add_state_eq_when_control_false_on_Case3Input`) without
needing per-position dispatch. -/

/-- **Case-2 no-op state_eq on (T, T) input** — validation theorem
for the R7d^xv reusable abstraction toolkit. -/
theorem toyWindow2Case2Gate_state_eq_TT_noop
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
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input acc b0Idx b1Idx true true := by
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  -- Aux: state b0Idx, b1Idx values at the (false, true) intermediate Case3Input.
  have h_state_b0 : toyWindow2Case3Input acc b0Idx b1Idx false true b0Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_state_b1 : toyWindow2Case3Input acc b0Idx b1Idx false true b1Idx = true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  -- The X1-flipped state equals Case3Input acc ... false true.
  have h_state_X1 : update (toyWindow2Case3Input acc b0Idx b1Idx true true) b0Idx (!true)
                  = toyWindow2Case3Input acc b0Idx b1Idx false true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ (Ne.symm h_b0_ne_b1)]
    rfl
  -- Input b0Idx = true (for X1 read).
  have h_input_b0 : toyWindow2Case3Input acc b0Idx b1Idx true true b0Idx = true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  -- Peel the 5 layers of case-2 gate.
  unfold toyWindow2Case2Gate
  -- Convert layout-form mod-add to SQIR form (def-eq).
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input acc b0Idx b1Idx true true
  rw [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [h_input_b0]
  rw [h_state_X1]
  -- Now the state going into C1 is Case3Input acc b0Idx b1Idx false true.
  -- Apply ccx_guard_false_noop for C1.
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  -- Apply mod_add_state_eq_when_control_false_on_Case3Input for M.
  rw [Gate.applyNat_seq]
  rw [mod_add_state_eq_when_control_false_on_Case3Input bits N
        (tableValue a N 2 k 2) acc flagIdx b0Idx b1Idx false true
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  -- Apply ccx_guard_false_noop for C2 (same guard).
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  -- Peel X2 and finish.
  rw [Gate.applyNat_X]
  rw [h_state_b0]
  -- After X2: update Case3Input ... false true) b0Idx (!false) = Case3Input ... true true.
  unfold toyWindow2Case3Input
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ (Ne.symm h_b0_ne_b1)]
  rfl

/-- **Case-2 no-op state_eq on (T, F) input** — Case 2 fires only on
(F, T). For input (T, F), the X1 normalization makes b0Idx internally
false, b1Idx remains false. The CCX guard (false ∧ false) is false, so
the inner C1-M-C2 sequence is identity, and the outer X-flip restores. -/
theorem toyWindow2Case2Gate_state_eq_TF_noop
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
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input acc b0Idx b1Idx true false := by
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  -- Aux: state b0Idx, b1Idx values at the (false, false) intermediate Case3Input.
  have h_state_b0 : toyWindow2Case3Input acc b0Idx b1Idx false false b0Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_state_b1 : toyWindow2Case3Input acc b0Idx b1Idx false false b1Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  -- The X1-flipped state equals Case3Input acc ... false false.
  have h_state_X1 : update (toyWindow2Case3Input acc b0Idx b1Idx true false) b0Idx (!true)
                  = toyWindow2Case3Input acc b0Idx b1Idx false false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ (Ne.symm h_b0_ne_b1)]
    rfl
  -- Input b0Idx = true (for X1 read).
  have h_input_b0 : toyWindow2Case3Input acc b0Idx b1Idx true false b0Idx = true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  -- Peel the 5 layers of case-2 gate.
  unfold toyWindow2Case2Gate
  -- Convert layout-form mod-add to SQIR form (def-eq).
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input acc b0Idx b1Idx true false
  rw [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [h_input_b0]
  rw [h_state_X1]
  -- Now the state going into C1 is Case3Input acc b0Idx b1Idx false false.
  -- Apply ccx_guard_false_noop for C1.
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  -- Apply mod_add_state_eq_when_control_false_on_Case3Input for M.
  rw [Gate.applyNat_seq]
  rw [mod_add_state_eq_when_control_false_on_Case3Input bits N
        (tableValue a N 2 k 2) acc flagIdx b0Idx b1Idx false false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  -- Apply ccx_guard_false_noop for C2 (same guard).
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  -- Peel X2 and finish.
  rw [Gate.applyNat_X]
  rw [h_state_b0]
  -- After X2: update Case3Input ... false false) b0Idx (!false) = Case3Input ... true false.
  unfold toyWindow2Case3Input
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ (Ne.symm h_b0_ne_b1)]
  rfl

/-- **Case-2 no-op state_eq on (F, F) input** — Case 2 fires only on
(F, T). For input (F, F), the X1 normalization makes b0Idx internally
true, b1Idx remains false. The CCX guard (true ∧ false) is false, so
the inner C1-M-C2 sequence is identity, and the outer X-flip restores. -/
theorem toyWindow2Case2Gate_state_eq_FF_noop
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
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false := by
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  -- Aux: state b0Idx, b1Idx values at the (true, false) intermediate Case3Input.
  have h_state_b0 : toyWindow2Case3Input acc b0Idx b1Idx true false b0Idx = true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_state_b1 : toyWindow2Case3Input acc b0Idx b1Idx true false b1Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  -- The X1-flipped state equals Case3Input acc ... true false.
  have h_state_X1 : update (toyWindow2Case3Input acc b0Idx b1Idx false false) b0Idx (!false)
                  = toyWindow2Case3Input acc b0Idx b1Idx true false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ (Ne.symm h_b0_ne_b1)]
    rfl
  -- Input b0Idx = false (for X1 read).
  have h_input_b0 : toyWindow2Case3Input acc b0Idx b1Idx false false b0Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  -- Peel the 5 layers of case-2 gate.
  unfold toyWindow2Case2Gate
  -- Convert layout-form mod-add to SQIR form (def-eq).
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false
  rw [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [h_input_b0]
  rw [h_state_X1]
  -- Now the state going into C1 is Case3Input acc b0Idx b1Idx true false.
  -- Apply ccx_guard_false_noop for C1.
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  -- Apply mod_add_state_eq_when_control_false_on_Case3Input for M.
  rw [Gate.applyNat_seq]
  rw [mod_add_state_eq_when_control_false_on_Case3Input bits N
        (tableValue a N 2 k 2) acc flagIdx b0Idx b1Idx true false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  -- Apply ccx_guard_false_noop for C2 (same guard).
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  -- Peel X2 and finish.
  rw [Gate.applyNat_X]
  rw [h_state_b0]
  -- After X2: update Case3Input ... true false) b0Idx (!true) = Case3Input ... false false.
  unfold toyWindow2Case3Input
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ (Ne.symm h_b0_ne_b1)]
  rfl

/-- **Case-2 unified state_eq** — for arbitrary `(b0, b1)`, dispatches
to the firing theorem (`toyWindow2Case2Gate_state_eq`) when `(!b0) && b1`
holds, and to the appropriate no-op theorem otherwise. -/
theorem toyWindow2Case2Gate_state_eq_unified
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
      = toyWindow2Case3Input
          (if (!b0) && b1 then (acc + tableValue a N 2 k 2) % N else acc)
          b0Idx b1Idx b0 b1 := by
  match b0, b1 with
  | true, true =>
    show Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input acc b0Idx b1Idx true true
    exact toyWindow2Case2Gate_state_eq_TT_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | true, false =>
    show Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input acc b0Idx b1Idx true false
    exact toyWindow2Case2Gate_state_eq_TF_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | false, true =>
    show Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input ((acc + tableValue a N 2 k 2) % N)
          b0Idx b1Idx false true
    exact toyWindow2Case2Gate_state_eq bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | false, false =>
    show Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false
    exact toyWindow2Case2Gate_state_eq_FF_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag


end Windowed
end VerifiedShor
