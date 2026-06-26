/- ToyWindow2Case3StateEquality — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.ToyWindow2Case3StateEquality.Part1

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ### R7d'' — cases v=1 and v=2

For v=1 (binary 01, b0=true b1=false) and v=2 (binary 10, b0=false
b1=true), the equality test requires X-normalization of the
relevant bit before the CCX cascade.

* v=1 gate: `X b1Idx ; CCX b0 b1 flag ; modAdd[flag] ; CCX b0 b1 flag ; X b1Idx`
  After the first X, b1 becomes `!b1` so the CCX computes
  `b0 ∧ !b1`, which is true iff (b0, b1) = (true, false), i.e. v=1.
* v=2 gate: symmetric with X on `b0Idx`.

Correctness proof mirrors v=3 with three extra rewriting steps:
1. Strip the outermost X (outside workspace at b0Idx or b1Idx) via
   `cuccaro_target_val_update_outside_workspace`.
2. Compute the inner X-flip's effect on the relevant bit
   (`F0 b1Idx = b1` so `! F0 b1Idx = !b1`).
3. Merge the double-update at the flipped bit position via
   `Framework.update_idem`. -/

/-- Arithmetic helper: `tableValue` for v=1. -/
theorem tableValue_window2_v1_eq (a N k : Nat) :
    tableValue a N 2 k 1 = (a * 2^(k * 2) * 1) % N := rfl

/-- Arithmetic helper: `tableValue` for v=2. -/
theorem tableValue_window2_v2_eq (a N k : Nat) :
    tableValue a N 2 k 2 = (a * 2^(k * 2) * 2) % N := rfl

/-- Arithmetic helper: `windowedStepSpec` for v=1. -/
theorem windowedStepSpec_window2_v1
    (a N k acc : Nat) (_hN_pos : 0 < N) :
    windowedStepSpec a N 2 k acc 1 = (acc + tableValue a N 2 k 1) % N := by
  unfold windowedStepSpec
  rfl

/-- Arithmetic helper: `windowedStepSpec` for v=2. -/
theorem windowedStepSpec_window2_v2
    (a N k acc : Nat) (_hN_pos : 0 < N) :
    windowedStepSpec a N 2 k acc 2 = (acc + tableValue a N 2 k 2) % N := by
  unfold windowedStepSpec
  rfl

/-- One window step's selected-add gate for the v=1 case
(binary 01).  X-normalizes b1 before/after the CCX cascade. -/
noncomputable def toyWindow2Case1Gate
    (bits N a k : Nat) (flagIdx b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 1
  Gate.seq (Gate.X b1Idx)
    (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
      (Gate.seq (ControlledModAdd.sqirCuccaroImpl.gate bits N c flagIdx)
        (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.X b1Idx))))

/-- One window step's selected-add gate for the v=2 case
(binary 10).  X-normalizes b0 before/after the CCX cascade. -/
noncomputable def toyWindow2Case2Gate
    (bits N a k : Nat) (flagIdx b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 2
  Gate.seq (Gate.X b0Idx)
    (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
      (Gate.seq (ControlledModAdd.sqirCuccaroImpl.gate bits N c flagIdx)
        (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.X b0Idx))))

/-- **R7d'' — toy case-1 selected-add correctness.**

When v=1 (b0=true, b1=false), the target accumulator advances by
`tableValue a N 2 k 1`; otherwise unchanged.  Proof mirrors v=3
with the X-flip handling described above. -/
theorem toyWindow2Case1Gate_correct
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_target_val bits 2
        (Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = if b0 && !b1 then (acc + tableValue a N 2 k 1) % N else acc := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change cuccaro_target_val bits 2
      (Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = if b0 && !b1 then (acc + tableValue a N 2 k 1) % N else acc
  simp only [Gate.applyNat_seq]
  -- Outermost X(b1Idx): outside workspace.
  rw [Gate.applyNat_X]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b1Idx _ _ h_b1_out]
  -- Outer-second CCX: outside workspace (flagIdx).
  rw [Gate.applyNat_CCX]
  rw [cuccaro_target_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  -- Compute the inner CCX result, factoring through the inner X(b1Idx).
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  -- F0 reads.  Here F0 = update (update G b0Idx b0) b1Idx b1; we
  -- compute its values at the three positions, and also at b1Idx
  -- *after* the X-flip — which is just !b1 by update_idem.
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_eq]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F0_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- After the X-flip, the state at b1Idx is !b1; at b0Idx is b0; at flagIdx is false.
  rw [h_F0_b1]
  -- Now reads on (update F0 b1Idx (!b1)):
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b1Idx (!b1) b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b1Idx (!b1) b1Idx
        = !b1 := by
    rw [FormalRV.Framework.update_eq]
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b1Idx (!b1) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.false_xor]
  -- Merge the double-update at b1Idx via update_idem.
  rw [FormalRV.Framework.update_idem]
  -- Now: update (update (update G b0Idx b0) b1Idx (!b1)) flagIdx (b0 && !b1)
  -- Reorder via update_comm to bring flagIdx update closest to G.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Push b0Idx, b1Idx updates outside the mod-add.
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx (!b1) _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx b0 _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  -- Drop the outside-workspace updates from cuccaro_target_val.
  rw [cuccaro_target_val_update_outside_workspace bits 2 b1Idx (!b1) _ h_b1_out]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b0Idx b0 _ h_b0_out]
  -- Close via R4b clean_targetDecode.
  exact ControlledModAdd.clean_targetDecode ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 1) acc flagIdx (b0 && !b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- **R7d'' — toy case-2 selected-add correctness.**

When v=2 (b0=false, b1=true), the target accumulator advances by
`tableValue a N 2 k 2`; otherwise unchanged.  Symmetric to v=1
with X on b0Idx. -/
theorem toyWindow2Case2Gate_correct
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_target_val bits 2
        (Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = if !b0 && b1 then (acc + tableValue a N 2 k 2) % N else acc := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change cuccaro_target_val bits 2
      (Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = if !b0 && b1 then (acc + tableValue a N 2 k 2) % N else acc
  simp only [Gate.applyNat_seq]
  -- Outermost X(b0Idx): outside workspace.
  rw [Gate.applyNat_X]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b0Idx _ _ h_b0_out]
  -- Outer-second CCX: outside workspace (flagIdx).
  rw [Gate.applyNat_CCX]
  rw [cuccaro_target_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  -- Compute inner CCX result via inner X(b0Idx).
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  rw [h_F0_b0]
  -- Reads on (update F0 b0Idx (!b0)):
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
  -- For the case-2 gate, the b0Idx update sequence is:
  -- update (update G b0Idx b0) b1Idx b1 -> (X) -> update (update (update G b0Idx b0) b1Idx b1) b0Idx (!b0)
  -- Reorder to bring the b0Idx (!b0) update to the right place:
  --   = update (update (update G b1Idx b1) b0Idx b0) b0Idx (!b0)   -- commute b1 and b0
  --   = update (update G b1Idx b1) b0Idx (!b0)                       -- update_idem
  -- Then update flagIdx ctrl on top, then commute.  Let's do it directly:
  -- The current expression after rw is:
  --   update (update (update (update G b0Idx b0) b1Idx b1) b0Idx (!b0)) flagIdx (!b0 && b1)
  -- First commute: swap the outer b0Idx (!b0) with b1Idx b1:
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  -- Now: update (update (update (update G b0Idx b0) b0Idx (!b0)) b1Idx b1) flagIdx ...
  -- Merge the double-update at b0Idx:
  rw [FormalRV.Framework.update_idem]
  -- Now: update (update (update G b1Idx b1) b0Idx (!b0)) flagIdx (!b0 && b1)
  -- Wait — the update_idem merged the b0Idx updates that were at the
  -- innermost (b0Idx b0) and the middle (b0Idx (!b0)) wrapping the
  -- swapped b1Idx update.  So after the swap+idem, the order is:
  --   update (update (update G b1Idx b1) b0Idx (!b0)) flagIdx ctrl
  -- The outermost update under flagIdx is at b0Idx, not b1Idx.
  -- So we must first swap flagIdx past b0Idx, then past b1Idx.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  -- Push b0Idx, b1Idx updates outside the mod-add.  Outermost is b0Idx.
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx (!b0) _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx b1 _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  -- Drop the outside-workspace updates.  Outermost is b0Idx.
  rw [cuccaro_target_val_update_outside_workspace bits 2 b0Idx (!b0) _ h_b0_out]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b1Idx b1 _ h_b1_out]
  -- Close via R4b clean_targetDecode.
  exact ControlledModAdd.clean_targetDecode ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 2) acc flagIdx (!b0 && b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-! ### R7d''' — composed windowSize=2 selected-add gate

The composed gate runs all three nonzero-case selected-add gates in
sequence.  For any input window value `v ∈ {0, 1, 2, 3}`, exactly
one case fires (or none, for v=0), advancing the target accumulator
by `tableValue a N 2 k v` modulo `N`. -/

/-- Composed windowSize=2 selected-add gate: case1 ; case2 ; case3. -/
noncomputable def toyWindow2SelectedAddGate
    (bits N a k : Nat) (flagIdx b0Idx b1Idx : Nat) : Gate :=
  Gate.seq (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
    (Gate.seq (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
              (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx))

/-- Arithmetic helper: `windowedStepSpec` for v=0 reduces to `acc`
when `acc < N`. -/
theorem windowedStepSpec_window2_v0
    (a N k acc : Nat) (_hN_pos : 0 < N) (hacc : acc < N) :
    windowedStepSpec a N 2 k acc 0 = acc := by
  unfold windowedStepSpec
  rw [tableValue_zero, Nat.add_zero]
  exact Nat.mod_eq_of_lt hacc


end Windowed
end VerifiedShor
