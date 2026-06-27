/- ToyWindow2Case3StateEquality — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.ToyWindow2Case3StateEquality.CasesV1V2AndComposedGate

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ### R7d^v — case-3 gate window-bit preservation helpers

These per-position helpers prove that `toyWindow2Case3Gate` preserves
the values at the external multiplier register positions `b0Idx`
and `b1Idx`.  They are the cleanest "outside workspace" cases and
the first step toward the full state-equality theorem
`toyWindow2Case3Gate_state_eq` (deferred to a follow-up tick).

Proof pattern (used by both):
1. Unfold the gate's 3-gate seq structure.
2. `change` to convert layout-form mod-add to SQIR-form (def-eq).
3. `simp only [Gate.applyNat_seq]` to expose the nested `Gate.applyNat`s.
4. Peel the outer CCX via `Gate.applyNat_CCX` + `update_neq` (direction:
   `h_bX_ne_flag`, since the pattern is `update _ flagIdx _ bXIdx`).
5. Peel the inner CCX via `Gate.applyNat_CCX`.
6. Substitute input reads at the three positions.
7. Simplify `xor false (true && true) = true`.
8. Reorder updates via `update_comm` (twice) to bring flagIdx innermost.
9. Push b0Idx/b1Idx outside the mod-add via
   `style_controlledModAddConst_gate_commute_update_outside_fun`.
10. Finish with `update_eq`. -/

/-- The case-3 gate preserves the value `true` at the external
multiplier register position `b0Idx`. -/
theorem toyWindow2Case3Gate_preserves_b0Idx
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
        (toyWindow2Case3Input acc b0Idx b1Idx true true) b0Idx = true := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b0Idx
      = true
  simp only [Gate.applyNat_seq]
  -- Peel outer CCX (writes at flagIdx; we read at b0Idx).
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
  -- Peel inner CCX.
  rw [Gate.applyNat_CCX]
  -- Compute input's value at the three positions.
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
  -- xor false (true && true) = true.
  simp only [Bool.and_self, Bool.false_xor]
  -- Reorder updates: bring flagIdx update innermost.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- State is now: update (update (update G flagIdx true) b0Idx true) b1Idx true.
  -- Push b1Idx (outermost) outside the mod-add.
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  -- Read at b0Idx through outer b1Idx update (b0Idx ≠ b1Idx).
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
  -- Push b0Idx outside the mod-add.
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  -- Read at b0Idx via update_eq.
  rw [FormalRV.Framework.update_eq]

/-- The case-3 gate restores the equality flag at `flagIdx` to its
original value `false` after the full CCX/modadd/CCX cycle.

The proof tracks the state through all three stages:
1. After the inner CCX, flagIdx is set to `xor false (true && true) = true`.
2. After the mod-add, flagIdx is preserved at `true` (via R4b's
   `clean_controlPreserved`).
3. After the outer CCX, flagIdx becomes `xor true (true && true) = false`. -/
theorem toyWindow2Case3Gate_restores_flagIdx
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
        (toyWindow2Case3Input acc b0Idx b1Idx true true) flagIdx = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  -- Helper: the input's values at b0Idx, b1Idx, flagIdx.
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
  -- Inner state values (after mod-add ∘ CCX1 applied to input).
  -- We prove (a) MA b0Idx = true, (b) MA b1Idx = true, (c) MA flagIdx = true.
  -- Each follows the same skeleton as in `_preserves_b0Idx`.
  -- Set the inner expression abbreviation isn't ergonomic with simp/rw,
  -- so we inline each subproof.
  have h_MA_b0 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true))
        b0Idx = true := by
    rw [Gate.applyNat_CCX]
    rw [h_input_b0, h_input_b1, h_input_flag]
    simp only [Bool.and_self, Bool.false_xor]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_eq]
  have h_MA_b1 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true))
        b1Idx = true := by
    rw [Gate.applyNat_CCX]
    rw [h_input_b0, h_input_b1, h_input_flag]
    simp only [Bool.and_self, Bool.false_xor]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_eq]
  have h_MA_flag :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true))
        flagIdx = true := by
    rw [Gate.applyNat_CCX]
    rw [h_input_b0, h_input_b1, h_input_flag]
    simp only [Bool.and_self, Bool.false_xor]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    -- Goal: Gate.applyNat (...) (update (cuccaro_input_F 2 false 0 acc) flagIdx true) flagIdx = true
    -- This is R4b clean_controlPreserved on sqirCuccaroImpl.
    exact ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
      bits N (tableValue a N 2 k 3) acc flagIdx true
      hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
  -- Combine.
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) flagIdx
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_eq]
  rw [h_MA_b0, h_MA_b1, h_MA_flag]
  decide

/-- The case-3 gate preserves the value `true` at the external
multiplier register position `b1Idx`.  Symmetric to
`_preserves_b0Idx`. -/
theorem toyWindow2Case3Gate_preserves_b1Idx
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
        (toyWindow2Case3Input acc b0Idx b1Idx true true) b1Idx = true := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b1Idx
      = true
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
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
  -- State: update (update (update G flagIdx true) b0Idx true) b1Idx true.
  -- Push b1Idx (outermost) outside the mod-add, then read via update_eq.
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_eq]


end Windowed
end VerifiedShor
