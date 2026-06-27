/- ToyWindow2CaseNoOpHelper — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.ToyWindow2Case3StateEquality

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ### R7d^x: full state equality for case-3 gate

Funext-assembly theorem combining all nine per-position helpers
(R7d^v through R7d^ix).  This is the compositional building block
needed for the eventual `toyWindow2SelectedAddGate_correct`. -/

/-- **Full state equality for the case-3 selected-add gate.**

When applied to `toyWindow2Case3Input acc b0Idx b1Idx true true`,
the case-3 gate produces exactly
`toyWindow2Case3Input ((acc + tableValue a N 2 k 3) % N) b0Idx b1Idx true true`.

The accumulator advances by `tableValue a N 2 k 3` (mod N), the
two window bits remain `true`, the equality flag is restored, and
the entire SQIR/Cuccaro workspace is restored to `0` (carry-in,
internal flag, read register, top carry).

Proof: `funext q`, case-split on `q`'s position class (b0Idx,
b1Idx, flagIdx, above-layout, scalar workspace, parametric
target/read bit), dispatch each case to the appropriate R7d^v
through R7d^ix helper.  The proof mirrors `modmult_step_state_eq`
from ModMult.lean but is parameterized over `b0Idx`/`b1Idx`/
`flagIdx` rather than the SQIR multiplier control index. -/
theorem toyWindow2Case3Gate_state_eq
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
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input ((acc + tableValue a N 2 k 3) % N)
          b0Idx b1Idx true true := by
  funext q
  set acc' := (acc + tableValue a N 2 k 3) % N with hacc'_def
  have hacc'_lt_N : acc' < N := Nat.mod_lt _ hN_pos
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  -- From `flagIdx < 2 ∧ flagIdx ≠ 1`, `flagIdx = 0`.
  have h_flag_eq_zero : flagIdx = 0 := by omega
  -- Case on q = b1Idx.
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    rw [toyWindow2Case3Gate_preserves_b1Idx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  -- Case on q = b0Idx (q ≠ b1Idx).
  by_cases hq_b0 : q = b0Idx
  · rw [hq_b0]
    rw [toyWindow2Case3Gate_preserves_b0Idx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  -- Case on q = flagIdx (q ≠ b1Idx, q ≠ b0Idx).
  by_cases hq_flag : q = flagIdx
  · rw [hq_flag]
    rw [toyWindow2Case3Gate_restores_flagIdx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- Now q ≠ b0Idx, q ≠ b1Idx, q ≠ flagIdx.
  -- Simplify the RHS to `cuccaro_input_F 2 false 0 acc' q`.
  have h_rhs :
      toyWindow2Case3Input acc' b0Idx b1Idx true true q
        = cuccaro_input_F 2 false 0 acc' q := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
  rw [h_rhs]
  -- Case on q ≥ 2 + 2*bits + 1 (above layout).
  by_cases hq_above : 2 + 2 * bits + 1 ≤ q
  · rw [toyWindow2Case3Gate_aboveLayoutFalse bits N a k acc flagIdx b0Idx b1Idx q
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
          hq_above hq_b0 hq_b1 hq_flag]
    exact (cuccaro_input_F_above_eq_false 2 bits acc' q hq_above hacc'_lt).symm
  push_neg at hq_above
  -- Now q < 2 + 2*bits + 1.
  -- Case q = 2 (carry-in).
  by_cases hq_2 : q = 2
  · subst hq_2
    rw [toyWindow2Case3Gate_carryInRestored bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    exact (cuccaro_input_F_at_c_in 2 false 0 acc').symm
  -- Case q = 1 (internal Cuccaro flag).
  by_cases hq_1 : q = 1
  · subst hq_1
    rw [toyWindow2Case3Gate_internalFlagFalse bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold cuccaro_input_F
    rw [if_pos (by omega : (1 : Nat) < 2)]
  -- Case q = 0 is excluded since q ≠ flagIdx = 0.
  by_cases hq_0 : q = 0
  · subst hq_0
    exact absurd h_flag_eq_zero.symm hq_flag
  -- Now q ≥ 3, q ≤ 2 + 2*bits.  Parity dispatch.
  by_cases h_q_odd : q % 2 = 1
  · -- Target bit: q = 2 + 2*((q-3)/2) + 1.
    have hi_lt : (q - 3) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
    rw [hq_eq]
    rw [toyWindow2Case3Gate_targetBit bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag ((q - 3) / 2) hi_lt]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc').symm
  · -- Read bit: q = 2 + 2*((q-4)/2) + 2.
    have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    rw [toyWindow2Case3Gate_readBit bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag ((q - 4) / 2) hi_lt]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc']
    exact (Nat.zero_testBit _).symm

/-! ### R7d^xi: case-1 read-value companion + full state equality

For the case-1 read-bit dispatch we need a companion theorem to
`toyWindow2Case1Gate_correct` proving the Cuccaro read register
remains 0 after the full case-1 gate (regardless of b0/b1).
Mirrors the case-1 `_correct` proof structurally but finishes
through `ControlledModAdd.clean_readZero` instead of
`clean_targetDecode`.

The full state-equality theorem then dispatches each q-position
inline.  We don't add separate per-position helpers (as for case
3); instead the dispatch is inlined in `_state_eq` to keep the
total line count bounded.  The X-flip on `b1Idx` is handled
specially in the q = b1Idx branch; for other q, the X-flips peel
trivially via `update_neq`. -/

/-- The case-1 gate leaves the Cuccaro read register at `0` after
the full sequence (independent of the window bits `b0`, `b1`).
Mirrors `toyWindow2Case1Gate_correct` structurally but routes
through `clean_readZero`. -/
theorem toyWindow2Case1Gate_readVal
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
        (Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = 0 := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change cuccaro_read_val bits 2
      (Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = 0
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b1Idx _ _ h_b1_out]
  rw [Gate.applyNat_CCX]
  rw [cuccaro_read_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_eq]
  rw [h_F0_b1]
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
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx (!b1) _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx b0 _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b1Idx (!b1) _ h_b1_out]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b0Idx b0 _ h_b0_out]
  exact ControlledModAdd.clean_readZero ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 1) acc flagIdx (b0 && !b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-1 gate's output is `false` at any position `q` above the
SQIR/Cuccaro layout (`q ≥ 2 + 2*bits + 1`) that is distinct from the
window bits `b0Idx`/`b1Idx` and the lookup equality flag `flagIdx`.
Mirrors `toyWindow2Case3Gate_aboveLayoutFalse` with two extra
`Gate.applyNat_X` peelings for the X-flip layers. -/
theorem toyWindow2Case1Gate_aboveLayoutFalse
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
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false) q = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_q_ne_one : q ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false) q
      = false
  simp only [Gate.applyNat_seq]
  -- Peel outer X (X2, last applied): writes b1Idx.
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b1]
  -- Peel outer CCX (C2): writes flagIdx.
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_flag]
  -- Peel inner CCX (C1) and compute its action.
  rw [Gate.applyNat_CCX]
  -- Peel inner X (X1): writes b1Idx.
  rw [Gate.applyNat_X]
  -- Substitute input reads.
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]
  rw [h_F0_b1]
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  -- Merge the double update on b1Idx via update_idem.
  rw [FormalRV.Framework.update_idem]
  -- Reorder updates to bring flagIdx innermost.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Push b1Idx, b0Idx outside mod-add and read through.
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b1]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b0]
  -- Now finish via the commute trick at q (same as case-3 aboveLayoutFalse).
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
      (tableValue a N 2 k 1) flagIdx q false
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true)
      h_q_out h_q_ne_one hq_ne_flag
  rw [h_in_eq] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q


end Windowed
end VerifiedShor
