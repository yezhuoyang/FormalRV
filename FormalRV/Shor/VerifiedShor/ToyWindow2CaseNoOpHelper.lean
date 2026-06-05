import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.ToyWindow2Case3StateEquality

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
through R7d^ix helper.  The proof mirrors `sqir_modmult_step_state_eq`
from SQIRModMult.lean but is parameterized over `b0Idx`/`b1Idx`/
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
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx (!b1) _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
    sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
      (tableValue a N 2 k 1) flagIdx q false
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true)
      h_q_out h_q_ne_one hq_ne_flag
  rw [h_in_eq] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

/-! ### R7d^xi: case-1 per-position helpers (continued)

Following the case-3 skeleton (R7d^v–R7d^ix), case 1 needs analogous
per-position helpers.  Most adaptations require only that we add an
outer `Gate.applyNat_X` peel layer (for the X2 = `Gate.X b1Idx` applied
last) and handle the X1 = `Gate.X b1Idx` applied first.  For positions
q ≠ b1Idx, both X-flips peel via `update_neq`; the inner CCX/mod-add
reasoning then mirrors the case-3 helper.

The exception is q = b1Idx itself: the X-flips give net !(!false) = false. -/

/-- Case-1 preserves the value `true` at the window-0 bit position
`b0Idx`. -/
theorem toyWindow2Case1Gate_preserves_b0Idx
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
        (toyWindow2Case3Input acc b0Idx b1Idx true false) b0Idx = true := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false) b0Idx
      = true
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
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
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_eq]

/-- Case-1 gate's output at target-bit position `2 + 2*i + 1`
(for `i < bits`) equals the `i`-th bit of `(acc + tableValue a N 2 k 1) % N`.
Derived from `toyWindow2Case1Gate_correct` + bits_match converse. -/
theorem toyWindow2Case1Gate_targetBit
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
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false) (2 + 2 * i + 1)
      = ((acc + tableValue a N 2 k 1) % N).testBit i := by
  have h_correct := toyWindow2Case1Gate_correct bits N a k acc flagIdx b0Idx b1Idx
    true false hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  have h_target_decode :
      cuccaro_target_val bits 2
          (Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
            (toyWindow2Case3Input acc b0Idx b1Idx true false))
        = (acc + tableValue a N 2 k 1) % N := by
    simpa using h_correct
  have h_acc'_lt_N : (acc + tableValue a N 2 k 1) % N < N := Nat.mod_lt _ hN_pos
  have h_acc'_lt : (acc + tableValue a N 2 k 1) % N < 2^bits :=
    Nat.lt_of_lt_of_le h_acc'_lt_N hN
  exact cuccaro_target_val_eq_implies_bits_match bits 2 _ _ h_acc'_lt
    h_target_decode i hi

/-- Case-1 gate's output at read-bit position `2 + 2*i + 2`
(for `i < bits`) equals `false`. -/
theorem toyWindow2Case1Gate_readBit
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
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false) (2 + 2 * i + 2)
      = false := by
  have h_rd := toyWindow2Case1Gate_readVal bits N a k acc flagIdx b0Idx b1Idx
    true false hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
  have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd i hi
  rw [h_bit, Nat.zero_testBit]

/-! ### R7d^xi^b — case-1 b1Idx preservation

The case-1 gate's outer X-flip layers (X b1Idx applied first AND last)
make the b1Idx-preservation proof more subtle than the case-3 analog.
We use a layered peel-and-prove pattern:

1. Peel the final X (X2): reduces goal to proving the value at b1Idx
   just before X2 is `true`.
2. Peel the second CCX (C2): writes only flagIdx, so reading at b1Idx
   passes through via `update_neq`.
3. Use the SQIR commute lemma at b1Idx (which is outside the workspace,
   ≠ 1, ≠ flagIdx) to show the mod-add preserves the value at b1Idx.
4. Prove the value at b1Idx after `C1 ∘ X1` is `true`: peel C1 (writes
   flagIdx), peel X1 (flips b1Idx from `false` to `true`).

The key trick is `set state := (CCX ∘ X) input`-style abstraction
before invoking the commute lemma — this avoids the unification
failures from R7d^xi. -/

/-- Case-1 preserves the value `false` at the window-1 bit position
`b1Idx`. The X-flips give net !(!false) = false. -/
theorem toyWindow2Case1Gate_preserves_b1Idx
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
        (toyWindow2Case3Input acc b0Idx b1Idx true false) b1Idx = false := by
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  -- Step 1: unfold to SQIR form.
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false) b1Idx
      = false
  simp only [Gate.applyNat_seq]
  -- Step 2: peel the outermost X (X2 applied last in applyNat order).
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_eq]
  -- Goal: !((applyNat C2 (applyNat M (applyNat C1 (applyNat X1 input)))) b1Idx) = false
  -- Step 3: peel C2 (writes flagIdx ≠ b1Idx).
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
  -- Goal: !((applyNat M (applyNat C1 (applyNat X1 input))) b1Idx) = false
  -- Step 4: prove the inner state at b1Idx equals true.
  have h_state_b1 :
      Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b1Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)) b1Idx
        = true := by
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_eq]
    -- Goal: !((update (update F b0Idx true) b1Idx false) b1Idx) = true
    rw [FormalRV.Framework.update_eq]
    -- Goal: !false = true
    rfl
  -- Step 5: abstract the inner state.
  set state := Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.applyNat (Gate.X b1Idx)
                    (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false))
    with hstate_def
  -- h_state_b1: state b1Idx = true.
  -- Show: update state b1Idx true = state (no-op update).
  have h_in_eq : update state b1Idx true = state := by
    funext p
    by_cases hp : p = b1Idx
    · subst hp
      rw [FormalRV.Framework.update_eq]
      exact h_state_b1.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
  -- Use the SQIR commute lemma at b1Idx with v = true.
  have h_commute :=
    sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
      (tableValue a N 2 k 1) flagIdx b1Idx true state
      h_b1_out h_b1_ne_one h_b1_ne_flag
  -- h_commute : applyNat M (update state b1Idx true) = update (applyNat M state) b1Idx true
  rw [h_in_eq] at h_commute
  -- h_commute : applyNat M state = update (applyNat M state) b1Idx true
  have h_at := congr_fun h_commute b1Idx
  rw [FormalRV.Framework.update_eq] at h_at
  -- h_at : (applyNat M state) b1Idx = true
  rw [h_at]
  -- Goal: !true = false.
  rfl

/-! ### R7d^xi^c — remaining case-1 scalar helpers

Three helpers needed for the case-1 state_eq assembly:
- `_internalFlagFalse` (position 1, finishes through `clean_flagFalse`).
- `_carryInRestored` (position 2, finishes through
  `sqir_style_controlledModAddConst_gate_carry_in_restored`).
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
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
  exact sqir_style_controlledModAddConst_gate_carry_in_restored bits N
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
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
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
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)))
        b1Idx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
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
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)))
        flagIdx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx (!b0) _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b0]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
    sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
    sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1)]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1)]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
