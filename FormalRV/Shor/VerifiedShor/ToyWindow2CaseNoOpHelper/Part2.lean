/- ToyWindow2CaseNoOpHelper — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.ToyWindow2CaseNoOpHelper.Part1

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

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
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
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
    style_controlledModAddConst_gate_commute_update_outside_fun bits N
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


end Windowed
end VerifiedShor
