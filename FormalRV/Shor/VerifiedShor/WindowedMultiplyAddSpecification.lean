import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.WindowedCaseUnifiedStateEq

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

/-! ## Phase R7d^xv — first reusable abstraction: CCX guard-false no-op

The "non-firing case-1 gate is identity" insight reduces to: when the
CCX's AND guard is false, the CCX update at flagIdx is a no-op. This
helper captures that fact in one line and will let case-2/case-3
non-firing proofs reuse it. -/

/-- **CCX guard-false no-op**: If the AND of the two control reads
on `state` is `false`, then applying the CCX at flagIdx is the
identity. The proof is one line via `update_self`. -/
theorem ccx_guard_false_noop
    (b0Idx b1Idx flagIdx : Nat) (state : Nat → Bool)
    (h_guard : (state b0Idx && state b1Idx) = false) :
    Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx) state = state := by
  rw [Gate.applyNat_CCX]
  rw [h_guard]
  simp only [Bool.xor_false]
  exact FormalRV.Framework.update_self state flagIdx

/-- **X-conjugate no-op**: If a gate is the identity on the X-flipped
state at position `q`, then the X-conjugated composition
`X q ∘ gate ∘ X q` is the identity on the original state. This
captures the case-N gate's X-normalization pattern when the inner
CCX-MOD-CCX subgate is a no-op. -/
theorem x_conjugate_noop
    (q : Nat) (gate : Gate) (state : Nat → Bool)
    (h_inner_noop : Gate.applyNat gate (update state q (!state q))
                  = update state q (!state q)) :
    Gate.applyNat (Gate.seq (Gate.X q) (Gate.seq gate (Gate.X q))) state = state := by
  simp only [Gate.applyNat_seq, Gate.applyNat_X]
  rw [h_inner_noop]
  rw [FormalRV.Framework.update_eq]
  simp only [Bool.not_not]
  rw [FormalRV.Framework.update_idem]
  exact FormalRV.Framework.update_self state q

/-- **Mod-add above-layout no-op**: M is identity on `cuccaro_input_F`
at any position `q` above the layout. This captures the most common
above-layout reasoning step in case-N noop proofs. -/
theorem mod_add_above_layout_noop_on_F
    (bits N c acc flagIdx q : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hacc : acc < N)
    (h_flag_lo : flagIdx < 2)
    (hq_above : 2 + 2 * bits + 1 ≤ q) (hq_ne_flag : q ≠ flagIdx) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c flagIdx 1)
        (cuccaro_input_F 2 false 0 acc) q
      = false := by
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
  have h_q_ne_one : q ≠ 1 := fun h => by omega
  have h_q_val : cuccaro_input_F 2 false 0 acc q = false :=
    cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt
  have h_F_self_q : update (cuccaro_input_F 2 false 0 acc) q false
                  = cuccaro_input_F 2 false 0 acc := by
    funext p
    by_cases hp : p = q
    · subst hp; rw [FormalRV.Framework.update_eq]; exact h_q_val.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
  have h_commute :=
    style_controlledModAddConst_gate_commute_update_outside_fun bits N
      c flagIdx q false
      (cuccaro_input_F 2 false 0 acc)
      h_q_out h_q_ne_one hq_ne_flag
  rw [h_F_self_q] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

/-- **Mod-add full state no-op on Case3Input** (control = false branch).

When applied to a `toyWindow2Case3Input acc b0Idx b1Idx b0 b1` state,
the controlled modular-add gate is the FULL-STATE identity (because
the input's flagIdx bit is `false` — the implicit control). This is
the most significant reusable helper for case-N noop proofs: it
captures the entire mod-add subtrace in the non-firing branch and
replaces ~150 lines of inline proof in each case-N noop.

Used in conjunction with `ccx_guard_false_noop` (CCXs) and
`x_conjugate_noop` (X-flips), the case-2/case-3 noop proofs
collapse from ~450 lines to ~150 lines each. -/
theorem mod_add_state_eq_when_control_false_on_Case3Input
    (bits N c acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c flagIdx 1)
        (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
      = toyWindow2Case3Input acc b0Idx b1Idx b0 b1 := by
  funext q
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  have h_flag_eq_zero : flagIdx = 0 := by omega
  have h_F_flag : cuccaro_input_F 2 false 0 acc flagIdx = false := by
    unfold cuccaro_input_F; rw [if_pos h_flag_lo]
  have h_F_self : update (cuccaro_input_F 2 false 0 acc) flagIdx false
                = cuccaro_input_F 2 false 0 acc := by
    funext p
    by_cases hp : p = flagIdx
    · subst hp; rw [FormalRV.Framework.update_eq]; exact h_F_flag.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
  unfold toyWindow2Case3Input
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        c flagIdx b1Idx b1 _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        c flagIdx b0Idx b0 _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    rw [FormalRV.Framework.update_eq, FormalRV.Framework.update_eq]
  by_cases hq_b0 : q = b0Idx
  · rw [hq_b0]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq, FormalRV.Framework.update_eq]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1,
      FormalRV.Framework.update_neq _ _ _ _ hq_b0,
      FormalRV.Framework.update_neq _ _ _ _ hq_b1,
      FormalRV.Framework.update_neq _ _ _ _ hq_b0]
  by_cases hq_flag : q = flagIdx
  · rw [hq_flag]
    conv_lhs => rw [← h_F_self]
    have h_clean : Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits 2 N c flagIdx 1)
        (update (cuccaro_input_F 2 false 0 acc) flagIdx false) flagIdx = false :=
      ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
        bits N c acc flagIdx false
        hbits hN_pos hN hN2 hc hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    rw [h_clean]
    exact h_F_flag.symm
  by_cases hq_above : 2 + 2 * bits + 1 ≤ q
  · rw [mod_add_above_layout_noop_on_F bits N c acc flagIdx q
        hbits hN_pos hN hN2 hc hacc h_flag_lo hq_above hq_flag]
    exact (cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt).symm
  push_neg at hq_above
  by_cases hq_2 : q = 2
  · subst hq_2
    conv_lhs => rw [← h_F_self]
    rw [style_controlledModAddConst_gate_carry_in_restored bits N
        c acc flagIdx false hbits hN_pos hN hN2 hc hacc h_flag_allowed h_flag_ne_1]
    exact (cuccaro_input_F_at_c_in 2 false 0 acc).symm
  by_cases hq_1 : q = 1
  · subst hq_1
    conv_lhs => rw [← h_F_self]
    have h_clean : Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits 2 N c flagIdx 1)
        (update (cuccaro_input_F 2 false 0 acc) flagIdx false) 1 = false :=
      ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
        bits N c acc flagIdx false
        hbits hN_pos hN hN2 hc hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    rw [h_clean]
    unfold cuccaro_input_F
    rw [if_pos (by omega : (1:Nat) < 2)]
  by_cases hq_0 : q = 0
  · subst hq_0
    exact absurd h_flag_eq_zero.symm hq_flag
  by_cases h_q_odd : q % 2 = 1
  · have hi_lt : (q - 3) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
    rw [hq_eq]
    conv_lhs => rw [← h_F_self]
    have h_clean := ControlledModAdd.clean_targetDecode ControlledModAdd.sqirCuccaroImpl
      bits N c acc flagIdx false
      hbits hN_pos hN hN2 hc hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    have h_target_decode : cuccaro_target_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c flagIdx 1)
          (update (cuccaro_input_F 2 false 0 acc) flagIdx false)) = acc := by
      simpa using h_clean
    have h_bit := cuccaro_target_val_eq_implies_bits_match bits 2 acc _ hacc_lt
      h_target_decode ((q - 3) / 2) hi_lt
    rw [h_bit]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc).symm
  · have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    conv_lhs => rw [← h_F_self]
    have h_clean := ControlledModAdd.clean_readZero ControlledModAdd.sqirCuccaroImpl
      bits N c acc flagIdx false
      hbits hN_pos hN hN2 hc hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    have h_read_zero : cuccaro_read_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c flagIdx 1)
          (update (cuccaro_input_F 2 false 0 acc) flagIdx false)) = 0 := by
      simpa using h_clean
    have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
    have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt
      h_read_zero ((q - 4) / 2) hi_lt
    rw [h_bit, Nat.zero_testBit]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc]
    exact (Nat.zero_testBit _).symm

/-! ## Phase R7d^xiv^d — case-1 unified state equality

Wrapper theorem covering all 4 (b0, b1) inputs via `match` dispatch:
- (true, false) → firing state_eq.
- (true, true), (false, true), (false, false) → no-op state_eq. -/

/-- **Unified case-1 state equality** covering all four (b0, b1)
input shapes. Dispatches to:
- `toyWindow2Case1Gate_state_eq` for `(true, false)` (firing).
- `toyWindow2Case1Gate_state_eq_TT_noop` for `(true, true)`.
- `toyWindow2Case1Gate_state_eq_FT_noop` for `(false, true)`.
- `toyWindow2Case1Gate_state_eq_FF_noop` for `(false, false)`. -/
theorem toyWindow2Case1Gate_state_eq_unified
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
      = toyWindow2Case3Input
          (if b0 && !b1 then (acc + tableValue a N 2 k 1) % N else acc)
          b0Idx b1Idx b0 b1 := by
  match b0, b1 with
  | true, false =>
    show Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input ((acc + tableValue a N 2 k 1) % N)
          b0Idx b1Idx true false
    exact toyWindow2Case1Gate_state_eq bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | true, true =>
    show Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input acc b0Idx b1Idx true true
    exact toyWindow2Case1Gate_state_eq_TT_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | false, true =>
    show Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input acc b0Idx b1Idx false true
    exact toyWindow2Case1Gate_state_eq_FT_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | false, false =>
    show Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false
    exact toyWindow2Case1Gate_state_eq_FF_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag

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

/-! ## Phase R7d^xviii — case-3 no-ops via reusable helpers

Case 3 fires only on `(b0=true, b1=true)`. Its gate has the form
`CCX-M-CCX` (no X-normalization), so each no-op proof reduces to
three reusable-helper applications:
- `ccx_guard_false_noop` on the first CCX (guard `b0 && b1 = false`),
- `mod_add_state_eq_when_control_false_on_Case3Input` on the modular
  add (flagIdx still false since CCX did not fire),
- `ccx_guard_false_noop` on the second CCX (same guard).

Each no-op proof is ~35 lines — even shorter than Case-2 no-ops
since Case 3 has no X-conjugation to peel. -/

/-- **Case-3 no-op state_eq on (T, F) input** — Case 3 fires only on
`(T, T)`. For input `(T, F)`, the CCX guard `true ∧ false = false` so
the inner mod-add sees `flagIdx = false`, the whole gate no-ops. -/
theorem toyWindow2Case3Gate_state_eq_TF_noop
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
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input acc b0Idx b1Idx true false := by
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  -- State values at input Case3Input ... true false.
  have h_state_b0 : toyWindow2Case3Input acc b0Idx b1Idx true false b0Idx = true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_state_b1 : toyWindow2Case3Input acc b0Idx b1Idx true false b1Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  -- Peel the 3 layers of case-3 gate.
  unfold toyWindow2Case3Gate
  -- Convert layout-form mod-add to SQIR form (def-eq).
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input acc b0Idx b1Idx true false
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  rw [Gate.applyNat_seq]
  rw [mod_add_state_eq_when_control_false_on_Case3Input bits N
        (tableValue a N 2 k 3) acc flagIdx b0Idx b1Idx true false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
        (by rw [h_state_b0, h_state_b1]; rfl)]

/-- **Case-3 no-op state_eq on (F, T) input** — Case 3 fires only on
`(T, T)`. For input `(F, T)`, the CCX guard `false ∧ true = false` so
the whole gate no-ops. -/
theorem toyWindow2Case3Gate_state_eq_FT_noop
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
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input acc b0Idx b1Idx false true := by
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  have h_state_b0 : toyWindow2Case3Input acc b0Idx b1Idx false true b0Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_state_b1 : toyWindow2Case3Input acc b0Idx b1Idx false true b1Idx = true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  unfold toyWindow2Case3Gate
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input acc b0Idx b1Idx false true
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  rw [Gate.applyNat_seq]
  rw [mod_add_state_eq_when_control_false_on_Case3Input bits N
        (tableValue a N 2 k 3) acc flagIdx b0Idx b1Idx false true
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
        (by rw [h_state_b0, h_state_b1]; rfl)]

/-- **Case-3 no-op state_eq on (F, F) input** — Case 3 fires only on
`(T, T)`. For input `(F, F)`, the CCX guard `false ∧ false = false`
so the whole gate no-ops. -/
theorem toyWindow2Case3Gate_state_eq_FF_noop
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
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false := by
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  have h_state_b0 : toyWindow2Case3Input acc b0Idx b1Idx false false b0Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_state_b1 : toyWindow2Case3Input acc b0Idx b1Idx false false b1Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  unfold toyWindow2Case3Gate
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  rw [Gate.applyNat_seq]
  rw [mod_add_state_eq_when_control_false_on_Case3Input bits N
        (tableValue a N 2 k 3) acc flagIdx b0Idx b1Idx false false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
        (by rw [h_state_b0, h_state_b1]; rfl)]

/-- **Case-3 unified state_eq** — for arbitrary `(b0, b1)`, dispatches
to the firing theorem (`toyWindow2Case3Gate_state_eq`) when `b0 && b1`
holds, and to the appropriate no-op theorem otherwise. -/
theorem toyWindow2Case3Gate_state_eq_unified
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
      = toyWindow2Case3Input
          (if b0 && b1 then (acc + tableValue a N 2 k 3) % N else acc)
          b0Idx b1Idx b0 b1 := by
  match b0, b1 with
  | true, true =>
    show Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input ((acc + tableValue a N 2 k 3) % N)
          b0Idx b1Idx true true
    exact toyWindow2Case3Gate_state_eq bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | true, false =>
    show Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input acc b0Idx b1Idx true false
    exact toyWindow2Case3Gate_state_eq_TF_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | false, true =>
    show Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input acc b0Idx b1Idx false true
    exact toyWindow2Case3Gate_state_eq_FT_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | false, false =>
    show Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false
    exact toyWindow2Case3Gate_state_eq_FF_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag

/-! ## Phase R7d^xix — composed selected-add correctness

Assembles the composed `toyWindow2SelectedAddGate` correctness theorem
via the three unified case state_eq theorems landed in R7d^xi^d,
R7d^xvii, and R7d^xviii. -/

/-- **Bridge: target_val on a `Case3Input` reduces to the accumulator**
when the window-bit indices are outside the Cuccaro workspace and the
accumulator fits within the data register. -/
theorem cuccaro_target_val_Case3Input
    (bits acc : Nat) (b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx)
    (h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx)
    (hacc_lt : acc < 2^bits) :
    cuccaro_target_val bits 2 (toyWindow2Case3Input acc b0Idx b1Idx b0 b1) = acc := by
  unfold toyWindow2Case3Input
  rw [cuccaro_target_val_update_outside_workspace bits 2 b1Idx _ _ h_b1_out]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b0Idx _ _ h_b0_out]
  exact cuccaro_target_val_input bits 2 0 acc false hacc_lt

/-- **R7d^xix — composed selected-add correctness.**

The windowSize=2 selected-add gate `case1 ; case2 ; case3` correctly
implements piecewise modular addition based on the window bits
`(b0, b1)`:
- `(F, F)` (v=0): accumulator unchanged.
- `(T, F)` (v=1): adds `tableValue a N 2 k 1`.
- `(F, T)` (v=2): adds `tableValue a N 2 k 2`.
- `(T, T)` (v=3): adds `tableValue a N 2 k 3`.

Proof is a pure composition of the three unified case state_eq theorems
plus the Case3Input → accumulator bridge. No internal gate machinery
is re-derived. -/
theorem toyWindow2SelectedAddGate_correct
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
        (Gate.applyNat (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = if b0 && b1 then (acc + tableValue a N 2 k 3) % N
        else if !b0 && b1 then (acc + tableValue a N 2 k 2) % N
        else if b0 && !b1 then (acc + tableValue a N 2 k 1) % N
        else acc := by
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  unfold toyWindow2SelectedAddGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  -- Apply Case 1 unified.
  rw [toyWindow2Case1Gate_state_eq_unified bits N a k acc flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  -- Intermediate accumulator after Case 1.
  set acc1 := if b0 && !b1 then (acc + tableValue a N 2 k 1) % N else acc with h_acc1_def
  have h_acc1_lt : acc1 < N := by
    rw [h_acc1_def]
    split
    · exact Nat.mod_lt _ hN_pos
    · exact hacc
  -- Apply Case 2 unified at acc1.
  rw [toyWindow2Case2Gate_state_eq_unified bits N a k acc1 flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 h_acc1_lt h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  set acc2 := if !b0 && b1 then (acc1 + tableValue a N 2 k 2) % N else acc1 with h_acc2_def
  have h_acc2_lt : acc2 < N := by
    rw [h_acc2_def]
    split
    · exact Nat.mod_lt _ hN_pos
    · exact h_acc1_lt
  -- Apply Case 3 unified at acc2.
  rw [toyWindow2Case3Gate_state_eq_unified bits N a k acc2 flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 h_acc2_lt h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  set acc3 := if b0 && b1 then (acc2 + tableValue a N 2 k 3) % N else acc2 with h_acc3_def
  have h_acc3_lt : acc3 < N := by
    rw [h_acc3_def]
    split
    · exact Nat.mod_lt _ hN_pos
    · exact h_acc2_lt
  -- Convert cuccaro_target_val (Case3Input acc3 ...) to acc3.
  rw [cuccaro_target_val_Case3Input bits acc3 b0Idx b1Idx b0 b1
        h_b0_out h_b1_out (Nat.lt_of_lt_of_le h_acc3_lt hN)]
  -- Unfold the abbreviations and reduce by case split on (b0, b1).
  rw [h_acc3_def, h_acc2_def, h_acc1_def]
  cases b0 <;> cases b1 <;> simp

/-! ## Phase R7d^xx — spec-layer wrapper

Lifts the selected-add composition correctness theorem
(`toyWindow2SelectedAddGate_correct`) into the windowed arithmetic
spec layer. The wrapper expresses the RHS using the existing
`windowedStepSpec` definition (rather than a piecewise if-then-else),
making the toy gate compatible with downstream `WindowedLookupModMulSpec`
infrastructure. -/

/-- Encode two window bits to a numeric window value `v ∈ [0, 4)`:
`v = b0.toNat + 2 * b1.toNat`. Convention matches the per-case theorems:
- `(F, F)` → 0
- `(T, F)` → 1
- `(F, T)` → 2
- `(T, T)` → 3 -/
def windowBits2_to_v (b0 b1 : Bool) : Nat := b0.toNat + 2 * b1.toNat

/-- **Window-size-2 spec bridge.** `windowedStepSpec` at the encoded
value `windowBits2_to_v b0 b1` is the piecewise modular addition
matching the four `(b0, b1)` cases.

The proof dispatches each `(b0, b1)` to the matching pre-existing
`windowedStepSpec_window2_vN` lemma. -/
theorem windowedStepSpec_window2_bool
    (a N k acc : Nat) (b0 b1 : Bool) (hN_pos : 0 < N) (hacc : acc < N) :
    windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1)
      = if b0 && b1 then (acc + tableValue a N 2 k 3) % N
        else if !b0 && b1 then (acc + tableValue a N 2 k 2) % N
        else if b0 && !b1 then (acc + tableValue a N 2 k 1) % N
        else acc := by
  cases b0 <;> cases b1
  all_goals simp [windowBits2_to_v, Bool.toNat]
  · exact windowedStepSpec_window2_v0 a N k acc hN_pos hacc
  · exact windowedStepSpec_window2_v2 a N k acc hN_pos
  · exact windowedStepSpec_window2_v1 a N k acc hN_pos
  · exact windowedStepSpec_window2_v3 a N k acc hN_pos

/-- **R7d^xx — spec-form selected-add correctness.**

The composed selected-add gate's target-decode matches `windowedStepSpec`
evaluated at the encoded window value `windowBits2_to_v b0 b1`. This is
the bridge from the explicit composition theorem to the abstract
windowed-arithmetic spec layer. -/
theorem toyWindow2SelectedAddGate_correct_spec
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
        (Gate.applyNat (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1) := by
  rw [toyWindow2SelectedAddGate_correct bits N a k acc flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  exact (windowedStepSpec_window2_bool a N k acc b0 b1 hN_pos hacc).symm

/-- **`Window2SelectedAddSpec`**: the spec contract for a composed
windowSize=2 selected-add component.

An implementation provides a gate constructor `gate` parameterized by
width and window index, plus a correctness proof that the gate
implements the piecewise modular addition matching `windowedStepSpec`
on all four `(b0, b1)` inputs.

This is the composed analog of `Window2LookupCase3Spec` (which only
covers the v=3 firing case). Once an instance exists, composing across
windows `k = 0 .. numWindows N 2` yields a full windowSize=2 lookup
modular multiplier. -/
structure Window2SelectedAddSpec (a N : Nat) where
  /-- The composed selected-add gate constructor. -/
  gate : (bits k flagIdx b0Idx b1Idx : Nat) → Gate
  /-- Correctness: the gate implements `windowedStepSpec` on the
  encoded window value `windowBits2_to_v b0 b1` for arbitrary
  `(b0, b1) : Bool × Bool`. -/
  selectedAddCorrect :
    ∀ (bits k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool),
      1 ≤ bits → 0 < N → N ≤ 2^bits → 2 * N ≤ 2^bits →
      acc < N →
      flagIdx < 2 → flagIdx ≠ 1 → flagIdx < sqir_modmult_rev_anc bits →
      2 + 2 * bits + 1 ≤ b0Idx → 2 + 2 * bits + 1 ≤ b1Idx →
      b0Idx ≠ b1Idx → b0Idx ≠ flagIdx → b1Idx ≠ flagIdx →
      cuccaro_target_val bits 2
          (Gate.applyNat (gate bits k flagIdx b0Idx b1Idx)
            (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
        = windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1)

/-- **Toy windowSize=2 selected-add spec implementation.**

Wraps the CCX-based `toyWindow2SelectedAddGate` as a
`Window2SelectedAddSpec a N` instance via the R7d^xx wrapper theorem. -/
noncomputable def toyWindow2SelectedAddSpecImpl (a N : Nat) :
    Window2SelectedAddSpec a N where
  gate := fun bits k flagIdx b0Idx b1Idx =>
            toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx
  selectedAddCorrect := fun bits k acc flagIdx b0Idx b1Idx b0 b1
                            hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
                            h_flag_lt_dim h_b0_hi h_b1_hi h_b0_ne_b1
                            h_b0_ne_flag h_b1_ne_flag =>
    toyWindow2SelectedAddGate_correct_spec bits N a k acc flagIdx b0Idx b1Idx
      b0 b1 hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag

/-! ## Phase R7d^xxi — multi-window spec scaffold

Pure spec-level layer for iterating `windowedStepSpec` over multiple
windows. Defines a windowed-bit accessor, an iterated step function,
and the basic unfold/boundedness lemmas needed by the future
multi-window circuit correctness theorem. No circuit-level reasoning
yet — this layer is purely arithmetic. -/

/-- Per-window bit accessor: extracts the window value at window
index `k` from a pair of bit functions `b0 : Nat → Bool` (LSB) and
`b1 : Nat → Bool` (MSB). The window value lives in `[0, 4)`. -/
def windowBits2_at (b0 b1 : Nat → Bool) (k : Nat) : Nat :=
  windowBits2_to_v (b0 k) (b1 k)

/-- The boolean-pair window encoding always fits in `[0, 4)`. -/
theorem windowBits2_to_v_lt_4 (b0 b1 : Bool) :
    windowBits2_to_v b0 b1 < 4 := by
  unfold windowBits2_to_v
  cases b0 <;> cases b1 <;> simp [Bool.toNat]

/-- Multi-window analog: every window value extracted via
`windowBits2_at` is bounded above by `4 = 2^2`. -/
theorem windowBits2_at_lt_4 (b0 b1 : Nat → Bool) (k : Nat) :
    windowBits2_at b0 b1 k < 4 := windowBits2_to_v_lt_4 (b0 k) (b1 k)

/-- **Iterated windowed step** at window size 2: applies
`windowedStepSpec a N 2 k` for `k = 0, …, numWin - 1` starting from
`acc`, with the `k`-th step using window value
`windowBits2_at b0 b1 k`. Recursive on `numWin` for clean induction. -/
def windowedStepSpecIter2
    (a N : Nat) (b0 b1 : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc =>
      windowedStepSpec a N 2 n
        (windowedStepSpecIter2 a N b0 b1 n acc)
        (windowBits2_at b0 b1 n)

/-- Base unfold: 0 windows leaves the accumulator unchanged. -/
@[simp] theorem windowedStepSpecIter2_zero
    (a N acc : Nat) (b0 b1 : Nat → Bool) :
    windowedStepSpecIter2 a N b0 b1 0 acc = acc := rfl

/-- Step unfold: `numWin + 1` windows compose as `numWin` windows
followed by the `numWin`-th selected-add. -/
@[simp] theorem windowedStepSpecIter2_succ
    (a N numWin acc : Nat) (b0 b1 : Nat → Bool) :
    windowedStepSpecIter2 a N b0 b1 (numWin + 1) acc
      = windowedStepSpec a N 2 numWin
          (windowedStepSpecIter2 a N b0 b1 numWin acc)
          (windowBits2_at b0 b1 numWin) := rfl

/-- **Iterated boundedness.** Every intermediate accumulator stays
in `[0, N)`. The base case uses the initial bound `acc < N`; the
inductive case uses `windowedStepSpec_lt_N` (the modular reduction
guarantees output `< N` unconditionally). -/
theorem windowedStepSpecIter2_lt_N
    (a N : Nat) (b0 b1 : Nat → Bool) (numWin acc : Nat)
    (hN_pos : 0 < N) (hacc : acc < N) :
    windowedStepSpecIter2 a N b0 b1 numWin acc < N := by
  induction numWin with
  | zero => exact hacc
  | succ n _ =>
    rw [windowedStepSpecIter2_succ]
    exact windowedStepSpec_lt_N a N 2 n _ _ hN_pos

/-- **Circuit skeleton: multi-window selected-add gate sequence.**

Given a `Window2SelectedAddSpec` implementation, sequences `numWin`
applications of its `gate` constructor over windows `k = 0, …,
numWin - 1`, with `b0Idx k` / `b1Idx k` supplying the per-window
bit positions. Recursion on `numWin` mirrors `windowedStepSpecIter2`.

This is the gate-level analog of `windowedStepSpecIter2`; proving its
correctness theorem (gate output's `cuccaro_target_val` matches
`windowedStepSpecIter2`) is the next major milestone (deferred). -/
noncomputable def windowed2SelectedAddGate
    {a N : Nat} (impl : Window2SelectedAddSpec a N)
    (bits flagIdx : Nat) (b0Idx b1Idx : Nat → Nat) : Nat → Gate
  | 0 => Gate.I
  | n + 1 =>
      Gate.seq (windowed2SelectedAddGate impl bits flagIdx b0Idx b1Idx n)
        (impl.gate bits n flagIdx (b0Idx n) (b1Idx n))

/-- Base unfold for the gate skeleton: 0 windows is the identity. -/
@[simp] theorem windowed2SelectedAddGate_zero
    {a N : Nat} (impl : Window2SelectedAddSpec a N)
    (bits flagIdx : Nat) (b0Idx b1Idx : Nat → Nat) :
    windowed2SelectedAddGate impl bits flagIdx b0Idx b1Idx 0 = Gate.I := rfl

/-- Step unfold for the gate skeleton: `numWin + 1` windows compose
as `numWin` windows followed by the `numWin`-th selected-add. -/
@[simp] theorem windowed2SelectedAddGate_succ
    {a N : Nat} (impl : Window2SelectedAddSpec a N)
    (bits flagIdx numWin : Nat) (b0Idx b1Idx : Nat → Nat) :
    windowed2SelectedAddGate impl bits flagIdx b0Idx b1Idx (numWin + 1)
      = Gate.seq (windowed2SelectedAddGate impl bits flagIdx b0Idx b1Idx numWin)
                 (impl.gate bits numWin flagIdx (b0Idx numWin) (b1Idx numWin)) :=
  rfl

/-! ## Phase R7d^xxii — full-state selected-add spec

Strengthens the selected-add spec from target-decode (R7d^xx) to
full-state correctness. The composed gate maps a `Case3Input`
state to a `Case3Input` state with the accumulator updated
according to `windowedStepSpec` — preserving the input shape so
the next selected-add gate (at the next window) can chain.

This is the prerequisite for the multi-window circuit correctness
theorem: without preserved state shape, sequential `selectedAdd`
applications can't be composed via the spec interface. -/

/-- **Full-state selected-add correctness.** The composed
windowSize=2 selected-add gate produces a `Case3Input` state with
the accumulator advanced by `windowedStepSpec a N 2 k acc
(windowBits2_to_v b0 b1)`, leaving all other bit positions intact
in the `Case3Input` shape.

Proof mirrors `toyWindow2SelectedAddGate_correct` (R7d^xix) but
stops at the state level — no `cuccaro_target_val` extraction. -/
theorem toyWindow2SelectedAddGate_state_eq_spec
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
      = toyWindow2Case3Input
          (windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1))
          b0Idx b1Idx b0 b1 := by
  unfold toyWindow2SelectedAddGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  -- Apply Case 1 unified.
  rw [toyWindow2Case1Gate_state_eq_unified bits N a k acc flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  set acc1 := if b0 && !b1 then (acc + tableValue a N 2 k 1) % N else acc
    with h_acc1_def
  have h_acc1_lt : acc1 < N := by
    rw [h_acc1_def]; split
    · exact Nat.mod_lt _ hN_pos
    · exact hacc
  -- Apply Case 2 unified at acc1.
  rw [toyWindow2Case2Gate_state_eq_unified bits N a k acc1 flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 h_acc1_lt h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  set acc2 := if !b0 && b1 then (acc1 + tableValue a N 2 k 2) % N else acc1
    with h_acc2_def
  have h_acc2_lt : acc2 < N := by
    rw [h_acc2_def]; split
    · exact Nat.mod_lt _ hN_pos
    · exact h_acc1_lt
  -- Apply Case 3 unified at acc2.
  rw [toyWindow2Case3Gate_state_eq_unified bits N a k acc2 flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 h_acc2_lt h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  set acc3 := if b0 && b1 then (acc2 + tableValue a N 2 k 3) % N else acc2
    with h_acc3_def
  -- Show acc3 = windowedStepSpec ... by unfolding + bool-bridge + cases.
  have h_acc3_eq : acc3 = windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1) := by
    rw [h_acc3_def, h_acc2_def, h_acc1_def,
        windowedStepSpec_window2_bool a N k acc b0 b1 hN_pos hacc]
    cases b0 <;> cases b1 <;> simp
  rw [h_acc3_eq]

/-- **`Window2SelectedAddStateSpec`**: stronger spec contract for a
composed windowSize=2 selected-add component, exposing the full-state
correctness theorem instead of just target-decode correctness.

The state-level field is required for multi-window composition:
without it, two consecutive selected-add gates can't be chained
through the spec interface (target-decode alone leaves the
intermediate state's shape unknown).

Strictly stronger than `Window2SelectedAddSpec` — instances of
this structure imply `Window2SelectedAddSpec` instances (see
`Window2SelectedAddStateSpec.toSelectedAddSpec`). -/
structure Window2SelectedAddStateSpec (a N : Nat) where
  /-- The composed selected-add gate constructor. -/
  gate : (bits k flagIdx b0Idx b1Idx : Nat) → Gate
  /-- Full-state correctness: the gate transforms a `Case3Input`
  state to a `Case3Input` state with the accumulator updated per
  `windowedStepSpec`. All other bit positions are preserved. -/
  selectedAddStateEq :
    ∀ (bits k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool),
      1 ≤ bits → 0 < N → N ≤ 2^bits → 2 * N ≤ 2^bits →
      acc < N →
      flagIdx < 2 → flagIdx ≠ 1 → flagIdx < sqir_modmult_rev_anc bits →
      2 + 2 * bits + 1 ≤ b0Idx → 2 + 2 * bits + 1 ≤ b1Idx →
      b0Idx ≠ b1Idx → b0Idx ≠ flagIdx → b1Idx ≠ flagIdx →
      Gate.applyNat (gate bits k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
        = toyWindow2Case3Input
            (windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1))
            b0Idx b1Idx b0 b1

/-- A `Window2SelectedAddStateSpec` instance yields a
`Window2SelectedAddSpec` instance by composing the state-eq theorem
with `cuccaro_target_val_Case3Input`. The conversion is uniform
in the implementation. -/
noncomputable def Window2SelectedAddStateSpec.toSelectedAddSpec
    {a N : Nat} (impl : Window2SelectedAddStateSpec a N) :
    Window2SelectedAddSpec a N where
  gate := impl.gate
  selectedAddCorrect := by
    intro bits k acc flagIdx b0Idx b1Idx b0 b1
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
    have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
    have h_step_lt : windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1) < N :=
      windowedStepSpec_lt_N a N 2 k acc _ hN_pos
    rw [impl.selectedAddStateEq bits k acc flagIdx b0Idx b1Idx b0 b1
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    exact cuccaro_target_val_Case3Input bits _ b0Idx b1Idx b0 b1
      h_b0_out h_b1_out (Nat.lt_of_lt_of_le h_step_lt hN)

/-- **Toy windowSize=2 selected-add full-state spec implementation.**

Wraps the CCX-based `toyWindow2SelectedAddGate` as a
`Window2SelectedAddStateSpec a N` instance via
`toyWindow2SelectedAddGate_state_eq_spec`. -/
noncomputable def toyWindow2SelectedAddStateSpecImpl (a N : Nat) :
    Window2SelectedAddStateSpec a N where
  gate := fun bits k flagIdx b0Idx b1Idx =>
            toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx
  selectedAddStateEq := fun bits k acc flagIdx b0Idx b1Idx b0 b1
                            hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
                            h_flag_lt_dim h_b0_hi h_b1_hi h_b0_ne_b1
                            h_b0_ne_flag h_b1_ne_flag =>
    toyWindow2SelectedAddGate_state_eq_spec bits N a k acc flagIdx b0Idx b1Idx
      b0 b1 hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag

/-! ## Phase R7d^xxiii — multi-window input encoding

All-windows-at-once input encoding for the windowSize=2 selected-add
pipeline. Installs every window's b0/b1 bits simultaneously over the
Cuccaro accumulator base. Recursive on `numWin` for clean induction;
proves basic readback lemmas (for an arbitrary installed window),
target-extraction (cuccaro_target_val ignores the high window bits),
and workspace preservation (a frame-style lemma for any low-position
query). -/

/-- **Multi-window input encoding.** Installs the b0/b1 bits for
windows `0, …, numWin - 1` on top of a Cuccaro-formatted accumulator
encoding. Recursive on `numWin`. -/
def windowed2Input
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) :
    Nat → (Nat → Bool)
  | 0 => cuccaro_input_F 2 false 0 acc
  | n + 1 =>
      update
        (update (windowed2Input acc b0Idx b1Idx b0 b1 n) (b0Idx n) (b0 n))
        (b1Idx n) (b1 n)

/-- Zero windows: the encoding is just the Cuccaro accumulator base. -/
@[simp] theorem windowed2Input_zero
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) :
    windowed2Input acc b0Idx b1Idx b0 b1 0
      = cuccaro_input_F 2 false 0 acc := rfl

/-- Successor unfold: install window `n`'s bits on top of windows
`0 … n - 1`. -/
@[simp] theorem windowed2Input_succ
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) (n : Nat) :
    windowed2Input acc b0Idx b1Idx b0 b1 (n + 1)
      = update
          (update (windowed2Input acc b0Idx b1Idx b0 b1 n) (b0Idx n) (b0 n))
          (b1Idx n) (b1 n) := rfl

/-- Latest-window readback for `b1`: just the outermost update. -/
theorem windowed2Input_succ_read_b1
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) (n : Nat) :
    windowed2Input acc b0Idx b1Idx b0 b1 (n + 1) (b1Idx n) = b1 n := by
  rw [windowed2Input_succ]
  exact FormalRV.Framework.update_eq _ _ _

/-- Latest-window readback for `b0`: strip the outer `update` at
`b1Idx n` (requires `b0Idx n ≠ b1Idx n`), then read the inner one. -/
theorem windowed2Input_succ_read_b0
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) (n : Nat)
    (h_ne : b0Idx n ≠ b1Idx n) :
    windowed2Input acc b0Idx b1Idx b0 b1 (n + 1) (b0Idx n) = b0 n := by
  rw [windowed2Input_succ]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_ne]
  exact FormalRV.Framework.update_eq _ _ _

/-- **General `b0` readback** for any installed window `k < numWin`,
under universal index-disjointness. -/
theorem windowed2Input_read_b0
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_b0_distinct : ∀ i j, i ≠ j → b0Idx i ≠ b0Idx j)
    (h_b0_b1 : ∀ i j, b0Idx i ≠ b1Idx j) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin (b0Idx k) = b0 k := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2Input_succ]
    by_cases hkn : k = n
    · subst hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_b1 k k)]
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_b1 k n)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_distinct k n hkn)]
      exact ih hk_lt_n

/-- **General `b1` readback** for any installed window `k < numWin`. -/
theorem windowed2Input_read_b1
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_b1_distinct : ∀ i j, i ≠ j → b1Idx i ≠ b1Idx j)
    (h_b0_b1 : ∀ i j, b0Idx i ≠ b1Idx j) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin (b1Idx k) = b1 k := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2Input_succ]
    by_cases hkn : k = n
    · subst hkn
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b1_distinct k n hkn)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm (h_b0_b1 n k))]
      exact ih hk_lt_n

/-- **Target extraction.** The Cuccaro target decoder ignores all
window bits (they live above the workspace), recovering the input
accumulator. -/
theorem cuccaro_target_val_windowed2Input
    (bits acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) (numWin : Nat)
    (hacc_bits : acc < 2^bits)
    (h_hi0 : ∀ k, 2 + 2 * bits + 1 ≤ b0Idx k)
    (h_hi1 : ∀ k, 2 + 2 * bits + 1 ≤ b1Idx k) :
    cuccaro_target_val bits 2 (windowed2Input acc b0Idx b1Idx b0 b1 numWin)
      = acc := by
  induction numWin with
  | zero =>
    rw [windowed2Input_zero]
    exact cuccaro_target_val_input bits 2 0 acc false hacc_bits
  | succ n ih =>
    rw [windowed2Input_succ]
    rw [cuccaro_target_val_update_outside_workspace bits 2 (b1Idx n) (b1 n) _
          (Or.inr (h_hi1 n))]
    rw [cuccaro_target_val_update_outside_workspace bits 2 (b0Idx n) (b0 n) _
          (Or.inr (h_hi0 n))]
    exact ih

/-- **Workspace preservation (frame-style).** At any position `q` in
the Cuccaro workspace (`q < 2 + 2 * bits`), the multi-window encoding
agrees with the base accumulator encoding. Useful for proving that
gates operating only on the workspace + flag + active window bits
preserve `cuccaro_target_val` / `cuccaro_read_val` semantics. -/
theorem windowed2Input_at_low
    (acc bits q : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin : Nat) (h_q_low : q < 2 + 2 * bits + 1)
    (h_hi0 : ∀ k, 2 + 2 * bits + 1 ≤ b0Idx k)
    (h_hi1 : ∀ k, 2 + 2 * bits + 1 ≤ b1Idx k) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin q
      = cuccaro_input_F 2 false 0 acc q := by
  induction numWin with
  | zero => rfl
  | succ n ih =>
    rw [windowed2Input_succ]
    have h_q_ne_b1 : q ≠ b1Idx n := by
      have := h_hi1 n; omega
    have h_q_ne_b0 : q ≠ b0Idx n := by
      have := h_hi0 n; omega
    rw [FormalRV.Framework.update_neq _ _ _ _ h_q_ne_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_q_ne_b0]
    exact ih

/-! ## Phase R7d^xxix-L-1 — q_start-parametric windowed input layout

R7d^xxix-L-DESIGN-LOCK selected Option C2: shift the Cuccaro
workspace above the official data register so that the official data
register `q < bits` is disjoint from the arithmetic accumulator /
workspace.

This section introduces the q_start-parametric counterpart of
`windowed2Input`, bridges it to the old `q_start = 2` layout, and
proves the readback / zero-base / shifted-layout disjointness lemmas
needed by the (forthcoming L-2 / L-3) parametric K-stage.

**Exact accumulator-bit formula (from `cuccaro_input_F`):** the
accumulator's `k`-th bit lives at position `q_start + 2*k + 1`.
(With `q_start = 2`, this gives the old positions `2*k + 3 = 3, 5,
7, ...`; with `q_start = bits`, this gives the shifted positions
`bits + 1, bits + 3, ...`.) -/

/-- **q_start-parametric multi-window input encoding.** Same recursive
structure as `windowed2Input`, but the underlying Cuccaro base allows
an arbitrary `q_start`. The old `windowed2Input` is the
`q_start = 2` specialization (see `windowed2Input_eq_qstart_2`). -/
def windowed2Input_qstart
    (q_start acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) : Nat → (Nat → Bool)
  | 0 => cuccaro_input_F q_start false 0 acc
  | n + 1 =>
      update
        (update
          (windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 n)
          (b0Idx n) (b0 n))
        (b1Idx n) (b1 n)

/-- Zero-window unfold for the q_start-parametric encoding. -/
@[simp] theorem windowed2Input_qstart_zero
    (q_start acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) :
    windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 0
      = cuccaro_input_F q_start false 0 acc := rfl

/-- Successor unfold for the q_start-parametric encoding. -/
@[simp] theorem windowed2Input_qstart_succ
    (q_start acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) (n : Nat) :
    windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 (n + 1)
      = update
          (update
            (windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 n)
            (b0Idx n) (b0 n))
          (b1Idx n) (b1 n) := rfl

/-- **Bridge to the old q_start = 2 layout.** The original
`windowed2Input` is the `q_start = 2` specialization of
`windowed2Input_qstart`. Proven by induction on `numWin`, with both
recursive defs unfolding identically. -/
theorem windowed2Input_eq_qstart_2
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin : Nat) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin
      = windowed2Input_qstart 2 acc b0Idx b1Idx b0 b1 numWin := by
  induction numWin with
  | zero => rfl
  | succ n ih =>
    rw [windowed2Input_succ, windowed2Input_qstart_succ, ih]

end Windowed
end VerifiedShor
