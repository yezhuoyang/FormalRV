/- WindowedMultiplyAddSpecification — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.WindowedCaseUnifiedStateEq

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
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


end Windowed
end VerifiedShor
