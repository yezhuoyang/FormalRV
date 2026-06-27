/- WindowedMultiplyAddSpecification — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.WindowedMultiplyAddSpecification.Case2NoOpReusable

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

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


end Windowed
end VerifiedShor
