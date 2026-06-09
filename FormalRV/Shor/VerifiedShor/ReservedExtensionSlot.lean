import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.McpAdapterInterface

namespace VerifiedShor
namespace MCPAdapter
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




/-! ### Level-3 layout structure

`MCPAdapterLayout` packages the adapter between the internal
multiplier register layout and the Shor-MCP-facing encoding
(`encodeDataZeroAnc`).  Data-level only; semantic theorems are
exposed as wrapper aliases on the SQIR/Cuccaro instance. -/
structure MCPAdapterLayout where
  /-- The underlying Level-2 multiplier-step layout. -/
  step                   : MultiplierStep.MultiplierStepLayout
  /-- Outer total dimension: `bits + ancilla`. -/
  totalDim               : Nat → Nat
  /-- Shor-MCP-facing input encoder: `|x⟩|0_anc⟩` packed
  big-endian. -/
  mcpEncode              : (bits anc x : Nat) → Nat → Bool
  /-- Shifted internal multiplier input encoder (positions
  `[0, bits)` reserved for the outer data register). -/
  shiftedMultInputEncode : (bits m acc : Nat) → Nat → Bool
  /-- Shift offset (the amount by which to shift the internal
  multiplier gate up — currently `bits`). -/
  shiftOffset            : Nat → Nat
  /-- Gate-level shift operator. -/
  shiftGate              : Nat → Gate → Gate
  /-- Adapter gate that maps the MCP encoding to the shifted
  internal layout (a register-reversal swap). -/
  encodeAdapter          : Nat → Gate

/-! ### SQIR/Cuccaro MCP adapter layout instance -/
def sqirCuccaroLayout : MCPAdapterLayout where
  step                   := MultiplierStep.sqirCuccaroLayout
  totalDim               := modmult_total_dim
  mcpEncode              := encodeDataZeroAnc
  shiftedMultInputEncode := mult_input_F_shifted
  shiftOffset            := fun bits => bits
  shiftGate              := Gate.shift
  encodeAdapter          := encode_to_mult_adapter

/-! ### Public aliases for MCP encoding facts -/

theorem sqirCuccaro_encode_data
    {n anc x i : Nat} (hx : x < 2^n) (hi : i < n) :
    encodeDataZeroAnc n anc x i
      = FormalRV.Framework.nat_to_funbool n x i :=
  encodeDataZeroAnc_data hx hi

theorem sqirCuccaro_encode_anc
    {n anc x j : Nat} (hx : x < 2^n) (hj : j < anc) :
    encodeDataZeroAnc n anc x (n + j) = false :=
  encodeDataZeroAnc_anc hx hj

theorem sqirCuccaro_encode_oob
    {n anc x i : Nat} (hanc_pos : 0 < anc) (hi : n + anc ≤ i) :
    encodeDataZeroAnc n anc x i = false :=
  encodeDataZeroAnc_oob hanc_pos hi

/-! ### Public aliases for shift facts (generic) -/

theorem shift_applyNat_at_lo
    (off : Nat) (g : Gate) (f : Nat → Bool) (q : Nat) (hq : q < off) :
    Gate.applyNat (Gate.shift off g) f q = f q :=
  Gate.applyNat_shift_at_lo off g f q hq

theorem shift_applyNat_at_hi
    (off : Nat) (g : Gate) (f : Nat → Bool) (q : Nat) (hq : off ≤ q) :
    Gate.applyNat (Gate.shift off g) f q
      = Gate.applyNat g (fun r => f (off + r)) (q - off) :=
  Gate.applyNat_shift_at_hi off g f q hq

theorem shift_wellTyped
    {off dim : Nat} {g : Gate} (h : Gate.WellTyped dim g) :
    Gate.WellTyped (off + dim) (Gate.shift off g) :=
  Gate.shift_wellTyped h

/-! ### Public aliases for adapter correctness -/

theorem sqirCuccaro_encodeAdapter_correct
    (bits x : Nat) (hbits : 1 ≤ bits) (hx : x < 2^bits) :
    Gate.applyNat (encode_to_mult_adapter bits)
        (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
      = mult_input_F_shifted bits x 0 :=
  encode_to_mult_adapter_correct bits x hbits hx

theorem sqirCuccaro_encodeAdapter_reverse
    (bits y : Nat) (hbits : 1 ≤ bits) (hy : y < 2^bits) :
    Gate.applyNat (encode_to_mult_adapter bits)
        (mult_input_F_shifted bits y 0)
      = encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) y :=
  encode_to_mult_adapter_reverse bits y hbits hy

theorem sqirCuccaro_encodeAdapter_wellTyped
    (bits : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (modmult_total_dim bits) (encode_to_mult_adapter bits) :=
  encode_to_mult_adapter_wellTyped bits hbits

/-! ### Public aliases for MCP-gate bridge facts

These re-export the R3 public `VerifiedShor.ModMul.*` theorems
through the `MCPAdapter` namespace so that the MCP adapter layer
is visibly the final bridge into `MultiplyCircuitProperty`. -/

theorem sqirCuccaro_gateMCP_apply_encode
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (ModMul.gateMCP bits N a ainv)
        (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) x)
      = encodeDataZeroAnc bits (ModMul.ancillaWidth bits) ((a * x) % N) :=
  ModMul.gateMCP_apply_encode bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv

theorem sqirCuccaro_gateMCP_wellTyped
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    Gate.WellTyped (ModMul.totalDim bits) (ModMul.gateMCP bits N a ainv) :=
  ModMul.gateMCP_wellTyped bits N a ainv hbits hN_pos hN hN2

theorem sqirCuccaro_satisfiesMultiplyCircuitProperty
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    FormalRV.SQIRPort.MultiplyCircuitProperty a N bits (ModMul.ancillaWidth bits)
      (Gate.toUCom (ModMul.totalDim bits) (ModMul.gateMCP bits N a ainv)) :=
  ModMul.satisfiesMultiplyCircuitProperty bits N a ainv hbits hN_pos hN hN2 h_ainv_le h_inv

/-! ### Smoke theorems -/

theorem sqirCuccaro_totalDim_eq (bits : Nat) :
    sqirCuccaroLayout.totalDim bits = modmult_total_dim bits := rfl

theorem sqirCuccaro_mcpEncode_eq (bits anc x : Nat) :
    sqirCuccaroLayout.mcpEncode bits anc x = encodeDataZeroAnc bits anc x := rfl

/-! ### MCP bridge via interface (Phase R6h — fallback wrappers)

These theorems lift the constant-multiplier theorem (R6g) and the
in-place wrapper to the MCP-encoding `MultiplyCircuitProperty`
bridge.  Like R6f/R6g, these are **fallback wrappers**: statement
uses MCP-adapter layout fields, proof routes through the existing
SQIR theorems. -/

theorem sqirCuccaro_inplace_candidate_state_eq_via_interface
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (modmult_inplace_candidate bits N a ainv)
        (MultiplierStep.sqirCuccaroLayout.multInputEncode bits x 0)
      = MultiplierStep.sqirCuccaroLayout.multInputEncode bits ((a * x) % N) 0 :=
  modmult_inplace_candidate_state_eq bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv

theorem sqirCuccaro_gateMCP_apply_encode_via_interfaces
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (ModMul.gateMCP bits N a ainv)
        (sqirCuccaroLayout.mcpEncode bits (ModMul.ancillaWidth bits) x)
      = sqirCuccaroLayout.mcpEncode bits (ModMul.ancillaWidth bits) ((a * x) % N) :=
  ModMul.gateMCP_apply_encode bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv

theorem sqirCuccaro_gateMCP_wellTyped_via_interfaces
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    Gate.WellTyped (sqirCuccaroLayout.totalDim bits)
      (ModMul.gateMCP bits N a ainv) :=
  ModMul.gateMCP_wellTyped bits N a ainv hbits hN_pos hN hN2

theorem sqirCuccaro_satisfiesMultiplyCircuitProperty_via_interfaces
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    FormalRV.SQIRPort.MultiplyCircuitProperty a N bits
      (ModMul.ancillaWidth bits)
      (Gate.toUCom (sqirCuccaroLayout.totalDim bits)
        (ModMul.gateMCP bits N a ainv)) :=
  ModMul.satisfiesMultiplyCircuitProperty bits N a ainv hbits hN_pos hN hN2 h_ainv_le h_inv

/-! ### MCP bridge — real interface routing (Phase R6h-real)

Replays each old SQIR proof step with the new R6g-real
constant-gate theorem (and its downstream consumers).

* In-place candidate: uses R6g-real const-gate ×2 + swap + arithmetic.
* In-place shifted: uses real in-place candidate via funext over the
  shift offset.
* MCP gate apply-encode: uses real shifted + adapter aliases.
* MCP gate wellTyped: composes adapter wellTyped + shifted wellTyped
  (neither forbidden).
* MultiplyCircuitProperty bridge: uses real apply-encode + real
  wellTyped through the `toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc`
  bridge.

None calls `modmult_const_gate_state_eq_from`,
`modmult_inplace_candidate_state_eq`,
`modmult_inplace_shifted_correct`,
`modmult_MCP_gate_apply_encode`, or
`modmult_MCP_gate_satisfies_MultiplyCircuitProperty`. -/

theorem sqirCuccaro_inplace_candidate_state_eq_real_sqir_form
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (modmult_inplace_candidate bits N a ainv)
        (modmult_input_F bits x 0)
      = modmult_input_F bits ((a * x) % N) 0 := by
  unfold modmult_inplace_candidate
  simp only [Gate.applyNat_seq]
  have hx_lt_pow : x < 2^bits := Nat.lt_of_lt_of_le hx hN
  rw [MultiplierStep.sqirCuccaro_const_gate_state_eq_from_real_sqir_form
        bits N a x 0 hbits hN_pos hN hN2 hN_pos hx_lt_pow]
  simp only [Nat.zero_add]
  have hax_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have hax_lt_pow : (a * x) % N < 2^bits := Nat.lt_of_lt_of_le hax_lt_N hN
  rw [modmult_swap_acc_mult_apply bits x ((a * x) % N) hbits hx_lt_pow hax_lt_pow]
  rw [MultiplierStep.sqirCuccaro_const_gate_state_eq_from_real_sqir_form
        bits N ((N - ainv) % N) ((a * x) % N) x hbits hN_pos hN hN2 hx hax_lt_pow]
  congr 1
  exact modmult_inverse_clear_arith N a ainv x hN_pos hx h_ainv_le h_inv

theorem sqirCuccaro_inplace_candidate_state_eq_real_via_interface
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (modmult_inplace_candidate bits N a ainv)
        (MultiplierStep.sqirCuccaroLayout.multInputEncode bits x 0)
      = MultiplierStep.sqirCuccaroLayout.multInputEncode bits ((a * x) % N) 0 :=
  sqirCuccaro_inplace_candidate_state_eq_real_sqir_form bits N a ainv x
    hbits hN_pos hN hN2 h_ainv_le hx h_inv

theorem sqirCuccaro_inplace_shifted_correct_real_via_interface
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (modmult_inplace_shifted bits N a ainv)
        (mult_input_F_shifted bits x 0)
      = mult_input_F_shifted bits ((a * x) % N) 0 := by
  unfold modmult_inplace_shifted
  funext q
  by_cases hq_lo : q < bits
  · rw [Gate.applyNat_shift_at_lo bits _ _ q hq_lo]
    rw [mult_input_F_shifted_below_bits bits x 0 q hq_lo]
    rw [mult_input_F_shifted_below_bits bits ((a * x) % N) 0 q hq_lo]
  · push_neg at hq_lo
    rw [Gate.applyNat_shift_at_hi bits _ _ q hq_lo]
    rw [mult_input_F_shifted_above_bits bits ((a * x) % N) 0 q hq_lo]
    have h_inner_eq : (fun r => mult_input_F_shifted bits x 0 (bits + r))
                    = modmult_input_F bits x 0 := by
      funext r
      rw [mult_input_F_shifted_above_bits bits x 0 (bits + r) (by omega)]
      congr 1; omega
    rw [h_inner_eq]
    rw [sqirCuccaro_inplace_candidate_state_eq_real_sqir_form bits N a ainv x
          hbits hN_pos hN hN2 h_ainv_le hx h_inv]

theorem sqirCuccaro_gateMCP_apply_encode_real_via_interfaces
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (ModMul.gateMCP bits N a ainv)
        (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) x)
      = encodeDataZeroAnc bits (ModMul.ancillaWidth bits) ((a * x) % N) := by
  show Gate.applyNat (modmult_MCP_gate bits N a ainv)
        (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
      = encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) ((a * x) % N)
  unfold modmult_MCP_gate
  simp only [Gate.applyNat_seq]
  have hx_lt_pow : x < 2^bits := Nat.lt_of_lt_of_le hx hN
  rw [sqirCuccaro_encodeAdapter_correct bits x hbits hx_lt_pow]
  rw [sqirCuccaro_inplace_shifted_correct_real_via_interface bits N a ainv x
        hbits hN_pos hN hN2 h_ainv_le hx h_inv]
  have h_ax_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have h_ax_lt_pow : (a * x) % N < 2^bits := Nat.lt_of_lt_of_le h_ax_lt_N hN
  exact sqirCuccaro_encodeAdapter_reverse bits ((a * x) % N) hbits h_ax_lt_pow

theorem sqirCuccaro_gateMCP_wellTyped_real_via_interfaces
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    Gate.WellTyped (sqirCuccaroLayout.totalDim bits)
      (ModMul.gateMCP bits N a ainv) := by
  show Gate.WellTyped (modmult_total_dim bits) (modmult_MCP_gate bits N a ainv)
  unfold modmult_MCP_gate
  refine ⟨?_, ?_, ?_⟩
  · exact sqirCuccaro_encodeAdapter_wellTyped bits hbits
  · exact modmult_inplace_shifted_wellTyped bits N a ainv hbits hN_pos hN hN2
  · exact sqirCuccaro_encodeAdapter_wellTyped bits hbits

theorem sqirCuccaro_satisfiesMultiplyCircuitProperty_real_via_interfaces
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    FormalRV.SQIRPort.MultiplyCircuitProperty a N bits
      (ModMul.ancillaWidth bits)
      (Gate.toUCom (sqirCuccaroLayout.totalDim bits)
        (ModMul.gateMCP bits N a ainv)) := by
  show FormalRV.SQIRPort.MultiplyCircuitProperty a N bits
        (sqir_modmult_rev_anc bits)
        (Gate.toUCom (modmult_total_dim bits) (modmult_MCP_gate bits N a ainv))
  unfold modmult_total_dim
  apply toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc
    (sqirCuccaro_gateMCP_wellTyped_real_via_interfaces bits N a ainv hbits hN_pos hN hN2)
    hN
  intro x hx
  exact sqirCuccaro_gateMCP_apply_encode_real_via_interfaces bits N a ainv x
    hbits hN_pos hN hN2 h_ainv_le hx h_inv

end MCPAdapter
end VerifiedShor
