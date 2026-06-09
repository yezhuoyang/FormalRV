/-
  FormalRV.Arithmetic.ModMult.ShorOracle.Correctness
  Semantic correctness of the Shor-layout modmult: WellTyped, the encodeDataZeroAnc
  action (x -> a*x mod N), and the `MultiplyCircuitProperty` discharge that lets it
  serve as Shor's ModMulImpl oracle. HEADLINE: modMultInPlaceShor_MultiplyCircuitProperty.
-/
import FormalRV.Arithmetic.ModMult.ShorOracle.Def
import FormalRV.Arithmetic.MCPBridge

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.SQIRPort

/-- **WellTyped for `modMultInPlaceShor`.** -/
theorem modMultInPlaceShor_wellTyped
    (bits N a ainv multBits : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) (h_multBits_pos : 0 < multBits) :
    Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
      (modMultInPlaceShor bits N a ainv multBits) := by
  unfold modMultInPlaceShor
  have h_dim_pos : 0 < multBits + (adder_n_qubits (bits + 1) + 1) := by omega
  have h_A_le : 0 + multBits ≤ multBits + (adder_n_qubits (bits + 1) + 1) := by omega
  have h_B_le : adder_n_qubits (bits + 1) + multBits
               ≤ multBits + (adder_n_qubits (bits + 1) + 1) := by omega
  have h_disjoint :
      0 + multBits ≤ adder_n_qubits (bits + 1) ∨
      adder_n_qubits (bits + 1) + multBits ≤ 0 := by
    left; unfold adder_n_qubits; omega
  have h_swap_wt : Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
      (reverse_register_swap multBits 0 (adder_n_qubits (bits + 1))) :=
    reverse_register_swap_wellTyped _ multBits 0 (adder_n_qubits (bits + 1))
      h_dim_pos h_A_le h_B_le h_disjoint
  have h_inplace_wt : Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
      (modMultInPlace bits N a ainv multBits) :=
    modMultInPlace_wellTyped_at_shor_dim bits N a ainv multBits hbits h_multBits_le
  exact ⟨h_swap_wt, h_inplace_wt, h_swap_wt⟩


/-- **HEADLINE: Layout-converting in-place modular multiplier
correctness.**  Applied to `encodeDataZeroAnc multBits (adder_n_qubits
(bits+1) + 1) x`, the gate produces `encodeDataZeroAnc multBits
(adder_n_qubits (bits+1) + 1) ((a*x) % N)`.  This is the exact shape
required by `toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc`. -/
theorem modMultInPlaceShor_correct
    (bits N a ainv multBits x : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (h_multBits_le : multBits ≤ bits + 1)
    (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2^multBits)
    (ha_pos : 0 < a) (ha_lt : a < N)
    (hainv_pos : 0 < ainv) (hainv_lt : ainv < N)
    (h_inv : a * ainv % N = 1)
    (hx_lt : x < N)
    (h_const_pos_a : ∀ j, j < multBits → 0 < (a * 2^j) % N)
    (h_const_pos_inv : ∀ j, j < multBits → 0 < ((N - ainv) % N * 2^j) % N) :
    Gate.applyNat (modMultInPlaceShor bits N a ainv multBits)
                  (encodeDataZeroAnc multBits (adder_n_qubits (bits + 1) + 1) x)
    = encodeDataZeroAnc multBits (adder_n_qubits (bits + 1) + 1) ((a * x) % N) := by
  unfold modMultInPlaceShor
  rw [Gate.applyNat_seq]
  -- Step 1: SWAP converts encodeDataZeroAnc x to mult_state_init x.
  have hx_lt_pow : x < 2^multBits := lt_of_lt_of_le hx_lt h_N_le_pow_multBits
  rw [reverse_register_swap_encodeDataZeroAnc_to_mult_state_init
        bits multBits x hbits h_multBits_le h_multBits_pos hx_lt_pow]
  rw [Gate.applyNat_seq]
  -- Step 2: In-place multiplier on mult_state_init x.
  rw [modMultInPlace_correct bits N a ainv multBits x
        hbits hN_pos hN h_multBits_le h_N_le_pow_multBits
        ha_pos ha_lt hainv_pos hainv_lt h_inv hx_lt
        h_const_pos_a h_const_pos_inv]
  -- Step 3: SWAP converts mult_state_init ((a*x)%N) back to encodeDataZeroAnc.
  -- Note: mult_input_F bits multBits 0 y = mult_state_init bits multBits y by definition.
  have h_ax_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have h_ax_lt_pow : (a * x) % N < 2^multBits :=
    lt_of_lt_of_le h_ax_lt_N h_N_le_pow_multBits
  show Gate.applyNat _ (mult_state_init bits multBits ((a * x) % N)) = _
  exact reverse_register_swap_mult_state_init_to_encodeDataZeroAnc
          bits multBits ((a * x) % N) hbits h_multBits_le h_multBits_pos h_ax_lt_pow


/-- **HEADLINE: `modMultInPlaceShor` satisfies `MultiplyCircuitProperty`.**
The compiled `BaseUCom (multBits + (adder_n_qubits (bits+1) + 1))` from
`Gate.toUCom` satisfies the SQIR-shape modular-multiplication property
required by `Shor_correct_var` / `Shor_correct`.  This is the structural
Phase 6 obligation, blocked since Tick 10 (out-of-place vs in-place,
layout mismatch) and now closed via path (A). -/
theorem modMultInPlaceShor_MultiplyCircuitProperty
    (bits N a ainv multBits : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (h_multBits_le : multBits ≤ bits + 1)
    (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2^multBits)
    (ha_pos : 0 < a) (ha_lt : a < N)
    (hainv_pos : 0 < ainv) (hainv_lt : ainv < N)
    (h_inv : a * ainv % N = 1)
    (h_const_pos_a : ∀ j, j < multBits → 0 < (a * 2^j) % N)
    (h_const_pos_inv : ∀ j, j < multBits → 0 < ((N - ainv) % N * 2^j) % N) :
    FormalRV.SQIRPort.MultiplyCircuitProperty a N multBits
      (adder_n_qubits (bits + 1) + 1)
      (Gate.toUCom (multBits + (adder_n_qubits (bits + 1) + 1))
        (modMultInPlaceShor bits N a ainv multBits)) := by
  apply toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc
  · -- WellTyped at (multBits + anc).
    exact modMultInPlaceShor_wellTyped bits N a ainv multBits hbits
            h_multBits_le h_multBits_pos
  · -- N ≤ 2^multBits.
    exact h_N_le_pow_multBits
  · -- Boolean correctness for all x < N.
    intro x hx_lt
    exact modMultInPlaceShor_correct bits N a ainv multBits x
            hbits hN_pos hN h_multBits_le h_multBits_pos h_N_le_pow_multBits
            ha_pos ha_lt hainv_pos hainv_lt h_inv hx_lt
            h_const_pos_a h_const_pos_inv


end FormalRV.BQAlgo
