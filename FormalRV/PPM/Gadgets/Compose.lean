/-
  FormalRV.PPM.Gadgets.Compose — COMPOSING the per-gadget compiled-PPM
  theorems back into full Shor, for BOTH verified modexp implementations,
  against ANY contract compiler.

  ## §1 Gadget composability witness

  `PPMCompilerSpec.seq_observes` says concatenated compiled programs observe
  chained semantics; §1 instantiates it: TWO multiplier gadget programs,
  concatenated as ONE concrete PPM syntax object, observe the two-step
  modular product.  This is the composition pattern by which the modexp
  pipeline is a single program.

  ## §2 Full Shor, per implementation

  For each modexp family the composition theorem conjoins, at the SAME
  parameters:
    (I)  the verified Shor order-finding success bound ≥ κ/(log₂N)⁴ run on
         that family, and
    (II) for EVERY iterate `i`, the compiled PPM program of iterate `i`'s
         gate observes `x ↦ (a^(2^i)·x) mod N` — every oracle call the QPE
         layer makes is PPM-realized, not just one representative instance
         (strengthens `shor_succeeds_with_ppm_realized_modmult`'s shape).

  Honest boundary (unchanged): QPE's Hadamard/rotation/measurement wrapper
  stays unitary (see `QPE/UnitaryPPMBoundary` for the seam theorem); success
  branch + named factory contracts as everywhere in this folder.

  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.Gadgets.ModExp.SqirModExpPPM
import FormalRV.PPM.Gadgets.ModExp.ShorOracleModExpPPM

namespace FormalRV.PPM.Gadgets.Compose

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.PPM.Gadgets.ModMulPPM
open FormalRV.PPM.Gadgets.ModExpPPM

/-! ## §1. Composability witness: two chained multiplier programs. -/

/-- **Two compiled multiplier gadgets, concatenated into ONE concrete PPM
    program, observe the chained product** `x ↦ (a₂·((a₁·x) mod N)) mod N`. -/
theorem sqirModMul_chain_compiles_to_PPM (S : PPMCompilerSpec)
    (bits N a₁ ainv₁ a₂ ainv₂ x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h1_le : ainv₁ ≤ N) (h1_inv : (a₁ * ainv₁) % N = 1)
    (h2_le : ainv₂ ≤ N) (h2_inv : (a₂ * ainv₂) % N = 1)
    (hx : x < N) :
    S.Observes
      (S.seqProg (S.compile (modmult_MCP_gate bits N a₁ ainv₁))
                 (S.compile (modmult_MCP_gate bits N a₂ ainv₂)))
      (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
      (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits)
        ((a₂ * ((a₁ * x) % N)) % N)) := by
  have h := S.seq_observes (modmult_MCP_gate bits N a₁ ainv₁)
      (modmult_MCP_gate bits N a₂ ainv₂)
      (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
  rw [modmult_MCP_gate_apply_encode bits N a₁ ainv₁ x hbits hN_pos hN hN2
        h1_le hx h1_inv,
      modmult_MCP_gate_apply_encode bits N a₂ ainv₂ ((a₁ * x) % N) hbits
        hN_pos hN hN2 h2_le (Nat.mod_lt _ hN_pos) h2_inv] at h
  exact h

/-! ## §2. Full Shor with every oracle iterate PPM-compiled. -/

/-- **Full Shor over the SQIR/Cuccaro modexp family**: success bound ∧ every
    iterate's gate compiled-PPM correct (any contract compiler). -/
theorem shor_succeeds_with_ppm_compiled_mcp_family (S : PPMCompilerSpec)
    (bits N a ainv m r : Nat)
    (hbits : 1 ≤ bits) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m bits)
    (h_N_gt_one : 1 < N) (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
        (sqir_modmult_rev_anc bits) (modexpFamilyMCP bits N a ainv)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
    ∧ ∀ i x, x < N →
        S.Observes
          (S.compile (modmult_MCP_gate bits N (a ^ 2 ^ i % N) (ainv ^ 2 ^ i % N)))
          (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
          (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits)
            ((a ^ 2 ^ i * x) % N)) := by
  refine ⟨Shor_correct_with_mcp_family bits N a ainv m r hbits (by omega) hN hN2
      h_basic (fun i => mul_pow_mod_one a ainv N (2 ^ i) h_N_gt_one h_inv), ?_⟩
  intro i x hx
  exact sqirModExp_iterate_compiles_to_PPM S bits N a ainv i x
    hbits hN hN2 h_N_gt_one h_inv hx

/-- **Full Shor over the Gidney/Shor-layout modexp family**: success bound ∧
    every iterate's gate compiled-PPM correct (any contract compiler). -/
theorem shor_succeeds_with_ppm_compiled_modexp_family (S : PPMCompilerSpec)
    (bits N a ainv multBits m r : Nat)
    (hbits : 1 ≤ bits) (hN : N ≤ 2 ^ bits)
    (h_multBits_le : multBits ≤ bits + 1) (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2 ^ multBits)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m multBits)
    (h_N_gt_one : 1 < N) (h_cop_two : Nat.Coprime 2 N)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m multBits
        (adder_n_qubits (bits + 1) + 1)
        (our_modmult_family bits N a ainv multBits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
    ∧ ∀ i x, x < N →
        S.Observes
          (S.compile (modMultInPlaceShor bits N (a ^ 2 ^ i % N)
            (ainv ^ 2 ^ i % N) multBits))
          (encodeDataZeroAnc multBits (adder_n_qubits (bits + 1) + 1) x)
          (encodeDataZeroAnc multBits (adder_n_qubits (bits + 1) + 1)
            ((a ^ 2 ^ i * x) % N)) := by
  refine ⟨Shor_correct_with_verified_modexp bits N a ainv multBits m r hbits
      (by omega) hN h_multBits_le h_multBits_pos h_N_le_pow_multBits h_basic
      h_N_gt_one h_cop_two h_inv, ?_⟩
  intro i x hx
  exact shorOracleModExp_iterate_compiles_to_PPM S bits N a ainv multBits i x
    hbits hN h_multBits_le h_multBits_pos h_N_le_pow_multBits
    h_N_gt_one h_cop_two h_inv hx

end FormalRV.PPM.Gadgets.Compose
