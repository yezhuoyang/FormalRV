/-
  FormalRV.PPM.Gadgets.ModExp.SqirModExpPPM — per-ITERATE compiled-PPM
  semantic correctness for the SQIR-layout modular-exponentiation family
  `modexpFamilyMCP` (squared-power family over `modmult_MCP_gate`).

  ## What "modexp compiled to PPM" means here

  The modexp oracle family is, by construction, one multiplier Gate per
  exponent bit, lifted to `BaseUCom` for QPE:

      modexpFamilyMCP bits N a ainv i
        = Gate.toUCom … (modmult_MCP_gate bits N (a^(2^i) % N) (ainv^(2^i) % N))

  The QPE control structure stays at the unitary layer (the honest
  boundary); the PPM-compilable objects are the iterate Gates.  This file
  proves: FOR EVERY iterate `i`, the compiled PPM program of iterate `i`'s
  gate observes `x ↦ (a^(2^i) · x) mod N` — from the minimal hypotheses
  (`1 < N`, `a·ainv ≡ 1`), with the per-iterate inverse facts derived via
  `mul_pow_mod_one`.

  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.Gadgets.ModMul.SqirModMulPPM
import FormalRV.Arithmetic.ModExp.ModExpCorrectness

namespace FormalRV.PPM.Gadgets.ModExpPPM

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.PPM.Gadgets.ModMulPPM

/-- **Every iterate of the SQIR-layout modexp family, compiled by any
    contract compiler, observes `x ↦ (a^(2^i)·x) mod N`.**  The gate below
    is literally the iterate `modexpFamilyMCP bits N a ainv i` before its
    `Gate.toUCom` lift. -/
theorem sqirModExp_iterate_compiles_to_PPM (S : PPMCompilerSpec)
    (bits N a ainv i x : Nat) (hbits : 1 ≤ bits)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_N_gt_one : 1 < N)
    (h_inv : a * ainv % N = 1) (hx : x < N) :
    S.Observes
      (S.compile (modmult_MCP_gate bits N (a ^ 2 ^ i % N) (ainv ^ 2 ^ i % N)))
      (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
      (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits)
        ((a ^ 2 ^ i * x) % N)) := by
  have hN_pos : 0 < N := by omega
  have h := sqirModMul_compiles_to_PPM S bits N (a ^ 2 ^ i % N) (ainv ^ 2 ^ i % N)
      x hbits hN_pos hN hN2 (le_of_lt (Nat.mod_lt _ hN_pos)) hx
      (mul_pow_mod_one a ainv N (2 ^ i) h_N_gt_one h_inv)
  rwa [Nat.mod_mul_mod] at h

end FormalRV.PPM.Gadgets.ModExpPPM
