/-
  FormalRV.PPM.Gadgets.ModMul.SqirModMulPPM — compiled-PPM semantic
  correctness for the SQIR-faithful (Cuccaro-lineage) in-place modular
  multiplier `modmult_MCP_gate`, against ANY `PPMCompilerSpec`.

  The arithmetic content is the sealed ModMult module's headline round-trip
  `modmult_MCP_gate_apply_encode : applyNat (modmult_MCP_gate …)
  (encodeDataZeroAnc … x) = encodeDataZeroAnc … ((a*x) % N)`; this file only
  composes it with the compiler contract.  The factory-grounded concrete
  instance of this statement is the existing
  `Shor/PPM/ShorModMulPPMFactoryE2E.shorModMul_compiles_to_PPM_with_factory`
  (via the alias `VerifiedShor.ModMul.gateMCP := modmult_MCP_gate`); the
  spec-parametric version here is what survives the Phase-D new-syntax
  compiler unchanged.

  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.Gadgets.CompilerContract
import FormalRV.Arithmetic.ModMult

namespace FormalRV.PPM.Gadgets.ModMulPPM

open FormalRV.Framework
open FormalRV.BQAlgo

/-- **The SQIR/Cuccaro-lineage modular multiplier, compiled by any contract
    compiler, observes `x ↦ (a·x) mod N`** on the encoded data register with
    clean ancillas. -/
theorem sqirModMul_compiles_to_PPM (S : PPMCompilerSpec)
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    S.Observes (S.compile (modmult_MCP_gate bits N a ainv))
      (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
      (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) ((a * x) % N)) := by
  have h := S.compile_observes (modmult_MCP_gate bits N a ainv)
      (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
  rwa [modmult_MCP_gate_apply_encode bits N a ainv x hbits hN_pos hN hN2
        h_ainv_le hx h_inv] at h

/-- Magic demand of the compiled multiplier = its Toffoli count (any compiler). -/
theorem sqirModMul_ppm_magic_demand (S : PPMCompilerSpec) (bits N a ainv : Nat) :
    S.magicDemand (S.compile (modmult_MCP_gate bits N a ainv))
      = FormalRV.Framework.CircuitToPPMFactoryProvision.gateCCXCount
          (modmult_MCP_gate bits N a ainv) :=
  S.compile_magicDemand _

end FormalRV.PPM.Gadgets.ModMulPPM
