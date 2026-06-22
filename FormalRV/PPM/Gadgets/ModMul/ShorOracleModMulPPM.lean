/-
  FormalRV.PPM.Gadgets.ModMul.ShorOracleModMulPPM — compiled-PPM semantic
  correctness for the SECOND modular multiplier: the Gidney-adder-based,
  Shor-layout in-place `modMultInPlaceShor`, against ANY `PPMCompilerSpec` —
  plus its factory-grounded concrete instance.

  This closes a gap: until now only the Cuccaro-lineage multiplier
  (`modmult_MCP_gate`) had a PPM end-to-end theorem
  (`ShorModMulPPMFactoryE2E`).  Both verified multiplier implementations now
  have one, per John's "support all existing implementations" directive.

  Arithmetic content: `modMultInPlaceShor_correct` (the sealed ModMult
  module's ShorOracle round-trip).  Honesty boundary: inherited unchanged
  from the compiler instance (success branch, named contracts).

  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.Gadgets.CompilerContract
import FormalRV.Arithmetic.ModMult

namespace FormalRV.PPM.Gadgets.ModMulPPM

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMToffoliMagic
open FormalRV.Framework.CircuitToPPMFactoryProvision

/-- **The Gidney-adder Shor-layout modular multiplier, compiled by any
    contract compiler, observes `x ↦ (a·x) mod N`** on the encoded data
    register with clean ancillas. -/
theorem shorOracleModMul_compiles_to_PPM (S : PPMCompilerSpec)
    (bits N a ainv multBits x : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits)
    (h_multBits_le : multBits ≤ bits + 1)
    (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2 ^ multBits)
    (ha_pos : 0 < a) (ha_lt : a < N)
    (hainv_pos : 0 < ainv) (hainv_lt : ainv < N)
    (h_inv : a * ainv % N = 1)
    (hx_lt : x < N)
    (h_const_pos_a : ∀ j, j < multBits → 0 < (a * 2 ^ j) % N)
    (h_const_pos_inv : ∀ j, j < multBits → 0 < ((N - ainv) % N * 2 ^ j) % N) :
    S.Observes (S.compile (modMultInPlaceShor bits N a ainv multBits))
      (encodeDataZeroAnc multBits (adder_n_qubits (bits + 1) + 1) x)
      (encodeDataZeroAnc multBits (adder_n_qubits (bits + 1) + 1) ((a * x) % N)) := by
  have h := S.compile_observes (modMultInPlaceShor bits N a ainv multBits)
      (encodeDataZeroAnc multBits (adder_n_qubits (bits + 1) + 1) x)
  rwa [modMultInPlaceShor_correct bits N a ainv multBits x hbits hN_pos hN
        h_multBits_le h_multBits_pos h_N_le_pow_multBits ha_pos ha_lt
        hainv_pos hainv_lt h_inv hx_lt h_const_pos_a h_const_pos_inv] at h

/-- **Factory-grounded instance (the second multiplier's E2E, new)**: the
    compiled magic-PPM program of `modMultInPlaceShor` runs to completion on
    a factory-provisioned certified-T pool and observes `(a·x) mod N`. -/
theorem shorOracleModMul_compiles_to_PPM_with_factory (F : TFactoryContract)
    (bits N a ainv multBits x : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits)
    (h_multBits_le : multBits ≤ bits + 1)
    (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2 ^ multBits)
    (ha_pos : 0 < a) (ha_lt : a < N)
    (hainv_pos : 0 < ainv) (hainv_lt : ainv < N)
    (h_inv : a * ainv % N = 1)
    (hx_lt : x < N)
    (h_const_pos_a : ∀ j, j < multBits → 0 < (a * 2 ^ j) % N)
    (h_const_pos_inv : ∀ j, j < multBits → 0 < ((N - ainv) % N * 2 ^ j) % N) :
    ∃ σ', MagicPPMProgramRel F
        (compileArithmeticGateToMagicPPM (modMultInPlaceShor bits N a ainv multBits))
        (encodeWithPool
          (encodeDataZeroAnc multBits (adder_n_qubits (bits + 1) + 1) x)
          (factoryProvision F
            (shorMagicDemand (modMultInPlaceShor bits N a ainv multBits)))) σ'
      ∧ (magicBasisRefinesApplyNat F).observesBits σ'
          (encodeDataZeroAnc multBits (adder_n_qubits (bits + 1) + 1) ((a * x) % N)) :=
  shorOracleModMul_compiles_to_PPM (magicFactoryCompiler F) bits N a ainv multBits x
    hbits hN_pos hN h_multBits_le h_multBits_pos h_N_le_pow_multBits ha_pos ha_lt
    hainv_pos hainv_lt h_inv hx_lt h_const_pos_a h_const_pos_inv

end FormalRV.PPM.Gadgets.ModMulPPM
