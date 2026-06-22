/-
  Audit · cain-xu-2026 (arXiv:2603.28627) · PPM-LEVEL END-TO-END (Pauli-product measurement + distilled T)
  ════════════════════════════════════════════════════════════════════════════
  Lowering cain-xu's end-to-end Shor circuit ALL THE WAY DOWN TO THE PPM LAYER, with SEMANTIC
  correctness and DISTILLED T-states — reusing the verified `CircuitToPPM*` framework (no new
  infrastructure).  Pauli-based computation: the windowed modular-exponentiation Gate is compiled to a
  magic-aware PPM program (every Clifford CX/X → frame-update + Pauli measurement; every Toffoli/CCX →
  a `teleportCCX` consuming one certified, factory-distilled |T⟩), the |T⟩ pool is provisioned from a
  `TFactoryContract`, the program RUNS to completion, and its measured output OBSERVES the correct
  modular product `(a·y) mod N`.

  Reuse: `compileToMagicPPM_provisioned_decoder_transfer` (generic Gate → magic-PPM run whose decoded
  output = the gate's `applyNat` value) instantiated on the verified windowed mod-N multiplier
  (`windowedModNMulInPlace`, value `windowedModNMulInPlace_value`), plus `shorMagicDemand_eq_ccxCount`
  (distilled-T demand = Toffoli count).  The QPE/order-finding SUCCESS (≥ κ/(log₂N)⁴) and the
  whole-ladder Toffoli/T count are the gate-level `cainxu_modexp_endToEnd` / `cainxu_qpe_factors_N`; this
  file adds the PPM-layer realisation of the per-iterate modexp with magic.

  Honest boundary (the framework's, named): the abstract `teleportCCXRel` Clifford+T contract, physical
  T cultivation/distillation correctness, and the per-request failure probability are explicit carried
  contracts (`TFactoryContract`), not re-proven here — exactly as in `ShorModMulPPMFactoryE2E`.
-/
import FormalRV.PPM.QECBridge.CircuitToPPMFactoryProvision
import FormalRV.Arithmetic.Windowed.WindowedModNInPlace

namespace FormalRV.Audit.CainXu2026

open FormalRV.Framework
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMToffoliMagic
open FormalRV.Framework.CircuitToPPMFactoryProvision
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit

/-- **★ CAIN-XU MODEXP REALISED AT THE PPM LAYER (with distilled T-states). ★**  The verified windowed
    modular-exponentiation Gate `windowedModNMulInPlace` is compiled to a magic-aware PPM program and
    run on a factory-provisioned certified-|T⟩ pool:

      (1) SEMANTIC CORRECTNESS at PPM level — the program RUNS (`MagicPPMProgramRel`) and its measured
          output OBSERVES a state decoding to `(a·y) mod N` (the correct modular product), via the
          generic decoder transfer on the gate's verified `applyNat` value `windowedModNMulInPlace_value`;
      (2) DISTILLED-T ACCOUNTING — the certified-|T⟩ demand provisioned from the factory `F` equals the
          modexp Gate's Toffoli (CCX) count (`shorMagicDemand_eq_ccxCount`): one distilled |T⟩ per
          `teleportCCX`.

    So cain-xu's logical modexp is lowered to genuine Pauli-product measurements + distilled magic, with
    the Boolean result PROVEN correct — not merely a gate count.  (Success ≥ κ/(log₂N)⁴ and the
    whole-ladder counts are the gate-level capstones; this is the PPM realisation of one iterate.) -/
theorem cainxu_modexp_ppm_realized
    (F : TFactoryContract)
    (w bits a ainv N numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < N) (hainv : ainv < N) (hinv : a * ainv % N = 1) :
    (∃ σ' output,
      MagicPPMProgramRel F
        (compileArithmeticGateToMagicPPM (windowedModNMulInPlace w bits a ainv N numWin))
        (encodeWithPool (mulInputOf cuccaroAdder w bits numWin y)
          (factoryProvision F (shorMagicDemand (windowedModNMulInPlace w bits a ainv N numWin)))) σ'
      ∧ (magicBasisRefinesApplyNat F).observesBits σ' output
      ∧ decodeReg (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits output = a * y % N)
    ∧ shorMagicDemand (windowedModNMulInPlace w bits a ainv N numWin)
        = gateCCXCount (windowedModNMulInPlace w bits a ainv N numWin) :=
  ⟨compileToMagicPPM_provisioned_decoder_transfer F
      (windowedModNMulInPlace w bits a ainv N numWin)
      (decodeReg (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits)
      (mulInputOf cuccaroAdder w bits numWin y) (a * y % N)
      (windowedModNMulInPlace_value w bits a ainv N numWin y hw hbits hN_pos hN2 hy hainv hinv
        (mulInputOf cuccaroAdder w bits numWin y) (modNMulReady_mulInputOf w bits numWin y)),
   shorMagicDemand_eq_ccxCount _⟩

end FormalRV.Audit.CainXu2026
