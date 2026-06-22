/-
  Audit · Pinnacle (arXiv:2602.11457) · PPM-LEVEL END-TO-END (Pauli-product measurement + distilled T)
  ════════════════════════════════════════════════════════════════════════════
  Lowering Pinnacle's efficient RNS modular-exponentiation ALL THE WAY DOWN TO THE PPM layer, with
  SEMANTIC correctness and DISTILLED T-states — reusing the verified `CircuitToPPM*` framework (no new
  infrastructure).  Pauli-based computation: the CFS residue-fold Gate `residueFold` (the |P|-register
  Chevignard RNS modexp Pinnacle uses) is compiled to a magic-aware PPM program (Clifford CX/X →
  frame-update + Pauli measurement; every Toffoli → a `teleportCCX` consuming one certified,
  factory-distilled |T⟩), the |T⟩ pool is provisioned from a `TFactoryContract`, the program RUNS, and
  its measured output, CRT-reconstructed, OBSERVES the correct modular exponential `g^e mod N`.

  Reuse: `compileToMagicPPM_provisioned_decoder_transfer` (generic Gate → magic-PPM run whose decoded
  output = the gate's `applyNat` value) instantiated on `residueFold` with the CRT decoder and its
  verified value `residueFold_crt_correct`, plus `shorMagicDemand_eq_ccxCount` (distilled-T demand =
  Toffoli count).  The EH frequency-measurement SUCCESS (`pinnacle_eh_rns_shor_succeeds`) and the
  assembled Toffoli/T count are the gate-level capstones; this adds the PPM-layer realisation.

  Honest boundary (the framework's, named): the abstract `teleportCCXRel` Clifford+T contract, physical
  T cultivation/distillation correctness, and per-request failure probability are carried contracts
  (`TFactoryContract`), not re-proven; and the EH oracle entanglement remains the abstracted
  `twoRegOracleState` (see `FactoringClosure`).  This file is the PPM realisation of the RNS arithmetic.
-/
import FormalRV.PPM.QECBridge.CircuitToPPMFactoryProvision
import FormalRV.Shor.CFS.ResidueCRT

namespace FormalRV.Audit.Pinnacle

open scoped BigOperators
open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMToffoliMagic
open FormalRV.Framework.CircuitToPPMFactoryProvision
open FormalRV.BQAlgo
open FormalRV.CFS

/-- **★ PINNACLE RNS MODEXP REALISED AT THE PPM LAYER (with distilled T-states). ★**  The verified CFS
    residue-fold Gate `residueFold` (Pinnacle's |P|-register Chevignard RNS modular exponentiation) is
    compiled to a magic-aware PPM program and run on a factory-provisioned certified-|T⟩ pool:

      (1) SEMANTIC CORRECTNESS at PPM level — the program RUNS (`MagicPPMProgramRel`) and its measured
          output, READ OUT and CRT-reconstructed (the `∑_j decodeReg · crtBasis mod ∏P mod N`), equals
          `g^e mod N`, via the generic decoder transfer on the gate's verified value
          `residueFold_crt_correct`;
      (2) DISTILLED-T ACCOUNTING — the certified-|T⟩ demand provisioned from factory `F` equals the
          residue-fold Gate's Toffoli (CCX) count (`shorMagicDemand_eq_ccxCount`): one distilled |T⟩
          per `teleportCCX`.

    So Pinnacle's logical RNS modexp is lowered to genuine Pauli-product measurements + distilled magic,
    with the Boolean result PROVEN correct (`g^e mod N`) — not merely a gate count. -/
theorem pinnacle_modexp_ppm_realized
    (F : TFactoryContract)
    (P : Nat → Nat) (ainvss : Nat → Nat → Nat) (numP w bits numWin g N e m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hPok : ∀ j, j < numP → 1 < P j ∧ 2 * P j ≤ 2 ^ bits ∧
      ∀ k, k < m → ainvss j k < P j ∧ residueConst g N (P j) e k * ainvss j k % (P j) = 1)
    (hN : 2 ≤ N) (hm : 1 ≤ m) (he : e < 2 ^ m)
    (hco : ∀ i j : Fin numP, i ≠ j → Nat.Coprime (P i.val) (P j.val))
    (hL : N ^ m ≤ ∏ i : Fin numP, P i.val) :
    (∃ σ' output,
      MagicPPMProgramRel F
        (compileArithmeticGateToMagicPPM (residueFold P ainvss numP w bits numWin g N e m))
        (encodeWithPool (globalInput w bits numWin)
          (factoryProvision F (shorMagicDemand (residueFold P ainvss numP w bits numWin g N e m)))) σ'
      ∧ (magicBasisRefinesApplyNat F).observesBits σ' output
      ∧ (∑ j : Fin numP,
          (decodeReg (fun i => j.val * residueWidth w bits numWin + (1 + 2 * w + (2 * bits + 1) + i)) bits
            output) * crtBasis (fun i : Fin numP => P i.val) j) % (∏ i : Fin numP, P i.val) % N
        = g ^ e % N)
    ∧ shorMagicDemand (residueFold P ainvss numP w bits numWin g N e m)
        = gateCCXCount (residueFold P ainvss numP w bits numWin g N e m) :=
  ⟨compileToMagicPPM_provisioned_decoder_transfer F
      (residueFold P ainvss numP w bits numWin g N e m)
      (fun output => (∑ j : Fin numP,
          (decodeReg (fun i => j.val * residueWidth w bits numWin + (1 + 2 * w + (2 * bits + 1) + i)) bits
            output) * crtBasis (fun i : Fin numP => P i.val) j) % (∏ i : Fin numP, P i.val) % N)
      (globalInput w bits numWin) (g ^ e % N)
      (residueFold_crt_correct P ainvss numP w bits numWin g N e m hw hbits hPok hN hm he hco hL),
   shorMagicDemand_eq_ccxCount _⟩

end FormalRV.Audit.Pinnacle
