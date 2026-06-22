/-
  FormalRV.Shor.ShorModMulPPMFactoryE2E — the verified Shor
  modular multiplier, compiled to a magic-aware PPM program and
  executed on a T-factory / `RequestMagicState` system-call
  provisioning, with end-to-end SEMANTIC correctness.

  ## What this file delivers

  The verified logical arithmetic circuit for Shor's modular
  multiplier is `VerifiedShor.ModMul.gateMCP bits N a ainv : Gate`,
  with Boolean correctness

      gateMCP_apply_encode :
        Gate.applyNat (gateMCP bits N a ainv)
            (encodeDataZeroAnc bits (ancillaWidth bits) x)
          = encodeDataZeroAnc bits (ancillaWidth bits) ((a * x) % N).

  This file CLOSES THE GAP between that logical circuit and the
  PPM-with-T-factory layer.  Combining

    * the verified `Gate.applyNat` action of `gateMCP`
      (`gateMCP_apply_encode`), with
    * the generic provisioned total-correctness theorem
      `compileToMagicPPM_provisioned_run_observe`
      (`Framework.CircuitToPPMFactoryProvision`),

  we obtain `shorModMul_compiles_to_PPM_with_factory`:

      Compile `gateMCP bits N a ainv` to the extended magic-aware
      PPM program (CNOT/X via frame-update + Pauli measurement,
      every Toffoli via a `teleportCCX` certified-T teleportation),
      provision exactly `shorMagicDemand (gateMCP …)` certified-T
      tokens from a factory `F`, and the program RUNS to completion
      and its output OBSERVES
      `encodeDataZeroAnc bits (ancillaWidth bits) ((a * x) % N)`
      — the correct modular-multiplication result.

  We also expose:
    * `shorModMul_factory_resource` — #(`RequestMagicState`
      system calls) = #(certified-T tokens provisioned) =
      magic demand = Toffoli count of the verified multiplier.
    * `shorModMul_PPM_from_atomic_factory` — the same end-to-end
      result with the abstract `TFactoryContract` derived from a
      backend `AtomicFactorySpec` (with its `WellFormed` proof),
      grounding the magic supply in the cultivation/distillation
      resource model.

  ## Honesty boundary

  This is the SUCCESS-BRANCH semantic closure at the PPM/logical
  layer.  It does NOT prove (these remain explicit named
  contracts, per CLAUDE.md depth-of-formalization policy):

    * the internal Clifford+T circuit realising `teleportCCXRel`
      (the abstract Toffoli teleportation contract);
    * physical T-state cultivation / distillation correctness;
    * the QEC / lattice-surgery backend implementation of the
      factory and of `teleportCCX`;
    * the per-request failure probability (only the success
      branch + request count are modelled; the probability lives
      in `TFactoryContract.successProbLB_ppm` /
      `AtomicFactorySpec.success_probability_ppm`);
    * the QPE / Ekerå–Håstad layers above the modular multiplier
      (the SQIR-level success-probability theorem
      `VerifiedShor.correct` is a separate, unitary-level result).

  What it DOES establish is the precise statement the project was
  missing: the verified logical modular-multiplier circuit, once
  further compiled down to PPM with a T-cultivation / factory
  system call, is semantically correct (runs and computes the
  right Boolean output) — not merely a syntactic gate-count.
-/
import FormalRV.Shor.VerifiedShor
import FormalRV.PPM.QECBridge.CircuitToPPMFactoryProvision

namespace FormalRV.Shor.ShorModMulPPMFactoryE2E

open FormalRV.Framework
open FormalRV.Framework.Factory
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMToffoliMagic
open FormalRV.Framework.CircuitToPPMFactoryProvision
open FormalRV.BQAlgo
open VerifiedShor

/-! ## §1. The headline closure theorem.

    The verified modular multiplier compiles to a PPM program that,
    on a factory-provisioned certified-T pool, runs and observes the
    correct modular-multiplication output. -/

theorem shorModMul_compiles_to_PPM_with_factory
    (F : TFactoryContract)
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    ∃ σ',
      MagicPPMProgramRel F
        (compileArithmeticGateToMagicPPM (ModMul.gateMCP bits N a ainv))
        (encodeWithPool
          (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) x)
          (factoryProvision F
            (shorMagicDemand (ModMul.gateMCP bits N a ainv)))) σ'
      ∧ (magicBasisRefinesApplyNat F).observesBits σ'
          (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) ((a * x) % N)) := by
  obtain ⟨σ', hrun, hobs⟩ :=
    compileToMagicPPM_provisioned_run_observe F (ModMul.gateMCP bits N a ainv)
      (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) x)
  refine ⟨σ', hrun, ?_⟩
  rwa [ModMul.gateMCP_apply_encode bits N a ainv x hbits hN_pos hN hN2
        h_ainv_le hx h_inv] at hobs

/-! ## §2. Factory resource accounting for the verified multiplier.

    The number of factory `RequestMagicState` system calls equals the
    number of certified-T tokens provisioned equals the circuit's
    magic demand equals its Toffoli count. -/

theorem shorModMul_factory_resource
    (F : TFactoryContract) (zone period bits N a ainv : Nat) :
    (factoryRequestSchedule zone period
        (shorMagicDemand (ModMul.gateMCP bits N a ainv))).length
        = shorMagicDemand (ModMul.gateMCP bits N a ainv)
    ∧ (factoryProvision F
        (shorMagicDemand (ModMul.gateMCP bits N a ainv))).length
        = shorMagicDemand (ModMul.gateMCP bits N a ainv)
    ∧ shorMagicDemand (ModMul.gateMCP bits N a ainv)
        = gateCCXCount (ModMul.gateMCP bits N a ainv) :=
  ⟨factoryRequestSchedule_length _ _ _,
   factoryProvision_length _ _,
   shorMagicDemand_eq_ccxCount _⟩

/-! ## §3. End-to-end with a backend `AtomicFactorySpec`.

    The abstract PPM-layer factory `F` is derived from a backend
    cultivation/distillation `AtomicFactorySpec` (T-output, ppm
    success within range), yielding a `WellFormed` factory and the
    same provisioned semantic closure. -/

theorem shorModMul_PPM_from_atomic_factory
    (spec : AtomicFactorySpec) (fid : Nat)
    (hkind : spec.kind = MagicStateKind.T)
    (hsucc : spec.success_probability_ppm ≤ 1_000_000)
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    (TFactoryContract.ofAtomic spec fid).WellFormed
    ∧ ∃ σ',
        MagicPPMProgramRel (TFactoryContract.ofAtomic spec fid)
          (compileArithmeticGateToMagicPPM (ModMul.gateMCP bits N a ainv))
          (encodeWithPool
            (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) x)
            (factoryProvision (TFactoryContract.ofAtomic spec fid)
              (shorMagicDemand (ModMul.gateMCP bits N a ainv)))) σ'
        ∧ (magicBasisRefinesApplyNat (TFactoryContract.ofAtomic spec fid)).observesBits σ'
            (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) ((a * x) % N)) :=
  ⟨TFactoryContract.ofAtomic_wellFormed spec fid hkind hsucc,
   shorModMul_compiles_to_PPM_with_factory (TFactoryContract.ofAtomic spec fid)
     bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv⟩

/-! ## §4. Smoke instance: a concrete tiny modular multiplier.

    `N = 3`, `bits = 3` (so `2*N = 6 ≤ 8 = 2^3`), `a = 2`, `ainv = 2`
    (since `2*2 = 4 ≡ 1 mod 3`), `x = 1` (`a*x = 2 mod 3`).  Verifies
    all side conditions discharge and the closure theorem
    instantiates. -/

example (F : TFactoryContract) :
    ∃ σ',
      MagicPPMProgramRel F
        (compileArithmeticGateToMagicPPM (ModMul.gateMCP 3 3 2 2))
        (encodeWithPool
          (encodeDataZeroAnc 3 (ModMul.ancillaWidth 3) 1)
          (factoryProvision F (shorMagicDemand (ModMul.gateMCP 3 3 2 2)))) σ'
      ∧ (magicBasisRefinesApplyNat F).observesBits σ'
          (encodeDataZeroAnc 3 (ModMul.ancillaWidth 3) ((2 * 1) % 3)) :=
  shorModMul_compiles_to_PPM_with_factory F 3 3 2 2 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end FormalRV.Shor.ShorModMulPPMFactoryE2E
