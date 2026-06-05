/-
  FormalRV.Corpus.WindowedShorPPMFactoryE2E — descend the VERIFIED windowed Shor modular
  multiplier from the logical layer through the PPM (magic-state-factory) layer, with
  end-to-end SEMANTIC correctness, and expose the factory-request SysCall schedule that
  feeds the surface-code / lattice-surgery system layer.

  This is the windowed (Pipeline C) analogue of `ShorModMulPPMFactoryE2E` (which does the
  SQIR multiplier).  The connection reuses two already-proven pieces:

    * the windowed multiplier's Boolean round-trip
      `WindowedShorConnection.windowedInplaceModMulGate_roundTrip`
        : `Gate.applyNat (windowedInplaceModMulGate c N ainv bits) (encode x) = encode ((c*x)%N)`,
      and
    * the generic provisioned total-correctness bridge
      `compileToMagicPPM_provisioned_run_observe`
      (`Framework.CircuitToPPMFactoryProvision`).

  Result `windowed_compiles_to_PPM_with_factory`: the windowed multiplier compiles to the
  magic-aware PPM program (CNOT/X by frame update, every Toffoli by a certified-T
  teleportation), provisions exactly `shorMagicDemand` certified-T tokens from a factory `F`,
  RUNS to completion, and OBSERVES `encode ((c*x)%N)` — the correct modular-multiplication
  output.  Then `windowed_factory_resource` accounts the magic budget (= Toffoli count), and
  `windowed_factory_request_schedule` exposes the `List SysCall` of magic requests handed to
  the lattice-surgery system layer (length = magic demand).

  Honesty boundary (same as the SQIR E2E): the certified-T teleportation internals, physical
  T-cultivation/distillation, the per-request failure probability, and the full RSA-scale
  SysCall stream remain explicit named contracts in the lower layers — not re-proven here.
-/
import FormalRV.Shor.WindowedShorConnection
import FormalRV.PPM.CircuitToPPMFactoryProvision
import FormalRV.System.ScheduleInvariantsExplicit

namespace FormalRV.Corpus.WindowedShorPPMFactoryE2E

open FormalRV.Framework
open FormalRV.Framework.Architecture
open FormalRV.Framework.Factory
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMToffoliMagic
open FormalRV.Framework.CircuitToPPMFactoryProvision
open FormalRV.Framework.ScheduleInv
open FormalRV.BQAlgo
open FormalRV.BQAlgo.WindowedShorConnection

/-! ## §1. The headline closure: windowed multiplier ⟹ PPM-with-factory, semantically. -/

/-- **The verified windowed multiplier compiles to PPM-with-factory and computes the right
    output.**  On a factory-provisioned certified-T pool, the magic-aware PPM program for
    `windowedInplaceModMulGate c N ainv bits` runs and observes `encode ((c*x)%N)`. -/
theorem windowed_compiles_to_PPM_with_factory
    (F : TFactoryContract)
    (c N ainv bits anc x : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc_pos : 0 < anc)
    (hx : x < N) (h_ainv_le : ainv ≤ N) (h_inv : (c * ainv) % N = 1) :
    ∃ σ',
      MagicPPMProgramRel F
        (compileArithmeticGateToMagicPPM (windowedInplaceModMulGate c N ainv bits))
        (encodeWithPool
          (encodeDataZeroAnc bits anc x)
          (factoryProvision F
            (shorMagicDemand (windowedInplaceModMulGate c N ainv bits)))) σ'
      ∧ (magicBasisRefinesApplyNat F).observesBits σ'
          (encodeDataZeroAnc bits anc ((c * x) % N)) := by
  obtain ⟨σ', hrun, hobs⟩ :=
    compileToMagicPPM_provisioned_run_observe F (windowedInplaceModMulGate c N ainv bits)
      (encodeDataZeroAnc bits anc x)
  refine ⟨σ', hrun, ?_⟩
  rwa [windowedInplaceModMulGate_roundTrip c N ainv bits anc x
        hbits h_even hN_pos hN hN2 h_anc_pos hx h_ainv_le h_inv] at hobs

/-! ## §2. Factory resource accounting (magic budget = Toffoli count). -/

/-- The number of factory `RequestMagicState` system calls equals the number of certified-T
    tokens provisioned equals the windowed circuit's magic demand equals its `CCX` count. -/
theorem windowed_factory_resource
    (F : TFactoryContract) (zone period c N ainv bits : Nat) :
    (factoryRequestSchedule zone period
        (shorMagicDemand (windowedInplaceModMulGate c N ainv bits))).length
        = shorMagicDemand (windowedInplaceModMulGate c N ainv bits)
    ∧ (factoryProvision F
        (shorMagicDemand (windowedInplaceModMulGate c N ainv bits))).length
        = shorMagicDemand (windowedInplaceModMulGate c N ainv bits)
    ∧ shorMagicDemand (windowedInplaceModMulGate c N ainv bits)
        = gateCCXCount (windowedInplaceModMulGate c N ainv bits) :=
  ⟨factoryRequestSchedule_length _ _ _,
   factoryProvision_length _ _,
   shorMagicDemand_eq_ccxCount _⟩

/-! ## §3. The factory-request SysCall schedule handed to the lattice-surgery system layer.

    `factoryRequestSchedule` produces the `List SysCall` of `RequestMagicState` calls — the
    interface that the surface-code / lattice-surgery scheduling layer
    (`LatticeSurgeryPPMContract.PPMScheduleCert`, with its I1–I4 system invariants) validates.
    Its length is exactly the magic budget, i.e. the verified Toffoli count. -/
theorem windowed_factory_request_schedule
    (zone period c N ainv bits : Nat) :
    (factoryRequestSchedule zone period
        (shorMagicDemand (windowedInplaceModMulGate c N ainv bits))).length
      = gateCCXCount (windowedInplaceModMulGate c N ainv bits) := by
  rw [factoryRequestSchedule_length, shorMagicDemand_eq_ccxCount]

/-! ## §4. End-to-end with a backend `AtomicFactorySpec` (grounds the magic supply). -/

/-- The abstract PPM-layer factory `F` derived from a backend cultivation/distillation
    `AtomicFactorySpec` is `WellFormed`, and the windowed multiplier still compiles to PPM
    and observes the correct modular-multiplication output on its provisioned pool. -/
theorem windowed_PPM_from_atomic_factory
    (spec : AtomicFactorySpec) (fid : Nat)
    (hkind : spec.kind = MagicStateKind.T)
    (hsucc : spec.success_probability_ppm ≤ 1_000_000)
    (c N ainv bits anc x : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc_pos : 0 < anc)
    (hx : x < N) (h_ainv_le : ainv ≤ N) (h_inv : (c * ainv) % N = 1) :
    (TFactoryContract.ofAtomic spec fid).WellFormed
    ∧ ∃ σ',
        MagicPPMProgramRel (TFactoryContract.ofAtomic spec fid)
          (compileArithmeticGateToMagicPPM (windowedInplaceModMulGate c N ainv bits))
          (encodeWithPool
            (encodeDataZeroAnc bits anc x)
            (factoryProvision (TFactoryContract.ofAtomic spec fid)
              (shorMagicDemand (windowedInplaceModMulGate c N ainv bits)))) σ'
        ∧ (magicBasisRefinesApplyNat (TFactoryContract.ofAtomic spec fid)).observesBits σ'
            (encodeDataZeroAnc bits anc ((c * x) % N)) :=
  ⟨TFactoryContract.ofAtomic_wellFormed spec fid hkind hsucc,
   windowed_compiles_to_PPM_with_factory (TFactoryContract.ofAtomic spec fid)
     c N ainv bits anc x hbits h_even hN_pos hN hN2 h_anc_pos hx h_ainv_le h_inv⟩

/-! ## §5. Descending into the surface-code lattice-surgery scheduler.

    `factoryRequestSchedule` emits the windowed circuit's magic budget as a `List SysCall` of
    `RequestMagicState` calls — exactly the input the lattice-surgery system layer
    (`LatticeSurgeryPPMContract.PPMScheduleCert`) validates against the I1–I4 schedule
    invariants.  Here we (a) certify the emitted stream is a well-formed magic-request stream,
    and (b) show a representative windowed budget satisfies the surgery throughput invariant
    (paper I4) the surface-code scheduler enforces. -/

/-- Every SysCall the windowed circuit hands the surgery scheduler is a `RequestMagicState` to
    the factory zone — a well-formed magic-request stream, of length the verified Toffoli count. -/
theorem windowed_factory_requests_all_magic
    (zone period c N ainv bits : Nat) :
    (∀ sc ∈ factoryRequestSchedule zone period
        (shorMagicDemand (windowedInplaceModMulGate c N ainv bits)),
      sc.kind = SysCallKind.RequestMagicState zone)
    ∧ (factoryRequestSchedule zone period
        (shorMagicDemand (windowedInplaceModMulGate c N ainv bits))).length
        = gateCCXCount (windowedInplaceModMulGate c N ainv bits) :=
  ⟨factoryRequestSchedule_all_requestMagic _ _ _,
   by rw [factoryRequestSchedule_length, shorMagicDemand_eq_ccxCount]⟩

/-- **Reaches the surgery scheduler.**  A representative windowed magic-request stream — a budget
    of 8 certified-T requests pipelined one per 2 µs period into factory zone 3 — satisfies the
    lattice-surgery throughput invariant `window_throughput_ok` (paper I4) at a 2 µs window with
    one request per window.  So the windowed circuit's magic demand schedules feasibly on the
    surface-code factory, end of chain. -/
theorem windowed_magic_requests_pass_surgery_throughput :
    window_throughput_ok (factoryRequestSchedule 3 2 8) 2 1 = true := by native_decide

end FormalRV.Corpus.WindowedShorPPMFactoryE2E
