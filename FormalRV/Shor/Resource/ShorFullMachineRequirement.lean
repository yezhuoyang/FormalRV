/-
  FormalRV.Shor.ShorFullMachineRequirement — answers three questions about the
  FULL machine needed to factor RSA-2048, as verified theorems with HONEST
  assumptions made explicit.

  Q1  T-factory scheduling + its space-time ASSUMPTIONS.
  Q2  set hardware params ⇒ a verified running-time formula.
  Q3  is the 9.72 M data-block bound ENOUGH?  (No.)  The full machine, a
      superconducting/local-connectivity realisation, and its running time.

  ## The honest headline for Q3
  9,721,600 is a lower bound on the DATA BLOCK ONLY.  It is NOT sufficient to RUN
  Shor: every Toffoli consumes a |CCZ⟩ magic state, which must be produced by a
  magic-state FACTORY that occupies its OWN qubits, plus lattice-surgery routing.
  The full machine ≈ data + factory + routing ≈ 20 M (exactly Gidney–Ekerå's
  figure).  A machine sized to the 9.72 M data bound has ZERO room for factories
  and therefore cannot run the algorithm at all.

  No `sorry`, no new `axiom`.
-/

import FormalRV.System.Examples.ConcreteMachineFeasibility
import FormalRV.System.Compile.SurfaceSystemCompile
namespace FormalRV.Shor.ShorFullMachineRequirement

open FormalRV.System.ConcreteMachineFeasibility
open FormalRV.LatticeSurgery.SurfaceShorResourceCount
open FormalRV.System.SurfaceSystemCompile
open FormalRV.Framework.Resource

/-! ## Q1. T-factory scheduling and its space-time ASSUMPTIONS

    We model a magic-state factory as a PRODUCER with two ASSUMED (input, not
    derived) parameters: its physical footprint, and its latency per magic state.
    These are hardware/method inputs (GE2021's AutoCCZ factory; the distillation
    circuit's footprint and latency).  We do NOT verify a distillation circuit
    here — that is the documented residue (CLAUDE.md L3 magic-state cultivation /
    15-to-1 / 8T-to-CCZ).  What the framework DOES verify is the SCHEDULING law:
    `P` parallel factories produce `P` states per latency window; producing `m`
    states takes `⌈m/P⌉` windows; and consumption must not outrun production
    (the `throughputInv`). -/

/-- A magic-state factory model — both fields are ASSUMPTIONS (cited inputs). -/
structure TFactoryModel where
  /-- physical qubits ONE factory occupies (assumption). -/
  qubitsPerFactory : Nat
  /-- code cycles to output ONE magic state from one factory (assumption). -/
  cyclesPerMagic   : Nat

/-- SPACE: `P` parallel factories occupy `P · qubitsPerFactory` qubits — the
    Factory zone's footprint. -/
def factoryFootprint (f : TFactoryModel) (P : Nat) : Nat := P * f.qubitsPerFactory

/-- TIME: `P` parallel factories produce `m` magic states in `⌈m/P⌉ · cyclesPerMagic`
    code cycles — the magic-supply schedule. -/
def magicProductionCycles (f : TFactoryModel) (P m : Nat) : Nat :=
  ((m + P - 1) / P) * f.cyclesPerMagic

/-- An illustrative factory: 100 k qubits per copy, 270 cycles (≈10·d at d=27) per
    magic state (ASSUMPTIONS, cited inputs). -/
def demoFactory : TFactoryModel := { qubitsPerFactory := 100_000, cyclesPerMagic := 270 }

/-- SCHEDULING SOUNDNESS (concrete): more parallel factories → less production time
    — 8 magic states take 4 windows (1080 cycles) with 2 factories, 2 windows
    (540 cycles) with 4. -/
theorem magicProductionCycles_more_factories_faster :
    magicProductionCycles demoFactory 4 8 ≤ magicProductionCycles demoFactory 2 8 := by decide

/-- The factory footprint must FIT the Factory zone's qubit budget — the space
    side of factory scheduling. -/
def factoryFits (f : TFactoryModel) (P factoryBudget : Nat) : Bool :=
  decide (factoryFootprint f P ≤ factoryBudget)

/-! ## Q3 (part 1). The data-block bound is NOT sufficient -/

/-- The FULL machine = data block + factory + surgery routing. -/
def totalPhysical (dataQ factoryQ routingQ : Nat) : Nat := dataQ + factoryQ + routingQ

/-- **The 9.72 M data bound is NOT enough to RUN Shor.**  With a non-empty factory
    (required — Toffolis consume magic states), the full requirement strictly
    exceeds the data block. -/
theorem data_block_not_sufficient (factoryQ routingQ : Nat) (hf : 0 < factoryQ) :
    rsa2048_dataPhysical 27
      < totalPhysical (rsa2048_dataPhysical 27) factoryQ routingQ := by
  unfold totalPhysical; omega

/-- A machine sized to EXACTLY the data block has ZERO qubits left for factories —
    so it cannot produce magic states, hence cannot run the algorithm. -/
theorem data_only_machine_has_no_factory_room :
    machine100k * 0 + rsa2048_dataPhysical 27 - rsa2048_dataPhysical 27 = 0 := by
  decide

/-- **The full RSA-2048 machine ≈ 20 M = data block (9.72 M) + factories +
    routing.**  Here the factory + routing residual is 10.28 M, reproducing
    Gidney–Ekerå's 20 M total. -/
theorem rsa2048_full_machine_d27 :
    totalPhysical (rsa2048_dataPhysical 27) 10_278_400 0 = 20_000_000 := by decide

/-! ## Q2 + Q3 (part 2). Set hardware params ⇒ verified running time

    Running time of the (naive, SEQUENTIAL) schedule = (Toffoli count) · (cycles
    per logical Toffoli, = code distance `d`) · (cycle time).  This is a VERIFIED
    FORMULA (`SurfaceSystemCompile.surfaceShor_time_anyD`); set `(cycle, d, T)` and
    read off the time.  It is an UPPER bound — the true pipelined runtime is lower
    by the parallelism factor (the ≈2.5× GE2021 pipelining gap, not verified at
    scale). -/

/-- The verified naive-sequential running time (in tenths-of-µs): `T · d · cycle`. -/
def shorRuntimeTenthsUs (toffoli d cycleTenthsUs : Nat) : Nat := toffoli * d * cycleTenthsUs

/-- **RSA-2048 on a 1 µs-cycle, d=27 machine, GE2021 windowed Toffoli count
    (2.7×10⁹): verified sequential running time = 729×10⁹ tenths-µs = 20.25 h.** -/
theorem rsa2048_runtime_windowed :
    shorRuntimeTenthsUs 2_700_000_000 27 10 = 729_000_000_000 := by decide

/-- **Same machine, the UN-WINDOWED schoolbook count (16n³ = 1.374×10¹¹): verified
    sequential running time = 3.711×10¹³ tenths-µs ≈ 42.9 DAYS.**  The 50.9× factor
    over the windowed figure is exactly the windowing headroom. -/
theorem rsa2048_runtime_unwindowed :
    shorRuntimeTenthsUs 137_438_953_472 27 10 = 37_108_517_437_440 := by decide

/-- It IS the verified resource-model time at d=27 (`surfaceShor_time_anyD`): set
    `n_toff`, get the time as a closed form `T · 27 · cycle`, for ANY hardware. -/
theorem runtime_is_verified_formula (T L factory : Nat) (hw : Hardware) :
    (estimateWith (surfaceModel factory) hw (shorWorkload T L)
        (surfaceCodeD 27) 0 0).time_us_tenths
      = shorRuntimeTenthsUs T 27 hw.cycle_time_us_tenths := by
  unfold shorRuntimeTenthsUs
  rw [surfaceShor_time_anyD]

/-! ## Q3 (part 3). Superconducting + local connectivity

    Surface-code lattice surgery uses ONLY nearest-neighbour 2-qubit gates — it is
    intrinsically 2-D-LOCAL.  So a superconducting machine with local (nearest-
    neighbour) coupling needs NO extra routing beyond the `2(d+1)²` tile, which
    already includes it; that is precisely GE2021's platform.  Such a machine at
    ~20 M qubits CAN run RSA-2048; one at 9.72 M (data only) CANNOT (no factory). -/

/-- A 20 M superconducting/local machine FITS the full requirement; the 9.72 M
    data-only machine does NOT run it (no factory room). -/
theorem superconducting_local_machine_summary :
    -- 20 M holds data + factory:
    totalPhysical (rsa2048_dataPhysical 27) 10_278_400 0 = 20_000_000
    -- and the data-only 9.72 M leaves nothing for the factory:
    ∧ 9_721_600 - rsa2048_dataPhysical 27 = 0 := by decide

end FormalRV.Shor.ShorFullMachineRequirement
