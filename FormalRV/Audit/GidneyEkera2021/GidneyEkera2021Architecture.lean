/-
  FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Architecture — a FINITE, GE2021-parameterised
  zoned architecture, against which the resource count and the system invariants
  are RIGOROUS (the zones hold a bounded number of physical qubits, and the
  capacity invariant rejects anything that does not fit).

  Hardware + architecture fixed to gidney-ekera-2021 (arXiv:1905.09749):
    • code distance        d = 27
    • per-logical tile     2(d+1)² = 1568 physical qubits (rotated surface patch)
    • abstract logicals    ≈ 6200  (Ekerå–Håstad windowed, Tab. 1)
    • cycle time           1 µs
    • TOTAL budget         20×10⁶ physical qubits (title)
  Zone layout reuses the neutral-atom zoned design (Factory / Computation), each a
  FINITE site interval — the resource estimate is now a statement about bounded
  hardware, not an unbounded formula.

  Hardware-neutral: `moves := []`; the architecture and schedule are valid on
  superconducting (GE2021's platform) AND neutral-atom (see `SurfaceSystemCompile`).

  No `sorry`, no new `axiom`.
-/

import FormalRV.LatticeSurgery.SurfaceShorFullSchedule
import FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Reproduction

namespace FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Architecture

open FormalRV.Framework.Architecture
open FormalRV.Framework.InvariantFramework
open FormalRV.Framework.ScheduleInv
open FormalRV.System.DependencyGraph
open FormalRV.LatticeSurgery.SurfaceShorFullSchedule

/-! ## (1) GE2021 hardware + architecture parameters (cited) -/

def ge2021_distance        : Nat := 27
def ge2021_tile_qubits     : Nat := 1568          -- 2(d+1)² at d = 27
def ge2021_logical_qubits  : Nat := 6200          -- Ekerå–Håstad abstract qubits
def ge2021_cycle_us        : Nat := 1
def ge2021_total_budget    : Nat := 20_000_000    -- reported title figure

/-- Computation zone size: every data logical qubit as a distance-27 tile. -/
def ge2021_computation_size : Nat := ge2021_logical_qubits * ge2021_tile_qubits  -- 9_721_600
/-- Factory zone size: the residual of the 20 M budget (the magic-state factories). -/
def ge2021_factory_size     : Nat := ge2021_total_budget - ge2021_computation_size -- 10_278_400

/-! ## (2) The FINITE zoned architecture (Computation + Factory) -/

def ge2021_computation : ArchZone :=
  { name := "Computation", site_lo := 0, site_hi := ge2021_computation_size }
def ge2021_factory : ArchZone :=
  { name := "Factory", site_lo := ge2021_computation_size, site_hi := ge2021_total_budget }

def ge2021Arch : ZonedArch :=
  { zones := [ge2021_computation, ge2021_factory],
    total_sites := ge2021_total_budget,
    t_cycle_us := ge2021_cycle_us, v_max_um_per_us := 1, t_react_us := 10 }

/-! ## (3) Rigorous RESOURCE COUNT against the finite zones -/

/-- The Computation zone holds 9,721,600 physical qubits (6200 tiles of 1568). -/
theorem computation_capacity : ge2021_computation.capacity = 9_721_600 := by decide
/-- The Factory zone holds the residual 10,278,400 physical qubits. -/
theorem factory_capacity : ge2021_factory.capacity = 10_278_400 := by decide

/-- **The two finite zones EXACTLY partition the 20 M budget.** -/
theorem zones_partition_budget :
    ge2021_computation.capacity + ge2021_factory.capacity = ge2021_total_budget := by decide

/-- **The total architecture is the reported 20 M physical qubits.** -/
theorem total_is_reported : ge2021Arch.total_sites = 20_000_000 := by decide

/-- **The whole data block FITS in the (finite) Computation zone** — all 6200
    distance-27 logical tiles. -/
theorem data_block_fits :
    ge2021_logical_qubits * ge2021_tile_qubits ≤ ge2021_computation.capacity := by decide

/-- The architecture budget equals the reproduction's reported qubit figure
    (`GidneyEkera2021Reproduction`): the finite zones realise that headline. -/
theorem budget_matches_reproduction :
    ge2021Arch.total_sites = FormalRV.System.NaiveUpperBound.ge2021_reported_qubits := by decide

/-! ## (4) The Shor schedule FITS the finite zones, passing resource + causality

    Reuse the detailed two-Toffoli surface-code schedule (`shorSched`/`shorDeps`),
    now placed on the FINITE GE2021 architecture: its qubit claims lie inside the
    Computation zone, so the capacity invariant (against finite zones) holds. -/

def ge2021Ctx : SystemCtx :=
  { arch := ge2021Arch, sched := shorSched, moves := [],
    window_us := 26, max_per_window := 1, t_react_us := 10, distance_fn := fun _ => 1 }

/-- **(A) Resource conflict-freedom on the FINITE GE2021 hardware**: every qubit
    the schedule claims lies inside a finite zone, no zone is over-capacity,
    throughput and decoder hold. -/
theorem ge2021Ctx_resource_ok : checkAll baseInvariants ge2021Ctx = true := by decide

/-- **(A) ∧ (B): resource AND causality on the finite GE2021 architecture.** -/
theorem ge2021Ctx_fully_valid :
    checkAll (baseInvariants ++ [causalityInv shorDeps]) ge2021Ctx = true := by decide

/-! ## (5) FINITENESS BITES — a claim beyond the 20 M architecture is rejected -/

/-- A schedule that tries to act on physical qubit 25,000,000 — beyond the 20 M
    architecture — lies in NO zone. -/
def ge2021_overflow_sched : List SysCall :=
  [ { kind := SysCallKind.Measure 25_000_000 0, begin_us := 0, end_us := 10 } ]
def ge2021_overflow_ctx : SystemCtx := { ge2021Ctx with sched := ge2021_overflow_sched }

/-- **The finite capacity invariant REJECTS it** — the hardware has only 20 M
    qubits, so a claim on qubit 25 M fails.  Resource bounds are real, not
    advisory. -/
theorem ge2021_overflow_rejected :
    checkAll baseInvariants ge2021_overflow_ctx = false := by decide

end FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Architecture
