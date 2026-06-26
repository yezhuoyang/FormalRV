/-
  FormalRV.System.Examples.ConcreteMachineFeasibility — two independent
  demonstrations that a resource estimate is only meaningful relative to a
  concrete machine:

  (1) SPACE FEASIBILITY (§1–§2): whether a fixed physical-qubit budget can
      hold the RSA-2048 data block — 6200 logical patches × `2(d+1)²`
      physical qubits each, all live simultaneously (they hold the quantum
      state, so they cannot be time-shared).  A 100 000-qubit machine
      cannot, at any useful distance; a 20 M machine can at d = 27.

  (2) CONNECTIVITY (§3): a pluggable coupling-map `SpaceTimeInvariant` —
      nearest-neighbour rejects a long-range Gate2q that all-to-all admits
      (superconducting / trapped-ion / neutral-atom each supply their own
      `couples`).

  The two halves are unrelated beyond sharing the SysCall / invariant
  vocabulary.  No `sorry`, no new `axiom`.
-/

import FormalRV.System.Invariants.InvariantFramework
import FormalRV.System.Params.RSA2048

set_option maxRecDepth 8000

namespace FormalRV.System.ConcreteMachineFeasibility

open FormalRV.System.Architecture
open FormalRV.System.InvariantFramework

/-! ## (1) Space requirement of RSA-2048 vs a bounded machine -/

/-- A distance-`d` rotated surface tile: `2(d+1)²` physical qubits per logical. -/
def surfaceTile (d : Nat) : Nat := 2 * (d + 1) ^ 2

/-- RSA-2048's live logical-qubit count: the canonical `RSA2048.patches`
    (= 6200, Ekerå–Håstad windowed layout). -/
def rsa2048_logical : Nat := FormalRV.System.RSA2048.patches

/-- Physical qubits the RSA-2048 DATA BLOCK needs at distance `d` (all live at
    once — not time-shareable). -/
def rsa2048_dataPhysical (d : Nat) : Nat := rsa2048_logical * surfaceTile d

/-- A concrete machine FITS the RSA-2048 data block at distance `d` iff its qubit
    budget covers it. -/
def machineFitsRSA2048 (budget d : Nat) : Bool := decide (rsa2048_dataPhysical d ≤ budget)

/-- The data block at d=27 is 6200 · 1568 = 9,721,600 physical qubits. -/
theorem rsa2048_dataPhysical_d27 : rsa2048_dataPhysical 27 = 9_721_600 := by decide

/-! ## (2) A 100 000-qubit machine CANNOT factor RSA-2048 -/

def machine100k : Nat := 100_000

/-- **INFEASIBLE.**  A 100 000-qubit machine cannot hold the RSA-2048 data block
    at d=27 (needs 9.72 M ≫ 100 k). -/
theorem machine100k_cannot_factor_rsa2048_d27 :
    machineFitsRSA2048 machine100k 27 = false := by decide

/-- The space requirement is a genuine lower bound: ANY machine that fits RSA-2048
    at d=27 has at least 9,721,600 qubits. -/
theorem rsa2048_space_lower_bound (budget : Nat)
    (h : machineFitsRSA2048 budget 27 = true) : 9_721_600 ≤ budget := by
  have := of_decide_eq_true h
  rwa [rsa2048_dataPhysical_d27] at this

/-- Even at the SMALLEST error-correcting distance d=3 (tile 32), RSA-2048's data
    block is 6200·32 = 198,400 > 100 k — still infeasible.  100 k cannot factor
    RSA-2048 at ANY useful distance. -/
theorem machine100k_infeasible_even_d3 :
    machineFitsRSA2048 machine100k 3 = false := by decide

/-- What a 100 k machine CAN hold at d=27: ⌊100000 / 1568⌋ = 63 logical qubits —
    enough only for a tiny (~20-bit) factoring instance, not RSA-2048's 6200. -/
theorem machine100k_holds_63_logical_d27 :
    machine100k / surfaceTile 27 = 63 := by decide

/-- A machine that DOES fit RSA-2048 at d=27 (e.g. Gidney's 20 M). -/
theorem machine20M_fits_rsa2048_d27 :
    machineFitsRSA2048 20_000_000 27 = true := by decide

/-! ## (3) Connectivity (coupling-map) constraint as a pluggable invariant -/

/-- A hardware connectivity constraint: every 2-qubit gate must act on a pair the
    machine can DIRECTLY couple, per `couples`.  Long-range gates must be routed
    (SWAP) and fail this until decomposed.  Hardware-specific: superconducting
    nearest-neighbour, trapped-ion all-to-all (`fun _ _ => true`), neutral-atom
    reconfigurable each supply their own `couples`. -/
def connectivityInv (couples : Nat → Nat → Bool) : SpaceTimeInvariant :=
  { name := "hardware connectivity (coupling map)",
    check := fun c => c.sched.all (fun sc =>
      match sc.kind with
      | SysCallKind.Gate2q q1 q2 _ => couples q1 q2
      | _                          => true) }

/-- 1-D nearest-neighbour coupling (the canonical superconducting constraint). -/
def nearestNeighbor1D (q1 q2 : Nat) : Bool :=
  decide (q1 + 1 = q2) || decide (q2 + 1 = q1) || decide (q1 = q2)

/-- A small schedule whose 2-qubit gates are all nearest-neighbour. -/
def nnSched : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 1 0, begin_us := 0,  end_us := 10 }
  , { kind := SysCallKind.Gate2q 1 2 0, begin_us := 10, end_us := 20 } ]

def nnCtx : SystemCtx :=
  { arch := demoArch, sched := nnSched, moves := [],
    window_us := 1000, max_per_window := 1, t_react_us := 10, distance_fn := demoDist }

/-- **Respects nearest-neighbour connectivity.** -/
theorem nnCtx_connectivity_ok :
    (connectivityInv nearestNeighbor1D).check nnCtx = true := by decide

/-- A schedule with a LONG-RANGE gate (qubits 0 and 5, distance 5) on a
    nearest-neighbour machine. -/
def longRangeSched : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 5 0, begin_us := 0, end_us := 10 } ]
def longRangeCtx : SystemCtx := { nnCtx with sched := longRangeSched }

/-- **REJECTED**: a long-range gate violates nearest-neighbour connectivity — it
    must be routed by SWAPs first.  Connection constraints are real, not advisory. -/
theorem longRange_rejected :
    (connectivityInv nearestNeighbor1D).check longRangeCtx = false := by decide

/-- The nearest-neighbour schedule passes the FULL check (resource A + connectivity
    as a composed hardware invariant) — one uniform `checkAll`. -/
theorem nnCtx_fully_valid :
    checkAll (baseInvariants ++ [connectivityInv nearestNeighbor1D]) nnCtx = true := by decide

/-- Trapped-ion all-to-all coupling (`couples = fun _ _ => true`) admits the
    long-range gate the nearest-neighbour machine rejected — the SAME schedule,
    different hardware connectivity. -/
theorem longRange_ok_on_all_to_all :
    (connectivityInv (fun _ _ => true)).check longRangeCtx = true := by decide

end FormalRV.System.ConcreteMachineFeasibility
