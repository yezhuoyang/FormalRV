/-
  Do FormalRV's system-level invariants STILL HOLD when the hardware is a NEUTRAL-ATOM machine?
  Yes — proven here.  Run:  `lake env lean --run Example/neutral_atom/NeutralAtomInvariants.lean`

  The FormalRV system layer is hardware-agnostic: the SysCall schedule + invariants are
  parameterized by an operation-capacity model.  The default (`adder_demo_opCap`) used
  SUPERCONDUCTING assumptions — `max_gate2q_active = 1` (one entangling gate at a time, single
  global laser).  A NEUTRAL-ATOM machine is different: a Rydberg pulse entangles MANY pairs at
  once.  Our ZAC compile of the distance-3 surface-code merge achieved **up to 12 parallel CZ per
  Rydberg stage**, and measurement happens in a parallel readout zone.  So the neutral-atom
  capacities are *higher*, and we check the SAME verified schedule still satisfies EVERY strict
  invariant under them.

  NOTE on layers/units: FormalRV's SysCall schedule is at the LOGICAL level (logical merges /
  measures, abstract cycle units); ZAC realizes each logical operation as physical atom moves
  (real µs — the merge is 22.4 ms of Rydberg + transport).  The two are complementary; the
  invariants checked here are the LOGICAL-level capacity/ordering/freshness constraints, which a
  more-parallel neutral-atom platform satisfies a fortiori.
-/
import FormalRV.System.Examples.AdderSystem

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.AdderSystem

/-- Neutral-atom operation-capacity model — derived from the ZAC compile of `surface3_xx_merge`:
    Rydberg pulses give up to 12 parallel CZ (so `max_gate2q_active = 12`, vs the superconducting
    single-laser `1`); parallel readout zone (`max_measure_active = 12`).  Other caps as default. -/
def neutralatom_opCap : OperationCapacityModel :=
  { adder_demo_opCap with
      max_gate2q_active  := 12      -- ZAC: max 12 parallel Rydberg CZ per stage
      max_measure_active := 12 }    -- parallel neutral-atom readout zone

/-- **The FormalRV system invariants hold on a NEUTRAL-ATOM machine too.**  The verified adder
    SysCall schedule satisfies every strict invariant (operation-capacity, feedback-after-decode,
    slot-capacity, ancilla-freshness) on the same architecture with neutral-atom capacities. -/
theorem adder_n1_neutralatom_system_ok :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        adder_demo_arch
        neutralatom_opCap
        adder_demo_slotCap
        adder_demo_ancillaModel
        adder_n1_syscalls
        adder_demo_t_react_us
        adder_demo_window_us
        adder_demo_max_per_window = true := by native_decide

def main : IO Unit := do
  IO.println "════════ FormalRV system invariants on NEUTRAL-ATOM hardware ════════"
  IO.println "neutral-atom op-capacity:  max_gate2q_active=12 (Rydberg parallelism, from ZAC),"
  IO.println "                           max_measure_active=12 (parallel readout)"
  IO.println "✓ VERIFIED  adder_n1_neutralatom_system_ok  (native_decide):"
  IO.println "    the verified surgery schedule satisfies ALL strict system invariants"
  IO.println "    (operation-capacity, feedback-after-decode, slot-capacity, ancilla-freshness)"
  IO.println "    on the SAME architecture with neutral-atom (Rydberg-parallel) capacities."
