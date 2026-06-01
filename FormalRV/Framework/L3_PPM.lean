/-
  FormalRV.Framework.L3_PPM — Layer 3 (Pauli-product measurement /
  logical operations) interface.

  Phase A.2 of the paper plan (`PAPER_PLAN.md`). This is the layer
  between L4 (QEC code) and L2 (logical arithmetic gadgets): the
  PPM gadget set + Clifford + T-injection that together form a
  complete logical gate set on top of an L4 code.

  L3 supplies the L3 → L2 contract:
     per_op_error (g : LogicalGate) (qec : QECCode) (hw : HardwareParams) : Nat
  bounded by `c · L4_cycle_logical_error_rate` for an explicit
  cycle-cost constant `c` derived from the gadget structure.

  This tick creates only the two top-level structures; magic-state
  cultivation, distillation factories, and the contract theorem
  are future ticks.
-/

import FormalRV.Framework.L4_QECCode

namespace FormalRV.Framework

/-- A PPM gadget: a protocol that performs one logical Pauli-product
measurement on the data qubits of an L4 code, at a stated cycle cost.

`operator_weight` is the maximum weight of the logical Pauli product the
gadget supports.  `tau_s` is the cycle count per measurement — for
standard surface-code lattice surgery this is `d`; for qLDPC surgery
it is generally `2 d / 3` (paper-cited, Layer-3 derivable from a
concrete surgery construction). -/
structure PPMGadget where
  /-- The L4 code on which this gadget acts. -/
  target : QECCode
  /-- Maximum operator weight (number of physical qubits) supported. -/
  operator_weight : Nat
  /-- Cycle count per logical measurement. -/
  tau_s : Nat
  deriving Inhabited

/-- A complete logical gate set on top of an L4 code: the Pauli /
Clifford generators that surface-code or qLDPC surgery makes available
natively, plus a `T`-state injection primitive that closes the gate
set to universal computation via the magic-state factory of L3.

The `ppm` field links back to the PPM gadget that implements joint
logical measurements; `magic_factory_qubit_cost` is a coarse placeholder
for the per-T-state qubit-rounds overhead — the L2 contract consumes
this directly. -/
structure LogicalGateSet where
  /-- The PPM gadget implementing joint logical measurements. -/
  ppm : PPMGadget
  /-- Whether the gate set supports a native logical Hadamard
  (true for surface code; depends on the L4 code for qLDPC families). -/
  has_logical_H : Bool
  /-- Whether the gate set supports native CNOT via lattice surgery. -/
  has_logical_CNOT : Bool
  /-- Coarse qubit-rounds-per-T-state placeholder for the magic-state
  cost L2 will consume.  Future ticks will refine to a derived
  function of cultivation rate + distillation ratio. -/
  magic_factory_qubit_cost : Nat
  deriving Inhabited

/-- Smoke check: a trivial gate set on a trivial code builds. -/
example : (LogicalGateSet.mk
            { target := default, operator_weight := 4, tau_s := 1 }
            true true 0).has_logical_H = true := by rfl

/-- Canonical cycle-cost projection on a PPM gadget: the number of L4
cycles per logical Pauli-product measurement.  Phase-C corpus instances
will read off paper-stated `τ_s` values through this projection so the
derivation chain is uniform. -/
def tau_s_cost (g : PPMGadget) : Nat := g.tau_s

end FormalRV.Framework
