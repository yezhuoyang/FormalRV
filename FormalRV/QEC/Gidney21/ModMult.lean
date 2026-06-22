/-
  FormalRV.QEC.Gidney21.ModMult
  ───────────────────────────────────────
  **modular constant multiplier (mod 15, ×7), compiled to physical surface-code (d = 27).**

  Carries the EXACT PPM object the PauliRotation layer already verified
  (`modMultConstLowered` : `LoweredOK`) straight through the physical compiler —
  no new circuit invented; the full pipeline stays one consistent object:

      Gate  ──gateRots/lowerFlat──▶  PPM (verified by modMultConstLowered)
            ──compilePPM @ d=27──▶  monolithic surface-code PhysCircuit.

  one modular multiplication, the inner loop body of windowed exponentiation.
-/
import FormalRV.QEC.Gidney21.Common

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC.LogicalLayout FormalRV.Resource FormalRV.PauliRotation
open FormalRV.BQAlgo FormalRV.Shor.WindowedCircuit

/-- The gadget (the SAME Gate the PauliRotation `LoweredOK` instance names). -/
def modmultGate : FormalRV.Framework.Gate := modmult_const_gate 2 15 7

/-- **SEMANTIC CORRECTNESS at d = 27**: the gadget's PPM program implements
its Boolean semantics (the EXISTING `modMultConstLowered` proof, reused verbatim) and
each surface patch's syndrome extraction measures the [[729,1,27]]
stabilizers. -/
theorem modmult_compiled : GadgetCompiledOK modmultGate :=
  gadgetCompiledOK_of _ modMultConstLowered

/-- **RESOURCE — syndrome measurements**, walked from the monolithic physical
circuit: `#physical-PPM-statements · 27 · (width · 728)`. -/
theorem modmult_measCount :
    measCountC (gadgetPhysical modmultGate)
      = physicalStmtCount (gadgetPPM modmultGate)
          * (27 * (Resource.width modmultGate * 728)) :=
  gadget_measCount modmultGate

/-- **RESOURCE — physical qubits**: `width · 1457` (one persistent d=27
patch per logical qubit). -/
theorem modmult_qubits :
    boardPhysQubits (gadgetBoard modmultGate)
      = Resource.width modmultGate * 1457 :=
  gadget_qubits modmultGate

-- THE HONEST PHYSICAL-QUBIT BREAKDOWN (all from walking real objects):
#eval Resource.width modmultGate                       -- logical qubits = surface patches
#eval gadgetDataQubits modmultGate                     -- DATA qubits (fixed): width × 729
#eval gadgetSyndromeQubits modmultGate                 -- SYNDROME qubits (SSA, fresh/round) = #measurements
#eval gadgetMergeCount modmultGate                     -- LATTICE-SURGERY merges (joint measurements)
#eval gadgetMergeAncilla modmultGate                   -- MERGE ANCILLA (fresh patch per merge — NOT FREE!)
#eval gadgetTotalPhysQubits modmultGate                -- GRAND TOTAL = data + syndrome + merge ancilla
#eval (gadgetReport modmultGate)                       -- the full report

end FormalRV.QEC.Gidney21
