/-
  FormalRV.QEC.Gidney21.ModExp
  ───────────────────────────────────────
  **verified modular exponentiation (a=7 mod 15), compiled to physical surface-code (d = 27).**

  Carries the EXACT PPM object the PauliRotation layer already verified
  (`shorModExpVerifiedLowered` : `LoweredOK`) straight through the physical compiler —
  no new circuit invented; the full pipeline stays one consistent object:

      Gate  ──gateRots/lowerFlat──▶  PPM (verified by shorModExpVerifiedLowered)
            ──compilePPM @ d=27──▶  monolithic surface-code PhysCircuit.

  the headline modexp — value-correct on the true modulus.
-/
import FormalRV.QEC.Gidney21.Common

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC.LogicalLayout FormalRV.Resource FormalRV.PauliRotation
open FormalRV.BQAlgo FormalRV.Shor.WindowedCircuit

/-- The gadget (the SAME Gate the PauliRotation `LoweredOK` instance names). -/
def modexpGate : FormalRV.Framework.Gate := shorModExpVerified 1 15 7 13

/-- **SEMANTIC CORRECTNESS at d = 27**: the gadget's PPM program implements
its Boolean semantics (the EXISTING `shorModExpVerifiedLowered` proof, reused verbatim) and
each surface patch's syndrome extraction measures the [[729,1,27]]
stabilizers. -/
theorem modexp_compiled : GadgetCompiledOK modexpGate :=
  gadgetCompiledOK_of _ shorModExpVerifiedLowered

/-- **RESOURCE — syndrome measurements**, walked from the monolithic physical
circuit: `#physical-PPM-statements · 27 · (width · 728)`. -/
theorem modexp_measCount :
    measCountC (gadgetPhysical modexpGate)
      = physicalStmtCount (gadgetPPM modexpGate)
          * (27 * (Resource.width modexpGate * 728)) :=
  gadget_measCount modexpGate

/-- **RESOURCE — physical qubits**: `width · 1457` (one persistent d=27
patch per logical qubit). -/
theorem modexp_qubits :
    boardPhysQubits (gadgetBoard modexpGate)
      = Resource.width modexpGate * 1457 :=
  gadget_qubits modexpGate

-- THE HONEST PHYSICAL-QUBIT BREAKDOWN (all from walking real objects):
#eval Resource.width modexpGate                       -- logical qubits = surface patches
#eval gadgetDataQubits modexpGate                     -- DATA qubits (fixed): width × 729
#eval gadgetSyndromeQubits modexpGate                 -- SYNDROME qubits (SSA, fresh/round) = #measurements
#eval gadgetMergeCount modexpGate                     -- LATTICE-SURGERY merges (joint measurements)
#eval gadgetMergeAncilla modexpGate                   -- MERGE ANCILLA (fresh patch per merge — NOT FREE!)
#eval gadgetTotalPhysQubits modexpGate                -- GRAND TOTAL = data + syndrome + merge ancilla
#eval (gadgetReport modexpGate)                       -- the full report

end FormalRV.QEC.Gidney21
