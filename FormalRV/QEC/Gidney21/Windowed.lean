/-
  FormalRV.QEC.Gidney21.Windowed
  ───────────────────────────────────────
  **windowed multiplier (window 2), compiled to physical surface-code (d = 27).**

  Carries the EXACT PPM object the PauliRotation layer already verified
  (`windowedMulLowered` : `LoweredOK`) straight through the physical compiler —
  no new circuit invented; the full pipeline stays one consistent object:

      Gate  ──gateRots/lowerFlat──▶  PPM (verified by windowedMulLowered)
            ──compilePPM @ d=27──▶  monolithic surface-code PhysCircuit.

  GE2021's table-lookup windowed arithmetic optimization.
-/
import FormalRV.QEC.Gidney21.Common

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC.LogicalLayout FormalRV.Resource FormalRV.PauliRotation
open FormalRV.BQAlgo FormalRV.Shor.WindowedCircuit

/-- The gadget (the SAME Gate the PauliRotation `LoweredOK` instance names). -/
def windowedGate : FormalRV.Framework.Gate := windowedMulCircuit 2 4 3 2

/-- **SEMANTIC CORRECTNESS at d = 27**: the gadget's PPM program implements
its Boolean semantics (the EXISTING `windowedMulLowered` proof, reused verbatim) and
each surface patch's syndrome extraction measures the [[729,1,27]]
stabilizers. -/
theorem windowed_compiled : GadgetCompiledOK windowedGate :=
  gadgetCompiledOK_of _ windowedMulLowered

/-- **RESOURCE — syndrome measurements**, walked from the monolithic physical
circuit: `#physical-PPM-statements · 27 · (width · 728)`. -/
theorem windowed_measCount :
    measCountC (gadgetPhysical windowedGate)
      = physicalStmtCount (gadgetPPM windowedGate)
          * (27 * (Resource.width windowedGate * 728)) :=
  gadget_measCount windowedGate

/-- **RESOURCE — physical qubits**: `width · 1457` (one persistent d=27
patch per logical qubit). -/
theorem windowed_qubits :
    boardPhysQubits (gadgetBoard windowedGate)
      = Resource.width windowedGate * 1457 :=
  gadget_qubits windowedGate

-- THE HONEST PHYSICAL-QUBIT BREAKDOWN (all from walking real objects):
#eval Resource.width windowedGate                       -- logical qubits = surface patches
#eval gadgetDataQubits windowedGate                     -- DATA qubits (fixed): width × 729
#eval gadgetSyndromeQubits windowedGate                 -- SYNDROME qubits (SSA, fresh/round) = #measurements
#eval gadgetMergeCount windowedGate                     -- LATTICE-SURGERY merges (joint measurements)
#eval gadgetMergeAncilla windowedGate                   -- MERGE ANCILLA (fresh patch per merge — NOT FREE!)
#eval gadgetTotalPhysQubits windowedGate                -- GRAND TOTAL = data + syndrome + merge ancilla
#eval (gadgetReport windowedGate)                       -- the full report

end FormalRV.QEC.Gidney21
