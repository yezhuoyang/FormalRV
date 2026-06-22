/-
  FormalRV.QEC.Gidney21.CuccaroAdder
  ───────────────────────────────────────
  **Cuccaro ripple-carry adder (4-bit), compiled to physical surface-code (d = 27).**

  Carries the EXACT PPM object the PauliRotation layer already verified
  (`cuccaroLowered` : `LoweredOK`) straight through the physical compiler —
  no new circuit invented; the full pipeline stays one consistent object:

      Gate  ──gateRots/lowerFlat──▶  PPM (verified by cuccaroLowered)
            ──compilePPM @ d=27──▶  monolithic surface-code PhysCircuit.

  the carry-propagating MAJ/UMA sweep — the core of every windowed lookup addition.
-/
import FormalRV.QEC.Gidney21.Common

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC.LogicalLayout FormalRV.Resource FormalRV.PauliRotation
open FormalRV.BQAlgo FormalRV.Shor.WindowedCircuit

/-- The gadget (the SAME Gate the PauliRotation `LoweredOK` instance names). -/
def cuccaroadderGate : FormalRV.Framework.Gate := cuccaro_n_bit_adder_full 4 0

/-- **SEMANTIC CORRECTNESS at d = 27**: the gadget's PPM program implements
its Boolean semantics (the EXISTING `cuccaroLowered` proof, reused verbatim) and
each surface patch's syndrome extraction measures the [[729,1,27]]
stabilizers. -/
theorem cuccaroadder_compiled : GadgetCompiledOK cuccaroadderGate :=
  gadgetCompiledOK_of _ cuccaroLowered

/-- **RESOURCE — syndrome measurements**, walked from the monolithic physical
circuit: `#physical-PPM-statements · 27 · (width · 728)`. -/
theorem cuccaroadder_measCount :
    measCountC (gadgetPhysical cuccaroadderGate)
      = physicalStmtCount (gadgetPPM cuccaroadderGate)
          * (27 * (Resource.width cuccaroadderGate * 728)) :=
  gadget_measCount cuccaroadderGate

/-- **RESOURCE — physical qubits**: `width · 1457` (one persistent d=27
patch per logical qubit). -/
theorem cuccaroadder_qubits :
    boardPhysQubits (gadgetBoard cuccaroadderGate)
      = Resource.width cuccaroadderGate * 1457 :=
  gadget_qubits cuccaroadderGate

-- THE HONEST PHYSICAL-QUBIT BREAKDOWN (all from walking real objects):
#eval Resource.width cuccaroadderGate                       -- logical qubits = surface patches
#eval gadgetDataQubits cuccaroadderGate                     -- DATA qubits (fixed): width × 729
#eval gadgetSyndromeQubits cuccaroadderGate                 -- SYNDROME qubits (SSA, fresh/round) = #measurements
#eval gadgetMergeCount cuccaroadderGate                     -- LATTICE-SURGERY merges (joint measurements)
#eval gadgetMergeAncilla cuccaroadderGate                   -- MERGE ANCILLA (fresh patch per merge — NOT FREE!)
#eval gadgetTotalPhysQubits cuccaroadderGate                -- GRAND TOTAL = data + syndrome + merge ancilla
#eval (gadgetReport cuccaroadderGate)                       -- the full report

end FormalRV.QEC.Gidney21
