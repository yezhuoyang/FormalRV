/-
  FormalRV.QEC.Gidney21.EndToEnd
  ──────────────────────────────
  **THE END-TO-END COMPILER: any PPM program → a fully detailed, VERIFIED
  surface-code (d = 27) QEC program — correctness FIRST, resources counted on
  the proven object.**

  `compileToQEC` takes an arbitrary `PPMProg` and produces a
  `VerifiedQECProgram`: a bundle of (1) the detailed physical lattice-surgery
  schedule realizing every measurement of every statement — pure-X, pure-Z,
  mixed cross-patch, and Y (by edge-tracking) — together with (2) the
  CORRECTNESS PROOF that the whole schedule is semantically correct (every
  syndrome extraction measures the merged stabilizers AND every lattice
  surgery measures its target logical).  The correctness is a FIELD of the
  compiled object.

  The resource counters (`measurements`, `gates`, `dataQubits`,
  `syndromeQubits`) are defined ON the `VerifiedQECProgram`, so they only ever
  parse an object that already carries its proof — counting a proven-correct
  syntactic circuit, never an unverified one.  No room to count fiction.
-/
import FormalRV.QEC.Gidney21.AdaptiveDispatch
import FormalRV.QEC.Gidney21.SplitDetach
import FormalRV.QEC.Gidney21.YByEdgeTracking
import FormalRV.Resource.QECCircuitCount

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC FormalRV.QEC.Circuit
open FormalRV.Framework.LDPC
open FormalRV.LatticeSurgery
open FormalRV.LatticeSurgery.SurfaceShorResourceCount
open FormalRV.PPM.Prog
open FormalRV.Resource

/-! ## §1. The verified compiled object (correctness as a field). -/

/-- **A compiled QEC program that CARRIES ITS CORRECTNESS PROOF.**  The
physical lattice-surgery schedule plus the proof that it is fully
semantically correct — so nothing downstream can count an unproven object. -/
structure VerifiedQECProgram where
  /-- the source PPM program -/
  source   : PPMProg
  /-- the detailed physical lattice-surgery schedule (every measurement of
  every statement, every adaptive branch, routed by Pauli type to a verified
  d=27 merge) -/
  schedule : List SurgeryGadget
  /-- **the correctness proof** — every merge has correct syndrome extraction
  AND a correct logical measurement -/
  hcorrect : ScheduleFullyCorrect schedule

/-- **THE END-TO-END COMPILER**: PPM program → verified d=27 QEC program.
The schedule is the full per-statement dispatch; the correctness field is
discharged once and for all by `fullSchedule_fully_correct`. -/
def compileToQEC (prog : PPMProg) : VerifiedQECProgram :=
  { source   := prog
    schedule := fullSchedule prog
    hcorrect := fullSchedule_fully_correct prog }

/-- **The detailed physical circuit** of a verified QEC program — the
concatenated `prep`/`cx`/`meas` syndrome-extraction circuits of all its
merges (Stim-emittable). -/
def VerifiedQECProgram.circuit (v : VerifiedQECProgram) : PhysCircuit :=
  scheduleCircuit v.schedule

/-! ## §2. The headline correctness theorem. -/

/-- **THE COMPILED PROGRAM IS FULLY SEMANTICALLY CORRECT.**  For ANY input
PPM program, every lattice surgery in the compiled d=27 QEC program has
correct syndrome extraction and measures its target logical Pauli — the
correctness travels with the object. -/
theorem compileToQEC_correct (prog : PPMProg) :
    ScheduleFullyCorrect (compileToQEC prog).schedule :=
  (compileToQEC prog).hcorrect

/-! ## §3. Resource counters — parsing the PROVEN syntactic object. -/

/-- Number of lattice-surgery merges in the verified program. -/
def VerifiedQECProgram.numMerges (v : VerifiedQECProgram) : Nat :=
  v.schedule.length

/-- **MEASUREMENTS** — walked from the proven circuit (`measCountC`). -/
def VerifiedQECProgram.measurements (v : VerifiedQECProgram) : Nat :=
  measCountC v.circuit

/-- **GATES (CNOTs)** — walked from the proven circuit (`cxCountC`). -/
def VerifiedQECProgram.gates (v : VerifiedQECProgram) : Nat :=
  cxCountC v.circuit

/-- **DATA + SURGERY-ANCILLA qubits** — the merged width of every merge
(data patches + surgery ancilla), summed. -/
def VerifiedQECProgram.dataQubits (v : VerifiedQECProgram) : Nat :=
  (v.schedule.map SurgeryGadget.merged_n).sum

/-- **SYNDROME qubits (SSA)** — one fresh qubit per stabilizer measurement,
so equal to the total measurement count. -/
def VerifiedQECProgram.syndromeQubits (v : VerifiedQECProgram) : Nat :=
  (v.schedule.map surgeryTotalMeas).sum

/-- **The measurement count IS the walked count of the proven circuit**, and
equals the per-merge `surgeryTotalMeas` sum (= the SSA syndrome-qubit count). -/
theorem VerifiedQECProgram.measurements_eq (v : VerifiedQECProgram) :
    v.measurements = v.syndromeQubits := by
  show measCountC (scheduleCircuit v.schedule)
      = (v.schedule.map surgeryTotalMeas).sum
  rw [scheduleCircuit_measCount]

/-- The compiled program's measurement count, on the proven object. -/
theorem compileToQEC_measurements (prog : PPMProg) :
    (compileToQEC prog).measurements
      = ((fullSchedule prog).map surgeryTotalMeas).sum := by
  show measCountC (scheduleCircuit (fullSchedule prog)) = _
  rw [scheduleCircuit_measCount]

/-! ## §4. The packaged resource report. -/

/-- The full resource breakdown of a verified QEC program. -/
structure QECResourceReport where
  merges         : Nat
  dataQubits     : Nat   -- data patches + surgery ancilla
  syndromeQubits : Nat   -- SSA, fresh per measurement
  measurements   : Nat
  gates          : Nat   -- CNOTs
  deriving Repr

/-- Assemble the report — every entry read off the PROVEN circuit/schedule. -/
def VerifiedQECProgram.report (v : VerifiedQECProgram) : QECResourceReport :=
  ⟨v.numMerges, v.dataQubits, v.syndromeQubits, v.measurements, v.gates⟩

/-! ## §5. A concrete end-to-end run. -/

/-- A small but real PPM program: a joint measurement, an adaptive π/8
(Y/X) measurement, a frame correction, and a mixed CCZ-style `measureSel2`. -/
def demoProgram : PPMProg :=
  [.measure 0 [⟨0, .z⟩, ⟨1, .z⟩],
   .measureSel [0] 1 [⟨0, .y⟩] [⟨0, .x⟩],
   .frame [⟨1, .x⟩],
   .measureSel2 [0] [1] 2 [⟨0, .x⟩, ⟨1, .z⟩] [⟨0, .z⟩, ⟨1, .x⟩]
     [⟨0, .x⟩, ⟨1, .x⟩] [⟨0, .z⟩, ⟨1, .z⟩]]

/-- **The demo compiles to a fully-correct d=27 QEC program.** -/
theorem demoProgram_compiled_correct :
    ScheduleFullyCorrect (compileToQEC demoProgram).schedule :=
  compileToQEC_correct demoProgram

-- The resource report of the compiled, PROVEN program (each count read off
-- the verified object):
#eval (compileToQEC demoProgram).numMerges          -- lattice-surgery merges
#eval (compileToQEC demoProgram).dataQubits         -- data + surgery-ancilla qubits
#eval (compileToQEC demoProgram).syndromeQubits     -- SSA syndrome qubits = measurements
#eval (compileToQEC demoProgram).report             -- the full breakdown

end FormalRV.QEC.Gidney21
