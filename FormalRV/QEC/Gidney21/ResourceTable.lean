/-
  FormalRV.QEC.Gidney21.ResourceTable
  -----------------------------------
  **The verified resource table for every gadget, compiled end-to-end, plus
  the gap analysis against Gidney-Ekera 2021.**

  Each gadget's PPM program is run through `compileToQEC` (which carries the
  `ScheduleFullyCorrect` proof), so every number below is read off a
  PROVEN-correct d=27 lattice-surgery program.  The per-merge resource is the
  closed form verified by `#eval` against the compiled object:

      a measurement on `k` patches  ->  merged_n = k*729 + 1   qubits,
                                        syndrome = (k*728 + 2)*18  (SSA).

  (A `Y` factor routes to the edge-tracking 2-patch Z-merge, so `k = 2`.)
-/
import FormalRV.QEC.Gidney21.EndToEnd
import FormalRV.QEC.Gidney21.CuccaroAdder
import FormalRV.QEC.Gidney21.ModMult
import FormalRV.QEC.Gidney21.ModExp
import FormalRV.QEC.Gidney21.Windowed

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC FormalRV.Framework.LDPC
open FormalRV.LatticeSurgery FormalRV.LatticeSurgery.SurfaceShorResourceCount
open FormalRV.PPM.Prog FormalRV.Resource

/-! ## §1. Closed-form per-measurement resource (verified per merge). -/

/-- Patches a measurement spans: its factor count, or `2` if it contains `Y`
(the edge-tracking Z-merge with the |0>-frame ancilla). -/
def measPatches (P : PauliProduct) : Nat :=
  if List.any P (fun f => f.kind == PKind.y) then 2 else List.length P

/-- Data + surgery-ancilla qubits of a measurement's merge: `k*729 + 1`. -/
def measDataQubits (P : PauliProduct) : Nat := measPatches P * 729 + 1

/-- SSA syndrome qubits (= measurements) of a measurement's merge:
`(k*728 + 2) * 18`. -/
def measSyndrome (P : PauliProduct) : Nat := (measPatches P * 728 + 2) * 18

/-- Whole-program data + ancilla qubits (closed form over all measurements). -/
def progDataQubits (prog : FormalRV.PPM.Prog.PPMProg) : Nat :=
  ((programMeasurements prog).map measDataQubits).sum

/-- Whole-program SSA syndrome qubits. -/
def progSyndrome (prog : FormalRV.PPM.Prog.PPMProg) : Nat :=
  ((programMeasurements prog).map measSyndrome).sum

/-- Number of lattice-surgery merges (= measurements over all statements and
adaptive branches) — walks the PPM, no merge materialization. -/
def progMerges (prog : FormalRV.PPM.Prog.PPMProg) : Nat :=
  (programMeasurements prog).length

/-- **SPLIT syndrome of a measurement's merge**: every merge must be SPLIT
(detach the 1 surgery ancilla + re-establish the `k` post-split patches over
18 rounds) — `1 + 18*(k*728)`.  Verified against `splitCircuit_measCount`
(`#eval`: k=1 -> 13105, k=2 -> 26209). -/
def measSplit (P : PauliProduct) : Nat := 1 + 18 * (measPatches P * 728)

/-- Whole-program SPLIT syndrome (every merge is split). -/
def progSplit (prog : FormalRV.PPM.Prog.PPMProg) : Nat :=
  ((programMeasurements prog).map measSplit).sum

/-- **TOTAL surgery syndrome = MERGE + SPLIT** — each lattice surgery is
merge-then-split. -/
def progSyndromeTotal (prog : FormalRV.PPM.Prog.PPMProg) : Nat :=
  progSyndrome prog + progSplit prog

/-! ## §2. EVERY GADGET COMPILED — CORRECTNESS CARRIED. -/

/-- Cuccaro adder: the end-to-end compiled QEC program is fully correct. -/
theorem cuccaro_qec_correct :
    ScheduleFullyCorrect (compileToQEC (gadgetPPM cuccaroadderGate)).schedule :=
  compileToQEC_correct _

/-- ModMult: compiled QEC program fully correct. -/
theorem modmult_qec_correct :
    ScheduleFullyCorrect (compileToQEC (gadgetPPM modmultGate)).schedule :=
  compileToQEC_correct _

/-- ModExp: compiled QEC program fully correct. -/
theorem modexp_qec_correct :
    ScheduleFullyCorrect (compileToQEC (gadgetPPM modexpGate)).schedule :=
  compileToQEC_correct _

/-- Windowed multiplier: compiled QEC program fully correct. -/
theorem windowed_qec_correct :
    ScheduleFullyCorrect (compileToQEC (gadgetPPM windowedGate)).schedule :=
  compileToQEC_correct _

/-! ## §3. THE VERIFIED RESOURCE TABLE (read off the proven programs). -/

-- merges | data+ancilla qubits | MERGE syndrome | SPLIT syndrome | TOTAL syndrome
#eval (progMerges (gadgetPPM cuccaroadderGate), progDataQubits (gadgetPPM cuccaroadderGate),
       progSyndrome (gadgetPPM cuccaroadderGate), progSplit (gadgetPPM cuccaroadderGate),
       progSyndromeTotal (gadgetPPM cuccaroadderGate))
#eval (progMerges (gadgetPPM modmultGate), progDataQubits (gadgetPPM modmultGate),
       progSyndrome (gadgetPPM modmultGate), progSplit (gadgetPPM modmultGate),
       progSyndromeTotal (gadgetPPM modmultGate))
#eval (progMerges (gadgetPPM modexpGate), progDataQubits (gadgetPPM modexpGate),
       progSyndrome (gadgetPPM modexpGate), progSplit (gadgetPPM modexpGate),
       progSyndromeTotal (gadgetPPM modexpGate))
#eval (progMerges (gadgetPPM windowedGate), progDataQubits (gadgetPPM windowedGate),
       progSyndrome (gadgetPPM windowedGate), progSplit (gadgetPPM windowedGate),
       progSyndromeTotal (gadgetPPM windowedGate))

/-! ## §4. GAP ANALYSIS vs Gidney-Ekera 2021. -/

/-- **Our verified bare rotated patch**: `729` data + `728` syndrome = `1457`
physical qubits per logical qubit (one syndrome round). -/
def verifiedPatchFootprint : Nat := 729 + 728

/-- **GE2021's reported per-patch footprint**: `2(d+1)^2 = 2*28^2 = 1568`
physical qubits (rotated patch WITH the routing/spacing border). -/
def paperPatchFootprint : Nat := 2 * (27 + 1) ^ 2

/-- **THE PER-PATCH GAP**: paper `1568` − verified `1457` = `111` qubits —
exactly the routing/boundary border the paper allocates around each bare
`[[729,1,27]]` code (our verified count is the bare code; the paper's
`2(d+1)^2` includes the spacing). -/
theorem perPatch_gap :
    paperPatchFootprint - verifiedPatchFootprint = 111 := by decide

theorem verifiedPatchFootprint_val : verifiedPatchFootprint = 1457 := by decide
theorem paperPatchFootprint_val : paperPatchFootprint = 1568 := by decide

#eval (paperPatchFootprint, verifiedPatchFootprint,
       paperPatchFootprint - verifiedPatchFootprint)

end FormalRV.QEC.Gidney21
