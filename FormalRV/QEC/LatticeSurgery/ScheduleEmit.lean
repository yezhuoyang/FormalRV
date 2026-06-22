/-
  FormalRV.LatticeSurgery.ScheduleEmit — emit a whole SURGERY SCHEDULE as one
  composed Stim circuit (the detailed, system-level scheduled physical circuit a
  third party can run), generalising `StimEmit.surgeryToStim` from a single gadget
  to a sequence laid out on DISJOINT physical-qubit ranges.

  This is the codegen half of the "emit detailed code for any N/a" goal: a verified
  schedule (`SurgerySchedule.Schedule`) → a Stim program whose every stabiliser is
  an explicit gate sequence.  Correctness is justified EXTERNALLY by Stim's
  stabiliser-flow analysis (PyCircuits/), the same gold standard the rest of the
  project uses.

  No Mathlib.  Pure String emission (no theorems about semantics here — those live
  in `SurgeryDemoSurface` / `SurgeryCorrect`; this file is the emitter).
-/

import FormalRV.QEC.LatticeSurgery.StimEmit
import FormalRV.QEC.LatticeSurgery.SurgerySchedule
namespace FormalRV.LatticeSurgery.ScheduleEmit

open FormalRV.Framework.LDPC
open FormalRV.LatticeSurgery.StimEmit
open FormalRV.Framework.SurgerySchedule

/-- Physical-qubit footprint of one gadget's emitted circuit: data + surgery
    ancilla (`merged_n`) plus one syndrome ancilla per merged check. -/
def gadgetFootprint (g : SurgeryGadget) : Nat :=
  g.merged_n + g.merged_hx.length + g.merged_hz.length

/-- Emit one gadget's merged-code syndrome circuit with ALL qubit indices shifted
    by `off`, so distinct schedule entries occupy disjoint physical-qubit ranges. -/
def surgeryToStimAt (g : SurgeryGadget) (off : Nat) : String :=
  let mn := g.merged_n
  let hx := g.merged_hx
  let hz := g.merged_hz
  let xBlocks := hx.zipIdx.map (fun p =>
    xCheckBlock (off + mn + p.2) ((rowSupport p.1).map (· + off)))
  let zBlocks := hz.zipIdx.map (fun p =>
    zCheckBlock (off + mn + hx.length + p.2) ((rowSupport p.1).map (· + off)))
  String.join xBlocks ++ String.join zBlocks

/-- Emit a whole schedule: each gadget at the running offset (sum of prior
    footprints), separated by `TICK`.  Carries the offset explicitly. -/
def emitScheduleStimFrom : Schedule → Nat → String
  | [],        _   => ""
  | g :: rest, off =>
      surgeryToStimAt g off ++ "TICK\n" ++ emitScheduleStimFrom rest (off + gadgetFootprint g)

/-- The detailed scheduled physical circuit for a surgery schedule (offset 0). -/
def emitScheduleStim (sched : Schedule) : String := emitScheduleStimFrom sched 0

/-- Total physical qubits the emitted scheduled circuit uses = the sum of the
    per-gadget footprints (disjoint placement). -/
def scheduleFootprint (sched : Schedule) : Nat :=
  (sched.map gadgetFootprint).foldl (· + ·) 0

private theorem foldl_add_replicate (n acc c : Nat) :
    (List.replicate n c).foldl (· + ·) acc = acc + n * c := by
  induction n generalizing acc with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.foldl_cons, ih, Nat.add_mul, Nat.one_mul]; omega

/-- Footprint of a schedule of `n` identical gadgets is `n · footprint` — the
    space the emitted code occupies grows linearly in the schedule length. -/
theorem scheduleFootprint_replicate (n : Nat) (g : SurgeryGadget) :
    scheduleFootprint (List.replicate n g) = n * gadgetFootprint g := by
  unfold scheduleFootprint
  rw [List.map_replicate, foldl_add_replicate]
  omega

end FormalRV.LatticeSurgery.ScheduleEmit
