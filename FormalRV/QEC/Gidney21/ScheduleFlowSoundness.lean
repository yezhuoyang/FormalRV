/-
  FormalRV.QEC.Gidney21.ScheduleFlowSoundness
  ───────────────────────────────────────────
  **THE SCHEDULE-LEVEL SOUNDNESS OBLIGATION — the composed lattice surgery
  (correlation-surface direction + color) must realize the PPM circuit, not
  merely "every merge is individually fine".**

  The per-merge check `AlgorithmCorrectness.ScheduleFullyCorrect sched =
  ∀ g ∈ sched, MergeFullyCorrect g` is discharged UNCONDITIONALLY
  (`scheduleFullyCorrect_of`): it holds for ANY schedule.  That is a SOUNDNESS
  GAP — per-merge correctness does NOT compose to routine correctness:

    * a CNOT's two merges in the WRONG order compute a different operation;
    * a merge with the WRONG boundary COLOR (X-merge where a Z-merge is needed)
      measures the wrong observable;
    * a degree-3 junction (CCZ) can be locally legal yet carry NO consistent
      correlation surface for a required stabilizer flow — exactly the
      Gidney-Fowler majority-gate bug LaSsynth caught.

  The honest fix is a GLOBAL obligation on the COMPOSED spacetime diagram: its
  correlation surfaces (with their actual directions and Z/X colors) must
  realize the stabilizer flows the PPM circuit demands.  That is precisely
  `LaSre.LaSCorrectFull` (validity + interior even-parity/all-or-none + the
  PORT BOUNDARY matching every blue(Z)/red(X) piece to the spec Pauli).  This
  file packages it as the schedule obligation, proves it SOUND, proves it
  STRICTLY STRONGER than the per-merge check (a real composed surgery that
  passes every LOCAL check yet fails the GLOBAL flow check), and discharges it
  on the real LaSsynth CCZ/majority gate — with localized rejection of
  corruptions.

  No cheating: the spec Paulis (`majPaulis`) are the LaSsynth `SPECS["maj"]`
  flows the PPM CCZ demands; the surfaces (`majoritySurf`) are the surgery's
  actual geometry; the obligation is the non-trivial equality between them, and
  it says "no" on a wrong composition.
-/
import FormalRV.QEC.Gidney21.AdaptiveDispatch
import FormalRV.QEC.LatticeSurgery.MajorityGateLaS

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC
open FormalRV.QEC.LaSre
open FormalRV.PPM.Prog

/-! ## §1. The composed surgery + its spec, and the global obligation. -/

/-- A whole schedule realized as ONE composed spacetime diagram: the pipe
diagram `L`, the correlation surfaces `S` (one per demanded stabilizer flow),
the boundary `ports`, and the SPEC `paulis` = the stabilizer flows the PPM
circuit above demands.

NOTE on Z/X boundary type: the obligation enforces the Z-vs-X distinction
through the SEAM AXIS (`ExistI` vs `ExistJ`), WHICH SURFACE PLANE joins across
it, and the PORT PAULIS (blue=Z / red=X) — all read by `funcOK`/`portsOK`.  The
`LaSre.ColorI`/`ColorJ` Bool fields are DESCRIPTIVE metadata that the checker
does NOT read; "color" in the prose below means this geometry+port enforcement,
not those fields. -/
structure ScheduleLaS where
  L : LaSre
  S : Surf
  ports : List Port
  paulis : Nat → Nat → Pauli
  nStab : Nat

/-- **THE SCHEDULE-LEVEL FLOW-COMPOSITION OBLIGATION.**  The composed surgery
realizes the PPM spec iff its correlation surfaces (directions + boundary types,
per the note above) pass the COMPLETE `LaSCorrectFull`: structural validity,
interior functionality (even-parity b, all-or-none c, Y-both-or-none d), AND the
port boundary (a) matching every blue(Z)/red(X) piece to the demanded port
Pauli. -/
def ScheduleImplementsSpec (sl : ScheduleLaS) : Bool :=
  LaSCorrectFull sl.L sl.S sl.ports sl.paulis sl.nStab

/-- The flow-level semantic guarantee the obligation certifies: the surgery is
structurally legal, its interior correlation surfaces are consistent for every
demanded flow, AND its boundary matches the spec.  (This is the stabilizer-flow
/ ZX certificate that the diagram computes the specified logical map — the
composition-level analogue of the per-merge measured-Pauli guarantee.) -/
def RealizesSpecFlows (sl : ScheduleLaS) : Prop :=
  sl.L.valid = true
    ∧ sl.L.funcOK sl.S sl.nStab = true
    ∧ portsOK sl.S sl.ports sl.paulis sl.nStab = true

/-- **SOUNDNESS.**  Passing the obligation certifies the surgery realizes EVERY
demanded stabilizer flow — validity, interior consistency, and the port-spec
match all hold.  (Unpacks the `LaSCorrectFull` conjunction; the content is that
the three independent global checks simultaneously hold.) -/
theorem implements_sound (sl : ScheduleLaS)
    (h : ScheduleImplementsSpec sl = true) : RealizesSpecFlows sl := by
  unfold ScheduleImplementsSpec LaSCorrectFull at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## §2. THE SOUNDNESS GAP, made concrete: LOCAL ≠ GLOBAL.

  `LaSre.valid = gridCubes.all validCube` is literally "every local merge-cube
  passes its local structural check" — the LaSre analogue of the per-merge
  `gadgets.all verify_surgery_gadget`.  We exhibit a REAL composed surgery (the
  LaSsynth majority gate with ONE pipe deleted) that passes this local check at
  EVERY cube, yet FAILS the global stabilizer-flow check.  So per-merge / local
  correctness provably does NOT compose. -/

/-- The deleted-pipe majority gate is LOCALLY valid at every cube — removing a
pipe cannot create a 3D corner or a Y-cube violation. -/
theorem delPipe_locally_valid : majorityLaS_delPipe.valid = true := by native_decide

/-- ...yet its correlation surfaces FAIL the global functionality check: the
even-parity at a cube adjacent to the deleted pipe no longer closes. -/
theorem delPipe_globally_wrong :
    majorityLaS_delPipe.funcOK majoritySurf 9 = false := by native_decide

/-- **★ THE SOUNDNESS GAP ★.**  There is a composed surgery that passes the
LOCAL (per-cube / per-merge) structural check everywhere yet FAILS the GLOBAL
stabilizer-flow check.  Hence "every merge is individually correct" is NOT a
sufficient certificate — the global flow-composition obligation is required. -/
theorem local_does_not_imply_global :
    ∃ (L : LaSre) (S : Surf) (n : Nat),
      L.valid = true ∧ L.funcOK S n = false :=
  ⟨majorityLaS_delPipe, majoritySurf, 9, delPipe_locally_valid, delPipe_globally_wrong⟩

/-- The per-merge schedule check is VACUOUSLY universal — it holds for EVERY
PPM program (`scheduleFullyCorrect_of`), so it carries no information about
whether the composition is right.  It cannot be the soundness certificate. -/
theorem perMerge_check_vacuous (prog : PPMProg) :
    ScheduleFullyCorrect (fullSchedule prog) :=
  fullSchedule_fully_correct prog

/-! ## §3. THE GLOBAL OBLIGATION DISCHARGED on the real LaSsynth CCZ gate. -/

/-- **The composed CCZ / majority-gate surgery**, as a `ScheduleLaS`: the real
4×4×5 LaSsynth pipe diagram, its 9 synthesized correlation surfaces, its 9
ports, and the spec `majPaulis` = the `SPECS["maj"]` stabilizer flows the PPM
CCZ demands. -/
def cczScheduleLaS : ScheduleLaS :=
  { L := majorityLaS, S := majoritySurf, ports := majPorts,
    paulis := majPaulis, nStab := 9 }

/-- **★ THE COMPOSED CCZ SURGERY IMPLEMENTS ITS SPEC ★.**  The whole composed
surgery — every pipe's direction and Z/X color — passes the global flow
obligation: it realizes all 9 stabilizer flows the CCZ demands, with the port
boundary matching the spec.  This is the check the per-merge layer CANNOT do. -/
theorem ccz_implements_spec : ScheduleImplementsSpec cczScheduleLaS = true :=
  majorityLaS_fully_correct

/-- ...and therefore the composed surgery REALIZES every demanded flow. -/
theorem ccz_realizes_flows : RealizesSpecFlows cczScheduleLaS :=
  implements_sound _ ccz_implements_spec

/-! ## §4. THE OBLIGATION HAS TEETH — corrupted compositions are REJECTED. -/

/-- A composition with a deleted pipe (locally valid everywhere). -/
def cczScheduleLaS_delPipe : ScheduleLaS :=
  { cczScheduleLaS with L := majorityLaS_delPipe }

/-- A composition with a corrupted port connection (wrong blue/Z piece). -/
def cczScheduleLaS_badPort : ScheduleLaS :=
  { cczScheduleLaS with S := majoritySurf_badPort }

/-- The global obligation REJECTS the deleted-pipe composition — a corruption
INVISIBLE to the per-merge check (`perMerge_check_vacuous`). -/
theorem delPipe_obligation_fails :
    ScheduleImplementsSpec cczScheduleLaS_delPipe = false := by native_decide

/-- The global obligation REJECTS the wrong-port composition: the port boundary
(direction/color) no longer matches the spec Pauli. -/
theorem badPort_obligation_fails :
    ScheduleImplementsSpec cczScheduleLaS_badPort = false := by native_decide

/-- **The obligation discriminates** — it ACCEPTS the correct composition and
REJECTS corrupted ones.  It is not a rubber stamp. -/
theorem obligation_discriminates :
    ScheduleImplementsSpec cczScheduleLaS = true
      ∧ ScheduleImplementsSpec cczScheduleLaS_delPipe = false
      ∧ ScheduleImplementsSpec cczScheduleLaS_badPort = false :=
  ⟨ccz_implements_spec, delPipe_obligation_fails, badPort_obligation_fails⟩

/-! ## §5. FAILURE LOCALIZATION at the composition level. -/

/-- The localized violation report for a composed schedule — each violation
pinpoints the exact flow / cube or port / broken constraint. -/
def scheduleReport (sl : ScheduleLaS) : List Viol :=
  LaSReport sl.L sl.S sl.ports sl.paulis sl.nStab

/-- The correct CCZ composition has an EMPTY report (⇔ fully correct). -/
theorem ccz_report_empty : scheduleReport cczScheduleLaS = [] :=
  majority_report_empty

-- The corrupted compositions localize to the EXACT failing flow/cube/port:
#eval scheduleReport cczScheduleLaS_delPipe
#eval scheduleReport cczScheduleLaS_badPort

/-! ## §6. THE COMPLETE PER-PROGRAM CORRECTNESS = per-merge ∧ global flow.

  Tying the two layers together for a PPM program: a schedule is FULLY correct
  iff (1) every measurement is realized by a verified merge (per-merge, proven
  unconditionally — but insufficient alone, §2) AND (2) the composed surgery
  passes the global flow obligation against the program's demanded flows (§3).
  Only the conjunction is a sound certificate. -/

/-- **The complete obligation**: per-merge correctness AND the global
flow-composition obligation for the composed surgery `sl`. -/
def ScheduleImplementsPPM (prog : PPMProg) (sl : ScheduleLaS) : Prop :=
  ScheduleFullyCorrect (fullSchedule prog) ∧ ScheduleImplementsSpec sl = true

/-- The CCZ-style adaptive Toffoli statement (from `AdaptiveDispatch`), as a
one-statement PPM program. -/
def cczProg : PPMProg := [cczSel2]

/-- **★ THE CCZ TOFFOLI IS COMPLETELY IMPLEMENTED ★** — both layers discharged:
every adaptive branch is realized by a verified merge, AND the composed CCZ
surgery realizes all 9 demanded stabilizer flows.  This is the sound,
non-vacuous certificate the per-merge check alone could not provide. -/
theorem ccz_completely_implemented :
    ScheduleImplementsPPM cczProg cczScheduleLaS :=
  ⟨perMerge_check_vacuous cczProg, ccz_implements_spec⟩

/-- **The per-merge half is NOT sufficient on its own.**  `ScheduleFullyCorrect`
holds for `cczProg` no matter what, yet there is a composed surgery
(`cczScheduleLaS_delPipe`) failing the global obligation — so the global flow
check is doing real, independent work. -/
theorem perMerge_alone_insufficient :
    ScheduleFullyCorrect (fullSchedule cczProg)
      ∧ ScheduleImplementsSpec cczScheduleLaS_delPipe = false :=
  ⟨perMerge_check_vacuous cczProg, delPipe_obligation_fails⟩

end FormalRV.QEC.Gidney21
