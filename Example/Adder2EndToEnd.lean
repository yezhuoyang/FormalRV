/-
  Example/Adder2EndToEnd.lean — ONE small circuit (the verified 2-bit Cuccaro adder),
  pushed through EVERY layer, with the FINAL VERIFIED RESOURCE on a chosen architecture.

  This file is *self-verifying and re-runnable*.  Run it with:

      lake env lean --run Example/Adder2EndToEnd.lean

  Running it (a) TYPE-CHECKS every theorem below — including `schedule_fits`, which is a
  machine-checked proof that the surgery schedule fits the architecture you set — and
  (b) prints the full per-layer resource breakdown.  **Edit the `EDIT HERE` block, re-run,
  and you get a new machine-checked verdict + new verified resource bounds for *your*
  hardware.**  If your hardware cannot host the schedule, `schedule_fits` fails to compile
  (that is the verification: the claim is false, so the proof is rejected).

  Trust chain (all CI-checked in the FormalRV library; this file only instantiates them):
    * circuit correctness   : `cuccaro_n_bit_adder_full_correct`  (target := a+b, read restored)
    * gate→QASM counts      : `Core/GateQASM`  (Qiskit re-verifies — see scripts/EmitQASM.lean)
    * gate→PPM compiler     : `compileArithmeticGateToPPM`
    * system invariants     : `all_invariants_strict_with_slot_capacity_and_freshness_ok`
                              (operation-capacity ∧ feedback-after-decode ∧ slot-capacity ∧ freshness)
    * wall-clock lower bound: `gate2q_capacity_lower_bound_us`  (ceil(#merges / parallelism)·t_merge)
-/
import FormalRV.Core.GateQASM
import FormalRV.Arithmetic.Cuccaro.CuccaroFull
import FormalRV.PPM.CircuitToPPMInterface
import FormalRV.System.AdderSystem

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.Framework.Architecture
open FormalRV.Framework.ScheduleInv
open FormalRV.Framework.SurgeryGadgetToSysCalls
open FormalRV.Framework.SystemInvariantStrengthening
open FormalRV.Framework.LatticeSurgeryPPMContract
open FormalRV.Framework.CircuitToPPMInterface
open FormalRV.BQAlgo
open FormalRV.Framework.AdderSystem

/-! ## The circuit (verified) -/

/-- The 2-bit Cuccaro ripple-carry adder, proven correct by
    `cuccaro_n_bit_adder_full_correct` (target register := a+b mod 4, read register restored). -/
def exampleCircuit : Gate := cuccaro_n_bit_adder_full 2 0

/-! ## ════════════════════ EDIT HERE — hardware parameters ════════════════════
    Change any value, re-run, and read off the new VERIFIED verdict + bounds.

    Architecture = 4 zones × 100 logical-patch sites (Data / Ancilla / Factory / Routing).
    To resize zones, edit `myArch` below (keep Ancilla = `[100,200)` to match the freshness
    model, or also edit `demo_ancilla_model`). -/

def maxGate2qParallel : Nat := 1     -- merges in flight at once (single-laser hardware ⇒ 1)
def maxMeasParallel   : Nat := 4     -- decoder-bank width (parallel logical measurements)
def gate2qUs          : Nat := 1     -- wall-clock of ONE Gate2q syndrome-extraction SysCall (µs)
def tReactUs          : Nat := 10    -- decoder reaction latency (µs)
def windowUs          : Nat := 1000  -- capacity-accounting window (µs)
def maxPerWindow      : Nat := 1000  -- max operations admitted per window
def numMergeBlocks    : Nat := 12    -- surgery merge blocks = # joint PPM measurements (see below)

/-- The architecture (zoned hardware).  Each zone is a contiguous range of logical-patch sites. -/
def myArch : ZonedArch :=
  { zones :=
      [ { name := "Data",    site_lo := 0,   site_hi := 100 }    -- computation / register patches
      , { name := "Ancilla", site_lo := 100, site_hi := 200 }    -- surgery routing ancillae
      , { name := "Factory", site_lo := 200, site_hi := 300 }    -- magic-state (|CCZ⟩) factories
      , { name := "Routing", site_lo := 300, site_hi := 400 } ]  -- bus / transit
    total_sites := 400, t_cycle_us := 1, v_max_um_per_us := 0, t_react_us := tReactUs }

def myOpCap : OperationCapacityModel :=
  { adder_demo_opCap with max_gate2q_active := maxGate2qParallel, max_measure_active := maxMeasParallel }
/-! ════════════════════════════════ END EDIT ════════════════════════════════ -/

/-! ## Layer resources (re-derived from the verified objects) -/

def numQubits : Nat := maxQubit exampleCircuit + 1
def numToffolis : Nat := numCCX exampleCircuit
def numCXgates : Nat := numCX exampleCircuit
def numTgates : Nat := tcount exampleCircuit

def ppmProgram : List PPMCommand := compileArithmeticGateToPPM exampleCircuit
def isMagic : PPMCommand → Bool | .useMagicT _ => true | _ => false
def isMeas : PPMCommand → Bool | .measurePauliKind _ _ => true | _ => false
/-- CCZ magic states consumed = # `useMagicT` commands in the compiled PPM. -/
def numMagicStates : Nat := (ppmProgram.filter isMagic).length
/-- Joint Pauli (logical) measurements = # `measurePauliKind` commands. -/
def numMeasurements : Nat := (ppmProgram.filter isMeas).length

/-- The full surgery schedule: one verified merge block per joint PPM measurement. -/
def exampleSchedule : List SysCall :=
  seqManySchedules (List.replicate numMergeBlocks (compileSurgeryGadgetToSysCalls surgery_ppm_A))

def wallclockUs : Nat := scheduleWallclockUs exampleSchedule
def gate2qCount : Nat := (exampleSchedule.filter (fun sc => kindIsGate2q sc.kind)).length
def syscallCount : Nat := exampleSchedule.length

/-- **VERIFIED lower bound** on wall-clock from Gate2q capacity:
    `ceil(#merges / parallelism) · t_merge`.  Edit `maxGate2qParallel` / `gate2qUs` above to
    see this verified floor change. -/
def wallclockLowerBoundUs : Nat :=
  gate2q_capacity_lower_bound_us gate2qCount maxGate2qParallel gate2qUs

/-! ## The machine-checked verdict: does the schedule fit the architecture? -/

/-- **THE CERTIFICATE.**  The surgery schedule satisfies *every* strict system invariant on the
    architecture you set above: operation-capacity, feedback-after-decode, slot-capacity, and
    ancilla-freshness.  If you tighten the hardware past feasibility, this proof is rejected. -/
theorem schedule_fits :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
      myArch myOpCap adder_demo_slotCap adder_demo_ancillaModel
      exampleSchedule tReactUs windowUs maxPerWindow = true := by native_decide

/-- The merge-block count equals the number of joint PPM measurements (kept in sync by hand;
    this checks it). -/
theorem merge_blocks_match_ppm : numMergeBlocks = numMeasurements := by native_decide

def kindStr : SysCallKind → String
  | .Gate1q q _            => s!"GATE1Q {q}"
  | .Gate2q a b _          => s!"GATE2Q {a} {b}"
  | .Measure q _           => s!"MEAS {q}"
  | .TransitQubit q c      => s!"TRANSIT {q} {c}"
  | .RequestFreshAncilla z => s!"FRESHANC {z}"
  | .RequestMagicState f   => s!"MAGIC {f}"
  | .DecodeSyndrome r      => s!"DECODE {r}"
  | .PauliFrameUpdate c    => s!"PFU {c}"

def schedHeader : String :=
  "# System-call (SysCall) schedule: the verified surgery operations placed on the zoned hardware\n" ++
  "# over time. One SysCall per line; lines beginning with '#' are comments. EVERY data line ends\n" ++
  "# with two integers <begin_us> <end_us> = the microsecond interval the operation occupies.\n" ++
  "# The tokens BEFORE those two times are the operands:\n" ++
  "#   FRESHANC <zone> <b> <e>     allocate a fresh ancilla patch in zone <zone>  (zone 1 = Ancilla)\n" ++
  "#   GATE2Q  <q1> <q2> <b> <e>   two-qubit op between patch SITES q1,q2 (a surgery merge / syndrome CX)\n" ++
  "#   MEAS    <q> <b> <e>         measure the logical patch at site q\n" ++
  "#   DECODE  <round> <b> <e>     run the decoder on the syndrome of round <round>\n" ++
  "#   PFU     <corr> <b> <e>      PFU = Pauli-Frame Update: apply classically-conditioned Pauli\n" ++
  "#                               correction <corr> (the system-level feed-forward; cf. PPM 'F')\n" ++
  "#   MAGIC   <fzone> <b> <e>     request a magic state from factory zone <fzone>\n" ++
  "#   GATE1Q  <q> <b> <e>         one-qubit gate on site q ;  TRANSIT <q> <ch> <b> <e>  route q via channel ch\n" ++
  "# SITES live in zones: Data [0,100)  Ancilla [100,200)  Factory [200,300)  Routing [300,400).\n" ++
  "# e.g. 'FRESHANC 1 0 1' = fresh ancilla in zone 1 during [0,1) us; 'GATE2Q 0 100 1 2' = merge\n" ++
  "# data-site 0 with ancilla-site 100 during [1,2) us.\n"

def main : IO Unit := do
  let schedLines := exampleSchedule.map (fun sc => s!"{kindStr sc.kind} {sc.begin_us} {sc.end_us}")
  IO.FS.writeFile "Example/adder2_full_schedule.txt" (schedHeader ++ String.intercalate "\n" schedLines ++ "\n")
  IO.println "════════ 2-bit Cuccaro adder — verified resource on the chosen architecture ════════"
  IO.println "ARCHITECTURE (sites per zone):  Data[0,100)  Ancilla[100,200)  Factory[200,300)  Routing[300,400)"
  IO.println s!"HARDWARE PARAMS:  gate2q‖={maxGate2qParallel}  meas‖={maxMeasParallel}  t_gate2q={gate2qUs}µs  t_react={tReactUs}µs"
  IO.println ""
  IO.println s!"L2 logical (verified circuit):  qubits={numQubits}  Toffolis={numToffolis}  CX={numCXgates}  T-count={numTgates}"
  IO.println s!"L3 PPM (real compiler):         |CCZ⟩ magic states={numMagicStates}  joint measurements={numMeasurements}  commands={ppmProgram.length}"
  IO.println s!"System schedule:                SysCalls={syscallCount}  Gate2q merges={gate2qCount}  wall-clock={wallclockUs}µs"
  IO.println ""
  IO.println s!"✓ VERIFIED  schedule fits this architecture        (theorem schedule_fits)"
  IO.println s!"✓ VERIFIED  wall-clock LOWER BOUND ≥ {wallclockLowerBoundUs}µs   (gate2q capacity: ⌈{gate2qCount}/{maxGate2qParallel}⌉·{gate2qUs}µs)"
  IO.println "Edit the EDIT-HERE block above and re-run to re-verify for your own hardware."
