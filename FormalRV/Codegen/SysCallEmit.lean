/-
  FormalRV.Codegen.SysCallEmit — a textual "device program" syntax that emits BOTH physical
  operations and system calls from one schedule.

  The `Architecture.SysCall` IR already unifies the two:
    * PHYSICAL operations — `Gate1q`, `Gate2q`, `Measure`, `TransitQubit` (the routing/transit);
    * SYSTEM calls       — `RequestFreshAncilla`, `RequestMagicState`, `DecodeSyndrome`,
                           `PauliFrameUpdate`.
  A `Schedule = List SysCall` therefore already interleaves both.  This file renders a schedule to
  a timestamped, category-tagged textual program (`DEVICE-PROGRAM 1.0`) so a backend can read off a
  single stream containing the quantum gates AND the classical/factory/decoder system calls.

  Rendering is a syntactic serialization; the schedule's MEANING (timing, conflicts, the wait law,
  the I1–I4 invariants) is what `System.DeviceSchedule` / `ScheduleInvariantsExplicit` verify.
-/
import FormalRV.System.Core.Architecture

namespace FormalRV.Codegen.SysCallEmit

open FormalRV.System.Architecture

def qref (q : Nat) : String := "q[" ++ toString q ++ "]"

/-! ## Canonical gate / basis name tables

    The DEVICE-PROGRAM syntax is EXPLICIT about which gate an op is
    (`gate=CNOT`, never an opaque numeral): the checkers verify both that
    the named gate is SUPPORTED by the backend and that its declared time
    matches the hardware gate table.  These tables are the single source
    of truth for the numeric-id ↔ name correspondence used by the emitter,
    the Lean parser (`Codegen/DeviceProgramParse`), and (by name) the
    FTQ-VM's gate tables. -/

/-- Canonical two-qubit gate names, indexed by `gate_id`. -/
def gate2qNames : List String := ["CNOT", "CZ", "SWAP", "XX", "ZZ"]

/-- Canonical single-qubit gate names, indexed by `gate_id`. -/
def gate1qNames : List String := ["X", "Y", "Z", "H", "S", "T", "Sdg", "Tdg"]

/-- Canonical measurement basis names, indexed by `basis`. -/
def basisNames : List String := ["Z", "X", "Y"]

def gate2qName (g : Nat) : String := (gate2qNames[g]?).getD s!"G2_{g}"
def gate1qName (g : Nat) : String := (gate1qNames[g]?).getD s!"G1_{g}"
def basisName  (b : Nat) : String := (basisNames[b]?).getD s!"B_{b}"

/-- Inverse lookups (used by the parser; `none` = unknown name). -/
def gate2qIdOf (s : String) : Option Nat := gate2qNames.idxOf? s
def gate1qIdOf (s : String) : Option Nat := gate1qNames.idxOf? s
def basisIdOf  (s : String) : Option Nat := basisNames.idxOf? s

/-- Is a SysCall a PHYSICAL operation or a SYSTEM call? -/
def categoryOf : SysCallKind → String
  | .Gate1q _ _          => "PHYS"
  | .Gate2q _ _ _        => "PHYS"
  | .Measure _ _         => "PHYS"
  | .TransitQubit _ _    => "PHYS"
  | .RequestFreshAncilla _ => "SYS "
  | .RequestMagicState _   => "SYS "
  | .DecodeSyndrome _      => "SYS "
  | .PauliFrameUpdate _    => "SYS "

/-- Render one SysCall's operation.  Gates and bases are rendered by NAME
    (`gate=CNOT`, `basis=Z`) and the ancilla request names its exact qubit
    (`request_ancilla q[100]`) — explicit, checkable syntax. -/
def renderKind : SysCallKind → String
  | .Gate1q q g            => "gate1q             " ++ qref q ++ " gate=" ++ gate1qName g
  | .Gate2q a b g          => "gate2q             " ++ qref a ++ "," ++ qref b ++ " gate=" ++ gate2qName g
  | .Measure q bas         => "measure            " ++ qref q ++ " basis=" ++ basisName bas
  | .TransitQubit q c      => "transit            " ++ qref q ++ " via channel=" ++ toString c
  | .RequestFreshAncilla site => "request_ancilla    " ++ qref site
  | .RequestMagicState z   => "request_magic      factory=" ++ toString z
  | .DecodeSyndrome r      => "decode_syndrome    round=" ++ toString r
  | .PauliFrameUpdate c    => "pauli_frame_update corr=" ++ toString c

/-- One program line: time window, category, operation. -/
def renderCall (sc : SysCall) : String :=
  "[" ++ toString sc.begin_us ++ "," ++ toString sc.end_us ++ ")us  "
    ++ categoryOf sc.kind ++ "  " ++ renderKind sc.kind

/-- Emit a full device program from a schedule (physical ops + system calls, in one stream). -/
def emitSchedule (name : String) (sched : Schedule) : String :=
  String.intercalate "\n"
    ([ "DEVICE-PROGRAM 1.0;",
       "// " ++ name ++ "  (PHYS = physical op, SYS = system call)" ] ++ sched.map renderCall)

/-- Count of physical-operation lines emitted. -/
def physCount (sched : Schedule) : Nat :=
  (sched.filter (fun sc => categoryOf sc.kind == "PHYS")).length
/-- Count of system-call lines emitted. -/
def sysCount (sched : Schedule) : Nat :=
  (sched.filter (fun sc => categoryOf sc.kind == "SYS ")).length

/-! ## Example: one magic-state Toffoli (π/8 rotation) as physical ops + system calls.

    A `T`/CCZ gate via magic-state consumption: distill a magic state (SYS), route it to the
    processor (PHYS transit), do the lattice-surgery joint measurement / teleport (PHYS gate2q +
    measure), decode the outcome (SYS), and apply the feed-forward Pauli correction (SYS). -/
def toffoliViaTeleport : Schedule :=
  [ { kind := SysCallKind.RequestMagicState 3,    begin_us := 0,  end_us := 12 },
    { kind := SysCallKind.TransitQubit 100 1,     begin_us := 12, end_us := 13 },
    { kind := SysCallKind.Gate2q 0 100 0,         begin_us := 13, end_us := 14 },
    { kind := SysCallKind.Measure 100 0,          begin_us := 14, end_us := 15 },
    { kind := SysCallKind.DecodeSyndrome 7,       begin_us := 15, end_us := 16 },
    { kind := SysCallKind.PauliFrameUpdate 7,     begin_us := 16, end_us := 17 } ]

/-- Example: TWO magic states distilled in PARALLEL factories (overlapping `request_magic` system
    calls), each routed and teleported into a distinct data qubit on disjoint channels — physical
    ops and system calls interleaved and concurrent. -/
def parallelTwoMagic : Schedule :=
  [ { kind := SysCallKind.RequestMagicState 3,  begin_us := 0,  end_us := 12 },   -- factory A
    { kind := SysCallKind.RequestMagicState 4,  begin_us := 0,  end_us := 12 },   -- factory B (parallel)
    { kind := SysCallKind.TransitQubit 100 1,   begin_us := 12, end_us := 13 },
    { kind := SysCallKind.TransitQubit 102 2,   begin_us := 12, end_us := 13 },
    { kind := SysCallKind.Gate2q 0 100 0,       begin_us := 13, end_us := 14 },
    { kind := SysCallKind.Gate2q 2 102 0,       begin_us := 13, end_us := 14 },
    { kind := SysCallKind.Measure 100 0,        begin_us := 14, end_us := 15 },
    { kind := SysCallKind.Measure 102 0,        begin_us := 14, end_us := 15 },
    { kind := SysCallKind.DecodeSyndrome 8,     begin_us := 15, end_us := 16 } ]

-- The example programs are emitted (printed) by the standalone demo
-- `FormalRV/Codegen/SysCallEmitDemo.lean`; this module is import-only (no `#eval`) so it can be part
-- of the umbrella `lake build`.

end FormalRV.Codegen.SysCallEmit
