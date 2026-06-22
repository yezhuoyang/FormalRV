/-
  FormalRV.Codegen.DeviceProgramParse — Lean-side parser of the shared
  DEVICE-PROGRAM 1.0 syntax (plus the shared backend JSON), closing the
  Lean ↔ FTQ-VM interop loop:

      Lean Schedule ──emitSchedule──▶ program.dp ──┬─▶ this parser ─▶ List SysCall
                                                   │      └─▶ the decidable invariant
                                                   │          bundle (same checkers
                                                   │          the theorems use)
                                                   └─▶ ftq_vm (Python) ─▶ discrete-event
                                                          finite-service verdict

  One schedule file, two independent checkers.  The grammar is exactly what
  `Codegen/SysCallEmit.emitSchedule` produces (round-trip: `parse (emit s) = s`,
  asserted at runtime by `scripts/CheckDeviceProgram.lean`); the backend JSON is
  the FTQ-VM machine description, from which this module reconstructs the
  `ZonedArch`, `OperationCapacityModel`, `SlotCapacityModel` and `AncillaModel`
  the strict bundle needs (zone ids = zones sorted by `site_lo`; the `x-lean`
  block carries the Lean-only parameters).
-/
import Lean.Data.Json
import FormalRV.System.Core.Architecture
import FormalRV.System.Invariants.ScheduleInvariantsExplicit
import FormalRV.System.Invariants.SystemInvariantStrengthening
import FormalRV.System.Params.HardwareCatalog
import FormalRV.Codegen.SysCallEmit

namespace FormalRV.Codegen.DeviceProgramParse

open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.HardwareCatalog (GateTable gate_support_ok)
open FormalRV.Codegen.SysCallEmit (gate1qIdOf gate2qIdOf basisIdOf)
open Lean (Json)

/-! ## §1. DEVICE-PROGRAM text → `List SysCall` -/

private def parseNat (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => .ok n
  | none   => .error s!"expected a number, got {s}"

/-- Parse `[a,b)us` into `(a, b)`. -/
private def parseInterval (tok : String) : Except String (Nat × Nat) := do
  let body ← match tok.dropPrefix? "[" with
    | some r => pure r.toString
    | none   => .error s!"expected [a,b)us, got {tok}"
  let body ← match body.dropSuffix? ")us" with
    | some r => pure r.toString
    | none   => .error s!"expected [a,b)us, got {tok}"
  match body.splitOn "," with
  | [a, b] => return (← parseNat a, ← parseNat b)
  | _      => .error s!"expected [a,b)us, got {tok}"

/-- Parse `q[7]` into `7`. -/
private def parseQref (tok : String) : Except String Nat := do
  let body ← match tok.dropPrefix? "q[" with
    | some r => pure r.toString
    | none   => .error s!"expected q[<site>], got {tok}"
  match body.dropSuffix? "]" with
  | some r => parseNat r.toString
  | none   => .error s!"expected q[<site>], got {tok}"

/-- Parse `key=7` (checking the key) into `7`. -/
private def parseKV (key : String) (tok : String) : Except String Nat :=
  match tok.splitOn "=" with
  | [k, v] => if k = key then parseNat v
              else .error s!"expected {key}=<n>, got {tok}"
  | _      => .error s!"expected {key}=<n>, got {tok}"

/-- Parse `key=NAME` through a canonical name table (gates and bases are
    NAMED, never numeric: `gate=CNOT`, `basis=Z`). -/
private def parseNamedKV (key : String) (lookup : String → Option Nat)
    (tok : String) : Except String Nat :=
  match tok.splitOn "=" with
  | [k, v] =>
      if k = key then
        match lookup v with
        | some n => .ok n
        | none   => .error s!"unknown {key} name {v} (names are explicit: gate=CNOT, basis=Z, ...)"
      else .error s!"expected {key}=<name>, got {tok}"
  | _ => .error s!"expected {key}=<name>, got {tok}"

/-- Parse one op line (already known to start with `[`). -/
private def parseOpLine (line : String) : Except String SysCall := do
  let tokens := (line.splitOn " ").filter (· ≠ "")
  match tokens with
  | interval :: _cat :: op :: args => do
      let (b, e) ← parseInterval interval
      if e ≤ b then .error s!"empty/inverted interval in {line}"
      let kind : SysCallKind ←
        match op, args with
        | "gate1q", [q, g] => do
            let qn ← parseQref q
            let gn ← parseNamedKV "gate" gate1qIdOf g
            pure (SysCallKind.Gate1q qn gn)
        | "gate2q", [qq, g] => do
            match qq.splitOn "," with
            | [qa, qb] => do
                let a ← parseQref qa
                let bq ← parseQref qb
                let gn ← parseNamedKV "gate" gate2qIdOf g
                pure (SysCallKind.Gate2q a bq gn)
            | _ => .error s!"expected q[i],q[j], got {qq}"
        | "measure", [q, bas] => do
            let qn ← parseQref q
            let bn ← parseNamedKV "basis" basisIdOf bas
            pure (SysCallKind.Measure qn bn)
        | "transit", [q, via_, c] => do
            if via_ ≠ "via" then
              .error s!"expected 'via', got {via_}"
            else do
              let qn ← parseQref q
              let cn ← parseKV "channel" c
              pure (SysCallKind.TransitQubit qn cn)
        | "request_ancilla", [q] => do
            -- the request names its EXACT qubit (no fungible zone form)
            let site ← parseQref q
            pure (SysCallKind.RequestFreshAncilla site)
        | "request_magic", [f] => do
            let fn ← parseKV "factory" f
            pure (SysCallKind.RequestMagicState fn)
        | "decode_syndrome", [r] => do
            let rn ← parseKV "round" r
            pure (SysCallKind.DecodeSyndrome rn)
        | "pauli_frame_update", [c] => do
            let cn ← parseKV "corr" c
            pure (SysCallKind.PauliFrameUpdate cn)
        | _, _ => .error s!"unknown op or bad arity: {line}"
      return { kind := kind, begin_us := b, end_us := e }
  | _ => .error s!"malformed op line: {line}"

/-- Parse a full DEVICE-PROGRAM 1.0 text into a `Schedule`. -/
def parseDeviceProgram (text : String) : Except String (List SysCall) := do
  let lines := (text.splitOn "\n").map (·.trimAscii.toString)
  match lines with
  | [] => .error "empty file"
  | header :: rest =>
      if ¬ header.startsWith "DEVICE-PROGRAM" then
        .error "missing DEVICE-PROGRAM header"
      else
        rest.foldlM (init := []) (fun acc line => do
          if line.isEmpty ∨ line.startsWith "//" ∨ line.startsWith "--" then
            return acc
          else
            return acc ++ [← parseOpLine line])

/-! ## §1.b Parallel-layer recognition

    Ops sharing the SAME half-open window `[begin, end)` form one
    simultaneous layer — written on separate lines, recognized after
    parsing.  Both checkers use the identical exact-interval rule (overlap
    that is not exact equality is handled by the resource/exclusivity
    checkers, not by layer grouping). -/

/-- Group a schedule into parallel layers by exact `[begin, end)` window,
    preserving first-occurrence order. -/
def parallelGroups (sched : List SysCall) :
    List ((Nat × Nat) × List SysCall) :=
  sched.foldl (init := []) fun acc sc =>
    let key := (sc.begin_us, sc.end_us)
    if acc.any (fun g => g.1 = key) then
      acc.map (fun g => if g.1 = key then (g.1, g.2 ++ [sc]) else g)
    else
      acc ++ [(key, [sc])]

/-- The widest simultaneous layer (1 = fully sequential). -/
def maxSimultaneous (sched : List SysCall) : Nat :=
  (parallelGroups sched).foldl (fun acc g => Nat.max acc g.2.length) 0

/-! ## §1.c Gate support: named gates must exist in the backend table

    `GateTable` and `gate_support_ok` are the catalog's
    (`System/Params/HardwareCatalog.lean`) — the single source of hardware
    assumptions; this parser only reconstructs the table from the backend
    JSON (§2). -/

/-! ## §2. Backend JSON → architecture + capacity models -/

/-- Everything the strict invariant bundle needs, reconstructed from the
    shared backend file. -/
structure ParsedBackend where
  arch          : ZonedArch
  opCap         : OperationCapacityModel
  slotCap       : SlotCapacityModel
  ancillaModel  : AncillaModel
  gateTable     : GateTable
  t_react_us    : Nat
  window_us     : Nat
  max_per_window : Nat
  /-- syndrome-stream contract (bits_per_measure, window_us, max_bits),
      from the backend's `throughput_caps` entry over `measure` ops. -/
  syndrome      : Option (Nat × Nat × Nat) := none
  /-- magic supply (initial stock, production period, per period) — from
      the `tokens.MagicState` inventory and `x-lean` factory fields. -/
  magic         : Nat × Nat × Nat := (0, 0, 0)

private def getNatD (j : Json) (key : String) (dflt : Nat) : Nat :=
  match j.getObjVal? key with
  | .ok v  => match v.getNat? with
              | .ok n => n
              | .error _ => dflt
  | .error _ => dflt

private def getBoolD (j : Json) (key : String) (dflt : Bool) : Bool :=
  match j.getObjVal? key with
  | .ok v  => v.getBool?.toOption.getD dflt
  | .error _ => dflt

private def objEntries (j : Json) : Except String (List (String × Json)) := do
  let node ← j.getObj?
  return node.foldl (fun acc k v => acc ++ [(k, v)]) []

/-- Parse the shared backend JSON. -/
def parseBackend (text : String) : Except String ParsedBackend := do
  let j ← Json.parse text
  let zonesJ ← j.getObjVal? "zones"
  let entries ← objEntries zonesJ
  -- (site_lo, name, count, reset_required) sorted by site_lo: zone ids by order
  let mut zs : List (Nat × String × Nat × Bool) := []
  for (name, zj) in entries do
    let lo := getNatD zj "site_lo" 0
    let count := getNatD zj "count" 1
    let reset := getBoolD zj "reset_required" false
    zs := zs ++ [(lo, name, count, reset)]
  let sorted := zs.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  let archZones := sorted.map (fun (lo, name, count, _) =>
    ({ name := name, site_lo := lo, site_hi := lo + count } : ArchZone))
  let totalSites := sorted.foldl (fun acc (lo, _, count, _) =>
    Nat.max acc (lo + count)) 0
  let xlean := (j.getObjVal? "x-lean").toOption.getD Json.null

  -- decoder service: first entry of kind "service" under resources
  let resources ← objEntries ((j.getObjVal? "resources").toOption.getD (Json.mkObj []))
  let mut workers := 100
  let mut tReact := 10
  for (_, rj) in resources do
    if ((rj.getObjVal? "kind").toOption.bind (·.getStr?.toOption)) = some "service" then
      workers := getNatD rj "workers" 100
      tReact := getNatD rj "max_latency_us" 10

  let gates := (j.getObjVal? "gates").toOption.getD (Json.mkObj [])
  let gateCap (g : String) : Nat :=
    match gates.getObjVal? g with
    | .ok gj => getNatD gj "max_parallel" 100
    | .error _ => 100
  -- the hardware gate table: name ↦ (duration_us, qubit arity).
  -- The class-level caps below take the MIN across a class's entries
  -- (exact when the class has one entry, conservative otherwise).
  let gateEntries ← objEntries gates
  let gateTable : GateTable := gateEntries.map (fun (name, gj) =>
    (name, getNatD gj "duration_us" 1, getNatD gj "qubits" 1))
  let classCap (arity : Nat) (skip : List String) : Nat :=
    gateEntries.foldl (init := 100) fun acc (name, gj) =>
      if skip.contains name then acc
      else if getNatD gj "qubits" 1 = arity then
        Nat.min acc (getNatD gj "max_parallel" 100)
      else acc

  let arch : ZonedArch :=
    { zones := archZones
      total_sites := totalSites
      t_cycle_us := getNatD xlean "t_cycle_us" 1
      v_max_um_per_us := getNatD xlean "v_max_um_per_us" 0
      t_react_us := tReact }
  let opCap : OperationCapacityModel :=
    { max_gate1q_active        := classCap 1 ["measure", "request_ancilla"]
      max_gate2q_active        := classCap 2 []
      max_measure_active       := gateCap "measure"
      max_decode_active        := workers
      max_feedback_active      := getNatD xlean "max_feedback_active" 100
      max_magic_req_active     := getNatD xlean "max_magic_req_active" 100
      max_fresh_ancilla_active := getNatD xlean "max_fresh_ancilla_active" 100
      max_transit_active       := getNatD xlean "max_transit_active" 100 }
  let slotCap : SlotCapacityModel :=
    { zones := (sorted.zipIdx).map (fun ((lo, _, count, _), idx) =>
        { zone_id := idx, site_lo := lo, site_hi := lo + count
          slot_capacity := count }) }
  let ancModel : AncillaModel :=
    { zones := ((sorted.zipIdx).filter (fun ((_, _, _, reset), _) => reset)).map
        (fun ((lo, _, count, _), idx) =>
          { zone_id := idx, site_lo := lo, site_hi := lo + count }) }
  -- syndrome-stream contract: the first throughput cap over `measure` ops
  let caps := ((j.getObjVal? "throughput_caps").toOption.bind
    (·.getArr?.toOption)).getD #[]
  let mut syndrome : Option (Nat × Nat × Nat) := none
  for capJ in caps do
    if syndrome.isNone then
      let kinds := ((capJ.getObjVal? "op_kinds").toOption.bind
        (·.getArr?.toOption)).getD #[]
      if kinds.any (fun k => k.getStr?.toOption = some "measure") then
        syndrome := some (getNatD capJ "weight_per_op" 1,
                          getNatD capJ "window_us" 1000,
                          getNatD capJ "max_weight" 0)
  -- magic supply: initial stock from the token table; production curve
  -- from x-lean (absent = no factory)
  let magicStock :=
    match (j.getObjVal? "tokens").toOption.bind
      (fun t => (t.getObjVal? "MagicState").toOption) with
    | some tj => getNatD tj "initial_inventory" 0
    | none    => 0
  return { arch := arch, opCap := opCap, slotCap := slotCap
           ancillaModel := ancModel, gateTable := gateTable
           t_react_us := tReact
           window_us := getNatD xlean "window_us" 1000
           max_per_window := getNatD xlean "max_per_window" 1000
           syndrome := syndrome
           magic := (magicStock, getNatD xlean "magic_period_us" 0,
                     getNatD xlean "magic_per_period" 0) }

/-! ## §3. The file-driven verdict: parse + run the SAME strict bundle -/

/-- Parse the shared backend + program files; the verdict conjoins

    1. `gate_support_ok` — every named gate/measure/request is SUPPORTED
       by the backend gate table and takes exactly its hardware time;
    2. the strict invariant bundle — the same `Bool` function the
       `native_decide` theorems certify, evaluated on the parsed input. -/
def checkDeviceProgram (backendText programText : String) :
    Except String Bool := do
  let pb ← parseBackend backendText
  let sched ← parseDeviceProgram programText
  return gate_support_ok pb.gateTable sched
    && (match pb.syndrome with
        | some (bits, w, mx) => syndrome_bandwidth_ok bits w mx sched
        | none => true)
    && syndrome_causality_ok sched
    && magic_supply_ok pb.magic.1 pb.magic.2.1 pb.magic.2.2 sched
    && all_invariants_strict_with_slot_capacity_and_freshness_ok
         pb.arch pb.opCap pb.slotCap pb.ancillaModel sched
         pb.t_react_us pb.window_us pb.max_per_window

/-! ## §4. Diagnostics: the CANONICAL CONTRACT CODES

    Both checkers report violations in ONE shared vocabulary, named after
    the violated hardware contract (not after either tool's internal
    mechanism), so the differential corpus compares reasons by literal
    equality.  The FTQ-VM emits the same codes
    (`ftq_vm/backend/device_program.py: CONTRACT_CODES / contract_code`);
    keep the two lists in sync.

      SYNTAX                    — rejected by the parser itself
      GATE_UNSUPPORTED          — a named gate the hardware does not offer
      GATE_DURATION             — a gate claiming ≠ its hardware time
      ARCH_BOUNDS               — a site outside every declared zone
      QUBIT_EXCLUSIVITY         — one qubit, two overlapping ops
      QUBIT_LIFECYCLE           — ancilla freshness (use-before-reset,
                                  reuse-after-measure, double-alloc, leak)
      GATE_PARALLELISM          — gate/measure concurrency caps
      CONTROL_PARALLELISM       — feedback/magic/ancilla/transit op caps
      DECODER_OVERLOAD          — the finite decoder service oversubscribed
                                  (Lean: concurrency > workers; VM: queue
                                  overflow — same contract, the residual
                                  mechanism difference is documented)
      DECODER_REACTION          — a decode exceeding the reaction budget
      FEEDFORWARD_CAUSALITY     — a Pauli-frame update before its decode
                                  result exists
      FEEDFORWARD_LATENCY       — a frame update slower than the cycle
                                  (Lean-side check; VM model gap)
      FEEDFORWARD_FRESHNESS     — a decode result consumed after its
                                  freshness window (VM-side check; Lean
                                  model gap — order-only feedback)
      MAGIC_DEMAND_WINDOW       — magic requests exceeding the demand
                                  window (Lean-side I4; VM model gap)
      MAGIC_SUPPLY              — a magic state consumed with none
                                  available (VM causal supply)
      FACTORY_PORT_EXCLUSIVITY  — overlapping claims on one factory port
      ZONE_CAPACITY             — per-zone slot capacity exceeded -/

open FormalRV.System.LatticeSurgeryPPMContract (factory_exclusivity_ok)

/-- Every named gate exists in the hardware table (support only). -/
def gates_supported_ok (table : GateTable) (sched : List SysCall) : Bool :=
  sched.all fun sc =>
    let known (name : String) : Bool := (table.find? (fun e => e.1 = name)).isSome
    match sc.kind with
    | .Gate1q _ g  => known (FormalRV.Codegen.SysCallEmit.gate1qName g)
    | .Gate2q _ _ g => known (FormalRV.Codegen.SysCallEmit.gate2qName g)
    | .Measure _ _ => known "measure"
    | .RequestFreshAncilla _ => known "request_ancilla"
    | _ => true

/-- Gates PRESENT in the table take exactly their hardware time. -/
def gate_durations_ok (table : GateTable) (sched : List SysCall) : Bool :=
  sched.all fun sc =>
    let check (name : String) : Bool :=
      match table.find? (fun e => e.1 = name) with
      | some (_, d, _) => decide (sc.end_us - sc.begin_us = d)
      | none           => true   -- support is GATE_UNSUPPORTED's job
    match sc.kind with
    | .Gate1q _ g  => check (FormalRV.Codegen.SysCallEmit.gate1qName g)
    | .Gate2q _ _ g => check (FormalRV.Codegen.SysCallEmit.gate2qName g)
    | .Measure _ _ => check "measure"
    | .RequestFreshAncilla _ => check "request_ancilla"
    | _ => true

/-- Physical-gate concurrency (gate1q/gate2q/measure classes). -/
def gate_parallelism_ok (cap : OperationCapacityModel)
    (sched : List SysCall) : Bool :=
  (scheduleEventTimes sched).all fun t =>
    decide (countActiveKindAt kindIsGate1q t sched ≤ cap.max_gate1q_active)
    && decide (countActiveKindAt kindIsGate2q t sched ≤ cap.max_gate2q_active)
    && decide (countActiveKindAt kindIsMeasure t sched ≤ cap.max_measure_active)

/-- Decoder concurrency against the finite worker pool. -/
def decoder_overload_ok (cap : OperationCapacityModel)
    (sched : List SysCall) : Bool :=
  (scheduleEventTimes sched).all fun t =>
    decide (countActiveKindAt kindIsDecode t sched ≤ cap.max_decode_active)

/-- The remaining op-concurrency caps (classical control plane). -/
def control_parallelism_ok (cap : OperationCapacityModel)
    (sched : List SysCall) : Bool :=
  (scheduleEventTimes sched).all fun t =>
    decide (countActiveKindAt kindIsFeedback t sched ≤ cap.max_feedback_active)
    && decide (countActiveKindAt kindIsMagicReq t sched ≤ cap.max_magic_req_active)
    && decide (countActiveKindAt kindIsFreshAnc t sched ≤ cap.max_fresh_ancilla_active)
    && decide (countActiveKindAt kindIsTransit t sched ≤ cap.max_transit_active)

/-- The canonical contract codes violated by the schedule (`[]` = PASS).
    The union of these checks equals `checkDeviceProgram`'s verdict (the
    split refines the bundle's conjuncts without changing their meaning). -/
def diagnose (pb : ParsedBackend) (sched : List SysCall) : List String :=
  let checks : List (String × Bool) :=
    [ ("GATE_UNSUPPORTED",         gates_supported_ok pb.gateTable sched)
    , ("GATE_DURATION",            gate_durations_ok pb.gateTable sched)
    , ("ARCH_BOUNDS",              capacity_in_arch_ok pb.arch sched)
    , ("ZONE_CAPACITY",            capacity_per_cycle_ok pb.arch sched
                                     && slot_capacity_ok pb.slotCap sched)
    , ("QUBIT_EXCLUSIVITY",        exclusivity_ok sched)
    , ("FACTORY_PORT_EXCLUSIVITY", factory_exclusivity_ok sched)
    , ("FEEDFORWARD_LATENCY",      feedback_latency_ok pb.arch.t_cycle_us sched)
    , ("DECODER_REACTION",         decoder_react_ok pb.t_react_us sched)
    , ("MAGIC_DEMAND_WINDOW",      window_throughput_ok sched pb.window_us pb.max_per_window)
    , ("GATE_PARALLELISM",         gate_parallelism_ok pb.opCap sched)
    , ("DECODER_OVERLOAD",         decoder_overload_ok pb.opCap sched)
    , ("CONTROL_PARALLELISM",      control_parallelism_ok pb.opCap sched)
    , ("FEEDFORWARD_CAUSALITY",    feedback_after_decode_ok sched)
    , ("QUBIT_LIFECYCLE",          ancilla_freshness_ok pb.ancillaModel sched)
    , ("SYNDROME_BANDWIDTH",
        match pb.syndrome with
        | some (bits, w, mx) => syndrome_bandwidth_ok bits w mx sched
        | none => true)
    , ("SYNDROME_CAUSALITY",      syndrome_causality_ok sched)
    , ("MAGIC_SUPPLY",
        magic_supply_ok pb.magic.1 pb.magic.2.1 pb.magic.2.2 sched) ]
  (checks.filter (fun c => ¬ c.2)).map (·.1)

/-- Parse both files and report the violated contract codes (`.error` for
    parse failures = the SYNTAX code; `[]` = PASS). -/
def diagnoseDeviceProgram (backendText programText : String) :
    Except String (List String) := do
  let pb ← parseBackend backendText
  let sched ← parseDeviceProgram programText
  return diagnose pb sched

end FormalRV.Codegen.DeviceProgramParse
