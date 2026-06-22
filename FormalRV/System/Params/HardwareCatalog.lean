/-
  FormalRV.System.Params.HardwareCatalog — THE single file where every
  hardware assumption / architecture parameter set is defined.

  ## Why this file exists

  The System layer is parametric: every checker takes the architecture and
  capacity models as ARGUMENTS, so the tool is not tied to any specific
  hardware.  Before this file, however, the parameter sets themselves were
  scattered (demo archs re-typed in several files, two of them verbatim
  mirrors).  This catalog is now the one place to:

    * SEE every hardware assumption the repository uses
      (§3 the catalog; §4 re-exports of the legacy/platform records);
    * CONFIGURE a new machine: write one `HardwareSpec` (§1) — every
      checker input (`ZonedArch`, `OperationCapacityModel`,
      `SlotCapacityModel`, `AncillaModel`, gate table) and the FTQ-VM
      backend JSON are DERIVED from it (§2), so Lean proofs and the VM
      run from the same definition;
    * CHECK any schedule on any spec: `checkScheduleOn` (§2.e) is the
      generic entry point — total in the spec, so users may set parameters
      arbitrarily BEFORE any hardware is fixed;
    * TRUST that parameters are live: §5 proves the same schedule gets
      DIFFERENT verdicts under different specs (reconfigurability is
      observable, not aspirational), and §6 pins the scattered legacy
      definitions to catalog entries by equality theorems.

  ## How to add your machine

      def myMachine : HardwareSpec :=
        { adder_d3 with name := "my-machine"
                        gates := [⟨"CNOT", 2, 2, 4⟩, ...] }

      #eval checkScheduleOn myMachine mySchedule          -- Bool verdict
      theorem my_ok : checkScheduleOn myMachine mySchedule = true := by
        native_decide
      #eval IO.println myMachine.toBackendJson            -- the VM backend

  Workload constants (RSA-2048 / GE2021) live in `Params/RSA2048.lean`
  (imported and re-exported here): workloads are what you RUN, hardware is
  what you RUN IT ON.
-/
import FormalRV.System.Invariants.SystemInvariantStrengthening
import FormalRV.System.Params.HardwareParams
import FormalRV.System.Params.RSA2048
import FormalRV.System.Compile.SurgeryGadgetToSysCalls
import FormalRV.System.Compile.PPMContractInstances
import FormalRV.System.Examples.AdderSystem
import FormalRV.System.Examples.SystemInvariantExamples
import FormalRV.System.Invariants.InvariantFramework
import FormalRV.Codegen.SysCallEmit

namespace FormalRV.System.HardwareCatalog

open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.Codegen.SysCallEmit (gate1qName gate2qName)

/-! ## §1. The unified hardware specification

    One record carrying EVERYTHING the System checkers and the FTQ-VM
    backend need.  Zones must be listed in ascending `site_lo` order
    (zone ids = list positions; `wellFormed` checks it). -/

/-- One gate the hardware supports: name, duration (µs), qubit arity, and
    how many may run simultaneously (control-electronics cap). -/
structure GateSpec where
  name         : String
  duration_us  : Nat
  qubits       : Nat
  max_parallel : Nat := 100
  deriving Repr, Inhabited

/-- One qubit zone: `vm_id` is the FTQ-VM zone identifier (`anc` →
    qubits `anc[0]`, …), `lean_name` the display name used in `ZonedArch`;
    the zone owns global sites `[site_lo, site_lo + count)`.  `tracked`
    zones follow the ancilla freshness lifecycle. -/
structure ZoneSpecH where
  vm_id     : String
  lean_name : String
  kind      : String
  site_lo   : Nat
  count     : Nat
  tracked   : Bool := false
  deriving Repr, Inhabited

/-- The classical decoder pool: finite workers, a reaction-time budget
    (doubles as the architecture's `t_react_us`), and — VM-side — a finite
    job queue. -/
structure DecoderSpec where
  workers            : Nat := 100
  max_latency_us     : Nat := 10
  queue_capacity     : Nat := 1000
  processing_time_us : Nat := 1
  deriving Repr, Inhabited

/-- A token kind the backend stocks/constrains (VM side): initial
    inventory and freshness window (`ttl_us = 0` ⇒ never expires). -/
structure TokenSpec where
  kind              : String
  initial_inventory : Nat := 0
  ttl_us            : Nat := 0
  deriving Repr, Inhabited

/-- The syndrome-stream link contract: each `Measure` injects
    `bits_per_measure` bits (hardware fact — 1 hard bit, or e.g. 64 = 8
    stabilizers × 8-bit soft data when one op reads out a whole d=3
    patch); the link carries at most `max_bits` per `window_us`.
    4 KB/ms ⇒ `window_us := 1000, max_bits := 32768`. -/
structure SyndromeSpec where
  bits_per_measure : Nat := 1
  window_us        : Nat := 1000
  max_bits         : Nat
  deriving Repr, Inhabited

/-- A complete hardware/architecture parameter set. -/
structure HardwareSpec where
  name                     : String
  zones                    : List ZoneSpecH
  gates                    : List GateSpec
  decoder                  : DecoderSpec := {}
  tokens                   : List TokenSpec := []
  /-- syndrome-stream bandwidth contract (`none` = unconstrained link) -/
  syndrome                 : Option SyndromeSpec := none
  /-- magic-state factory production curve: one batch of
      `magic_per_period` states is fully PREPARED every
      `magic_period_us` µs (0 = no production; stock only).  Feeds the
      I6.b supply-causality check with the `MagicState` token stock. -/
  magic_period_us          : Nat := 0
  magic_per_period         : Nat := 0
  t_cycle_us               : Nat := 1
  v_max_um_per_us          : Nat := 0
  /-- magic-state demand window (I4): at most `max_per_window` requests
      may begin in any `window_us` window. -/
  window_us                : Nat := 1000
  max_per_window           : Nat := 1000
  max_feedback_active      : Nat := 100
  max_magic_req_active     : Nat := 100
  max_fresh_ancilla_active : Nat := 100
  max_transit_active       : Nat := 100
  deriving Repr, Inhabited

/-- Zones are listed in ascending `site_lo` order and gates have positive
    durations — the well-formedness a configuration must satisfy. -/
def HardwareSpec.wellFormed (s : HardwareSpec) : Bool :=
  (List.range s.zones.length).all (fun i =>
    match s.zones[i]?, s.zones[i+1]? with
    | some a, some b => decide (a.site_lo + a.count ≤ b.site_lo)
    | _, _           => true)
  && s.gates.all (fun g => decide (0 < g.duration_us))

/-! ## §2. Derivations: one spec → every checker input + the VM backend -/

/-- §2.a The zoned architecture (zone ids = list positions). -/
def HardwareSpec.toZonedArch (s : HardwareSpec) : ZonedArch :=
  { zones := s.zones.map (fun z =>
      { name := z.lean_name, site_lo := z.site_lo, site_hi := z.site_lo + z.count })
    total_sites := s.zones.foldl (fun acc z => Nat.max acc (z.site_lo + z.count)) 0
    t_cycle_us := s.t_cycle_us
    v_max_um_per_us := s.v_max_um_per_us
    t_react_us := s.decoder.max_latency_us }

/-- §2.b Per-kind operation caps.  Gate classes take the MIN across the
    class's entries (exact when one entry per class). -/
def HardwareSpec.toOpCap (s : HardwareSpec) : OperationCapacityModel :=
  let classCap (arity : Nat) (skip : List String) : Nat :=
    s.gates.foldl (init := 100) fun acc g =>
      if skip.contains g.name then acc
      else if g.qubits = arity then Nat.min acc g.max_parallel else acc
  let namedCap (n : String) : Nat :=
    match s.gates.find? (fun g => g.name = n) with
    | some g => g.max_parallel
    | none   => 100
  { max_gate1q_active        := classCap 1 ["measure", "request_ancilla"]
    max_gate2q_active        := classCap 2 []
    max_measure_active       := namedCap "measure"
    max_decode_active        := s.decoder.workers
    max_feedback_active      := s.max_feedback_active
    max_magic_req_active     := s.max_magic_req_active
    max_fresh_ancilla_active := s.max_fresh_ancilla_active
    max_transit_active       := s.max_transit_active }

/-- §2.c Per-zone slot capacities (every site of a zone usable). -/
def HardwareSpec.toSlotCap (s : HardwareSpec) : SlotCapacityModel :=
  { zones := (s.zones.zipIdx).map (fun (z, idx) =>
      { zone_id := idx, site_lo := z.site_lo, site_hi := z.site_lo + z.count
        slot_capacity := z.count }) }

/-- §2.d The freshness-tracked ancilla zones. -/
def HardwareSpec.toAncillaModel (s : HardwareSpec) : AncillaModel :=
  { zones := ((s.zones.zipIdx).filter (fun (z, _) => z.tracked)).map
      (fun (z, idx) =>
        { zone_id := idx, site_lo := z.site_lo, site_hi := z.site_lo + z.count }) }

/-- The gate-support table: name ↦ (duration, arity).  Shared shape with
    `Codegen/DeviceProgramParse.parseBackend`. -/
abbrev GateTable := List (String × Nat × Nat)

def HardwareSpec.toGateTable (s : HardwareSpec) : GateTable :=
  s.gates.map (fun g => (g.name, g.duration_us, g.qubits))

/-- Every named gate / measure / ancilla-request in the schedule is
    SUPPORTED by the table with matching duration (gate times are hardware
    facts).  Mirrored by the FTQ-VM's load-time enforcement. -/
def gate_support_ok (table : GateTable) (sched : List SysCall) : Bool :=
  sched.all fun sc =>
    let dur := sc.end_us - sc.begin_us
    let check (name : String) : Bool :=
      match table.find? (fun e => e.1 = name) with
      | some (_, d, _) => decide (dur = d)
      | none           => false
    match sc.kind with
    | .Gate1q _ g  => check (gate1qName g)
    | .Gate2q _ _ g => check (gate2qName g)
    | .Measure _ _ => check "measure"
    | .RequestFreshAncilla _ => check "request_ancilla"
    | _ => true

/-- The backend's initial `MagicState` stock (from the token table). -/
def HardwareSpec.magicInitialStock (s : HardwareSpec) : Nat :=
  ((s.tokens.find? (fun t => t.kind = "MagicState")).map
    (·.initial_inventory)).getD 0

/-- §2.e **The generic verdict** — gate support ∧ I5 link bandwidth ∧
    I6 causality ∧ the strict invariant bundle, all inputs derived from
    the spec.  Total in `s`: any configuration may be checked, none is
    privileged. -/
def checkScheduleOn (s : HardwareSpec) (sched : List SysCall) : Bool :=
  gate_support_ok s.toGateTable sched
  && (match s.syndrome with
      | some sy => syndrome_bandwidth_ok sy.bits_per_measure sy.window_us
                     sy.max_bits sched
      | none    => true)
  -- I6 space-time causality: measure before decode; prepare before consume
  && syndrome_causality_ok sched
  && magic_supply_ok s.magicInitialStock s.magic_period_us
       s.magic_per_period sched
  && all_invariants_strict_with_slot_capacity_and_freshness_ok
       s.toZonedArch s.toOpCap s.toSlotCap s.toAncillaModel sched
       s.decoder.max_latency_us s.window_us s.max_per_window

/-! §2.f The FTQ-VM backend JSON — so the Python VM runs from the SAME
    definition.  `Codegen/DeviceProgramParse.parseBackend` reads this text
    back into the models above (zone names modulo `vm_id`/`lean_name`). -/

private def jsonBool (b : Bool) : String := if b then "true" else "false"

def ZoneSpecH.toJson (z : ZoneSpecH) : String :=
  s!"    \"{z.vm_id}\": \{\"kind\": \"{z.kind}\", \"count\": {z.count}, \"site_lo\": {z.site_lo}"
  ++ (if z.tracked then
        ", \"reset_required\": true, \"start_dirty\": true, "
        ++ "\"reset_kinds\": [\"request_ancilla\"], \"dirty_kinds\": [\"measure\"], "
        ++ "\"min_reset_us\": 1}"
      else "}")

def GateSpec.toJson (g : GateSpec) : String :=
  s!"    \"{g.name}\": \{\"duration_us\": {g.duration_us}, \"qubits\": {g.qubits}, \"max_parallel\": {g.max_parallel}}"

def TokenSpec.toJson (t : TokenSpec) : String :=
  s!"    \"{t.kind}\": \{\"initial_inventory\": {t.initial_inventory}"
  ++ (if t.ttl_us = 0 then "}" else s!", \"ttl_us\": {t.ttl_us}}")

/-- Render the spec as the shared FTQ-VM backend JSON. -/
def HardwareSpec.toBackendJson (s : HardwareSpec) : String :=
  let zones := String.intercalate ",\n" (s.zones.map ZoneSpecH.toJson)
  let gates := String.intercalate ",\n" (s.gates.map GateSpec.toJson)
  let tokens :=
    if s.tokens.isEmpty then ""
    else "  \"tokens\": {\n"
         ++ String.intercalate ",\n" (s.tokens.map TokenSpec.toJson)
         ++ "\n  },\n"
  let syndrome :=
    match s.syndrome with
    | none => ""
    | some sy =>
        "  \"throughput_caps\": [\n"
        ++ s!"    \{\"id\": \"syndrome_stream\", \"op_kinds\": [\"measure\"], "
        ++ s!"\"weight_per_op\": {sy.bits_per_measure}, \"window_us\": {sy.window_us}, "
        ++ s!"\"max_weight\": {sy.max_bits}, \"unit\": \"bits\"}\n  ],\n"
  "{\n  \"unit\": {\"time\": \"us\"},\n"
  ++ s!"  \"name\": \"{s.name}\",\n"
  ++ "  \"description\": \"GENERATED from FormalRV/System/Params/HardwareCatalog.lean — configure there, not here.\",\n"
  ++ "  \"zones\": {\n" ++ zones ++ "\n  },\n"
  ++ "  \"resources\": {\n"
  ++ s!"    \"decoder_pool\": \{\"kind\": \"service\", \"workers\": {s.decoder.workers}, "
  ++ s!"\"max_latency_us\": {s.decoder.max_latency_us}, \"queue_capacity\": {s.decoder.queue_capacity}, "
  ++ s!"\"processing_time_us\": {s.decoder.processing_time_us}}\n"
  ++ "  },\n"
  ++ tokens
  ++ syndrome
  ++ "  \"gates\": {\n" ++ gates ++ "\n  },\n"
  ++ "  \"x-lean\": {\n"
  ++ s!"    \"t_cycle_us\": {s.t_cycle_us}, \"v_max_um_per_us\": {s.v_max_um_per_us},\n"
  ++ s!"    \"window_us\": {s.window_us}, \"max_per_window\": {s.max_per_window},\n"
  ++ s!"    \"magic_period_us\": {s.magic_period_us}, \"magic_per_period\": {s.magic_per_period},\n"
  ++ s!"    \"max_feedback_active\": {s.max_feedback_active}, \"max_magic_req_active\": {s.max_magic_req_active},\n"
  ++ s!"    \"max_fresh_ancilla_active\": {s.max_fresh_ancilla_active}, \"max_transit_active\": {s.max_transit_active}\n"
  ++ "  }\n}\n"

/-! ## §3. THE CATALOG — every parameter set, in one place

    Each entry is a complete machine description.  Derive new machines
    with record-update syntax (`{ adder_d3 with ... }`). -/

/-- The standard 1-µs gate set used by the surgery/PPM demos:
    CNOT (2q, cap 1 — single-laser hardware), H (1q, cap 4),
    measurement (cap 4 — decoder-bank width), explicit ancilla reset. -/
def standardGates : List GateSpec :=
  [ { name := "CNOT", duration_us := 1, qubits := 2, max_parallel := 1 }
  , { name := "H", duration_us := 1, qubits := 1, max_parallel := 4 }
  , { name := "measure", duration_us := 1, qubits := 1, max_parallel := 4 }
  , { name := "request_ancilla", duration_us := 1, qubits := 1 } ]

/-- **adder_d3 / surgery demo machine** — 4 zones × 100 logical-patch
    sites (each a d=3 surface patch), standard 1-µs gates, a 4-worker
    decoder with a 10 µs reaction budget.  THE spec behind both
    `surgery_arch`/`adder_demo_*` (Lean) and
    `ftq_vm/backend/examples/adder_d3_backend.json` (VM). -/
def adder_d3 : HardwareSpec :=
  { name := "adder_d3_demoArch"
    zones :=
      [ { vm_id := "data",    lean_name := "Data",    kind := "data_qubit",    site_lo := 0,   count := 100 }
      , { vm_id := "anc",     lean_name := "Ancilla", kind := "helper_qubit",  site_lo := 100, count := 100, tracked := true }
      , { vm_id := "factory", lean_name := "Factory", kind := "factory_qubit", site_lo := 200, count := 100 }
      , { vm_id := "routing", lean_name := "Routing", kind := "routing_qubit", site_lo := 300, count := 100 } ]
    gates := standardGates
    decoder := { workers := 4, max_latency_us := 10, queue_capacity := 1000 }
    max_feedback_active := 4 }

/-- Reconfiguration A: dual-rail control — TWO simultaneous CNOTs.
    (§5 proves this flips the parallel-adder verdict.) -/
def adder_d3_dualRail : HardwareSpec :=
  { adder_d3 with
      name := "adder_d3_dualRail"
      gates := [ { name := "CNOT", duration_us := 1, qubits := 2, max_parallel := 2 }
               , { name := "H", duration_us := 1, qubits := 1, max_parallel := 4 }
               , { name := "measure", duration_us := 1, qubits := 1, max_parallel := 4 }
               , { name := "request_ancilla", duration_us := 1, qubits := 1 } ] }

/-- Reconfiguration B: a decoder with NO reaction budget (0 µs) — every
    decode misses.  (§5 proves this flips the good adder verdict.) -/
def adder_d3_zeroReaction : HardwareSpec :=
  { adder_d3 with
      name := "adder_d3_zeroReaction"
      decoder := { workers := 4, max_latency_us := 0, queue_capacity := 1000 } }

/-- Reconfiguration C: a tiny 8-slot decoder queue — syndrome bursts
    overflow it (the differential corpus exercises this). -/
def adder_d3_tinyQueue : HardwareSpec :=
  { adder_d3 with
      name := "adder_d3_tinyQueue"
      decoder := { workers := 4, max_latency_us := 10, queue_capacity := 8 } }

/-- Reconfiguration D: a stocked magic-state inventory (VM tokens) with
    the qianxu demand window (≤ 1 request per 12 000 µs) — used to exhibit
    the I4-window check as a Lean-side discipline the VM's causal token
    model does not duplicate. -/
def adder_d3_magicStock : HardwareSpec :=
  { adder_d3 with
      name := "adder_d3_magicStock"
      tokens := [{ kind := "MagicState", initial_inventory := 10 }]
      window_us := 12000
      max_per_window := 1 }

/-- Reconfiguration D2: a SCARCE magic stock — exactly ONE prepared state
    and no factory production.  A second consumption is causally
    impossible (I6.b; the VM's token ledger rejects it identically:
    `MAGIC_SUPPLY`). -/
def adder_d3_magicScarce : HardwareSpec :=
  { adder_d3 with
      name := "adder_d3_magicScarce"
      tokens := [{ kind := "MagicState", initial_inventory := 1 }] }

/-- Reconfiguration E: decode-result tokens that EXPIRE after 5 µs — the
    VM's token freshness (ttl) catches stale feedforward that Lean's
    order-only `feedback_after_decode_ok` accepts. -/
def adder_d3_staleDecode : HardwareSpec :=
  { adder_d3 with
      name := "adder_d3_staleDecode"
      tokens := [ { kind := "decode0", ttl_us := 5 }
                , { kind := "decode1", ttl_us := 5 }
                , { kind := "decode2", ttl_us := 5 } ] }

/-- Reconfiguration F: a STRICT decoder service — 2 workers, each
    occupied for the full decode latency (the schedules use 1 ms decodes)
    and freed only when it finishes; NO queue (`queue_capacity = 0`), so
    over-subscription is an error rather than a wait.  This makes the
    VM's FIFO service semantically identical to the Lean concurrency
    model (`active decodes ≤ workers` at every instant): both report
    `DECODER_OVERLOAD` on the same schedules.  The 2 ms reaction budget
    leaves headroom so the overload is the ONLY violation. -/
def adder_d3_strictDecoder : HardwareSpec :=
  { adder_d3 with
      name := "adder_d3_strictDecoder"
      decoder := { workers := 2, max_latency_us := 2000, queue_capacity := 0 } }

/-! ### §3.b THE GIDNEY–EKERÅ 2021 MACHINE (arXiv 1905.09749)

    "How to factor 2048 bit RSA integers in 8 hours using 20 million
    noisy qubits."  Every number below is a reference to the canonical
    constants in `Params/RSA2048.lean` (single-source rule) — d = 27
    patches, 1 µs code cycle, 10 µs reaction budget, 6200 logical
    patches, 62 000 decode lanes, 1093 CCZ factories at one state per
    12 000 µs each, 20 M physical qubits.

    TWO granularities, deliberately:

    * `ge2021_physical` — the PHYSICAL-qubit architecture (20 M sites,
      Computation + Factory zones).  Its `toZonedArch` is rfl-pinned to
      the audit's `ge2021Arch` (`Audit/GidneyEkera2021/SystemZones`).
      Lean-side audits only — never emitted to the VM (a 20 M-resource
      expansion is not a backend file).

    * `ge2021_logical` — the PATCH-granular machine the QEC-level
      compilation lands on (one site = one d = 27 patch / factory
      port): 6200 data patches, 6200 routing/bus patches (the ×2
      routing share of the 1568-qubit tile, made explicit and
      freshness-tracked), 1093 factory output ports.  VM-emittable
      (13 493 sites).  Logical ops are 1 µs (= one code cycle); a merge
      is `tau_s = 27` rounds, carried by the gadget, not the gate
      table. -/

/-- The physical-budget architecture (Lean-side audits). -/
def ge2021_physical : HardwareSpec :=
  { name := "ge2021_physical"
    zones :=
      [ { vm_id := "comp", lean_name := "Computation", kind := "data_qubit"
          site_lo := 0, count := FormalRV.System.RSA2048.computationZoneQubits }
      , { vm_id := "factory", lean_name := "Factory", kind := "factory_qubit"
          site_lo := FormalRV.System.RSA2048.computationZoneQubits
          count := FormalRV.System.RSA2048.physicalBudget
                     - FormalRV.System.RSA2048.computationZoneQubits } ]
    gates := standardGates
    decoder := { workers := FormalRV.System.RSA2048.decodeLanesRequired
                 max_latency_us := FormalRV.System.RSA2048.reactionUs }
    t_cycle_us := FormalRV.System.RSA2048.cycleUs
    v_max_um_per_us := 1
    window_us := FormalRV.System.RSA2048.cczWindowUs
    max_per_window := FormalRV.System.RSA2048.factoriesNeeded }

/-- The patch-granular GE2021 machine (the QEC→system lane's target). -/
def ge2021_logical : HardwareSpec :=
  { name := "ge2021_logical"
    zones :=
      [ { vm_id := "data", lean_name := "Data", kind := "data_qubit"
          site_lo := 0, count := FormalRV.System.RSA2048.patches }
      , { vm_id := "bus", lean_name := "Routing", kind := "helper_qubit"
          site_lo := FormalRV.System.RSA2048.patches
          count := FormalRV.System.RSA2048.patches, tracked := true }
      , { vm_id := "factory", lean_name := "FactoryPorts"
          kind := "factory_qubit"
          site_lo := 2 * FormalRV.System.RSA2048.patches
          count := FormalRV.System.RSA2048.factoriesNeeded } ]
    gates :=
      [ { name := "CNOT", duration_us := 1, qubits := 2
          max_parallel := FormalRV.System.RSA2048.patches }
      , { name := "H", duration_us := 1, qubits := 1
          max_parallel := FormalRV.System.RSA2048.patches }
      , { name := "measure", duration_us := 1, qubits := 1
          max_parallel := FormalRV.System.RSA2048.patches }
      , { name := "request_ancilla", duration_us := 1, qubits := 1 } ]
    decoder := { workers := FormalRV.System.RSA2048.decodeLanesRequired
                 max_latency_us := FormalRV.System.RSA2048.reactionUs
                 queue_capacity := FormalRV.System.RSA2048.decodeLanesRequired }
    -- a small steady-state output buffer of prepared CCZ states, plus
    -- the 1093-factory production curve (I6.b prepare-before-consume)
    tokens := [{ kind := "MagicState", initial_inventory := 2 }]
    magic_period_us := FormalRV.System.RSA2048.cczWindowUs
    magic_per_period := FormalRV.System.RSA2048.factoriesNeeded
    -- the syndrome link must sustain ALL patches each cycle:
    -- 6200 patches × 728 bits (d²−1 at d = 27) per µs
    syndrome := some
      { bits_per_measure := FormalRV.System.RSA2048.syndromeBitsPerPatchRound
        window_us := 1000
        max_bits := 1000 * FormalRV.System.RSA2048.patches
                      * FormalRV.System.RSA2048.syndromeBitsPerPatchRound }
    t_cycle_us := FormalRV.System.RSA2048.cycleUs
    v_max_um_per_us := 1
    window_us := FormalRV.System.RSA2048.cczWindowUs
    max_per_window := FormalRV.System.RSA2048.factoriesNeeded
    max_feedback_active := FormalRV.System.RSA2048.patches
    max_fresh_ancilla_active := FormalRV.System.RSA2048.patches
    max_magic_req_active := FormalRV.System.RSA2048.factoriesNeeded }

/-- The patch-granular layout's implied PHYSICAL cost fits the paper's
    20 M budget: 6200 tiles × 1568 + 1093 factories × 2565 ≤ 20 000 000
    (the residual is distillation/routing headroom). -/
theorem ge2021_logical_fits_physical_budget :
    FormalRV.System.RSA2048.computationZoneQubits
      + FormalRV.System.RSA2048.factoriesNeeded
          * FormalRV.System.RSA2048.cczFactoryQubits
      ≤ FormalRV.System.RSA2048.physicalBudget := by decide

theorem ge2021_wellFormed :
    (ge2021_physical.wellFormed && ge2021_logical.wellFormed) = true := by
  native_decide

/-- **Surface-code syndrome-streaming machine**: a 4×4 tile of d=3 surface
    patches.  Each patch is read out once per round as ONE `Measure` op on
    its `syn` site, contributing 8 stabilizers × 8-bit soft data = 64 bits
    to the syndrome stream; the classical link carries **4 KB/ms**
    (`max_bits = 32768` per 1000 µs).  Budget arithmetic: a round costs
    16 × 64 = 1024 bits, so the link sustains at most
    ⌊32768 / 1024⌋ = 32 rounds per ms — a 25 µs cadence (40 rounds/ms =
    40960 bits/ms) BREAKS the link; a 40 µs cadence (25 rounds/ms =
    25600 bits/ms) fits. -/
def surface_d3_stream : HardwareSpec :=
  { name := "surface_d3_stream"
    zones :=
      [ { vm_id := "data", lean_name := "Data",     kind := "data_qubit",     site_lo := 0,  count := 16 }
      , { vm_id := "syn",  lean_name := "Syndrome", kind := "syndrome_qubit", site_lo := 16, count := 16 } ]
    gates :=
      [ { name := "CNOT", duration_us := 1, qubits := 2, max_parallel := 4 }
      , { name := "H", duration_us := 1, qubits := 1, max_parallel := 4 }
      , { name := "measure", duration_us := 1, qubits := 1, max_parallel := 32 }
      , { name := "request_ancilla", duration_us := 1, qubits := 1 } ]
    decoder := { workers := 4, max_latency_us := 10, queue_capacity := 1000 }
    syndrome := some { bits_per_measure := 64, window_us := 1000,
                       max_bits := 32768 } }

/-- **Invariant-examples machine** (`SystemInvariantExamples.demoArch`):
    Data/Ancilla/Factory × 100, 1 µs cycle, 10 µs reaction, and the qianxu
    CCZ-factory demand window (≤ 1 magic state per 12 000 µs). -/
def invariant_demo : HardwareSpec :=
  { name := "invariant_demo"
    zones :=
      [ { vm_id := "data",    lean_name := "Data",    kind := "data_qubit",    site_lo := 0,   count := 100 }
      , { vm_id := "anc",     lean_name := "Ancilla", kind := "helper_qubit",  site_lo := 100, count := 100, tracked := true }
      , { vm_id := "factory", lean_name := "Factory", kind := "factory_qubit", site_lo := 200, count := 100 } ]
    gates := standardGates
    decoder := { workers := 4, max_latency_us := 10 }
    window_us := 12000
    max_per_window := 1 }

/-- **PPM-pair machine** (`PPMContractInstances.ppm_pair_arch`):
    Data/Ancilla × 100. -/
def ppm_pair : HardwareSpec :=
  { name := "ppm_pair"
    zones :=
      [ { vm_id := "data", lean_name := "Data",    kind := "data_qubit",   site_lo := 0,   count := 100 }
      , { vm_id := "anc",  lean_name := "Ancilla", kind := "helper_qubit", site_lo := 100, count := 100, tracked := true } ]
    gates := standardGates
    decoder := { workers := 4, max_latency_us := 10 } }

/-- **Fault-tolerant worked-instance machine** — the arch that
    `Checkers/FaultTolerantSchedule.demoArch` AND its acknowledged mirror
    `Invariants/InvariantFramework.demoArch` both define: 4 zones × 10
    sites, 100 µs stabilizer cycle, 5 µm/µs transport limit.  §6 pins both
    mirrors to this single entry. -/
def ftDemo : HardwareSpec :=
  { name := "ftDemo"
    zones :=
      [ { vm_id := "data",      lean_name := "Data",      kind := "data_qubit",    site_lo := 0,  count := 10 }
      , { vm_id := "workspace", lean_name := "Workspace", kind := "helper_qubit",  site_lo := 10, count := 10 }
      , { vm_id := "factory",   lean_name := "Factory",   kind := "factory_qubit", site_lo := 20, count := 10 }
      , { vm_id := "routing",   lean_name := "Routing",   kind := "routing_qubit", site_lo := 30, count := 10 } ]
    gates := standardGates
    decoder := { workers := 4, max_latency_us := 10 }
    t_cycle_us := 100
    v_max_um_per_us := 5 }

/-! ## §4. Re-exports: the legacy / platform parameter records

    Other hardware records predate `HardwareSpec` and serve different
    lanes; they are catalogued here as the canonical reference points
    (`Params/HardwareParams.MachineParams` reconciles their shared
    fields):

    * **Platform instances** (`Core/Architecture.lean`, cited values):
      `neutral_atom_mini`, `trapped_ion_mini`, `superconducting_mini` —
      `Architecture` records (zones + channels + cycle/reaction/coherence).
    * **Magic-state factories** (`Core/Architecture.lean`):
      `ccz_spec_qianxu` (2565 qubits, 12 000 µs, 80 %),
      `t_spec_qianxu` (73 qubits, 5 000 µs, 80 %).
    * **GE2021 device lane** (`Params/HardwareParams.ge2021Device`,
      `Bounds/HardwareSensitivity.HW.ge2021` / `.gidney2025`): the 20 M-qubit
      / 10 µs-reaction / d = 27 records used by the bounds and audits.
    * **Zone budgets** (`Params/ZoneBudget.toArch`): derive a `ZonedArch`
      from qubit-count budgets.
    * **Workload constants** (`Params/RSA2048`): `toffoliReported`,
      `magicBudget`, `patches`, `decodeLanesRequired`, `cczFactoryQubits`,
      `cczWindowUs`, `factoriesNeeded`. -/

export FormalRV.System.RSA2048 (toffoliReported magicBudget patches
  decodeLanesRequired cczFactoryQubits cczWindowUs factoriesNeeded)

/-! ## §5. Reconfigurability — parameters are LIVE

    The same schedules, checked under different catalog entries, get
    different verdicts: the toolchain is demonstrably not tied to one
    parameter set.  (`bad_parallel_adder_syscalls` runs two surgery blocks
    simultaneously; `surgery_ppm_A` is one sequential block.) -/

open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.AdderSystem

/-- The sequential surgery block PASSES on the standard machine. -/
theorem block_ok_on_adder_d3 :
    checkScheduleOn adder_d3 (compileSurgeryGadgetToSysCalls surgery_ppm_A)
      = true := by native_decide

/-- The SAME block FAILS on the zero-reaction machine — the decoder
    budget is live. -/
theorem block_fails_on_zeroReaction :
    checkScheduleOn adder_d3_zeroReaction
      (compileSurgeryGadgetToSysCalls surgery_ppm_A) = false := by native_decide

/-- The parallel adder FAILS on the standard machine (CNOT cap 1)… -/
theorem parallel_fails_on_adder_d3 :
    checkScheduleOn adder_d3 bad_parallel_adder_syscalls = false := by
  native_decide

/-- …and the SAME schedule PASSES on the dual-rail machine (CNOT cap 2) —
    the control-parallelism cap is live.  Reconfiguring the catalog entry
    changes which schedules are feasible, with no checker changes. -/
theorem parallel_ok_on_dualRail :
    checkScheduleOn adder_d3_dualRail bad_parallel_adder_syscalls = true := by
  native_decide

/-- A burst of patch readouts at the given cadence: one `Measure` per
    `syn` site (16..31) per round, `rounds` rounds spaced `cadence` µs. -/
def syndromeBurst (rounds cadence : Nat) : List SysCall :=
  (List.range rounds).flatMap fun r =>
    (List.range 16).map fun p =>
      { kind := SysCallKind.Measure (16 + p) 0
        begin_us := r * cadence, end_us := r * cadence + 1 }

/-- The syndrome BIT accounting is live: 40 rounds × 16 patches × 64 bits
    = 40960 bits inside one 1000 µs window EXCEEDS the 4 KB/ms link… -/
theorem syndrome_flood_rejected :
    checkScheduleOn surface_d3_stream (syndromeBurst 40 25) = false := by
  native_decide

/-- …while 25 rounds/ms × 1024 bits = 25600 ≤ 32768 fits the same link —
    and the very same flood is fine on a machine with no link contract. -/
theorem syndrome_paced_accepted :
    checkScheduleOn surface_d3_stream (syndromeBurst 25 40) = true := by
  native_decide

theorem syndrome_flood_ok_without_link_contract :
    checkScheduleOn { surface_d3_stream with syndrome := none }
      (syndromeBurst 40 25) = true := by
  native_decide

/-- `n` decode calls of 1 ms each, at the given times (offset past a
    prefix of n sequential 1 µs measurements on data sites — each decode
    is causally fed, so I6.a is satisfied and the theorems below isolate
    decoder OCCUPANCY). -/
def decodesAt (times : List Nat) : List SysCall :=
  ((List.range times.length).map fun k =>
    ({ kind := SysCallKind.Measure k 0
       begin_us := k, end_us := k + 1 } : SysCall))
  ++ ((times.zipIdx).map fun (t, r) =>
    { kind := SysCallKind.DecodeSyndrome r
      begin_us := times.length + t, end_us := times.length + t + 1000 })

/-- Decoder-occupancy semantics, positive: 6 one-millisecond decodes
    through 2 workers succeed ONLY because each worker is freed when its
    decode finishes (exactly 1000 µs after it began, half-open) and
    immediately reused. -/
theorem decoder_paced_reuse_accepted :
    checkScheduleOn adder_d3_strictDecoder
      (decodesAt [0, 0, 1000, 1000, 2000, 2000]) = true := by native_decide

/-- …negative: reusing a worker 1 µs BEFORE its decode finishes makes 3
    decodes simultaneously active on 2 workers — rejected.  The decoder
    is finite and its latency is real. -/
theorem decoder_premature_reuse_rejected :
    checkScheduleOn adder_d3_strictDecoder
      (decodesAt [0, 0, 999]) = false := by native_decide

/-! ### §5.b I6 CAUSALITY is live (pure space-time ordering)

    Syndrome data must EXIST before it is shipped to the decoder, and a
    magic state must be PREPARED before it is consumed. -/

/-- Measure [2,3) then decode [3,4): causal — ACCEPTED. -/
theorem decode_after_measure_accepted :
    checkScheduleOn adder_d3
      [ { kind := SysCallKind.Measure 0 0, begin_us := 2, end_us := 3 }
      , { kind := SysCallKind.DecodeSyndrome 0, begin_us := 3, end_us := 4 } ]
      = true := by native_decide

/-- The decoder called at t = 2 while the measurement still runs until
    t = 3 — the syndrome data does not exist yet: REJECTED, even though
    every resource is free. -/
theorem decode_before_measure_rejected :
    checkScheduleOn adder_d3
      [ { kind := SysCallKind.Measure 0 0, begin_us := 2, end_us := 3 }
      , { kind := SysCallKind.DecodeSyndrome 0, begin_us := 2, end_us := 3 } ]
      = false := by native_decide

/-- TWO magic consumptions against ONE prepared state: the second is
    causally impossible — REJECTED on the scarce machine… -/
theorem second_magic_unprepared_rejected :
    checkScheduleOn adder_d3_magicScarce
      [ { kind := SysCallKind.RequestMagicState 0, begin_us := 0, end_us := 1 }
      , { kind := SysCallKind.RequestMagicState 1, begin_us := 5, end_us := 6 } ]
      = false := by native_decide

/-- …but ACCEPTED once a factory PREPARES one more state every 12 000 µs
    and the second consumption waits for the batch to finish (t = 12 000):
    prepare-before-consume, on the production curve. -/
theorem second_magic_after_production_accepted :
    checkScheduleOn
      { adder_d3_magicScarce with
          magic_period_us := 12000, magic_per_period := 1
          window_us := 1000, max_per_window := 1 }
      [ { kind := SysCallKind.RequestMagicState 0, begin_us := 0, end_us := 1 }
      , { kind := SysCallKind.RequestMagicState 1, begin_us := 12000,
          end_us := 12001 } ]
      = true := by native_decide

/-- …and the same second consumption ONE µs before the batch finishes is
    rejected: preparation must COMPLETE first. -/
theorem second_magic_during_production_rejected :
    checkScheduleOn
      { adder_d3_magicScarce with
          magic_period_us := 12000, magic_per_period := 1
          window_us := 1000, max_per_window := 1 }
      [ { kind := SysCallKind.RequestMagicState 0, begin_us := 0, end_us := 1 }
      , { kind := SysCallKind.RequestMagicState 1, begin_us := 11999,
          end_us := 12000 } ]
      = false := by native_decide

/-! ## §6. The catalog is canonical — legacy definitions pinned

    The scattered demo records equal their catalog derivations
    definitionally, so configuring HERE configures everything. -/

theorem adder_d3_arch_eq : adder_d3.toZonedArch = surgery_arch := rfl
theorem adder_d3_opCap_eq : adder_d3.toOpCap = adder_demo_opCap := rfl
theorem adder_d3_slotCap_eq :
    adder_d3.toSlotCap = generous_slot_capacity_model := rfl
theorem adder_d3_ancilla_eq :
    adder_d3.toAncillaModel = demo_ancilla_model := rfl

theorem invariant_demo_arch_eq :
    invariant_demo.toZonedArch
      = FormalRV.System.SystemInvariantExamples.demoArch := rfl

theorem ppm_pair_arch_eq :
    ppm_pair.toZonedArch
      = FormalRV.System.LatticeSurgeryPPMContract.ppm_pair_arch := rfl

/-- The two mirrored worked-instance archs are BOTH this catalog entry —
    the duplication is now formally pinned to one source. -/
theorem ftDemo_arch_eq_checker :
    ftDemo.toZonedArch = FormalRV.System.FTSchedule.demoArch := rfl
theorem ftDemo_arch_eq_framework :
    ftDemo.toZonedArch = FormalRV.System.InvariantFramework.demoArch := rfl

/-- Catalog entries are well-formed configurations. -/
theorem catalog_wellFormed :
    (adder_d3.wellFormed && adder_d3_dualRail.wellFormed
      && adder_d3_zeroReaction.wellFormed && invariant_demo.wellFormed
      && ppm_pair.wellFormed && ftDemo.wellFormed) = true := by native_decide

end FormalRV.System.HardwareCatalog
