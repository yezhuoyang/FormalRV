/-
  FormalRV.System.Compile.QECScheduleToSystem — **W2: the QEC→System driver.**

  The pipeline is

      Shor @ PPM  ──W1──►  QEC layer  ──W2──►  System layer
                           (`Schedule = List SurgeryGadget`:
                            merges / CCZ injection, SEMANTICS)

  This module is W2: an EXECUTABLE whole-program compiler from a QEC-layer
  surgery program to the system-level `List SysCall` that the decidable
  invariant bundle (`HardwareCatalog.checkScheduleOn`) and the FTQ-VM check.
  It replaces the removed legacy artifacts (hand-written `shorSched`,
  replicate-one-gadget `shorSchedule`): every SysCall here is DERIVED from
  the QEC gadgets' connection matrices, never typed in.

  Design points (each fixing an audited gap):

  * **Whole programs, not single gadgets** — `compileQECProgram` drives a
    `List QECEvent` with a running clock and a running decoder-round
    counter; gadgets are HETEROGENEOUS (any mix of merges and magic
    injections).
  * **Globally unique decode ids** — round ids are strictly consecutive
    across the whole program (`decodeIds_eq_range'`), so every
    `PauliFrameUpdate` matches EXACTLY ONE `DecodeSyndrome` (no
    stale-syndrome aliasing; the Lean existential check and the FTQ-VM
    token FIFO agree by construction).
  * **Explicit-qubit discipline** — every ancilla site a round touches is
    explicitly requested (`RequestFreshAncilla site`) and re-requested
    after its dirtying measurement, satisfying `ancilla_freshness_ok`.
  * **Magic binding** — a `teleportCCX` injection is one
    `RequestMagicState` followed by its three merge gadgets
    (`QECEvent.cczInjection`, anchored to the QEC layer's
    `cczInjectionSchedule`).
  * **Resource counting by recursion** — `programSyscallCount` /
    `programRounds` give closed counts proven equal to the compiled
    output's, the seed of symbolic resource upper bounds at this layer.
-/
import FormalRV.System.Compile.SurgeryGadgetToSysCalls
import FormalRV.QEC.LatticeSurgery.MagicInjectionSurgery
import FormalRV.System.Params.HardwareCatalog
import FormalRV.Resource.SysCallCount

namespace FormalRV.System.QECScheduleToSystem

open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.Framework.LDPC
open FormalRV.System.SurgeryGadgetToSysCalls (SiteId connEdges)

/-! ## §1. The W2 input: QEC events

    A QEC-layer program for the system compiler: plain surgery merges
    (the QEC `Schedule = List SurgeryGadget` embeds via `ofSchedule`)
    plus magic-consuming injections (which bind a factory id — the one
    piece of system information the QEC semantic layer does not carry). -/

inductive QECEvent where
  /-- one lattice-surgery merge (a logical Pauli-product measurement) -/
  | surgery (g : SurgeryGadget) : QECEvent
  /-- a magic-state injection: consume one magic state from `factory`,
      then run the injection's merge gadgets -/
  | magicSurgery (factory : Nat) (injection : List SurgeryGadget) : QECEvent

abbrev QECProgram := List QECEvent

/-- Embed a plain QEC `Schedule` (no magic). -/
def ofSchedule (s : List SurgeryGadget) : QECProgram := s.map .surgery

/-- A `teleportCCX` injection event, anchored to the QEC layer's
    `cczInjectionSchedule` (3 merges + exactly 1 magic state). -/
def QECEvent.cczInjection (factory : Nat) (mA mB mC : SurgeryGadget) : QECEvent :=
  .magicSurgery factory
    (FormalRV.LatticeSurgery.MagicInjectionSurgery.cczInjectionSchedule mA mB mC)

/-- Every gadget must run ≥ 1 syndrome round (a 0-round gadget would emit
    a frame update with no decode to match). -/
def QECEvent.wf : QECEvent → Bool
  | .surgery g          => decide (1 ≤ g.tau_s)
  | .magicSurgery _ gs  => gs.all (fun g => decide (1 ≤ g.tau_s))

def programWf (p : QECProgram) : Bool := p.all QECEvent.wf

/-! ## §2. Layout

    The system-side placement: data-qubit index → site, ancilla-qubit
    index → site.  (Patch placement / routing policy lives here; the
    compiler itself is layout-generic.) -/

structure SurgeryLayout where
  dataSite    : Nat → SiteId
  ancillaSite : Nat → SiteId

/-! ## §3. Per-round and per-gadget emission

    One round of gadget `g` at base time `t0` with decode id `rid`
    (all SEQUENTIAL, 1 µs per op — safe under every per-kind cap):

      [t0+k, t0+k+1)        RequestFreshAncilla (ancillaSite k),  k < a
      [t0+a+i, ..+1)        Gate2q per X-edge (dataSite j, ancillaSite i)
      [t0+a+|ex|+i, ..+1)   Gate2q per Z-edge (dataSite i, ancillaSite j)
      [t0+a+G+k, ..+1)      Measure (ancillaSite k),              k < a
      [t0+2a+G, ..+1)       DecodeSyndrome rid

    Round length = `2a + G + 1`.  Unlike the per-gadget §9 compiler, EVERY
    touched ancilla site is requested each round (explicit-qubit rule), so
    the stream passes `ancilla_freshness_ok` on a tracked ancilla zone. -/

/-- Gate2q count of one round (true entries of both connection matrices). -/
def gateCount (g : SurgeryGadget) : Nat :=
  (connEdges g.conn_x).length + (connEdges g.conn_z).length

/-- SysCalls per round: `a` requests + `G` gates + `a` measures + 1 decode. -/
def roundLen (g : SurgeryGadget) : Nat := 2 * g.ancilla_n + gateCount g + 1

/-- SysCalls per gadget: `tau_s` rounds + the final frame update. -/
def gadgetLen (g : SurgeryGadget) : Nat := roundLen g * g.tau_s + 1

def emitRound (L : SurgeryLayout) (g : SurgeryGadget)
    (t0 rid : Nat) : List SysCall :=
  let a  := g.ancilla_n
  let ex := connEdges g.conn_x
  let ez := connEdges g.conn_z
  let reqs := (List.range a).map fun k =>
    { kind := SysCallKind.RequestFreshAncilla (L.ancillaSite k)
      begin_us := t0 + k, end_us := t0 + k + 1 : SysCall }
  let gx := ex.mapIdx fun idx ij =>
    { kind := SysCallKind.Gate2q (L.dataSite ij.2) (L.ancillaSite ij.1) 0
      begin_us := t0 + a + idx, end_us := t0 + a + idx + 1 : SysCall }
  let gz := ez.mapIdx fun idx ij =>
    { kind := SysCallKind.Gate2q (L.dataSite ij.1) (L.ancillaSite ij.2) 0
      begin_us := t0 + a + ex.length + idx
      end_us   := t0 + a + ex.length + idx + 1 : SysCall }
  let meas := (List.range a).map fun k =>
    { kind := SysCallKind.Measure (L.ancillaSite k) 0
      begin_us := t0 + a + gateCount g + k
      end_us   := t0 + a + gateCount g + k + 1 : SysCall }
  let dec :=
    { kind := SysCallKind.DecodeSyndrome rid
      begin_us := t0 + 2 * a + gateCount g
      end_us   := t0 + 2 * a + gateCount g + 1 : SysCall }
  reqs ++ gx ++ gz ++ meas ++ [dec]

/-- Compile one gadget at start time `t`, decoder base `base`: `tau_s`
    rounds with CONSECUTIVE decode ids, then one frame update keyed to
    the gadget's base round. -/
def emitGadget (L : SurgeryLayout) (g : SurgeryGadget)
    (t base : Nat) : List SysCall :=
  (List.range g.tau_s).flatMap
    (fun r => emitRound L g (t + roundLen g * r) (base + r))
  ++ [ { kind := SysCallKind.PauliFrameUpdate base
         begin_us := t + roundLen g * g.tau_s
         end_us   := t + roundLen g * g.tau_s + 1 } ]

/-! ## §4. The whole-program driver -/

/-- Compile a gadget list sequentially, threading (clock, next round id). -/
def compileGadgets (L : SurgeryLayout) :
    List SurgeryGadget → Nat → Nat → List SysCall
  | [],      _, _    => []
  | g :: gs, t, base =>
      emitGadget L g t base
      ++ compileGadgets L gs (t + gadgetLen g) (base + g.tau_s)

/-- Rounds consumed by a gadget list. -/
def gadgetsRounds (gs : List SurgeryGadget) : Nat :=
  (gs.map (·.tau_s)).sum

/-- Duration (µs) of a compiled gadget list. -/
def gadgetsDuration (gs : List SurgeryGadget) : Nat :=
  (gs.map gadgetLen).sum

def eventRounds : QECEvent → Nat
  | .surgery g         => g.tau_s
  | .magicSurgery _ gs => gadgetsRounds gs

def eventDuration : QECEvent → Nat
  | .surgery g         => gadgetLen g
  | .magicSurgery _ gs => 1 + gadgetsDuration gs

def eventSyscallCount : QECEvent → Nat
  | .surgery g         => gadgetLen g
  | .magicSurgery _ gs => 1 + (gs.map gadgetLen).sum

/-- Compile one event at (t, base). -/
def compileEvent (L : SurgeryLayout) (t base : Nat) : QECEvent → List SysCall
  | .surgery g => emitGadget L g t base
  | .magicSurgery factory gs =>
      { kind := SysCallKind.RequestMagicState factory
        begin_us := t, end_us := t + 1 }
      :: compileGadgets L gs (t + 1) base

/-- **The W2 driver**: compile a heterogeneous QEC program to one
    system-level SysCall schedule, threading the clock and the global
    decoder-round counter. -/
def compileEvents (L : SurgeryLayout) :
    QECProgram → Nat → Nat → List SysCall
  | [],      _, _    => []
  | e :: es, t, base =>
      compileEvent L t base e
      ++ compileEvents L es (t + eventDuration e) (base + eventRounds e)

def compileQECProgram (L : SurgeryLayout) (p : QECProgram)
    (t0 : Nat := 0) (round0 : Nat := 0) : List SysCall :=
  compileEvents L p t0 round0

/-- Closed-form SysCall count of a compiled program (recursive — no
    expansion needed to know the size). -/
def programSyscallCount (p : QECProgram) : Nat :=
  (p.map eventSyscallCount).sum

/-- Closed-form total round count. -/
def programRounds (p : QECProgram) : Nat :=
  (p.map eventRounds).sum

/-! ## §5. Framework checks: decode-id uniqueness

    The audited aliasing gap: a schedule whose decode round ids repeat
    makes `feedback_after_decode_ok` satisfiable by STALE syndromes and
    diverges from the FTQ-VM token FIFO.  The compiled stream gets
    consecutive ids by construction; `decode_ids_unique_ok` is the
    reusable Bool check any schedule can be audited against. -/

/- `decodeIds` / `pfuCorrs` are THE canonical counters
   (`Resource/SysCallCount`) — single-source rule. -/
open FormalRV.Resource.SysCallCount (decodeIds pfuCorrs decodeIds_append
                                     pfuCorrs_append)

/-- Every decode id is distinct AND every frame update has a matching
    decode — together with the bundle's `feedback_after_decode_ok` this
    upgrades "some same-id decode ended earlier" to "EXACTLY ONE matching
    decode exists" (no stale-syndrome aliasing).  Built ON the canonical
    counters (a verifier USING the counting system, never redefining it). -/
def decode_ids_unique_ok (sched : List SysCall) : Bool :=
  let ids := decodeIds sched
  ids.Nodup && (pfuCorrs sched).all (fun c => ids.contains c)

/-- `range'` glue (step 1), proven directly to avoid step-argument
    normalization games. -/
private theorem range'_append_one (s m n : Nat) :
    List.range' s m ++ List.range' (s + m) n = List.range' s (m + n) := by
  induction m generalizing s with
  | zero => simp
  | succ k ih =>
      rw [List.range'_succ, List.cons_append,
          show s + (k + 1) = (s + 1) + k from by omega, ih,
          ← List.range'_succ]
      congr 1
      omega

/-- One round contributes exactly its decode id. -/
theorem decodeIds_emitRound (L : SurgeryLayout) (g : SurgeryGadget)
    (t0 rid : Nat) : decodeIds (emitRound L g t0 rid) = [rid] := by
  have hnil : ∀ (l : List SysCall),
      (∀ sc ∈ l, decodeIds [sc] = []) → decodeIds l = [] := by
    intro l h
    induction l with
    | nil => rfl
    | cons x xs ih =>
        have hx := h x (by simp)
        have hsplit : decodeIds (x :: xs) = decodeIds [x] ++ decodeIds xs := by
          simpa using decodeIds_append [x] xs
        rw [hsplit, hx, ih (fun sc hsc => h sc (by simp [hsc]))]
        rfl
  rw [emitRound, decodeIds_append, decodeIds_append, decodeIds_append,
      decodeIds_append]
  rw [hnil _ (by intro sc h; simp [List.mem_map] at h
                 obtain ⟨k, _, rfl⟩ := h; rfl),
      hnil _ (by intro sc h; rw [List.mem_mapIdx] at h
                 obtain ⟨i, _, rfl⟩ := h; rfl),
      hnil _ (by intro sc h; rw [List.mem_mapIdx] at h
                 obtain ⟨i, _, rfl⟩ := h; rfl),
      hnil _ (by intro sc h; simp [List.mem_map] at h
                 obtain ⟨k, _, rfl⟩ := h; rfl)]
  rfl

/-- A gadget's decode ids are the consecutive block `[base, base+tau_s)`. -/
theorem decodeIds_emitGadget (L : SurgeryLayout) (g : SurgeryGadget)
    (t base : Nat) :
    decodeIds (emitGadget L g t base) = List.range' base g.tau_s := by
  rw [emitGadget, decodeIds_append]
  have hpfu : decodeIds
      [{ kind := SysCallKind.PauliFrameUpdate base
         begin_us := t + roundLen g * g.tau_s
         end_us := t + roundLen g * g.tau_s + 1 }] = [] := rfl
  rw [hpfu, List.append_nil]
  induction g.tau_s with
  | zero => rfl
  | succ m ih =>
      rw [List.range_succ, List.flatMap_append, decodeIds_append, ih]
      simp [decodeIds_emitRound, List.range'_concat]

/-- **Compiled programs have globally consecutive decode ids** —
    `decodeIds (compileEvents L p t base) = [base, base + programRounds p)`.
    Uniqueness (`Nodup`) is immediate from `List.nodup_range'`. -/
theorem decodeIds_compileGadgets (L : SurgeryLayout) :
    ∀ (gs : List SurgeryGadget) (t base : Nat),
      decodeIds (compileGadgets L gs t base)
        = List.range' base (gadgetsRounds gs)
  | [], _, _ => by simp [compileGadgets, decodeIds, gadgetsRounds]
  | g :: gs, t, base => by
      rw [compileGadgets, decodeIds_append, decodeIds_emitGadget,
          decodeIds_compileGadgets L gs _ _]
      have hsum : gadgetsRounds (g :: gs) = g.tau_s + gadgetsRounds gs := by
        simp [gadgetsRounds]
      rw [hsum, range'_append_one]

theorem decodeIds_compileEvent (L : SurgeryLayout) (t base : Nat)
    (e : QECEvent) :
    decodeIds (compileEvent L t base e) = List.range' base (eventRounds e) := by
  cases e with
  | surgery g => simpa [compileEvent, eventRounds] using
      decodeIds_emitGadget L g t base
  | magicSurgery f gs =>
      have hcons : decodeIds (compileEvent L t base (.magicSurgery f gs))
          = decodeIds (compileGadgets L gs (t + 1) base) := rfl
      rw [hcons, decodeIds_compileGadgets]
      rfl

theorem decodeIds_compileEvents (L : SurgeryLayout) :
    ∀ (p : QECProgram) (t base : Nat),
      decodeIds (compileEvents L p t base)
        = List.range' base (programRounds p)
  | [], _, _ => by simp [compileEvents, decodeIds, programRounds]
  | e :: es, t, base => by
      rw [compileEvents, decodeIds_append, decodeIds_compileEvent,
          decodeIds_compileEvents L es _ _]
      have hsum : programRounds (e :: es) = eventRounds e + programRounds es := by
        simp [programRounds]
      rw [hsum, range'_append_one]

/-- **The aliasing gap is closed for compiled programs** (parametric, any
    layout, any program): all decode ids are distinct. -/
theorem compileQECProgram_decodeIds_nodup
    (L : SurgeryLayout) (p : QECProgram) (t0 round0 : Nat) :
    (decodeIds (compileQECProgram L p t0 round0)).Nodup := by
  rw [compileQECProgram, decodeIds_compileEvents]
  exact List.nodup_range'

/-! ## §6. Resource counting by recursion (count = expansion) -/

theorem emitRound_length (L : SurgeryLayout) (g : SurgeryGadget)
    (t0 rid : Nat) : (emitRound L g t0 rid).length = roundLen g := by
  simp [emitRound, roundLen, gateCount]
  omega

theorem emitGadget_length (L : SurgeryLayout) (g : SurgeryGadget)
    (t base : Nat) : (emitGadget L g t base).length = gadgetLen g := by
  have h : ∀ n, ((List.range n).flatMap
      (fun r => emitRound L g (t + roundLen g * r) (base + r))).length
        = roundLen g * n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih]
        simp [emitRound_length, Nat.mul_succ]
  rw [emitGadget, List.length_append, h g.tau_s, gadgetLen]
  rfl

theorem compileGadgets_length (L : SurgeryLayout) :
    ∀ (gs : List SurgeryGadget) (t base : Nat),
      (compileGadgets L gs t base).length = (gs.map gadgetLen).sum
  | [], _, _ => rfl
  | g :: gs, t, base => by
      simp [compileGadgets, emitGadget_length,
            compileGadgets_length L gs _ _]

/-- **count = expansion** at the program level: the closed recursive count
    equals the compiled schedule's length — resource upper bounds can be
    computed without materializing. -/
theorem compileQECProgram_length (L : SurgeryLayout) :
    ∀ (p : QECProgram) (t0 round0 : Nat),
      (compileQECProgram L p t0 round0).length = programSyscallCount p
  | [], _, _ => rfl
  | e :: es, t, base => by
      have hev : (compileEvent L t base e).length = eventSyscallCount e := by
        cases e with
        | surgery g => simpa [compileEvent, eventSyscallCount] using
            emitGadget_length L g t base
        | magicSurgery f gs =>
            simp [compileEvent, eventSyscallCount,
                  compileGadgets_length L gs _ _]
            omega
      have ih := compileQECProgram_length L es (t + eventDuration e)
                   (base + eventRounds e)
      simp only [compileQECProgram, compileEvents, List.length_append, hev,
                 programSyscallCount, List.map_cons, List.sum_cons]
      simpa [compileQECProgram, programSyscallCount] using ih

/-! ## §7. Worked heterogeneous program — compiled, then audited

    The shape the legacy replicate artifacts faked, now derived: an X-type
    merge, a CCZ magic injection (1 magic state + 3 DIFFERENT merges), and
    a deeper Z-type merge — compiled by the driver and checked by the SAME
    `checkScheduleOn` the corpus uses, on the catalog's magic-stocked
    machine. -/

section Demo
open FormalRV.System.HardwareCatalog

/-- Layout on the `adder_d3` zone plan: data qubit `i` ↦ site `i` (Data
    zone), ancilla qubit `k` ↦ site `100 + k` (tracked Ancilla zone). -/
def demoLayout : SurgeryLayout :=
  { dataSite := fun i => i, ancillaSite := fun k => 100 + k }

/-- X-type merge: ancilla X-check couples to both data qubits, 2 rounds. -/
def demo_merge_x : SurgeryGadget :=
  { data_code := { n := 2, k := 0, d := 0, hx := [], hz := [[true, false]] }
    ancilla_n := 2, ancilla_hx := [[false, true]], ancilla_hz := []
    conn_x := [[true, true]], conn_z := []
    tau_s := 2, target_pauli := [true, true, false, false]
    span_witness := [true], merged_qldpc_bound := 10 }

/-- Z-type merge: data Z-check couples to the ancilla, 3 rounds (deeper). -/
def demo_merge_z : SurgeryGadget :=
  { data_code := { n := 2, k := 0, d := 0, hx := [], hz := [[true, true]] }
    ancilla_n := 1, ancilla_hx := [], ancilla_hz := []
    conn_x := [], conn_z := [[true]]
    tau_s := 3, target_pauli := [false, true, true]
    span_witness := [true], merged_qldpc_bound := 10 }

/-- Injection merges (the 3 surgery steps of one `teleportCCX`), each a
    single-round single-ancilla merge on a DIFFERENT data qubit pair. -/
def demo_inj (j : Nat) : SurgeryGadget :=
  { data_code := { n := 3, k := 0, d := 0, hx := [], hz := [] }
    ancilla_n := 1
    ancilla_hx := [[true]], ancilla_hz := []
    conn_x := [[j == 0, j == 1, j == 2]], conn_z := []
    tau_s := 1, target_pauli := [j == 0, j == 1, j == 2, true]
    span_witness := [true], merged_qldpc_bound := 10 }

/-- The heterogeneous QEC program: merge ∥ CCZ injection ∥ merge. -/
def demoProgram : QECProgram :=
  [ .surgery demo_merge_x
  , QECEvent.cczInjection 0 (demo_inj 0) (demo_inj 1) (demo_inj 2)
  , .surgery demo_merge_z ]

theorem demoProgram_wf : programWf demoProgram = true := by decide

/-- The compiled schedule: every SysCall derived from connection matrices,
    clock and decoder rounds threaded by the driver. -/
def demoCompiled : List SysCall := compileQECProgram demoLayout demoProgram

/-- **The compiled heterogeneous program PASSES the full system audit**
    (gate support ∧ strict bundle: capacity, exclusivity, freshness,
    decoder budget, I4 magic window, …) on the magic-stocked catalog
    machine. -/
theorem demoCompiled_passes :
    checkScheduleOn adder_d3_magicStock demoCompiled = true := by native_decide

/-- Decode ids are globally unique (instance of the §5 parametric law). -/
theorem demoCompiled_decode_ids_unique :
    decode_ids_unique_ok demoCompiled = true := by native_decide

/-- Reconfigurability holds for compiled QEC programs too: the SAME
    compiled schedule fails on a zero-reaction-budget machine. -/
theorem demoCompiled_fails_without_reaction_budget :
    checkScheduleOn
      { adder_d3_magicStock with
          decoder := { workers := 4, max_latency_us := 0,
                       queue_capacity := 1000 } }
      demoCompiled = false := by native_decide

/-- The closed count matches the compiled length (instance of §6):
    (7·2 + 1) merge-x ++ (1 + 3·(4·1 + 1)) injection ++ (4·3 + 1) merge-z
    = 15 + 16 + 13 = 44 SysCalls. -/
theorem demoCompiled_count :
    demoCompiled.length = programSyscallCount demoProgram :=
  compileQECProgram_length demoLayout demoProgram 0 0

theorem demoCompiled_count_value : programSyscallCount demoProgram = 44 := by
  decide

end Demo

/-! ## §8. GE2021 READINESS — the machine is configured and the lane is
       proven open at d = 27

    When the QEC-level compilation of Gidney–Ekerå 2021 lands (a
    `QECProgram` over d = 27 patches), the system audit is ready: the
    probe below is a GE2021-shaped program — a `tau_s = 27` X-merge, a
    CCZ injection (1 magic state + 3 merges, each 27 rounds), a
    `tau_s = 27` Z-merge — compiled by the W2 driver onto the
    patch-granular GE2021 layout and PASSING `checkScheduleOn
    ge2021_logical` (decoder lanes, reaction budget, syndrome link,
    magic supply curve, causality, freshness — the lot). -/

section GE2021Ready
open FormalRV.System.HardwareCatalog

/-- Patch-granular GE2021 layout: data patch `i` ↦ site `i`, routing/bus
    patch `k` ↦ site `patches + k`. -/
def ge2021Layout : SurgeryLayout :=
  { dataSite := fun i => i
    ancillaSite := fun k => FormalRV.System.RSA2048.patches + k }

/-- A d = 27 two-body merge (27 syndrome rounds, as the paper's lattice
    surgery requires). -/
def ge2021_merge (hz : List (List Bool)) (cx cz : List (List Bool))
    (tp : List Bool) : SurgeryGadget :=
  { data_code := { n := 2, k := 0, d := 0, hx := [], hz := hz }
    ancilla_n := 1, ancilla_hx := [[true]], ancilla_hz := []
    conn_x := cx, conn_z := cz
    tau_s := FormalRV.System.RSA2048.distance
    target_pauli := tp, span_witness := [true]
    merged_qldpc_bound := 10 }

/-- The GE2021-shaped probe: X-merge ∥ CCZ injection ∥ Z-merge, all at
    `tau_s = 27`. -/
def ge2021Probe : QECProgram :=
  [ .surgery (ge2021_merge [] [[true, true]] [] [true, true, false])
  , QECEvent.cczInjection 0
      (ge2021_merge [] [[true, false]] [] [true, false, true])
      (ge2021_merge [] [[false, true]] [] [false, true, true])
      (ge2021_merge [] [[true, true]] [] [true, true, true])
  , .surgery (ge2021_merge [[true, true]] [] [[true]] [false, true, true]) ]

def ge2021ProbeCompiled : List SysCall :=
  compileQECProgram ge2021Layout ge2021Probe

/-- **READY**: the d = 27 probe, compiled by the whole-program driver,
    passes the full GE2021 system audit. -/
theorem ge2021_probe_passes :
    checkScheduleOn ge2021_logical ge2021ProbeCompiled = true := by
  native_decide

/-- The paper's parameters are LIVE on this lane too: halving nothing
    but the reaction budget to 0 µs kills the same compiled probe. -/
theorem ge2021_probe_fails_without_reaction_budget :
    checkScheduleOn
      { ge2021_logical with
          decoder := { workers := FormalRV.System.RSA2048.decodeLanesRequired
                       max_latency_us := 0 } }
      ge2021ProbeCompiled = false := by native_decide

/-- Decode rounds stay globally unique at d = 27 (5 gadgets × 27). -/
theorem ge2021_probe_decode_ids_unique :
    decode_ids_unique_ok ge2021ProbeCompiled = true := by native_decide

theorem ge2021_probe_count :
    ge2021ProbeCompiled.length = programSyscallCount ge2021Probe :=
  compileQECProgram_length ge2021Layout ge2021Probe 0 0

end GE2021Ready

end FormalRV.System.QECScheduleToSystem
