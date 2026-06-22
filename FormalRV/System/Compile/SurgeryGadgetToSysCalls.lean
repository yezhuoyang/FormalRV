/-
  FormalRV.System.SurgeryGadgetToSysCalls — compilers from the
  `LDPCSurgery.SurgeryGadget` qLDPC IR to `SysCall` streams that feed
  the strengthened system-layer cert (`PPMScheduleCertWithFactoryPorts`
  from `Compile/PPMScheduleContract.lean`).

  ## Platform-neutral terminology

  The system layer is **NOT** specific to neutral atoms.  A `SiteId` /
  `PhysicalResourceId` may denote a superconducting physical qubit, a
  trapped-ion zone/qubit, a neutral atom, a spin qubit, a qLDPC block
  position, a lattice-surgery patch slot, or a factory output port —
  depending on the hardware instantiation.  Schedulable-gadget fields
  here use **site** instead of **atom**.  Legacy `atom`-named fields in
  foundational code (`ScheduleInv.ArchZone.site_lo`, `site_hi`,
  `total_sites`, `contains_atom`, `Architecture.syscall_acts_on`) are
  RETAINED to avoid a dangerous global rename; read them as site /
  physical-resource ids.

  ## Contents

    * §1–§8 simple compiler: `SchedulableSurgeryGadget` +
      `compileSurgeryGadgetToSysCalls` (consumes only `tau_s`; fixed
      two-data-site pattern; `5·tau_s + 1` SysCalls).  By-construction
      `rfl` agreement with the hand-written GE2021 `ppm_block_syscalls`
      (`compile_basic_ppm_eq_existing_ppm_block`); cert existence via
      `surgeryGadget_cert_of_valid`; parallel-aliasing rejected,
      parallel-distinct / sequential-triple accepted; foldl-derived
      wallclocks.
    * §9–§12 topology-aware compiler: `connEdges`,
      `TopologySchedulableSurgeryGadget`,
      `compileTopologySurgeryToSysCalls` — the `Gate2q` / `Measure`
      stream is derived from the gadget's actual `conn_x` / `conn_z`
      matrices and `ancilla_n`; demo gadget passes the existing qLDPC
      structural verifier.
    * §13–§16 L3/system contract:
      `verify_surgery_gadget_with_schedule` (qLDPC structural verifier
      ∧ strengthened system bundle), decomposition lemmas, cert
      extraction, the bundled `verify_surgery_gadget_with_schedule_sound`;
      instantiated on the topology demo and the corpus Steane X̄
      surgery, with a negative sanity check.

  Reuses (no re-implementation): `SurgeryGadget` from
  `QEC/LatticeSurgery/LDPCSurgery.lean`; the cert, validator, builder,
  and schedule combinators from `Compile/PPMScheduleContract.lean` /
  `Core/ScheduleCombinators.lean`; `ppm_block_syscalls` and
  `ge2021_ppm_arch` from `PPM/GE2021PPMSysInv.lean`.

  ## Verification boundary

  Verified: SysCall compilation from L3 surgery-gadget descriptions;
  definitional agreement of the simple compiler with the hand-written
  GE2021 PPM block under matching parameters; strengthened system
  invariants on compiled streams; derived wallclock/resource values.

  NOT verified: quantum-semantic correctness of the PPM (whether the
  lattice surgery actually measures the claimed Pauli product);
  decoder algorithm correctness; physical derivation of per-SysCall
  durations; schedule optimality; the full GE2021 schedule at
  RSA-2048 scale.

  No Mathlib.  Pure Bool / Nat / List.  Decidable.
-/

import FormalRV.QEC.LatticeSurgery.LDPCSurgery
import FormalRV.System.Compile.LatticeSurgeryPPMContract
import FormalRV.PPM.GE2021PPMSysInv
import FormalRV.QEC.LatticeSurgery.SurgeryDemoSteane
namespace FormalRV.System.SurgeryGadgetToSysCalls

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.Framework.LDPC
open FormalRV.Framework.GE2021PPMSysInv
open FormalRV.System.LatticeSurgeryPPMContract

/-! ## §0. Platform-neutral identifier aliases

    These type aliases give NEW abstractions a hardware-agnostic
    vocabulary.  All four expand to `Nat`; the type abbreviation
    is documentation-only but lets future code declare the
    intended meaning of an id at its use site.

    Legacy `atom`-named identifiers in foundational code
    (`ArchZone.site_lo`, `contains_atom`, `syscall_acts_on`, etc.)
    are READ AS site / physical-resource ids under this
    platform-neutral framing.  See the file header for the full
    legacy-compatibility note. -/

/-- A generic physical-resource identifier (a qubit, an ion, an
    atom, a slot — depends on the platform). -/
abbrev PhysicalResourceId : Type := Nat

/-- A physical-qubit identifier. -/
abbrev PhysicalQubitId    : Type := Nat

/-- A generic site id (a slot in the data/ancilla/factory layout). -/
abbrev SiteId             : Type := Nat

/-- A lattice-surgery patch slot id. -/
abbrev PatchSlotId        : Type := Nat

/-- A factory output port id (a logical "where a magic state
    appears"; semantics is platform-dependent). -/
abbrev FactoryPortId      : Type := Nat

/-- A routing-graph site id. -/
abbrev RoutingSiteId      : Type := Nat

/-! ## §1. Scheduling spec on top of the existing `SurgeryGadget` IR

    `SurgeryGadget` (from `QEC/LatticeSurgery/LDPCSurgery.lean`) is an
    abstract qLDPC IR: it knows `tau_s` (rounds) but NOT the
    physical-resource ids, the start time, or the decoder-id base
    to use for SysCall emission.  We add a scheduling spec that
    supplies these. -/

/-- A schedulable wrapper: an existing `SurgeryGadget` plus the
    timing / physical-resource mapping context the compiler needs.

    The compiler uses:
      * `gadget.tau_s` — number of stabilizer-extraction rounds.
      * `data_site_a`, `data_site_b` — two representative data
        sites participating in the joint measurement.  (For a
        full qLDPC surgery the merge stabilizer touches many
        more; this minimal compiler captures the worst-case
        per-round resource-traffic pattern.)
      * `ancilla_site` — single ancilla site used across all
        rounds (each round's `RequestFreshAncilla` re-initialises
        it).
      * `start_us` — when the gadget's SysCall stream begins.
      * `decoder_id_base` — first decoder id; round `r` uses
        `decoder_id_base + r`.

    A `SiteId` here may denote a superconducting physical qubit,
    a trapped-ion zone/qubit, a neutral atom, a spin qubit, or a
    lattice-surgery patch slot — depending on the hardware
    instantiation.  See the file header for the
    platform-neutrality note.

    For a real `SurgeryGadget` instance the spec must reflect
    the actual physical-resource layout; this minimal form is
    enough to populate the strengthened cert. -/
structure SchedulableSurgeryGadget where
  gadget          : SurgeryGadget
  data_site_a     : SiteId
  data_site_b     : SiteId
  ancilla_site    : SiteId
  start_us        : Nat
  decoder_id_base : Nat
  deriving Inhabited

/-! ## §2. Compiler from a gadget to SysCalls -/

/-- One round of stabilizer extraction: 5 SysCalls.

      [t0, t0+1)  RequestFreshAncilla
      [t0+1, t0+2) Gate2q data_a → ancilla
      [t0+2, t0+3) Gate2q data_b → ancilla
      [t0+3, t0+4) Measure ancilla
      [t0+4, t0+5) DecodeSyndrome -/
def compileSurgeryGadgetRound
    (s : SchedulableSurgeryGadget) (round_idx : Nat) : List SysCall :=
  let t0  := s.start_us + 5 * round_idx
  let did := s.decoder_id_base + round_idx
  [ { kind     := SysCallKind.RequestFreshAncilla s.ancilla_site
      begin_us := t0
      end_us   := t0 + 1 }
  , { kind     := SysCallKind.Gate2q s.data_site_a s.ancilla_site 0
      begin_us := t0 + 1
      end_us   := t0 + 2 }
  , { kind     := SysCallKind.Gate2q s.data_site_b s.ancilla_site 0
      begin_us := t0 + 2
      end_us   := t0 + 3 }
  , { kind     := SysCallKind.Measure s.ancilla_site 0
      begin_us := t0 + 3
      end_us   := t0 + 4 }
  , { kind     := SysCallKind.DecodeSyndrome did
      begin_us := t0 + 4
      end_us   := t0 + 5 } ]

/-- Compile the full gadget: `tau_s` rounds, then one
    `PauliFrameUpdate` for the final Pauli correction.

    Total SysCalls = `5 · tau_s + 1`. -/
def compileSurgeryGadgetToSysCalls
    (s : SchedulableSurgeryGadget) : List SysCall :=
  (List.range s.gadget.tau_s).flatMap (compileSurgeryGadgetRound s)
  ++ [ { kind     := SysCallKind.PauliFrameUpdate s.decoder_id_base
         begin_us := s.start_us + 5 * s.gadget.tau_s
         end_us   := s.start_us + 5 * s.gadget.tau_s + 1 } ]

/-- Each round emits exactly 5 SysCalls. -/
theorem compileSurgeryGadgetRound_length
    (s : SchedulableSurgeryGadget) (r : Nat) :
    (compileSurgeryGadgetRound s r).length = 5 := rfl

/-- The flatMap-over-range part of the compiled stream has length
    `5 · n` for any `n`.  By induction on `n`. -/
private theorem rounds_flatMap_length (s : SchedulableSurgeryGadget) (n : Nat) :
    ((List.range n).flatMap (compileSurgeryGadgetRound s)).length = 5 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ih]
      simp [compileSurgeryGadgetRound_length]
      omega

/-- Total SysCall count: `5 · tau_s + 1`. -/
theorem compileSurgeryGadgetToSysCalls_length
    (s : SchedulableSurgeryGadget) :
    (compileSurgeryGadgetToSysCalls s).length = 5 * s.gadget.tau_s + 1 := by
  unfold compileSurgeryGadgetToSysCalls
  rw [List.length_append, rounds_flatMap_length]
  rfl

/-! ## §3. The compiler reproduces the existing GE2021 hand-written
       PPM block under matching parameters

    For a `SchedulableSurgeryGadget` with `tau_s = 3`,
    `data_site_a = 0`, `data_site_b = 50`, `ancilla_site = 100`,
    `start_us = 0`, `decoder_id_base = 0`, the compiler emits
    EXACTLY the existing `ppm_block_syscalls`. -/

/-- A trivial `SurgeryGadget` with `tau_s = 3` and otherwise
    empty fields.  Used solely to drive the SysCall compiler
    structurally — the qLDPC structural verifier passes
    vacuously on this gadget (empty codes), but the compiler
    consumes only `tau_s`. -/
def trivial_tau3_gadget : SurgeryGadget :=
  { data_code         := { n := 0, k := 0, d := 0, hx := [], hz := [] }
    ancilla_n         := 0
    ancilla_hx        := []
    ancilla_hz        := []
    conn_x            := []
    conn_z            := []
    tau_s             := 3
    target_pauli      := []
    span_witness      := []
    merged_qldpc_bound := 0
  }

/-- The schedulable spec that, when compiled, exactly reproduces
    `ppm_block_syscalls` (sites 0, 50, 100; start 0; decoder
    base 0). -/
def ge2021_basic_ppm_gadget_spec : SchedulableSurgeryGadget :=
  { gadget          := trivial_tau3_gadget
    data_site_a     := 0
    data_site_b     := 50
    ancilla_site    := 100
    start_us        := 0
    decoder_id_base := 0
  }

/-- Design-intent consistency check (`rfl`): with parameters chosen
    to mirror the hand-written block (sites 0/50/100, start 0,
    decoder base 0), the compiler reproduces `ppm_block_syscalls`
    definitionally.  The compiler was written so that this holds —
    it is a by-construction sanity check, not an independent
    correspondence result. -/
theorem compile_basic_ppm_eq_existing_ppm_block :
    compileSurgeryGadgetToSysCalls ge2021_basic_ppm_gadget_spec
      = ppm_block_syscalls := by
  rfl

/-- The compiler preserves the strengthened invariant bundle on
    the matching spec — reuses the EXISTING
    `ge2021_ppm_block_factory_exclusivity_ok` +
    `ppm_block_all_invariants_ok` (after composing with the
    strengthened bundle).  Closed by `native_decide` (small
    16-SysCall schedule). -/
theorem compile_basic_ppm_all_invariants_ok :
    all_invariants_with_factory_ports_ok
        ge2021_ppm_arch
        (compileSurgeryGadgetToSysCalls ge2021_basic_ppm_gadget_spec)
        10 1000 1000 = true := by
  native_decide

/-! ## §4. Existence theorem: compiled stream → strengthened cert -/

/-- **Cert constructor for surgery gadgets**: whenever the
    compiled SysCall stream of a `SchedulableSurgeryGadget`
    passes the strengthened invariant bundle under the given
    parameters, a `PPMScheduleCertWithFactoryPorts` exists with
    matching fields and a derived wallclock.

    REUSES `mkPPMScheduleCertWithFactoryPorts_of_valid` from
    `PPMScheduleContract.lean` — no duplication of proof
    unpacking. -/
theorem surgeryGadget_cert_of_valid
    (arch : ZonedArch) (s : SchedulableSurgeryGadget)
    (t_react_us window_us max_per_window : Nat)
    (h : all_invariants_with_factory_ports_ok arch
           (compileSurgeryGadgetToSysCalls s)
           t_react_us window_us max_per_window = true) :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.arch = arch
      ∧ cert.syscalls = compileSurgeryGadgetToSysCalls s
      ∧ cert.wallclock_us
          = scheduleWallclockUs (compileSurgeryGadgetToSysCalls s) := by
  obtain ⟨cert, h1, h2, _, _, _, h6⟩ :=
    mkPPMScheduleCertWithFactoryPorts_of_valid
      arch (compileSurgeryGadgetToSysCalls s)
      t_react_us window_us max_per_window h
  exact ⟨cert, h1, h2, h6⟩

/-- Concrete cert existence for the basic GE2021 PPM gadget. -/
theorem ge2021_basic_ppm_surgery_cert_exists :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.arch = ge2021_ppm_arch
      ∧ cert.syscalls
          = compileSurgeryGadgetToSysCalls ge2021_basic_ppm_gadget_spec := by
  obtain ⟨cert, h1, h2, _⟩ :=
    surgeryGadget_cert_of_valid ge2021_ppm_arch ge2021_basic_ppm_gadget_spec
      10 1000 1000 compile_basic_ppm_all_invariants_ok
  exact ⟨cert, h1, h2⟩

/-! ## §5. Good / bad surgery gadgets

    Three concrete `SchedulableSurgeryGadget`s sharing the trivial
    `tau_s = 3` qLDPC IR but with different site layouts.
    (`site` here is platform-neutral; see §0.) -/

/-- Good gadget A: data sites 0/50, ancilla site 100, start t=0. -/
def surgery_ppm_A : SchedulableSurgeryGadget :=
  { gadget          := trivial_tau3_gadget
    data_site_a     := 0
    data_site_b     := 50
    ancilla_site    := 100
    start_us        := 0
    decoder_id_base := 0 }

/-- Good gadget B with DISTINCT ancilla (101): for parallel
    composition. -/
def surgery_ppm_B_distinct : SchedulableSurgeryGadget :=
  { gadget          := trivial_tau3_gadget
    data_site_a     := 10
    data_site_b     := 60
    ancilla_site    := 101
    start_us        := 0
    decoder_id_base := 10 }

/-- Good gadget C with another distinct ancilla (102). -/
def surgery_ppm_C_distinct : SchedulableSurgeryGadget :=
  { gadget          := trivial_tau3_gadget
    data_site_a     := 20
    data_site_b     := 70
    ancilla_site    := 102
    start_us        := 0
    decoder_id_base := 20 }

/-- Bad gadget B with the SAME ancilla 100 as A: parallel
    composition with A causes ancilla aliasing. -/
def surgery_ppm_B_alias : SchedulableSurgeryGadget :=
  { gadget          := trivial_tau3_gadget
    data_site_a     := 10
    data_site_b     := 60
    ancilla_site    := 100        -- ← SAME as A
    start_us        := 0
    decoder_id_base := 10 }

/-- The good gadget A's compiled stream passes the strengthened
    bundle under the existing GE2021 architecture.  By
    construction `surgery_ppm_A` is the same spec as the basic
    GE2021 one. -/
theorem surgery_ppm_A_all_invariants_ok :
    all_invariants_with_factory_ports_ok ge2021_ppm_arch
        (compileSurgeryGadgetToSysCalls surgery_ppm_A) 10 1000 1000 = true := by
  native_decide

theorem surgery_good_cert_exists :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.syscalls = compileSurgeryGadgetToSysCalls surgery_ppm_A := by
  obtain ⟨cert, _, h2, _⟩ :=
    surgeryGadget_cert_of_valid ge2021_ppm_arch surgery_ppm_A
      10 1000 1000 surgery_ppm_A_all_invariants_ok
  exact ⟨cert, h2⟩

/-! ## §6. Parallel composition of two surgery gadgets

    We need a larger architecture (`surgery_arch`) than
    `ge2021_ppm_arch` to accommodate the larger site range used
    by the parallel/triple compositions below. -/

/-- A larger architecture accommodating multiple parallel
    surgery gadgets.  4 zones × 100 sites each, 400 sites total.
    Ancilla zone big enough for the 3 ancilla sites used in the
    triple example.  (`total_sites` is the legacy field name on
    `ScheduleInv.ZonedArch`; read it as "total sites" in
    platform-neutral terms.) -/
def surgery_arch : ZonedArch :=
  { zones :=
      [ { name := "Data",    site_lo := 0,   site_hi := 100 }
      , { name := "Ancilla", site_lo := 100, site_hi := 200 }
      , { name := "Factory", site_lo := 200, site_hi := 300 }
      , { name := "Routing", site_lo := 300, site_hi := 400 } ]
    total_sites := 400
    t_cycle_us  := 1
    v_max_um_per_us := 0
    t_react_us := 10
  }

/-! ### §6.a Parallel-aliasing REJECTED -/

def surgery_pair_parallel_alias_syscalls : List SysCall :=
  parSchedules
    (compileSurgeryGadgetToSysCalls surgery_ppm_A)
    (compileSurgeryGadgetToSysCalls surgery_ppm_B_alias)

/-- The parallel-aliasing surgery pair is REJECTED by the
    strengthened bundle (Gate2qs in concurrent rounds both claim
    ancilla 100). -/
theorem surgery_pair_parallel_alias_rejected :
    validateScheduleWithFactoryPorts
        surgery_arch surgery_pair_parallel_alias_syscalls 10 1000 1000 = false := by
  native_decide

/-! ### §6.b Parallel-distinct ACCEPTED -/

def surgery_pair_parallel_distinct_syscalls : List SysCall :=
  parSchedules
    (compileSurgeryGadgetToSysCalls surgery_ppm_A)
    (compileSurgeryGadgetToSysCalls surgery_ppm_B_distinct)

theorem surgery_pair_parallel_distinct_all_invariants_ok :
    all_invariants_with_factory_ports_ok surgery_arch
        surgery_pair_parallel_distinct_syscalls 10 1000 1000 = true := by
  native_decide

theorem surgery_pair_parallel_distinct_cert_exists :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.syscalls
        = parSchedules
            (compileSurgeryGadgetToSysCalls surgery_ppm_A)
            (compileSurgeryGadgetToSysCalls surgery_ppm_B_distinct) := by
  obtain ⟨cert, _, h2, _⟩ :=
    mkPPMScheduleCertWithFactoryPorts_of_valid
      surgery_arch surgery_pair_parallel_distinct_syscalls 10 1000 1000
      surgery_pair_parallel_distinct_all_invariants_ok
  exact ⟨cert, h2⟩

/-! ## §7. Three-gadget composition

    `seqManySchedules` over three compiled gadget streams. -/

def surgery_triple_sequential_syscalls : List SysCall :=
  seqManySchedules
    [ compileSurgeryGadgetToSysCalls surgery_ppm_A
    , compileSurgeryGadgetToSysCalls surgery_ppm_B_distinct
    , compileSurgeryGadgetToSysCalls surgery_ppm_C_distinct ]

theorem surgery_triple_sequential_all_invariants_ok :
    all_invariants_with_factory_ports_ok surgery_arch
        surgery_triple_sequential_syscalls 10 1000 1000 = true := by
  native_decide

theorem surgery_triple_sequential_cert_exists :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.syscalls = surgery_triple_sequential_syscalls := by
  obtain ⟨cert, _, h2, _⟩ :=
    mkPPMScheduleCertWithFactoryPorts_of_valid
      surgery_arch surgery_triple_sequential_syscalls 10 1000 1000
      surgery_triple_sequential_all_invariants_ok
  exact ⟨cert, h2⟩

/-! ## §8. Derived resource theorems (anti-spreadsheet)

    All wallclock numbers are `foldl`-derived. -/

/-- The good gadget's wallclock IS the foldl of its compiled
    stream — not a typed-in number. -/
theorem surgery_good_wallclock_is_derived :
    scheduleWallclockUs (compileSurgeryGadgetToSysCalls surgery_ppm_A)
      = (compileSurgeryGadgetToSysCalls surgery_ppm_A).foldl
          (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

/-- Same for the triple schedule. -/
theorem surgery_triple_wallclock_is_derived :
    scheduleWallclockUs surgery_triple_sequential_syscalls
      = surgery_triple_sequential_syscalls.foldl
          (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

/-- Concrete wallclock values for the good gadget and triple. -/
theorem surgery_good_wallclock_value :
    scheduleWallclockUs (compileSurgeryGadgetToSysCalls surgery_ppm_A) = 16 := by
  native_decide

theorem surgery_triple_wallclock_value :
    scheduleWallclockUs surgery_triple_sequential_syscalls = 48 := by native_decide
  -- 3 sequential gadgets, each wallclock 16 µs, no overlap.

/-! ## §9. Topology-aware compiler

    The simple compiler above (`compileSurgeryGadgetToSysCalls`)
    uses ONLY `gadget.tau_s` and a fixed two-data-site pattern.
    It does NOT inspect the qLDPC connection matrices `conn_x`
    and `conn_z`.

    This section adds a SECOND, topology-aware compiler that
    derives its `Gate2q` / `Measure` / `DecodeSyndrome` stream
    from the actual connection data of the underlying
    `SurgeryGadget`.  The original simple compiler is preserved
    UNCHANGED (the `rfl` match
    `compile_basic_ppm_eq_existing_ppm_block` continues to hold).

    Conventions used here:
      * `conn_x : BoolMat` — rows index ancilla X-checks
        (length `ancilla_hx.length`); cols index data qubits
        (length `data_code.n`).  An entry `conn_x[i][j] = true`
        means ancilla X-check #i is coupled to data qubit #j.
      * `conn_z : BoolMat` — rows index data Z-checks (length
        `data_code.hz.length`); cols index ancilla qubits
        (length `ancilla_n`).  An entry `conn_z[i][j] = true`
        means data Z-check #i is coupled to ancilla qubit #j.

    Both index conventions match `merged_hx` / `merged_hz` in
    `LDPCSurgery.lean`. -/

/-! ### §9.a Edge extraction from a connection matrix -/

/-- Tail-recursive helper: given a row index `i` and a starting
    column position `j`, walk the BoolVec and emit `(i, k)` for
    every position `k ≥ j` whose entry is `true`. -/
def rowEdgesAux (i : Nat) : Nat → BoolVec → List (Nat × Nat)
  | _, []           => []
  | j, true  :: rest => (i, j) :: rowEdgesAux i (j + 1) rest
  | j, false :: rest => rowEdgesAux i (j + 1) rest

/-- Walk a `BoolMat` and emit the `(row_idx, col_idx)` pairs of
    every `true` entry, with row indices starting from `i`. -/
def connEdgesAux : Nat → BoolMat → List (Nat × Nat)
  | _, []           => []
  | i, row :: rest  => rowEdgesAux i 0 row ++ connEdgesAux (i + 1) rest

/-- Computable edge-list extraction from a connection matrix.
    Output: every `(i, j)` such that `conn[i][j] = true`, in
    row-major order. -/
def connEdges (conn : BoolMat) : List (Nat × Nat) :=
  connEdgesAux 0 conn

/-- The empty connection matrix produces no edges. -/
theorem connEdges_empty : connEdges ([] : BoolMat) = [] := rfl

/-! ### §9.b Topology-schedulable gadget -/

/-- A TOPOLOGY-aware schedulable wrapper.  Unlike
    `SchedulableSurgeryGadget` (which hard-codes two data sites
    and one ancilla site), this wrapper carries SITE-MAPPING
    FUNCTIONS that the compiler applies to the connection-matrix
    indices to derive the actual physical-resource ids used in
    each `Gate2q` / `Measure`.

    Fields:
      * `gadget` — the underlying `SurgeryGadget`.  All of its
        structural fields (`data_code`, `ancilla_n`, `conn_x`,
        `conn_z`, `tau_s`) are CONSUMED by the compiler.
      * `start_us` — when the gadget's SysCall stream begins.
      * `dataSite : Nat → SiteId` — maps a data-qubit index
        `j ∈ {0, …, data_code.n - 1}` to its physical-resource
        id.
      * `ancillaSite : Nat → SiteId` — maps an ancilla-qubit
        index `i ∈ {0, …, ancilla_n - 1}` to its
        physical-resource id.
      * `decoderBase : Nat` — first decoder id; round `r` uses
        `decoderBase + r`.

    `SiteId` is platform-neutral (see §0). -/
structure TopologySchedulableSurgeryGadget where
  gadget       : SurgeryGadget
  start_us     : Nat
  dataSite     : Nat → SiteId
  ancillaSite  : Nat → SiteId
  decoderBase  : Nat

/-- Number of `Gate2q` calls one topology round emits = number
    of `true` entries in `conn_x` plus number of `true` entries
    in `conn_z`. -/
def topologyRoundGateCount (s : TopologySchedulableSurgeryGadget) : Nat :=
  (connEdges s.gadget.conn_x).length + (connEdges s.gadget.conn_z).length

/-- Number of SysCalls one topology round emits:
      1 RequestFreshAncilla + |edges_x| + |edges_z| +
      ancilla_n Measures + 1 DecodeSyndrome
    = `2 + |gates| + ancilla_n`. -/
def topologyRoundLength (s : TopologySchedulableSurgeryGadget) : Nat :=
  2 + topologyRoundGateCount s + s.gadget.ancilla_n

/-! ### §9.c Per-round compiler -/

/-- Emit a per-edge `Gate2q` SysCall stream for the X-coupling
    block.  An X-edge `(i, j)` (ancilla X-check `i`, data qubit
    `j`) emits `Gate2q (dataSite j) (ancillaSite i)` at the
    given offset. -/
def emitXEdgeGates
    (s : TopologySchedulableSurgeryGadget)
    (t_start : Nat)
    (edges : List (Nat × Nat)) : List SysCall :=
  edges.mapIdx fun idx ij =>
    let (i, j) := ij
    { kind     := SysCallKind.Gate2q (s.dataSite j) (s.ancillaSite i) 0
      begin_us := t_start + idx
      end_us   := t_start + idx + 1 }

/-- Emit a per-edge `Gate2q` SysCall stream for the Z-coupling
    block.  A Z-edge `(i, j)` (data Z-check `i`, ancilla qubit
    `j`) emits `Gate2q (dataSite i) (ancillaSite j)` at the
    given offset.

    The role of `i`/`j` swaps relative to X-edges because of the
    asymmetric matrix conventions in `LDPCSurgery.lean`: `conn_x`
    cols are data, `conn_z` cols are ancilla. -/
def emitZEdgeGates
    (s : TopologySchedulableSurgeryGadget)
    (t_start : Nat)
    (edges : List (Nat × Nat)) : List SysCall :=
  edges.mapIdx fun idx ij =>
    let (i, j) := ij
    { kind     := SysCallKind.Gate2q (s.dataSite i) (s.ancillaSite j) 0
      begin_us := t_start + idx
      end_us   := t_start + idx + 1 }

/-- Emit one `Measure` SysCall per ancilla qubit. -/
def emitAncillaMeasures
    (s : TopologySchedulableSurgeryGadget) (t_start : Nat) : List SysCall :=
  (List.range s.gadget.ancilla_n).map fun k =>
    { kind     := SysCallKind.Measure (s.ancillaSite k) 0
      begin_us := t_start + k
      end_us   := t_start + k + 1 }

/-- One topology round emits:
      [t0, t0+1)                    RequestFreshAncilla
      [t0+1, t0+1+|ex|)             Gate2q per X-edge
      [t0+1+|ex|, t0+1+|ex|+|ez|)   Gate2q per Z-edge
      [..|gates|, ..|gates|+a)      Measure per ancilla qubit
      [t0+1+|gates|+a, t0+2+|gates|+a) DecodeSyndrome
    Total per-round SysCalls = `topologyRoundLength s`. -/
def compileTopologySurgeryRound
    (s : TopologySchedulableSurgeryGadget) (round_idx : Nat) : List SysCall :=
  let t0   := s.start_us + (topologyRoundLength s) * round_idx
  let did  := s.decoderBase + round_idx
  let ex   := connEdges s.gadget.conn_x
  let ez   := connEdges s.gadget.conn_z
  let nGx  := ex.length
  let nGz  := ez.length
  let a    := s.gadget.ancilla_n
  let req  := { kind     := SysCallKind.RequestFreshAncilla (s.ancillaSite 0)
                begin_us := t0
                end_us   := t0 + 1 : SysCall }
  let gx   := emitXEdgeGates s (t0 + 1) ex
  let gz   := emitZEdgeGates s (t0 + 1 + nGx) ez
  let meas := emitAncillaMeasures s (t0 + 1 + nGx + nGz)
  let dec  := { kind     := SysCallKind.DecodeSyndrome did
                begin_us := t0 + 1 + nGx + nGz + a
                end_us   := t0 + 2 + nGx + nGz + a : SysCall }
  [req] ++ gx ++ gz ++ meas ++ [dec]

/-! ### §9.d Full gadget compiler -/

/-- Compile a topology-aware schedulable gadget: `tau_s` rounds,
    each derived from the actual connection matrices, plus one
    final `PauliFrameUpdate`. -/
def compileTopologySurgeryToSysCalls
    (s : TopologySchedulableSurgeryGadget) : List SysCall :=
  (List.range s.gadget.tau_s).flatMap (compileTopologySurgeryRound s)
  ++ [ { kind     := SysCallKind.PauliFrameUpdate s.decoderBase
         begin_us := s.start_us + (topologyRoundLength s) * s.gadget.tau_s
         end_us   := s.start_us + (topologyRoundLength s) * s.gadget.tau_s + 1 } ]

/-- The wallclock of the topology-compiled stream IS the foldl
    over `end_us` — not a typed-in number. -/
theorem compileTopologySurgery_wallclock_is_derived
    (s : TopologySchedulableSurgeryGadget) :
    scheduleWallclockUs (compileTopologySurgeryToSysCalls s)
      = (compileTopologySurgeryToSysCalls s).foldl
          (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

/-! ## §10. Topology demo

    A tiny but non-trivial gadget exercising the connection
    matrices.  Two data qubits, two ancilla qubits, one
    X-coupling edge, one Z-coupling edge, `tau_s = 2` rounds. -/

/-- A non-trivial gadget: 2 data qubits, 2 ancilla qubits, one
    X-coupling edge `(0, 0)` (ancilla X-check #0 ↔ data qubit
    #0), one Z-coupling edge `(0, 1)` (data Z-check #0 ↔ ancilla
    qubit #1). -/
def topology_demo_gadget : SurgeryGadget :=
  { data_code         := { n := 2, k := 0, d := 0, hx := [], hz := [[true, false]] }
    ancilla_n         := 2
    ancilla_hx        := [[false, true]]
    ancilla_hz        := []
    conn_x            := [[true, false]]
    conn_z            := [[false, true]]
    tau_s             := 2
    target_pauli      := [true, false, false, true]
    span_witness      := [true]
    merged_qldpc_bound := 10 }

/-- The demo gadget passes the EXISTING qLDPC structural
    verifier from `LDPCSurgery.lean`.  Closed by `native_decide`
    on the small finite structure. -/
theorem topology_demo_gadget_verifies :
    SurgeryGadget.verify_surgery_gadget topology_demo_gadget = true := by
  native_decide

/-- The demo schedulable wrapper: data sites 0/1, ancilla sites
    100/101, start at t=0, decoder base 0. -/
def topology_demo : TopologySchedulableSurgeryGadget :=
  { gadget      := topology_demo_gadget
    start_us    := 0
    dataSite    := fun j => j         -- data qubit j ↦ site j
    ancillaSite := fun i => 100 + i   -- ancilla qubit i ↦ site 100 + i
    decoderBase := 0 }

/-- Edge-list correctness for the X-coupling. -/
theorem topology_demo_x_edges :
    connEdges topology_demo.gadget.conn_x = [(0, 0)] := rfl

/-- Edge-list correctness for the Z-coupling. -/
theorem topology_demo_z_edges :
    connEdges topology_demo.gadget.conn_z = [(0, 1)] := rfl

/-- Per-round SysCall count: 1 ancilla request + 1 X-edge gate +
    1 Z-edge gate + 2 ancilla measures + 1 decode = 6. -/
theorem topology_demo_round_length :
    topologyRoundLength topology_demo = 6 := rfl

/-- Total SysCall count of the topology-compiled demo:
    2 rounds × 6 per-round = 12, plus 1 PauliFrameUpdate. -/
theorem topology_demo_total_syscalls :
    (compileTopologySurgeryToSysCalls topology_demo).length = 13 := by
  native_decide

/-- The topology-compiled demo stream passes the strengthened
    system-layer invariant bundle on the larger surgery
    architecture (`surgery_arch`). -/
theorem topology_demo_all_invariants_with_factory_ports_ok :
    all_invariants_with_factory_ports_ok surgery_arch
        (compileTopologySurgeryToSysCalls topology_demo) 10 1000 1000 = true := by
  native_decide

/-- Existence of a strengthened cert for the topology-compiled
    demo schedule. -/
theorem topology_demo_cert_exists :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.arch = surgery_arch
      ∧ cert.syscalls = compileTopologySurgeryToSysCalls topology_demo := by
  obtain ⟨cert, h1, h2, _⟩ :=
    mkPPMScheduleCertWithFactoryPorts_of_valid
      surgery_arch (compileTopologySurgeryToSysCalls topology_demo)
      10 1000 1000 topology_demo_all_invariants_with_factory_ports_ok
  exact ⟨cert, h1, h2⟩

/-- The topology-compiled demo's wallclock is foldl-derived. -/
theorem topology_demo_wallclock_is_derived :
    scheduleWallclockUs (compileTopologySurgeryToSysCalls topology_demo)
      = (compileTopologySurgeryToSysCalls topology_demo).foldl
          (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

/-- Concrete wallclock value: 6 µs × 2 rounds + 1 µs PauliFrameUpdate = 13. -/
theorem topology_demo_wallclock_value :
    scheduleWallclockUs (compileTopologySurgeryToSysCalls topology_demo) = 13 := by
  native_decide

/-! ## §11. Combined qLDPC + system-invariant verifier

    A unified checker that pairs the EXISTING qLDPC structural
    verifier (`verify_surgery_gadget` from `LDPCSurgery.lean`)
    with the strengthened system-layer invariant bundle
    (`all_invariants_with_factory_ports_ok` from
    `PPMScheduleContract.lean`).

    A topology-scheduled surgery gadget passes the combined
    checker iff:
      (a) its underlying qLDPC gadget passes the structural
          verifier (dimensions, qLDPC-bound, τ_s sufficient,
          row-span identity); AND
      (b) its topology-compiled SysCall stream passes the
          strengthened system-layer invariant bundle (I1-I4 +
          factory-port exclusivity). -/

/-- The combined verifier. -/
def verify_surgery_gadget_with_schedule
    (s : TopologySchedulableSurgeryGadget)
    (arch : ZonedArch)
    (t_react_us window_us max_per_window : Nat) : Bool :=
  SurgeryGadget.verify_surgery_gadget s.gadget
  && all_invariants_with_factory_ports_ok arch
        (compileTopologySurgeryToSysCalls s)
        t_react_us window_us max_per_window

/-- The demo passes the combined verifier under
    `(surgery_arch, 10, 1000, 1000)`. -/
theorem topology_demo_combined_verifies :
    verify_surgery_gadget_with_schedule
      topology_demo surgery_arch 10 1000 1000 = true := by
  native_decide

/-! ## §12. Parallel-aliasing rejection at the topology layer -/

/-- A second topology-schedulable gadget with the SAME ancilla
    sites as `topology_demo`: parallel composition causes
    ancilla aliasing.  Same structural gadget; different start
    time and decoder base. -/
def topology_demo_alias : TopologySchedulableSurgeryGadget :=
  { gadget      := topology_demo_gadget
    start_us    := 0
    dataSite    := fun j => 10 + j      -- distinct data sites
    ancillaSite := fun i => 100 + i     -- ← SAME ancilla sites as topology_demo
    decoderBase := 20 }

def topology_pair_alias_syscalls : List SysCall :=
  parSchedules
    (compileTopologySurgeryToSysCalls topology_demo)
    (compileTopologySurgeryToSysCalls topology_demo_alias)

/-- The parallel-aliasing topology pair is REJECTED by the
    strengthened bundle (concurrent rounds both claim ancilla
    sites 100/101). -/
theorem topology_pair_alias_rejected :
    validateScheduleWithFactoryPorts
        surgery_arch topology_pair_alias_syscalls 10 1000 1000 = false := by
  native_decide

/-- A topology-schedulable gadget with DISTINCT ancilla sites
    from `topology_demo`: parallel composition is admissible. -/
def topology_demo_distinct : TopologySchedulableSurgeryGadget :=
  { gadget      := topology_demo_gadget
    start_us    := 0
    dataSite    := fun j => 10 + j      -- distinct data sites
    ancillaSite := fun i => 110 + i     -- distinct ancilla sites
    decoderBase := 20 }

def topology_pair_distinct_syscalls : List SysCall :=
  parSchedules
    (compileTopologySurgeryToSysCalls topology_demo)
    (compileTopologySurgeryToSysCalls topology_demo_distinct)

theorem topology_pair_distinct_all_invariants_ok :
    all_invariants_with_factory_ports_ok surgery_arch
        topology_pair_distinct_syscalls 10 1000 1000 = true := by
  native_decide

theorem topology_pair_distinct_cert_exists :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.syscalls = topology_pair_distinct_syscalls := by
  obtain ⟨cert, _, h2, _⟩ :=
    mkPPMScheduleCertWithFactoryPorts_of_valid
      surgery_arch topology_pair_distinct_syscalls 10 1000 1000
      topology_pair_distinct_all_invariants_ok
  exact ⟨cert, h2⟩

/-! ## §13. L3/system contract theorems

    The combined Boolean checker
    `verify_surgery_gadget_with_schedule` returns `true` iff
    both (a) the underlying `SurgeryGadget` passes the EXISTING
    qLDPC structural verifier and (b) the topology-compiled
    SysCall stream passes the strengthened system-layer
    invariant bundle.

    This section turns that Boolean conjunction into proper
    theorems: a checker that returns `true` yields a
    `PPMScheduleCertWithFactoryPorts` whose wallclock is derived
    by `scheduleWallclockUs` over the compiled stream.

    The theorems are stated for arbitrary `arch`, `s`,
    `t_react_us`, `window_us`, `max_per_window` — they are
    reusable certificates, not demo-specific facts. -/

/-! ### §13.a Boolean decomposition lemmas -/

/-- If the combined checker holds, the underlying
    `SurgeryGadget` passes the existing qLDPC structural
    verifier. -/
theorem verify_surgery_gadget_with_schedule_implies_gadget_ok
    (arch : ZonedArch) (s : TopologySchedulableSurgeryGadget)
    (t_react_us window_us max_per_window : Nat)
    (h : verify_surgery_gadget_with_schedule
            s arch t_react_us window_us max_per_window = true) :
    SurgeryGadget.verify_surgery_gadget s.gadget = true := by
  unfold verify_surgery_gadget_with_schedule at h
  exact (Bool.and_eq_true _ _).mp h |>.1

/-- If the combined checker holds, the underlying gadget — as a
    one-element schedule — passes the qLDPC schedule verifier.
    (The schedule verifier just maps `verify_surgery_gadget`
    over every gadget in the list.) -/
theorem verify_surgery_gadget_with_schedule_implies_schedule_ok
    (arch : ZonedArch) (s : TopologySchedulableSurgeryGadget)
    (t_react_us window_us max_per_window : Nat)
    (h : verify_surgery_gadget_with_schedule
            s arch t_react_us window_us max_per_window = true) :
    SurgeryGadget.verify_surgery_schedule [s.gadget] = true := by
  have hg : SurgeryGadget.verify_surgery_gadget s.gadget = true :=
    verify_surgery_gadget_with_schedule_implies_gadget_ok
      arch s t_react_us window_us max_per_window h
  simp [SurgeryGadget.verify_surgery_schedule, List.all_cons, List.all_nil, hg]

/-- If the combined checker holds, the topology-compiled SysCall
    stream passes the strengthened system-layer invariant
    bundle. -/
theorem verify_surgery_gadget_with_schedule_implies_system_ok
    (arch : ZonedArch) (s : TopologySchedulableSurgeryGadget)
    (t_react_us window_us max_per_window : Nat)
    (h : verify_surgery_gadget_with_schedule
            s arch t_react_us window_us max_per_window = true) :
    all_invariants_with_factory_ports_ok arch
      (compileTopologySurgeryToSysCalls s)
      t_react_us window_us max_per_window = true := by
  unfold verify_surgery_gadget_with_schedule at h
  exact (Bool.and_eq_true _ _).mp h |>.2

/-! ### §13.b Certificate extraction theorem

    This theorem is the L3/system contract: a verified
    `SurgeryGadget` plus a system-valid compiled SysCall stream
    yields a `PPMScheduleCertWithFactoryPorts` whose resources
    are derived from the compiled stream.

    What is NOT proven here:
      * quantum semantic correctness of the PPM (whether the
        lattice surgery actually measures the claimed Pauli
        product) — `verify_surgery_gadget` is a STRUCTURAL
        check (dimensions, qLDPC bound, τ_s sufficiency,
        row-span identity);
      * physical derivation of per-SysCall durations;
      * decoder algorithm correctness;
      * schedule optimality;
      * full GE2021 schedule at RSA-2048 scale. -/

/-- **Main contract theorem.**  If the combined checker
    returns `true` on a topology-schedulable gadget, then a
    strengthened cert exists with EXACTLY the input parameters
    and the wallclock derived from the compiled stream by
    `scheduleWallclockUs`.

    Reuses
    `mkPPMScheduleCertWithFactoryPorts_of_valid` — no
    duplication of the 7-fold invariant unpacking. -/
theorem verify_surgery_gadget_with_schedule_cert_exists
    (arch : ZonedArch) (s : TopologySchedulableSurgeryGadget)
    (t_react_us window_us max_per_window : Nat)
    (h : verify_surgery_gadget_with_schedule
            s arch t_react_us window_us max_per_window = true) :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.arch = arch
      ∧ cert.syscalls = compileTopologySurgeryToSysCalls s
      ∧ cert.t_react_us = t_react_us
      ∧ cert.window_us = window_us
      ∧ cert.max_per_window = max_per_window
      ∧ cert.wallclock_us
          = scheduleWallclockUs (compileTopologySurgeryToSysCalls s) :=
  mkPPMScheduleCertWithFactoryPorts_of_valid
    arch (compileTopologySurgeryToSysCalls s)
    t_react_us window_us max_per_window
    (verify_surgery_gadget_with_schedule_implies_system_ok
      arch s t_react_us window_us max_per_window h)

/-! ### §13.c Bundled soundness theorem (paper-facing)

    Single statement that returns all three facts together —
    the natural form for citing the L3/system contract from
    paper-facing prose. -/

/-- **The paper-facing contract theorem.**  If the combined
    Boolean checker returns `true`, then:

      (1) the qLDPC `SurgeryGadget` passes the existing
          structural verifier;
      (2) the same gadget — as a one-element schedule — passes
          the qLDPC schedule verifier;
      (3) the topology-compiled SysCall stream passes the
          strengthened system-layer invariant bundle (I1-I4 +
          factory-port exclusivity); AND
      (4) a `PPMScheduleCertWithFactoryPorts` exists whose
          `syscalls` field is exactly the compiled stream. -/
theorem verify_surgery_gadget_with_schedule_sound
    (arch : ZonedArch) (s : TopologySchedulableSurgeryGadget)
    (t_react_us window_us max_per_window : Nat)
    (h : verify_surgery_gadget_with_schedule
            s arch t_react_us window_us max_per_window = true) :
    SurgeryGadget.verify_surgery_gadget s.gadget = true
    ∧ SurgeryGadget.verify_surgery_schedule [s.gadget] = true
    ∧ all_invariants_with_factory_ports_ok arch
        (compileTopologySurgeryToSysCalls s)
        t_react_us window_us max_per_window = true
    ∧ ∃ cert : PPMScheduleCertWithFactoryPorts,
        cert.syscalls = compileTopologySurgeryToSysCalls s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact verify_surgery_gadget_with_schedule_implies_gadget_ok
            arch s t_react_us window_us max_per_window h
  · exact verify_surgery_gadget_with_schedule_implies_schedule_ok
            arch s t_react_us window_us max_per_window h
  · exact verify_surgery_gadget_with_schedule_implies_system_ok
            arch s t_react_us window_us max_per_window h
  · obtain ⟨cert, _, hsc, _, _, _, _⟩ :=
      verify_surgery_gadget_with_schedule_cert_exists
        arch s t_react_us window_us max_per_window h
    exact ⟨cert, hsc⟩

/-! ## §14. Demo instantiations of the L3/system contract -/

/-- The demo architecture — alias for `surgery_arch`.  Stated
    as a separate `def` so the demo theorems quote a
    "demo-named" parameter rather than the generic
    `surgery_arch`. -/
def topology_demo_arch : ZonedArch := surgery_arch

/-- Standard decoder-react budget for the demos: 10 µs. -/
def topology_demo_t_react_us : Nat := 10

/-- Standard throughput window for the demos: 1000 µs. -/
def topology_demo_window_us : Nat := 1000

/-- Standard max syscalls per window for the demos. -/
def topology_demo_max_per_window : Nat := 1000

/-- The topology demo passes the combined verifier under the
    demo parameters.  Re-stated from
    `topology_demo_combined_verifies` so it quotes the demo
    aliases rather than the literals. -/
theorem topology_demo_combined_verifies_alias :
    verify_surgery_gadget_with_schedule
      topology_demo topology_demo_arch
      topology_demo_t_react_us topology_demo_window_us
      topology_demo_max_per_window = true := by
  unfold topology_demo_arch topology_demo_t_react_us
         topology_demo_window_us topology_demo_max_per_window
  exact topology_demo_combined_verifies

/-- **Demo instantiation of the bundled contract theorem.** -/
theorem topology_demo_sound :
    SurgeryGadget.verify_surgery_gadget topology_demo.gadget = true
    ∧ SurgeryGadget.verify_surgery_schedule [topology_demo.gadget] = true
    ∧ all_invariants_with_factory_ports_ok topology_demo_arch
        (compileTopologySurgeryToSysCalls topology_demo)
        topology_demo_t_react_us topology_demo_window_us
        topology_demo_max_per_window = true
    ∧ ∃ cert : PPMScheduleCertWithFactoryPorts,
        cert.syscalls = compileTopologySurgeryToSysCalls topology_demo :=
  verify_surgery_gadget_with_schedule_sound
    topology_demo_arch topology_demo
    topology_demo_t_react_us topology_demo_window_us
    topology_demo_max_per_window
    topology_demo_combined_verifies_alias

/-- **Demo cert extraction**: the topology demo yields a
    strengthened cert whose wallclock is derived from its
    compiled stream. -/
theorem topology_demo_cert_from_combined_verifier :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.arch = topology_demo_arch
      ∧ cert.syscalls = compileTopologySurgeryToSysCalls topology_demo
      ∧ cert.wallclock_us
          = scheduleWallclockUs (compileTopologySurgeryToSysCalls topology_demo) := by
  obtain ⟨cert, harch, hsc, _, _, _, hwc⟩ :=
    verify_surgery_gadget_with_schedule_cert_exists
      topology_demo_arch topology_demo
      topology_demo_t_react_us topology_demo_window_us
      topology_demo_max_per_window
      topology_demo_combined_verifies_alias
  exact ⟨cert, harch, hsc, hwc⟩

/-! ## §15. Reuse on an existing corpus surgery gadget

    `QEC/LatticeSurgery/SurgeryDemoSteane.lean` defines `steane_x_surgery`,
    a real `SurgeryGadget` measuring logical X̄ on Steane
    [[7,1,3]] code, with `steane_x_surgery_verifies` proving it
    passes the EXISTING qLDPC structural verifier.

    We wrap it in a `TopologySchedulableSurgeryGadget` with
    natural site maps (data sites 0..6, ancilla site 100) and
    apply the L3/system contract.  No re-definition of the
    gadget — only a scheduling spec on top. -/

/-- The Steane X-surgery gadget wrapped as a topology
    schedulable.  Reuses
    `FormalRV.LatticeSurgery.SurgeryDemoSteane.steane_x_surgery`. -/
def topology_steane_x : TopologySchedulableSurgeryGadget :=
  { gadget      := FormalRV.LatticeSurgery.SurgeryDemoSteane.steane_x_surgery
    start_us    := 0
    dataSite    := fun j => j         -- data qubit j ↦ site j
    ancillaSite := fun i => 100 + i   -- ancilla qubit i ↦ site 100 + i
    decoderBase := 0 }

/-- Edge-count sanity: the Steane X-surgery has 3 X-edges
    (row 0 of `conn_x` touches data qubits 3, 5, 6; row 1 is
    all-zero) and 0 Z-edges (the Z-coupling matrix is all
    false).  Closed by `decide` since `topology_steane_x` and
    its underlying gadget are `def`s (no `@[reducible]`); both
    sides are concrete and decidable. -/
theorem topology_steane_x_x_edges :
    connEdges topology_steane_x.gadget.conn_x = [(0, 3), (0, 5), (0, 6)] := by
  decide

theorem topology_steane_x_z_edges :
    connEdges topology_steane_x.gadget.conn_z = [] := by
  decide

/-- Per-round SysCall count: 1 ancilla request + 3 X-edge gates
    + 0 Z-edge gates + 1 ancilla measure + 1 decode = 6. -/
theorem topology_steane_x_round_length :
    topologyRoundLength topology_steane_x = 6 := by
  decide

/-- The Steane topology gadget passes the combined verifier on
    `topology_demo_arch`. -/
theorem topology_steane_x_combined_verifies :
    verify_surgery_gadget_with_schedule
      topology_steane_x topology_demo_arch
      topology_demo_t_react_us topology_demo_window_us
      topology_demo_max_per_window = true := by
  native_decide

/-- **Corpus instantiation of the bundled contract theorem.** -/
theorem topology_steane_x_sound :
    SurgeryGadget.verify_surgery_gadget topology_steane_x.gadget = true
    ∧ SurgeryGadget.verify_surgery_schedule [topology_steane_x.gadget] = true
    ∧ all_invariants_with_factory_ports_ok topology_demo_arch
        (compileTopologySurgeryToSysCalls topology_steane_x)
        topology_demo_t_react_us topology_demo_window_us
        topology_demo_max_per_window = true
    ∧ ∃ cert : PPMScheduleCertWithFactoryPorts,
        cert.syscalls = compileTopologySurgeryToSysCalls topology_steane_x :=
  verify_surgery_gadget_with_schedule_sound
    topology_demo_arch topology_steane_x
    topology_demo_t_react_us topology_demo_window_us
    topology_demo_max_per_window
    topology_steane_x_combined_verifies

/-- **Corpus cert extraction.** -/
theorem topology_steane_x_cert_from_combined_verifier :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.arch = topology_demo_arch
      ∧ cert.syscalls = compileTopologySurgeryToSysCalls topology_steane_x
      ∧ cert.wallclock_us
          = scheduleWallclockUs (compileTopologySurgeryToSysCalls topology_steane_x) := by
  obtain ⟨cert, harch, hsc, _, _, _, hwc⟩ :=
    verify_surgery_gadget_with_schedule_cert_exists
      topology_demo_arch topology_steane_x
      topology_demo_t_react_us topology_demo_window_us
      topology_demo_max_per_window
      topology_steane_x_combined_verifies
  exact ⟨cert, harch, hsc, hwc⟩

/-! ## §16. Negative soundness sanity check

    The bundled contract theorem applies only when the combined
    Boolean checker returns `true`.  To show this premise is
    NOT vacuous, we verify that the existing
    `topology_pair_alias_syscalls` schedule (parallel
    composition of two gadgets with aliased ancilla sites) is
    REJECTED by the system part — under the SAME demo
    parameters that admit `topology_demo`. -/

theorem topology_alias_pair_system_not_ok :
    all_invariants_with_factory_ports_ok
        topology_demo_arch topology_pair_alias_syscalls
        topology_demo_t_react_us topology_demo_window_us
        topology_demo_max_per_window = false := by
  native_decide

end FormalRV.System.SurgeryGadgetToSysCalls
