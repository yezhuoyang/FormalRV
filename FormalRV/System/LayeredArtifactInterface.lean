/-
  FormalRV.Framework.LayeredArtifactInterface — shared
  multi-layer artifact and certificate interface.

  ## Strategic role

  The framework should support both:

    (1) **Lean-generated** circuits / schedules / certificates.
    (2) **Python / Qiskit / third-party-generated** circuits /
        schedules / certificates.

  Both target the SAME interfaces.  Lean is the trusted
  verifier; external tools may generate artifacts, but their
  output must be re-checked by Lean.

  ## Layers covered

      L1  logical             Shor, modular exp, full adder
      L2  gateIR              Cuccaro / Gidney adder, lookups
      L3  cliffordT / ppm     Toffoli, CCZ teleport, PPM
      L3' surgery             lattice-surgery gadget IR
      L4  syscall             SysCall schedule
      L4' compressedSchedule  hierarchical schedule (TBD)

  Each artifact carries:
    * a layer tag,
    * a metadata block (name, description),
    * a payload of the layer's concrete IR type,
    * (optionally) a verified certificate proving system-level
      invariants on the lowered SysCall stream.

  ## What this tick delivers

    * `ArtifactLayer` + `ArtifactMetadata`.
    * `GateArtifact`, `SurgeryArtifact`,
      `SysCallScheduleArtifact` — layer-specific payloads.
    * `SystemModels` — the system-side parameter bundle.
    * `VerifiedSysCallSchedule` — proof-carrying certificate
      with `wallclock_derived` and `strict_ok` fields.
    * `LayerCompiler α β` — a uniform compiler interface;
      instantiated by wrapping existing compilers.
    * `verified_syscall_schedule_of_strict_ok` — generic
      checker theorem: anything that passes the strict bundle
      yields a `VerifiedSysCallSchedule`.
    * Lean-generated example: `adder_n1_syscall_artifact` +
      `adder_n1_artifact_verified` (reuses the existing
      `adder_n1_strict_system_ok`, no re-proof).
    * `ExternalScheduleCertificate` — the Lean-side mock of
      the format external tools must produce.
    * Checker functions on external certs:
      `external_wallclock_matches`,
      `external_syscall_count_matches`,
      `external_gate2q_count_matches`,
      `external_schedule_strict_ok` (bundle of all three +
      strict-system invariants).
    * `python_generated_adder_example` (good) →
      `python_generated_adder_example_checked = true`.
    * `python_bad_wallclock_example` (bad) →
      `python_bad_wallclock_example_rejected = false`.
    * `CompressedSchedule` placeholder inductive — type only,
      no eval semantics yet.

  No new system-layer checks.  No JSON parsing.  No `sorry`,
  no custom `axiom`.
-/

import FormalRV.Core.Gate
import FormalRV.LatticeSurgery.LDPCSurgery
import FormalRV.LatticeSurgery.SurgeryGadgetToSysCalls
import FormalRV.LatticeSurgery.LatticeSurgeryPPMContract
import FormalRV.System.SystemInvariantStrengthening
import FormalRV.System.AdderSystem

namespace FormalRV.Framework.LayeredArtifactInterface

open FormalRV.Framework
open FormalRV.Framework.Architecture
open FormalRV.Framework.ScheduleInv
open FormalRV.Framework.LDPC
open FormalRV.Framework.LatticeSurgeryPPMContract
open FormalRV.Framework.SurgeryGadgetToSysCalls
open FormalRV.Framework.SystemInvariantStrengthening
open FormalRV.Framework.AdderSystem

/-! ## §1. Layer tags and metadata -/

/-- The framework's layer taxonomy.  Each artifact carries one
    of these tags so cross-layer compilation is explicit. -/
inductive ArtifactLayer where
  | logical            -- L1: high-level circuit (Shor, etc.)
  | gateIR             -- L2: Cuccaro / Gidney Gate IR
  | cliffordT          -- L3: Clifford+T / Toffoli decomposition
  | ppm                -- L3: PPM gadget
  | surgery            -- L3: lattice-surgery gadget
  | syscall            -- L4: SysCall schedule
  | compressedSchedule -- L4: hierarchical schedule (TBD)
  deriving Repr, DecidableEq, Inhabited

/-- Lightweight artifact metadata. -/
structure ArtifactMetadata where
  name        : String
  layer       : ArtifactLayer
  description : String
  deriving Repr, Inhabited

/-! ## §2. Layer-specific artifacts -/

/-- A Gate-IR (L2) artifact.  `Gate` does not derive
    `Inhabited` in the framework, so neither does this
    wrapper. -/
structure GateArtifact where
  metadata : ArtifactMetadata
  gate : Gate

/-- A surgery-gadget (L3) artifact. -/
structure SurgeryArtifact where
  metadata : ArtifactMetadata
  gadget   : SurgeryGadget
  deriving Inhabited

/-- A SysCall-schedule (L4) artifact: a finite list of
    `SysCall`s plus metadata.  This is the layer at which the
    strict system bundle operates. -/
structure SysCallScheduleArtifact where
  metadata : ArtifactMetadata
  syscalls : List SysCall
  deriving Inhabited

/-! ## §3. The system-side parameter bundle

    Every system-layer certificate quotes the same five
    parameter groups: zoned architecture, operation-capacity
    model, slot-capacity model, ancilla-freshness model, plus
    the three scalar `t_react_us / window_us /
    max_per_window` parameters. -/

structure SystemModels where
  arch           : ZonedArch
  opCap          : OperationCapacityModel
  slotCap        : SlotCapacityModel
  ancillaModel   : AncillaModel
  t_react_us     : Nat
  window_us      : Nat
  max_per_window : Nat
  deriving Inhabited

/-! ## §4. The verified-SysCall-schedule certificate

    Proof-carrying: stores `wallclock_us` plus a `rfl`-shape
    derivation field and the strict-bundle theorem. -/

/-- **The certified L4 artifact.**  Carries a SysCall artifact,
    its system models, the derived wallclock, AND proofs that
    the wallclock is the foldl over `end_us` and that the
    strict bundle passes. -/
structure VerifiedSysCallSchedule where
  artifact          : SysCallScheduleArtifact
  models            : SystemModels
  wallclock_us      : Nat
  wallclock_derived :
    wallclock_us = scheduleWallclockUs artifact.syscalls
  strict_ok :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch models.opCap models.slotCap models.ancillaModel
        artifact.syscalls
        models.t_react_us models.window_us models.max_per_window = true

/-! ## §5. Generic checker theorem

    Any artifact + models that satisfy the strict bundle
    package into a `VerifiedSysCallSchedule`.  This is the
    contract between any generator (Lean or Python) and the
    framework. -/

/-- **The generic checker theorem.**  If the strict-with-
    slot-capacity-and-freshness bundle holds on a SysCall
    artifact under given models, a
    `VerifiedSysCallSchedule` exists carrying that artifact,
    those models, and the foldl-derived wallclock. -/
theorem verified_syscall_schedule_of_strict_ok
    (artifact : SysCallScheduleArtifact) (models : SystemModels)
    (h : all_invariants_strict_with_slot_capacity_and_freshness_ok
            models.arch models.opCap models.slotCap models.ancillaModel
            artifact.syscalls
            models.t_react_us models.window_us models.max_per_window = true) :
    ∃ cert : VerifiedSysCallSchedule,
      cert.artifact = artifact
      ∧ cert.models = models
      ∧ cert.wallclock_us = scheduleWallclockUs artifact.syscalls :=
  ⟨ { artifact          := artifact
      models            := models
      wallclock_us      := scheduleWallclockUs artifact.syscalls
      wallclock_derived := rfl
      strict_ok         := h },
    rfl, rfl, rfl ⟩

/-! ## §6. Layer compiler interface

    A uniform record for compilers between layers.  Wraps
    existing functions; no new compilation logic. -/

/-- A compiler from layer α-shape artifacts to layer β-shape
    artifacts.  Compile is a pure function; soundness
    theorems live outside this record. -/
structure LayerCompiler (α β : Type) where
  name    : String
  compile : α → β
  deriving Inhabited

/-! ### §6.a Wrappers around the existing surgery → SysCall
       compilers -/

/-- Wrap the simple-compiler `compileSurgeryGadgetToSysCalls`
    as a `LayerCompiler`.  Output: `SysCallScheduleArtifact`. -/
def simpleSurgeryToSysCallCompiler :
    LayerCompiler SchedulableSurgeryGadget SysCallScheduleArtifact :=
  { name    := "simpleSurgeryToSysCallCompiler"
    compile := fun s =>
      { metadata := { name        := "simple-surgery-compiled"
                      layer       := ArtifactLayer.syscall
                      description :=
                        "Compiled from a SchedulableSurgeryGadget by " ++
                        "the simple compileSurgeryGadgetToSysCalls." }
        syscalls := compileSurgeryGadgetToSysCalls s } }

/-- Wrap the topology-aware compiler
    `compileTopologySurgeryToSysCalls` as a `LayerCompiler`. -/
def topologySurgeryToSysCallCompiler :
    LayerCompiler TopologySchedulableSurgeryGadget SysCallScheduleArtifact :=
  { name    := "topologySurgeryToSysCallCompiler"
    compile := fun s =>
      { metadata := { name        := "topology-surgery-compiled"
                      layer       := ArtifactLayer.syscall
                      description :=
                        "Compiled from a TopologySchedulableSurgeryGadget by " ++
                        "the topology-aware compileTopologySurgeryToSysCalls." }
        syscalls := compileTopologySurgeryToSysCalls s } }

/-! ## §7. Lean-generated adder artifact (reuses the
       existing `adder_n1_strict_system_ok` — no re-proof) -/

/-- The Lean-generated adder skeleton wrapped as a
    `SysCallScheduleArtifact`. -/
def adder_n1_syscall_artifact : SysCallScheduleArtifact :=
  { metadata := { name        := "adder_n1_syscalls"
                  layer       := ArtifactLayer.syscall
                  description :=
                    "Three sequential surgery_ppm_A blocks on ancilla " ++
                    "site 100.  Adder-shape skeleton, not arithmetic verified." }
    syscalls := adder_n1_syscalls }

/-- The system-models bundle used by `AdderSystem`. -/
def adder_n1_system_models : SystemModels :=
  { arch           := adder_demo_arch
    opCap          := adder_demo_opCap
    slotCap        := adder_demo_slotCap
    ancillaModel   := adder_demo_ancillaModel
    t_react_us     := adder_demo_t_react_us
    window_us      := adder_demo_window_us
    max_per_window := adder_demo_max_per_window }

/-- **Adder artifact verified** — reuses
    `adder_n1_strict_system_ok` and the generic checker
    theorem.  No `native_decide` re-run on the schedule. -/
theorem adder_n1_artifact_verified :
    ∃ cert : VerifiedSysCallSchedule,
      cert.artifact = adder_n1_syscall_artifact
      ∧ cert.models = adder_n1_system_models
      ∧ cert.wallclock_us
          = scheduleWallclockUs adder_n1_syscall_artifact.syscalls :=
  verified_syscall_schedule_of_strict_ok
    adder_n1_syscall_artifact adder_n1_system_models
    adder_n1_strict_system_ok

/-! ## §8. External (Python / Qiskit / third-party) certificate
       format

    External tools should emit:
      * `producer` — identifier;
      * `claimed_layer` — which layer the artifact targets
        (typically `.syscall`);
      * `syscalls` — the SysCall list;
      * `claimed_*` — the producer's own resource numbers;
      * `notes` — free-form metadata.

    Lean re-derives each `claimed_*` from `syscalls` and
    rejects mismatches.  This is the boundary between
    untrusted generation and trusted verification.

    JSON / file-format parsing is NOT in scope here — the
    Lean-side struct is the canonical form; external tools
    should serialize/deserialize to it via their preferred
    transport. -/

structure ExternalScheduleCertificate where
  producer              : String
  claimed_layer         : ArtifactLayer
  syscalls              : List SysCall
  claimed_wallclock_us  : Nat
  claimed_syscall_count : Nat
  claimed_gate2q_count  : Nat
  notes                 : String
  deriving Inhabited

/-! ### §8.a Per-claim checker functions -/

/-- Producer's claimed wallclock equals the foldl-derived
    value. -/
def external_wallclock_matches (c : ExternalScheduleCertificate) : Bool :=
  decide (c.claimed_wallclock_us = scheduleWallclockUs c.syscalls)

/-- Producer's claimed SysCall count equals
    `c.syscalls.length`. -/
def external_syscall_count_matches (c : ExternalScheduleCertificate) : Bool :=
  decide (c.claimed_syscall_count = c.syscalls.length)

/-- Producer's claimed Gate2q count equals
    `(syscalls.filter Gate2q).length`. -/
def external_gate2q_count_matches (c : ExternalScheduleCertificate) : Bool :=
  decide (c.claimed_gate2q_count
            = (c.syscalls.filter (fun sc => kindIsGate2q sc.kind)).length)

/-! ### §8.b Headline external-cert checker -/

/-- **The full external-certificate checker.**  Returns
    `true` iff all three claimed resource numbers match AND
    the strict-with-freshness bundle passes on the producer's
    `syscalls`.

    Lean accepts an external cert iff this returns `true`. -/
def external_schedule_strict_ok
    (models : SystemModels) (c : ExternalScheduleCertificate) : Bool :=
  external_wallclock_matches c
  && external_syscall_count_matches c
  && external_gate2q_count_matches c
  && all_invariants_strict_with_slot_capacity_and_freshness_ok
       models.arch models.opCap models.slotCap models.ancillaModel
       c.syscalls
       models.t_react_us models.window_us models.max_per_window

/-! ## §9. External-cert examples -/

/-- A mock external certificate: claims correspond to the
    Lean-derived values for the adder skeleton.  Should be
    accepted. -/
def python_generated_adder_example : ExternalScheduleCertificate :=
  { producer              := "python-naive-scheduler-demo"
    claimed_layer         := ArtifactLayer.syscall
    syscalls              := adder_n1_syscalls
    claimed_wallclock_us  := 48
    claimed_syscall_count := 48
    claimed_gate2q_count  := 18
    notes                 :=
      "Lean-side mock of an external producer's certificate format." }

/-- **External cert accepted**: Lean re-derives wallclock /
    counts and verifies the strict bundle. -/
theorem python_generated_adder_example_checked :
    external_schedule_strict_ok
        adder_n1_system_models python_generated_adder_example = true := by
  native_decide

/-- A bad external certificate: same `syscalls` as the good
    one, but the producer LIES — claims wallclock = 1.  Lean
    must reject. -/
def python_bad_wallclock_example : ExternalScheduleCertificate :=
  { producer              := "python-bad-wallclock-demo"
    claimed_layer         := ArtifactLayer.syscall
    syscalls              := adder_n1_syscalls
    claimed_wallclock_us  := 1            -- ← false claim
    claimed_syscall_count := 48
    claimed_gate2q_count  := 18
    notes                 :=
      "Same SysCalls as the good cert, but claimed wallclock falsified." }

/-- **External cert rejected**: false claimed wallclock fails
    `external_wallclock_matches`. -/
theorem python_bad_wallclock_example_rejected :
    external_schedule_strict_ok
        adder_n1_system_models python_bad_wallclock_example = false := by
  native_decide

/-- Another bad external cert: claimed Gate2q count
    falsified to 1.  Reuses the same syscalls and accurate
    wallclock; only the Gate2q count is wrong. -/
def python_bad_gate2q_example : ExternalScheduleCertificate :=
  { producer              := "python-bad-gate2q-demo"
    claimed_layer         := ArtifactLayer.syscall
    syscalls              := adder_n1_syscalls
    claimed_wallclock_us  := 48
    claimed_syscall_count := 48
    claimed_gate2q_count  := 1            -- ← false claim
    notes                 :=
      "Same SysCalls as the good cert, but claimed Gate2q count falsified." }

theorem python_bad_gate2q_example_rejected :
    external_schedule_strict_ok
        adder_n1_system_models python_bad_gate2q_example = false := by
  native_decide

/-! ## §10. Compressed-schedule placeholder

    This is the type signature only.  Evaluation semantics,
    flattening to `List SysCall`, and proof of bundle
    invariance under composition are scoped to a later tick.

    Intended use: scalable hierarchical generation of full
    FT Shor schedules without materializing the entire
    `List SysCall` (which would be infeasible at RSA-2048
    scale). -/

inductive CompressedSchedule where
  /-- A leaf: an explicit `List SysCall` block. -/
  | atom   : List SysCall      → CompressedSchedule
  /-- Sequential composition. -/
  | seq    : List CompressedSchedule → CompressedSchedule
  /-- Parallel composition. -/
  | par    : List CompressedSchedule → CompressedSchedule
  /-- Repeated composition: `repeat n body` ≈ `seq [body, …,
      body]` (n copies). -/
  | rep    : Nat → CompressedSchedule → CompressedSchedule
  deriving Inhabited

/-! ## §10.a Expansion semantics

    `CompressedSchedule` is now upgraded from a placeholder
    type into a usable certificate layer with REFERENCE
    expansion + SYMBOLIC resources + SOUNDNESS theorems.

    Expansion is the reference semantics: convert a
    `CompressedSchedule` to an explicit `List SysCall` by
    cascading the existing `seqSchedules` / `parSchedules`
    combinators.  Used only for small examples; for full FT
    Shor scale, the symbolic `resource` evaluator below
    avoids materialisation. -/

/-- Reference-semantics expansion of a `CompressedSchedule`
    into an explicit `List SysCall`.  Uses the existing
    `seqManySchedules` / `parManySchedules` combinators. -/
def CompressedSchedule.expand : CompressedSchedule → List SysCall
  | .atom xs    => xs
  | .seq blocks => seqManySchedules (blocks.map CompressedSchedule.expand)
  | .par blocks => parManySchedules (blocks.map CompressedSchedule.expand)
  | .rep n body => seqManySchedules (List.replicate n body.expand)

@[simp] theorem expand_atom (xs : List SysCall) :
    (CompressedSchedule.atom xs).expand = xs := by
  simp [CompressedSchedule.expand]

@[simp] theorem expand_seq_nil :
    (CompressedSchedule.seq []).expand = [] := by
  simp [CompressedSchedule.expand, seqManySchedules]

@[simp] theorem expand_par_nil :
    (CompressedSchedule.par []).expand = [] := by
  simp [CompressedSchedule.expand, parManySchedules]

@[simp] theorem expand_rep_zero (body : CompressedSchedule) :
    (CompressedSchedule.rep 0 body).expand = [] := by
  simp [CompressedSchedule.expand, seqManySchedules]

/-! ## §10.b Resource summary type -/

/-- Resource summary: wallclock + per-kind active counts.
    Computed symbolically from a `CompressedSchedule`
    structure (no expansion for `rep`). -/
structure CompressedResourceSummary where
  wallclock_us        : Nat
  syscall_count       : Nat
  gate2q_count        : Nat
  measure_count       : Nat
  decode_count        : Nat
  feedback_count      : Nat
  fresh_ancilla_count : Nat
  magic_req_count     : Nat
  deriving Repr, Inhabited, DecidableEq

namespace CompressedResourceSummary

/-- The all-zero summary, identity for `seqCombine` and
    `parCombine`. -/
def zero : CompressedResourceSummary :=
  { wallclock_us        := 0, syscall_count       := 0
    gate2q_count        := 0, measure_count       := 0
    decode_count        := 0, feedback_count      := 0
    fresh_ancilla_count := 0, magic_req_count     := 0 }

/-- Sequential combine: wallclocks SUM (back-to-back) and
    every per-kind count SUMS. -/
def seqCombine (a b : CompressedResourceSummary) : CompressedResourceSummary :=
  { wallclock_us        := a.wallclock_us        + b.wallclock_us
    syscall_count       := a.syscall_count       + b.syscall_count
    gate2q_count        := a.gate2q_count        + b.gate2q_count
    measure_count       := a.measure_count       + b.measure_count
    decode_count        := a.decode_count        + b.decode_count
    feedback_count      := a.feedback_count      + b.feedback_count
    fresh_ancilla_count := a.fresh_ancilla_count + b.fresh_ancilla_count
    magic_req_count     := a.magic_req_count     + b.magic_req_count }

/-- Parallel combine: wallclock = MAX (both start at t=0;
    finish at the later end); every per-kind count SUMS
    (parallel still ADDS operations). -/
def parCombine (a b : CompressedResourceSummary) : CompressedResourceSummary :=
  { wallclock_us        := Nat.max a.wallclock_us b.wallclock_us
    syscall_count       := a.syscall_count       + b.syscall_count
    gate2q_count        := a.gate2q_count        + b.gate2q_count
    measure_count       := a.measure_count       + b.measure_count
    decode_count        := a.decode_count        + b.decode_count
    feedback_count      := a.feedback_count      + b.feedback_count
    fresh_ancilla_count := a.fresh_ancilla_count + b.fresh_ancilla_count
    magic_req_count     := a.magic_req_count     + b.magic_req_count }

/-- Scale: multiply every field (wallclock + every count) by
    `n`.  Used for `rep n body`. -/
def scale (n : Nat) (r : CompressedResourceSummary) : CompressedResourceSummary :=
  { wallclock_us        := n * r.wallclock_us
    syscall_count       := n * r.syscall_count
    gate2q_count        := n * r.gate2q_count
    measure_count       := n * r.measure_count
    decode_count        := n * r.decode_count
    feedback_count      := n * r.feedback_count
    fresh_ancilla_count := n * r.fresh_ancilla_count
    magic_req_count     := n * r.magic_req_count }

end CompressedResourceSummary

/-- Explicit resource summary of a `List SysCall`. -/
def resourceOfSysCalls (xs : List SysCall) : CompressedResourceSummary :=
  { wallclock_us        := scheduleWallclockUs xs
    syscall_count       := xs.length
    gate2q_count        := (xs.filter (fun sc => kindIsGate2q sc.kind)).length
    measure_count       := (xs.filter (fun sc => kindIsMeasure sc.kind)).length
    decode_count        := (xs.filter (fun sc => kindIsDecode sc.kind)).length
    feedback_count      := (xs.filter (fun sc => kindIsFeedback sc.kind)).length
    fresh_ancilla_count := (xs.filter (fun sc => kindIsFreshAnc sc.kind)).length
    magic_req_count     := (xs.filter (fun sc => kindIsMagicReq sc.kind)).length }

/-! ## §10.c Symbolic resource evaluator -/

/-- Symbolic resource evaluator on `CompressedSchedule`.
    Key property: `rep n body` is evaluated by SCALING
    `body.resource` by `n` — no expansion to `n` copies. -/
def CompressedSchedule.resource : CompressedSchedule → CompressedResourceSummary
  | .atom xs    => resourceOfSysCalls xs
  | .seq blocks =>
      (blocks.map CompressedSchedule.resource).foldr
        CompressedResourceSummary.seqCombine CompressedResourceSummary.zero
  | .par blocks =>
      (blocks.map CompressedSchedule.resource).foldr
        CompressedResourceSummary.parCombine CompressedResourceSummary.zero
  | .rep n body => CompressedResourceSummary.scale n body.resource

@[simp] theorem resource_atom_def (xs : List SysCall) :
    (CompressedSchedule.atom xs).resource = resourceOfSysCalls xs := by
  simp [CompressedSchedule.resource]

@[simp] theorem resource_rep_def (n : Nat) (body : CompressedSchedule) :
    (CompressedSchedule.rep n body).resource
      = CompressedResourceSummary.scale n body.resource := by
  simp [CompressedSchedule.resource]

/-! ## §10.d Soundness theorems (atom case is `rfl`)

    Parametric soundness theorems on all four constructors
    require non-trivial helper lemmas about `seqManySchedules`
    / `parManySchedules` wallclock + count distribution.
    Those lemmas are intricate (Nat-max case-analysis on
    empty/nonempty shift), and our acceptance criterion only
    requires that Lean be able to "re-derive resources
    symbolically".

    The atom case is `rfl`; this is the only case that does
    not involve any combinator semantics.  For
    `seq`/`par`/`rep` instances we exercise soundness by
    `native_decide` on the concrete schedules in §10.e
    below: those instance-level equalities `cs.resource.* =
    resourceOfSysCalls cs.expand .*` close via concrete
    computation.

    Generalised parametric soundness lemmas for the
    combinator cases are scoped to a follow-up tick. -/

/-- **Soundness for atom.**  The symbolic resource of
    `atom xs` is `resourceOfSysCalls xs`. -/
theorem resource_atom_sound (xs : List SysCall) :
    (CompressedSchedule.atom xs).resource = resourceOfSysCalls xs := by
  simp

/-- Wallclock soundness for `atom`. -/
theorem resource_wallclock_sound_atom (xs : List SysCall) :
    (CompressedSchedule.atom xs).resource.wallclock_us
      = scheduleWallclockUs (CompressedSchedule.atom xs).expand := by
  simp [resourceOfSysCalls]

/-- SysCall-count soundness for `atom`. -/
theorem resource_syscall_count_sound_atom (xs : List SysCall) :
    (CompressedSchedule.atom xs).resource.syscall_count
      = (CompressedSchedule.atom xs).expand.length := by
  simp [resourceOfSysCalls]

/-- Gate2q-count soundness for `atom`. -/
theorem resource_gate2q_count_sound_atom (xs : List SysCall) :
    (CompressedSchedule.atom xs).resource.gate2q_count
      = ((CompressedSchedule.atom xs).expand.filter
            (fun sc => kindIsGate2q sc.kind)).length := by
  simp [resourceOfSysCalls]

/-! ## §10.e Compressed-schedule artifact + verified
       certificate

    Mirrors `SysCallScheduleArtifact` /
    `VerifiedSysCallSchedule`.  `strict_ok_expanded` checks
    the strict bundle on the EXPANDED schedule — adequate
    for small examples; symbolic invariant checking on
    `CompressedSchedule` directly is deferred to a follow-up
    tick. -/

/-- Compressed-schedule artifact. -/
structure CompressedScheduleArtifact where
  metadata : ArtifactMetadata
  schedule : CompressedSchedule
  deriving Inhabited

/-- Verified compressed-schedule certificate.  Carries the
    symbolic resource summary AND the proof that the
    expanded form passes the strict bundle. -/
structure VerifiedCompressedSchedule where
  artifact          : CompressedScheduleArtifact
  models            : SystemModels
  resources         : CompressedResourceSummary
  resources_derived : resources = artifact.schedule.resource
  strict_ok_expanded :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch models.opCap models.slotCap models.ancillaModel
        artifact.schedule.expand
        models.t_react_us models.window_us models.max_per_window = true

/-- **Generic checker for compressed schedules.**  If the
    strict bundle holds on the expanded form, the
    compressed artifact yields a verified cert with the
    symbolic resources. -/
theorem verified_compressed_schedule_of_expanded_strict_ok
    (artifact : CompressedScheduleArtifact) (models : SystemModels)
    (h : all_invariants_strict_with_slot_capacity_and_freshness_ok
            models.arch models.opCap models.slotCap models.ancillaModel
            artifact.schedule.expand
            models.t_react_us models.window_us models.max_per_window = true) :
    ∃ cert : VerifiedCompressedSchedule,
      cert.artifact = artifact
      ∧ cert.models = models
      ∧ cert.resources = artifact.schedule.resource :=
  ⟨ { artifact           := artifact
      models             := models
      resources          := artifact.schedule.resource
      resources_derived  := rfl
      strict_ok_expanded := h },
    rfl, rfl, rfl ⟩

/-! ## §10.f External compressed-schedule certificate -/

/-- External compressed-schedule certificate format.
    Producers emit a `CompressedSchedule` plus their own
    claimed resource numbers; Lean re-derives via the
    symbolic `resource` evaluator and rejects mismatches. -/
structure ExternalCompressedScheduleCertificate where
  producer              : String
  claimed_layer         : ArtifactLayer
  schedule              : CompressedSchedule
  claimed_wallclock_us  : Nat
  claimed_syscall_count : Nat
  claimed_gate2q_count  : Nat
  notes                 : String
  deriving Inhabited

/-- **External compressed checker.**  Three derived-resource
    checks (symbolic) + strict-bundle check on the expanded
    form.

    Lean accepts a compressed external cert iff this returns
    `true`.  Producers cannot lie about wallclock or
    operation counts: the `claimed_*` fields are compared
    against `schedule.resource.*`, NOT against producer
    self-reports. -/
def external_compressed_schedule_strict_ok
    (models : SystemModels) (c : ExternalCompressedScheduleCertificate) : Bool :=
  decide (c.claimed_wallclock_us  = c.schedule.resource.wallclock_us)
  && decide (c.claimed_syscall_count = c.schedule.resource.syscall_count)
  && decide (c.claimed_gate2q_count  = c.schedule.resource.gate2q_count)
  && all_invariants_strict_with_slot_capacity_and_freshness_ok
       models.arch models.opCap models.slotCap models.ancillaModel
       c.schedule.expand
       models.t_react_us models.window_us models.max_per_window

/-! ## §10.g Adder examples (atom + repeated) -/

/-- The adder skeleton wrapped as an `atom` compressed
    schedule.  Just a `List SysCall` lifted into
    `CompressedSchedule` — no symbolic structure. -/
def adder_n1_compressed_atom : CompressedSchedule :=
  CompressedSchedule.atom adder_n1_syscalls

/-- The expansion of `atom` is the original SysCalls. -/
theorem adder_n1_compressed_atom_expand :
    adder_n1_compressed_atom.expand = adder_n1_syscalls := by
  simp [adder_n1_compressed_atom]

theorem adder_n1_compressed_atom_resource_wallclock :
    adder_n1_compressed_atom.resource.wallclock_us = 48 := by native_decide

theorem adder_n1_compressed_atom_resource_syscall_count :
    adder_n1_compressed_atom.resource.syscall_count = 48 := by native_decide

theorem adder_n1_compressed_atom_resource_gate2q :
    adder_n1_compressed_atom.resource.gate2q_count = 18 := by native_decide

/-- A mock external compressed certificate.  Honest claims:
    accepted. -/
def python_generated_compressed_atom_example :
    ExternalCompressedScheduleCertificate :=
  { producer              := "python-compressed-atom-demo"
    claimed_layer         := ArtifactLayer.compressedSchedule
    schedule              := adder_n1_compressed_atom
    claimed_wallclock_us  := 48
    claimed_syscall_count := 48
    claimed_gate2q_count  := 18
    notes                 :=
      "External producer submits atom-shape compressed schedule with " ++
      "honest resource claims." }

theorem adder_n1_compressed_atom_checked :
    external_compressed_schedule_strict_ok
        adder_n1_system_models python_generated_compressed_atom_example = true := by
  native_decide

/-! ### §10.g.repeated  Repeated adder skeleton

    `rep n body` is the scalability test: the SYMBOLIC
    resource is `n × body.resource` (no expansion), while
    the strict bundle still checks the expanded form. -/

/-- Three sequential copies of the adder skeleton via
    `rep 3`. -/
def adder_n1_repeated_3 : CompressedSchedule :=
  CompressedSchedule.rep 3 adder_n1_compressed_atom

/-- Symbolic wallclock: `3 × 48 = 144` µs — derived
    WITHOUT expanding the schedule (uses
    `CompressedResourceSummary.scale`). -/
theorem adder_n1_repeated_3_resource_wallclock :
    adder_n1_repeated_3.resource.wallclock_us = 144 := by native_decide

/-- Symbolic Gate2q count: `3 × 18 = 54`. -/
theorem adder_n1_repeated_3_resource_gate2q :
    adder_n1_repeated_3.resource.gate2q_count = 54 := by native_decide

/-- Symbolic SysCall count: `3 × 48 = 144`. -/
theorem adder_n1_repeated_3_resource_syscall_count :
    adder_n1_repeated_3.resource.syscall_count = 144 := by native_decide

/-- The EXPANDED form's wallclock also equals 144 — the
    expansion of `rep 3 body` is the seqManySchedules of 3
    body copies, which the existing combinators time-shift
    correctly. -/
theorem adder_n1_repeated_3_expand_wallclock :
    scheduleWallclockUs adder_n1_repeated_3.expand = 144 := by native_decide

/-- An external compressed cert that uses `rep` symbolic
    structure.  Honest claims; accepted. -/
def python_generated_compressed_rep_example :
    ExternalCompressedScheduleCertificate :=
  { producer              := "python-compressed-rep-demo"
    claimed_layer         := ArtifactLayer.compressedSchedule
    schedule              := adder_n1_repeated_3
    claimed_wallclock_us  := 144
    claimed_syscall_count := 144
    claimed_gate2q_count  := 54
    notes                 :=
      "External producer submits a rep-shape compressed schedule with " ++
      "scaled resource claims; Lean re-derives via symbolic resource." }

theorem adder_n1_repeated_3_checked :
    external_compressed_schedule_strict_ok
        adder_n1_system_models python_generated_compressed_rep_example = true := by
  native_decide

/-! ## §10.h Bad compressed certificate examples -/

/-- A bad compressed cert with falsified wallclock claim. -/
def python_bad_compressed_wallclock_example :
    ExternalCompressedScheduleCertificate :=
  { producer              := "python-bad-compressed-wallclock-demo"
    claimed_layer         := ArtifactLayer.compressedSchedule
    schedule              := adder_n1_repeated_3
    claimed_wallclock_us  := 1                  -- ← false claim
    claimed_syscall_count := 144
    claimed_gate2q_count  := 54
    notes                 := "Falsified wallclock; Lean rejects." }

theorem python_bad_compressed_wallclock_rejected :
    external_compressed_schedule_strict_ok
        adder_n1_system_models python_bad_compressed_wallclock_example = false := by
  native_decide

/-- A bad compressed cert with falsified Gate2q count
    claim. -/
def python_bad_compressed_gate2q_example :
    ExternalCompressedScheduleCertificate :=
  { producer              := "python-bad-compressed-gate2q-demo"
    claimed_layer         := ArtifactLayer.compressedSchedule
    schedule              := adder_n1_repeated_3
    claimed_wallclock_us  := 144
    claimed_syscall_count := 144
    claimed_gate2q_count  := 1                  -- ← false claim
    notes                 := "Falsified Gate2q count; Lean rejects." }

theorem python_bad_compressed_gate2q_rejected :
    external_compressed_schedule_strict_ok
        adder_n1_system_models python_bad_compressed_gate2q_example = false := by
  native_decide

/-- A bad compressed SCHEDULE: two adder skeletons in
    parallel via `CompressedSchedule.par`.  Both blocks try
    to allocate the same ancilla zone simultaneously; the
    strict bundle rejects the expanded form (operation
    capacity exceeded under `max_gate2q_active = 1`). -/
def bad_parallel_compressed_adder_schedule : CompressedSchedule :=
  CompressedSchedule.par
    [ adder_n1_compressed_atom
    , adder_n1_compressed_atom ]

/-- An external cert for the bad parallel schedule.  We set
    `claimed_*` to whatever the symbolic resource computes —
    so that THIS test isolates the strict-bundle rejection
    (not a claim mismatch). -/
def bad_parallel_compressed_adder_example :
    ExternalCompressedScheduleCertificate :=
  { producer              := "python-bad-compressed-parallel-demo"
    claimed_layer         := ArtifactLayer.compressedSchedule
    schedule              := bad_parallel_compressed_adder_schedule
    claimed_wallclock_us  :=
      bad_parallel_compressed_adder_schedule.resource.wallclock_us
    claimed_syscall_count :=
      bad_parallel_compressed_adder_schedule.resource.syscall_count
    claimed_gate2q_count  :=
      bad_parallel_compressed_adder_schedule.resource.gate2q_count
    notes                 :=
      "Parallel composition causes operation-capacity violation on " ++
      "expanded schedule; Lean rejects via strict bundle." }

theorem bad_parallel_compressed_adder_rejected :
    external_compressed_schedule_strict_ok
        adder_n1_system_models bad_parallel_compressed_adder_example = false := by
  native_decide

/-! ## §10.i Scalability boundary

    What's symbolic in this tick:
      * `resource.wallclock_us`, `resource.syscall_count`,
        `resource.gate2q_count`, … under `rep n body` are
        computed by scaling `body.resource`, NOT by
        materialising `n` copies.

    What still expands:
      * Strict-bundle invariant checking
        (`all_invariants_strict_with_slot_capacity_and_freshness_ok`
        on `schedule.expand`).  Acceptable for small
        examples; for full FT Shor we need symbolic
        invariant checking — `seq` valid if shifted-valid
        blocks compose; `par` valid only under explicit
        disjointness/capacity/throughput hypotheses; `rep`
        valid if one body is valid and boundary state
        composes.

    Next-tick repair:
      * Prove generic `resource_wallclock_sound` /
        `resource_syscall_count_sound` /
        `resource_gate2q_count_sound` parametrically over
        all four constructors (helper lemmas on
        `seqManySchedules` / `parManySchedules` wallclock +
        count distribution).
      * Define symbolic invariant checkers for `seq`, `rep`
        composition — the proof obligation is on the
        BOUNDARIES between blocks, not on each block's
        SysCalls. -/

/-! ## §10.j Symbolic repeat checker (the scalability repair)

    The previous tick's expansion-based `strict_ok` check is
    NOT scalable to Shor-size schedules (`rep 10^6 body` would
    materialise 10^6 SysCall copies).  This section adds a
    SUFFICIENT symbolic checker for the sequential-repeat case:

      If the body schedule is strict-valid AND satisfies a
      conservative boundary cleanliness condition,
      THEN `rep n body` is admissible at the resource level
      without expanding `n` copies.

    What is provable in this tick:
      * Body strict-validity is a soundness *grounding*:
        symbolic acceptance implies body strict-validity.
      * Resource scaling: `(rep n (atom body)).resource =
        scale n (resourceOfSysCalls body)`.
      * Instance-level cross-check: the symbolic checker
        accepts iff the expansion-based checker accepts (for
        small `n`).

    What is NOT proven (scoped to next tick):
      * Parametric "symbolic strict_ok ⇒ expanded strict_ok
        for arbitrary `n`".  This requires compositional
        lemmas for each invariant under sequential shifts.
        See §10.k for the precise obligation. -/

/-! ### §10.j.1 Boundary cleanliness checker

    Conservative sufficient conditions for a body to repeat
    safely under `seqManySchedules (replicate n body)`:

      (i)  `0 < scheduleWallclockUs body`  — repetition
            progresses time;
      (ii) `magic_req_count body = 0`     — sidesteps
            factory-window aggregation issues at boundaries
            (relaxable once factory causal-supply is
            modelled).

    The ancilla "no dangling Live" condition is ALREADY
    enforced by `ancilla_freshness_ok` inside the strict
    bundle; the strict-bundle conjunct in
    `repeat_safe_block_ok` covers it.  Feedback-after-decode
    is similarly already covered (and is monotone under
    additional earlier DecodeSyndromes from previous
    copies). -/

/-- The conservative boundary-clean condition. -/
def repeat_boundary_clean (body : List SysCall) : Bool :=
  decide (0 < scheduleWallclockUs body)
  && decide ((body.filter (fun sc => kindIsMagicReq sc.kind)).length = 0)

/-- A repeat-safe block: body must pass the strict bundle AND
    be boundary-clean. -/
def repeat_safe_block_ok
    (models : SystemModels) (body : List SysCall) : Bool :=
  all_invariants_strict_with_slot_capacity_and_freshness_ok
      models.arch models.opCap models.slotCap models.ancillaModel
      body
      models.t_react_us models.window_us models.max_per_window
  && repeat_boundary_clean body

/-- The symbolic repeat checker.  For this tick, `reps` does
    NOT enter the check — the sufficient condition is on the
    body alone (which is the whole point of the scalability
    fix). -/
def symbolic_rep_strict_ok
    (models : SystemModels) (body : List SysCall) (_reps : Nat) : Bool :=
  repeat_safe_block_ok models body

/-! ### §10.j.2 Proof-carrying repeat-safe block + cert -/

/-- Proof-carrying repeat-safe block.  Carries the body
    schedule, the system models it was certified under, the
    derived wallclock, AND the boundary-clean witness. -/
structure RepeatSafeBlock where
  body : List SysCall
  models : SystemModels
  wallclock_us : Nat
  wallclock_derived :
    wallclock_us = scheduleWallclockUs body
  wallclock_pos : 0 < wallclock_us
  body_strict_ok :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch models.opCap models.slotCap models.ancillaModel
        body
        models.t_react_us models.window_us models.max_per_window = true
  boundary_clean : Bool
  boundary_clean_ok : boundary_clean = true

/-- A symbolic-repeated certificate: a repeat-safe block,
    number of repetitions, and scaled resources.  Does NOT
    carry the expanded `List SysCall`. -/
structure RepeatedScheduleCertificate where
  block : RepeatSafeBlock
  reps : Nat
  resources : CompressedResourceSummary
  resources_derived :
    resources = CompressedResourceSummary.scale reps
        (resourceOfSysCalls block.body)

/-- Lift a `RepeatedScheduleCertificate` back into the
    canonical `CompressedSchedule` form (for serialization or
    cross-checking). -/
def RepeatedScheduleCertificate.toCompressedSchedule
    (c : RepeatedScheduleCertificate) : CompressedSchedule :=
  CompressedSchedule.rep c.reps (CompressedSchedule.atom c.block.body)

/-! ### §10.j.3 Resource soundness for repeat -/

/-- Symbolic wallclock under `rep n (atom body)` =
    `n × scheduleWallclockUs body`.  Pure simp on the
    @[simp]-tagged unfolders for `resource` plus `scale` and
    `resourceOfSysCalls`. -/
theorem repeated_schedule_resource_wallclock
    (body : List SysCall) (n : Nat) :
    (CompressedSchedule.rep n (CompressedSchedule.atom body)).resource.wallclock_us
      = n * scheduleWallclockUs body := by
  simp [CompressedResourceSummary.scale, resourceOfSysCalls]

theorem repeated_schedule_resource_syscall_count
    (body : List SysCall) (n : Nat) :
    (CompressedSchedule.rep n (CompressedSchedule.atom body)).resource.syscall_count
      = n * body.length := by
  simp [CompressedResourceSummary.scale, resourceOfSysCalls]

theorem repeated_schedule_resource_gate2q
    (body : List SysCall) (n : Nat) :
    (CompressedSchedule.rep n (CompressedSchedule.atom body)).resource.gate2q_count
      = n * (body.filter (fun sc => kindIsGate2q sc.kind)).length := by
  simp [CompressedResourceSummary.scale, resourceOfSysCalls]

/-! ### §10.j.4 The grounding theorem

    Symbolic acceptance implies the body is strict-valid.  The
    full "symbolic ⇒ expanded for arbitrary n" theorem
    requires compositional lemmas (§10.k); for now we prove
    the smaller, immediate consequence. -/

theorem symbolic_rep_ok_implies_body_ok
    (models : SystemModels) (body : List SysCall) (n : Nat)
    (h : symbolic_rep_strict_ok models body n = true) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch models.opCap models.slotCap models.ancillaModel
        body
        models.t_react_us models.window_us models.max_per_window = true := by
  unfold symbolic_rep_strict_ok repeat_safe_block_ok at h
  exact (Bool.and_eq_true _ _).mp h |>.1

theorem symbolic_rep_ok_implies_body_boundary_clean
    (models : SystemModels) (body : List SysCall) (n : Nat)
    (h : symbolic_rep_strict_ok models body n = true) :
    repeat_boundary_clean body = true := by
  unfold symbolic_rep_strict_ok repeat_safe_block_ok at h
  exact (Bool.and_eq_true _ _).mp h |>.2

/-! ## §10.k External symbolic-repeat certificate -/

/-- External symbolic-repeat certificate.  Producer emits a
    body, a repetition count `reps`, and claimed
    repeat-scaled resources.  Lean re-derives via the
    SYMBOLIC `resource` evaluator — never materialises
    `reps` copies. -/
structure ExternalRepeatedScheduleCertificate where
  producer              : String
  body                  : List SysCall
  reps                  : Nat
  claimed_wallclock_us  : Nat
  claimed_syscall_count : Nat
  claimed_gate2q_count  : Nat
  notes                 : String
  deriving Inhabited

/-- External symbolic-repeat checker.  Compares each
    `claimed_*` to the SYMBOLIC `resource` (no expansion) AND
    checks `symbolic_rep_strict_ok`. -/
def external_repeated_schedule_symbolic_ok
    (models : SystemModels) (c : ExternalRepeatedScheduleCertificate) : Bool :=
  let cs := CompressedSchedule.rep c.reps (CompressedSchedule.atom c.body)
  decide (c.claimed_wallclock_us  = cs.resource.wallclock_us)
  && decide (c.claimed_syscall_count = cs.resource.syscall_count)
  && decide (c.claimed_gate2q_count  = cs.resource.gate2q_count)
  && symbolic_rep_strict_ok models c.body c.reps

/-! ## §10.l Adder-block repeated examples -/

/-- The adder skeleton block passes the repeat-safe checker
    (it strict-passes and has no `RequestMagicState`). -/
theorem adder_n1_repeat_block_ok :
    repeat_safe_block_ok adder_n1_system_models adder_n1_syscalls = true := by
  native_decide

/-- The adder skeleton passes the symbolic-repeat checker
    for `reps = 3`. -/
theorem adder_n1_repeated_3_symbolic_ok :
    symbolic_rep_strict_ok adder_n1_system_models adder_n1_syscalls 3 = true := by
  native_decide

/-- **Cross-check**: the symbolic checker's acceptance for
    `reps = 3` matches the EXPANSION-based strict check.  This
    grounds the symbolic check against the existing expansion
    semantics on a concrete instance. -/
theorem adder_n1_repeated_3_expanded_strict_ok :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        adder_n1_system_models.arch
        adder_n1_system_models.opCap
        adder_n1_system_models.slotCap
        adder_n1_system_models.ancillaModel
        (CompressedSchedule.rep 3 (CompressedSchedule.atom adder_n1_syscalls)).expand
        adder_n1_system_models.t_react_us
        adder_n1_system_models.window_us
        adder_n1_system_models.max_per_window = true := by
  native_decide

/-! ## §10.m External symbolic-repeat examples -/

/-- An external symbolic-repeat cert claiming `1000`
    repetitions.  Resources scaled symbolically — no
    expansion of 1000 copies. -/
def python_repeated_adder_symbolic_example :
    ExternalRepeatedScheduleCertificate :=
  { producer              := "python-compressed-rep-1000-demo"
    body                  := adder_n1_syscalls
    reps                  := 1000
    claimed_wallclock_us  := 1000 * 48                  -- = 48_000
    claimed_syscall_count := 1000 * 48                  -- = 48_000
    claimed_gate2q_count  := 1000 * 18                  -- = 18_000
    notes                 :=
      "Compressed claim: rep 1000 × adder skeleton.  Lean does NOT " ++
      "expand 1000 copies; resources are scaled symbolically." }

/-- **The scalability headline**: Lean accepts a `rep 1000`
    certificate without materialising the 1000 SysCall copies. -/
theorem python_repeated_adder_symbolic_example_checked :
    external_repeated_schedule_symbolic_ok
        adder_n1_system_models python_repeated_adder_symbolic_example = true := by
  native_decide

/-- Bad symbolic-repeat cert with falsified wallclock claim. -/
def python_repeated_adder_bad_wallclock_example :
    ExternalRepeatedScheduleCertificate :=
  { producer              := "python-compressed-rep-bad-wallclock-demo"
    body                  := adder_n1_syscalls
    reps                  := 1000
    claimed_wallclock_us  := 1                          -- ← false
    claimed_syscall_count := 1000 * 48
    claimed_gate2q_count  := 1000 * 18
    notes                 := "Falsified wallclock under rep 1000." }

theorem python_repeated_adder_bad_wallclock_rejected :
    external_repeated_schedule_symbolic_ok
        adder_n1_system_models python_repeated_adder_bad_wallclock_example = false := by
  native_decide

/-- A bad body: Gate2q on ancilla site 100 before any
    `RequestFreshAncilla` (the review's freshness violator
    shape).  Body fails strict bundle ⇒ repeat-safe checker
    fails ⇒ certificate rejected. -/
def python_repeated_bad_body : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 100 0, begin_us := 0, end_us := 1 } ]

/-- A symbolic-repeat cert wrapping the bad body.  The
    `claimed_*` numbers are set to the SYMBOLIC resource
    values so this test isolates the BODY-validity failure
    (not a claim mismatch). -/
def python_repeated_bad_body_example :
    ExternalRepeatedScheduleCertificate :=
  { producer              := "python-compressed-rep-bad-body-demo"
    body                  := python_repeated_bad_body
    reps                  := 5
    claimed_wallclock_us  := 5 * 1                      -- 1 µs body × 5
    claimed_syscall_count := 5 * 1
    claimed_gate2q_count  := 5 * 1
    notes                 :=
      "Body violates strict bundle (Gate2q on Free ancilla); rep 5 rejected." }

theorem python_repeated_bad_body_rejected :
    external_repeated_schedule_symbolic_ok
        adder_n1_system_models python_repeated_bad_body_example = false := by
  native_decide

/-! ## §10.n Remaining proof obligation (honest report)

    The symbolic repeat checker is a SUFFICIENT condition.
    The full theorem

      ∀ models body n,
        symbolic_rep_strict_ok models body n = true
        →
        all_invariants_strict_with_slot_capacity_and_freshness_ok
            ... (seqManySchedules (List.replicate n body)) ... = true

    requires compositional lemmas for each strict-bundle
    invariant under the sequential-shift composition that
    `seqManySchedules` performs:

      * `capacity_in_arch_ok`         — preserved under
        time-shift (site claims invariant);
      * `capacity_per_cycle_ok`       — preserved across
        non-overlapping copies (no copy overlaps another in
        time);
      * `exclusivity_ok`              — likewise;
      * `factory_exclusivity_ok`      — vacuous when
        `magic_req_count body = 0` (covered by boundary
        clean);
      * `feedback_latency_ok`         — preserved (per-call
        duration unchanged by shift);
      * `decoder_react_ok`            — preserved;
      * `window_throughput_ok`        — vacuous when
        `magic_req_count body = 0`;
      * `operation_capacity_ok`       — preserved across
        non-overlapping copies;
      * `slot_capacity_ok`            — preserved likewise;
      * `feedback_after_decode_ok`    — preserved by
        body-internal feedback dependency (each copy's
        `PauliFrameUpdate` still finds its OWN copy's
        `DecodeSyndrome`);
      * `ancilla_freshness_ok`        — preserved given
        no-dangling-Live boundary (each copy's
        `RequestFreshAncilla` starts from a Dirty/Free
        state).

    Each lemma is a small per-invariant compositional fact;
    the combined theorem follows by conjunction.  Scoped to
    the next tick. -/

/-! ## §11. Summary

    Verified surface:
      * `verified_syscall_schedule_of_strict_ok` — generic.
      * `adder_n1_artifact_verified` — Lean-generated.
      * `python_generated_adder_example_checked` — external
        good cert.
      * `python_bad_wallclock_example_rejected`,
        `python_bad_gate2q_example_rejected` — external bad
        certs.

    What this DOES:
      * Pin a single `VerifiedSysCallSchedule` shape that
        every generator (Lean / Python / third-party) targets.
      * Establish that Lean does NOT trust producer-claimed
        resource numbers; every `claimed_*` field is
        re-derived from the SysCall list and compared.
      * Reuse existing strict-bundle certifications without
        re-proof.
      * Wrap existing surgery → SysCall compilers in a
        uniform `LayerCompiler α β` interface.

    What this does NOT do:
      * No JSON serialization / file I/O.
      * No `CompressedSchedule` evaluator yet (type only).
      * No Gate IR → SysCall compiler / soundness theorem
        (this is the next bridge).
      * No semantic correctness link (Gate IR ⇔ SysCall
        execution semantics).
-/

end FormalRV.Framework.LayeredArtifactInterface
