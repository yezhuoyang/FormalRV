/-
  FormalRV.System.Artifacts.LayeredArtifactCore — core layer-tag,
  artifact, and external-certificate interface (namespace
  `FormalRV.System.LayeredArtifactInterface`, shared with the
  sibling `CompressedSchedule.lean`).

  Lean is the trusted verifier: external tools (Python / Qiskit /
  third-party) may generate schedules and certificates, but every
  claimed resource number is re-derived from the SysCall list and
  re-checked by Lean.

  * `ArtifactLayer`, `ArtifactMetadata` — layer taxonomy + metadata.
  * `GateArtifact` / `SurgeryArtifact` / `SysCallScheduleArtifact`
    — layer-specific payloads.
  * `SystemModels` — the system-side parameter bundle quoted by
    every system-layer certificate.
  * `VerifiedSysCallSchedule` +
    `verified_syscall_schedule_of_strict_ok` — proof-carrying L4
    certificate and the generic checker theorem.
  * `LayerCompiler` + wrappers around the surgery → SysCall
    compilers.
  * `ExternalScheduleCertificate` + per-claim checkers and the
    `external_schedule_strict_ok` bundle, with accept/reject
    examples on the adder skeleton.

  The compressed-schedule subsystem lives in the sibling module
  `CompressedSchedule.lean` (which imports this file).  The FTQ-VM
  certificate checker (Lean-checkable certificates emitted by the
  Python discrete-event VM) will also land in this folder.
-/

import FormalRV.Core.Gate
import FormalRV.QEC.LatticeSurgery.LDPCSurgery
import FormalRV.System.Compile.SurgeryGadgetToSysCalls
import FormalRV.System.Compile.LatticeSurgeryPPMContract
import FormalRV.System.Invariants.SystemInvariantStrengthening
import FormalRV.System.Examples.AdderSystem

set_option maxRecDepth 8000

namespace FormalRV.System.LayeredArtifactInterface

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.Framework.LDPC
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.AdderSystem

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
  | compressedSchedule -- L4: hierarchical schedule (CompressedSchedule.lean)
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
  decide

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
  decide

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
  decide

end FormalRV.System.LayeredArtifactInterface
