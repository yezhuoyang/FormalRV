/-
  FormalRV.Framework.LayeredPPMQECInterface — the first
  clean interface connecting the PPM/QEC LOGICAL layer to the
  existing backend compressed-schedule certificate, without
  falsely identifying PPM with physical SysCalls.

  ## Architectural layering (top → bottom)

      Logical Shor / arithmetic correctness
          ↓
      Logical circuit / Clifford+T
          ↓
      PPM / lattice-surgery logical-measurement layer
          ↓
      QEC gadget implementation: stabilizer rounds, decoder,
        Pauli frame
          ↓
      Backend compressed SysCall schedule
          ↓
      System resource/invariant certificate

  ## What is and is NOT inside the existing System layer

  The compressed-schedule strict certificate (closed in
  `FormalRV.System.CompressedRepeatSoundness`) is a
  backend resource/scheduling proof: it speaks about
  `List SysCall`, physical site claims, factory ports, decoder
  service times, slot capacities, ancilla freshness, and
  per-cycle invariants.  It is NOT the PPM semantic layer.

  PPM and QEC live ABOVE the backend system layer.  This file
  introduces the FIRST layered interface:

    * `PPMSpec` — abstract logical-measurement spec.
    * `QECGadgetSpec` — abstract QEC-gadget spec wrapping a
      `PPMSpec`.
    * `PPMToSystemLoweringCertificate` — pairs a PPM/QEC
      semantic obligation (carried as a `Prop` placeholder)
      with a backend compressed-schedule strict certificate.
    * `VerifiedBackendBlock` — a packaged backend block that
      satisfies the strict system bundle on its expansion.
    * `VerifiedPPMBlock` — a packaged PPM/QEC block that
      EXPOSES (but does not yet prove) the semantic obligation
      AND inherits backend system-correctness from its
      `VerifiedBackendBlock`.
    * `ShorResourceVerificationInterface` — a top-level
      skeleton for end-to-end Shor resource verification.

  ## Out of scope for this tick

  * Parallel composition soundness for `.par`.
  * Full PPM semantics proof (`semantic_ok` is a placeholder).
  * QEC decoder correctness or syndrome consistency.
  * Hardware-specific routing (neutral-atom moves,
    superconducting microwave control, ion-trap shuttling).
  * Shor top-level theorem.

  Neutral-atom and superconducting backends will instantiate
  the backend `SystemModels` differently, but they share this
  interface.
-/

import FormalRV.System.Artifacts.CompressedRepeatSoundness
import FormalRV.Framework.L4_QECCode
import FormalRV.Framework.L3_PPM
import FormalRV.PPM.Syntax.PauliOps

namespace FormalRV.Framework.LayeredPPMQECInterface

open FormalRV.Framework
open FormalRV.System.CompressedRepeatSoundness
open FormalRV.System.LayeredArtifactInterface
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.Architecture

/-! ## Reuse policy

    This file is an INTEGRATION BOUNDARY, not a replacement
    for the existing PPM/QEC code.  Existing definitions in
    `FormalRV.Framework.{L3_PPM, L4_QECCode, PauliOps,
    CodedLayout, MultiQubitPPM, PPMOperational,
    PauliSemantics, ...}` flow in through `open` /
    type-aliases / structure-field reuse.

    Refactored types in this tick:

    * `PPMSpec.measuredPauliKind : PauliKind`  — reuses the
      existing `FormalRV.System.Architecture.PauliKind`
      I/X/Y/Z type from `PauliOps.lean`.
    * `QECGadgetSpec.code : QECCode`           — reuses the
      existing `FormalRV.Framework.QECCode` from
      `L4_QECCode.lean` (parity-check matrices + `[[n, k, d]]`
      code parameters).
    * `QECGadgetSpec.gadget : PPMGadget`       — reuses the
      existing `FormalRV.Framework.PPMGadget` from
      `L3_PPM.lean` (operator weight + per-measurement cycle
      cost `tau_s`).

    Reused as type-aliases / `abbrev`s (deferred direct reuse):

    * `LogicalQubitId := Nat`   — matches the existing
      `LogicalQubitBinding.logical_id : Nat` convention in
      `CodedLayout.lean`.
    * `LogicalPatchId := Nat`   — matches the existing
      `CodeBlockBinding.block_id : Nat` convention.
    * `PhysicalSiteId := Nat`   — matches the existing
      `physical_qubits : List Nat` convention.
    * `DecoderId := Nat`        — no existing decoder type;
      a future tick can refine to a `DecoderSpec` structure.
    * `FactoryPortId := Nat`    — matches the existing
      `RequestMagicState`-zone convention.

    Existing definitions NOT YET integrated (deferred):

    * `PauliString` — both
      `FormalRV.System.Architecture.PauliString` (list
      of `PauliFactor`) and `FormalRV.Framework.PauliSem.PauliString`
      (phase + ops list) exist.  Today's `PPMSpec` carries
      only the Pauli KIND of the measurement (X / Z), not the
      full physical string.  A future tick can add an
      `expectedPhysicalPauli : PauliString` field if needed.
    * `CodedLogicalLayout` / `CodeBlockBinding` /
      `LogicalQubitBinding` — these belong on the LOWERING
      side of the interface (mapping logical qubits to
      physical-site lists), to be wired in when
      `PPMToSystemLoweringCertificate.semantic_ok` is refined
      to a concrete relation.
    * `JointPauliMeasurementClaim` — useful when the PPM
      measures a multi-qubit Pauli product, can be added as
      an optional field.
    * `PPMOperational.StabilizerState`,
      `PauliSemantics` Pauli/Phase machinery — these
      formalise PPM operational semantics; they will be
      consumed by the future `semantic_ok` refinement, not by
      this tick. -/

/-! ## §1. Abstraction-level identifiers.

    Lightweight `abbrev`s.  Where a refined type exists in
    the existing code, the alias is kept `Nat` for backwards
    compatibility; the named alias still flags intent at the
    PPM/QEC interface. -/

/-- Identifier for a logical qubit.  Aligned with
    `LogicalQubitBinding.logical_id : Nat` in
    `CodedLayout.lean`. -/
abbrev LogicalQubitId := Nat

/-- Identifier for a logical-qubit patch (a `CodeBlockBinding`
    in the existing code, identified by its `block_id : Nat`). -/
abbrev LogicalPatchId := Nat

/-- Identifier for a physical site (atom / qubit / cell) in
    the backend.  Aligned with the existing
    `physical_qubits : List Nat` convention. -/
abbrev PhysicalSiteId := Nat

/-- Identifier for a decoder instance.  No existing decoder
    structure; a future tick can refine this to a
    `DecoderSpec`. -/
abbrev DecoderId := Nat

/-- Identifier for a factory-output port.  Aligned with the
    existing `RequestMagicState`-zone convention. -/
abbrev FactoryPortId := Nat

/-! ## §2. PPM and QEC semantic specifications.

    `PPMSpec` describes WHAT a logical measurement does;
    `QECGadgetSpec` wraps it with the existing L3 / L4
    engineering specs (`PPMGadget` + `QECCode`).

    `PPMGadget` and `QECCode` are NOT re-defined here — they
    are reused directly from `L3_PPM.lean` / `L4_QECCode.lean`. -/

/-- Abstract specification of a logical Pauli measurement
    (PPM) block.  `measuredPauliKind` reuses the existing
    `Architecture.PauliKind` (I/X/Y/Z); a future tick can
    extend to a full `PauliString`-product measurement via
    `JointPauliMeasurementClaim` from `MultiQubitPPM.lean`. -/
structure PPMSpec where
  measuredPauliKind : PauliKind
  logicalInputs     : List LogicalQubitId
  logicalOutputs    : List LogicalQubitId
  rounds            : Nat
  distance          : Nat

/-- Abstract specification of a QEC gadget implementing a
    `PPMSpec`.

    Wraps the existing L3 `PPMGadget` (operator-weight +
    `tau_s` cycle cost) and the existing L4 `QECCode`
    (parity-check matrices + `[[n, k, d]]` parameters), so
    consumers downstream of this interface can pull engineering
    cost / code parameters directly from the standard
    structures. -/
structure QECGadgetSpec where
  ppm            : PPMSpec
  /-- L4 QEC code (parity-check matrices + parameters).
      Reused from `FormalRV.Framework.L4_QECCode`. -/
  code           : QECCode
  /-- L3 PPM gadget engineering spec (operator weight +
      `tau_s` cycles per measurement).  Reused from
      `FormalRV.Framework.L3_PPM`. -/
  gadget         : PPMGadget
  syndromeRounds : Nat
  decoder        : DecoderId
  usesPauliFrame : Bool

/-! ## §2.b Adapter from existing `PauliMeasurementClaim`.

    `FormalRV.System.Architecture.PauliMeasurementClaim`
    (defined in `PauliOps.lean`) is the existing structure for
    a claimed single-logical-qubit Pauli measurement.  This
    adapter projects such a claim into the `PPMSpec` shape so
    submissions that already produce `PauliMeasurementClaim`s
    can plug into the layered interface directly.

    The adapter is minimal — extra fields (`rounds`,
    `distance`) come from the user since they live at the QEC
    engineering layer, not in `PauliMeasurementClaim`. -/

def PPMSpec.ofPauliMeasurementClaim
    (claim : PauliMeasurementClaim)
    (rounds distance : Nat) : PPMSpec :=
  { measuredPauliKind := claim.pauli_kind
    logicalInputs     := [claim.logical_id]
    logicalOutputs    := [claim.logical_id]
    rounds            := rounds
    distance          := distance }

/-- Adapter from the existing L3 `PPMGadget` + an in-flight
    `PPMSpec` into a `QECGadgetSpec`.  Hardware-generic
    `decoder` and `usesPauliFrame` are supplied by the caller. -/
def QECGadgetSpec.ofPPMGadget
    (ppm : PPMSpec) (gadget : PPMGadget)
    (syndromeRounds : Nat) (decoder : DecoderId)
    (usesPauliFrame : Bool) : QECGadgetSpec :=
  { ppm := ppm
    code := gadget.target
    gadget := gadget
    syndromeRounds := syndromeRounds
    decoder := decoder
    usesPauliFrame := usesPauliFrame }

/-! ## §3. Lowering certificate from PPM/QEC to backend
       schedule.

    The certificate pairs:
    * a PPM-level semantic obligation (`semantic_ok : Prop`),
      currently carried as an unproved placeholder;
    * a backend compressed-schedule strict certificate
      (`system_ok`), already proven via
      `compressed_schedule_strict_certificate_ok`.

    The two are kept SEPARATE on purpose: the upper-layer
    PPM/QEC correctness obligation and the lower-layer
    backend resource/scheduling obligation are different
    statements about different objects, and we must not
    conflate them.

    The `Prop` slot is a stable interface point.  A future
    tick will refine `semantic_ok` to a concrete formal
    relation (state-vector equivalence, Pauli-frame
    propagation, etc.) and require a proof; today's tick
    intentionally does not prove it. -/

structure PPMToSystemLoweringCertificate
    (models : SystemModels) where
  spec        : PPMSpec
  qec         : QECGadgetSpec
  schedule    : CompressedSchedule
  /-- Placeholder for the PPM-level semantic correctness
      statement.  NOT proved here. -/
  semantic_ok : Prop
  /-- Backend system-resource/scheduling certificate. -/
  system_ok :
    compressed_schedule_strict_certificate_ok models schedule = true

/-! ## §4. `VerifiedBackendBlock` — packaged backend block.

    A `VerifiedBackendBlock` is a `CompressedSchedule` bundled
    with its strict-certificate proof.  This is the BACKEND
    abstraction — it knows nothing about PPM/QEC. -/

structure VerifiedBackendBlock (models : SystemModels) where
  schedule : CompressedSchedule
  cert_ok  : compressed_schedule_strict_certificate_ok models schedule = true

/-- A `VerifiedBackendBlock` satisfies the strict invariant
    bundle on its expanded schedule.  Pure projection from
    `compressed_schedule_strict_soundness`. -/
theorem VerifiedBackendBlock.strict_invariants_ok
    (models : SystemModels) (b : VerifiedBackendBlock models) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch
        models.opCap
        models.slotCap
        models.ancillaModel
        b.schedule.expand
        models.t_react_us
        models.window_us
        models.max_per_window = true :=
  compressed_schedule_strict_soundness models b.schedule b.cert_ok

/-! ## §5. `VerifiedPPMBlock` — packaged PPM/QEC block.

    A `VerifiedPPMBlock` carries:
    * the PPM/QEC SPECIFICATIONS (`ppmSpec`, `qecSpec`);
    * a `VerifiedBackendBlock` (the backend implementation);
    * a placeholder Prop slot `semantic_ok` for the PPM-level
      semantic correctness obligation — NOT proved here.

    The structure DELIBERATELY separates the two obligations.
    A later tick will populate `semantic_ok` with a real
    statement and require a real proof; today's tick only
    projects backend system-correctness. -/

structure VerifiedPPMBlock (models : SystemModels) where
  ppmSpec       : PPMSpec
  qecSpec       : QECGadgetSpec
  backend       : VerifiedBackendBlock models
  /-- Placeholder for the PPM/QEC semantic correctness
      obligation.  NOT proved in this interface tick. -/
  semantic_ok   : Prop

/-- System-invariant projection: a `VerifiedPPMBlock` inherits
    backend system-correctness from its `VerifiedBackendBlock`.

    This theorem does NOT prove PPM/QEC semantic correctness —
    it merely projects the already-proved backend resource
    safety.  Semantic correctness lives in `semantic_ok` and
    must be proved separately when refined to a concrete
    statement. -/
theorem VerifiedPPMBlock.system_invariants_ok
    (models : SystemModels) (b : VerifiedPPMBlock models) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch
        models.opCap
        models.slotCap
        models.ancillaModel
        b.backend.schedule.expand
        models.t_react_us
        models.window_us
        models.max_per_window = true :=
  b.backend.strict_invariants_ok models

/-! ## §6. `ShorResourceVerificationInterface` — top-level
       end-to-end skeleton.

    A stub structure for end-to-end Shor resource
    verification.  Carries the logical-correctness statement
    (Prop placeholder), the compressed-schedule, its backend
    certificate, the resource summary (Prop placeholder), and
    the list of constituent PPM specifications.

    Intentionally NOT a theorem — this tick does not connect
    it to the Shor end-to-end correctness statement. -/

structure ShorResourceVerificationInterface
    (models : SystemModels) where
  /-- Placeholder for the logical-Shor correctness statement
      (Ekerå–Håstad post-processing, modular-exponentiation
      semantics, etc.).  NOT proved here. -/
  logical_correctness_statement : Prop
  schedule       : CompressedSchedule
  schedule_cert  :
    compressed_schedule_strict_certificate_ok models schedule = true
  /-- Placeholder for the resource summary statement
      (T-count, physical-qubit count, wallclock, decoder
      runtime, etc.).  NOT proved here. -/
  resource_summary : Prop
  ppm_blocks : List PPMSpec

/-- The backend system-resource bundle holds on a
    `ShorResourceVerificationInterface`'s schedule.  Same
    projection as `VerifiedBackendBlock.strict_invariants_ok`.

    This theorem does NOT prove logical-Shor correctness — it
    only projects backend resource safety. -/
theorem ShorResourceVerificationInterface.system_invariants_ok
    (models : SystemModels)
    (s : ShorResourceVerificationInterface models) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch
        models.opCap
        models.slotCap
        models.ancillaModel
        s.schedule.expand
        models.t_react_us
        models.window_us
        models.max_per_window = true :=
  compressed_schedule_strict_soundness models s.schedule s.schedule_cert

/-! ## §7. Layering notes (read this before adding theorems).

    The System layer is BELOW PPM.  The
    `compressed_schedule_strict_certificate_ok` theorem proves
    backend system/resource safety only.  PPM/QEC semantics
    must be proved separately and connected through a
    lowering certificate (`PPMToSystemLoweringCertificate`),
    which currently carries `semantic_ok` as an unproved
    placeholder.

    Different backends instantiate the System layer
    differently:
    * Neutral-atom: timing / shuttling / Rydberg interaction
      models.
    * Superconducting: microwave control / crosstalk /
      flux-tunability models.
    * Ion trap: shuttling / laser-time / phonon-budget models.

    Routing, crosstalk, and control-resource models are
    future BACKEND extensions, not PPM semantics.  They
    refine `SystemModels`; PPM/QEC specs are unchanged when
    the backend model is swapped. -/

end FormalRV.Framework.LayeredPPMQECInterface
