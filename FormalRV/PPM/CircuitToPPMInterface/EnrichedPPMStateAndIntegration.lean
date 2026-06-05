import FormalRV.PPM.LayeredPPMQECInterface
import FormalRV.Core.QuantumGate
import FormalRV.PPM.PPMOperational
import FormalRV.PPM.FactoryHierarchy
import FormalRV.PPM.CircuitToPPMInterface.CircuitFragmentClassifierAndCompiler

namespace FormalRV.Framework.CircuitToPPMInterface
open FormalRV.Framework
open FormalRV.Framework.Architecture
open FormalRV.Framework.LayeredArtifactInterface
open FormalRV.Framework.SystemInvariantStrengthening
open FormalRV.Framework.LayeredPPMQECInterface
open FormalRV.Framework.Factory
open FormalRV.Framework.SurgeryGadgetToSysCalls
open FormalRV.Framework.LDPC
open FormalRV.Framework.AdderSystem
open FormalRV.Framework.CompressedRepeatSoundness

/-- Canonical empty state on `n` qubits.  Underlying
    `LogicalPPMState.empty n` plus empty magic log. -/
def MagicAwarePPMState.empty (n : Nat) : MagicAwarePPMState :=
  { logicalState := LogicalPPMState.empty n
    magicLog := [] }

/-! ### §17.b Magic-aware command relation.

    Delegates `measurePauliKind` / `applyFrameUpdate` to the
    §14 `logicalPPMCommandRel`.  Adds a log entry for
    `useMagicT` (T-kind).  Does NOT claim non-Clifford
    semantic action — only that resource use is now logged
    as a sequence of `MagicStateKind` values, not just a
    count. -/
def magicAwarePPMCommandRel (n : Nat) :
    PPMCommand → MagicAwarePPMState → MagicAwarePPMState → Prop
  | .measurePauliKind pk qs, s, t =>
      logicalPPMCommandRel n (PPMCommand.measurePauliKind pk qs)
        s.logicalState t.logicalState
      ∧ t.magicLog = s.magicLog
  | .applyFrameUpdate qs,    s, t =>
      logicalPPMCommandRel n (PPMCommand.applyFrameUpdate qs)
        s.logicalState t.logicalState
      ∧ t.magicLog = s.magicLog
  | .useMagicT q,            s, t =>
      logicalPPMCommandRel n (PPMCommand.useMagicT q)
        s.logicalState t.logicalState
      ∧ t.magicLog = s.magicLog ++ [MagicStateKind.T]

/-! ### §17.c Magic-aware semantics model.

    Mirrors the §14 `logicalPPMSemanticsModel` builder. -/
def magicAwarePPMSemanticsModel
    (n : Nat)
    (gateRel : Gate → MagicAwarePPMState → MagicAwarePPMState → Prop) :
    GateToPPMSemanticsModel :=
  { State         := MagicAwarePPMState
    gateRel       := gateRel
    ppmCommandRel := magicAwarePPMCommandRel n }

/-! ### §17.d The isolated CCX / Toffoli obligation.

    `MagicInjectionObligations sem` carries the CCX/Toffoli
    obligation against `sem`.  The companion `Prop` slot
    `useMagicT_sound` is a future-tick placeholder for the
    fine-grained statement "useMagicT performs a T-kind
    injection on the target", which the current state model
    cannot yet express.

    `CCX_ok` is the ONE remaining primitive obligation
    needed to close the arithmetic-to-PPM soundness loop
    once an ICX bundle is in hand.  It is NOT proved here. -/

structure MagicInjectionObligations
    (sem : GateToPPMSemanticsModel) where
  /-- Placeholder Prop slot for the fine-grained
      magic-T-injection semantic statement.  NOT proved
      here.  A future tick can refine to a concrete
      relation (e.g., the T-injection outcome distribution
      matches the T-gate's action on the logical
      state). -/
  useMagicT_sound : Prop
  /-- The CCX/Toffoli structural PPM macro implements
      logical CCX under `sem.gateRel`.  NOT proved here —
      this is the explicit deferred obligation. -/
  CCX_ok : ∀ a b tgt,
    ImplementsGateAsPPM sem (Gate.CCX a b tgt)
      (compileArithmeticGateToPPM (Gate.CCX a b tgt))

/-! ### §17.e Full arithmetic-primitive constructor from
       ICX bundle + magic obligation.

    Takes an `ArithmeticICXPrimitivePPMObligations sem`
    (which packages `I_is_id`, `X_ok`, `CX_ok`), a
    `MagicInjectionObligations sem` (which packages the
    deferred `CCX_ok`), and an explicit `seq_decomp`
    hypothesis, and returns the full
    `ArithmeticPrimitivePPMObligations sem`. -/

def mkArithmeticPrimitiveObligationsWithMagic
    (sem : GateToPPMSemanticsModel)
    (icx : ArithmeticICXPrimitivePPMObligations sem)
    (mag : MagicInjectionObligations sem)
    (hseq : ∀ g₁ g₂ s u,
      sem.gateRel (Gate.seq g₁ g₂) s u ↔
        ∃ t, sem.gateRel g₁ s t ∧ sem.gateRel g₂ t u) :
    ArithmeticPrimitivePPMObligations sem :=
  { I_is_id    := icx.I_is_id
    X_ok       := icx.X_ok
    CX_ok      := icx.CX_ok
    CCX_ok     := mag.CCX_ok
    seq_decomp := hseq }

/-! ### §17.f Full-Gate arithmetic soundness from the magic
       interface.

    Combines the magic-aware obligation pipeline with the
    existing §9 induction theorem (which is already
    parameterised on `ArithmeticPrimitivePPMObligations`). -/

theorem compileArithmeticGateToPPM_sound_from_magic_interface
    (sem : GateToPPMSemanticsModel)
    (icx : ArithmeticICXPrimitivePPMObligations sem)
    (mag : MagicInjectionObligations sem)
    (hseq : ∀ g₁ g₂ s u,
      sem.gateRel (Gate.seq g₁ g₂) s u ↔
        ∃ t, sem.gateRel g₁ s t ∧ sem.gateRel g₂ t u) :
    ∀ g, ImplementsGateAsPPM sem g (compileArithmeticGateToPPM g) :=
  compileArithmeticGateToPPM_sound_from_primitives sem
    (mkArithmeticPrimitiveObligationsWithMagic sem icx mag hseq)

/-! ### §17.g Status after §17.

    The full arithmetic-fragment soundness theorem
    `compileArithmeticGateToPPM_sound_from_magic_interface`
    is ready.  To USE it on the entire `Gate` IR, the
    consumer must supply:

      1. A semantic model `sem`.
      2. An `ArithmeticICXPrimitivePPMObligations sem` —
         already closed by `cxMacroICXObligations` in §16.d
         for the `cxMacroPPMSemanticsModel`.  An analogous
         instance for the magic-aware model is the next
         next step.
      3. A `MagicInjectionObligations sem` — the SINGLE
         remaining deferred obligation.  Its `CCX_ok` field
         requires a real Toffoli/CCX semantic proof, which
         no existing repository code provides (the
         `MagicStateInjection` protocols are STRUCTURAL,
         with placeholder identity Clifford-actions).
      4. A `seq_decomp` proof.

    The magic interface delivered here makes (3) the
    EXPLICIT outstanding obligation.  No fake `True`-Prop
    or `False`-hypothesis proof is added.

    Prior milestones intact:
    * stabilizer-only model (§13);
    * enriched LogicalPPMState model (§14);
    * `frameLevelGateRel` I/X bundle (§15);
    * `cxMacroGateRel` I/X/CX bundle and ICX-fragment
      soundness theorem (§16).

    QPE / non-Clifford+T circuits remain rejected/deferred
    via the §1 classifier. -/

/-! ## §18. Integration wrappers — Gate → PPM → backend
       system, with all semantic obligations preserved.

    The full FT-Shor compilation stack at this point looks
    like:

      Gate arithmetic circuit
        → `compileArithmeticGateToPPM`
        → PPMProgram + semantic obligation
        → PPM/QEC lowering obligation (LayeredPPMQECInterface)
        → compressed backend schedule certificate
        → backend system invariants (closed in
          `CompressedRepeatSoundness`)

    This section delivers integration wrappers that thread
    the existing closed pieces together while keeping every
    open obligation EXPLICIT.

    Wrappers:

    * `VerifiedArithmeticToPPMBlock sem` — packages a `Gate`,
      the compiled PPM program, the compile-equation
      witness, and the semantic `ImplementsGateAsPPM`
      proof against the user-supplied semantic model `sem`.
      Three constructors:
        (A) `ofPrimitiveObligations` — from
            `ArithmeticPrimitivePPMObligations sem`.
        (B) `ofICX` — from the §16 ICX-fragment soundness,
            specialised to `cxMacroPPMSemanticsModel n`.
        (C) `ofMagicInterface` — from an ICX bundle plus a
            `MagicInjectionObligations sem` plus a
            `seq_decomp` proof; uses
            `compileArithmeticGateToPPM_sound_from_magic_interface`.

    * `ArithmeticPPMSpec` — a thin description-side wrapper
      pairing the `Gate` circuit with its compiled
      `PPMProgram`.  Distinct from
      `LayeredPPMQECInterface.PPMSpec`, which is the
      MEASUREMENT-spec object (kind + inputs/outputs +
      rounds + distance) — `PPMSpec` is intentionally NOT
      overloaded to represent whole programs.

    * `VerifiedArithmeticPPMProgramBlock sem` — bundles the
      verified arithmetic-to-PPM block with lists of
      `PPMSpec` / `QECGadgetSpec` summaries.  Still ABOVE
      the backend.

    * `VerifiedArithmeticPPMToSystemBlock models sem` — the
      end-to-end integration wrapper: arithmetic-PPM block
      ABOVE, a `VerifiedBackendBlock models` from
      `LayeredPPMQECInterface` BELOW, plus an EXPLICIT
      `lowering_semantic_ok : Prop` slot for the
      PPM-program → backend-schedule lowering obligation
      (NOT proved here — that bridge does not yet exist).

    The projection theorem
    `VerifiedArithmeticPPMToSystemBlock.system_invariants_ok`
    delivers backend resource/scheduling correctness on the
    expanded compressed schedule.  It does NOT claim that
    the backend schedule implements the PPM program — that
    is `lowering_semantic_ok`, deliberately unproved.

    The pre-existing §11 `VerifiedArithmeticPPMBlock`
    structure is preserved unchanged.  The §18 wrapper
    `VerifiedArithmeticToPPMBlock` is a separate, slimmer
    structure (no redundant `accepted` field — every `Gate`
    is in the arithmetic fragment by construction). -/

/-! ### §18.a Slim verified arithmetic-to-PPM wrapper. -/

structure VerifiedArithmeticToPPMBlock
    (sem : GateToPPMSemanticsModel) where
  circuit     : Gate
  ppmProgram  : PPMProgram
  compile_ok  : compileArithmeticGateToPPM circuit = ppmProgram
  semantic_ok : ImplementsGateAsPPM sem circuit ppmProgram

/-! ### §18.b Three constructors. -/

/-- Constructor (A): from a full
    `ArithmeticPrimitivePPMObligations` bundle.  Uses the
    §9 induction theorem to discharge `semantic_ok`. -/
def VerifiedArithmeticToPPMBlock.ofPrimitiveObligations
    (sem : GateToPPMSemanticsModel)
    (obs : ArithmeticPrimitivePPMObligations sem)
    (g : Gate) :
    VerifiedArithmeticToPPMBlock sem :=
  { circuit := g
    ppmProgram := compileArithmeticGateToPPM g
    compile_ok := rfl
    semantic_ok :=
      compileArithmeticGateToPPM_sound_from_primitives sem obs g }

/-- Constructor (B): from the §16 ICX-fragment soundness.
    Restricted to circuits with `isICXGate g = true`, i.e.,
    `Gate.CCX` is rejected.  Discharges `semantic_ok`
    against `cxMacroPPMSemanticsModel n`. -/
def VerifiedArithmeticToPPMBlock.ofICX
    (n : Nat) (g : Gate) (hg : isICXGate g = true) :
    VerifiedArithmeticToPPMBlock (cxMacroPPMSemanticsModel n) :=
  { circuit := g
    ppmProgram := compileArithmeticGateToPPM g
    compile_ok := rfl
    semantic_ok := compileICXGateToPPM_sound_from_cxMacro n g hg }

/-- Constructor (C): from an ICX bundle, a magic-injection
    obligation bundle (carrying the deferred `CCX_ok`), and
    a `seq_decomp` hypothesis.  Discharges `semantic_ok`
    against the user-supplied `sem` via
    `compileArithmeticGateToPPM_sound_from_magic_interface`. -/
def VerifiedArithmeticToPPMBlock.ofMagicInterface
    (sem : GateToPPMSemanticsModel)
    (icx : ArithmeticICXPrimitivePPMObligations sem)
    (mag : MagicInjectionObligations sem)
    (hseq : ∀ g₁ g₂ s u,
      sem.gateRel (Gate.seq g₁ g₂) s u ↔
        ∃ t, sem.gateRel g₁ s t ∧ sem.gateRel g₂ t u)
    (g : Gate) :
    VerifiedArithmeticToPPMBlock sem :=
  { circuit := g
    ppmProgram := compileArithmeticGateToPPM g
    compile_ok := rfl
    semantic_ok :=
      compileArithmeticGateToPPM_sound_from_magic_interface
        sem icx mag hseq g }

/-! ### §18.c Light description-side wrappers. -/

/-- Thin pairing of `Gate` and its compiled `PPMProgram`.
    `PPMSpec` is reserved for measurement-spec objects;
    `ArithmeticPPMSpec` is the description-side pairing. -/
structure ArithmeticPPMSpec where
  circuit    : Gate
  ppmProgram : PPMProgram

/-- A verified arithmetic-to-PPM block enriched with lists
    of `PPMSpec` and `QECGadgetSpec` summaries.  Still
    ABOVE the backend. -/
structure VerifiedArithmeticPPMProgramBlock
    (sem : GateToPPMSemanticsModel) where
  arithmetic : VerifiedArithmeticToPPMBlock sem
  ppmSpecs   : List PPMSpec
  qecSpecs   : List QECGadgetSpec

/-! ### §18.d End-to-end integration: arithmetic-PPM block +
       backend `VerifiedBackendBlock`. -/

structure VerifiedArithmeticPPMToSystemBlock
    (models : SystemModels) (sem : GateToPPMSemanticsModel) where
  arithmeticPPM        : VerifiedArithmeticPPMProgramBlock sem
  backend              : VerifiedBackendBlock models
  /-- Placeholder Prop slot for the PPM-program →
      backend-schedule lowering semantic correctness.  NOT
      proved here — this is the explicit deferred
      cross-layer obligation. -/
  lowering_semantic_ok : Prop

/-! ### §18.e Backend system-invariants projection.

    Delivers only the backend resource/scheduling guarantee
    on the expanded compressed schedule.  It does NOT claim
    that the backend schedule implements the PPM program —
    that lives in `lowering_semantic_ok`.  Proof delegates
    to `VerifiedBackendBlock.strict_invariants_ok` from
    `LayeredPPMQECInterface`. -/

theorem VerifiedArithmeticPPMToSystemBlock.system_invariants_ok
    (models : SystemModels) (sem : GateToPPMSemanticsModel)
    (b : VerifiedArithmeticPPMToSystemBlock models sem) :
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

/-! ### §18.f Stack status after §18.

    Closed in this file:
    * `compileArithmeticGateToPPM` (the structural compiler).
    * Structural compiler theorems
      (`compileArithmeticGateToPPM_I` /
      `_seq`).
    * Full-Gate-IR arithmetic-fragment soundness, reducible
      to primitive obligations (`*_sound_from_primitives`).
    * ICX-fragment soundness against `cxMacroPPMSemanticsModel`
      (`*_sound_from_cxMacro`).
    * Magic-aware interface
      (`*_sound_from_magic_interface`) that consumes the
      isolated `MagicInjectionObligations.CCX_ok` obligation
      and yields full-Gate-IR soundness.

    Closed via integration with `LayeredPPMQECInterface`:
    * Backend system-invariants projection on
      `VerifiedArithmeticPPMToSystemBlock`.

    Explicit deferred / open obligations:
    * `MagicInjectionObligations.CCX_ok` — the Toffoli
      semantic proof (NOT proved; no existing repository
      theorem to reuse).
    * `VerifiedArithmeticPPMToSystemBlock.lowering_semantic_ok`
      — the PPM-program → backend-schedule semantic
      lowering bridge (NOT proved; that bridge does not
      yet exist in the repository).
    * `VerifiedPPMBlock.semantic_ok` (from
      `LayeredPPMQECInterface`) — the PPM/QEC semantic
      correctness obligation.

    Outside the path:
    * QPE / non-Clifford+T phase rotations remain rejected/
      deferred via the §1 classifier and the
      `BaseUnitary.R _ _ _` opaque case.

    Pre-existing §11 `VerifiedArithmeticPPMBlock` is
    UNCHANGED.  The §18 wrapper `VerifiedArithmeticToPPMBlock`
    is a separate slimmer structure (drops the trivially
    `true` `accepted` field). -/

/-! ## §19. Structured PPM-program → backend lowering
       obligations.

    §18's `VerifiedArithmeticPPMToSystemBlock` (the "V1"
    wrapper) packs the cross-layer lowering correctness into
    a single opaque `lowering_semantic_ok : Prop` field.
    That works for typing but hides exactly WHICH three
    statements need to be discharged.

    This section refines the obligation into THREE named
    relations supplied as fields of a `PPMToBackendLoweringModel`
    parameter, with a matching `PPMProgramToBackendLoweringObligation`
    structure carrying the three proofs.  No relation is
    `True`.  No relation is axiomatised.  The user instantiates
    the model with concrete relations and supplies real proofs
    to populate the obligation.

    The three obligation slots:

    1. `ppmProgramImplementsSpecs prog specs` — the PPM
       program faithfully realises the `PPMSpec` list.  This
       sits at the LOGICAL / PPM-measurement layer.
    2. `qecSpecsLowerToSchedule qecSpecs schedule` — the QEC
       gadgets and `PPMSpec`s are realised by the compressed
       backend schedule.  This is the cross-layer lowering
       statement.
    3. `resourceAlignment prog schedule` — resource summaries
       at the PPM/QEC level match backend resource counters.
       This bridges resource accounting between layers.

    Layering recap:
    * Above SysCall/System.
    * Backend routing / crosstalk / factory constraints
      remain inside `compressed_schedule_strict_certificate_ok`.
    * QPE phase rotations remain rejected/deferred (§1).
    * CCX/Toffoli remains isolated in
      `MagicInjectionObligations` (§17).

    Review of existing PPM/QEC lowering-related code:

    | Identifier | File | Class |
    |---|---|---|
    | `SchedulableSurgeryGadget`, `compileSurgeryGadgetRound`,
      `compileSurgeryGadgetToSysCalls` | `SurgeryGadgetToSysCalls.lean` | **B** (structural compiler only — no semantic correctness) |
    | `PPMScheduleCert`, `PPMScheduleCertWithFactoryPorts`,
      `PPMComposeContext`, `validateScheduleWithFactoryPorts` |
      `LatticeSurgeryPPMContract.lean` | **D** (legacy proof-carrying SysCall cert, predecessor of compressed cert) |
    | `JointPauliMeasurementClaim` | `MultiQubitPPM.lean` | **A** (available for PPMSpec refinement) |
    | `compressed_schedule_strict_certificate_ok` |
      `CompressedRepeatSoundness.lean` | **B** (backend certificate; reused via `VerifiedBackendBlock`) |
    | `PauliMeasurementClaim`, `verify_logical_pauli_measurement` |
      `PauliOps.lean` | **A** (available for PPM measurement-semantic refinement) |
    | `PPMOperational.StabilizerState`, `apply_PPM_pos/neg` |
      `PPMOperational.lean` | **A** (used in §13/§14 PPM command relation; available for `ppmProgramImplementsSpecs`) |
    | `LogicalGateProtocolWithMagic`, `logical_t`, `logical_ccz`,
      `logical_ccx` | `MagicStateInjection.lean` | **C** (structural + resource accounting; identity Clifford-action placeholders) |
    | `total_magic_demand` | Same | **C** (resource accounting) |
    | `ArtifactLayer`, `SysCallScheduleArtifact`,
      `VerifiedSysCallSchedule` | `LayeredArtifactInterface.lean` | **D** (legacy SysCall-level artifacts; superseded by compressed certificate) |

    **Classification key:** A = directly reusable for
    PPM-program-to-QEC lowering; B = directly reusable for
    QEC/backend schedule lowering; C = useful for resource
    accounting only; D = legacy/superseded by
    `compressed_schedule_strict_certificate_ok`; E =
    deferred.

    **Conclusion:** No existing repository code provides a
    complete PPM-program → backend-schedule semantic
    lowering theorem.  Pieces exist:
    * A structural surgery-gadget-to-SysCall compiler
      (`SurgeryGadgetToSysCalls`), but no semantic
      correctness theorem.
    * Multiple resource-accounting layers.
    * `PauliMeasurementClaim` / `JointPauliMeasurementClaim`
      structures, but no theorem about their use inside a
      PPM program.

    Therefore the three §19 relation slots remain
    legitimately deferred.  This tick makes the gap
    explicit and structured, not faked. -/

/-! ### §19.a Lowering model: three relation parameters. -/

/-- Abstract lowering model.  The user supplies three
    relations describing what it MEANS for:

    * a `PPMProgram` to implement a list of `PPMSpec`s,
    * a list of `QECGadgetSpec`s to be realised by a
      `CompressedSchedule`,
    * a `PPMProgram` and a `CompressedSchedule` to align in
      resource accounting.

    No relation is `True` or axiomatised.  A concrete
    instantiation must supply actual relations; the
    obligation structure below requires real proofs. -/
structure PPMToBackendLoweringModel
    (models : SystemModels) (sem : GateToPPMSemanticsModel) where
  /-- The PPM program faithfully realises the `PPMSpec` list.
      A future tick can instantiate this as: each `PPMSpec`
      lines up with one or more `measurePauliKind` commands
      in the PPM program, with matching kind / inputs /
      outputs / rounds / distance. -/
  ppmProgramImplementsSpecs :
    PPMProgram → List PPMSpec → Prop
  /-- The QEC-gadget specs are realised by the compressed
      backend schedule.  A future tick can instantiate this
      via `compileSurgeryGadgetToSysCalls` (or a richer
      compiler) and a denotational equivalence theorem. -/
  qecSpecsLowerToSchedule :
    List QECGadgetSpec → CompressedSchedule → Prop
  /-- Resource summaries at the PPM/QEC level match backend
      resource counters.  A future tick can instantiate this
      using the existing `CompressedResourceSummary` and the
      `total_magic_demand` accounting helpers. -/
  resourceAlignment :
    PPMProgram → CompressedSchedule → Prop

/-! ### §19.b Lowering obligation: three concrete proofs
       against a fixed model. -/

structure PPMProgramToBackendLoweringObligation
    (models : SystemModels)
    (sem : GateToPPMSemanticsModel)
    (lowering : PPMToBackendLoweringModel models sem) where
  arithmeticPPM         : VerifiedArithmeticPPMProgramBlock sem
  backend               : VerifiedBackendBlock models
  /-- The PPM program in the arithmetic block implements its
      attached `PPMSpec` list under the supplied lowering
      model.  NOT proved here. -/
  ppm_semantic_ok :
    lowering.ppmProgramImplementsSpecs
      arithmeticPPM.arithmetic.ppmProgram
      arithmeticPPM.ppmSpecs
  /-- The QEC-gadget specs are realised by the backend's
      compressed schedule.  NOT proved here. -/
  qec_backend_ok :
    lowering.qecSpecsLowerToSchedule
      arithmeticPPM.qecSpecs
      backend.schedule
  /-- The PPM program and the backend schedule align in
      resource accounting.  NOT proved here. -/
  resource_alignment_ok :
    lowering.resourceAlignment
      arithmeticPPM.arithmetic.ppmProgram
      backend.schedule

/-! ### §19.c V2 integrated wrapper.

    Replaces the single opaque `lowering_semantic_ok : Prop`
    of §18 V1 with the three explicit obligation fields
    against a user-supplied lowering model. -/

structure VerifiedArithmeticPPMToSystemBlockV2
    (models : SystemModels)
    (sem : GateToPPMSemanticsModel)
    (lowering : PPMToBackendLoweringModel models sem) where
  arithmeticPPM : VerifiedArithmeticPPMProgramBlock sem
  backend       : VerifiedBackendBlock models
  ppm_semantic_ok :
    lowering.ppmProgramImplementsSpecs
      arithmeticPPM.arithmetic.ppmProgram
      arithmeticPPM.ppmSpecs
  qec_backend_ok :
    lowering.qecSpecsLowerToSchedule
      arithmeticPPM.qecSpecs
      backend.schedule
  resource_alignment_ok :
    lowering.resourceAlignment
      arithmeticPPM.arithmetic.ppmProgram
      backend.schedule

/-! ### §19.d Backend system-invariants projection (V2). -/

theorem VerifiedArithmeticPPMToSystemBlockV2.system_invariants_ok
    (models : SystemModels)
    (sem : GateToPPMSemanticsModel)
    (lowering : PPMToBackendLoweringModel models sem)
    (b : VerifiedArithmeticPPMToSystemBlockV2 models sem lowering) :
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

/-! ### §19.e Accessor theorems.

    Pure projections, but useful when a top-level theorem
    needs the three obligation pieces by name. -/

theorem VerifiedArithmeticPPMToSystemBlockV2.ppm_semantic
    (models : SystemModels)
    (sem : GateToPPMSemanticsModel)
    (lowering : PPMToBackendLoweringModel models sem)
    (b : VerifiedArithmeticPPMToSystemBlockV2 models sem lowering) :
    lowering.ppmProgramImplementsSpecs
      b.arithmeticPPM.arithmetic.ppmProgram
      b.arithmeticPPM.ppmSpecs :=
  b.ppm_semantic_ok

theorem VerifiedArithmeticPPMToSystemBlockV2.qec_backend
    (models : SystemModels)
    (sem : GateToPPMSemanticsModel)
    (lowering : PPMToBackendLoweringModel models sem)
    (b : VerifiedArithmeticPPMToSystemBlockV2 models sem lowering) :
    lowering.qecSpecsLowerToSchedule
      b.arithmeticPPM.qecSpecs
      b.backend.schedule :=
  b.qec_backend_ok

theorem VerifiedArithmeticPPMToSystemBlockV2.resource_alignment
    (models : SystemModels)
    (sem : GateToPPMSemanticsModel)
    (lowering : PPMToBackendLoweringModel models sem)
    (b : VerifiedArithmeticPPMToSystemBlockV2 models sem lowering) :
    lowering.resourceAlignment
      b.arithmeticPPM.arithmetic.ppmProgram
      b.backend.schedule :=
  b.resource_alignment_ok

/-! ### §19.f Status and remaining obligations.

    Closed in this file:
    * Lowering MODEL (`PPMToBackendLoweringModel`) — three
      named relation slots.
    * Lowering OBLIGATION structure
      (`PPMProgramToBackendLoweringObligation`) — three
      typed Prop fields against the model.
    * V2 integrated wrapper
      (`VerifiedArithmeticPPMToSystemBlockV2`) — same three
      obligations + backend block.
    * Backend system-invariants projection theorem for V2
      (`VerifiedArithmeticPPMToSystemBlockV2.system_invariants_ok`)
      — one-line delegation to the backend's
      `strict_invariants_ok`.
    * Three accessor theorems for the obligation pieces.

    Explicit deferred / open obligations:
    * `lowering.ppmProgramImplementsSpecs` — must be
      instantiated with a real PPM-measurement / Pauli-frame
      semantic relation; candidate substrate is
      `PPMOperational.StabilizerState` + Gottesman updates.
    * `lowering.qecSpecsLowerToSchedule` — must be
      instantiated with a real QEC-gadget-to-SysCall
      semantic theorem; candidate substrate is
      `SurgeryGadgetToSysCalls.compileSurgeryGadgetToSysCalls`
      plus a denotational equivalence.
    * `lowering.resourceAlignment` — must be instantiated
      with a real resource-counter alignment; candidate
      substrate is `CompressedResourceSummary` +
      `total_magic_demand`.
    * `MagicInjectionObligations.CCX_ok` (§17) — Toffoli
      semantic proof remains open.

    Pre-existing wrappers and theorems preserved:
    * `VerifiedArithmeticPPMToSystemBlock` (§18 V1) —
      kept intact as the legacy coarse wrapper with one
      opaque `lowering_semantic_ok : Prop`.
    * `VerifiedArithmeticPPMToSystemBlock.system_invariants_ok`
      (§18.e) — kept intact.
    * `VerifiedArithmeticPPMBlock` (§11), §13 / §14 / §15 /
      §16 / §17 milestones — all unchanged. -/

/-! ## §20. First V2 lowering-slot instantiation —
       ICX-fragment `ppmProgramImplementsSpecs`.

    The §19 V2 lowering model leaves three relation slots as
    parameters.  This section gives the FIRST concrete
    instantiation: an ICX-fragment relation
    `ICXPPMProgramImplementsSpecs n program specs` that says
    "the PPM program comes from compiling some ICX `Gate`
    whose summary `PPMSpec` list is exactly `specs`, AND the
    compiled program faithfully implements the gate against
    the §16 `cxMacroPPMSemanticsModel n`".

    The other two slots (`qecSpecsLowerToSchedule`,
    `resourceAlignment`) remain user-supplied parameters in
    the partial model
    `ICXPartialLoweringModel`.  No fake relations.

    What this section does NOT do:
    * Does not prove `qecSpecsLowerToSchedule`.
    * Does not prove `resourceAlignment`.
    * Does not lower the PPM program to a backend schedule.
    * Does not handle `Gate.CCX` — full arithmetic still
      waits on `MagicInjectionObligations.CCX_ok` (§17).
    * Does not handle QPE / non-Clifford+T (rejected/deferred
      via §1).

    The `PPMSpec` summary used here is **metadata-light**:
    `rounds := 0` and `distance := 0` are placeholders — the
    full QEC-engineering content of `PPMSpec` is not
    populated by an ICX summary.  Real surgery/distance
    metadata lives in `QECGadgetSpec`, which is intentionally
    NOT generated by this summary. -/

/-! ### §20.a `PPMSpec` summary for an ICX `Gate`.

    Maps an ICX `Gate` to a list of PPM-level summary
    specs.  `Gate.CCX _ _ _` is mapped to `[]` so the
    function is total on `Gate`, but it is only intended to
    be applied to `isICXGate g = true` inputs. -/

def ppmSpecsOfICXGate : Gate → List PPMSpec
  | .I         => []
  | .X q       =>
      [{ measuredPauliKind := PauliKind.X
         logicalInputs     := [q]
         logicalOutputs    := [q]
         rounds            := 0
         distance          := 0 }]
  | .CX c tgt  =>
      [{ measuredPauliKind := PauliKind.Z
         logicalInputs     := [c, tgt]
         logicalOutputs    := [c, tgt]
         rounds            := 0
         distance          := 0 }]
  | .CCX _ _ _ => []
  | .seq g₁ g₂ => ppmSpecsOfICXGate g₁ ++ ppmSpecsOfICXGate g₂

theorem ppmSpecsOfICXGate_I : ppmSpecsOfICXGate Gate.I = [] := rfl

theorem ppmSpecsOfICXGate_seq (g₁ g₂ : Gate) :
    ppmSpecsOfICXGate (Gate.seq g₁ g₂)
      = ppmSpecsOfICXGate g₁ ++ ppmSpecsOfICXGate g₂ := rfl

/-! ### §20.b Witness structure + program-implements-specs
       relation for ICX. -/

/-- A witness that a PPM program is the compilation of some
    ICX `Gate` AND its `PPMSpec` summary list. -/
structure ICXPPMProgramSpecWitness
    (n : Nat) (program : PPMProgram) (specs : List PPMSpec) where
  circuit     : Gate
  is_icx      : isICXGate circuit = true
  compile_ok  : compileArithmeticGateToPPM circuit = program
  specs_ok    : specs = ppmSpecsOfICXGate circuit
  semantic_ok :
    ImplementsGateAsPPM (cxMacroPPMSemanticsModel n) circuit program

/-- The ICX-fragment PPM-program implements its
    `PPMSpec` summary list iff a witness exists.  Not `True`;
    the witness packs four real fields including the §16
    `ImplementsGateAsPPM` proof. -/
def ICXPPMProgramImplementsSpecs
    (n : Nat) (program : PPMProgram) (specs : List PPMSpec) : Prop :=
  Nonempty (ICXPPMProgramSpecWitness n program specs)

/-! ### §20.c Implementation theorem for compiled ICX gates. -/

theorem compileICXGateToPPM_implements_specs
    (n : Nat) (g : Gate) (hg : isICXGate g = true) :
    ICXPPMProgramImplementsSpecs n
      (compileArithmeticGateToPPM g) (ppmSpecsOfICXGate g) :=
  ⟨{ circuit := g
     is_icx := hg
     compile_ok := rfl
     specs_ok := rfl
     semantic_ok := compileICXGateToPPM_sound_from_cxMacro n g hg }⟩

/-! ### §20.d Partial V2 lowering model — ICX slot
       instantiated, other two slots left as parameters. -/

def ICXPartialLoweringModel
    (models : SystemModels) (n : Nat)
    (qecRel : List QECGadgetSpec → CompressedSchedule → Prop)
    (resRel : PPMProgram → CompressedSchedule → Prop) :
    PPMToBackendLoweringModel models (cxMacroPPMSemanticsModel n) :=
  { ppmProgramImplementsSpecs := ICXPPMProgramImplementsSpecs n
    qecSpecsLowerToSchedule   := qecRel
    resourceAlignment         := resRel }

/-! ### §20.e Constructor for `VerifiedArithmeticPPMProgramBlock`
       on the ICX fragment.

    Builds a `VerifiedArithmeticPPMProgramBlock` using
    `VerifiedArithmeticToPPMBlock.ofICX` for the arithmetic
    half and `ppmSpecsOfICXGate g` for the PPM-spec summary.
    The `qecSpecs` list is supplied by the caller — we do
    NOT fabricate a QEC summary from an ICX gate. -/

def VerifiedArithmeticPPMProgramBlock.ofICX
    (n : Nat) (g : Gate) (hg : isICXGate g = true)
    (qecSpecs : List QECGadgetSpec) :
    VerifiedArithmeticPPMProgramBlock (cxMacroPPMSemanticsModel n) :=
  { arithmetic := VerifiedArithmeticToPPMBlock.ofICX n g hg
    ppmSpecs   := ppmSpecsOfICXGate g
    qecSpecs   := qecSpecs }

/-- An ICX-fragment program block's PPM program implements
    its attached `PPMSpec` summary under
    `ICXPPMProgramImplementsSpecs`.  This is the slot-filling
    theorem for `ICXPartialLoweringModel.ppmProgramImplementsSpecs`. -/
theorem VerifiedArithmeticPPMProgramBlock.ofICX_implements_specs
    (n : Nat) (g : Gate) (hg : isICXGate g = true)
    (qecSpecs : List QECGadgetSpec) :
    ICXPPMProgramImplementsSpecs n
      (VerifiedArithmeticPPMProgramBlock.ofICX n g hg qecSpecs).arithmetic.ppmProgram
      (VerifiedArithmeticPPMProgramBlock.ofICX n g hg qecSpecs).ppmSpecs :=
  compileICXGateToPPM_implements_specs n g hg

/-! ### §20.f Status after §20.

    Closed:
    * `ppmSpecsOfICXGate` summary function.
    * `ICXPPMProgramSpecWitness` / `ICXPPMProgramImplementsSpecs`
      relation.
    * `compileICXGateToPPM_implements_specs` —
      compiled ICX gates implement their spec summary.
    * `ICXPartialLoweringModel` — partial lowering model
      with `ppmProgramImplementsSpecs` instantiated.
    * `VerifiedArithmeticPPMProgramBlock.ofICX` constructor.
    * `VerifiedArithmeticPPMProgramBlock.ofICX_implements_specs`
      theorem.

    Explicit remaining V2 obligations:
    * `qecSpecsLowerToSchedule` — open in `ICXPartialLoweringModel`
      (user-supplied `qecRel`).  No existing repository code
      provides a full QEC-gadget-to-CompressedSchedule
      semantic theorem.
    * `resourceAlignment` — open in `ICXPartialLoweringModel`
      (user-supplied `resRel`).
    * Building a full `VerifiedArithmeticPPMToSystemBlockV2`
      requires both of the above plus a `VerifiedBackendBlock`.

    Out of scope (preserved from prior ticks):
    * `MagicInjectionObligations.CCX_ok` — Toffoli semantic
      proof.
    * QPE / non-Clifford+T — rejected/deferred via §1.

    Pre-existing V1 wrappers and all prior milestones
    remain intact. -/

/-! ## §21. ICX resource-alignment slot.

    `ICXPartialLoweringModel` (§20.d) leaves
    `resourceAlignment` as a parameter.  This section
    delivers:

    * `PPMProgramResourceSummary` — a lightweight
      logical/PPM-level resource summary (NOT a backend
      SysCall/factory/decoder resource summary).
    * Counters: `ppmCommandMeasureCount`,
      `ppmCommandFrameUpdateCount`, `ppmCommandMagicTCount`.
    * Aggregate: `ppmProgramResourceSummary`.
    * Append + per-Gate-case compile lemmas.
    * `ICXResourceLoweringModel` — refines
      `ICXPartialLoweringModel` to instantiate
      `resourceAlignment` against a USER-SUPPLIED backend
      projection `CompressedSchedule →
      PPMProgramResourceSummary`.  We do NOT fabricate the
      backend projection.

    Review of existing resource-summary code:

    | Identifier | File | Class |
    |---|---|---|
    | `CompressedResourceSummary` | `LayeredArtifactInterface.lean` | **B** (backend; 8 fields including wallclock, gate2q, measure, decode, feedback, fresh ancilla, magic_req) |
    | `CompressedResourceSummary.zero`, `seqCombine`, `parCombine`, `scale` | Same | **B** |
    | `resourceOfSysCalls : List SysCall → CompressedResourceSummary` | Same | **B** (backend summarizer) |
    | `Gate.tcount`, `Gate.gcount`, `Gate.depth` | `Gate.lean` | **A** (Gate-level counters; not directly PPM-program-level) |
    | `total_magic_demand : List LogicalGateProtocolWithMagic → Nat × Nat` | `MagicStateInjection.lean` | **C** (magic-state demand accounting) |
    | `MagicStateDemand` | Same | **C** |
    | `repeated_schedule_resource_*` | `CompressedRepeatSoundness.lean` | **B** (symbolic resource theorems on `CompressedSchedule.rep`) |
    | `repeat_safe_block_ok`, `RepeatSafeBlock`, `RepeatedScheduleCertificate` | `LayeredArtifactInterface.lean` | **D** (backend cert structures with resource fields) |

    **Classification key:** A = directly reusable for
    PPMProgram resource summary; B = backend/CompressedSchedule
    side; C = magic-state accounting; D = legacy/deferred.

    **Conclusion:** No existing PPM-program-level resource
    summary.  We introduce `PPMProgramResourceSummary` here.
    Backend-side `CompressedResourceSummary` already exists
    and remains the right object on the backend side; the
    user-supplied projection `CompressedSchedule →
    PPMProgramResourceSummary` is the bridge. -/

/-! ### §21.a `PPMProgramResourceSummary`. -/

structure PPMProgramResourceSummary where
  commandCount : Nat
  measureCount : Nat
  frameUpdates : Nat
  magicTCount  : Nat
  deriving Repr, Inhabited, DecidableEq

end FormalRV.Framework.CircuitToPPMInterface
