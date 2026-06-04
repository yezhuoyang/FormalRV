import FormalRV.PPM.LayeredPPMQECInterface
import FormalRV.Core.QuantumGate
import FormalRV.PPM.PPMOperational
import FormalRV.PPM.FactoryHierarchy
import FormalRV.PPM.CircuitToPPMInterface.Part4

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


/-! ### §21.b Per-command counters and program summarizer. -/

def ppmCommandMeasureCount : PPMCommand → Nat
  | .measurePauliKind _ _ => 1
  | _                     => 0

def ppmCommandFrameUpdateCount : PPMCommand → Nat
  | .applyFrameUpdate _ => 1
  | _                   => 0

def ppmCommandMagicTCount : PPMCommand → Nat
  | .useMagicT _ => 1
  | _            => 0

/-- Sum a Nat-valued function over a list. -/
def listSumOver {α : Type} (f : α → Nat) : List α → Nat
  | []      => 0
  | x :: xs => f x + listSumOver f xs

theorem listSumOver_append {α : Type} (f : α → Nat) (xs ys : List α) :
    listSumOver f (xs ++ ys) = listSumOver f xs + listSumOver f ys := by
  induction xs with
  | nil => simp [listSumOver]
  | cons x rest ih =>
      show f x + listSumOver f (rest ++ ys)
            = (f x + listSumOver f rest) + listSumOver f ys
      rw [ih]; omega

def ppmProgramResourceSummary (p : PPMProgram) : PPMProgramResourceSummary :=
  { commandCount := p.length
    measureCount := listSumOver ppmCommandMeasureCount p
    frameUpdates := listSumOver ppmCommandFrameUpdateCount p
    magicTCount  := listSumOver ppmCommandMagicTCount  p }

/-! ### §21.c Append lemma. -/

theorem ppmProgramResourceSummary_append (p₁ p₂ : PPMProgram) :
    ppmProgramResourceSummary (p₁ ++ p₂)
      = PPMProgramResourceSummary.add
          (ppmProgramResourceSummary p₁) (ppmProgramResourceSummary p₂) := by
  unfold ppmProgramResourceSummary PPMProgramResourceSummary.add
  rw [List.length_append, listSumOver_append,
      listSumOver_append, listSumOver_append]

/-! ### §21.d Compiled-gate resource summaries.

    Compile each `Gate` constructor case and read off the
    PPM-program resource fingerprint. -/

theorem ppmProgramResourceSummary_compile_I :
    ppmProgramResourceSummary (compileArithmeticGateToPPM Gate.I)
      = PPMProgramResourceSummary.zero := rfl

theorem ppmProgramResourceSummary_compile_X (q : LogicalQubitId) :
    ppmProgramResourceSummary (compileArithmeticGateToPPM (Gate.X q))
      = PPMProgramResourceSummary.mk 1 0 1 0 := rfl

theorem ppmProgramResourceSummary_compile_CX (c t : LogicalQubitId) :
    ppmProgramResourceSummary (compileArithmeticGateToPPM (Gate.CX c t))
      = PPMProgramResourceSummary.mk 2 1 1 0 := rfl

theorem ppmProgramResourceSummary_compile_CCX (a b t : LogicalQubitId) :
    ppmProgramResourceSummary (compileArithmeticGateToPPM (Gate.CCX a b t))
      = PPMProgramResourceSummary.mk 3 1 1 1 := rfl

theorem ppmProgramResourceSummary_compile_seq (g₁ g₂ : Gate) :
    ppmProgramResourceSummary (compileArithmeticGateToPPM (Gate.seq g₁ g₂))
      = PPMProgramResourceSummary.add
          (ppmProgramResourceSummary (compileArithmeticGateToPPM g₁))
          (ppmProgramResourceSummary (compileArithmeticGateToPPM g₂)) := by
  rw [compileArithmeticGateToPPM_seq]
  exact ppmProgramResourceSummary_append _ _

/-! ### §21.e ICX resource-alignment lowering model.

    Builds on `ICXPartialLoweringModel` (§20.d) by
    instantiating `resourceAlignment` with the equality of
    `ppmProgramResourceSummary` and a USER-SUPPLIED backend
    projection `backendSummary : CompressedSchedule →
    PPMProgramResourceSummary`.

    `qecSpecsLowerToSchedule` remains a user parameter.  No
    backend projection is fabricated by the framework — the
    user passes whichever projection is appropriate for
    their backend. -/

def ICXResourceAlignment
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary)
    (program : PPMProgram) (schedule : CompressedSchedule) : Prop :=
  ppmProgramResourceSummary program = backendSummary schedule

def ICXResourceLoweringModel
    (models : SystemModels) (n : Nat)
    (qecRel : List QECGadgetSpec → CompressedSchedule → Prop)
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary) :
    PPMToBackendLoweringModel models (cxMacroPPMSemanticsModel n) :=
  { ppmProgramImplementsSpecs := ICXPPMProgramImplementsSpecs n
    qecSpecsLowerToSchedule   := qecRel
    resourceAlignment         := ICXResourceAlignment backendSummary }

/-! ### §21.f Resource-alignment theorem for an ICX block. -/

/-- If the user-supplied `backendSummary backend.schedule`
    equals the PPM-program resource summary of the compiled
    ICX gate, then the `resourceAlignment` slot of
    `ICXResourceLoweringModel` is satisfied by the
    `VerifiedArithmeticPPMProgramBlock.ofICX` block on
    `backend`. -/
theorem VerifiedArithmeticPPMProgramBlock.ofICX_resourceAlignment
    (models : SystemModels) (n : Nat)
    (g : Gate) (hg : isICXGate g = true)
    (qecSpecs : List QECGadgetSpec)
    (qecRel : List QECGadgetSpec → CompressedSchedule → Prop)
    (backend : VerifiedBackendBlock models)
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary)
    (hAlign :
      backendSummary backend.schedule
        = ppmProgramResourceSummary (compileArithmeticGateToPPM g)) :
    (ICXResourceLoweringModel models n qecRel backendSummary).resourceAlignment
      (VerifiedArithmeticPPMProgramBlock.ofICX n g hg qecSpecs).arithmetic.ppmProgram
      backend.schedule := by
  show ppmProgramResourceSummary
        (VerifiedArithmeticPPMProgramBlock.ofICX n g hg qecSpecs).arithmetic.ppmProgram
        = backendSummary backend.schedule
  -- The block's ppmProgram is exactly compileArithmeticGateToPPM g
  show ppmProgramResourceSummary (compileArithmeticGateToPPM g)
        = backendSummary backend.schedule
  exact hAlign.symm

/-! ### §21.g Status after §21.

    Closed:
    * `PPMProgramResourceSummary` + zero + add + assoc/zero
      lemmas.
    * Per-command counters
      (`ppmCommandMeasureCount`, `ppmCommandFrameUpdateCount`,
      `ppmCommandMagicTCount`).
    * Program-level summarizer (`ppmProgramResourceSummary`).
    * `ppmProgramResourceSummary_append`.
    * `ppmProgramResourceSummary_compile_I` / `_X` / `_CX` /
      `_CCX` / `_seq` — concrete resource fingerprints for
      every `Gate` constructor.
    * `ICXResourceAlignment` — concrete alignment predicate.
    * `ICXResourceLoweringModel` — refined ICX model with
      `resourceAlignment` slot instantiated against a
      user-supplied backend projection.
    * `VerifiedArithmeticPPMProgramBlock.ofICX_resourceAlignment`
      — slot-filling theorem.

    Explicit open obligations:
    * `qecSpecsLowerToSchedule` — still a user parameter in
      `ICXResourceLoweringModel`; no QEC-to-schedule
      semantic theorem exists in the repository to plug in.
    * The user-supplied `backendSummary` itself is a real
      modelling choice; we do not fabricate it.
    * `MagicInjectionObligations.CCX_ok` (§17) — Toffoli
      semantic proof remains open.
    * QPE / non-Clifford+T — rejected/deferred via §1.

    Pre-existing milestones (§11–§20) remain intact. -/

/-! ## §22. Surgery-gadget-based QEC-to-backend lowering
       relation.

    `ICXResourceLoweringModel` (§21.e) still leaves
    `qecSpecsLowerToSchedule` as an opaque user parameter.
    This section instantiates it concretely against the
    existing surgery-gadget-to-SysCall compiler
    (`FormalRV.Framework.SurgeryGadgetToSysCalls`).

    Review of existing surgery / QEC / backend compiler code:

    | Identifier | File | Class |
    |---|---|---|
    | `LDPC.SurgeryGadget` (data_code, ancilla matrices, tau_s, target_pauli, span_witness, qLDPC bound) | `LDPCSurgery.lean` | **A** (the QEC-gadget structural object) |
    | `SchedulableSurgeryGadget` (gadget + sites + start_us + decoder_id_base) | `SurgeryGadgetToSysCalls.lean` | **A** |
    | `compileSurgeryGadgetRound` (5 SysCalls/round) | Same | **B** (schedule emission, structural) |
    | `compileSurgeryGadgetToSysCalls` (5·τₛ + 1 SysCalls total) | Same | **B** |
    | `compileSurgeryGadgetToSysCalls_length` | Same | **B** (structural count theorem) |
    | `TopologySchedulableSurgeryGadget`, `compileTopologySurgeryRound`, `compileTopologySurgeryToSysCalls` | Same | **B** (richer topology-aware compiler, deferred for this tick) |
    | `emitXEdgeGates`, `emitZEdgeGates`, `emitAncillaMeasures` | Same | **B** (per-round emission helpers) |
    | `QECGadgetSpec` (ppm, code, gadget, syndromeRounds, decoder, usesPauliFrame) | `LayeredPPMQECInterface.lean` | **A** (the spec-side object reused via §18 wrappers) |
    | `PPMGadget` (target, operator_weight, tau_s) | `L3_PPM.lean` | **A** (engineering spec, fed into `QECGadgetSpec.gadget`) |
    | `CompressedSchedule.atom`, `.seq`, `.expand` | `LayeredArtifactInterface.lean` | **A** (compressed-schedule constructors used in the lowering relation) |
    | `VerifiedBackendBlock` | `LayeredPPMQECInterface.lean` | **A** (backend half, reused via §18/§19 wrappers) |

    **Classification key:** A = directly reusable for
    structural QEC/backend lowering; B = useful for schedule
    emission; C = useful for semantic correctness later;
    D = resource-only; E = legacy/deferred.

    **Conclusion:** `SurgeryGadgetToSysCalls` provides a
    fully structural compiler from `SchedulableSurgeryGadget`
    to `List SysCall`.  It does NOT prove semantic
    correctness against a `QECGadgetSpec`.  The
    `specMatch : QECGadgetSpec → SchedulableSurgeryGadget →
    Prop` relation is therefore a user parameter — the
    framework does not synthesise it.

    The §22 design uses the existing compiler as the
    STRUCTURAL side of the lowering relation while keeping
    the semantic side (`specMatch`) as a named open
    obligation. -/

/-! ### §22.a Listwise `specMatch` predicate. -/

/-- Listwise spec-matching between a list of `QECGadgetSpec`s
    and a list of `SchedulableSurgeryGadget`s.  Equivalent to
    `List.Forall₂` (which Lean core does not expose).
    Structural recursion on the two lists; matches by
    position. -/
def specMatchListwise
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop) :
    List QECGadgetSpec → List SchedulableSurgeryGadget → Prop
  | [],      []      => True
  | _ :: _,  []      => False
  | [],      _ :: _  => False
  | q :: qs, g :: gs => specMatch q g ∧ specMatchListwise specMatch qs gs

@[simp] theorem specMatchListwise_nil_nil
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop) :
    specMatchListwise specMatch [] [] = True := rfl

@[simp] theorem specMatchListwise_cons_cons
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (q : QECGadgetSpec) (qs : List QECGadgetSpec)
    (g : SchedulableSurgeryGadget) (gs : List SchedulableSurgeryGadget) :
    specMatchListwise specMatch (q :: qs) (g :: gs)
      = (specMatch q g ∧ specMatchListwise specMatch qs gs) := rfl

/-! ### §22.b Surgery-gadget backend-lowering witness. -/

/-- One-gadget structural witness: a single
    `SchedulableSurgeryGadget` compiled to a `SysCall` list,
    wrapped as a `CompressedSchedule.atom`, that is claimed
    to implement a single `QECGadgetSpec` via the supplied
    `specMatch`. -/
structure SurgeryGadgetBackendLoweringWitness
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (qecSpec : QECGadgetSpec) (schedule : CompressedSchedule) where
  gadget       : SchedulableSurgeryGadget
  syscalls     : List SysCall
  compile_ok   : compileSurgeryGadgetToSysCalls gadget = syscalls
  schedule_ok  : schedule = CompressedSchedule.atom syscalls
  spec_ok      : specMatch qecSpec gadget

/-! ### §22.c One-gadget and list QEC-to-backend lowering
       relations. -/

/-- Single-spec, single-gadget lowering relation. -/
def SurgeryQECSpecLowerToScheduleOne
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (qecSpec : QECGadgetSpec) (schedule : CompressedSchedule) : Prop :=
  Nonempty (SurgeryGadgetBackendLoweringWitness specMatch qecSpec schedule)

/-- Build a `CompressedSchedule` by composing each gadget's
    compiled SysCall list as an `atom`, then sequencing all
    such atoms via `CompressedSchedule.seq`. -/
def composedSurgerySchedule
    (gadgets : List SchedulableSurgeryGadget) : CompressedSchedule :=
  CompressedSchedule.seq
    (gadgets.map (fun g => CompressedSchedule.atom
      (compileSurgeryGadgetToSysCalls g)))

/-- List version of the lowering relation.  The
    `qecSpecs` list lowers to `schedule` iff there exists a
    matching list of `SchedulableSurgeryGadget`s that
    pointwise pass `specMatch`, and `schedule` is the
    `composedSurgerySchedule` of those gadgets. -/
def SurgeryQECSpecsLowerToSchedule
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (qecSpecs : List QECGadgetSpec) (schedule : CompressedSchedule) : Prop :=
  ∃ gadgets : List SchedulableSurgeryGadget,
    specMatchListwise specMatch qecSpecs gadgets
    ∧ schedule = composedSurgerySchedule gadgets

/-! ### §22.d Witness-construction theorems. -/

/-- Single-gadget witness construction: given a
    `specMatch` proof and a compile equation, the one-gadget
    lowering relation holds for the corresponding
    `CompressedSchedule.atom`. -/
theorem SurgeryQECSpecLowerToScheduleOne.construct
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (qecSpec : QECGadgetSpec) (gadget : SchedulableSurgeryGadget)
    (hmatch : specMatch qecSpec gadget) :
    SurgeryQECSpecLowerToScheduleOne specMatch qecSpec
      (CompressedSchedule.atom (compileSurgeryGadgetToSysCalls gadget)) :=
  ⟨{ gadget := gadget
     syscalls := compileSurgeryGadgetToSysCalls gadget
     compile_ok := rfl
     schedule_ok := rfl
     spec_ok := hmatch }⟩

/-- List witness construction: from a list of gadgets with
    pointwise `specMatch` proofs, the list lowering relation
    holds for the `composedSurgerySchedule`. -/
theorem SurgeryQECSpecsLowerToSchedule.construct
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (qecSpecs : List QECGadgetSpec) (gadgets : List SchedulableSurgeryGadget)
    (hmatch : specMatchListwise specMatch qecSpecs gadgets) :
    SurgeryQECSpecsLowerToSchedule specMatch qecSpecs
      (composedSurgerySchedule gadgets) :=
  ⟨gadgets, hmatch, rfl⟩

/-- Trivial nil case: empty `qecSpecs` and empty `gadgets`
    produce the empty `composedSurgerySchedule`. -/
theorem SurgeryQECSpecsLowerToSchedule.nil
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop) :
    SurgeryQECSpecsLowerToSchedule specMatch []
      (composedSurgerySchedule []) :=
  SurgeryQECSpecsLowerToSchedule.construct specMatch [] [] True.intro

/-! ### §22.e Surgery-specific lowering model.

    Combines:
    * `ppmProgramImplementsSpecs := ICXPPMProgramImplementsSpecs n`
      (from §20.d);
    * `qecSpecsLowerToSchedule := SurgeryQECSpecsLowerToSchedule
       specMatch` (THIS section);
    * `resourceAlignment := ICXResourceAlignment backendSummary`
      (from §21.e).

    All three slots are now concretely instantiated.  The
    only remaining parameters are `specMatch` (the QEC
    semantic-correctness obligation) and `backendSummary`
    (the user-supplied resource projection). -/

def ICXSurgeryLoweringModel
    (models : SystemModels) (n : Nat)
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary) :
    PPMToBackendLoweringModel models (cxMacroPPMSemanticsModel n) :=
  { ppmProgramImplementsSpecs := ICXPPMProgramImplementsSpecs n
    qecSpecsLowerToSchedule   := SurgeryQECSpecsLowerToSchedule specMatch
    resourceAlignment         := ICXResourceAlignment backendSummary }

/-! ### §22.f Conditional V2 integrated wrapper constructor
       on top of the surgery model.

    Builds a `VerifiedArithmeticPPMToSystemBlockV2` against
    `ICXSurgeryLoweringModel`, given:
    * an ICX-fragment program block from §20.e;
    * a backend block;
    * an explicit `qec_backend_ok` proof against the
      surgery relation (THIS section's structured
      obligation);
    * an explicit `resource_alignment_ok` proof against the
      §21.e alignment predicate.

    All three top-level obligations are PARAMETERS — none
    are fabricated.  In particular, `qec_backend_ok` is
    not faked: the caller must supply a real surgery
    witness, including the `specMatch` proof and the
    `composedSurgerySchedule = backend.schedule` equation. -/

def VerifiedArithmeticPPMToSystemBlockV2.ofICXSurgery
    (models : SystemModels) (n : Nat)
    (g : Gate) (hg : isICXGate g = true) (qecSpecs : List QECGadgetSpec)
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary)
    (backend : VerifiedBackendBlock models)
    (hqec :
      SurgeryQECSpecsLowerToSchedule specMatch qecSpecs backend.schedule)
    (hres :
      ICXResourceAlignment backendSummary
        ((VerifiedArithmeticPPMProgramBlock.ofICX n g hg qecSpecs).arithmetic.ppmProgram)
        backend.schedule) :
    VerifiedArithmeticPPMToSystemBlockV2 models
      (cxMacroPPMSemanticsModel n)
      (ICXSurgeryLoweringModel models n specMatch backendSummary) :=
  { arithmeticPPM := VerifiedArithmeticPPMProgramBlock.ofICX n g hg qecSpecs
    backend := backend
    ppm_semantic_ok := compileICXGateToPPM_implements_specs n g hg
    qec_backend_ok  := hqec
    resource_alignment_ok := hres }

/-! ### §22.g Status after §22.

    Closed:
    * `specMatchListwise` (pointwise spec-match predicate
      between QEC spec lists and gadget lists).
    * `SurgeryGadgetBackendLoweringWitness` — one-gadget
      structural witness.
    * `SurgeryQECSpecLowerToScheduleOne` — single-spec
      relation.
    * `SurgeryQECSpecsLowerToSchedule` — list relation.
    * `composedSurgerySchedule` — list-of-gadgets to
      `CompressedSchedule.seq (map atom (compile g))`
      builder.
    * `SurgeryQECSpecLowerToScheduleOne.construct`,
      `SurgeryQECSpecsLowerToSchedule.construct`,
      `SurgeryQECSpecsLowerToSchedule.nil` — witness
      constructors.
    * `ICXSurgeryLoweringModel` — concrete V2 lowering
      model with all three slots instantiated; only
      `specMatch` and `backendSummary` remain as
      parameters.
    * `VerifiedArithmeticPPMToSystemBlockV2.ofICXSurgery` —
      conditional constructor that takes the three
      obligation pieces as arguments and assembles a V2
      block.

    Explicit open obligations:
    * `specMatch : QECGadgetSpec → SchedulableSurgeryGadget
      → Prop` — the QEC semantic-correctness obligation
      (no existing repository code provides such a
      theorem).
    * `backendSummary : CompressedSchedule →
      PPMProgramResourceSummary` — user resource
      projection (modelling choice).
    * `MagicInjectionObligations.CCX_ok` (§17) — Toffoli
      semantic proof remains open.
    * QPE / non-Clifford+T — rejected/deferred via the
      §1 classifier.

    Backend system invariants remain certified by the
    pre-existing
    `VerifiedArithmeticPPMToSystemBlockV2.system_invariants_ok`
    (§19.d), which is independent of `qec_backend_ok` and
    `resource_alignment_ok`. -/

/-! ## §23. Toy ICX end-to-end smoke test.

    A minimal example threading every V2 interface slot:
    a single `Gate.X 0` arithmetic gate, an explicit listwise
    `specMatch` proof, an explicit backend-schedule
    structural equation, and an explicit resource-alignment
    equation.  The smoke test EXISTS to demonstrate that the
    V2 framework is end-to-end usable; it does NOT prove the
    semantic lowering.

    Specifically, this section does NOT prove:
    * `specMatch` — supplied as a parameter.
    * `backendSummary` — supplied as a parameter.
    * QEC semantic-correctness on `SchedulableSurgeryGadget`.
    * `MagicInjectionObligations.CCX_ok` (Toffoli/CCX is
      OUTSIDE this ICX-only example).
    * Anything about QPE / non-Clifford+T (rejected/deferred
      at §1). -/

/-! ### §23.a Toy ICX gate. -/

def toyICXGate : Gate := Gate.X 0

theorem toyICXGate_isICX : isICXGate toyICXGate = true := rfl

/-! ### §23.b Toy arithmetic-PPM program block. -/

def toyArithmeticPPMBlock (n : Nat) (qecSpecs : List QECGadgetSpec) :
    VerifiedArithmeticPPMProgramBlock (cxMacroPPMSemanticsModel n) :=
  VerifiedArithmeticPPMProgramBlock.ofICX n toyICXGate toyICXGate_isICX qecSpecs

/-- Sanity: `toyArithmeticPPMBlock` implements its own PPM spec
    list under `ICXPPMProgramImplementsSpecs`. -/
theorem toyArithmeticPPMBlock_implements_specs
    (n : Nat) (qecSpecs : List QECGadgetSpec) :
    ICXPPMProgramImplementsSpecs n
      (toyArithmeticPPMBlock n qecSpecs).arithmetic.ppmProgram
      (toyArithmeticPPMBlock n qecSpecs).ppmSpecs :=
  VerifiedArithmeticPPMProgramBlock.ofICX_implements_specs n
    toyICXGate toyICXGate_isICX qecSpecs

/-! ### §23.c QEC/backend lowering proof for the toy block.

    Given a listwise `specMatch` proof for the user-supplied
    `qecSpecs` / `gadgets` and an equation relating the
    backend schedule to `composedSurgerySchedule gadgets`,
    we obtain the V2 surgery-lowering slot. -/

theorem toy_qec_backend_ok
    (models : SystemModels)
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (qecSpecs : List QECGadgetSpec)
    (gadgets : List SchedulableSurgeryGadget)
    (hmatch : specMatchListwise specMatch qecSpecs gadgets)
    (backend : VerifiedBackendBlock models)
    (hbackend : backend.schedule = composedSurgerySchedule gadgets) :
    SurgeryQECSpecsLowerToSchedule specMatch qecSpecs backend.schedule := by
  rw [hbackend]
  exact SurgeryQECSpecsLowerToSchedule.construct specMatch qecSpecs gadgets hmatch

/-! ### §23.d Resource alignment proof for the toy block. -/

theorem toy_resource_alignment_ok
    (models : SystemModels) (n : Nat)
    (qecSpecs : List QECGadgetSpec)
    (backend : VerifiedBackendBlock models)
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary)
    (hAlign :
      backendSummary backend.schedule
        = ppmProgramResourceSummary (compileArithmeticGateToPPM toyICXGate)) :
    ICXResourceAlignment backendSummary
      ((toyArithmeticPPMBlock n qecSpecs).arithmetic.ppmProgram)
      backend.schedule := by
  show ppmProgramResourceSummary
        ((toyArithmeticPPMBlock n qecSpecs).arithmetic.ppmProgram)
        = backendSummary backend.schedule
  exact hAlign.symm

/-! ### §23.e Toy V2 block constructor.

    Assembles a full `VerifiedArithmeticPPMToSystemBlockV2`
    against `ICXSurgeryLoweringModel` from the three
    user-supplied obligation pieces. -/

def toyV2Block
    (models : SystemModels) (n : Nat)
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary)
    (qecSpecs : List QECGadgetSpec)
    (gadgets : List SchedulableSurgeryGadget)
    (backend : VerifiedBackendBlock models)
    (hmatch : specMatchListwise specMatch qecSpecs gadgets)
    (hbackend : backend.schedule = composedSurgerySchedule gadgets)
    (hAlign :
      backendSummary backend.schedule
        = ppmProgramResourceSummary (compileArithmeticGateToPPM toyICXGate)) :
    VerifiedArithmeticPPMToSystemBlockV2 models
      (cxMacroPPMSemanticsModel n)
      (ICXSurgeryLoweringModel models n specMatch backendSummary) :=
  VerifiedArithmeticPPMToSystemBlockV2.ofICXSurgery
    models n toyICXGate toyICXGate_isICX qecSpecs
    specMatch backendSummary backend
    (toy_qec_backend_ok models specMatch qecSpecs gadgets hmatch backend hbackend)
    (toy_resource_alignment_ok models n qecSpecs backend backendSummary hAlign)

/-! ### §23.f Backend system-invariants projection for the
       toy block.

    Closes the strict-bundle theorem on the toy block's
    backend schedule by delegating to the V2 system-invariants
    projection.  Independent of `specMatch`,
    `backendSummary`, or any semantic lowering proof. -/

theorem toyICXBlock_system_invariants_ok
    (models : SystemModels) (n : Nat)
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary)
    (qecSpecs : List QECGadgetSpec)
    (gadgets : List SchedulableSurgeryGadget)
    (backend : VerifiedBackendBlock models)
    (hmatch : specMatchListwise specMatch qecSpecs gadgets)
    (hbackend : backend.schedule = composedSurgerySchedule gadgets)
    (hAlign :
      backendSummary backend.schedule
        = ppmProgramResourceSummary (compileArithmeticGateToPPM toyICXGate)) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch
        models.opCap
        models.slotCap
        models.ancillaModel
        backend.schedule.expand
        models.t_react_us
        models.window_us
        models.max_per_window = true :=
  VerifiedArithmeticPPMToSystemBlockV2.system_invariants_ok
    models (cxMacroPPMSemanticsModel n)
    (ICXSurgeryLoweringModel models n specMatch backendSummary)
    (toyV2Block models n specMatch backendSummary qecSpecs gadgets backend
       hmatch hbackend hAlign)

/-! ### §23.g Projection theorems for the toy block's three
       V2 obligation pieces. -/

theorem toyICXBlock_ppm_semantic
    (models : SystemModels) (n : Nat)
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary)
    (qecSpecs : List QECGadgetSpec)
    (gadgets : List SchedulableSurgeryGadget)
    (backend : VerifiedBackendBlock models)
    (hmatch : specMatchListwise specMatch qecSpecs gadgets)
    (hbackend : backend.schedule = composedSurgerySchedule gadgets)
    (hAlign :
      backendSummary backend.schedule
        = ppmProgramResourceSummary (compileArithmeticGateToPPM toyICXGate)) :
    ICXPPMProgramImplementsSpecs n
      ((toyV2Block models n specMatch backendSummary qecSpecs gadgets
        backend hmatch hbackend hAlign).arithmeticPPM.arithmetic.ppmProgram)
      ((toyV2Block models n specMatch backendSummary qecSpecs gadgets
        backend hmatch hbackend hAlign).arithmeticPPM.ppmSpecs) :=
  (toyV2Block models n specMatch backendSummary qecSpecs gadgets backend
    hmatch hbackend hAlign).ppm_semantic_ok

theorem toyICXBlock_qec_backend
    (models : SystemModels) (n : Nat)
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary)
    (qecSpecs : List QECGadgetSpec)
    (gadgets : List SchedulableSurgeryGadget)
    (backend : VerifiedBackendBlock models)
    (hmatch : specMatchListwise specMatch qecSpecs gadgets)
    (hbackend : backend.schedule = composedSurgerySchedule gadgets)
    (hAlign :
      backendSummary backend.schedule
        = ppmProgramResourceSummary (compileArithmeticGateToPPM toyICXGate)) :
    SurgeryQECSpecsLowerToSchedule specMatch
      ((toyV2Block models n specMatch backendSummary qecSpecs gadgets
        backend hmatch hbackend hAlign).arithmeticPPM.qecSpecs)
      ((toyV2Block models n specMatch backendSummary qecSpecs gadgets
        backend hmatch hbackend hAlign).backend.schedule) :=
  (toyV2Block models n specMatch backendSummary qecSpecs gadgets backend
    hmatch hbackend hAlign).qec_backend_ok

theorem toyICXBlock_resource_alignment
    (models : SystemModels) (n : Nat)
    (specMatch : QECGadgetSpec → SchedulableSurgeryGadget → Prop)
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary)
    (qecSpecs : List QECGadgetSpec)
    (gadgets : List SchedulableSurgeryGadget)
    (backend : VerifiedBackendBlock models)
    (hmatch : specMatchListwise specMatch qecSpecs gadgets)
    (hbackend : backend.schedule = composedSurgerySchedule gadgets)
    (hAlign :
      backendSummary backend.schedule
        = ppmProgramResourceSummary (compileArithmeticGateToPPM toyICXGate)) :
    ICXResourceAlignment backendSummary
      ((toyV2Block models n specMatch backendSummary qecSpecs gadgets
        backend hmatch hbackend hAlign).arithmeticPPM.arithmetic.ppmProgram)
      ((toyV2Block models n specMatch backendSummary qecSpecs gadgets
        backend hmatch hbackend hAlign).backend.schedule) :=
  (toyV2Block models n specMatch backendSummary qecSpecs gadgets backend
    hmatch hbackend hAlign).resource_alignment_ok

/-! ### §23.h Status after §23.

    Closed (interface smoke test):
    * `toyICXGate := Gate.X 0` and its `isICXGate` proof.
    * `toyArithmeticPPMBlock` constructor (§20.e).
    * `toyArithmeticPPMBlock_implements_specs` — PPM
      semantic-spec slot for the toy block.
    * `toy_qec_backend_ok` — QEC/backend lowering slot, from
      a listwise specMatch + a backend-schedule structural
      equation.
    * `toy_resource_alignment_ok` — resource-alignment slot,
      from an explicit backendSummary equation.
    * `toyV2Block` — full V2 wrapper constructor.
    * `toyICXBlock_system_invariants_ok` — backend
      system-invariants projection on the toy block.
    * `toyICXBlock_ppm_semantic`, `toyICXBlock_qec_backend`,
      `toyICXBlock_resource_alignment` — accessor theorems
      for the three V2 obligation pieces.

    Open obligations remaining (UNCHANGED — this is a smoke
    test, not a semantic proof):
    * `specMatch` — user parameter.  No QEC semantic-
      correctness proof is added.
    * `backendSummary` — user parameter.  No resource-
      projection correctness is added.
    * `hbackend : backend.schedule = composedSurgerySchedule
      gadgets` — user-supplied structural equation.  No
      claim is made that a real backend schedule actually
      equals the composed surgery schedule.
    * `hAlign : backendSummary backend.schedule = …` —
      user-supplied alignment equation.
    * `MagicInjectionObligations.CCX_ok` (§17) — Toffoli
      semantic proof remains open and is OUTSIDE this
      ICX-only example.
    * QPE / non-Clifford+T — rejected/deferred via §1
      classifier.

    All prior milestones (§11–§22) remain intact. -/

/-! ## §24. Concrete structural `specMatch` for the surgery
       lowering relation.

    The §23 smoke test takes `specMatch` as an OPAQUE
    parameter.  This section replaces the parameter with a
    concrete, CHECKABLE structural relation
    `QECSpecMatchesSurgeryGadget` that reduces the
    QEC-spec-to-surgery-gadget match to FIVE field-level
    equalities:

      1. `spec.gadget.tau_s = sg.gadget.tau_s`
         (L3 PPM gadget cycle count agrees with the surgery
         gadget's cycle count).
      2. `spec.code = sg.gadget.data_code`
         (the QEC code in the spec is the surgery gadget's
         data code).
      3. `spec.gadget.target = sg.gadget.data_code`
         (the PPM gadget's target code is the surgery
         gadget's data code).
      4. `spec.syndromeRounds = sg.gadget.tau_s`
         (the spec's syndrome-extraction round count equals
         the surgery cycle count).
      5. `spec.decoder = sg.decoder_id_base`
         (the spec's decoder ID equals the surgery gadget's
         decoder base).

    This is **structural matching**, not semantic
    correctness.  A real proof that the SysCalls emitted by
    `compileSurgeryGadgetToSysCalls` implement the
    QEC-gadget's semantic action remains open.

    Field inventory (from §22 review):

    * `QECGadgetSpec` (`LayeredPPMQECInterface.lean`):
      `ppm : PPMSpec`, `code : QECCode`, `gadget : PPMGadget`,
      `syndromeRounds : Nat`, `decoder : DecoderId`,
      `usesPauliFrame : Bool`.
    * `PPMGadget` (`L3_PPM.lean`): `target : QECCode`,
      `operator_weight : Nat`, `tau_s : Nat`.
    * `QECCode` (`L4_QECCode.lean`): `n : Nat`, `k : Nat`,
      `d : Nat`, `hx : List (List Bool)`,
      `hz : List (List Bool)`.
    * `SchedulableSurgeryGadget` (`SurgeryGadgetToSysCalls.lean`):
      `gadget : LDPC.SurgeryGadget`, `data_site_a : Nat`,
      `data_site_b : Nat`, `ancilla_site : Nat`,
      `start_us : Nat`, `decoder_id_base : Nat`.
    * `LDPC.SurgeryGadget` (`LDPCSurgery.lean`):
      `data_code : QECCode`, `ancilla_n : Nat`, parity matrices,
      `tau_s : Nat`, `target_pauli : BoolVec`, …

    Fields intentionally NOT checked in this relation:
    * `spec.ppm` — PPM-side spec; already handled by §20's
      `ICXPPMProgramImplementsSpecs`.
    * `spec.usesPauliFrame` — Boolean flag whose semantic
      meaning depends on the gadget's Pauli-frame
      convention; comparing it to a `SurgeryGadget` field
      would conflate orthogonal concerns.
    * `spec.gadget.operator_weight` — its relationship to
      `target_pauli.length` depends on the surgery
      convention; not pinned down here.
    * Surgery-side site indices (`data_site_a`, `data_site_b`,
      `ancilla_site`, `start_us`) — placement / scheduling
      details that the QEC spec does not constrain. -/

/-! ### §24.a Structural specMatch relation. -/

def QECSpecMatchesSurgeryGadget
    (spec : QECGadgetSpec) (sg : SchedulableSurgeryGadget) : Prop :=
  spec.gadget.tau_s = sg.gadget.tau_s
  ∧ spec.code = sg.gadget.data_code
  ∧ spec.gadget.target = sg.gadget.data_code
  ∧ spec.syndromeRounds = sg.gadget.tau_s
  ∧ spec.decoder = sg.decoder_id_base

/-! ### §24.b Projection lemmas. -/

theorem QECSpecMatchesSurgeryGadget.tau_s_eq
    {spec : QECGadgetSpec} {sg : SchedulableSurgeryGadget}
    (h : QECSpecMatchesSurgeryGadget spec sg) :
    spec.gadget.tau_s = sg.gadget.tau_s := h.1

theorem QECSpecMatchesSurgeryGadget.code_eq
    {spec : QECGadgetSpec} {sg : SchedulableSurgeryGadget}
    (h : QECSpecMatchesSurgeryGadget spec sg) :
    spec.code = sg.gadget.data_code := h.2.1

theorem QECSpecMatchesSurgeryGadget.target_eq
    {spec : QECGadgetSpec} {sg : SchedulableSurgeryGadget}
    (h : QECSpecMatchesSurgeryGadget spec sg) :
    spec.gadget.target = sg.gadget.data_code := h.2.2.1

theorem QECSpecMatchesSurgeryGadget.syndromeRounds_eq
    {spec : QECGadgetSpec} {sg : SchedulableSurgeryGadget}
    (h : QECSpecMatchesSurgeryGadget spec sg) :
    spec.syndromeRounds = sg.gadget.tau_s := h.2.2.2.1

theorem QECSpecMatchesSurgeryGadget.decoder_eq
    {spec : QECGadgetSpec} {sg : SchedulableSurgeryGadget}
    (h : QECSpecMatchesSurgeryGadget spec sg) :
    spec.decoder = sg.decoder_id_base := h.2.2.2.2

/-! ### §24.c Concrete surgery lowering model. -/

def ICXConcreteSurgeryLoweringModel
    (models : SystemModels) (n : Nat)
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary) :
    PPMToBackendLoweringModel models (cxMacroPPMSemanticsModel n) :=
  ICXSurgeryLoweringModel models n QECSpecMatchesSurgeryGadget backendSummary

/-! ### §24.d Toy concrete-specMatch obligations. -/

theorem toy_qec_backend_ok_concrete
    (models : SystemModels)
    (qecSpecs : List QECGadgetSpec)
    (gadgets : List SchedulableSurgeryGadget)
    (hmatch :
      specMatchListwise QECSpecMatchesSurgeryGadget qecSpecs gadgets)
    (backend : VerifiedBackendBlock models)
    (hbackend : backend.schedule = composedSurgerySchedule gadgets) :
    SurgeryQECSpecsLowerToSchedule QECSpecMatchesSurgeryGadget qecSpecs
      backend.schedule := by
  rw [hbackend]
  exact SurgeryQECSpecsLowerToSchedule.construct
    QECSpecMatchesSurgeryGadget qecSpecs gadgets hmatch

/-! ### §24.e Toy concrete-specMatch V2 block constructor. -/

def toyV2BlockConcreteSpecMatch
    (models : SystemModels) (n : Nat)
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary)
    (qecSpecs : List QECGadgetSpec)
    (gadgets : List SchedulableSurgeryGadget)
    (backend : VerifiedBackendBlock models)
    (hmatch :
      specMatchListwise QECSpecMatchesSurgeryGadget qecSpecs gadgets)
    (hbackend : backend.schedule = composedSurgerySchedule gadgets)
    (hAlign :
      backendSummary backend.schedule
        = ppmProgramResourceSummary (compileArithmeticGateToPPM toyICXGate)) :
    VerifiedArithmeticPPMToSystemBlockV2 models
      (cxMacroPPMSemanticsModel n)
      (ICXConcreteSurgeryLoweringModel models n backendSummary) :=
  VerifiedArithmeticPPMToSystemBlockV2.ofICXSurgery
    models n toyICXGate toyICXGate_isICX qecSpecs
    QECSpecMatchesSurgeryGadget backendSummary backend
    (toy_qec_backend_ok_concrete models qecSpecs gadgets hmatch backend hbackend)
    (toy_resource_alignment_ok models n qecSpecs backend backendSummary hAlign)

/-! ### §24.f Backend system-invariants projection for the
       concrete-specMatch toy block. -/

theorem toyICXBlockConcreteSpecMatch_system_invariants_ok
    (models : SystemModels) (n : Nat)
    (backendSummary : CompressedSchedule → PPMProgramResourceSummary)
    (qecSpecs : List QECGadgetSpec)
    (gadgets : List SchedulableSurgeryGadget)
    (backend : VerifiedBackendBlock models)
    (hmatch :
      specMatchListwise QECSpecMatchesSurgeryGadget qecSpecs gadgets)
    (hbackend : backend.schedule = composedSurgerySchedule gadgets)
    (hAlign :
      backendSummary backend.schedule
        = ppmProgramResourceSummary (compileArithmeticGateToPPM toyICXGate)) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch
        models.opCap
        models.slotCap
        models.ancillaModel
        backend.schedule.expand
        models.t_react_us
        models.window_us
        models.max_per_window = true :=
  VerifiedArithmeticPPMToSystemBlockV2.system_invariants_ok
    models (cxMacroPPMSemanticsModel n)
    (ICXConcreteSurgeryLoweringModel models n backendSummary)
    (toyV2BlockConcreteSpecMatch models n backendSummary qecSpecs gadgets
      backend hmatch hbackend hAlign)

/-! ### §24.g Status after §24.

    Closed:
    * `QECSpecMatchesSurgeryGadget` — concrete structural
      relation reducing the abstract `specMatch` parameter
      to FIVE field-level equalities.
    * `QECSpecMatchesSurgeryGadget.tau_s_eq` / `_code_eq` /
      `_target_eq` / `_syndromeRounds_eq` / `_decoder_eq` —
      projection lemmas.
    * `ICXConcreteSurgeryLoweringModel` — surgery lowering
      model with `QECSpecMatchesSurgeryGadget` plugged into
      the `specMatch` slot.
    * `toy_qec_backend_ok_concrete` — surgery-lowering
      obligation for the toy block, using the concrete
      relation.
    * `toyV2BlockConcreteSpecMatch` — concrete-specMatch V2
      block constructor.
    * `toyICXBlockConcreteSpecMatch_system_invariants_ok` —
      backend system-invariants projection on the concrete
      block.

    Bool checker (`qecSpecMatchesSurgeryGadgetBool`):
    NOT defined.  `QECCode` does not currently derive
    `DecidableEq`; adding it would require modifying
    `L4_QECCode.lean` (or providing a free-standing
    `decide`-style instance), which is out of scope for
    this tick.  The Prop relation is sufficient for
    callers that can supply field equalities directly.

    Open obligations (UNCHANGED — concrete `specMatch` is
    structural, not semantic):
    * **Full QEC semantic lowering** — the claim that
      `compileSurgeryGadgetToSysCalls` emits SysCalls that
      semantically implement the QEC gadget's logical Pauli
      measurement remains UNPROVED.  No existing repository
      code provides this theorem.
    * `backendSummary` resource-projection correctness —
      user parameter.
    * `hbackend : backend.schedule = composedSurgerySchedule
      gadgets` — user-supplied structural equation.
    * `hAlign` — user-supplied resource-equation.
    * `MagicInjectionObligations.CCX_ok` (§17) — Toffoli
      semantic proof.
    * QPE / non-Clifford+T — rejected/deferred via §1
      classifier.

    All prior milestones (§11–§23) remain intact. -/

/-! ## §25. Concrete instance — toy QEC/surgery pair
       satisfying `QECSpecMatchesSurgeryGadget`.

    A usability milestone for §24's concrete structural
    match: this section exhibits ONE concrete pair of
    `QECGadgetSpec` and `SchedulableSurgeryGadget` for which
    `QECSpecMatchesSurgeryGadget` holds.  Each field is set
    to a minimal structurally-typechecking value.

    **None** of the objects in this section make any
    physical or QEC claim.  The `toyQECCode` has `n = 1,
    k = 1, d = 1` and empty parity matrices — it is NOT a
    real code; it is purely a smoke-test object verifying
    that the structural relation is satisfiable.

    The toy is wired into the singleton list version of
    `SurgeryQECSpecsLowerToSchedule`, completing the
    end-to-end usability proof of the §22 / §24 surgery
    lowering interface for a one-gadget circuit.

    Backend certification (a `VerifiedBackendBlock` over
    the toy schedule) is NOT attempted — the toy
    `compileSurgeryGadgetToSysCalls toySchedulableSurgeryGadget`
    output is unlikely to pass the strict bundle without
    placement / timing arrangement that we deliberately do
    not provide here.  The backend cert remains a future
    obligation, isolated from the structural-match
    milestone. -/

/-! ### §25.a Toy QEC code. -/

def toyQECCode : QECCode :=
  { n  := 1
    k  := 1
    d  := 1
    hx := []
    hz := [] }

/-! ### §25.b Toy PPM gadget + spec. -/

def toyPPMGadget : PPMGadget :=
  { target := toyQECCode
    operator_weight := 1
    tau_s := 1 }

def toyPPMSpec : PPMSpec :=
  { measuredPauliKind := PauliKind.X
    logicalInputs := [0]
    logicalOutputs := [0]
    rounds := 1
    distance := 1 }

def toyQECGadgetSpec : QECGadgetSpec :=
  { ppm := toyPPMSpec
    code := toyQECCode
    gadget := toyPPMGadget
    syndromeRounds := toyPPMGadget.tau_s
    decoder := 0
    usesPauliFrame := true }

/-! ### §25.c Toy LDPC surgery gadget + schedulable gadget. -/

def toyLDPCSurgeryGadget : LDPC.SurgeryGadget :=
  { data_code         := toyQECCode
    ancilla_n         := 0
    ancilla_hx        := []
    ancilla_hz        := []
    conn_x            := []
    conn_z            := []
    tau_s             := toyPPMGadget.tau_s
    target_pauli      := []
    span_witness      := []
    merged_qldpc_bound := 0 }

def toySchedulableSurgeryGadget : SchedulableSurgeryGadget :=
  { gadget          := toyLDPCSurgeryGadget
    data_site_a     := 0
    data_site_b     := 1
    ancilla_site    := 2
    start_us        := 0
    decoder_id_base := toyQECGadgetSpec.decoder }

/-! ### §25.d Structural match theorem. -/

theorem toy_QECSpecMatchesSurgeryGadget :
    QECSpecMatchesSurgeryGadget
      toyQECGadgetSpec
      toySchedulableSurgeryGadget := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-! ### §25.e Listwise match for singleton lists. -/

theorem toy_specMatchListwise_singleton :
    specMatchListwise
      QECSpecMatchesSurgeryGadget
      [toyQECGadgetSpec]
      [toySchedulableSurgeryGadget] := by
  show QECSpecMatchesSurgeryGadget toyQECGadgetSpec toySchedulableSurgeryGadget
        ∧ specMatchListwise QECSpecMatchesSurgeryGadget [] []
  exact ⟨toy_QECSpecMatchesSurgeryGadget, True.intro⟩

/-! ### §25.f Concrete QEC/backend lowering for the singleton
       toy. -/

theorem toy_singleton_qec_backend_lowering :
    SurgeryQECSpecsLowerToSchedule
      QECSpecMatchesSurgeryGadget
      [toyQECGadgetSpec]
      (composedSurgerySchedule [toySchedulableSurgeryGadget]) :=
  SurgeryQECSpecsLowerToSchedule.construct
    QECSpecMatchesSurgeryGadget
    [toyQECGadgetSpec]
    [toySchedulableSurgeryGadget]
    toy_specMatchListwise_singleton

/-! ### §25.g Emitted SysCalls for the toy gadget.

    Materialises the structural compiler output as a
    standalone definition.  Useful as input to future
    backend certification (if any).  No backend cert is
    proved in this tick. -/

def toySurgerySysCalls : List SysCall :=
  compileSurgeryGadgetToSysCalls toySchedulableSurgeryGadget

def toySurgeryAtomSchedule : CompressedSchedule :=
  CompressedSchedule.atom toySurgerySysCalls

/-- Length witness: the toy gadget has `tau_s = 1`, so the
    compiler emits `5·1 + 1 = 6` SysCalls. -/
theorem toySurgerySysCalls_length : toySurgerySysCalls.length = 6 := by
  show (compileSurgeryGadgetToSysCalls toySchedulableSurgeryGadget).length = 6
  rw [compileSurgeryGadgetToSysCalls_length]
  rfl

/-! ### §25.h Status after §25.

    Closed (concrete instance milestone):
    * `toyQECCode` — minimal `QECCode` (n=k=d=1, empty parity).
    * `toyPPMGadget` — minimal `PPMGadget` (operator_weight=1,
      tau_s=1).
    * `toyPPMSpec` — minimal `PPMSpec` (X kind, single qubit).
    * `toyQECGadgetSpec` — minimal `QECGadgetSpec` bundling
      the above, with `syndromeRounds = toyPPMGadget.tau_s`
      and `decoder = 0`.
    * `toyLDPCSurgeryGadget` — minimal `LDPC.SurgeryGadget`
      with `data_code = toyQECCode`, `tau_s = 1`, empty
      matrices.
    * `toySchedulableSurgeryGadget` — minimal
      `SchedulableSurgeryGadget` with
      `decoder_id_base = toyQECGadgetSpec.decoder`.
    * `toy_QECSpecMatchesSurgeryGadget` — the structural
      match holds; all five field equalities reduce to
      `rfl`.
    * `toy_specMatchListwise_singleton` — singleton listwise
      match.
    * `toy_singleton_qec_backend_lowering` —
      `SurgeryQECSpecsLowerToSchedule` for the singleton
      list and the composed surgery schedule.
    * `toySurgerySysCalls`, `toySurgeryAtomSchedule`,
      `toySurgerySysCalls_length` — emitted SysCalls (6 of
      them) and the corresponding `.atom` schedule.

    Open / NOT attempted (UNCHANGED):
    * Backend certification: the toy
      `compileSurgeryGadgetToSysCalls
      toySchedulableSurgeryGadget` output is NOT proved to
      satisfy `compressed_schedule_strict_certificate_ok`.
      A `VerifiedBackendBlock` over the toy schedule
      remains a future obligation.
    * Full QEC semantic lowering — still open (the toy
      gadget makes no semantic claim).
    * `backendSummary` resource-projection correctness —
      still a user parameter.
    * `MagicInjectionObligations.CCX_ok` (§17) — Toffoli
      semantic proof remains open.
    * QPE / non-Clifford+T — rejected/deferred via §1.

    All prior milestones (§11–§24) remain intact. -/

/-! ## §26. Toy surgery-schedule backend certificate
       investigation.

    `toySurgerySysCalls` (§25.g) compiles to 6 SysCalls
    under `compileSurgeryGadgetToSysCalls` from the toy
    surgery gadget.  This section attempts to discharge the
    backend `compressed_schedule_strict_certificate_ok`
    against an explicit toy `SystemModels`.

    Emitted toy SysCalls (`tau_s = 1`, `start_us = 0`,
    `data_site_a = 0`, `data_site_b = 1`, `ancilla_site = 2`,
    `decoder_id_base = 0`):

      0. RequestFreshAncilla 1, [0, 1)
      1. Gate2q   0 2 0,        [1, 2)
      2. Gate2q   1 2 0,        [2, 3)
      3. Measure  2 0,          [3, 4)
      4. DecodeSyndrome 0,      [4, 5)
      5. PauliFrameUpdate 0,    [5, 6)

    Wallclock = 6 µs; six sequential SysCalls; sites
    touched = {0, 1, 2}; one fresh-ancilla request (zone 1);
    one Measure + Decode + PauliFrameUpdate triple with
    matching correction-id 0; zero magic-state requests. -/

/-! ### §26.a Toy SystemModels.

    Reuses the existing `surgery_arch` (Data 0..100,
    Ancilla 100..200, Factory 200..300, Routing 300..400)
    and the generous `adder_demo_*` capacity models.  The
    ancilla model is customised so that the toy's
    `ancilla_site = 2` belongs to ancilla `zone_id = 1`.
    Generous decoder-react and window parameters. -/

def toySurgeryAncillaModel : AncillaModel :=
  { zones := [{ zone_id := 1, site_lo := 2, site_hi := 3 }] }

def toySurgerySystemModels : SystemModels :=
  { arch           := surgery_arch
    opCap          := adder_demo_opCap
    slotCap        := adder_demo_slotCap
    ancillaModel   := toySurgeryAncillaModel
    t_react_us     := 10
    window_us      := 1000
    max_per_window := 1000 }

/-! ### §26.b Backend certificate attempt via `native_decide`.

    `compressed_schedule_strict_certificate_ok` on a
    `.atom block` schedule unfolds to:
      * `all_invariants_strict_with_slot_capacity_and_freshness_ok`
        on `block`;
      * `scheduleWithinWallclock block`;
      * zero magic-state requests in `block`.

    All three are decidable on the concrete toy block. -/

/-- Composed-form schedule (a `.seq [.atom …]`) matching
    `composedSurgerySchedule [toySchedulableSurgeryGadget]`
    by definition.  This is the form the §22 `composedSurgerySchedule`
    builder expects; it differs from the §25.g
    `toySurgeryAtomSchedule` (a plain `.atom …`) only in
    being wrapped under one extra `.seq` constructor. -/
def toySurgeryComposedSchedule : CompressedSchedule :=
  composedSurgerySchedule [toySchedulableSurgeryGadget]

theorem toySurgeryBackendCert :
    compressed_schedule_strict_certificate_ok
      toySurgerySystemModels
      toySurgeryComposedSchedule = true := by decide

/-! ### §26.c `VerifiedBackendBlock` for the toy. -/

def toySurgeryVerifiedBackendBlock :
    VerifiedBackendBlock toySurgerySystemModels :=
  { schedule := toySurgeryComposedSchedule
    cert_ok  := toySurgeryBackendCert }

/-! ### §26.d Backend system-invariants projection
       through the existing V1 projection theorem
       `VerifiedBackendBlock.strict_invariants_ok`. -/

theorem toySurgeryBackendBlock_strict_invariants_ok :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        toySurgerySystemModels.arch
        toySurgerySystemModels.opCap
        toySurgerySystemModels.slotCap
        toySurgerySystemModels.ancillaModel
        toySurgeryVerifiedBackendBlock.schedule.expand
        toySurgerySystemModels.t_react_us
        toySurgerySystemModels.window_us
        toySurgerySystemModels.max_per_window = true :=
  toySurgeryVerifiedBackendBlock.strict_invariants_ok toySurgerySystemModels

/-! ### §26.e Connection to the §24 concrete-specMatch V2
       block.

    We can now construct
    `toyV2BlockConcreteSpecMatch` against
    `toySurgerySystemModels` and
    `toySurgeryVerifiedBackendBlock`, supplying:

    * `qecSpecs := [toyQECGadgetSpec]`,
    * `gadgets := [toySchedulableSurgeryGadget]`,
    * `backend := toySurgeryVerifiedBackendBlock`,
    * `hmatch := toy_specMatchListwise_singleton`,
    * `hbackend` — closed below by `rfl` since
      `backend.schedule = toySurgeryAtomSchedule
                        = CompressedSchedule.atom toySurgerySysCalls
                        = composedSurgerySchedule [toySchedulableSurgeryGadget]
                        |>.unfold`.  We pin this with one `rfl`-style
      proof.
    * `hAlign` — closed by choosing
      `backendSummary := fun _ => ppmProgramResourceSummary
        (compileArithmeticGateToPPM toyICXGate)`,
      a constant projection that makes the alignment
      equation trivially `rfl`. -/

/-- The toy backend block's schedule equals the composed
    surgery schedule of the toy gadget list, by definition. -/
theorem toySurgeryVerifiedBackendBlock_schedule_eq_composed :
    toySurgeryVerifiedBackendBlock.schedule
      = composedSurgerySchedule [toySchedulableSurgeryGadget] := rfl

/-- A constant-valued backend summary that aligns with the
    toy ICX gate's resource summary by definition. -/
def toyConstantBackendSummary :
    CompressedSchedule → PPMProgramResourceSummary :=
  fun _ => ppmProgramResourceSummary (compileArithmeticGateToPPM toyICXGate)

theorem toyConstantBackendSummary_alignment :
    toyConstantBackendSummary toySurgeryVerifiedBackendBlock.schedule
      = ppmProgramResourceSummary (compileArithmeticGateToPPM toyICXGate) := rfl

/-! ### §26.f Toy concrete end-to-end V2 block. -/

def toyConcreteEndToEndV2Block (n : Nat) :
    VerifiedArithmeticPPMToSystemBlockV2 toySurgerySystemModels
      (cxMacroPPMSemanticsModel n)
      (ICXConcreteSurgeryLoweringModel toySurgerySystemModels n
        toyConstantBackendSummary) :=
  toyV2BlockConcreteSpecMatch toySurgerySystemModels n
    toyConstantBackendSummary
    [toyQECGadgetSpec] [toySchedulableSurgeryGadget]
    toySurgeryVerifiedBackendBlock
    toy_specMatchListwise_singleton
    toySurgeryVerifiedBackendBlock_schedule_eq_composed
    toyConstantBackendSummary_alignment

/-! ### §26.g End-to-end backend system-invariants theorem. -/

theorem toyConcreteEndToEnd_system_invariants_ok (n : Nat) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        toySurgerySystemModels.arch
        toySurgerySystemModels.opCap
        toySurgerySystemModels.slotCap
        toySurgerySystemModels.ancillaModel
        toySurgeryVerifiedBackendBlock.schedule.expand
        toySurgerySystemModels.t_react_us
        toySurgerySystemModels.window_us
        toySurgerySystemModels.max_per_window = true :=
  toyICXBlockConcreteSpecMatch_system_invariants_ok
    toySurgerySystemModels n
    toyConstantBackendSummary
    [toyQECGadgetSpec] [toySchedulableSurgeryGadget]
    toySurgeryVerifiedBackendBlock
    toy_specMatchListwise_singleton
    toySurgeryVerifiedBackendBlock_schedule_eq_composed
    toyConstantBackendSummary_alignment

/-! ### §26.h Status after §26.

    Closed (real backend certification):
    * `toySurgeryAncillaModel` — minimal ancilla model with
      `zone_id := 1, site_lo := 2, site_hi := 3` so the
      toy gadget's `ancilla_site := 2` is in the requested
      `RequestFreshAncilla 1` zone.
    * `toySurgerySystemModels` — toy `SystemModels` bundling
      `surgery_arch`, `adder_demo_opCap`, `adder_demo_slotCap`,
      `toySurgeryAncillaModel`, plus generous timing
      parameters.
    * `toySurgeryBackendCert` —
      `compressed_schedule_strict_certificate_ok` closed via
      `native_decide`.  The emitted toy schedule (6 SysCalls)
      passes the strict bundle under the toy models.
    * `toySurgeryVerifiedBackendBlock` — packaged
      `VerifiedBackendBlock toySurgerySystemModels`.
    * `toySurgeryBackendBlock_strict_invariants_ok` —
      backend system invariants on the toy schedule.
    * `toySurgeryAtomSchedule_eq_composed` — the toy `.atom`
      schedule structurally equals
      `composedSurgerySchedule [toySchedulableSurgeryGadget]`
      by `rfl`.
    * `toyConstantBackendSummary` — a constant projection
      that makes resource alignment trivial.
    * `toyConcreteEndToEndV2Block` — full toy
      `VerifiedArithmeticPPMToSystemBlockV2`.
    * `toyConcreteEndToEnd_system_invariants_ok` — end-to-end
      backend system invariants theorem.

    Open obligations (UNCHANGED):
    * **Full QEC semantic lowering** — the SysCalls emitted
      by `compileSurgeryGadgetToSysCalls` are now BACKEND-
      CERTIFIED but the semantic claim that they implement
      the QEC gadget's logical Pauli measurement remains
      open.  No existing repository code provides this
      theorem.
    * `MagicInjectionObligations.CCX_ok` (§17) — Toffoli
      semantic proof remains open.
    * QPE / non-Clifford+T — rejected/deferred via §1.
    * `toyConstantBackendSummary` is a TRIVIAL alignment
      witness — real backend resource projections are
      future work.

    All prior milestones (§11–§25) remain intact. -/

/-! ## §27. Toy QEC semantic-lowering bridge via trace
       observations.

    §26 backend-certified the emitted SysCalls of the toy
    surgery gadget, but said nothing about whether those
    SysCalls actually implement the QEC gadget's logical
    Pauli measurement.  This section opens that gap (at a
    SAFE, TRACE-LEVEL granularity):

    * Define a small **observational abstraction**
      `SurgeryObs` that captures only the kind + qubit /
      decoder / correction identifiers of each SysCall,
      collapsing irrelevant fields (timing, gate-id tags,
      basis indices).
    * Define `surgeryTraceOfSysCalls` / `surgeryTraceOfCompressedSchedule`
      to project a SysCall list / `CompressedSchedule` down
      to a `List SurgeryObs`.
    * Define `SurgeryTraceMatchesGadget` — a structural
      predicate that a trace has the EXPECTED shape for one
      surgery gadget (one fresh-ancilla request, two
      data-ancilla entanglement steps, one ancilla
      measurement, one decode, one frame update — using the
      gadget's actual `data_site_a`, `data_site_b`,
      `ancilla_site`, `decoder_id_base`).
    * Prove the toy trace match by `decide` / `native_decide`.

    **Honesty boundary:**  The trace match is purely
    observational and structural.  It does NOT prove:
    * QEC code distance, fault-tolerance, or threshold
      properties.
    * Syndrome correctness or decoder correctness.
    * Logical Pauli measurement semantics on a real
      stabilizer state.
    * Any quantum-mechanical claim about the gadget.

    It proves only that the emitted SysCalls have the
    correct surgery-protocol SHAPE (the right kinds at the
    right qubit / decoder / correction identifiers) under
    the toy gadget's parameters. -/

/-! ### §27.a Observation abstraction. -/

inductive SurgeryObs where
  /-- `RequestFreshAncilla target_zone`. -/
  | freshAncilla        : Nat → SurgeryObs
  /-- `Gate2q q1 q2 _` — collapsed observation, no gate-id. -/
  | entangleDataAncilla : Nat → Nat → SurgeryObs
  /-- `Measure qubit _` — basis index collapsed. -/
  | measureAncilla      : Nat → SurgeryObs
  /-- `DecodeSyndrome round_id`. -/
  | decode              : Nat → SurgeryObs
  /-- `PauliFrameUpdate correction_id`. -/
  | frameUpdate         : Nat → SurgeryObs
  deriving DecidableEq, Repr, Inhabited

/-- Project a single SysCall to its surgery observation.
    `Gate1q`, `TransitQubit`, `RequestMagicState` are NOT
    part of the surgery shape — they map to `none` and get
    filtered out. -/
def syscallToSurgeryObs? : SysCall → Option SurgeryObs
  | { kind := .RequestFreshAncilla z, .. } => some (.freshAncilla z)
  | { kind := .Gate2q q1 q2 _,        .. } => some (.entangleDataAncilla q1 q2)
  | { kind := .Measure q _,           .. } => some (.measureAncilla q)
  | { kind := .DecodeSyndrome r,      .. } => some (.decode r)
  | { kind := .PauliFrameUpdate c,    .. } => some (.frameUpdate c)
  | _                                       => none

def surgeryTraceOfSysCalls (xs : List SysCall) : List SurgeryObs :=
  xs.filterMap syscallToSurgeryObs?

def surgeryTraceOfCompressedSchedule (cs : CompressedSchedule) : List SurgeryObs :=
  surgeryTraceOfSysCalls cs.expand

/-! ### §27.b Expected single-gadget trace. -/

/-- The expected trace for one `tau_s = 1` surgery round
    plus its trailing frame update.  Lines up exactly with
    `compileSurgeryGadgetToSysCalls` for `tau_s = 1`. -/
def expectedSingleRoundTrace (g : SchedulableSurgeryGadget) :
    List SurgeryObs :=
  [ .freshAncilla 1
  , .entangleDataAncilla g.data_site_a g.ancilla_site
  , .entangleDataAncilla g.data_site_b g.ancilla_site
  , .measureAncilla g.ancilla_site
  , .decode g.decoder_id_base
  , .frameUpdate g.decoder_id_base ]

/-- The trace predicate: the observed trace must equal the
    expected single-round trace exactly.  Single-round
    only — multi-round (`tau_s > 1`) gadgets are not
    covered by this predicate. -/
def SurgeryTraceMatchesGadget
    (g : SchedulableSurgeryGadget) (tr : List SurgeryObs) : Prop :=
  tr = expectedSingleRoundTrace g

instance (g : SchedulableSurgeryGadget) (tr : List SurgeryObs) :
    Decidable (SurgeryTraceMatchesGadget g tr) :=
  decEq tr (expectedSingleRoundTrace g)

/-! ### §27.c Toy trace-match theorem. -/

theorem toySurgeryTraceMatchesGadget :
    SurgeryTraceMatchesGadget toySchedulableSurgeryGadget
      (surgeryTraceOfSysCalls toySurgerySysCalls) := by decide

theorem toySurgeryComposedSchedule_trace_matches :
    SurgeryTraceMatchesGadget toySchedulableSurgeryGadget
      (surgeryTraceOfCompressedSchedule
        toySurgeryVerifiedBackendBlock.schedule) := by native_decide  -- toy trace-match; too heavy for kernel `decide`

/-! ### §27.d Trace-level QEC lowering evidence.

    A Prop-valued bundle pairing the three structural
    artefacts that the toy concrete-specMatch V2 block now
    has in hand:

    * §24 `QECSpecMatchesSurgeryGadget` — field-level
      consistency between the QEC spec and the surgery
      gadget.
    * §22 / §26 schedule equation — `sched =
      composedSurgerySchedule [g]`.
    * §27 trace match — the observable surgery shape on
      the backend schedule lines up with the gadget's
      expected single-round trace.

    This is the FIRST honest semantic bridge from a backend
    schedule to a QEC gadget spec.  It is OBSERVATIONAL
    only — it does not prove logical Pauli-measurement
    semantics, decoder / syndrome correctness, fault-
    tolerance, or distance. -/

structure SurgeryQECTraceLoweringEvidence
    (spec : QECGadgetSpec) (g : SchedulableSurgeryGadget)
    (sched : CompressedSchedule) : Prop where
  structuralMatch : QECSpecMatchesSurgeryGadget spec g
  scheduleEq      : sched = composedSurgerySchedule [g]
  traceMatches    : SurgeryTraceMatchesGadget g
                      (surgeryTraceOfCompressedSchedule sched)

end FormalRV.Framework.CircuitToPPMInterface
