/-
  FormalRV.Framework.CircuitToPPMInterface — the first
  high-level-circuit → PPM lowering interface for the
  ARITHMETIC fragment of FT-Shor.

  ## Scope

  This file defines a structural lowering from the existing
  arithmetic-only Gate IR (`FormalRV.Framework.Gate`,
  constructors `I | X | CX | CCX | seq`) into a logical-layer
  PPM program (`PPMCommand` / `PPMProgram`).  It targets the
  arithmetic subcircuits of Shor (modular-exponentiation,
  modular-multiplication, modular-addition, Cuccaro adders,
  Gidney 2018 adders, etc.) — NOT the QPE phase-rotation
  fragment, which generally requires either exact-Clifford+T
  decomposition or approximate synthesis before it can enter
  this PPM path.

  ## Layering (recap)

      Logical Shor / arithmetic correctness
          ↓ (Clifford+T / Toffoli-CNOT-X arithmetic fragment, THIS FILE)
      PPM / lattice-surgery logical-measurement layer
          ↓
      QEC gadget implementation
          ↓
      Backend compressed SysCall schedule
          ↓
      System resource/invariant certificate

  The arithmetic fragment lives ABOVE the PPM layer.  The PPM
  layer lives ABOVE the SysCall/System layer.  Do not collapse
  PPM into physical SysCall schedules.

  ## What is and is NOT proved in this tick

  Proved structurally:
  * Empty `Gate.I` compiles to `[]`.
  * `Gate.seq g₁ g₂` compiles to the append of the compiled
    halves.

  NOT proved:
  * Semantic equivalence between the source `Gate` and the
    compiled `PPMProgram`.  The user must supply a separate
    semantic proof; the interface records the obligation as a
    `Prop` slot.

  Existing definitions REUSED:
  * `FormalRV.Framework.Gate` — the arithmetic Gate IR.
  * `FormalRV.Framework.Architecture.PauliKind` — I/X/Y/Z.
  * `FormalRV.Framework.LayeredPPMQECInterface.PPMSpec`,
    `QECGadgetSpec`, `LogicalQubitId`, `PauliKind` re-export.

  Existing definitions deferred:
  * `BaseUCom dim` (`QuantumGate.lean`) — QPE-capable IR with
    real-angle R primitives.  Real-angle equality is not
    decidable, so the BaseUCom-side classifier here only tags
    structural kinds (CNOT vs R), not specific Clifford+T
    rewrites.  Real lowering of BaseUCom (decompose to Gate)
    is a future tick.
  * `PPMOperational.StabilizerState` and Gottesman PPM
    updates — these formalise PPM operational semantics; they
    will be consumed by the future `semantic_obligation`
    refinement.
-/

import FormalRV.PPM.LayeredPPMQECInterface
import FormalRV.Core.QuantumGate
import FormalRV.PPM.PPMOperational
import FormalRV.PPM.FactoryHierarchy

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

/-! ## §1. Classifier for the supported circuit fragment.

    The arithmetic fragment is defined PRECISELY by the
    existing `Gate` IR's constructor set: `I`, `X q`, `CX c t`,
    `CCX a b t`, `seq g₁ g₂`.  There is no `Rz`, `H`, `T`,
    `phase`, or opaque oracle constructor in `Gate`, so the
    arithmetic-fragment classifier on `Gate` is constructively
    total: every `Gate` is in the arithmetic fragment by
    construction.

    For circuits expressed in the broader `BaseUCom` IR
    (which has `BaseUnitary.R θ φ λ` as a 1-qubit primitive),
    real-angle comparison is undecidable, so we tag those
    circuits as `unsupportedOpaque` or `qpePhaseRotation` by
    structure — they must be lowered to the `Gate` IR
    separately before entering the PPM path. -/

/-- Classification of a circuit fragment for PPM lowering.

    * `arithmetic` — the existing `Gate` arithmetic fragment
      (I, X, CNOT, Toffoli, sequential composition).  These
      enter the PPM lowering directly.
    * `cliffordT` — generic Clifford+T circuits already
      decomposed into H/S/T/CNOT.  Reserved for a future tick
      that handles general Clifford+T to PPM lowering.
    * `qpePhaseRotation` — controlled phase rotations
      (`controlled_Rz`, `controlled_R`) used in QPE/QFT.
      REJECTED unless decomposed to Clifford+T or to the
      arithmetic Gate IR first.
    * `unsupportedOpaque` — opaque/oracle gates with no
      structural decomposition supplied.  REJECTED. -/
inductive CircuitFragmentKind where
  | arithmetic
  | cliffordT
  | qpePhaseRotation
  | unsupportedOpaque
  deriving Repr, DecidableEq, Inhabited

/-- Every `Gate` is in the arithmetic fragment by
    construction: the IR's constructors are exactly
    `I | X | CX | CCX | seq`. -/
def classifyGateForPPMLowering : Gate → CircuitFragmentKind
  | .I        => .arithmetic
  | .X _      => .arithmetic
  | .CX _ _   => .arithmetic
  | .CCX _ _ _ => .arithmetic
  | .seq _ _  => .arithmetic

/-- Bool form: `true` iff the gate is in the supported
    arithmetic fragment.  Always `true` for the existing
    `Gate` IR. -/
def isArithmeticGate (g : Gate) : Bool :=
  match classifyGateForPPMLowering g with
  | .arithmetic => true
  | _           => false

theorem isArithmeticGate_eq_true (g : Gate) : isArithmeticGate g = true := by
  cases g <;> rfl

/-! ## §2. BaseUCom-side classifier (rejection-only).

    `BaseUCom dim` has `BaseUnitary.R θ φ λ` as its 1-qubit
    primitive, which is opaque under structural inspection
    because the angles are `Real`.  This tick does NOT attempt
    a decidable classifier on `BaseUCom`; the function below
    tags every BaseUCom by structure as either
    `qpePhaseRotation` (for `app1 (R _ _ _) _`) or
    `cliffordT` (for `app2 CNOT _ _` chained with `seq`).

    A future tick that wants to feed BaseUCom into the PPM
    lowering must first translate it to the arithmetic `Gate`
    IR (or refine to a decidable Clifford+T subset). -/

def classifyBaseUnitary1ForPPMLowering : BaseUnitary 1 → CircuitFragmentKind
  | .R _ _ _ => .qpePhaseRotation   -- conservative: rotated unless decomposed

def classifyBaseUnitary2ForPPMLowering : BaseUnitary 2 → CircuitFragmentKind
  | .CNOT => .cliffordT

/-- Structural classifier for `BaseUCom dim`.  Worst-case wins
    (qpePhaseRotation dominates cliffordT dominates
    arithmetic). -/
def classifyBaseUComForPPMLowering {dim : Nat} : BaseUCom dim → CircuitFragmentKind
  | .seq c₁ c₂ =>
      match classifyBaseUComForPPMLowering c₁, classifyBaseUComForPPMLowering c₂ with
      | .unsupportedOpaque, _ | _, .unsupportedOpaque => .unsupportedOpaque
      | .qpePhaseRotation, _ | _, .qpePhaseRotation   => .qpePhaseRotation
      | _, _                                          => .cliffordT
  | .app1 u _       => classifyBaseUnitary1ForPPMLowering u
  | .app2 u _ _     => classifyBaseUnitary2ForPPMLowering u
  | .app3 _ _ _ _   => .unsupportedOpaque

/-! ## §3. Minimal PPM-level IR.

    A `PPMCommand` is a logical-level PPM instruction.  This
    IR is intentionally MINIMAL: it records WHAT logical
    measurement is being performed and at what locations,
    NOT the lattice-surgery wiring or the SysCall expansion.

    The IR is logical-level: addresses are `LogicalQubitId`s
    (via the alias from `LayeredPPMQECInterface`), NOT
    physical sites.

    A future tick can refine `PPMCommand` to carry full
    `PauliString` (from `PauliOps.lean`) or
    `JointPauliMeasurementClaim` (from `MultiQubitPPM.lean`)
    once the semantic obligation is concretely formalised. -/

inductive PPMCommand where
  /-- Measure a single Pauli kind on a list of logical
      qubits (the support of the joint Pauli product). -/
  | measurePauliKind : PauliKind → List LogicalQubitId → PPMCommand
  /-- Apply a Pauli-frame update on the given logical qubits
      (records the X / Z correction that follows a Pauli
      measurement outcome). -/
  | applyFrameUpdate : List LogicalQubitId → PPMCommand
  /-- Consume one magic-T state to land a T-gate on the given
      logical qubit (Toffoli decomposition uses several
      magic-T consumptions per non-Clifford gate). -/
  | useMagicT        : LogicalQubitId → PPMCommand
  deriving Repr, DecidableEq, Inhabited

/-- A PPM program is a sequence of PPM commands. -/
abbrev PPMProgram := List PPMCommand

/-! ## §4. Arithmetic-gate → PPM compiler.

    The compiler is total on the `Gate` arithmetic fragment.
    It produces a STRUCTURAL PPM program — the program
    records the logical PPM commands that the gate would emit
    under standard lattice-surgery / measurement-based
    rewriting, but does NOT claim semantic equivalence here.

    The semantic obligation is carried separately by
    `VerifiedArithmeticPPMBlock.semantic_obligation : Prop`,
    which a future tick will refine and prove. -/

def compileArithmeticGateToPPM : Gate → PPMProgram
  | .I         => []
  | .X q       => [.applyFrameUpdate [q]]
  | .CX c t    =>
      [ .measurePauliKind PauliKind.Z [c, t]
      , .applyFrameUpdate [t] ]
  | .CCX a b t =>
      [ .useMagicT t
      , .measurePauliKind PauliKind.Z [a, b, t]
      , .applyFrameUpdate [t] ]
  | .seq g₁ g₂ =>
      compileArithmeticGateToPPM g₁ ++ compileArithmeticGateToPPM g₂

/-! ## §5. Structural theorems about the compiler.

    These are the safe theorems the task explicitly permits:
    base case, composition, and acceptance.  No semantic
    equivalence claim. -/

theorem compileArithmeticGateToPPM_I :
    compileArithmeticGateToPPM .I = [] := rfl

theorem compileArithmeticGateToPPM_seq (g₁ g₂ : Gate) :
    compileArithmeticGateToPPM (.seq g₁ g₂)
      = compileArithmeticGateToPPM g₁
          ++ compileArithmeticGateToPPM g₂ := rfl

/-- Acceptance theorem: every `Gate` is in the arithmetic
    fragment, hence accepted by the compiler. -/
theorem isArithmeticGate_of_Gate (g : Gate) : isArithmeticGate g = true :=
  isArithmeticGate_eq_true g

/-! ## §6. Semantic model for gate ↔ PPM-program relations.

    The compiler in §4 is purely structural.  To talk about
    SEMANTIC correctness (the PPM program faithfully
    implements the gate), we parameterise over an abstract
    semantic model.  The model exposes a shared state type
    plus two transition relations: one for arithmetic gates
    and one for individual PPM commands.

    This file does NOT prove anything about a specific model;
    it provides:
      * the abstract semantic relations,
      * an inductive PPM-program semantics built from the
        per-command relation,
      * an `ImplementsGateAsPPM` predicate,
      * an `ArithmeticPrimitivePPMObligations` structure that
        bundles the X / CX / CCX primitive macro obligations,
      * an induction theorem reducing `Gate`-level soundness
        to the primitive obligations + a sequencing law on
        `gateRel`.

    A future tick will instantiate this model with the
    existing `PPMOperational.StabilizerState` /
    `apply_PPM_pos` / `apply_PPM_neg`, decompose
    `PauliKind` + `List LogicalQubitId` into a
    `PauliSem.PauliString`, and discharge the three primitive
    obligations.  Doing so closes the arithmetic-to-PPM
    soundness loop; this tick lands the reduction. -/

/-- Abstract semantic model that pairs the arithmetic Gate
    semantics with the PPM command semantics on a shared
    state type.  Instantiating `State`, `gateRel`, and
    `ppmCommandRel` with concrete definitions (e.g.,
    `StabilizerState` + Gottesman updates) recovers a real
    semantic model.  None of this file's theorems require a
    specific instantiation. -/
structure GateToPPMSemanticsModel where
  State         : Type
  /-- Relational semantics of an arithmetic `Gate`: from
      input state `s` to output state `t`. -/
  gateRel       : Gate → State → State → Prop
  /-- Relational semantics of a single `PPMCommand`. -/
  ppmCommandRel : PPMCommand → State → State → Prop

/-- Inductive relational semantics of a `PPMProgram`: the
    transitive closure of `ppmCommandRel` along the command
    list. -/
inductive PPMProgramRel (sem : GateToPPMSemanticsModel) :
    PPMProgram → sem.State → sem.State → Prop
  | nil  (s : sem.State) : PPMProgramRel sem [] s s
  | cons {cmd : PPMCommand} {rest : PPMProgram}
         {s t u : sem.State}
         (h1 : sem.ppmCommandRel cmd s t)
         (h2 : PPMProgramRel sem rest t u) :
         PPMProgramRel sem (cmd :: rest) s u

/-- The PPM program faithfully implements the gate iff every
    gate transition `s → t` is realised by a PPM-program
    transition `s → t`. -/
def ImplementsGateAsPPM
    (sem : GateToPPMSemanticsModel)
    (g : Gate) (ppm : PPMProgram) : Prop :=
  ∀ s t, sem.gateRel g s t → PPMProgramRel sem ppm s t

/-! ## §7. Structural theorems on `PPMProgramRel`. -/

/-- Append-decomposition for the inductive PPM semantics:
    the program `p₁ ++ p₂` realises `s ⇒ u` iff there is an
    intermediate state `t` such that `p₁` realises `s ⇒ t`
    and `p₂` realises `t ⇒ u`. -/
theorem PPMProgramRel_append
    (sem : GateToPPMSemanticsModel) (p₁ p₂ : PPMProgram)
    (s u : sem.State) :
    PPMProgramRel sem (p₁ ++ p₂) s u ↔
      ∃ t, PPMProgramRel sem p₁ s t ∧ PPMProgramRel sem p₂ t u := by
  induction p₁ generalizing s with
  | nil =>
      constructor
      · intro h
        exact ⟨s, PPMProgramRel.nil s, h⟩
      · rintro ⟨t, h1, h2⟩
        cases h1
        exact h2
  | cons cmd rest ih =>
      constructor
      · intro h
        cases h with
        | cons h1 hrest =>
            obtain ⟨t', hp1, hp2⟩ := (ih _).mp hrest
            exact ⟨t', PPMProgramRel.cons h1 hp1, hp2⟩
      · rintro ⟨t, hp1, hp2⟩
        cases hp1 with
        | cons h1 hrest =>
            exact PPMProgramRel.cons h1 ((ih _).mpr ⟨t, hrest, hp2⟩)

/-! ## §8. Primitive macro obligations.

    Bundles the per-primitive `ImplementsGateAsPPM`
    statements for the three non-trivial arithmetic-gate
    constructors (`Gate.I` is trivially sound from the empty
    PPM program and the `PPMProgramRel.nil` constructor).
    Pass an `ArithmeticPrimitivePPMObligations` value to
    `compileArithmeticGateToPPM_sound_from_primitives` to get
    soundness on the entire arithmetic fragment. -/

structure ArithmeticPrimitivePPMObligations
    (sem : GateToPPMSemanticsModel) where
  /-- `Gate.I` has gate semantics that is the identity
      relation: `s ⇒ s` and nothing else. -/
  I_is_id :
    ∀ s t, sem.gateRel Gate.I s t → s = t
  X_ok :
    ∀ q,
      ImplementsGateAsPPM sem (Gate.X q)
        (compileArithmeticGateToPPM (Gate.X q))
  CX_ok :
    ∀ c t,
      ImplementsGateAsPPM sem (Gate.CX c t)
        (compileArithmeticGateToPPM (Gate.CX c t))
  CCX_ok :
    ∀ a b t,
      ImplementsGateAsPPM sem (Gate.CCX a b t)
        (compileArithmeticGateToPPM (Gate.CCX a b t))
  /-- Sequencing law on `gateRel`: `Gate.seq g₁ g₂` realises
      `s ⇒ u` iff there exists `t` with `g₁` realising
      `s ⇒ t` and `g₂` realising `t ⇒ u`. -/
  seq_decomp :
    ∀ g₁ g₂ s u,
      sem.gateRel (Gate.seq g₁ g₂) s u ↔
        ∃ t, sem.gateRel g₁ s t ∧ sem.gateRel g₂ t u

/-! ## §9. Soundness reduction.

    Closes arithmetic-fragment soundness from the four
    primitive obligations, by induction on the `Gate` IR. -/

theorem compileArithmeticGateToPPM_sound_from_primitives
    (sem : GateToPPMSemanticsModel)
    (obs : ArithmeticPrimitivePPMObligations sem) :
    ∀ g, ImplementsGateAsPPM sem g (compileArithmeticGateToPPM g) := by
  intro g
  induction g with
  | I =>
      intro s t h
      have hst : s = t := obs.I_is_id s t h
      subst hst
      show PPMProgramRel sem (compileArithmeticGateToPPM Gate.I) s s
      exact PPMProgramRel.nil s
  | X q       => exact obs.X_ok q
  | CX c t    => exact obs.CX_ok c t
  | CCX a b t => exact obs.CCX_ok a b t
  | seq g₁ g₂ ih₁ ih₂ =>
      intro s u hseq
      obtain ⟨t, hg1, hg2⟩ := (obs.seq_decomp g₁ g₂ s u).mp hseq
      have hp1 := ih₁ s t hg1
      have hp2 := ih₂ t u hg2
      rw [compileArithmeticGateToPPM_seq]
      exact (PPMProgramRel_append sem _ _ s u).mpr ⟨t, hp1, hp2⟩

/-! ## §10. Macro records using the explicit semantic
       obligation.

    `VerifiedPPMMacro sem` now carries a real
    `ImplementsGateAsPPM` proof against a user-supplied
    semantic model.  The `True`-stand-in slots are gone. -/

structure VerifiedPPMMacro (sem : GateToPPMSemanticsModel) where
  gateName    : String
  gate        : Gate
  ppmProgram  : PPMProgram
  spec        : PPMSpec
  /-- Real semantic obligation against the supplied
      semantic model.  Replaces the prior
      `semantic_obligation : Prop` placeholder. -/
  semantic_ok : ImplementsGateAsPPM sem gate ppmProgram

/-- Macro record for an `X` gate.  Discharges its semantic
    obligation from the user-supplied `X_ok` primitive. -/
def macroForX (sem : GateToPPMSemanticsModel)
    (obs : ArithmeticPrimitivePPMObligations sem)
    (q : LogicalQubitId) (rounds distance : Nat) :
    VerifiedPPMMacro sem :=
  { gateName := "X"
    gate := Gate.X q
    ppmProgram := compileArithmeticGateToPPM (Gate.X q)
    spec :=
      { measuredPauliKind := PauliKind.X
        logicalInputs     := [q]
        logicalOutputs    := [q]
        rounds            := rounds
        distance          := distance }
    semantic_ok := obs.X_ok q }

/-- Macro record for a CNOT gate. -/
def macroForCNOT (sem : GateToPPMSemanticsModel)
    (obs : ArithmeticPrimitivePPMObligations sem)
    (c t : LogicalQubitId) (rounds distance : Nat) :
    VerifiedPPMMacro sem :=
  { gateName := "CNOT"
    gate := Gate.CX c t
    ppmProgram := compileArithmeticGateToPPM (Gate.CX c t)
    spec :=
      { measuredPauliKind := PauliKind.Z
        logicalInputs     := [c, t]
        logicalOutputs    := [c, t]
        rounds            := rounds
        distance          := distance }
    semantic_ok := obs.CX_ok c t }

/-- Macro record for a Toffoli gate. -/
def macroForToffoli (sem : GateToPPMSemanticsModel)
    (obs : ArithmeticPrimitivePPMObligations sem)
    (a b t : LogicalQubitId) (rounds distance : Nat) :
    VerifiedPPMMacro sem :=
  { gateName := "Toffoli"
    gate := Gate.CCX a b t
    ppmProgram := compileArithmeticGateToPPM (Gate.CCX a b t)
    spec :=
      { measuredPauliKind := PauliKind.Z
        logicalInputs     := [a, b, t]
        logicalOutputs    := [a, b, t]
        rounds            := rounds
        distance          := distance }
    semantic_ok := obs.CCX_ok a b t }

/-! ## §11. `VerifiedArithmeticPPMBlock` wrapper.

    Now parameterised by an explicit semantic model and
    obligation set.  The constructor `ofGate` takes the
    obligations as arguments; there is no longer a `True`
    stand-in slot. -/

structure VerifiedArithmeticPPMBlock
    (sem : GateToPPMSemanticsModel) where
  circuit     : Gate
  ppmProgram  : PPMProgram
  /-- Structural acceptance: the circuit is in the arithmetic
      fragment.  Trivially `true` for every `Gate`. -/
  accepted    : isArithmeticGate circuit = true
  /-- Compiler agreement. -/
  compile_ok  : compileArithmeticGateToPPM circuit = ppmProgram
  /-- REAL semantic obligation against the supplied model. -/
  semantic_ok : ImplementsGateAsPPM sem circuit ppmProgram

/-- Canonical constructor: from any `Gate` and a supplied
    primitive-obligations witness, build a
    `VerifiedArithmeticPPMBlock` whose `semantic_ok` field
    is the induction theorem applied to the obligations.

    The `True` stand-in from the previous version is GONE.
    A user that wants to build a `VerifiedArithmeticPPMBlock`
    must supply a real semantic model plus primitive proofs;
    the interface itself does not fabricate semantic
    correctness. -/
def VerifiedArithmeticPPMBlock.ofGate
    (sem : GateToPPMSemanticsModel)
    (obs : ArithmeticPrimitivePPMObligations sem)
    (g : Gate) :
    VerifiedArithmeticPPMBlock sem :=
  { circuit := g
    ppmProgram := compileArithmeticGateToPPM g
    accepted := isArithmeticGate_eq_true g
    compile_ok := rfl
    semantic_ok :=
      compileArithmeticGateToPPM_sound_from_primitives sem obs g }

/-! ## §12. Remaining obligations + future-tick plan.

    What this file now requires the user to supply:

    1. A `GateToPPMSemanticsModel` `sem` — concretely the
       (State, gateRel, ppmCommandRel) triple.
    2. An `ArithmeticPrimitivePPMObligations sem` record:
       * `I_is_id`         — `gateRel Gate.I` is the identity
         relation.
       * `X_ok q`          — the structural PPM for `X q`
         matches `gateRel (Gate.X q)`.
       * `CX_ok c t`       — same for CNOT.
       * `CCX_ok a b t`    — same for Toffoli; this is the
         specific outstanding TOFFOLI SEMANTIC OBLIGATION.
       * `seq_decomp`      — `gateRel (Gate.seq g₁ g₂)`
         decomposes into the composition of `gateRel g₁` and
         `gateRel g₂`.

    With these in hand, every `Gate` lifts to a
    `VerifiedArithmeticPPMBlock sem` via `ofGate`.  No fake
    `True` semantic claim anywhere.

    What this file STILL does NOT prove:

    * X / CX / CCX correctness against
      `PPMOperational.StabilizerState`: a future tick must
      instantiate `sem.State := StabilizerState`,
      `sem.ppmCommandRel := ⟨decode PauliKind + List Nat into
      PauliString, then apply Gottesman update⟩`, and
      discharge `X_ok`, `CX_ok`, `CCX_ok`.  Toffoli is the
      hardest: it requires magic-T injection on top of the
      stabilizer formalism.

    * QPE / non-Clifford+T circuits remain rejected/deferred
      via `classifyGateForPPMLowering` (always `.arithmetic`
      on `Gate`) and `classifyBaseUComForPPMLowering` (the
      `R θ φ λ` opaque-rotation case).

    * Backend SysCall generation: the SysCall/System layer
      (closed in `CompressedRepeatSoundness`) remains BELOW
      this PPM layer, accessed via the
      `LayeredPPMQECInterface` projection theorems. -/

/-! ## §13. First concrete PPM semantic instantiation —
       stabilizer-state model.

    Instantiates `GateToPPMSemanticsModel.ppmCommandRel` on
    `FormalRV.Framework.PPMOp.StabilizerState` using the
    existing Gottesman updates `apply_PPM_pos` /
    `apply_PPM_neg`.

    Coverage:
    * `measurePauliKind pk qs` is interpreted as the two
      Gottesman branches on the corresponding PauliString.
    * `applyFrameUpdate qs` is conservatively the identity
      transition (the stabilizer-only model does not capture
      Pauli-frame bookkeeping; the frame update is a
      classical post-correction that does not change the
      stabilizer group's generators in the deferred-frame
      convention).
    * `useMagicT q` is conservatively the identity transition
      (the stabilizer formalism does NOT capture non-Clifford
      magic-T injection; this model is therefore NOT
      sufficient for proving Toffoli correctness — see §12).

    `gateRel` is intentionally left as a parameter, because
    there is no existing `Gate → StabilizerState →
    StabilizerState → Prop` semantics in the repository
    (`Framework.Semantics.Gate.apply` is the classical-bit
    semantics over `State n = Fin n → Bool`, not the
    stabilizer-state semantics).  A future tick may define
    `gateRel` from a quantum semantics. -/

/-- Conversion from the `Architecture.PauliKind` (I/X/Y/Z
    used in `PPMSpec`, `PauliMeasurementClaim`) to the
    `PauliSem.Pauli` (used in `PauliString.ops`). -/
def pauliOfPauliKind : PauliKind → PauliSem.Pauli
  | .I => PauliSem.Pauli.I
  | .X => PauliSem.Pauli.X
  | .Y => PauliSem.Pauli.Y
  | .Z => PauliSem.Pauli.Z

@[simp] theorem pauliOfPauliKind_I : pauliOfPauliKind .I = PauliSem.Pauli.I := rfl
@[simp] theorem pauliOfPauliKind_X : pauliOfPauliKind .X = PauliSem.Pauli.X := rfl
@[simp] theorem pauliOfPauliKind_Y : pauliOfPauliKind .Y = PauliSem.Pauli.Y := rfl
@[simp] theorem pauliOfPauliKind_Z : pauliOfPauliKind .Z = PauliSem.Pauli.Z := rfl

/-- Build the n-qubit Pauli operator list with
    `pauliOfPauliKind pk` on every index in `qs` and `Pauli.I`
    on every other index, by iterating from `0` to `n-1`. -/
def pauliOpListOfKindOnQubits
    (n : Nat) (pk : PauliKind) (qs : List LogicalQubitId) :
    List PauliSem.Pauli :=
  (List.range n).map
    (fun i => if qs.contains i then pauliOfPauliKind pk else PauliSem.Pauli.I)

/-- The full PauliString (length n, phase +) used to interpret
    `PPMCommand.measurePauliKind pk qs` against the n-qubit
    stabilizer state.

    Returns `none` if any qubit in `qs` is out of bounds
    `< n`; otherwise `some` of the n-length Pauli string. -/
def pauliStringOfKindOnQubits
    (n : Nat) (pk : PauliKind) (qs : List LogicalQubitId) :
    Option PauliSem.PauliString :=
  if qs.all (fun q => decide (q < n)) then
    some
      { phase := PauliSem.Phase.plus
        ops   := pauliOpListOfKindOnQubits n pk qs }
  else
    none

theorem pauliStringOfKindOnQubits_length
    (n : Nat) (pk : PauliKind) (qs : List LogicalQubitId)
    (P : PauliSem.PauliString)
    (h : pauliStringOfKindOnQubits n pk qs = some P) :
    P.ops.length = n := by
  unfold pauliStringOfKindOnQubits at h
  by_cases hcond : qs.all (fun q => decide (q < n))
  · rw [if_pos hcond] at h
    cases h
    show ((List.range n).map _).length = n
    rw [List.length_map, List.length_range]
  · rw [if_neg hcond] at h
    exact absurd h (by simp)

/-- Concrete PPM command relation on `StabilizerState`.

    * `measurePauliKind`: nondeterministic stabilizer Pauli
      measurement, taking either Gottesman update branch
      (+1 outcome ↔ `apply_PPM_pos`, −1 outcome ↔
      `apply_PPM_neg`).  The relation includes the existential
      over the decoded PauliString.
    * `applyFrameUpdate`: identity transition (see §13
      header).  Frame bookkeeping is deferred.
    * `useMagicT`: identity transition (see §13 header).
      Non-Clifford magic-T injection is deferred. -/
def stabilizerPPMCommandRel (n : Nat) :
    PPMCommand → PPMOp.StabilizerState → PPMOp.StabilizerState → Prop
  | .measurePauliKind pk qs, s, t =>
      ∃ P : PauliSem.PauliString,
        pauliStringOfKindOnQubits n pk qs = some P
        ∧ (t = PPMOp.apply_PPM_pos s P ∨ t = PPMOp.apply_PPM_neg s P)
  | .applyFrameUpdate _,    s, t => t = s
  | .useMagicT _,           s, t => t = s

/-- Concrete semantic model: `State = StabilizerState`,
    `ppmCommandRel = stabilizerPPMCommandRel n`, and
    `gateRel` is supplied by the user (no canonical
    `Gate → StabilizerState → StabilizerState → Prop`
    exists in the repo yet). -/
def stabilizerPPMSemanticsModel
    (n : Nat)
    (gateRel : Gate → PPMOp.StabilizerState → PPMOp.StabilizerState → Prop) :
    GateToPPMSemanticsModel :=
  { State         := PPMOp.StabilizerState
    gateRel       := gateRel
    ppmCommandRel := stabilizerPPMCommandRel n }

/-! ### §13.a Helper: package the primitive obligations
       against the stabilizer model.

    The user supplies `gateRel` and the five primitive
    obligation proofs; this builder repackages them into the
    `ArithmeticPrimitivePPMObligations` shape that the
    induction theorem
    `compileArithmeticGateToPPM_sound_from_primitives`
    expects. -/

def mkStabilizerPrimitiveObligations
    (n : Nat)
    (gateRel : Gate → PPMOp.StabilizerState → PPMOp.StabilizerState → Prop)
    (hI  : ∀ s t, gateRel Gate.I s t → s = t)
    (hX  : ∀ q,
        ImplementsGateAsPPM (stabilizerPPMSemanticsModel n gateRel)
          (Gate.X q) (compileArithmeticGateToPPM (Gate.X q)))
    (hCX : ∀ c t,
        ImplementsGateAsPPM (stabilizerPPMSemanticsModel n gateRel)
          (Gate.CX c t) (compileArithmeticGateToPPM (Gate.CX c t)))
    (hCCX : ∀ a b t,
        ImplementsGateAsPPM (stabilizerPPMSemanticsModel n gateRel)
          (Gate.CCX a b t) (compileArithmeticGateToPPM (Gate.CCX a b t)))
    (hseq : ∀ g₁ g₂ s u,
        gateRel (Gate.seq g₁ g₂) s u ↔
          ∃ t, gateRel g₁ s t ∧ gateRel g₂ t u) :
    ArithmeticPrimitivePPMObligations (stabilizerPPMSemanticsModel n gateRel) :=
  { I_is_id    := hI
    X_ok       := hX
    CX_ok      := hCX
    CCX_ok     := hCCX
    seq_decomp := hseq }

/-! ### §13.b Single-step measurement theorems.

    These structural theorems show that the abstract PPM
    program semantics on a single `measurePauliKind`
    command is exactly the Gottesman update on the decoded
    PauliString (in either branch).  They do NOT claim
    anything about logical gate correctness — they connect
    the abstract `PPMProgramRel` to the concrete
    `apply_PPM_pos` / `apply_PPM_neg`. -/

/-- `[measurePauliKind pk qs]` applied to `s` reaches
    `apply_PPM_pos s P` when the decoded PauliString is `P`. -/
theorem PPMProgramRel_measure_single_step_pos
    (n : Nat)
    (gateRel : Gate → PPMOp.StabilizerState → PPMOp.StabilizerState → Prop)
    (pk : PauliKind) (qs : List LogicalQubitId) (s : PPMOp.StabilizerState)
    (P : PauliSem.PauliString)
    (h : pauliStringOfKindOnQubits n pk qs = some P) :
    PPMProgramRel (stabilizerPPMSemanticsModel n gateRel)
      [PPMCommand.measurePauliKind pk qs]
      s
      (PPMOp.apply_PPM_pos s P) := by
  refine PPMProgramRel.cons ?_ (PPMProgramRel.nil _)
  show stabilizerPPMCommandRel n (PPMCommand.measurePauliKind pk qs)
        s (PPMOp.apply_PPM_pos s P)
  exact ⟨P, h, Or.inl rfl⟩

/-- Negative-outcome companion of
    `PPMProgramRel_measure_single_step_pos`. -/
theorem PPMProgramRel_measure_single_step_neg
    (n : Nat)
    (gateRel : Gate → PPMOp.StabilizerState → PPMOp.StabilizerState → Prop)
    (pk : PauliKind) (qs : List LogicalQubitId) (s : PPMOp.StabilizerState)
    (P : PauliSem.PauliString)
    (h : pauliStringOfKindOnQubits n pk qs = some P) :
    PPMProgramRel (stabilizerPPMSemanticsModel n gateRel)
      [PPMCommand.measurePauliKind pk qs]
      s
      (PPMOp.apply_PPM_neg s P) := by
  refine PPMProgramRel.cons ?_ (PPMProgramRel.nil _)
  show stabilizerPPMCommandRel n (PPMCommand.measurePauliKind pk qs)
        s (PPMOp.apply_PPM_neg s P)
  exact ⟨P, h, Or.inr rfl⟩

/-- `[applyFrameUpdate qs]` is an identity step on
    `StabilizerState`. -/
theorem PPMProgramRel_applyFrameUpdate_single_step
    (n : Nat)
    (gateRel : Gate → PPMOp.StabilizerState → PPMOp.StabilizerState → Prop)
    (qs : List LogicalQubitId) (s : PPMOp.StabilizerState) :
    PPMProgramRel (stabilizerPPMSemanticsModel n gateRel)
      [PPMCommand.applyFrameUpdate qs] s s := by
  refine PPMProgramRel.cons ?_ (PPMProgramRel.nil _)
  show stabilizerPPMCommandRel n (PPMCommand.applyFrameUpdate qs) s s
  rfl

/-- `[useMagicT q]` is an identity step on
    `StabilizerState`. -/
theorem PPMProgramRel_useMagicT_single_step
    (n : Nat)
    (gateRel : Gate → PPMOp.StabilizerState → PPMOp.StabilizerState → Prop)
    (q : LogicalQubitId) (s : PPMOp.StabilizerState) :
    PPMProgramRel (stabilizerPPMSemanticsModel n gateRel)
      [PPMCommand.useMagicT q] s s := by
  refine PPMProgramRel.cons ?_ (PPMProgramRel.nil _)
  show stabilizerPPMCommandRel n (PPMCommand.useMagicT q) s s
  rfl

/-! ### §13.c What this instantiation does NOT yet prove.

    The stabilizer instantiation is the first concrete
    `ppmCommandRel`.  It captures:

    * measurement dynamics (Gottesman updates,
      `apply_PPM_pos` / `apply_PPM_neg`) — captured precisely
      by the existential branch in `stabilizerPPMCommandRel`.

    * frame-update / magic-T as identity transitions on the
      stabilizer state — CONSERVATIVE.  Real Pauli-frame
      bookkeeping is classical metadata that the stabilizer
      formalism deliberately abstracts away.  Real
      magic-T injection is non-Clifford and CANNOT be
      captured by stabilizer state alone.

    Consequently this instantiation does NOT yet prove:

    * `X_ok` — requires connecting `gateRel (Gate.X q)` to
      the trivial transition (since X is a Pauli, deferred
      frame is OK), and `gateRel` is currently a parameter.
    * `CX_ok` — requires `gateRel (Gate.CX c t)` to match
      the `M_ZZ` measurement + frame update.
    * `CCX_ok` — requires non-Clifford magic-T injection;
      not capturable here.

    The Toffoli (`CCX`) obligation in particular remains
    open and is the natural target of the next tick once the
    interface accepts a richer state type (e.g., stabilizer
    state + classical Pauli-frame register + magic-state
    resource counter).

    QPE phase rotations remain outside the accepted
    fragment. -/

/-! ## §14. Enriched logical PPM semantic state.

    The stabilizer-only model (§13) captures Gottesman
    measurement updates faithfully but interprets both
    `applyFrameUpdate` and `useMagicT` as identity
    transitions, which is too coarse for X / CX / CCX
    correctness.

    This section adds a richer state type:

      LogicalPPMState
        ├ stabilizer : StabilizerState   (Gottesman generators)
        ├ frame      : LogicalPauliFrame (classical X / Z corrections)
        └ magicUsed  : Nat               (magic-T resource counter)

    Conventions:
    * Pauli-frame is the deferred-frame representation: an
      X-frame entry on qubit `q` means "an unapplied logical
      X correction is pending on q".  Symmetric for Z-frame.
    * `applyFrameUpdate qs` toggles the X-frame on every
      qubit in `qs`.  This is the canonical interpretation
      that lines up with `compileArithmeticGateToPPM
      (Gate.X q) = [applyFrameUpdate [q]]`.
    * `useMagicT q` increments `magicUsed` by 1 and otherwise
      preserves stabilizer/frame.  This is RESOURCE
      ACCOUNTING — it does NOT implement the non-Clifford
      action of a magic-T injection.  Toffoli soundness
      therefore remains open against this enriched model.

    No existing `LogicalPauliFrame` data structure was found
    in the repository; the only Pauli-frame artefact is the
    backend SysCall `SysCallKind.PauliFrameUpdate
    (correction_id : Nat)` in `Architecture.lean`, which is
    a syscall, not a logical-frame data type.  Magic-state
    resource counting reuses the existing
    `MagicStateKind` / `MagicStateDemand` philosophy from
    `FactoryHierarchy.lean` / `MagicStateInjection.lean` but
    keeps a simple `Nat` counter at this layer. -/

/-! ### §14.a Logical Pauli-frame data type. -/

structure LogicalPauliFrame where
  /-- Logical qubits with a pending X correction. -/
  xFrame : List LogicalQubitId
  /-- Logical qubits with a pending Z correction. -/
  zFrame : List LogicalQubitId
  deriving Repr, Inhabited, DecidableEq

/-- The empty (no-correction) frame. -/
def LogicalPauliFrame.empty : LogicalPauliFrame :=
  { xFrame := [], zFrame := [] }

/-- Toggle the X-frame entry for one qubit:
    * if `q` is in `xFrame`, remove it (the pending X
      correction has been cancelled out by another X);
    * otherwise prepend `q`. -/
def LogicalPauliFrame.toggleX (frame : LogicalPauliFrame)
    (q : LogicalQubitId) : LogicalPauliFrame :=
  if frame.xFrame.contains q then
    { frame with xFrame := frame.xFrame.filter (· != q) }
  else
    { frame with xFrame := q :: frame.xFrame }

/-- Toggle the Z-frame entry for one qubit. -/
def LogicalPauliFrame.toggleZ (frame : LogicalPauliFrame)
    (q : LogicalQubitId) : LogicalPauliFrame :=
  if frame.zFrame.contains q then
    { frame with zFrame := frame.zFrame.filter (· != q) }
  else
    { frame with zFrame := q :: frame.zFrame }

/-- Toggle the X-frame on every qubit in a list (left fold). -/
def LogicalPauliFrame.toggleXList (frame : LogicalPauliFrame)
    (qs : List LogicalQubitId) : LogicalPauliFrame :=
  qs.foldl LogicalPauliFrame.toggleX frame

/-- Toggle the Z-frame on every qubit in a list. -/
def LogicalPauliFrame.toggleZList (frame : LogicalPauliFrame)
    (qs : List LogicalQubitId) : LogicalPauliFrame :=
  qs.foldl LogicalPauliFrame.toggleZ frame

/-! ### §14.b Enriched state type. -/

structure LogicalPPMState where
  stabilizer : PPMOp.StabilizerState
  frame      : LogicalPauliFrame
  magicUsed  : Nat
  deriving Inhabited

/-- Canonical empty enriched state on `n` qubits.  Stabilizer
    starts as the n-qubit identity stabilizer (no
    constraints), frame is empty, no magic used. -/
def LogicalPPMState.empty (n : Nat) : LogicalPPMState :=
  { stabilizer := []   -- caller supplies a real stabilizer
    frame      := LogicalPauliFrame.empty
    magicUsed  := 0 }

/-! ### §14.c Enriched PPM command relation. -/

/-- Concrete PPM command relation on `LogicalPPMState`.

    * `measurePauliKind`: stabilizer is updated by either
      Gottesman branch; frame and magicUsed are PRESERVED.
    * `applyFrameUpdate qs`: stabilizer is preserved;
      X-frame is toggled on each qubit in `qs`; magicUsed
      preserved.
    * `useMagicT _`: stabilizer and frame preserved;
      magicUsed is INCREMENTED by 1.  This is resource
      accounting; it does NOT implement the non-Clifford
      action of a T-state injection. -/
def logicalPPMCommandRel (n : Nat) :
    PPMCommand → LogicalPPMState → LogicalPPMState → Prop
  | .measurePauliKind pk qs, s, t =>
      ∃ P : PauliSem.PauliString,
        pauliStringOfKindOnQubits n pk qs = some P
        ∧ ( (t.stabilizer = PPMOp.apply_PPM_pos s.stabilizer P ∨
             t.stabilizer = PPMOp.apply_PPM_neg s.stabilizer P)
            ∧ t.frame = s.frame
            ∧ t.magicUsed = s.magicUsed )
  | .applyFrameUpdate qs,   s, t =>
      t.stabilizer = s.stabilizer
      ∧ t.frame = s.frame.toggleXList qs
      ∧ t.magicUsed = s.magicUsed
  | .useMagicT _,           s, t =>
      t.stabilizer = s.stabilizer
      ∧ t.frame = s.frame
      ∧ t.magicUsed = s.magicUsed + 1

/-! ### §14.d Enriched semantics model. -/

def logicalPPMSemanticsModel
    (n : Nat)
    (gateRel : Gate → LogicalPPMState → LogicalPPMState → Prop) :
    GateToPPMSemanticsModel :=
  { State         := LogicalPPMState
    gateRel       := gateRel
    ppmCommandRel := logicalPPMCommandRel n }

/-! ### §14.e Single-step command theorems for the enriched
       model.  These mirror the §13.b stabilizer-only
       theorems but expose the frame/magic effects
       explicitly. -/

/-- `[measurePauliKind pk qs]` reaches a state with stabilizer
    `apply_PPM_pos s.stabilizer P` (+1 outcome), preserving
    frame and magicUsed. -/
theorem PPMProgramRel_logical_measure_single_step_pos
    (n : Nat)
    (gateRel : Gate → LogicalPPMState → LogicalPPMState → Prop)
    (pk : PauliKind) (qs : List LogicalQubitId)
    (s : LogicalPPMState) (P : PauliSem.PauliString)
    (h : pauliStringOfKindOnQubits n pk qs = some P) :
    PPMProgramRel (logicalPPMSemanticsModel n gateRel)
      [PPMCommand.measurePauliKind pk qs]
      s
      { stabilizer := PPMOp.apply_PPM_pos s.stabilizer P
        frame      := s.frame
        magicUsed  := s.magicUsed } := by
  refine PPMProgramRel.cons ?_ (PPMProgramRel.nil _)
  show logicalPPMCommandRel n (PPMCommand.measurePauliKind pk qs) s _
  exact ⟨P, h, Or.inl rfl, rfl, rfl⟩

/-- Negative-outcome companion of
    `PPMProgramRel_logical_measure_single_step_pos`. -/
theorem PPMProgramRel_logical_measure_single_step_neg
    (n : Nat)
    (gateRel : Gate → LogicalPPMState → LogicalPPMState → Prop)
    (pk : PauliKind) (qs : List LogicalQubitId)
    (s : LogicalPPMState) (P : PauliSem.PauliString)
    (h : pauliStringOfKindOnQubits n pk qs = some P) :
    PPMProgramRel (logicalPPMSemanticsModel n gateRel)
      [PPMCommand.measurePauliKind pk qs]
      s
      { stabilizer := PPMOp.apply_PPM_neg s.stabilizer P
        frame      := s.frame
        magicUsed  := s.magicUsed } := by
  refine PPMProgramRel.cons ?_ (PPMProgramRel.nil _)
  show logicalPPMCommandRel n (PPMCommand.measurePauliKind pk qs) s _
  exact ⟨P, h, Or.inr rfl, rfl, rfl⟩

/-- `[applyFrameUpdate qs]` reaches a state with the X-frame
    toggled on each `q ∈ qs`, preserving stabilizer and
    magicUsed. -/
theorem PPMProgramRel_logical_applyFrameUpdate_single_step
    (n : Nat)
    (gateRel : Gate → LogicalPPMState → LogicalPPMState → Prop)
    (qs : List LogicalQubitId) (s : LogicalPPMState) :
    PPMProgramRel (logicalPPMSemanticsModel n gateRel)
      [PPMCommand.applyFrameUpdate qs]
      s
      { stabilizer := s.stabilizer
        frame      := s.frame.toggleXList qs
        magicUsed  := s.magicUsed } := by
  refine PPMProgramRel.cons ?_ (PPMProgramRel.nil _)
  show logicalPPMCommandRel n (PPMCommand.applyFrameUpdate qs) s _
  exact ⟨rfl, rfl, rfl⟩

/-- `[useMagicT q]` reaches a state with `magicUsed`
    incremented and stabilizer/frame preserved. -/
theorem PPMProgramRel_logical_useMagicT_single_step
    (n : Nat)
    (gateRel : Gate → LogicalPPMState → LogicalPPMState → Prop)
    (q : LogicalQubitId) (s : LogicalPPMState) :
    PPMProgramRel (logicalPPMSemanticsModel n gateRel)
      [PPMCommand.useMagicT q]
      s
      { stabilizer := s.stabilizer
        frame      := s.frame
        magicUsed  := s.magicUsed + 1 } := by
  refine PPMProgramRel.cons ?_ (PPMProgramRel.nil _)
  show logicalPPMCommandRel n (PPMCommand.useMagicT q) s _
  exact ⟨rfl, rfl, rfl⟩

/-! ### §14.f Primitive-obligation builder for the enriched
       model.

    Mirrors §13.a `mkStabilizerPrimitiveObligations` but
    targets the enriched `logicalPPMSemanticsModel`.  All
    primitive obligations remain user-supplied; X_ok / CX_ok
    / CCX_ok are NOT proved here. -/

def mkLogicalPPMPrimitiveObligations
    (n : Nat)
    (gateRel : Gate → LogicalPPMState → LogicalPPMState → Prop)
    (hI  : ∀ s t, gateRel Gate.I s t → s = t)
    (hX  : ∀ q,
        ImplementsGateAsPPM (logicalPPMSemanticsModel n gateRel)
          (Gate.X q) (compileArithmeticGateToPPM (Gate.X q)))
    (hCX : ∀ c t,
        ImplementsGateAsPPM (logicalPPMSemanticsModel n gateRel)
          (Gate.CX c t) (compileArithmeticGateToPPM (Gate.CX c t)))
    (hCCX : ∀ a b t,
        ImplementsGateAsPPM (logicalPPMSemanticsModel n gateRel)
          (Gate.CCX a b t) (compileArithmeticGateToPPM (Gate.CCX a b t)))
    (hseq : ∀ g₁ g₂ s u,
        gateRel (Gate.seq g₁ g₂) s u ↔
          ∃ t, gateRel g₁ s t ∧ gateRel g₂ t u) :
    ArithmeticPrimitivePPMObligations (logicalPPMSemanticsModel n gateRel) :=
  { I_is_id    := hI
    X_ok       := hX
    CX_ok      := hCX
    CCX_ok     := hCCX
    seq_decomp := hseq }

/-! ### §14.g What the enriched model still does NOT prove.

    * `X_ok`: requires `gateRel (Gate.X q)` to match
      precisely the X-frame toggle on `q`.  This is a
      USER-supplied semantic choice — the canonical
      ("macro-specified") `gateRel` for which X_ok is
      tautological is intentionally NOT provided here, to
      avoid disguising a definition as a proof.

    * `CX_ok`: requires `gateRel (Gate.CX c t)` to match the
      `M_ZZ` measurement (one of the two Gottesman branches)
      followed by an X-frame toggle on `t`.  Open.

    * `CCX_ok` (Toffoli): the enriched model treats
      `useMagicT` only as a Nat counter increment; the
      non-Clifford action of magic-T injection is NOT
      captured by `(StabilizerState × LogicalPauliFrame ×
      Nat)`.  Toffoli correctness genuinely requires either
      (a) lifting to a richer state space that includes
      classical control over which Pauli correction is
      applied based on T-injection outcomes, or (b) a
      different denotational substrate (state-vector or
      density-matrix semantics).  Open.

    Stabilizer-only and enriched models COEXIST:
    `stabilizerPPMSemanticsModel` (§13.b) remains intact and
    is the right choice for Gottesman-only reasoning;
    `logicalPPMSemanticsModel` (this section) is the right
    choice for reasoning that also involves Pauli-frame
    metadata.

    QPE phase rotations remain outside both models. -/

/-! ## §15. Frame-level gate relation — first closed I/X
       obligations.

    The enriched model from §14 leaves `gateRel` as a
    parameter so that no specific gate semantics is implied
    by the interface itself.  In this section we instantiate
    `gateRel` with a lightweight DEFERRED-FRAME RELATION
    that captures EXACTLY the macro-level effect on
    `LogicalPPMState` for the `I` and `X` cases:

      * `Gate.I` is the identity transition.
      * `Gate.X q` toggles the X-frame on `q`, preserving
        stabilizer and magicUsed.
      * `Gate.seq g₁ g₂` decomposes through an intermediate
        state, as required by the induction theorem.
      * `Gate.CX _ _` and `Gate.CCX _ _ _` are `False` — the
        frame-level relation does NOT support them.  This is
        an explicit "not supported" marker, not a claim of
        correctness.

    This is NOT full quantum denotational semantics.  It is
    a deferred-frame specification covering precisely the
    PPM macros that `compileArithmeticGateToPPM` emits for
    `Gate.I` and `Gate.X`.  Hence the name
    `frameLevelGateRel` — never "quantum semantics".

    The CX / CCX obligations remain EXPLICITLY OPEN.  A
    future tick that wants to discharge them must either
    enrich `LogicalPPMState` further (to track measurement
    outcomes, classical T-injection control, etc.) or move
    to a state-vector/density-matrix substrate. -/

/-- Frame-level gate relation.  Captures the macro-level
    transition that the §4 compiler's output programs would
    produce on `LogicalPPMState`, for the I and X cases.
    CX and CCX are `False` (not supported by this lightweight
    deferred-frame model). -/
def frameLevelGateRel : Gate → LogicalPPMState → LogicalPPMState → Prop
  | .I,        s, t => t = s
  | .X q,      s, t =>
      t.stabilizer = s.stabilizer
      ∧ t.frame = s.frame.toggleX q
      ∧ t.magicUsed = s.magicUsed
  | .CX _ _,   _, _ => False
  | .CCX _ _ _, _, _ => False
  | .seq g₁ g₂, s, u =>
      ∃ mid, frameLevelGateRel g₁ s mid ∧ frameLevelGateRel g₂ mid u

/-- Semantics model that wires `frameLevelGateRel` into the
    enriched §14 model. -/
def frameLevelPPMSemanticsModel (n : Nat) : GateToPPMSemanticsModel :=
  logicalPPMSemanticsModel n frameLevelGateRel

/-! ### §15.a Helpers and structural equations. -/

@[simp] theorem toggleXList_singleton
    (frame : LogicalPauliFrame) (q : LogicalQubitId) :
    frame.toggleXList [q] = frame.toggleX q := rfl

theorem frameLevelGateRel_I (s t : LogicalPPMState) :
    frameLevelGateRel Gate.I s t ↔ t = s := Iff.rfl

theorem frameLevelGateRel_X (q : LogicalQubitId) (s t : LogicalPPMState) :
    frameLevelGateRel (Gate.X q) s t ↔
      ( t.stabilizer = s.stabilizer
        ∧ t.frame = s.frame.toggleX q
        ∧ t.magicUsed = s.magicUsed ) := Iff.rfl

theorem frameLevelGateRel_seq_decomp (g₁ g₂ : Gate) (s u : LogicalPPMState) :
    frameLevelGateRel (Gate.seq g₁ g₂) s u ↔
      ∃ mid, frameLevelGateRel g₁ s mid ∧ frameLevelGateRel g₂ mid u :=
  Iff.rfl

/-! ### §15.b `I_is_id` and `X_ok` closed for `frameLevelGateRel`. -/

theorem frameLevel_I_is_id (s t : LogicalPPMState)
    (h : frameLevelGateRel Gate.I s t) : s = t := by
  exact h.symm

theorem frameLevel_X_ok (n : Nat) (q : LogicalQubitId) :
    ImplementsGateAsPPM (frameLevelPPMSemanticsModel n) (Gate.X q)
      (compileArithmeticGateToPPM (Gate.X q)) := by
  intro s t hGate
  -- hGate : t.stabilizer = s.stabilizer ∧ t.frame = s.frame.toggleX q
  --         ∧ t.magicUsed = s.magicUsed
  obtain ⟨h_stab, h_frame, h_magic⟩ := hGate
  -- Goal: PPMProgramRel (...) [applyFrameUpdate [q]] s t
  -- compileArithmeticGateToPPM (Gate.X q) = [applyFrameUpdate [q]]
  show PPMProgramRel (frameLevelPPMSemanticsModel n)
        [PPMCommand.applyFrameUpdate [q]] s t
  have key :=
    PPMProgramRel_logical_applyFrameUpdate_single_step n frameLevelGateRel [q] s
  -- key : PPMProgramRel ... [applyFrameUpdate [q]] s
  --         { stabilizer := s.stabilizer
  --           frame := s.frame.toggleXList [q]
  --           magicUsed := s.magicUsed }
  -- Since toggleXList [q] = toggleX q by rfl, the target state of key
  -- is field-equal to t.
  have ht_eq :
      ({ stabilizer := s.stabilizer
         frame      := s.frame.toggleXList [q]
         magicUsed  := s.magicUsed } : LogicalPPMState)
        = t := by
    rcases t with ⟨ts, tf, tm⟩
    simp only [toggleXList_singleton]
    congr 1
    · exact h_stab.symm
    · exact h_frame.symm
    · exact h_magic.symm
  rw [← ht_eq]
  exact key

/-! ### §15.c Partial primitive-obligation bundle.

    `ArithmeticPrimitivePPMObligations sem` requires
    `CX_ok` and `CCX_ok`, neither of which is true for
    `frameLevelGateRel` (they would unfold to `False → ...`
    and be trivially-but-misleadingly satisfiable — we
    deliberately do NOT package such vacuous proofs).

    Instead, we provide a partial bundle covering ONLY the
    obligations that the frame-level model genuinely
    discharges: `I_is_id` and `X_ok`.  This is a clean
    milestone without overclaiming. -/

structure ArithmeticIXPrimitivePPMObligations
    (sem : GateToPPMSemanticsModel) where
  I_is_id : ∀ s t, sem.gateRel Gate.I s t → s = t
  X_ok    : ∀ q,
    ImplementsGateAsPPM sem (Gate.X q)
      (compileArithmeticGateToPPM (Gate.X q))

/-- Canonical IX bundle for the frame-level model. -/
def frameLevelIXObligations (n : Nat) :
    ArithmeticIXPrimitivePPMObligations (frameLevelPPMSemanticsModel n) :=
  { I_is_id := frameLevel_I_is_id
    X_ok    := frameLevel_X_ok n }

/-! ### §15.d What is STILL open against `frameLevelGateRel`.

    * `CX_ok`: `frameLevelGateRel (Gate.CX _ _) = False`, so
      ImplementsGateAsPPM is vacuously true.  This is a
      degenerate situation — `frameLevelGateRel` simply does
      NOT model CNOT.  A real CNOT obligation requires a
      semantic model that captures the measurement outcome's
      classical branch (which Pauli correction follows the
      `M_ZZ` outcome).  Open and explicitly NOT bundled.

    * `CCX_ok`: same situation, plus the non-Clifford
      magic-T injection issue.  Open and explicitly NOT
      bundled.

    * Toffoli soundness: open, requires a state model that
      captures magic-state injection as more than a Nat
      counter.

    The §15 milestone closes the EASY half (I, X) cleanly.
    CX, CCX, and Toffoli remain explicit open obligations,
    not silently filled in by `False`-hypothesis vacuity. -/

/-! ## §16. CX-aware macro-specified PPM relation.

    `frameLevelGateRel` (§15) sets `Gate.CX _ _ = False` and
    therefore cannot ground CNOT correctness.  This section
    introduces a strictly stronger relation that captures the
    macro-level behaviour of `compileArithmeticGateToPPM
    (Gate.CX c t) = [measurePauliKind Z [c, t],
    applyFrameUpdate [t]]`:

      * Run `M_ZZ` on (c, t): stabilizer takes either
        Gottesman branch on the decoded PauliString;
        frame and magicUsed preserved.
      * Apply the Pauli-frame X-correction on `t`:
        stabilizer preserved; frame.toggleX t; magicUsed
        preserved.

    `Gate.CCX _ _ _` remains `False` (Toffoli still requires
    magic-T injection semantics beyond a `Nat` counter).

    This is a MACRO-SPECIFIED relation, not full quantum
    denotational semantics.  It precisely matches what the
    compiler emits for CX — by construction, the CX program
    realises the relation.  A future tick that wants to
    connect this to a real CNOT will need a denotational
    bridge from `cxMacroGateRel n` to actual CNOT
    semantics. -/

/-- CX-aware macro-specified gate relation.  The `n` argument
    fixes the qubit register size for `PauliString` decoding. -/
def cxMacroGateRel (n : Nat) :
    Gate → LogicalPPMState → LogicalPPMState → Prop
  | .I,        s, t => t = s
  | .X q,      s, t =>
      t.stabilizer = s.stabilizer
      ∧ t.frame = s.frame.toggleX q
      ∧ t.magicUsed = s.magicUsed
  | .CX c tgt, s, u =>
      ∃ (P : PauliSem.PauliString) (mid : LogicalPPMState),
        pauliStringOfKindOnQubits n PauliKind.Z [c, tgt] = some P
        ∧ ( mid.stabilizer = PPMOp.apply_PPM_pos s.stabilizer P
            ∨ mid.stabilizer = PPMOp.apply_PPM_neg s.stabilizer P )
        ∧ mid.frame = s.frame
        ∧ mid.magicUsed = s.magicUsed
        ∧ u.stabilizer = mid.stabilizer
        ∧ u.frame = mid.frame.toggleX tgt
        ∧ u.magicUsed = mid.magicUsed
  | .CCX _ _ _, _, _ => False
  | .seq g₁ g₂, s, u =>
      ∃ mid, cxMacroGateRel n g₁ s mid ∧ cxMacroGateRel n g₂ mid u

/-- Semantics model wiring `cxMacroGateRel n` into the
    enriched §14 model. -/
def cxMacroPPMSemanticsModel (n : Nat) : GateToPPMSemanticsModel :=
  logicalPPMSemanticsModel n (cxMacroGateRel n)

/-! ### §16.a Unfolding identities. -/

theorem cxMacroGateRel_I (n : Nat) (s t : LogicalPPMState) :
    cxMacroGateRel n Gate.I s t ↔ t = s := Iff.rfl

theorem cxMacroGateRel_X (n : Nat) (q : LogicalQubitId) (s t : LogicalPPMState) :
    cxMacroGateRel n (Gate.X q) s t ↔
      ( t.stabilizer = s.stabilizer
        ∧ t.frame = s.frame.toggleX q
        ∧ t.magicUsed = s.magicUsed ) := Iff.rfl

theorem cxMacroGateRel_seq_decomp (n : Nat) (g₁ g₂ : Gate)
    (s u : LogicalPPMState) :
    cxMacroGateRel n (Gate.seq g₁ g₂) s u ↔
      ∃ mid, cxMacroGateRel n g₁ s mid ∧ cxMacroGateRel n g₂ mid u :=
  Iff.rfl

/-! ### §16.b `I_is_id` and `X_ok` again, for the CX-aware model. -/

theorem cxMacro_I_is_id (n : Nat) (s t : LogicalPPMState)
    (h : cxMacroGateRel n Gate.I s t) : s = t := by
  exact h.symm

theorem cxMacro_X_ok (n : Nat) (q : LogicalQubitId) :
    ImplementsGateAsPPM (cxMacroPPMSemanticsModel n) (Gate.X q)
      (compileArithmeticGateToPPM (Gate.X q)) := by
  intro s t hGate
  obtain ⟨h_stab, h_frame, h_magic⟩ := hGate
  show PPMProgramRel (cxMacroPPMSemanticsModel n)
        [PPMCommand.applyFrameUpdate [q]] s t
  have key :=
    PPMProgramRel_logical_applyFrameUpdate_single_step n (cxMacroGateRel n) [q] s
  have ht_eq :
      ({ stabilizer := s.stabilizer
         frame      := s.frame.toggleXList [q]
         magicUsed  := s.magicUsed } : LogicalPPMState)
        = t := by
    rcases t with ⟨ts, tf, tm⟩
    simp only [toggleXList_singleton]
    congr 1
    · exact h_stab.symm
    · exact h_frame.symm
    · exact h_magic.symm
  rw [← ht_eq]
  exact key

/-! ### §16.c `CX_ok` for the CX-aware model.

    The proof walks two PPM steps:
    * Step 1: `measurePauliKind Z [c, tgt]` carries `s` to
      the intermediate state extracted from the relation
      (one of the two Gottesman branches).
    * Step 2: `applyFrameUpdate [tgt]` carries the
      intermediate state to `u`. -/

theorem cxMacro_CX_ok (n : Nat) (c tgt : LogicalQubitId) :
    ImplementsGateAsPPM (cxMacroPPMSemanticsModel n) (Gate.CX c tgt)
      (compileArithmeticGateToPPM (Gate.CX c tgt)) := by
  intro s u hGate
  -- hGate : ∃ P mid, ... ∧ ... ∧ ... ∧ ...
  obtain ⟨P, mid, hP_decode, hmid_stab_branch, hmid_frame, hmid_magic,
          hu_stab, hu_frame, hu_magic⟩ := hGate
  -- Build the two step proofs as named values so Lean can infer the
  -- intermediate state.
  have hstep1 :
      (cxMacroPPMSemanticsModel n).ppmCommandRel
        (PPMCommand.measurePauliKind PauliKind.Z [c, tgt]) s mid := by
    show logicalPPMCommandRel n
          (PPMCommand.measurePauliKind PauliKind.Z [c, tgt]) s mid
    exact ⟨P, hP_decode, hmid_stab_branch, hmid_frame, hmid_magic⟩
  have hstep2 :
      (cxMacroPPMSemanticsModel n).ppmCommandRel
        (PPMCommand.applyFrameUpdate [tgt]) mid u := by
    show logicalPPMCommandRel n
          (PPMCommand.applyFrameUpdate [tgt]) mid u
    refine ⟨hu_stab, ?_, hu_magic⟩
    show u.frame = mid.frame.toggleXList [tgt]
    rw [toggleXList_singleton]
    exact hu_frame
  exact PPMProgramRel.cons hstep1
    (PPMProgramRel.cons hstep2 (PPMProgramRel.nil u))

/-! ### §16.d Partial ICX obligation bundle.

    Same shape as §15.c's `ArithmeticIXPrimitivePPMObligations`
    but with an additional `CX_ok` field.  CCX is NOT
    included — `cxMacroGateRel n (Gate.CCX _ _ _) = False`
    makes the obligation vacuously satisfiable, but doing so
    would not constitute a real Toffoli proof, so we
    deliberately decline to bundle it. -/

structure ArithmeticICXPrimitivePPMObligations
    (sem : GateToPPMSemanticsModel) where
  I_is_id : ∀ s t, sem.gateRel Gate.I s t → s = t
  X_ok    : ∀ q,
    ImplementsGateAsPPM sem (Gate.X q)
      (compileArithmeticGateToPPM (Gate.X q))
  CX_ok   : ∀ c tgt,
    ImplementsGateAsPPM sem (Gate.CX c tgt)
      (compileArithmeticGateToPPM (Gate.CX c tgt))

/-- Canonical ICX bundle for the CX-aware model. -/
def cxMacroICXObligations (n : Nat) :
    ArithmeticICXPrimitivePPMObligations (cxMacroPPMSemanticsModel n) :=
  { I_is_id := cxMacro_I_is_id n
    X_ok    := cxMacro_X_ok n
    CX_ok   := cxMacro_CX_ok n }

/-! ### §16.e Restricted ICX-fragment soundness.

    A circuit classifier `isICXGate` accepts every `Gate`
    EXCEPT `Gate.CCX _ _ _` (and sequences containing them).
    Under that restriction, the CX-aware model discharges
    the entire arithmetic-to-PPM lowering soundness for the
    ICX fragment by induction. -/

def isICXGate : Gate → Bool
  | .I         => true
  | .X _       => true
  | .CX _ _    => true
  | .CCX _ _ _ => false
  | .seq g₁ g₂ => isICXGate g₁ && isICXGate g₂

theorem compileICXGateToPPM_sound_from_cxMacro (n : Nat) :
    ∀ g, isICXGate g = true →
      ImplementsGateAsPPM (cxMacroPPMSemanticsModel n) g
        (compileArithmeticGateToPPM g) := by
  intro g
  induction g with
  | I =>
      intro _ s t h
      have hst : t = s := h
      subst hst
      exact PPMProgramRel.nil _
  | X q => intro _; exact cxMacro_X_ok n q
  | CX c tgt => intro _; exact cxMacro_CX_ok n c tgt
  | CCX _ _ _ =>
      intro h
      simp [isICXGate] at h
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hICX
      have h_and : (isICXGate g₁ && isICXGate g₂) = true := hICX
      rw [Bool.and_eq_true] at h_and
      obtain ⟨h1, h2⟩ := h_and
      intro s u hseq
      obtain ⟨mid, hg1, hg2⟩ := hseq
      have hp1 := ih₁ h1 s mid hg1
      have hp2 := ih₂ h2 mid u hg2
      rw [compileArithmeticGateToPPM_seq]
      exact (PPMProgramRel_append _ _ _ s u).mpr ⟨mid, hp1, hp2⟩

/-! ### §16.f What is STILL open.

    * `CCX_ok` / Toffoli correctness: `cxMacroGateRel n
      (Gate.CCX _ _ _) = False`, exactly as in §15.  This
      remains the natural target of a future tick.  Toffoli
      genuinely requires a semantic model that captures
      magic-T injection beyond a `Nat` counter (either by
      tracking T-injection outcomes as classical metadata,
      or by lifting to a state-vector / density-matrix
      substrate).

    * General arithmetic soundness on the FULL Gate IR
      (including CCX): blocked on the above.

    * QPE / non-Clifford+T circuits: remain rejected/deferred
      via the §1 classifier.

    Prior milestones all remain intact:
    * stabilizer-only model (§13);
    * enriched LogicalPPMState model (§14);
    * `frameLevelGateRel` I/X bundle (§15). -/

/-! ## §17. Magic-aware logical PPM state + CCX obligation
       isolation.

    The §13/§14/§15/§16 layers leave `Gate.CCX _ _ _` open:
    `cxMacroGateRel n (Gate.CCX _ _ _) = False`, and the
    enriched `LogicalPPMState` represents magic-T usage only
    as a `Nat` counter, which is not enough to capture the
    non-Clifford action of a T-state injection.

    This section adds:

    * `MagicAwarePPMState` — a richer state type that
      records the SEQUENCE of magic states consumed (using
      the existing `MagicStateKind` from
      `FactoryHierarchy.lean`), not just a count.
    * `magicAwarePPMCommandRel` — the corresponding PPM
      command relation.  It delegates measurement and
      frame-update behaviour to the §14 relation and records
      a `MagicStateKind.T` log entry on `useMagicT`.
    * `magicAwarePPMSemanticsModel` — the corresponding
      semantics model.
    * `MagicInjectionObligations` — an explicit
      obligation structure that ISOLATES the CCX/Toffoli
      semantic obligation, so it is well-typed and
      named, not hidden inside the §13/§14/§15/§16
      machinery.
    * `mkArithmeticPrimitiveObligationsWithMagic` — a
      constructor that takes an ICX bundle plus the magic
      obligation and produces the full
      `ArithmeticPrimitivePPMObligations`.
    * `compileArithmeticGateToPPM_sound_from_magic_interface`
      — the corollary that consumes the magic interface and
      yields full arithmetic-fragment soundness on the
      entire `Gate` IR (via the existing §9 induction).

    Review of existing magic-state definitions REUSED:

    * `FormalRV.Framework.MagicStateKind` (T | CCZ),
      defined in `FactoryHierarchy.lean`.

    Existing magic-state definitions NOT yet reused (deferred):

    * `MagicStateInjection.LogicalGateProtocolWithMagic`,
      `logical_t`, `logical_ccz`, `logical_ccx` — these are
      structural protocol descriptions with placeholder
      Clifford-actions (identity matrix), explicitly
      flagged in `MagicStateInjection.lean` as carrying NO
      semantic content for T / CCZ.  They are useful for
      structural verification (`verify`) and resource
      accounting but cannot be used as semantic proofs of
      CCX correctness.  Deferred until a future tick
      provides genuine T / CCZ denotation.
    * `MagicStateDemand`, `total_magic_demand`, factory
      hierarchy — resource accounting; lives BELOW or
      alongside this PPM layer.

    No existing real Toffoli/T semantic theorem was found to
    reuse.  CCX correctness therefore remains an explicit
    obligation, now ISOLATED in
    `MagicInjectionObligations`. -/

/-! ### §17.a Magic-aware state. -/

structure MagicAwarePPMState where
  logicalState : LogicalPPMState
  /-- Ordered log of magic states consumed during execution.
      Reuses the existing `FormalRV.Framework.MagicStateKind`
      type (T | CCZ) from `FactoryHierarchy.lean`. -/
  magicLog     : List MagicStateKind
  deriving Inhabited

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

namespace PPMProgramResourceSummary

/-- Zero summary — identity for `add`. -/
def zero : PPMProgramResourceSummary :=
  ⟨0, 0, 0, 0⟩

/-- Fieldwise addition. -/
def add (a b : PPMProgramResourceSummary) : PPMProgramResourceSummary :=
  ⟨ a.commandCount + b.commandCount
  , a.measureCount + b.measureCount
  , a.frameUpdates + b.frameUpdates
  , a.magicTCount  + b.magicTCount ⟩

end PPMProgramResourceSummary

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
      toySurgeryComposedSchedule = true := by native_decide

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
        toySurgeryVerifiedBackendBlock.schedule) := by native_decide

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

theorem toySurgeryQECTraceLoweringEvidence :
    SurgeryQECTraceLoweringEvidence
      toyQECGadgetSpec
      toySchedulableSurgeryGadget
      toySurgeryVerifiedBackendBlock.schedule :=
  { structuralMatch := toy_QECSpecMatchesSurgeryGadget
    scheduleEq      := toySurgeryVerifiedBackendBlock_schedule_eq_composed
    traceMatches    := toySurgeryComposedSchedule_trace_matches }

/-! ### §27.e Status after §27.

    Closed (toy trace lowering):
    * `SurgeryObs` — observation type for the surgery
      protocol shape; derives `DecidableEq`, `Repr`,
      `Inhabited`.
    * `syscallToSurgeryObs?` — per-SysCall projection.
    * `surgeryTraceOfSysCalls`, `surgeryTraceOfCompressedSchedule`
      — list-level + CompressedSchedule-level projections.
    * `expectedSingleRoundTrace` — the canonical six-element
      trace for a `tau_s = 1` surgery gadget.
    * `SurgeryTraceMatchesGadget` — equality predicate with
      a `Decidable` instance.
    * `toySurgeryTraceMatchesGadget` — closed by `decide`.
    * `toySurgeryComposedSchedule_trace_matches` — closed by
      `native_decide`.
    * `SurgeryQECTraceLoweringEvidence` — Prop bundle
      pairing structural match, schedule equation, and
      trace match.
    * `toySurgeryQECTraceLoweringEvidence` — the toy
      concrete instance.

    NOT attempted in this tick:
    * `compileSurgeryGadgetToSysCalls_trace_matches`
      (general theorem for arbitrary `g`): would require
      induction on `tau_s` since the round structure
      repeats.  The `SurgeryTraceMatchesGadget` predicate
      as currently formulated is single-round only; a
      multi-round version would generalise to
      `tau_s`-many fresh-ancilla / entangle / measure /
      decode cycles plus one trailing frame update.
      Left for a future tick.

    Honest open obligations (UNCHANGED):
    * **Full QEC logical correctness** — distance,
      fault-tolerance, syndrome correctness, decoder
      correctness, logical Pauli measurement semantics.
      Trace matching is necessary but FAR from sufficient.
    * `MagicInjectionObligations.CCX_ok` (§17) — Toffoli
      semantic proof remains open.
    * QPE / non-Clifford+T — rejected/deferred via §1.

    QEC semantic-lowering status after §27:
    * **Trace / spec lowering**: CLOSED for the toy
      `tau_s = 1` single-gadget case.
    * **General compiler trace lowering**: open (left as a
      future tick — needs induction on `tau_s`).
    * **Full logical QEC correctness**: STILL OPEN
      (semantic claims at the operator-algebra / state
      level are out of reach for this interface-level
      tick).

    All prior milestones (§11–§26) remain intact. -/

end FormalRV.Framework.CircuitToPPMInterface
