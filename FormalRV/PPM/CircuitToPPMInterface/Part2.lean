import FormalRV.PPM.LayeredPPMQECInterface
import FormalRV.Core.QuantumGate
import FormalRV.PPM.PPMOperational
import FormalRV.PPM.FactoryHierarchy
import FormalRV.PPM.CircuitToPPMInterface.Part1

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

end FormalRV.Framework.CircuitToPPMInterface
