/-
  FormalRV.Framework.CircuitToPPMSemanticBridge — the
  semantic-refinement bridge from compiled ideal PPM programs
  to `Gate.applyNat`-level Boolean-function correctness, which
  is the semantic layer Shor's arithmetic stack uses.

  ## What this file IS

  A minimal, honest, parametric refinement interface stating:

      PPM-program execution starting from an `encodeBits f` state
      observationally refines `Gate.applyNat g f`.

  Combined with existing `Gate.applyNat`-level arithmetic
  correctness theorems (e.g., `cuccaro_target_val_eq_...`
  in `FormalRV.BQAlgo.CuccaroDecoded`), this lets us
  TRANSFER decoder-level postconditions from the logical-Gate
  layer down to the compiled ideal-PPM layer, without faking
  any quantum semantics.

  Concretely, the file provides:

  * `PPMRefinesApplyNat sem` — a parametric bridge interface
    pairing an encoding `(Nat → Bool) → State`, an observation
    relation `State → (Nat → Bool) → Prop`, and the per-gate
    refinement field `gateRel_applyNat_obs`.

  * `PPMReflectsGateRel sem g ppm` — the converse direction
    of `ImplementsGateAsPPM`, exposed honestly as a separate
    interface field (since `ImplementsGateAsPPM` alone is
    forward-only and cannot derive `applyNatSound`).

  * `LogicalGateAsPPMApplyNat sem bridge g` — the per-gate
    refinement predicate combining `ppmSound`
    (`ImplementsGateAsPPM`) and `applyNatSound` (the
    direction we actually need to transfer postconditions).

  * `LogicalGateAsPPMApplyNat.from_refinement` — the generic
    constructor.

  * `compileICXGateToPPM_applyNat_bridge` — instance for the
    ICX fragment using the existing `cxMacroPPMSemanticsModel`
    + `compileICXGateToPPM_sound_from_cxMacro`.

  * `compileArithmeticGateToPPM_applyNat_bridge_from_magic` —
    instance for the FULL arithmetic fragment (including CCX)
    via `compileArithmeticGateToPPM_sound_from_magic_interface`,
    modulo the existing `MagicInjectionObligations.CCX_ok`.

  * `applyNat_postcondition_transfers_to_PPM` — abstract
    `(Nat → Bool) → Prop` transfer theorem.

  * `decoder_postcondition_transfers_to_PPM` — decoder-shaped
    specialisation (`decode (Gate.applyNat g input) = expected`).

  * `shor_arithmetic_applyNat_correctness_transfers_to_PPM` —
    Shor-facing wrapper at arithmetic-block level.

  ## What this file is NOT

  This file does NOT prove:
  * QEC / lattice-surgery / backend SysCall schedules implement
    ideal PPM measurement (still open above the PPM layer).
  * Decoder correctness (the syndrome decoder is not modelled
    semantically anywhere in the project).
  * Syndrome correctness.
  * Code distance.
  * Fault tolerance.
  * CCX / Toffoli magic injection (only EXPOSED as an explicit
    `MagicInjectionObligations.CCX_ok` assumption; never
    discharged here).
  * QPE arbitrary / non-Clifford rotations (the arithmetic
    Gate IR has no rotation constructor).
  * Full Shor success-probability correctness.
  * Any concrete `PPMRefinesApplyNat` instance for
    `cxMacroPPMSemanticsModel n` (the bridge is parametric;
    we deliberately do NOT define a fake `encodeBits` /
    `observesBits` pair).

  The deliverable is the abstract refinement interface plus
  the transfer theorems.  Concrete model instances become a
  separate future tick whose only honest discharge requires a
  real semantic state model.
-/
import FormalRV.Arithmetic.Correctness
import FormalRV.PPM.Compiler.CircuitToPPMInterface

namespace FormalRV.Framework.CircuitToPPMSemanticBridge

open FormalRV.Framework
open FormalRV.Framework.CircuitToPPMInterface
open FormalRV.BQAlgo

/-! ## §1. The parametric PPM-to-`Gate.applyNat` refinement bridge.

    The bridge ties three things together:

    * an INPUT encoding `encodeBits : (Nat → Bool) → State`
      that lifts a Boolean bit-state into the abstract
      semantic state space `sem.State`;
    * an OUTPUT observation relation `observesBits : State →
      (Nat → Bool) → Prop` saying "this semantic state is
      observed as this bit-state";
    * the per-gate refinement field `gateRel_applyNat_obs`
      witnessing that whenever `sem.gateRel g` reaches state
      `σ'` from an encoded input, `σ'` indeed observes the
      `Gate.applyNat g`-image of the input.

    The bridge stays PARAMETRIC.  We deliberately do NOT
    provide a concrete `encodeBits` / `observesBits` instance
    for any specific `sem`, because no such honest instance
    exists in the project yet (`cxMacroPPMSemanticsModel`'s
    logical state does not yet carry a bit-readout map).
    Future ticks instantiate this bridge against a real
    semantic substrate (e.g. a stabilizer state plus a
    deterministic computational-basis readout function). -/

/-- Parametric semantic refinement bridge between an abstract
    `GateToPPMSemanticsModel` and the canonical Boolean-function
    Gate semantics `Gate.applyNat`. -/
structure PPMRefinesApplyNat (sem : GateToPPMSemanticsModel) where
  /-- Lift a Boolean bit-state into the model's state space. -/
  encodeBits      : (Nat → Bool) → sem.State
  /-- Observation relation between semantic states and bit-states. -/
  observesBits    : sem.State → (Nat → Bool) → Prop
  /-- Encoded bit-states observe themselves. -/
  encode_observes : ∀ f, observesBits (encodeBits f) f
  /-- The model's `gateRel g` from an encoded input lands in
      a state observing the `Gate.applyNat g`-image. -/
  gateRel_applyNat_obs :
    ∀ (g : Gate) (f : Nat → Bool) (σ' : sem.State),
      sem.gateRel g (encodeBits f) σ' →
      observesBits σ' (Gate.applyNat g f)

/-! ## §2. The converse-direction interface lemma.

    `ImplementsGateAsPPM sem g ppm` is the FORWARD direction:

      ∀ s t, sem.gateRel g s t → PPMProgramRel sem ppm s t.

    To certify `applyNatSound` we need the CONVERSE: from a
    PPM-program transition (the only thing the compiled
    artefact exposes) we must recover the gate-level
    transition, so the bridge's `gateRel_applyNat_obs` field
    can fire.

    `ImplementsGateAsPPM` alone is too weak: it lets
    PPMProgramRel be strictly more permissive than `gateRel`.
    Therefore we expose the converse honestly as a separate
    interface obligation `PPMReflectsGateRel`.  No `axiom`,
    no fake content.

    For deterministic semantic models the converse usually
    holds; discharging it for `cxMacroPPMSemanticsModel n` is
    a future tick. -/

/-- Converse of `ImplementsGateAsPPM`: every PPM-program
    transition factors through the gate's semantic relation.
    Honestly named so consumers see the asymmetry. -/
def PPMReflectsGateRel
    (sem : GateToPPMSemanticsModel)
    (g : Gate) (ppm : PPMProgram) : Prop :=
  ∀ s t, PPMProgramRel sem ppm s t → sem.gateRel g s t

/-! ## §3. The corrected logical-gate-as-PPM refinement
       predicate. -/

/-- A `Gate` `g` is refined by its compiled PPM program in the
    sense Shor's arithmetic stack needs:

    * `ppmSound`     — forward `ImplementsGateAsPPM`;
    * `applyNatSound` — every PPM-program execution from an
      encoded bit-input lands in a state observing the
      `Gate.applyNat g` image. -/
structure LogicalGateAsPPMApplyNat
    (sem : GateToPPMSemanticsModel)
    (bridge : PPMRefinesApplyNat sem)
    (g : Gate) : Prop where
  ppmSound :
    ImplementsGateAsPPM sem g (compileArithmeticGateToPPM g)
  applyNatSound :
    ∀ (f : Nat → Bool) (σ' : sem.State),
      PPMProgramRel sem
        (compileArithmeticGateToPPM g)
        (bridge.encodeBits f)
        σ' →
      bridge.observesBits σ' (Gate.applyNat g f)

/-! ## §4. The generic constructor.

    Combines `hppm : ImplementsGateAsPPM` (the forward
    direction) with the explicit converse `hreflect`
    (`PPMReflectsGateRel`) and the bridge's
    `gateRel_applyNat_obs` field.  The asymmetry is exposed
    in the signature, not hidden. -/

theorem LogicalGateAsPPMApplyNat.from_refinement
    (sem : GateToPPMSemanticsModel)
    (bridge : PPMRefinesApplyNat sem)
    (g : Gate)
    (hppm :
      ImplementsGateAsPPM sem g (compileArithmeticGateToPPM g))
    (hreflect :
      PPMReflectsGateRel sem g (compileArithmeticGateToPPM g)) :
    LogicalGateAsPPMApplyNat sem bridge g :=
  { ppmSound      := hppm
    applyNatSound := by
      intro f σ' hrun
      have hgate := hreflect _ _ hrun
      exact bridge.gateRel_applyNat_obs g f σ' hgate }

/-! ## §5. ICX-fragment refinement instance.

    Uses the existing
    `compileICXGateToPPM_sound_from_cxMacro` (§16.e of
    `CircuitToPPMInterface.lean`) to discharge `ppmSound`
    for any ICX-fragment `Gate` against `cxMacroPPMSemanticsModel n`.
    The converse direction (PPM-program transitions reflect
    back to `cxMacroGateRel`) is left as an explicit
    hypothesis — the cxMacro state model does not yet carry
    the structural inversion needed to prove it, and we
    refuse to invent one. -/

theorem compileICXGateToPPM_applyNat_bridge
    (n : Nat)
    (bridge : PPMRefinesApplyNat (cxMacroPPMSemanticsModel n))
    (g : Gate)
    (hICX : isICXGate g = true)
    (hreflect :
      PPMReflectsGateRel (cxMacroPPMSemanticsModel n) g
        (compileArithmeticGateToPPM g)) :
    LogicalGateAsPPMApplyNat (cxMacroPPMSemanticsModel n) bridge g :=
  LogicalGateAsPPMApplyNat.from_refinement _ bridge g
    (compileICXGateToPPM_sound_from_cxMacro n g hICX) hreflect

/-! ## §5.5. Discharging `PPMReflectsGateRel` for the ICX
       fragment over `cxMacroPPMSemanticsModel`.

    The §5 ICX bridge takes the converse-direction
    `PPMReflectsGateRel` hypothesis as an explicit argument
    because `ImplementsGateAsPPM` is forward-only.  In this
    section we DISCHARGE that hypothesis for the ICX fragment
    (I / X / CX / seq, no CCX) against the existing
    `cxMacroPPMSemanticsModel n`.

    The proof inverts the compiled PPM program structurally:
    the cxMacro `ppmCommandRel` exactly mirrors the macro
    decomposition baked into `cxMacroGateRel`, so each PPM
    step recovers the gate-level relation.  The argument is
    NOT a quantum-semantic equivalence — it just witnesses
    that the macro-specified gate relation and the macro
    compiler are inverses on the ICX fragment, which they
    were designed to be. -/

/-! ### §5.5.a Inversion lemmas for `PPMProgramRel`. -/

/-- Empty-program inversion: `PPMProgramRel sem [] s t` iff
    `s = t`. -/
theorem PPMProgramRel_nil_iff
    (sem : GateToPPMSemanticsModel) (s t : sem.State) :
    PPMProgramRel sem [] s t ↔ s = t := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h; rfl
  · cases h; exact PPMProgramRel.nil _

/-- Cons-program inversion: every `cmd :: rest` execution
    factors through an intermediate state reached by `cmd`. -/
theorem PPMProgramRel_cons_inv
    (sem : GateToPPMSemanticsModel)
    (cmd : PPMCommand) (rest : PPMProgram)
    (s u : sem.State)
    (h : PPMProgramRel sem (cmd :: rest) s u) :
    ∃ mid, sem.ppmCommandRel cmd s mid
        ∧ PPMProgramRel sem rest mid u := by
  cases h with
  | cons h1 h2 => exact ⟨_, h1, h2⟩

/-- Append-program inversion (forward direction of the
    existing iff `PPMProgramRel_append`).  Restated as a
    one-arrow form for convenience. -/
theorem PPMProgramRel_append_inv
    (sem : GateToPPMSemanticsModel)
    (p q : PPMProgram) (s u : sem.State)
    (h : PPMProgramRel sem (p ++ q) s u) :
    ∃ mid, PPMProgramRel sem p s mid
        ∧ PPMProgramRel sem q mid u :=
  (PPMProgramRel_append sem p q s u).mp h

/-! ### §5.5.b Primitive reflection for I / X / CX. -/

/-- `Gate.I` reflects: the empty compiled program forces
    `s = t`, which is exactly `cxMacroGateRel n Gate.I`. -/
theorem cxMacro_I_reflects_gateRel (n : Nat) :
    PPMReflectsGateRel (cxMacroPPMSemanticsModel n)
      Gate.I (compileArithmeticGateToPPM Gate.I) := by
  intro s t h
  show cxMacroGateRel n Gate.I s t
  have hst : s = t := (PPMProgramRel_nil_iff _ _ _).mp h
  -- `cxMacroGateRel n Gate.I s t = (t = s)` by definition
  exact hst.symm

/-- `Gate.X q` reflects: the singleton `applyFrameUpdate [q]`
    program forces the macro X-frame toggle.  `q : Nat` is
    the logical-qubit index. -/
theorem cxMacro_X_reflects_gateRel (n : Nat) (q : Nat) :
    PPMReflectsGateRel (cxMacroPPMSemanticsModel n)
      (Gate.X q) (compileArithmeticGateToPPM (Gate.X q)) := by
  intro s t h
  -- compileArithmeticGateToPPM (Gate.X q) = [applyFrameUpdate [q]]
  obtain ⟨mid, hcmd, hrest⟩ :=
    PPMProgramRel_cons_inv _ _ _ _ _ h
  have hmid_eq : mid = t := (PPMProgramRel_nil_iff _ _ _).mp hrest
  -- hcmd : logicalPPMCommandRel n (applyFrameUpdate [q]) s mid
  obtain ⟨h_stab, h_frame, h_magic⟩ := hcmd
  rw [toggleXList_singleton] at h_frame
  show cxMacroGateRel n (Gate.X q) s t
  rw [← hmid_eq]
  exact ⟨h_stab, h_frame, h_magic⟩

/-- `Gate.CX c tgt` reflects.  Inverts the two-command
    program `[measurePauliKind Z [c, tgt], applyFrameUpdate
    [tgt]]` step by step and recovers the existential
    Gottesman-branch witness baked into `cxMacroGateRel`. -/
theorem cxMacro_CX_reflects_gateRel
    (n : Nat) (c tgt : Nat) :
    PPMReflectsGateRel (cxMacroPPMSemanticsModel n)
      (Gate.CX c tgt)
      (compileArithmeticGateToPPM (Gate.CX c tgt)) := by
  intro s u h
  -- compileArithmeticGateToPPM (Gate.CX c tgt) =
  --   [measurePauliKind Z [c, tgt], applyFrameUpdate [tgt]]
  obtain ⟨mid₁, hstep1, hafter⟩ :=
    PPMProgramRel_cons_inv _ _ _ _ _ h
  obtain ⟨mid₂, hstep2, hnil⟩ :=
    PPMProgramRel_cons_inv _ _ _ _ _ hafter
  have hmid2_eq : mid₂ = u := (PPMProgramRel_nil_iff _ _ _).mp hnil
  -- hstep1 : logicalPPMCommandRel n (measurePauliKind Z [c,tgt]) s mid₁
  obtain ⟨P, hP_decode, hmid₁_stab, hmid₁_frame, hmid₁_magic⟩ := hstep1
  -- hstep2 : logicalPPMCommandRel n (applyFrameUpdate [tgt]) mid₁ mid₂
  obtain ⟨h_stab2, h_frame2, h_magic2⟩ := hstep2
  rw [toggleXList_singleton] at h_frame2
  show cxMacroGateRel n (Gate.CX c tgt) s u
  refine ⟨P, mid₁, hP_decode, hmid₁_stab, hmid₁_frame, hmid₁_magic,
          ?_, ?_, ?_⟩
  · rw [← hmid2_eq]; exact h_stab2
  · rw [← hmid2_eq]; exact h_frame2
  · rw [← hmid2_eq]; exact h_magic2

/-! ### §5.5.c Sequencing reflection. -/

/-- `Gate.seq g₁ g₂` reflects whenever both components
    reflect.  Inverts the appended compiled program via
    `PPMProgramRel_append_inv`. -/
theorem cxMacro_seq_reflects_gateRel
    (n : Nat) (g₁ g₂ : Gate)
    (h₁ :
      PPMReflectsGateRel (cxMacroPPMSemanticsModel n)
        g₁ (compileArithmeticGateToPPM g₁))
    (h₂ :
      PPMReflectsGateRel (cxMacroPPMSemanticsModel n)
        g₂ (compileArithmeticGateToPPM g₂)) :
    PPMReflectsGateRel (cxMacroPPMSemanticsModel n)
      (Gate.seq g₁ g₂)
      (compileArithmeticGateToPPM (Gate.seq g₁ g₂)) := by
  intro s u h
  -- compileArithmeticGateToPPM (Gate.seq g₁ g₂)
  --   = compileArithmeticGateToPPM g₁ ++ compileArithmeticGateToPPM g₂
  rw [compileArithmeticGateToPPM_seq] at h
  obtain ⟨mid, hp1, hp2⟩ :=
    PPMProgramRel_append_inv _ _ _ _ _ h
  show cxMacroGateRel n (Gate.seq g₁ g₂) s u
  exact ⟨mid, h₁ s mid hp1, h₂ mid u hp2⟩

/-! ### §5.5.d Full ICX-fragment reflection. -/

/-- For every Gate `g` in the ICX fragment (no CCX), the
    compiled PPM program reflects back to `cxMacroGateRel n`.
    Proven by induction on `g` matching the §16.e forward
    soundness proof's case split. -/
theorem compileICXGateToPPM_reflects_gateRel_from_cxMacro
    (n : Nat) :
    ∀ g, isICXGate g = true →
      PPMReflectsGateRel (cxMacroPPMSemanticsModel n) g
        (compileArithmeticGateToPPM g) := by
  intro g
  induction g with
  | I =>
      intro _
      exact cxMacro_I_reflects_gateRel n
  | X q =>
      intro _
      exact cxMacro_X_reflects_gateRel n q
  | CX c tgt =>
      intro _
      exact cxMacro_CX_reflects_gateRel n c tgt
  | CCX _ _ _ =>
      intro h
      simp [isICXGate] at h
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hICX
      have h_and : (isICXGate g₁ && isICXGate g₂) = true := hICX
      rw [Bool.and_eq_true] at h_and
      obtain ⟨h1, h2⟩ := h_and
      exact cxMacro_seq_reflects_gateRel n g₁ g₂
        (ih₁ h1) (ih₂ h2)

/-! ### §5.5.e `hreflect`-free ICX `applyNat` bridge.

    Composes §5's `compileICXGateToPPM_applyNat_bridge` with
    the newly-discharged §5.5.d reflection theorem, yielding
    the ICX `Gate.applyNat` bridge without the external
    converse-direction obligation. -/

theorem compileICXGateToPPM_applyNat_bridge_no_reflect_hyp
    (n : Nat)
    (bridge : PPMRefinesApplyNat (cxMacroPPMSemanticsModel n))
    (g : Gate)
    (hICX : isICXGate g = true) :
    LogicalGateAsPPMApplyNat (cxMacroPPMSemanticsModel n) bridge g :=
  compileICXGateToPPM_applyNat_bridge n bridge g hICX
    (compileICXGateToPPM_reflects_gateRel_from_cxMacro n g hICX)

/-! ## §6. Generic `(Nat → Bool) → Prop` postcondition
       transfer. -/

/-- Any predicate `P` over output bit-states that holds for
    `Gate.applyNat g input` also holds for some bit-state
    observed by the PPM-program output state.  This is the
    abstract semantic transport from `Gate.applyNat`-level
    correctness to PPM-program execution. -/
theorem applyNat_postcondition_transfers_to_PPM
    (sem : GateToPPMSemanticsModel)
    (bridge : PPMRefinesApplyNat sem)
    (g : Gate)
    (P : (Nat → Bool) → Prop)
    (hbridge : LogicalGateAsPPMApplyNat sem bridge g)
    (input : Nat → Bool)
    (σ' : sem.State)
    (hrun :
      PPMProgramRel sem
        (compileArithmeticGateToPPM g)
        (bridge.encodeBits input)
        σ')
    (hpost : P (Gate.applyNat g input)) :
    ∃ output, bridge.observesBits σ' output ∧ P output :=
  ⟨Gate.applyNat g input,
    hbridge.applyNatSound input σ' hrun,
    hpost⟩

/-! ## §7. Decoder-shaped postcondition transfer.

    The Shor arithmetic stack's correctness theorems have
    the shape:

        decode (Gate.applyNat g input) = expected

    where `decode` is one of the project's Nat decoders, e.g.

    * `FormalRV.BQAlgo.cuccaro_target_val bits q_start`
    * `FormalRV.BQAlgo.gidney_target_val bits`

    or any other `(Nat → Bool) → Nat` readout used by the
    arithmetic-circuit correctness theorems.  This corollary
    transports such a decoder-shaped postcondition through
    the bridge. -/

theorem decoder_postcondition_transfers_to_PPM
    (sem : GateToPPMSemanticsModel)
    (bridge : PPMRefinesApplyNat sem)
    (g : Gate)
    (decode : (Nat → Bool) → Nat)
    (expected : Nat)
    (hbridge : LogicalGateAsPPMApplyNat sem bridge g)
    (input : Nat → Bool)
    (σ' : sem.State)
    (hrun :
      PPMProgramRel sem
        (compileArithmeticGateToPPM g)
        (bridge.encodeBits input)
        σ')
    (hgate : decode (Gate.applyNat g input) = expected) :
    ∃ output,
      bridge.observesBits σ' output ∧ decode output = expected :=
  applyNat_postcondition_transfers_to_PPM
    sem bridge g
    (fun output => decode output = expected)
    hbridge input σ' hrun hgate

/-! ## §8. Shor-facing arithmetic wrapper.

    The Shor stack does not need anything more than the
    decoder transfer.  We give an explicit Shor-facing alias
    to mark the layer in the public API, and to make the
    semantic story explicit in the proof script.

    This is THE first serious semantic bridge between the
    Gate.applyNat-level arithmetic correctness theorems and
    the compiled ideal-PPM execution layer. -/

theorem shor_arithmetic_applyNat_correctness_transfers_to_PPM
    (sem : GateToPPMSemanticsModel)
    (bridge : PPMRefinesApplyNat sem)
    (g : Gate)
    (decode : (Nat → Bool) → Nat)
    (input : Nat → Bool)
    (expected : Nat)
    (hbridge : LogicalGateAsPPMApplyNat sem bridge g)
    (σ' : sem.State)
    (hrun :
      PPMProgramRel sem
        (compileArithmeticGateToPPM g)
        (bridge.encodeBits input)
        σ')
    (hGateCorrect : decode (Gate.applyNat g input) = expected) :
    ∃ output,
      bridge.observesBits σ' output ∧ decode output = expected :=
  decoder_postcondition_transfers_to_PPM
    sem bridge g decode expected hbridge input σ' hrun hGateCorrect

/-! ## §8.5. Shor-facing ICX decoder transfer, without
       `hreflect`.

    Combines §5.5.e's no-`hreflect` ICX bridge with §8's
    decoder transfer.  This is the publicly-callable
    Shor-arithmetic ICX statement: given a Gate.applyNat-level
    decoder postcondition (e.g.
    `cuccaro_target_val bits q_start (Gate.applyNat g input) = expected`),
    the same postcondition is observable on the compiled
    PPM execution, with NO external converse-direction
    obligation.  The bridge is still parametric — concrete
    `encodeBits` / `observesBits` for `LogicalPPMState` is
    deferred. -/

theorem shor_arithmetic_ICX_correctness_transfers_to_PPM_no_reflect_hyp
    (n : Nat)
    (bridge : PPMRefinesApplyNat (cxMacroPPMSemanticsModel n))
    (g : Gate)
    (hICX : isICXGate g = true)
    (decode : (Nat → Bool) → Nat)
    (input : Nat → Bool)
    (expected : Nat)
    (σ' : (cxMacroPPMSemanticsModel n).State)
    (hrun :
      PPMProgramRel (cxMacroPPMSemanticsModel n)
        (compileArithmeticGateToPPM g)
        (bridge.encodeBits input)
        σ')
    (hGateCorrect : decode (Gate.applyNat g input) = expected) :
    ∃ output,
      bridge.observesBits σ' output ∧ decode output = expected :=
  shor_arithmetic_applyNat_correctness_transfers_to_PPM
    (cxMacroPPMSemanticsModel n) bridge g decode input expected
    (compileICXGateToPPM_applyNat_bridge_no_reflect_hyp n bridge g hICX)
    σ' hrun hGateCorrect

/-! ## §9. Full-arithmetic refinement instance modulo magic /
       CCX, via the existing magic interface.

    Uses `compileArithmeticGateToPPM_sound_from_magic_interface`
    (§17.f of `CircuitToPPMInterface.lean`) to discharge
    `ppmSound` for the ENTIRE arithmetic Gate IR (I, X, CX,
    CCX, seq), given:

    * an `ArithmeticICXPrimitivePPMObligations sem` (already
      closed for `cxMacroPPMSemanticsModel n` via
      `cxMacroICXObligations n`);
    * a `MagicInjectionObligations sem` (the deferred CCX
      obligation; the entire magic injection / Toffoli
      semantic correctness is ISOLATED here and NOT proved);
    * the standard sequencing law on `gateRel`;
    * the converse-direction `PPMReflectsGateRel` for the
      compiled program of `g`.

    Closing the CCX obligation is BEYOND scope; we expose it
    as an explicit assumption per the project's depth-of-
    formalization policy. -/

theorem compileArithmeticGateToPPM_applyNat_bridge_from_magic
    (sem : GateToPPMSemanticsModel)
    (icx : ArithmeticICXPrimitivePPMObligations sem)
    (mag : MagicInjectionObligations sem)
    (hseq :
      ∀ g₁ g₂ s u,
        sem.gateRel (Gate.seq g₁ g₂) s u ↔
          ∃ t, sem.gateRel g₁ s t ∧ sem.gateRel g₂ t u)
    (bridge : PPMRefinesApplyNat sem)
    (g : Gate)
    (hreflect :
      PPMReflectsGateRel sem g (compileArithmeticGateToPPM g)) :
    LogicalGateAsPPMApplyNat sem bridge g :=
  LogicalGateAsPPMApplyNat.from_refinement sem bridge g
    (compileArithmeticGateToPPM_sound_from_magic_interface
        sem icx mag hseq g)
    hreflect

/-! ## §10. Shor-arithmetic transfer using the full magic
       interface.

    Composes §9's full-arithmetic refinement instance with
    §8's decoder-shaped postcondition transfer.  This is the
    statement Shor's arithmetic uses directly:

      Given any Gate.applyNat-level correctness
        `decode (Gate.applyNat g input) = expected`,
      plus a faithful PPM bridge, plus the (deferred) magic
      obligation, plus the converse direction,
      the same decoder postcondition holds on the compiled
      PPM execution's output. -/

theorem shor_arithmetic_full_correctness_transfers_to_PPM_modulo_magic
    (sem : GateToPPMSemanticsModel)
    (icx : ArithmeticICXPrimitivePPMObligations sem)
    (mag : MagicInjectionObligations sem)
    (hseq :
      ∀ g₁ g₂ s u,
        sem.gateRel (Gate.seq g₁ g₂) s u ↔
          ∃ t, sem.gateRel g₁ s t ∧ sem.gateRel g₂ t u)
    (bridge : PPMRefinesApplyNat sem)
    (g : Gate)
    (decode : (Nat → Bool) → Nat)
    (input : Nat → Bool)
    (expected : Nat)
    (σ' : sem.State)
    (hreflect :
      PPMReflectsGateRel sem g (compileArithmeticGateToPPM g))
    (hrun :
      PPMProgramRel sem
        (compileArithmeticGateToPPM g)
        (bridge.encodeBits input)
        σ')
    (hGateCorrect : decode (Gate.applyNat g input) = expected) :
    ∃ output,
      bridge.observesBits σ' output ∧ decode output = expected :=
  shor_arithmetic_applyNat_correctness_transfers_to_PPM
    sem bridge g decode input expected
    (compileArithmeticGateToPPM_applyNat_bridge_from_magic
      sem icx mag hseq bridge g hreflect)
    σ' hrun hGateCorrect

/-! ## §11. Status summary.

    Closed in this file:

    * `PPMRefinesApplyNat` — parametric bridge interface.
    * `PPMReflectsGateRel` — converse-direction interface
      obligation, honestly exposed.
    * `LogicalGateAsPPMApplyNat` — per-gate refinement
      predicate.
    * `LogicalGateAsPPMApplyNat.from_refinement` — generic
      constructor from `ImplementsGateAsPPM` + converse +
      bridge field.
    * `compileICXGateToPPM_applyNat_bridge` — ICX-fragment
      instance (still takes `hreflect`).
    * `PPMProgramRel_nil_iff` / `PPMProgramRel_cons_inv` /
      `PPMProgramRel_append_inv` — structural inversion
      lemmas.
    * `cxMacro_I_reflects_gateRel` /
      `cxMacro_X_reflects_gateRel` /
      `cxMacro_CX_reflects_gateRel` /
      `cxMacro_seq_reflects_gateRel` — primitive + seq
      reflection lemmas for the CX-aware macro model.
    * `compileICXGateToPPM_reflects_gateRel_from_cxMacro` —
      full ICX-fragment converse-direction theorem.
    * `compileICXGateToPPM_applyNat_bridge_no_reflect_hyp` —
      hreflect-free ICX `Gate.applyNat` bridge.
    * `applyNat_postcondition_transfers_to_PPM` — generic
      Prop-level transfer.
    * `decoder_postcondition_transfers_to_PPM` — Nat-decoder
      transfer.
    * `shor_arithmetic_applyNat_correctness_transfers_to_PPM`
      — Shor-facing alias.
    * `shor_arithmetic_ICX_correctness_transfers_to_PPM_no_reflect_hyp`
      — Shor-facing ICX decoder transfer with NO external
      converse-direction obligation.
    * `compileArithmeticGateToPPM_applyNat_bridge_from_magic`
      — full Gate IR refinement instance, modulo
      `MagicInjectionObligations.CCX_ok`.
    * `shor_arithmetic_full_correctness_transfers_to_PPM_modulo_magic`
      — full-stack Shor decoder transfer, modulo magic.

    Deferred (explicit obligations, not silent axioms):

    * Concrete `PPMRefinesApplyNat (cxMacroPPMSemanticsModel n)`
      instance (needs a real bit-readout function on
      `LogicalPPMState`).
    * `MagicInjectionObligations.CCX_ok` (Toffoli semantic
      correctness).
    * Reflection (`PPMReflectsGateRel`) for the
      magic-aware model on CCX: blocked on the same
      Toffoli semantic content.
    * QEC / surgery / backend lowering of ideal PPM
      (orthogonal; still open above this file).
    * QPE / non-Clifford rotations (out of scope of the
      arithmetic Gate IR).
    * Full Shor success-probability theorem (open). -/

end FormalRV.Framework.CircuitToPPMSemanticBridge
