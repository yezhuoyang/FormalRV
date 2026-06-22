/-
  FormalRV.Framework.CircuitToPPMObservationBridge — the
  honest Boolean-basis (computational-basis) PPM reference
  semantics that CLOSES the `PPMRefinesApplyNat` obligation
  for the ICX fragment without any external bridge,
  reflection, or magic assumption.

  ## E20 review finding (why a new model is needed)

  `LogicalPPMState` (in `CircuitToPPMInterface.lean`) carries
  `stabilizer : PPMOp.StabilizerState`, `frame :
  LogicalPauliFrame` (lists of qubits with deferred X/Z
  corrections), and `magicUsed : Nat`.  None of these
  exposes a Boolean valuation `Nat → Bool` on logical
  qubits.  Moreover,

      cxMacroGateRel n (Gate.CX c tgt) s u

  toggles the X-frame on `tgt` UNCONDITIONALLY (no
  dependence on the control's value).  Boolean `Gate.CX` is
  CONTROLLED: target flips iff control bit is `1`.  The
  cxMacro relation therefore does NOT match Boolean
  `Gate.CX` semantics, and a concrete
  `PPMRefinesApplyNat (cxMacroPPMSemanticsModel n)` instance
  cannot be honestly defined.

  Per the E18/E19/E20 honesty rule we do NOT fake an
  observation map on `LogicalPPMState`.  Instead this file
  introduces a SEPARATE reference Boolean-basis model:

      basisPPMSemanticsModel : GateToPPMSemanticsModel

  whose `gateRel` matches `Gate.applyNat` exactly, and whose
  `ppmCommandRel` is the unique deterministic interpretation
  under which the existing compiler's ICX-fragment PPM
  expansion is sound.

  ## What this file proves

  * `BasisPPMState` and `basisPPMSemanticsModel`.
  * `basisRefinesApplyNat` — concrete `PPMRefinesApplyNat`
    instance with honest `encodeBits`/`observesBits`/
    `gateRel_applyNat_obs`.
  * `basisPPMSound_ICX` — ICX forward `ImplementsGateAsPPM`.
  * `basisPPMReflects_ICX` — ICX `PPMReflectsGateRel`.
  * `compileICXGateToPPM_applyNat_bridge_basisPPM` — ICX
    `LogicalGateAsPPMApplyNat` instance with NO external
    arguments (no `bridge`, no `hreflect`).
  * `shor_arithmetic_ICX_correctness_transfers_to_basisPPM`
    — Shor-facing ICX decoder transfer with NO external
    arguments.

  ## Honesty boundary

  * `basisPPMSemanticsModel` is a REFERENCE Boolean-basis
    semantics.  It is NOT a claim that real lattice-surgery
    /stabilizer PPM physically realises CX via the
    `[measurePauliKind Z; applyFrameUpdate]` placeholder
    expansion.  In real lattice surgery, a logical CNOT
    uses ancilla qubits + conditional Pauli corrections
    determined by measurement outcomes.  Our basis
    `ppmCommandRel` is the deterministic interpretation that
    makes the existing placeholder compiler sound; it does
    NOT model measurement-outcome randomness or
    fault-tolerance.

  * `cxMacroPPMSemanticsModel` and `basisPPMSemanticsModel`
    are NOT claimed equivalent or simulation-related.  Any
    bridge between them is a separate future deliverable
    (it would need either an outcome-tracking observation
    map or a reformulation of `cxMacroGateRel` to encode
    control-dependence).

  * CCX/Toffoli is NOT proved here.  `basisPPMGateRel` does
    include a Boolean Toffoli case (matching
    `Gate.applyNat (Gate.CCX a b c)`), but the
    `useMagicT` command's interpretation is identity-on-bits
    + magic-count increment, which does NOT match Boolean
    Toffoli composed with `measurePauliKind Z` +
    `applyFrameUpdate`.  CCX therefore remains an open
    obligation; we explicitly do NOT claim ICX coverage of
    CCX.

  * QEC/surgery/backend lowering of ideal PPM remains open
    above this file.

  * QPE / non-Clifford rotations remain out of scope (no
    rotation constructor in the arithmetic Gate IR).
-/
import FormalRV.PPM.Semantics.CircuitToPPMSemanticBridge

namespace FormalRV.Framework.CircuitToPPMObservationBridge

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.Framework.CircuitToPPMInterface
open FormalRV.Framework.CircuitToPPMSemanticBridge
open FormalRV.BQAlgo

/-! ## §1. Boolean-basis state. -/

/-- A computational-basis PPM state: a Boolean bit-function
    plus the magic-state resource counter.  No stabilizer or
    Pauli frame — this is a REFERENCE basis model, not a
    physical-substrate model. -/
structure BasisPPMState where
  bits      : Nat → Bool
  magicUsed : Nat

instance : Inhabited BasisPPMState := ⟨{ bits := fun _ => false, magicUsed := 0 }⟩

/-! ## §2. Boolean-basis gate relation.

    Matches `Gate.applyNat` exactly on bits; tracks magic
    usage with a `+1` on `CCX` (magic-T injection accounting,
    not semantic correctness — see honesty boundary). -/

def basisPPMGateRel : Gate → BasisPPMState → BasisPPMState → Prop
  | .I,         s, t => t = s
  | .X q,       s, t =>
      t.bits = update s.bits q (!s.bits q)
      ∧ t.magicUsed = s.magicUsed
  | .CX c tgt,  s, t =>
      t.bits = update s.bits tgt (xor (s.bits tgt) (s.bits c))
      ∧ t.magicUsed = s.magicUsed
  | .CCX a b c, s, t =>
      t.bits = update s.bits c (xor (s.bits c) (s.bits a && s.bits b))
      ∧ t.magicUsed = s.magicUsed + 1
  | .seq g₁ g₂, s, u =>
      ∃ mid, basisPPMGateRel g₁ s mid ∧ basisPPMGateRel g₂ mid u

/-! ## §3. Boolean-basis PPM command relation.

    The unique deterministic interpretation under which the
    existing compiler's ICX expansion computes
    `Gate.applyNat`.

    * `applyFrameUpdate qs`: unconditional XOR-1 (bit flip)
      on each qubit in `qs`.  Matches `Gate.X q`'s singleton
      compile.
    * `measurePauliKind Z [c, tgt]`: writes `bits[tgt] :=
      xor bits[tgt] (¬ bits[c])`.  This is the unique
      single-step that makes
      `[measurePauliKind Z [c, tgt]; applyFrameUpdate [tgt]]`
      compute Boolean `Gate.CX c tgt`: after the
      measurement step `bits[tgt] = xor s.bits[tgt]
      (¬ s.bits[c])`, the subsequent unconditional flip
      yields `xor s.bits[tgt] s.bits[c]`.
    * Other `measurePauliKind` cases: identity (we do not
      interpret them in this model).
    * `useMagicT _`: identity on bits + magic-count
      increment.  This does NOT semantically realise
      magic-T injection. -/

def basisPPMCommandRel :
    PPMCommand → BasisPPMState → BasisPPMState → Prop
  | .applyFrameUpdate qs, s, t =>
      t.bits = qs.foldl (fun bs q => update bs q (!bs q)) s.bits
      ∧ t.magicUsed = s.magicUsed
  | .measurePauliKind PauliKind.Z [c, tgt], s, t =>
      t.bits = update s.bits tgt (xor (s.bits tgt) (!s.bits c))
      ∧ t.magicUsed = s.magicUsed
  | .measurePauliKind _ _, s, t =>
      t = s
  | .useMagicT _, s, t =>
      t.bits = s.bits
      ∧ t.magicUsed = s.magicUsed + 1

/-! ## §4. Boolean-basis semantics model. -/

def basisPPMSemanticsModel : GateToPPMSemanticsModel :=
  { State         := BasisPPMState
    gateRel       := basisPPMGateRel
    ppmCommandRel := basisPPMCommandRel }

/-! ## §5. Concrete encoding + observation. -/

/-- Encode a Boolean bit-state as a `BasisPPMState` with
    zero magic usage. -/
def basisEncodeBits (f : Nat → Bool) : basisPPMSemanticsModel.State :=
  { bits := f, magicUsed := 0 }

/-- A `BasisPPMState` observes the bit-function it carries
    on its `bits` field. -/
def basisObservesBits
    (s : basisPPMSemanticsModel.State) (f : Nat → Bool) : Prop :=
  s.bits = f

theorem basisEncode_observes (f : Nat → Bool) :
    basisObservesBits (basisEncodeBits f) f := rfl

/-! ## §6. The bridge field: `gateRel` of a basis state observes
       `Gate.applyNat` of the encoded bits.

    Proven by induction on `g`, generalised over arbitrary
    start states (not just `basisEncodeBits f`). -/

/-- Generalised statement: any `basisPPMGateRel` transition
    produces a target state whose `bits` field equals
    `Gate.applyNat g` applied to the source's bits. -/
theorem basisPPMGateRel_imp_applyNat
    (g : Gate) :
    ∀ (s σ' : BasisPPMState),
      basisPPMGateRel g s σ' → σ'.bits = Gate.applyNat g s.bits := by
  induction g with
  | I =>
      intro s σ' h
      have hst : σ' = s := h
      rw [hst]
      rfl
  | X q =>
      intro s σ' h
      exact h.1
  | CX c tgt =>
      intro s σ' h
      exact h.1
  | CCX a b c =>
      intro s σ' h
      exact h.1
  | seq g₁ g₂ ih₁ ih₂ =>
      intro s σ' h
      obtain ⟨mid, h₁, h₂⟩ := h
      have hb1 : mid.bits = Gate.applyNat g₁ s.bits := ih₁ s mid h₁
      have hb2 : σ'.bits = Gate.applyNat g₂ mid.bits := ih₂ mid σ' h₂
      rw [hb2, hb1]
      rfl

/-- The bridge field for `PPMRefinesApplyNat`. -/
theorem basisGateRel_applyNat_obs
    (g : Gate) (f : Nat → Bool) (σ' : basisPPMSemanticsModel.State)
    (h : basisPPMSemanticsModel.gateRel g (basisEncodeBits f) σ') :
    basisObservesBits σ' (Gate.applyNat g f) := by
  show σ'.bits = Gate.applyNat g f
  have := basisPPMGateRel_imp_applyNat g (basisEncodeBits f) σ' h
  exact this

/-! ## §7. The concrete `PPMRefinesApplyNat` instance. -/

def basisRefinesApplyNat : PPMRefinesApplyNat basisPPMSemanticsModel :=
  { encodeBits           := basisEncodeBits
    observesBits         := basisObservesBits
    encode_observes      := basisEncode_observes
    gateRel_applyNat_obs := basisGateRel_applyNat_obs }

/-! ## §8. Forward soundness `ImplementsGateAsPPM` for ICX.

    Builds the PPM-program execution witness from each
    `basisPPMGateRel` transition.  CX uses the
    intermediate-state construction laid out in §3. -/

theorem basisPPM_I_sound :
    ImplementsGateAsPPM basisPPMSemanticsModel Gate.I
      (compileArithmeticGateToPPM Gate.I) := by
  intro s t hGate
  -- hGate : basisPPMGateRel Gate.I s t  i.e. t = s
  have hst : t = s := hGate
  rw [hst]
  exact PPMProgramRel.nil s

theorem basisPPM_X_sound (q : Nat) :
    ImplementsGateAsPPM basisPPMSemanticsModel (Gate.X q)
      (compileArithmeticGateToPPM (Gate.X q)) := by
  intro s t hGate
  -- hGate : t.bits = update s.bits q (!s.bits q) ∧ t.magicUsed = s.magicUsed
  obtain ⟨hbits, hmag⟩ := hGate
  -- Program is [applyFrameUpdate [q]].  One cons + one nil.
  refine PPMProgramRel.cons (cmd := PPMCommand.applyFrameUpdate [q]) ?_ (PPMProgramRel.nil t)
  show basisPPMCommandRel (PPMCommand.applyFrameUpdate [q]) s t
  refine ⟨?_, hmag⟩
  show t.bits = ([q].foldl (fun bs q' => update bs q' (!bs q')) s.bits)
  simp [List.foldl]
  exact hbits

theorem basisPPM_CX_sound (c tgt : Nat) :
    ImplementsGateAsPPM basisPPMSemanticsModel (Gate.CX c tgt)
      (compileArithmeticGateToPPM (Gate.CX c tgt)) := by
  intro s u hGate
  obtain ⟨hbits, hmag⟩ := hGate
  -- Intermediate state mid: bits[tgt] := xor s.bits[tgt] (!s.bits[c]); magicUsed = s.magicUsed.
  let mid : BasisPPMState :=
    { bits := update s.bits tgt (xor (s.bits tgt) (!s.bits c))
      magicUsed := s.magicUsed }
  -- Step 1: measurePauliKind Z [c, tgt] s mid.
  have hstep1 :
      basisPPMCommandRel (PPMCommand.measurePauliKind PauliKind.Z [c, tgt])
        s mid := by
    refine ⟨?_, rfl⟩
    show mid.bits = update s.bits tgt (xor (s.bits tgt) (!s.bits c))
    rfl
  -- Step 2: applyFrameUpdate [tgt] mid u.
  have hstep2 :
      basisPPMCommandRel (PPMCommand.applyFrameUpdate [tgt]) mid u := by
    refine ⟨?_, ?_⟩
    · -- Goal: u.bits = [tgt].foldl ... mid.bits
      simp only [List.foldl_cons, List.foldl_nil]
      -- Goal: u.bits = update mid.bits tgt (!mid.bits tgt)
      -- Unfold mid.bits to its definitional body
      show u.bits = update
        (update s.bits tgt (xor (s.bits tgt) (!s.bits c))) tgt
        (! update s.bits tgt (xor (s.bits tgt) (!s.bits c)) tgt)
      rw [hbits]
      funext i
      by_cases hi : i = tgt
      · subst hi
        simp only [update_eq]
        -- Goal: xor (s.bits i) (s.bits c) = !(xor (s.bits i) (!s.bits c))
        cases s.bits i <;> cases s.bits c <;> rfl
      · rw [update_neq _ _ _ _ hi, update_neq _ _ _ _ hi, update_neq _ _ _ _ hi]
    · show u.magicUsed = s.magicUsed
      rw [hmag]
  -- Assemble.
  exact PPMProgramRel.cons hstep1 (PPMProgramRel.cons hstep2 (PPMProgramRel.nil u))

theorem basisPPM_seq_sound (g₁ g₂ : Gate)
    (h₁ : ImplementsGateAsPPM basisPPMSemanticsModel g₁
            (compileArithmeticGateToPPM g₁))
    (h₂ : ImplementsGateAsPPM basisPPMSemanticsModel g₂
            (compileArithmeticGateToPPM g₂)) :
    ImplementsGateAsPPM basisPPMSemanticsModel (Gate.seq g₁ g₂)
      (compileArithmeticGateToPPM (Gate.seq g₁ g₂)) := by
  intro s u hGate
  obtain ⟨mid, hg1, hg2⟩ := hGate
  have hp1 := h₁ s mid hg1
  have hp2 := h₂ mid u hg2
  rw [compileArithmeticGateToPPM_seq]
  exact (PPMProgramRel_append _ _ _ s u).mpr ⟨mid, hp1, hp2⟩

theorem basisPPMSound_ICX :
    ∀ g, isICXGate g = true →
      ImplementsGateAsPPM basisPPMSemanticsModel g
        (compileArithmeticGateToPPM g) := by
  intro g
  induction g with
  | I => intro _; exact basisPPM_I_sound
  | X q => intro _; exact basisPPM_X_sound q
  | CX c tgt => intro _; exact basisPPM_CX_sound c tgt
  | CCX _ _ _ => intro h; simp [isICXGate] at h
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hICX
      have h_and : (isICXGate g₁ && isICXGate g₂) = true := hICX
      rw [Bool.and_eq_true] at h_and
      obtain ⟨ha, hb⟩ := h_and
      exact basisPPM_seq_sound g₁ g₂ (ih₁ ha) (ih₂ hb)

/-! ## §9. Reflection `PPMReflectsGateRel` for ICX. -/

theorem basisPPM_I_reflects :
    PPMReflectsGateRel basisPPMSemanticsModel Gate.I
      (compileArithmeticGateToPPM Gate.I) := by
  intro s t h
  show basisPPMGateRel Gate.I s t
  have hst : s = t := (PPMProgramRel_nil_iff _ _ _).mp h
  -- basisPPMGateRel Gate.I s t  ↔  t = s
  exact hst.symm

theorem basisPPM_X_reflects (q : Nat) :
    PPMReflectsGateRel basisPPMSemanticsModel (Gate.X q)
      (compileArithmeticGateToPPM (Gate.X q)) := by
  intro s t h
  obtain ⟨mid, hcmd, hrest⟩ :=
    PPMProgramRel_cons_inv _ _ _ _ _ h
  have hmid_eq : mid = t := (PPMProgramRel_nil_iff _ _ _).mp hrest
  -- hcmd : basisPPMCommandRel (applyFrameUpdate [q]) s mid
  obtain ⟨h_bits, h_mag⟩ := hcmd
  -- h_bits : mid.bits = [q].foldl (fun bs q' => update bs q' (!bs q')) s.bits
  -- Simplify the foldl on [q]
  simp [List.foldl] at h_bits
  show basisPPMGateRel (Gate.X q) s t
  refine ⟨?_, ?_⟩
  · rw [← hmid_eq]; exact h_bits
  · rw [← hmid_eq]; exact h_mag

theorem basisPPM_CX_reflects (c tgt : Nat) :
    PPMReflectsGateRel basisPPMSemanticsModel (Gate.CX c tgt)
      (compileArithmeticGateToPPM (Gate.CX c tgt)) := by
  intro s u h
  obtain ⟨mid₁, hstep1, hafter⟩ :=
    PPMProgramRel_cons_inv _ _ _ _ _ h
  obtain ⟨mid₂, hstep2, hnil⟩ :=
    PPMProgramRel_cons_inv _ _ _ _ _ hafter
  have hmid2 : mid₂ = u := (PPMProgramRel_nil_iff _ _ _).mp hnil
  -- hstep1 : basisPPMCommandRel (measurePauliKind Z [c, tgt]) s mid₁
  obtain ⟨h_mbits, h_mmag⟩ := hstep1
  -- hstep2 : basisPPMCommandRel (applyFrameUpdate [tgt]) mid₁ mid₂
  obtain ⟨h_fbits, h_fmag⟩ := hstep2
  simp [List.foldl] at h_fbits
  show basisPPMGateRel (Gate.CX c tgt) s u
  refine ⟨?_, ?_⟩
  · -- u.bits = update s.bits tgt (xor s.bits[tgt] s.bits[c])
    rw [← hmid2, h_fbits, h_mbits]
    funext i
    by_cases hi : i = tgt
    · subst hi
      simp only [update_eq]
      cases s.bits i <;> cases s.bits c <;> rfl
    · rw [update_neq _ _ _ _ hi, update_neq _ _ _ _ hi, update_neq _ _ _ _ hi]
  · rw [← hmid2, h_fmag, h_mmag]

theorem basisPPM_seq_reflects (g₁ g₂ : Gate)
    (h₁ : PPMReflectsGateRel basisPPMSemanticsModel g₁
            (compileArithmeticGateToPPM g₁))
    (h₂ : PPMReflectsGateRel basisPPMSemanticsModel g₂
            (compileArithmeticGateToPPM g₂)) :
    PPMReflectsGateRel basisPPMSemanticsModel (Gate.seq g₁ g₂)
      (compileArithmeticGateToPPM (Gate.seq g₁ g₂)) := by
  intro s u h
  rw [compileArithmeticGateToPPM_seq] at h
  obtain ⟨mid, hp1, hp2⟩ := PPMProgramRel_append_inv _ _ _ _ _ h
  show basisPPMGateRel (Gate.seq g₁ g₂) s u
  exact ⟨mid, h₁ s mid hp1, h₂ mid u hp2⟩

theorem basisPPMReflects_ICX :
    ∀ g, isICXGate g = true →
      PPMReflectsGateRel basisPPMSemanticsModel g
        (compileArithmeticGateToPPM g) := by
  intro g
  induction g with
  | I => intro _; exact basisPPM_I_reflects
  | X q => intro _; exact basisPPM_X_reflects q
  | CX c tgt => intro _; exact basisPPM_CX_reflects c tgt
  | CCX _ _ _ => intro h; simp [isICXGate] at h
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hICX
      have h_and : (isICXGate g₁ && isICXGate g₂) = true := hICX
      rw [Bool.and_eq_true] at h_and
      obtain ⟨ha, hb⟩ := h_and
      exact basisPPM_seq_reflects g₁ g₂ (ih₁ ha) (ih₂ hb)

/-! ## §10. The ICX `Gate.applyNat` bridge with NO external
       arguments. -/

theorem compileICXGateToPPM_applyNat_bridge_basisPPM
    (g : Gate) (hICX : isICXGate g = true) :
    LogicalGateAsPPMApplyNat basisPPMSemanticsModel
      basisRefinesApplyNat g :=
  LogicalGateAsPPMApplyNat.from_refinement
    basisPPMSemanticsModel basisRefinesApplyNat g
    (basisPPMSound_ICX g hICX)
    (basisPPMReflects_ICX g hICX)

/-! ## §11. Shor-facing ICX decoder transfer with NO external
       arguments. -/

theorem shor_arithmetic_ICX_correctness_transfers_to_basisPPM
    (g : Gate) (hICX : isICXGate g = true)
    (decode : (Nat → Bool) → Nat)
    (input : Nat → Bool) (expected : Nat)
    (σ' : basisPPMSemanticsModel.State)
    (hrun :
      PPMProgramRel basisPPMSemanticsModel
        (compileArithmeticGateToPPM g)
        (basisRefinesApplyNat.encodeBits input)
        σ')
    (hGateCorrect :
      decode (Gate.applyNat g input) = expected) :
    ∃ output,
      basisRefinesApplyNat.observesBits σ' output
        ∧ decode output = expected :=
  shor_arithmetic_applyNat_correctness_transfers_to_PPM
    basisPPMSemanticsModel basisRefinesApplyNat g decode input expected
    (compileICXGateToPPM_applyNat_bridge_basisPPM g hICX)
    σ' hrun hGateCorrect

/-! ## §12. Honest non-connection to cxMacroPPMSemanticsModel.

    We deliberately do NOT provide any theorem of the shape:

      cxMacroPPMSemanticsModel n  ↔  basisPPMSemanticsModel
      cxMacroPPMSemanticsModel n  simulates basisPPMSemanticsModel

    Such a connection would require either:
      (i) reformulating `cxMacroGateRel` to encode the
          control-dependence of CX (currently it
          unconditionally toggles the X-frame on the
          target), or
      (ii) an outcome-tracking observation map that reads
           Boolean bits out of a `StabilizerState +
           LogicalPauliFrame` state given some encoding
           convention.

    Neither is closed here.  Future ticks may attempt one of
    these; the framework's only requirement is that any such
    bridge be honest, not faked.  In the meantime, the
    arithmetic Shor stack's `Gate.applyNat`-level correctness
    transfers to ideal Boolean-basis PPM execution via the
    §11 theorem; the corresponding transfer to
    cxMacroPPMSemanticsModel remains parametric on an
    honest bridge instance.

    ## Status summary

    Closed in this file:

    * `basisPPMSemanticsModel`, `BasisPPMState` — the
      reference Boolean-basis semantic substrate.
    * `basisRefinesApplyNat` — concrete
      `PPMRefinesApplyNat` instance with honest
      encode/observation/bridge fields.
    * `basisPPMSound_ICX` — full ICX forward soundness.
    * `basisPPMReflects_ICX` — full ICX reflection.
    * `compileICXGateToPPM_applyNat_bridge_basisPPM` — ICX
      `LogicalGateAsPPMApplyNat` instance with no
      external arguments.
    * `shor_arithmetic_ICX_correctness_transfers_to_basisPPM`
      — ICX Shor decoder transfer with no external
      arguments.

    Deferred (open obligations, not silent axioms):

    * Concrete `PPMRefinesApplyNat (cxMacroPPMSemanticsModel n)`
      instance — IMPOSSIBLE without either reformulating
      `cxMacroGateRel` (it loses control-dependence) or
      adding a Boolean readout / outcome track to
      `LogicalPPMState`.  Honestly noted; no fake bridge
      provided.
    * Simulation / observation connection between
      cxMacroPPMSemanticsModel and basisPPMSemanticsModel.
    * CCX/Toffoli (basis-model `useMagicT` is bit-identity +
      magic count; it does NOT realise Boolean Toffoli when
      composed with the §3 `measurePauliKind` /
      `applyFrameUpdate` interpretations).
    * QEC / surgery / backend lowering of ideal PPM.
    * QPE / non-Clifford rotations. -/

end FormalRV.Framework.CircuitToPPMObservationBridge
