/-
  FormalRV.Framework.CircuitToPPMToffoliMagic — PPM-level
  Toffoli teleportation primitive + extended command IR.

  ## E22 review and motivation

  E22 introduced `TFactoryToffoliObligationV2`, the
  non-vacuous Toffoli obligation, but did NOT instantiate
  it.  The reason: the existing `PPMCommand` IR exposes
  three commands —
    * `applyFrameUpdate qs` (deterministic bit flip),
    * `measurePauliKind pk qs` (in `basisPPMCommandRel`,
      identity except for the special `Z [c, t]` case
      which writes a CX-style XOR-with-NOT bit),
    * `useMagicT q` (resource counter; no nonlinear
      semantics in `magicBasisPPMCommandRel`).

  None of these can construct nonlinear Boolean Toffoli on
  the success branch without conditional / nonlinear
  control by the bit values — which the existing
  `magicBasisPPMCommandRel` does not provide.

  ## What this file adds

  This file introduces an EXTENDED command IR
  `MagicPPMCommand` with two cases:

    * `base : PPMCommand → MagicPPMCommand`
    * `teleportCCX : Nat → Nat → Nat → MagicPPMCommand`

  and the matching `MagicPPMProgram := List MagicPPMCommand`,
  `MagicPPMProgramRel F`, and a new compiler
  `compileArithmeticGateToMagicPPM`.

  The `teleportCCX a b c` primitive's relation
  `teleportCCXRel F a b c s t` says: there exists a
  certified-T token at the head of the magic pool that the
  primitive consumes, and `t.bits = Gate.applyNat
  (Gate.CCX a b c) s.bits`.  This is the SUCCESS-BRANCH
  semantics of an abstract gate-teleportation contract.

  Using this primitive, we instantiate a non-vacuous
  `TFactoryToffoliObligationV3` and prove a full-arithmetic
  Shor decoder transfer through the extended compiler
  WITHOUT requiring an external Toffoli obligation
  argument.

  ## Honesty boundary

  This file does NOT prove:
    * Physical factory / distillation correctness.
    * The internal Clifford+T circuit that realises
      gate-teleportation Toffoli; `teleportCCXRel` is the
      success-branch CONTRACT, not its low-level proof.
    * QEC / backend implementation of the factory or of
      teleportation.
    * Full Shor success-probability correctness.
    * QPE / non-Clifford rotations.
    * Any equivalence between `MagicPPMProgram` and a
      backend SysCall schedule.

  The PPM-level teleportation primitive is honest at THIS
  layer: it abstracts the internal teleportation circuit
  into one named relation whose obligations (certified
  token consumption + Boolean Toffoli output) are
  explicit.  A future tick can refine `teleportCCXRel`
  into a Clifford+T circuit proof.
-/
import FormalRV.PPM.CircuitToPPMMagicFactory

namespace FormalRV.Framework.CircuitToPPMToffoliMagic

open FormalRV.Framework
open FormalRV.Framework.Architecture
open FormalRV.Framework.Factory
open FormalRV.Framework.CircuitToPPMInterface
open FormalRV.Framework.CircuitToPPMSemanticBridge
open FormalRV.Framework.CircuitToPPMObservationBridge
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.BQAlgo

/-! ## §1. Extended command IR. -/

inductive MagicPPMCommand : Type
  | base        : PPMCommand → MagicPPMCommand
  | teleportCCX : Nat → Nat → Nat → MagicPPMCommand
  deriving Inhabited

abbrev MagicPPMProgram := List MagicPPMCommand

/-! ## §2. Magic-T request count for the extended program. -/

def magicPPMCommandMagicTCount : MagicPPMCommand → Nat
  | .base cmd          => ppmCommandMagicTCount cmd
  | .teleportCCX _ _ _ => 1

def magicPPMRequestCount (p : MagicPPMProgram) : Nat :=
  listSumOver magicPPMCommandMagicTCount p

theorem magicPPMRequestCount_nil :
    magicPPMRequestCount [] = 0 := rfl

theorem magicPPMRequestCount_append (p q : MagicPPMProgram) :
    magicPPMRequestCount (p ++ q)
      = magicPPMRequestCount p + magicPPMRequestCount q := by
  unfold magicPPMRequestCount
  exact listSumOver_append _ _ _

theorem magicPPMRequestCount_teleportCCX (a b c : Nat) :
    magicPPMRequestCount [MagicPPMCommand.teleportCCX a b c] = 1 := rfl

/-! ## §3. Per-command semantic relation. -/

/-- The success-branch relation for the abstract Toffoli
    teleportation primitive.  Consumes one certified-T
    token from the head of the pool and writes the Boolean
    Toffoli output on `bits`. -/
def teleportCCXRel
    (F : TFactoryContract) (a b c : Nat)
    (s t : MagicBasisPPMState) : Prop :=
  ∃ tok rest,
    s.magicPool = tok :: rest
    ∧ MagicToken.IsCertifiedTFrom F tok
    ∧ t.bits      = Gate.applyNat (Gate.CCX a b c) s.bits
    ∧ t.magicUsed = s.magicUsed + 1
    ∧ t.magicPool = rest
    ∧ t.failed    = s.failed

/-- The extended command relation.  `.base cmd` dispatches
    to `magicBasisPPMCommandRel F`.  `.teleportCCX a b c`
    invokes `teleportCCXRel`. -/
def magicPPMCommandRel
    (F : TFactoryContract) :
    MagicPPMCommand → MagicBasisPPMState → MagicBasisPPMState → Prop
  | .base cmd,          s, t => magicBasisPPMCommandRel F cmd s t
  | .teleportCCX a b c, s, t => teleportCCXRel F a b c s t

/-! ## §4. Extended program relation. -/

inductive MagicPPMProgramRel (F : TFactoryContract) :
    MagicPPMProgram → MagicBasisPPMState → MagicBasisPPMState → Prop
  | nil  (s : MagicBasisPPMState) : MagicPPMProgramRel F [] s s
  | cons {cmd : MagicPPMCommand} {rest : MagicPPMProgram}
         {s t u : MagicBasisPPMState}
         (h1 : magicPPMCommandRel F cmd s t)
         (h2 : MagicPPMProgramRel F rest t u) :
         MagicPPMProgramRel F (cmd :: rest) s u

theorem MagicPPMProgramRel_nil_iff
    (F : TFactoryContract) (s t : MagicBasisPPMState) :
    MagicPPMProgramRel F [] s t ↔ s = t := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h; rfl
  · cases h; exact MagicPPMProgramRel.nil _

theorem MagicPPMProgramRel_cons_inv
    (F : TFactoryContract)
    (cmd : MagicPPMCommand) (rest : MagicPPMProgram)
    (s u : MagicBasisPPMState)
    (h : MagicPPMProgramRel F (cmd :: rest) s u) :
    ∃ mid, magicPPMCommandRel F cmd s mid
        ∧ MagicPPMProgramRel F rest mid u := by
  cases h with
  | cons h1 h2 => exact ⟨_, h1, h2⟩

theorem MagicPPMProgramRel_append
    (F : TFactoryContract) (p q : MagicPPMProgram)
    (s u : MagicBasisPPMState) :
    MagicPPMProgramRel F (p ++ q) s u ↔
      ∃ t, MagicPPMProgramRel F p s t ∧ MagicPPMProgramRel F q t u := by
  induction p generalizing s with
  | nil =>
      refine ⟨fun h => ⟨s, MagicPPMProgramRel.nil s, h⟩, ?_⟩
      rintro ⟨t, h1, h2⟩
      cases h1
      exact h2
  | cons cmd rest ih =>
      refine ⟨fun h => ?_, ?_⟩
      · cases h with
        | cons h1 hrest =>
            obtain ⟨t', hp1, hp2⟩ := (ih _).mp hrest
            exact ⟨t', MagicPPMProgramRel.cons h1 hp1, hp2⟩
      · rintro ⟨t, hp1, hp2⟩
        cases hp1 with
        | cons h1 hrest =>
            exact MagicPPMProgramRel.cons h1 ((ih _).mpr ⟨t, hrest, hp2⟩)

theorem MagicPPMProgramRel_append_inv
    (F : TFactoryContract) (p q : MagicPPMProgram)
    (s u : MagicBasisPPMState)
    (h : MagicPPMProgramRel F (p ++ q) s u) :
    ∃ mid, MagicPPMProgramRel F p s mid
        ∧ MagicPPMProgramRel F q mid u :=
  (MagicPPMProgramRel_append F p q s u).mp h

/-! ## §5. Lift between `MagicPPMProgramRel F (l.map .base)`
       and the base-level `PPMProgramRel`. -/

theorem MagicPPMProgramRel_base_map_iff
    (F : TFactoryContract) (l : PPMProgram) :
    ∀ (s σ' : MagicBasisPPMState),
      MagicPPMProgramRel F (l.map MagicPPMCommand.base) s σ' ↔
        PPMProgramRel (magicBasisPPMSemanticsModel F) l s σ' := by
  induction l with
  | nil =>
      intro s σ'
      simp only [List.map_nil]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hst : s = σ' := (MagicPPMProgramRel_nil_iff F _ _).mp h
        rw [hst]; exact PPMProgramRel.nil _
      · have hst : s = σ' := (PPMProgramRel_nil_iff _ _ _).mp h
        rw [hst]; exact MagicPPMProgramRel.nil _
  | cons cmd rest ih =>
      intro s σ'
      simp only [List.map_cons]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨mid, h1, h2⟩ :=
          MagicPPMProgramRel_cons_inv F _ _ _ _ h
        -- h1 : magicPPMCommandRel F (.base cmd) s mid
        --    = magicBasisPPMCommandRel F cmd s mid
        exact PPMProgramRel.cons h1 ((ih _ _).mp h2)
      · obtain ⟨mid, h1, h2⟩ :=
          PPMProgramRel_cons_inv _ _ _ _ _ h
        exact MagicPPMProgramRel.cons h1 ((ih _ _).mpr h2)

/-! ## §6. The Toffoli macro program. -/

def teleportCCXProgram (a b c : Nat) : MagicPPMProgram :=
  [MagicPPMCommand.teleportCCX a b c]

theorem teleportCCXProgram_uses_magic
    (F : TFactoryContract) (a b c : Nat) :
    magicPPMRequestCount (teleportCCXProgram a b c) > 0 := by
  show magicPPMRequestCount [MagicPPMCommand.teleportCCX a b c] > 0
  rw [magicPPMRequestCount_teleportCCX]
  decide

theorem teleportCCXProgram_correct_on_success
    (F : TFactoryContract) (a b c : Nat)
    (input : Nat → Bool)
    (s σ' : MagicBasisPPMState)
    (hobs : (magicBasisRefinesApplyNat F).observesBits s input)
    (hrun : MagicPPMProgramRel F (teleportCCXProgram a b c) s σ') :
    (magicBasisRefinesApplyNat F).observesBits σ'
      (Gate.applyNat (Gate.CCX a b c) input) := by
  -- teleportCCXProgram = [.teleportCCX a b c]
  obtain ⟨mid, hcmd, hrest⟩ :=
    MagicPPMProgramRel_cons_inv F _ _ _ _ hrun
  have hmid : mid = σ' := (MagicPPMProgramRel_nil_iff F _ _).mp hrest
  -- hcmd : magicPPMCommandRel F (.teleportCCX a b c) s mid = teleportCCXRel F a b c s mid
  obtain ⟨tok, rest, hpool_s, htokCert, h_bits, h_mag, h_pool_t, h_fail⟩ := hcmd
  obtain ⟨hs_bits, hs_fail⟩ := hobs
  refine ⟨?_, ?_⟩
  · -- σ'.bits = Gate.applyNat (Gate.CCX a b c) input
    rw [← hmid, h_bits, hs_bits]
  · -- σ'.failed = false
    rw [← hmid, h_fail]; exact hs_fail

/-! ## §7. Extended full-arithmetic compiler. -/

def compileArithmeticGateToMagicPPM : Gate → MagicPPMProgram
  | Gate.I         =>
      (compileArithmeticGateToPPM Gate.I).map MagicPPMCommand.base
  | Gate.X q       =>
      (compileArithmeticGateToPPM (Gate.X q)).map MagicPPMCommand.base
  | Gate.CX c t    =>
      (compileArithmeticGateToPPM (Gate.CX c t)).map MagicPPMCommand.base
  | Gate.CCX a b c => teleportCCXProgram a b c
  | Gate.seq g₁ g₂ =>
      compileArithmeticGateToMagicPPM g₁
        ++ compileArithmeticGateToMagicPPM g₂

/-! ## §8. Helper: ICX observation transfer through old `PPMProgramRel`.

    Reuses the E21 reflection theorem and the two preservation
    helpers to lift any ICX-fragment `PPMProgramRel` execution
    to an observation of `Gate.applyNat g`. -/

theorem magicBasisPPM_applyNat_sound_ICX_from_observed
    (F : TFactoryContract)
    (g : Gate) (hICX : isICXGate g = true)
    (input : Nat → Bool)
    (s σ' : MagicBasisPPMState)
    (hobs : (magicBasisRefinesApplyNat F).observesBits s input)
    (hrun : PPMProgramRel (magicBasisPPMSemanticsModel F)
              (compileArithmeticGateToPPM g) s σ') :
    (magicBasisRefinesApplyNat F).observesBits σ'
      (Gate.applyNat g input) := by
  obtain ⟨hs_bits, hs_fail⟩ := hobs
  have hgate := magicBasisPPMReflects_ICX F g hICX s σ' hrun
  have h_app := magicBasisPPMGateRel_imp_applyNat g s σ' hgate
  have h_fail := magicBasisPPMGateRel_preserves_failed g s σ' hgate
  refine ⟨?_, ?_⟩
  · rw [h_app, hs_bits]
  · rw [h_fail]; exact hs_fail

/-! ## §9. Strong full-arithmetic soundness for the extended
       compiler. -/

theorem compileArithmeticGateToMagicPPM_applyNat_sound_from_observed
    (F : TFactoryContract) :
    ∀ (g : Gate) (input : Nat → Bool)
      (s σ' : MagicBasisPPMState),
      (magicBasisRefinesApplyNat F).observesBits s input →
      MagicPPMProgramRel F (compileArithmeticGateToMagicPPM g) s σ' →
      (magicBasisRefinesApplyNat F).observesBits σ'
        (Gate.applyNat g input) := by
  intro g
  induction g with
  | I =>
      intro input s σ' hobs hrun
      -- compile = ([] : PPMProgram).map .base = [] (MagicPPMProgram)
      -- Lift to base and use ICX helper at g = Gate.I
      have hbase :
          PPMProgramRel (magicBasisPPMSemanticsModel F)
            (compileArithmeticGateToPPM Gate.I) s σ' := by
        exact (MagicPPMProgramRel_base_map_iff F _ s σ').mp hrun
      exact magicBasisPPM_applyNat_sound_ICX_from_observed F
        Gate.I rfl input s σ' hobs hbase
  | X q =>
      intro input s σ' hobs hrun
      have hbase :
          PPMProgramRel (magicBasisPPMSemanticsModel F)
            (compileArithmeticGateToPPM (Gate.X q)) s σ' := by
        exact (MagicPPMProgramRel_base_map_iff F _ s σ').mp hrun
      exact magicBasisPPM_applyNat_sound_ICX_from_observed F
        (Gate.X q) rfl input s σ' hobs hbase
  | CX c t =>
      intro input s σ' hobs hrun
      have hbase :
          PPMProgramRel (magicBasisPPMSemanticsModel F)
            (compileArithmeticGateToPPM (Gate.CX c t)) s σ' := by
        exact (MagicPPMProgramRel_base_map_iff F _ s σ').mp hrun
      exact magicBasisPPM_applyNat_sound_ICX_from_observed F
        (Gate.CX c t) rfl input s σ' hobs hbase
  | CCX a b c =>
      intro input s σ' hobs hrun
      -- compile = teleportCCXProgram a b c
      exact teleportCCXProgram_correct_on_success F a b c input s σ' hobs hrun
  | seq g₁ g₂ ih₁ ih₂ =>
      intro input s σ' hobs hrun
      -- compile = compileArithmeticGateToMagicPPM g₁ ++ ... g₂
      obtain ⟨mid, hp1, hp2⟩ := MagicPPMProgramRel_append_inv F _ _ _ _ hrun
      have hmid := ih₁ input s mid hobs hp1
      have hσ := ih₂ (Gate.applyNat g₁ input) mid σ' hmid hp2
      exact hσ

theorem compileArithmeticGateToMagicPPM_applyNat_sound
    (F : TFactoryContract)
    (g : Gate) (input : Nat → Bool)
    (σ' : MagicBasisPPMState)
    (hrun : MagicPPMProgramRel F
              (compileArithmeticGateToMagicPPM g)
              ((magicBasisRefinesApplyNat F).encodeBits input) σ') :
    (magicBasisRefinesApplyNat F).observesBits σ'
      (Gate.applyNat g input) :=
  compileArithmeticGateToMagicPPM_applyNat_sound_from_observed F
    g input _ σ'
    ((magicBasisRefinesApplyNat F).encode_observes input) hrun

/-! ## §10. Shor-facing full-arithmetic decoder transfer
       through the extended magic-teleport PPM compiler. -/

theorem shor_arithmetic_full_correctness_transfers_to_magicTeleportPPM
    (F : TFactoryContract)
    (g : Gate)
    (decode : (Nat → Bool) → Nat)
    (input : Nat → Bool) (expected : Nat)
    (σ' : MagicBasisPPMState)
    (hrun : MagicPPMProgramRel F
              (compileArithmeticGateToMagicPPM g)
              ((magicBasisRefinesApplyNat F).encodeBits input) σ')
    (hGateCorrect : decode (Gate.applyNat g input) = expected) :
    ∃ output,
      (magicBasisRefinesApplyNat F).observesBits σ' output
        ∧ decode output = expected :=
  ⟨Gate.applyNat g input,
    compileArithmeticGateToMagicPPM_applyNat_sound F g input σ' hrun,
    hGateCorrect⟩

/-! ## §11. V3 Toffoli obligation + instantiation.

    `TFactoryToffoliObligationV2` (E22) was over old
    `PPMProgram`.  The new compiler uses the extended
    `MagicPPMProgram`, so we define V3 over the extended
    IR.  Crucially, V3 has an honest concrete instantiation
    (`teleportCCX_ToffoliObligationV3`) below — this is the
    first non-vacuous, non-trivial Toffoli obligation
    instance in the project. -/

structure TFactoryToffoliObligationV3 (F : TFactoryContract) where
  ccx_program : Nat → Nat → Nat → MagicPPMProgram
  ccx_uses_magic :
    ∀ a b c, magicPPMRequestCount (ccx_program a b c) > 0
  ccx_correct_on_success :
    ∀ a b c (input : Nat → Bool)
      (s σ' : MagicBasisPPMState),
      (magicBasisRefinesApplyNat F).observesBits s input →
      MagicPPMProgramRel F (ccx_program a b c) s σ' →
      (magicBasisRefinesApplyNat F).observesBits σ'
        (Gate.applyNat (Gate.CCX a b c) input)

/-- Concrete instantiation of V3 using the explicit
    `teleportCCXProgram` primitive. -/
def teleportCCX_ToffoliObligationV3 (F : TFactoryContract) :
    TFactoryToffoliObligationV3 F :=
  { ccx_program            := teleportCCXProgram
    ccx_uses_magic         := teleportCCXProgram_uses_magic F
    ccx_correct_on_success := teleportCCXProgram_correct_on_success F }

/-! ## §12. Resource-count lemmas for the extended compiler. -/

theorem magicPPMRequestCount_base_map (l : PPMProgram) :
    magicPPMRequestCount (l.map MagicPPMCommand.base)
      = magicRequestCount l := by
  induction l with
  | nil => rfl
  | cons cmd rest ih =>
      show magicPPMCommandMagicTCount (MagicPPMCommand.base cmd)
            + magicPPMRequestCount (rest.map MagicPPMCommand.base)
          = ppmCommandMagicTCount cmd
            + magicRequestCount rest
      show ppmCommandMagicTCount cmd
            + magicPPMRequestCount (rest.map MagicPPMCommand.base)
          = ppmCommandMagicTCount cmd
            + magicRequestCount rest
      rw [ih]

theorem magicPPMRequestCount_compileArithmeticGateToMagicPPM_I :
    magicPPMRequestCount (compileArithmeticGateToMagicPPM Gate.I) = 0 := by
  show magicPPMRequestCount
        ((compileArithmeticGateToPPM Gate.I).map MagicPPMCommand.base) = 0
  rw [magicPPMRequestCount_base_map, magicRequestCount_compile_I]

theorem magicPPMRequestCount_compileArithmeticGateToMagicPPM_X (q : Nat) :
    magicPPMRequestCount (compileArithmeticGateToMagicPPM (Gate.X q)) = 0 := by
  show magicPPMRequestCount
        ((compileArithmeticGateToPPM (Gate.X q)).map MagicPPMCommand.base) = 0
  rw [magicPPMRequestCount_base_map, magicRequestCount_compile_X]

theorem magicPPMRequestCount_compileArithmeticGateToMagicPPM_CX (c t : Nat) :
    magicPPMRequestCount (compileArithmeticGateToMagicPPM (Gate.CX c t)) = 0 := by
  show magicPPMRequestCount
        ((compileArithmeticGateToPPM (Gate.CX c t)).map MagicPPMCommand.base) = 0
  rw [magicPPMRequestCount_base_map, magicRequestCount_compile_CX]

theorem magicPPMRequestCount_compileArithmeticGateToMagicPPM_CCX (a b c : Nat) :
    magicPPMRequestCount (compileArithmeticGateToMagicPPM (Gate.CCX a b c)) = 1 := by
  show magicPPMRequestCount (teleportCCXProgram a b c) = 1
  rfl

theorem magicPPMRequestCount_compileArithmeticGateToMagicPPM_CCX_pos
    (a b c : Nat) :
    magicPPMRequestCount (compileArithmeticGateToMagicPPM (Gate.CCX a b c)) > 0 := by
  rw [magicPPMRequestCount_compileArithmeticGateToMagicPPM_CCX]
  decide

theorem magicPPMRequestCount_compileArithmeticGateToMagicPPM_seq (g₁ g₂ : Gate) :
    magicPPMRequestCount (compileArithmeticGateToMagicPPM (Gate.seq g₁ g₂))
      = magicPPMRequestCount (compileArithmeticGateToMagicPPM g₁)
        + magicPPMRequestCount (compileArithmeticGateToMagicPPM g₂) := by
  show magicPPMRequestCount
        (compileArithmeticGateToMagicPPM g₁
          ++ compileArithmeticGateToMagicPPM g₂)
      = _
  exact magicPPMRequestCount_append _ _

theorem magicPPMRequestCount_compileArithmeticGateToMagicPPM_ICX :
    ∀ g, isICXGate g = true →
      magicPPMRequestCount (compileArithmeticGateToMagicPPM g) = 0 := by
  intro g
  induction g with
  | I => intro _; exact magicPPMRequestCount_compileArithmeticGateToMagicPPM_I
  | X q => intro _; exact magicPPMRequestCount_compileArithmeticGateToMagicPPM_X q
  | CX c t => intro _; exact magicPPMRequestCount_compileArithmeticGateToMagicPPM_CX c t
  | CCX _ _ _ => intro h; simp [isICXGate] at h
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hICX
      have h_and : (isICXGate g₁ && isICXGate g₂) = true := hICX
      rw [Bool.and_eq_true] at h_and
      obtain ⟨ha, hb⟩ := h_and
      rw [magicPPMRequestCount_compileArithmeticGateToMagicPPM_seq,
          ih₁ ha, ih₂ hb]

/-! ## §13. Status summary.

    Closed in this file:

    * `MagicPPMCommand`, `MagicPPMProgram` — extended IR
      with explicit `teleportCCX` primitive.
    * `magicPPMRequestCount` + per-command lemmas.
    * `teleportCCXRel F a b c` — abstract success-branch
      teleportation relation.
    * `magicPPMCommandRel F`, `MagicPPMProgramRel F` —
      extended command + program semantics.
    * Inversion lemmas: `_nil_iff`, `_cons_inv`,
      `_append`, `_append_inv`.
    * `MagicPPMProgramRel_base_map_iff` — lift between
      base-only programs and the underlying `PPMProgramRel`.
    * `teleportCCXProgram` + `_uses_magic` +
      `_correct_on_success` — the Toffoli macro and its
      Boolean-Toffoli correctness on the success branch.
    * `compileArithmeticGateToMagicPPM` — extended
      full-arithmetic compiler.
    * `compileArithmeticGateToMagicPPM_applyNat_sound_from_observed`
      and `_sound` — full-Gate-IR observation soundness,
      including CCX.
    * `shor_arithmetic_full_correctness_transfers_to_magicTeleportPPM`
      — Shor decoder transfer with NO external Toffoli
      obligation argument.
    * `TFactoryToffoliObligationV3` — Toffoli obligation
      over the extended IR.
    * `teleportCCX_ToffoliObligationV3` — CONCRETE
      instantiation of V3.  First non-vacuous Toffoli
      obligation instance in the project.
    * Per-Gate magic-request-count lemmas (I/X/CX/CCX/seq/ICX).

    Deferred (explicit obligations, not silent axioms):

    * Internal Clifford+T circuit realising
      `teleportCCXRel` — refinement target for a future
      tick.
    * Physical T-state distillation correctness.
    * QEC / surgery / backend implementation of the
      factory and of `teleportCCX`.
    * Full Shor success-probability theorem (counting is
      closed; probabilistic semantics open).
    * QPE / non-Clifford rotations.
    * Bridge between `MagicPPMProgram` and the backend
      SysCall schedule layer. -/

end FormalRV.Framework.CircuitToPPMToffoliMagic
