/-
  FormalRV.Framework.CircuitToPPMMagicFactory — abstract
  PPM-level T-factory + magic-token interface.

  ## Scope (E21)

  This file introduces an HONEST abstraction layer for a
  T-factory operating at the PPM/logical level:

    * `TFactoryContract` — a parametric factory contract
      (output kind, latency, footprint, success-probability
      lower bound, output-error upper bound, herald flag),
      with a `WellFormed` predicate.
    * `MagicToken` and `FactoryOutcome` — typed magic tokens
      and the success / herald-fail / unherald-fail outcome
      sum.
    * `MagicBasisPPMState` — the basisPPM state of E20
      extended with a pool of certified tokens and a
      `failed` flag, plus projection back to `BasisPPMState`.
    * `magicBasisPPMSemanticsModel F` — a magic-aware
      semantic model that lifts the E20 ICX soundness /
      reflection to the magic state space; `useMagicT`
      consumes one certified T token; `CCX` remains
      structurally `False` (not realised here).
    * `magicBasisRefinesApplyNat F` — the concrete
      `PPMRefinesApplyNat` bridge.
    * `magicRequestCount` — the magic-T-request count of a
      `PPMProgram` and its lemmas (using the existing
      `ppmCommandMagicTCount` from
      `CircuitToPPMInterface.lean §21`).
    * `allMagicRequestsSuccessProbLB` — Nat-scaled
      success-probability lower-bound accounting.
    * `TFactoryToffoliObligation F` — the named future
      obligation: a magic-using PPM program for `Gate.CCX`
      that is sound under `magicBasisPPMSemanticsModel F`.
      NOT instantiated here.

  ## Honesty boundary

  This file does NOT prove:
    * Physical T-state distillation correctness.
    * Gate teleportation correctness.
    * CCX / Toffoli correctness (the current compiler emits
      one `useMagicT` for `Gate.CCX` which is a placeholder
      resource count, not a Toffoli decomposition; we
      explicitly note this).
    * Full Shor success-probability correctness.
    * QEC / surgery / backend implementation of magic
      factories.

  The success-probability accounting uses Nat-scaled
  parts-per-million / per-Q-fold representations, NOT real
  numbers; this matches the existing `AtomicFactorySpec`'s
  `success_probability_ppm` convention in
  `FactoryHierarchy.lean`.
-/
import FormalRV.PPM.CircuitToPPMInterface
import FormalRV.PPM.CircuitToPPMSemanticBridge
import FormalRV.PPM.CircuitToPPMObservationBridge

namespace FormalRV.Framework.CircuitToPPMMagicFactory

open FormalRV.Framework
open FormalRV.Framework.Architecture
open FormalRV.Framework.Factory
open FormalRV.Framework.CircuitToPPMInterface
open FormalRV.Framework.CircuitToPPMSemanticBridge
open FormalRV.Framework.CircuitToPPMObservationBridge
open FormalRV.BQAlgo

/-! ## §1. T-factory contract.

    Mirrors the existing `AtomicFactorySpec`'s use of
    Nat-scaled probabilities (parts per million).  Distinct
    from `AtomicFactorySpec` because we want a clean
    PPM-layer view (no atom budget, latency in cycles not
    microseconds) parameterised differently from the backend
    schedule layer.

    The two layers are intentionally separate:
    `AtomicFactorySpec` lives at the backend SysCall layer;
    `TFactoryContract` lives at the PPM/logical layer.  A
    future tick can connect them. -/

/-- Abstract T-factory contract at the PPM layer.  Nat-scaled
    probabilities (ppm = parts per million; 1_000_000 = 100%). -/
structure TFactoryContract where
  factoryId               : Nat
  outputKind              : MagicStateKind
  latencyCycles           : Nat
  footprintSites          : Nat
  successProbLB_ppm       : Nat
  outputErrorUB_ppm       : Nat
  heraldedFailure         : Bool
  deriving Repr, Inhabited, DecidableEq

/-- Well-formedness for a `TFactoryContract`: it must produce
    `T` states, and the ppm fields must lie in `[0, 10^6]`. -/
def TFactoryContract.WellFormed (F : TFactoryContract) : Prop :=
  F.outputKind = MagicStateKind.T
  ∧ F.successProbLB_ppm ≤ 1_000_000
  ∧ F.outputErrorUB_ppm ≤ 1_000_000

/-! ## §2. Magic tokens and factory outcomes. -/

/-- A typed magic token issued by a specific factory.  The
    `certified` flag records whether post-distillation
    acceptance/verification passed. -/
structure MagicToken where
  tokenId   : Nat
  factoryId : Nat
  kind      : MagicStateKind
  certified : Bool
  deriving Repr, Inhabited, DecidableEq

/-- A factory's nondeterministic outcome.  We expose three
    branches: success (with a token), heralded failure
    (factory signals failure), and unheralded failure
    (silent error — accepted under false certification). -/
inductive FactoryOutcome where
  | success         (tok : MagicToken)
  | heraldedFailure
  | unheraldedFailure
  deriving Repr, Inhabited

/-- A token is a certified-T from `F` iff its factory id and
    kind match `F`'s and `certified = true`. -/
def MagicToken.IsCertifiedTFrom
    (F : TFactoryContract) (tok : MagicToken) : Prop :=
  tok.factoryId = F.factoryId
  ∧ tok.kind = MagicStateKind.T
  ∧ tok.certified = true

/-! ## §3. Magic-aware PPM state.

    Extends `BasisPPMState` (E20) with a pool of certified
    tokens and a `failed` flag.  We deliberately do NOT
    overload `BasisPPMState`; the magic-aware state is a
    distinct type so the bridge composition stays explicit. -/

structure MagicBasisPPMState : Type where
  bits      : Nat → Bool
  magicUsed : Nat
  magicPool : List MagicToken
  failed    : Bool

instance : Inhabited MagicBasisPPMState :=
  ⟨{ bits := fun _ => false
     magicUsed := 0
     magicPool := []
     failed := false }⟩

/-- Forget the magic pool and failure flag, returning the
    underlying basis state. -/
def MagicBasisPPMState.toBasis (s : MagicBasisPPMState) : BasisPPMState :=
  { bits := s.bits, magicUsed := s.magicUsed }

/-- Lift a `BasisPPMState` to a `MagicBasisPPMState` with no
    tokens and no failure. -/
def BasisPPMState.withEmptyMagic (s : BasisPPMState) : MagicBasisPPMState :=
  { bits := s.bits, magicUsed := s.magicUsed
    magicPool := [], failed := false }

/-! ## §4. Magic-supply operations. -/

/-- The state holds at least one certified-T token from `F`. -/
def hasCertifiedT (F : TFactoryContract) (s : MagicBasisPPMState) : Prop :=
  ∃ tok ∈ s.magicPool, MagicToken.IsCertifiedTFrom F tok

/-- Consume one certified-T token from `s.magicPool`,
    incrementing `magicUsed` and preserving bits.  No
    failure: `failed` flag remains `false`.  This is the
    success branch of a T-supply call. -/
def consumeCertifiedT
    (F : TFactoryContract) (s t : MagicBasisPPMState) : Prop :=
  ∃ tok rest,
    s.magicPool = tok :: rest
    ∧ MagicToken.IsCertifiedTFrom F tok
    ∧ t.bits      = s.bits
    ∧ t.magicUsed = s.magicUsed + 1
    ∧ t.magicPool = rest
    ∧ t.failed    = s.failed

/-- Request the factory to supply a new certified-T token on
    the success branch: prepends `tok` to the pool, leaves
    everything else unchanged. -/
def requestTSuccess
    (F : TFactoryContract)
    (s t : MagicBasisPPMState) (tok : MagicToken) : Prop :=
  MagicToken.IsCertifiedTFrom F tok
  ∧ t.bits      = s.bits
  ∧ t.magicUsed = s.magicUsed
  ∧ t.magicPool = tok :: s.magicPool
  ∧ t.failed    = s.failed

/-! ## §5. Magic-request count + success-probability
       accounting. -/

/-- Number of `useMagicT` requests in a `PPMProgram`.  Reuses
    the existing per-command counter from §21.b of
    `CircuitToPPMInterface.lean`. -/
def magicRequestCount (p : PPMProgram) : Nat :=
  listSumOver ppmCommandMagicTCount p

theorem magicRequestCount_nil : magicRequestCount [] = 0 := by
  rfl

theorem magicRequestCount_append (p q : PPMProgram) :
    magicRequestCount (p ++ q)
      = magicRequestCount p + magicRequestCount q := by
  unfold magicRequestCount
  exact listSumOver_append _ _ _

theorem magicRequestCount_compile_I :
    magicRequestCount (compileArithmeticGateToPPM Gate.I) = 0 := rfl

theorem magicRequestCount_compile_X (q : Nat) :
    magicRequestCount (compileArithmeticGateToPPM (Gate.X q)) = 0 := rfl

theorem magicRequestCount_compile_CX (c t : Nat) :
    magicRequestCount (compileArithmeticGateToPPM (Gate.CX c t)) = 0 := rfl

theorem magicRequestCount_compile_CCX (a b c : Nat) :
    magicRequestCount (compileArithmeticGateToPPM (Gate.CCX a b c)) = 1 := rfl

/-- ICX gates have zero magic-T requests in their compiled
    PPM program. -/
theorem magicRequestCount_compile_ICX :
    ∀ g, isICXGate g = true →
      magicRequestCount (compileArithmeticGateToPPM g) = 0 := by
  intro g
  induction g with
  | I => intro _; rfl
  | X q => intro _; rfl
  | CX c t => intro _; rfl
  | CCX _ _ _ => intro h; simp [isICXGate] at h
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hICX
      have h_and : (isICXGate g₁ && isICXGate g₂) = true := hICX
      rw [Bool.and_eq_true] at h_and
      obtain ⟨ha, hb⟩ := h_and
      have e₁ := ih₁ ha
      have e₂ := ih₂ hb
      show magicRequestCount
            (compileArithmeticGateToPPM g₁ ++ compileArithmeticGateToPPM g₂) = 0
      rw [magicRequestCount_append, e₁, e₂]

/-- Nat-scaled success-probability lower bound for `k` independent
    factory invocations: `(p_LB)^k` in ppm-units.  Closed-form
    placeholder; not used as a real bound (which would need a
    `Rat`/`Real` story). -/
def allMagicRequestsSuccessProbLB
    (F : TFactoryContract) (k : Nat) : Nat :=
  F.successProbLB_ppm ^ k

theorem allMagicRequestsSuccessProbLB_zero (F : TFactoryContract) :
    allMagicRequestsSuccessProbLB F 0 = 1 := by
  rfl

theorem allMagicRequestsSuccessProbLB_succ (F : TFactoryContract) (k : Nat) :
    allMagicRequestsSuccessProbLB F (k + 1)
      = allMagicRequestsSuccessProbLB F k * F.successProbLB_ppm := by
  rfl

/-! ## §6. Magic-aware PPM command relation. -/

/-- The magic-aware command relation.  For ICX commands
    (`applyFrameUpdate`, `measurePauliKind`) it lifts the
    E20 `basisPPMCommandRel` action on `bits`, preserving
    `magicPool` and `failed`.  `useMagicT q` consumes one
    certified-T token from the pool. -/
def magicBasisPPMCommandRel
    (F : TFactoryContract) :
    PPMCommand → MagicBasisPPMState → MagicBasisPPMState → Prop
  | .applyFrameUpdate qs, s, t =>
      t.bits = qs.foldl (fun bs q => update bs q (!bs q)) s.bits
      ∧ t.magicUsed = s.magicUsed
      ∧ t.magicPool = s.magicPool
      ∧ t.failed    = s.failed
  | .measurePauliKind PauliKind.Z [c, tgt], s, t =>
      t.bits = update s.bits tgt (xor (s.bits tgt) (!s.bits c))
      ∧ t.magicUsed = s.magicUsed
      ∧ t.magicPool = s.magicPool
      ∧ t.failed    = s.failed
  | .measurePauliKind _ _, s, t =>
      t = s
  | .useMagicT _, s, t =>
      consumeCertifiedT F s t

/-! ## §7. Magic-aware gate relation.

    Matches `Gate.applyNat` on the `bits` field for the ICX
    fragment, preserves `magicPool` and `failed`.  `CCX`
    remains structurally `False` (the existing compiler's
    one-`useMagicT` placeholder is NOT a real Toffoli;
    §10 records the future obligation that closes this gap). -/

def magicBasisPPMGateRel : Gate → MagicBasisPPMState → MagicBasisPPMState → Prop
  | .I,         s, t => t = s
  | .X q,       s, t =>
      t.bits = update s.bits q (!s.bits q)
      ∧ t.magicUsed = s.magicUsed
      ∧ t.magicPool = s.magicPool
      ∧ t.failed    = s.failed
  | .CX c tgt,  s, t =>
      t.bits = update s.bits tgt (xor (s.bits tgt) (s.bits c))
      ∧ t.magicUsed = s.magicUsed
      ∧ t.magicPool = s.magicPool
      ∧ t.failed    = s.failed
  | .CCX _ _ _, _, _ => False
  | .seq g₁ g₂, s, u =>
      ∃ mid, magicBasisPPMGateRel g₁ s mid
          ∧ magicBasisPPMGateRel g₂ mid u

/-! ## §8. Magic-aware semantic model. -/

def magicBasisPPMSemanticsModel (F : TFactoryContract) : GateToPPMSemanticsModel :=
  { State         := MagicBasisPPMState
    gateRel       := magicBasisPPMGateRel
    ppmCommandRel := magicBasisPPMCommandRel F }

/-! ## §9. ICX soundness and reflection for the magic-aware
       model. -/

theorem magicBasisPPM_I_sound (F : TFactoryContract) :
    ImplementsGateAsPPM (magicBasisPPMSemanticsModel F) Gate.I
      (compileArithmeticGateToPPM Gate.I) := by
  intro s t hGate
  have hst : t = s := hGate
  rw [hst]
  exact PPMProgramRel.nil s

theorem magicBasisPPM_X_sound (F : TFactoryContract) (q : Nat) :
    ImplementsGateAsPPM (magicBasisPPMSemanticsModel F) (Gate.X q)
      (compileArithmeticGateToPPM (Gate.X q)) := by
  intro s t hGate
  obtain ⟨hbits, hmag, hpool, hfail⟩ := hGate
  refine PPMProgramRel.cons (cmd := PPMCommand.applyFrameUpdate [q]) ?_
          (PPMProgramRel.nil t)
  show magicBasisPPMCommandRel F (PPMCommand.applyFrameUpdate [q]) s t
  refine ⟨?_, hmag, hpool, hfail⟩
  simp [List.foldl]
  exact hbits

theorem magicBasisPPM_CX_sound (F : TFactoryContract) (c tgt : Nat) :
    ImplementsGateAsPPM (magicBasisPPMSemanticsModel F) (Gate.CX c tgt)
      (compileArithmeticGateToPPM (Gate.CX c tgt)) := by
  intro s u hGate
  obtain ⟨hbits, hmag, hpool, hfail⟩ := hGate
  -- Intermediate state mid: bits[tgt] := xor s.bits[tgt] (!s.bits[c]); other fields preserved.
  let mid : MagicBasisPPMState :=
    { bits := update s.bits tgt (xor (s.bits tgt) (!s.bits c))
      magicUsed := s.magicUsed
      magicPool := s.magicPool
      failed    := s.failed }
  have hstep1 :
      magicBasisPPMCommandRel F
        (PPMCommand.measurePauliKind PauliKind.Z [c, tgt]) s mid := by
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hstep2 :
      magicBasisPPMCommandRel F (PPMCommand.applyFrameUpdate [tgt]) mid u := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Goal: u.bits = [tgt].foldl ... mid.bits
      simp only [List.foldl_cons, List.foldl_nil]
      show u.bits = update
        (update s.bits tgt (xor (s.bits tgt) (!s.bits c))) tgt
        (! update s.bits tgt (xor (s.bits tgt) (!s.bits c)) tgt)
      rw [hbits]
      funext i
      by_cases hi : i = tgt
      · subst hi
        simp only [update_eq]
        cases s.bits i <;> cases s.bits c <;> rfl
      · rw [update_neq _ _ _ _ hi, update_neq _ _ _ _ hi, update_neq _ _ _ _ hi]
    · show u.magicUsed = s.magicUsed; rw [hmag]
    · show u.magicPool = s.magicPool; rw [hpool]
    · show u.failed = s.failed; rw [hfail]
  exact PPMProgramRel.cons hstep1 (PPMProgramRel.cons hstep2 (PPMProgramRel.nil u))

theorem magicBasisPPM_seq_sound (F : TFactoryContract) (g₁ g₂ : Gate)
    (h₁ : ImplementsGateAsPPM (magicBasisPPMSemanticsModel F) g₁
            (compileArithmeticGateToPPM g₁))
    (h₂ : ImplementsGateAsPPM (magicBasisPPMSemanticsModel F) g₂
            (compileArithmeticGateToPPM g₂)) :
    ImplementsGateAsPPM (magicBasisPPMSemanticsModel F) (Gate.seq g₁ g₂)
      (compileArithmeticGateToPPM (Gate.seq g₁ g₂)) := by
  intro s u hGate
  obtain ⟨mid, hg1, hg2⟩ := hGate
  have hp1 := h₁ s mid hg1
  have hp2 := h₂ mid u hg2
  rw [compileArithmeticGateToPPM_seq]
  exact (PPMProgramRel_append _ _ _ s u).mpr ⟨mid, hp1, hp2⟩

theorem magicBasisPPMSound_ICX (F : TFactoryContract) :
    ∀ g, isICXGate g = true →
      ImplementsGateAsPPM (magicBasisPPMSemanticsModel F) g
        (compileArithmeticGateToPPM g) := by
  intro g
  induction g with
  | I => intro _; exact magicBasisPPM_I_sound F
  | X q => intro _; exact magicBasisPPM_X_sound F q
  | CX c tgt => intro _; exact magicBasisPPM_CX_sound F c tgt
  | CCX _ _ _ => intro h; simp [isICXGate] at h
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hICX
      have h_and : (isICXGate g₁ && isICXGate g₂) = true := hICX
      rw [Bool.and_eq_true] at h_and
      obtain ⟨ha, hb⟩ := h_and
      exact magicBasisPPM_seq_sound F g₁ g₂ (ih₁ ha) (ih₂ hb)

theorem magicBasisPPM_I_reflects (F : TFactoryContract) :
    PPMReflectsGateRel (magicBasisPPMSemanticsModel F) Gate.I
      (compileArithmeticGateToPPM Gate.I) := by
  intro s t h
  show magicBasisPPMGateRel Gate.I s t
  have hst : s = t := (PPMProgramRel_nil_iff _ _ _).mp h
  exact hst.symm

theorem magicBasisPPM_X_reflects (F : TFactoryContract) (q : Nat) :
    PPMReflectsGateRel (magicBasisPPMSemanticsModel F) (Gate.X q)
      (compileArithmeticGateToPPM (Gate.X q)) := by
  intro s t h
  obtain ⟨mid, hcmd, hrest⟩ :=
    PPMProgramRel_cons_inv _ _ _ _ _ h
  have hmid_eq : mid = t := (PPMProgramRel_nil_iff _ _ _).mp hrest
  obtain ⟨h_bits, h_mag, h_pool, h_fail⟩ := hcmd
  simp [List.foldl] at h_bits
  show magicBasisPPMGateRel (Gate.X q) s t
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmid_eq]; exact h_bits
  · rw [← hmid_eq]; exact h_mag
  · rw [← hmid_eq]; exact h_pool
  · rw [← hmid_eq]; exact h_fail

theorem magicBasisPPM_CX_reflects (F : TFactoryContract) (c tgt : Nat) :
    PPMReflectsGateRel (magicBasisPPMSemanticsModel F) (Gate.CX c tgt)
      (compileArithmeticGateToPPM (Gate.CX c tgt)) := by
  intro s u h
  obtain ⟨mid₁, hstep1, hafter⟩ :=
    PPMProgramRel_cons_inv _ _ _ _ _ h
  obtain ⟨mid₂, hstep2, hnil⟩ :=
    PPMProgramRel_cons_inv _ _ _ _ _ hafter
  have hmid2 : mid₂ = u := (PPMProgramRel_nil_iff _ _ _).mp hnil
  obtain ⟨h_mbits, h_mmag, h_mpool, h_mfail⟩ := hstep1
  obtain ⟨h_fbits, h_fmag, h_fpool, h_ffail⟩ := hstep2
  simp [List.foldl] at h_fbits
  show magicBasisPPMGateRel (Gate.CX c tgt) s u
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmid2, h_fbits, h_mbits]
    funext i
    by_cases hi : i = tgt
    · subst hi
      simp only [update_eq]
      cases s.bits i <;> cases s.bits c <;> rfl
    · rw [update_neq _ _ _ _ hi, update_neq _ _ _ _ hi, update_neq _ _ _ _ hi]
  · rw [← hmid2, h_fmag, h_mmag]
  · rw [← hmid2, h_fpool, h_mpool]
  · rw [← hmid2, h_ffail, h_mfail]

theorem magicBasisPPM_seq_reflects (F : TFactoryContract) (g₁ g₂ : Gate)
    (h₁ : PPMReflectsGateRel (magicBasisPPMSemanticsModel F) g₁
            (compileArithmeticGateToPPM g₁))
    (h₂ : PPMReflectsGateRel (magicBasisPPMSemanticsModel F) g₂
            (compileArithmeticGateToPPM g₂)) :
    PPMReflectsGateRel (magicBasisPPMSemanticsModel F) (Gate.seq g₁ g₂)
      (compileArithmeticGateToPPM (Gate.seq g₁ g₂)) := by
  intro s u h
  rw [compileArithmeticGateToPPM_seq] at h
  obtain ⟨mid, hp1, hp2⟩ := PPMProgramRel_append_inv _ _ _ _ _ h
  show magicBasisPPMGateRel (Gate.seq g₁ g₂) s u
  exact ⟨mid, h₁ s mid hp1, h₂ mid u hp2⟩

theorem magicBasisPPMReflects_ICX (F : TFactoryContract) :
    ∀ g, isICXGate g = true →
      PPMReflectsGateRel (magicBasisPPMSemanticsModel F) g
        (compileArithmeticGateToPPM g) := by
  intro g
  induction g with
  | I => intro _; exact magicBasisPPM_I_reflects F
  | X q => intro _; exact magicBasisPPM_X_reflects F q
  | CX c tgt => intro _; exact magicBasisPPM_CX_reflects F c tgt
  | CCX _ _ _ => intro h; simp [isICXGate] at h
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hICX
      have h_and : (isICXGate g₁ && isICXGate g₂) = true := hICX
      rw [Bool.and_eq_true] at h_and
      obtain ⟨ha, hb⟩ := h_and
      exact magicBasisPPM_seq_reflects F g₁ g₂ (ih₁ ha) (ih₂ hb)

/-! ## §10. Concrete observation bridge for the magic-aware
       model. -/

/-- Encoder parametric in the contract `F`.  The factory
    parameter affects only the `ppmCommandRel`
    interpretation of `useMagicT`; encoded states are the
    same. -/
def magicBasisEncodeBits (F : TFactoryContract) (f : Nat → Bool) :
    (magicBasisPPMSemanticsModel F).State :=
  { bits := f, magicUsed := 0, magicPool := [], failed := false }

/-- A magic-aware state observes a bit-state iff its `bits`
    field matches and the `failed` flag is `false`. -/
def magicBasisObservesBits (F : TFactoryContract)
    (s : (magicBasisPPMSemanticsModel F).State)
    (f : Nat → Bool) : Prop :=
  s.bits = f ∧ s.failed = false

theorem magicBasisEncode_observes (F : TFactoryContract) (f : Nat → Bool) :
    magicBasisObservesBits F (magicBasisEncodeBits F f) f := by
  exact ⟨rfl, rfl⟩

/-- Generalised statement: any `magicBasisPPMGateRel`
    transition produces a target state whose `bits` field
    equals `Gate.applyNat g` applied to the source's bits.
    CCX is `False` in this gate relation, so the case
    closes vacuously. -/
theorem magicBasisPPMGateRel_imp_applyNat
    (g : Gate) :
    ∀ (s σ' : MagicBasisPPMState),
      magicBasisPPMGateRel g s σ' → σ'.bits = Gate.applyNat g s.bits := by
  induction g with
  | I =>
      intro s σ' h
      have hst : σ' = s := h
      rw [hst]; rfl
  | X q => intro s σ' h; exact h.1
  | CX c tgt => intro s σ' h; exact h.1
  | CCX _ _ _ => intro s σ' h; exact h.elim
  | seq g₁ g₂ ih₁ ih₂ =>
      intro s σ' h
      obtain ⟨mid, h₁, h₂⟩ := h
      have hb1 : mid.bits = Gate.applyNat g₁ s.bits := ih₁ s mid h₁
      have hb2 : σ'.bits = Gate.applyNat g₂ mid.bits := ih₂ mid σ' h₂
      rw [hb2, hb1]; rfl

/-- Similarly preserve the `failed` flag through any
    `magicBasisPPMGateRel` transition.  Required because
    `magicBasisObservesBits` checks `failed = false`. -/
theorem magicBasisPPMGateRel_preserves_failed
    (g : Gate) :
    ∀ (s σ' : MagicBasisPPMState),
      magicBasisPPMGateRel g s σ' → σ'.failed = s.failed := by
  induction g with
  | I =>
      intro s σ' h
      have hst : σ' = s := h
      rw [hst]
  | X q => intro s σ' h; exact h.2.2.2
  | CX c tgt => intro s σ' h; exact h.2.2.2
  | CCX _ _ _ => intro s σ' h; exact h.elim
  | seq g₁ g₂ ih₁ ih₂ =>
      intro s σ' h
      obtain ⟨mid, h₁, h₂⟩ := h
      have e₁ := ih₁ s mid h₁
      have e₂ := ih₂ mid σ' h₂
      rw [e₂, e₁]

theorem magicBasisGateRel_applyNat_obs (F : TFactoryContract)
    (g : Gate) (f : Nat → Bool)
    (σ' : (magicBasisPPMSemanticsModel F).State)
    (h : (magicBasisPPMSemanticsModel F).gateRel g
            (magicBasisEncodeBits F f) σ') :
    magicBasisObservesBits F σ' (Gate.applyNat g f) := by
  refine ⟨?_, ?_⟩
  · -- bits
    have := magicBasisPPMGateRel_imp_applyNat g (magicBasisEncodeBits F f) σ' h
    exact this
  · -- failed
    have := magicBasisPPMGateRel_preserves_failed g (magicBasisEncodeBits F f) σ' h
    exact this

/-! ## §11. Concrete `PPMRefinesApplyNat` instance. -/

def magicBasisRefinesApplyNat (F : TFactoryContract) :
    PPMRefinesApplyNat (magicBasisPPMSemanticsModel F) :=
  { encodeBits           := magicBasisEncodeBits F
    observesBits         := magicBasisObservesBits F
    encode_observes      := magicBasisEncode_observes F
    gateRel_applyNat_obs := magicBasisGateRel_applyNat_obs F }

/-! ## §12. ICX bridge with NO external arguments,
       lifted to the magic-aware model. -/

theorem compileICXGateToPPM_applyNat_bridge_magicBasisPPM
    (F : TFactoryContract) (g : Gate) (hICX : isICXGate g = true) :
    LogicalGateAsPPMApplyNat (magicBasisPPMSemanticsModel F)
      (magicBasisRefinesApplyNat F) g :=
  LogicalGateAsPPMApplyNat.from_refinement
    (magicBasisPPMSemanticsModel F) (magicBasisRefinesApplyNat F) g
    (magicBasisPPMSound_ICX F g hICX)
    (magicBasisPPMReflects_ICX F g hICX)

/-! ## §13. Shor-facing ICX decoder transfer over magicBasisPPM. -/

theorem shor_arithmetic_ICX_correctness_transfers_to_magicBasisPPM
    (F : TFactoryContract)
    (g : Gate) (hICX : isICXGate g = true)
    (decode : (Nat → Bool) → Nat)
    (input : Nat → Bool) (expected : Nat)
    (σ' : (magicBasisPPMSemanticsModel F).State)
    (hrun :
      PPMProgramRel (magicBasisPPMSemanticsModel F)
        (compileArithmeticGateToPPM g)
        ((magicBasisRefinesApplyNat F).encodeBits input)
        σ')
    (hGateCorrect : decode (Gate.applyNat g input) = expected) :
    ∃ output,
      (magicBasisRefinesApplyNat F).observesBits σ' output
        ∧ decode output = expected :=
  shor_arithmetic_applyNat_correctness_transfers_to_PPM
    (magicBasisPPMSemanticsModel F) (magicBasisRefinesApplyNat F) g
    decode input expected
    (compileICXGateToPPM_applyNat_bridge_magicBasisPPM F g hICX)
    σ' hrun hGateCorrect

/-! ## §14. Future-facing CCX/Toffoli obligation.

    The named precise obligation that a future tick must
    discharge to upgrade `MagicInjectionObligations.CCX_ok`
    against the magic-aware basis model.

    Fields are PROPOSITIONS / data, not theorems — supplying
    a value of this structure constitutes the assumption.
    No instance is constructed here. -/

structure TFactoryToffoliObligation
    (F : TFactoryContract) where
  /-- A magic-using PPM program implementing `Gate.CCX a b c`. -/
  ccx_program            : Nat → Nat → Nat → PPMProgram
  /-- The program actually requests at least one certified-T
      token from the factory. -/
  ccx_uses_certified_T   :
    ∀ a b c, magicRequestCount (ccx_program a b c) > 0
  /-- The program is sound for `Gate.CCX` in the magic-aware
      model.  This field is an ASSUMPTION (a future
      obligation), NOT a theorem proved here. -/
  ccx_sound              :
    ∀ a b c,
      ImplementsGateAsPPM (magicBasisPPMSemanticsModel F)
        (Gate.CCX a b c) (ccx_program a b c)

/-! ## §15. E22 — Non-vacuous Toffoli/T-factory obligation.

    ### §15.a Review of the §14 obligation's vacuity.

    `TFactoryToffoliObligation.ccx_sound` (§14) is stated as:

      ImplementsGateAsPPM (magicBasisPPMSemanticsModel F)
        (Gate.CCX a b c) (ccx_program a b c)

    Recall `ImplementsGateAsPPM sem g ppm := ∀ s t,
    sem.gateRel g s t → PPMProgramRel sem ppm s t`.  In
    `magicBasisPPMGateRel` (§7), the CCX case is `False`, so
    the premise `sem.gateRel (Gate.CCX ...) s t` is never
    satisfied and the implication is vacuously true.  The
    §14 obligation therefore provides NO semantic content
    for Toffoli.

    The fix below introduces a `V2` obligation that talks
    about actual PPM-program execution starting from any
    observing state and ending in a state observing
    `Gate.applyNat (Gate.CCX a b c) input`.  Both sides of
    the implication carry non-trivial content.  The §14
    obligation is preserved (per the project's append-only
    rule) but deprecated. -/

/-! ### §15.b Decoder-free Boolean-CCX observation
       predicate. -/

/-- `σ'` observes the Boolean-`Gate.CCX a b c` image of
    `input` in the magic-aware model.  Used as the
    direct semantic target of a non-vacuous Toffoli
    obligation. -/
def ObservesCCXApplyNat
    (F : TFactoryContract) (a b c : Nat)
    (input : Nat → Bool)
    (σ' : (magicBasisPPMSemanticsModel F).State) : Prop :=
  (magicBasisRefinesApplyNat F).observesBits σ'
    (Gate.applyNat (Gate.CCX a b c) input)

/-! ### §15.c The repaired (V2) Toffoli/T-factory
       obligation.

    Strong form: the contract holds starting from ANY
    observing state, not only from the canonical
    `encodeBits` encoding.  This is needed for the `seq`
    induction below, and is the natural form of a Toffoli
    teleportation contract that may consume tokens supplied
    by upstream gates. -/

structure TFactoryToffoliObligationV2 (F : TFactoryContract) where
  /-- A PPM program implementing `Gate.CCX a b c`. -/
  ccx_program : Nat → Nat → Nat → PPMProgram
  /-- The program uses at least one certified-T request. -/
  ccx_uses_magic : ∀ a b c, magicRequestCount (ccx_program a b c) > 0
  /-- The program implements Boolean Toffoli on observed
      bits, starting from ANY state already observing
      `input`.  This is the non-vacuous semantic content. -/
  ccx_correct_on_success :
    ∀ a b c
      (input : Nat → Bool)
      (s σ' : (magicBasisPPMSemanticsModel F).State),
      (magicBasisRefinesApplyNat F).observesBits s input →
      PPMProgramRel (magicBasisPPMSemanticsModel F)
        (ccx_program a b c) s σ' →
      (magicBasisRefinesApplyNat F).observesBits σ'
        (Gate.applyNat (Gate.CCX a b c) input)

/-! ### §15.d CCX decoder-transfer from the V2 obligation. -/

theorem toffoli_obligationV2_decoder_transfer
    (F : TFactoryContract)
    (obl : TFactoryToffoliObligationV2 F)
    (a b c : Nat)
    (decode : (Nat → Bool) → Nat)
    (input : Nat → Bool) (expected : Nat)
    (σ' : (magicBasisPPMSemanticsModel F).State)
    (hrun :
      PPMProgramRel (magicBasisPPMSemanticsModel F)
        (obl.ccx_program a b c)
        ((magicBasisRefinesApplyNat F).encodeBits input) σ')
    (hGateCorrect :
      decode (Gate.applyNat (Gate.CCX a b c) input) = expected) :
    ∃ output,
      (magicBasisRefinesApplyNat F).observesBits σ' output
        ∧ decode output = expected :=
  ⟨Gate.applyNat (Gate.CCX a b c) input,
    obl.ccx_correct_on_success a b c input _ σ'
      ((magicBasisRefinesApplyNat F).encode_observes input) hrun,
    hGateCorrect⟩

/-! ### §15.e New compiler that uses the V2 program for CCX. -/

/-- A compiler that emits the same PPM program as
    `compileArithmeticGateToPPM` on ICX gates (so ICX
    soundness/reflection from §9 carries over), and uses the
    V2 obligation's `ccx_program` on CCX.  Recurses on
    `seq` by concatenation. -/
def compileArithmeticGateToPPMWithToffoli
    (F : TFactoryContract)
    (obl : TFactoryToffoliObligationV2 F) :
    Gate → PPMProgram
  | Gate.I         => compileArithmeticGateToPPM Gate.I
  | Gate.X q       => compileArithmeticGateToPPM (Gate.X q)
  | Gate.CX c t    => compileArithmeticGateToPPM (Gate.CX c t)
  | Gate.CCX a b c => obl.ccx_program a b c
  | Gate.seq g₁ g₂ =>
      compileArithmeticGateToPPMWithToffoli F obl g₁
        ++ compileArithmeticGateToPPMWithToffoli F obl g₂

/-! ### §15.f Strong soundness from ANY observing state.

    Inducts on the gate.  ICX cases reuse the §6/§9 / §10
    structure (inversion + bit equations + `failed`
    preservation).  CCX uses `obl.ccx_correct_on_success`
    directly.  `seq` uses `PPMProgramRel_append_inv` and
    the two IHs. -/

theorem compileArithmeticGateToPPMWithToffoli_applyNat_sound_from_observed
    (F : TFactoryContract)
    (obl : TFactoryToffoliObligationV2 F) :
    ∀ (g : Gate) (input : Nat → Bool)
      (s σ' : (magicBasisPPMSemanticsModel F).State),
      (magicBasisRefinesApplyNat F).observesBits s input →
      PPMProgramRel (magicBasisPPMSemanticsModel F)
        (compileArithmeticGateToPPMWithToffoli F obl g) s σ' →
      (magicBasisRefinesApplyNat F).observesBits σ'
        (Gate.applyNat g input) := by
  intro g
  induction g with
  | I =>
      intro input s σ' hobs hrun
      -- compile = []; PPMProgramRel sem [] s σ' ↔ s = σ'
      have hsσ : s = σ' := (PPMProgramRel_nil_iff _ _ _).mp hrun
      rw [← hsσ]
      exact hobs
  | X q =>
      intro input s σ' hobs hrun
      -- compile = [applyFrameUpdate [q]]
      obtain ⟨mid, hcmd, hrest⟩ :=
        PPMProgramRel_cons_inv _ _ _ _ _ hrun
      have hmid : mid = σ' := (PPMProgramRel_nil_iff _ _ _).mp hrest
      obtain ⟨h_bits, h_mag, h_pool, h_fail⟩ := hcmd
      simp [List.foldl] at h_bits
      obtain ⟨hs_bits, hs_fail⟩ := hobs
      refine ⟨?_, ?_⟩
      · -- σ'.bits = update input q (!input q)
        rw [← hmid, h_bits, hs_bits]
        rfl
      · rw [← hmid, h_fail]; exact hs_fail
  | CX c tgt =>
      intro input s u hobs hrun
      -- compile = [meas Z [c, tgt]; applyFrameUpdate [tgt]]
      obtain ⟨mid₁, hstep1, hafter⟩ :=
        PPMProgramRel_cons_inv _ _ _ _ _ hrun
      obtain ⟨mid₂, hstep2, hnil⟩ :=
        PPMProgramRel_cons_inv _ _ _ _ _ hafter
      have hmid2 : mid₂ = u := (PPMProgramRel_nil_iff _ _ _).mp hnil
      obtain ⟨h_mbits, h_mmag, h_mpool, h_mfail⟩ := hstep1
      obtain ⟨h_fbits, h_fmag, h_fpool, h_ffail⟩ := hstep2
      simp [List.foldl] at h_fbits
      obtain ⟨hs_bits, hs_fail⟩ := hobs
      refine ⟨?_, ?_⟩
      · rw [← hmid2, h_fbits, h_mbits, hs_bits]
        simp only [Gate.applyNat_CX]
        funext i
        by_cases hi : i = tgt
        · subst hi
          simp only [update_eq]
          cases input i <;> cases input c <;> rfl
        · rw [update_neq _ _ _ _ hi, update_neq _ _ _ _ hi, update_neq _ _ _ _ hi]
      · rw [← hmid2, h_ffail, h_mfail]; exact hs_fail
  | CCX a b c =>
      intro input s σ' hobs hrun
      -- compile = obl.ccx_program a b c
      exact obl.ccx_correct_on_success a b c input s σ' hobs hrun
  | seq g₁ g₂ ih₁ ih₂ =>
      intro input s σ' hobs hrun
      -- compile = compileArithmeticGateToPPMWithToffoli F obl g₁ ++ ... g₂
      obtain ⟨mid, hp1, hp2⟩ := PPMProgramRel_append_inv _ _ _ _ _ hrun
      have hmid := ih₁ input s mid hobs hp1
      have hσ := ih₂ (Gate.applyNat g₁ input) mid σ' hmid hp2
      -- Gate.applyNat (Gate.seq g₁ g₂) input = Gate.applyNat g₂ (Gate.applyNat g₁ input)
      exact hσ

/-! ### §15.g Canonical-encoding sound theorem. -/

theorem compileArithmeticGateToPPMWithToffoli_applyNat_sound
    (F : TFactoryContract)
    (obl : TFactoryToffoliObligationV2 F)
    (g : Gate) (input : Nat → Bool)
    (σ' : (magicBasisPPMSemanticsModel F).State)
    (hrun :
      PPMProgramRel (magicBasisPPMSemanticsModel F)
        (compileArithmeticGateToPPMWithToffoli F obl g)
        ((magicBasisRefinesApplyNat F).encodeBits input) σ') :
    (magicBasisRefinesApplyNat F).observesBits σ'
      (Gate.applyNat g input) :=
  compileArithmeticGateToPPMWithToffoli_applyNat_sound_from_observed
    F obl g input _ σ'
    ((magicBasisRefinesApplyNat F).encode_observes input) hrun

/-! ### §15.h Shor-facing full-arithmetic decoder transfer
       under the V2 obligation. -/

theorem shor_arithmetic_full_correctness_transfers_to_magicPPM_from_ToffoliObligation
    (F : TFactoryContract)
    (obl : TFactoryToffoliObligationV2 F)
    (g : Gate)
    (decode : (Nat → Bool) → Nat)
    (input : Nat → Bool) (expected : Nat)
    (σ' : (magicBasisPPMSemanticsModel F).State)
    (hrun :
      PPMProgramRel (magicBasisPPMSemanticsModel F)
        (compileArithmeticGateToPPMWithToffoli F obl g)
        ((magicBasisRefinesApplyNat F).encodeBits input) σ')
    (hGateCorrect : decode (Gate.applyNat g input) = expected) :
    ∃ output,
      (magicBasisRefinesApplyNat F).observesBits σ' output
        ∧ decode output = expected :=
  ⟨Gate.applyNat g input,
    compileArithmeticGateToPPMWithToffoli_applyNat_sound F obl g input σ' hrun,
    hGateCorrect⟩

/-! ### §15.i Resource-count lemmas for the new compiler. -/

theorem magicRequestCount_compileWithToffoli_I
    (F : TFactoryContract) (obl : TFactoryToffoliObligationV2 F) :
    magicRequestCount (compileArithmeticGateToPPMWithToffoli F obl Gate.I) = 0 :=
  magicRequestCount_compile_I

theorem magicRequestCount_compileWithToffoli_X
    (F : TFactoryContract) (obl : TFactoryToffoliObligationV2 F) (q : Nat) :
    magicRequestCount (compileArithmeticGateToPPMWithToffoli F obl (Gate.X q)) = 0 :=
  magicRequestCount_compile_X q

theorem magicRequestCount_compileWithToffoli_CX
    (F : TFactoryContract) (obl : TFactoryToffoliObligationV2 F) (c t : Nat) :
    magicRequestCount (compileArithmeticGateToPPMWithToffoli F obl (Gate.CX c t)) = 0 :=
  magicRequestCount_compile_CX c t

theorem magicRequestCount_compileWithToffoli_CCX
    (F : TFactoryContract) (obl : TFactoryToffoliObligationV2 F) (a b c : Nat) :
    magicRequestCount (compileArithmeticGateToPPMWithToffoli F obl (Gate.CCX a b c))
      = magicRequestCount (obl.ccx_program a b c) := rfl

theorem magicRequestCount_compileWithToffoli_seq
    (F : TFactoryContract) (obl : TFactoryToffoliObligationV2 F) (g₁ g₂ : Gate) :
    magicRequestCount (compileArithmeticGateToPPMWithToffoli F obl (Gate.seq g₁ g₂))
      = magicRequestCount (compileArithmeticGateToPPMWithToffoli F obl g₁)
        + magicRequestCount (compileArithmeticGateToPPMWithToffoli F obl g₂) := by
  show magicRequestCount
        (compileArithmeticGateToPPMWithToffoli F obl g₁
          ++ compileArithmeticGateToPPMWithToffoli F obl g₂)
      = _
  exact magicRequestCount_append _ _

theorem magicRequestCount_compileWithToffoli_ICX
    (F : TFactoryContract) (obl : TFactoryToffoliObligationV2 F) :
    ∀ g, isICXGate g = true →
      magicRequestCount (compileArithmeticGateToPPMWithToffoli F obl g) = 0 := by
  intro g
  induction g with
  | I => intro _; rfl
  | X q => intro _; rfl
  | CX c t => intro _; rfl
  | CCX _ _ _ => intro h; simp [isICXGate] at h
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hICX
      have h_and : (isICXGate g₁ && isICXGate g₂) = true := hICX
      rw [Bool.and_eq_true] at h_and
      obtain ⟨ha, hb⟩ := h_and
      rw [magicRequestCount_compileWithToffoli_seq, ih₁ ha, ih₂ hb]

/-! ### §15.j Note on the relationship to
       `MagicInjectionObligations.CCX_ok`.

    `MagicInjectionObligations.CCX_ok` (§17.d of
    `CircuitToPPMInterface.lean`) is stated as
    `ImplementsGateAsPPM sem (Gate.CCX a b t)
       (compileArithmeticGateToPPM (Gate.CCX a b t))`,
    which has the same vacuity issue as the V1 obligation
    here whenever `sem.gateRel (Gate.CCX ...) = False`
    (as in `cxMacroPPMSemanticsModel` and
    `magicBasisPPMSemanticsModel`).

    `TFactoryToffoliObligationV2` is the non-vacuous
    `Gate.applyNat`-level replacement.  Connecting V2 to
    `MagicInjectionObligations.CCX_ok` is NOT attempted here
    because the latter is tied to a forward-only
    `ImplementsGateAsPPM` shape; future work that wants the
    bridge can either:
      (i) reformulate `MagicInjectionObligations.CCX_ok` in
          observational form, or
      (ii) supply a model whose CCX-side `gateRel` is
           non-vacuous (a real Toffoli denotational
           substrate). -/

/-! ## §16. Status summary.

    Closed in this file:

    * `TFactoryContract` + `WellFormed` predicate.
    * `MagicToken` / `FactoryOutcome` /
      `MagicToken.IsCertifiedTFrom`.
    * `MagicBasisPPMState` (+ projection / lifting).
    * `consumeCertifiedT`, `requestTSuccess`,
      `hasCertifiedT`.
    * `magicRequestCount` with append + per-Gate lemmas;
      `magicRequestCount_compile_ICX`.
    * `allMagicRequestsSuccessProbLB` (Nat-scaled) + base
      cases.
    * `magicBasisPPMCommandRel`, `magicBasisPPMGateRel`,
      `magicBasisPPMSemanticsModel F`.
    * `magicBasisPPMSound_ICX F` and
      `magicBasisPPMReflects_ICX F`.
    * `magicBasisRefinesApplyNat F` — concrete
      `PPMRefinesApplyNat` instance.
    * `compileICXGateToPPM_applyNat_bridge_magicBasisPPM` —
      ICX `LogicalGateAsPPMApplyNat` instance with no
      external arguments.
    * `shor_arithmetic_ICX_correctness_transfers_to_magicBasisPPM`
      — Shor-facing ICX decoder transfer with no external
      arguments under the magic-aware model.
    * `TFactoryToffoliObligation F` — named CCX obligation
      structure for a future tick.

    Deferred (explicit obligations, not silent axioms):

    * Discharging `TFactoryToffoliObligation F` (a real
      Toffoli decomposition using certified T tokens).
    * Equivalence of `magicBasisPPMSemanticsModel F` with
      either `cxMacroPPMSemanticsModel n` or
      `magicAwarePPMSemanticsModel n` (separate semantic
      substrate).
    * Physical T-state distillation correctness.
    * Gate teleportation correctness.
    * Full Shor success-probability correctness.
    * QEC / surgery / backend implementation of magic
      factories.
    * QPE / non-Clifford rotations. -/

end FormalRV.Framework.CircuitToPPMMagicFactory
