/-
  FormalRV.Framework.CircuitToPPMFactoryProvision — closing the
  gap between the logical arithmetic Gate IR and an *executable*
  magic-aware PPM program supplied by a T-factory / `RequestMagicState`
  system call.

  ## What gap this file closes

  The E18–E23 stack
  (`CircuitToPPMSemanticBridge` → `…ObservationBridge` →
  `…MagicFactory` → `…ToffoliMagic`) proved *soundness* of the
  magic-aware compiler:

      IF a run `MagicPPMProgramRel F (compile g) s σ'` exists,
      THEN `σ'` observes `Gate.applyNat g input`.

  But three things were missing, and they are exactly the seam between
  the verified logical circuit and the PPM-with-factory layer:

  1. **Executability / totality.**  The canonical encoder
     `magicBasisEncodeBits` produces an *empty* magic pool
     (`magicPool := []`).  `teleportCCXRel` consumes a certified-T
     token from the head of the pool, so from an empty pool *no run
     exists* for any circuit containing a Toffoli.  The soundness
     theorems are therefore vacuous on the full arithmetic circuit:
     nobody proved a successful run **exists**.

  2. **Factory system-call provisioning.**  The magic pool was an
     abstract `List MagicToken`.  It was never connected to the
     backend `SysCallKind.RequestMagicState` factory call, nor to the
     `AtomicFactorySpec` resource model, nor was the *number* of magic
     requests tied to the circuit's Toffoli count.

  3. **Resource ↔ executability link.**  Nobody proved that
     provisioning ≥ (magic demand) certified-T tokens is *sufficient*
     to run the whole compiled program to completion.

  This file closes all three at the PPM/logical layer, honestly:

  * `magicCompile_executable` — from a pool of certified-T tokens whose
    length is ≥ the program's magic demand, a successful run
    **exists** (with exact pool-consumption bookkeeping
    `σ'.magicPool = s.magicPool.drop demand`).
  * `compileToMagicPPM_run_observe` /
    `…_provisioned_run_observe` — executability ∧ the (already-proved)
    observational soundness, giving **total correctness** at this
    layer: the program runs AND its output observes `Gate.applyNat g`.
  * `factoryProvision` / `factoryRequestSchedule` — a concrete
    certified-T token pool and the matching list of
    `RequestMagicState` system calls; their lengths both equal the
    circuit's magic demand.
  * `TFactoryContract.ofAtomic` — connects the abstract PPM-layer
    `TFactoryContract` to the backend `AtomicFactorySpec`
    (the E21 "future tick can connect them" obligation).
  * `shorMagicDemand_eq_ccxCount` — the magic demand equals the
    circuit's Toffoli count: one teleported-CCX magic request per
    `Gate.CCX`.

  ## Honesty boundary (unchanged from E23)

  This file does NOT prove (and does not pretend to):
  * the internal Clifford+T circuit realising `teleportCCXRel`;
  * physical T-state distillation / cultivation correctness;
  * QEC / lattice-surgery backend implementation of the factory or of
    `teleportCCX`;
  * the probabilistic success semantics (we provision the *success*
    branch and count requests; the per-request failure probability
    lives in `TFactoryContract.successProbLB_ppm` /
    `AtomicFactorySpec.success_probability_ppm`, not in the run);
  * QPE / non-Clifford rotations.

  Everything proved here is structural: the abstract teleportation
  contract `teleportCCXRel` is taken as the success-branch semantics
  (E23), and we show the *compiler + factory provisioning* makes a
  whole verified arithmetic circuit executable and correct modulo that
  one named contract.
-/
import FormalRV.PPM.Magic.CircuitToPPMToffoliMagic

namespace FormalRV.Framework.CircuitToPPMFactoryProvision

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.Framework.Factory
open FormalRV.Framework.CircuitToPPMInterface
open FormalRV.Framework.CircuitToPPMSemanticBridge
open FormalRV.Framework.CircuitToPPMObservationBridge
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMToffoliMagic
open FormalRV.BQAlgo

/-! ## §1. Certified-T token pools. -/

/-- Every token in `pool` is a certified-T token issued by `F`. -/
def AllCertifiedT (F : TFactoryContract) (pool : List MagicToken) : Prop :=
  ∀ tok ∈ pool, MagicToken.IsCertifiedTFrom F tok

theorem AllCertifiedT_nil (F : TFactoryContract) : AllCertifiedT F [] := by
  intro tok htok; exact absurd htok (by simp)

/-- Dropping a prefix preserves the all-certified property
    (every remaining token was already in the pool). -/
theorem AllCertifiedT_drop (F : TFactoryContract) :
    ∀ (n : Nat) (pool : List MagicToken),
      AllCertifiedT F pool → AllCertifiedT F (pool.drop n) := by
  intro n
  induction n with
  | zero => intro pool h; simpa using h
  | succ k ih =>
      intro pool h
      cases pool with
      | nil => intro tok htok; simp at htok
      | cons a l =>
          show AllCertifiedT F (l.drop k)
          apply ih l
          intro tok htok
          exact h tok (List.mem_cons_of_mem a htok)

/-! ## §2. Bit-input encoder carrying a provisioned magic pool.

    The canonical `magicBasisEncodeBits` has an EMPTY pool, so it
    cannot start a run that consumes magic.  `encodeWithPool` injects a
    Boolean input together with a factory-provisioned token pool while
    still observing `input` (bits match, no failure). -/

def encodeWithPool (input : Nat → Bool) (pool : List MagicToken) :
    MagicBasisPPMState :=
  { bits := input, magicUsed := 0, magicPool := pool, failed := false }

@[simp] theorem encodeWithPool_bits (input : Nat → Bool) (pool : List MagicToken) :
    (encodeWithPool input pool).bits = input := rfl

@[simp] theorem encodeWithPool_magicPool (input : Nat → Bool) (pool : List MagicToken) :
    (encodeWithPool input pool).magicPool = pool := rfl

@[simp] theorem encodeWithPool_failed (input : Nat → Bool) (pool : List MagicToken) :
    (encodeWithPool input pool).failed = false := rfl

theorem encodeWithPool_observes (F : TFactoryContract)
    (input : Nat → Bool) (pool : List MagicToken) :
    (magicBasisRefinesApplyNat F).observesBits (encodeWithPool input pool) input :=
  ⟨rfl, rfl⟩

/-! ## §3. Totality of the ICX gate relation.

    For the ICX fragment (no Toffoli) the magic-aware gate relation is
    total and pool/failed-preserving: from any state there is a target
    state related to it that leaves the magic pool and failure flag
    untouched.  This lets us *construct* (not merely accept) a run for
    the ICX cases of the executability theorem, reusing E21's ICX
    forward soundness `magicBasisPPMSound_ICX`. -/

theorem magicBasisPPMGateRel_ICX_total :
    ∀ (g : Gate), isICXGate g = true →
      ∀ (s : MagicBasisPPMState),
        ∃ t, magicBasisPPMGateRel g s t
          ∧ t.magicPool = s.magicPool ∧ t.failed = s.failed := by
  intro g
  induction g with
  | I =>
      intro _ s
      exact ⟨s, rfl, rfl, rfl⟩
  | X q =>
      intro _ s
      refine ⟨{ bits := update s.bits q (!s.bits q), magicUsed := s.magicUsed,
                magicPool := s.magicPool, failed := s.failed }, ?_, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl, rfl⟩
  | CX c tgt =>
      intro _ s
      refine ⟨{ bits := update s.bits tgt (xor (s.bits tgt) (s.bits c)),
                magicUsed := s.magicUsed, magicPool := s.magicPool,
                failed := s.failed }, ?_, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl, rfl⟩
  | CCX a b c =>
      intro h _
      simp [isICXGate] at h
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hICX s
      have h_and : (isICXGate g₁ && isICXGate g₂) = true := hICX
      rw [Bool.and_eq_true] at h_and
      obtain ⟨ha, hb⟩ := h_and
      obtain ⟨mid, hrel₁, hpool₁, hfail₁⟩ := ih₁ ha s
      obtain ⟨t, hrel₂, hpool₂, hfail₂⟩ := ih₂ hb mid
      refine ⟨t, ⟨mid, hrel₁, hrel₂⟩, ?_, ?_⟩
      · rw [hpool₂, hpool₁]
      · rw [hfail₂, hfail₁]

/-- For ICX gates the extended compiler equals the base compiler's
    output wrapped in `.base`.  (CCX is the only case that emits the
    `teleportCCX` primitive.) -/
theorem compileMagic_ICX_eq_base_map :
    ∀ (g : Gate), isICXGate g = true →
      compileArithmeticGateToMagicPPM g
        = (compileArithmeticGateToPPM g).map MagicPPMCommand.base := by
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
      show compileArithmeticGateToMagicPPM g₁ ++ compileArithmeticGateToMagicPPM g₂
            = (compileArithmeticGateToPPM g₁ ++ compileArithmeticGateToPPM g₂).map
                MagicPPMCommand.base
      rw [ih₁ ha, ih₂ hb, List.map_append]

/-- ICX executability: a run of the extended compiled program exists
    from any state, leaving the magic pool unchanged (ICX gates request
    no magic). -/
theorem magicCompile_executable_ICX (F : TFactoryContract) :
    ∀ (g : Gate), isICXGate g = true →
      ∀ (s : MagicBasisPPMState),
        ∃ σ', MagicPPMProgramRel F (compileArithmeticGateToMagicPPM g) s σ'
            ∧ σ'.magicPool = s.magicPool := by
  intro g hICX s
  obtain ⟨t, hrel, hpool, _hfail⟩ := magicBasisPPMGateRel_ICX_total g hICX s
  have hsound :
      PPMProgramRel (magicBasisPPMSemanticsModel F)
        (compileArithmeticGateToPPM g) s t :=
    magicBasisPPMSound_ICX F g hICX s t hrel
  have hrun :
      MagicPPMProgramRel F
        ((compileArithmeticGateToPPM g).map MagicPPMCommand.base) s t :=
    (MagicPPMProgramRel_base_map_iff F (compileArithmeticGateToPPM g) s t).mpr hsound
  rw [← compileMagic_ICX_eq_base_map g hICX] at hrun
  exact ⟨t, hrun, hpool⟩

/-! ## §4. The executability theorem (the missing existence direction).

    Given a magic pool of certified-T tokens whose length is at least
    the program's magic demand, a successful run of the whole compiled
    program exists, consuming exactly `demand` tokens from the head of
    the pool. -/

theorem magicCompile_executable (F : TFactoryContract) :
    ∀ (g : Gate) (s : MagicBasisPPMState),
      AllCertifiedT F s.magicPool →
      magicPPMRequestCount (compileArithmeticGateToMagicPPM g) ≤ s.magicPool.length →
      ∃ σ',
        MagicPPMProgramRel F (compileArithmeticGateToMagicPPM g) s σ'
        ∧ σ'.magicPool
            = s.magicPool.drop
                (magicPPMRequestCount (compileArithmeticGateToMagicPPM g)) := by
  intro g
  induction g with
  | I =>
      intro s _ _
      refine ⟨s, MagicPPMProgramRel.nil s, ?_⟩
      rw [magicPPMRequestCount_compileArithmeticGateToMagicPPM_I, List.drop_zero]
  | X q =>
      intro s _ _
      obtain ⟨σ', hrun, hpool⟩ := magicCompile_executable_ICX F (Gate.X q) rfl s
      refine ⟨σ', hrun, ?_⟩
      rw [magicPPMRequestCount_compileArithmeticGateToMagicPPM_X, List.drop_zero]
      exact hpool
  | CX c t =>
      intro s _ _
      obtain ⟨σ', hrun, hpool⟩ := magicCompile_executable_ICX F (Gate.CX c t) rfl s
      refine ⟨σ', hrun, ?_⟩
      rw [magicPPMRequestCount_compileArithmeticGateToMagicPPM_CX, List.drop_zero]
      exact hpool
  | CCX a b c =>
      intro s hcert hlen
      have hcount :
          magicPPMRequestCount (compileArithmeticGateToMagicPPM (Gate.CCX a b c)) = 1 :=
        magicPPMRequestCount_compileArithmeticGateToMagicPPM_CCX a b c
      have hlen1 : 1 ≤ s.magicPool.length := by rw [hcount] at hlen; exact hlen
      cases hm : s.magicPool with
      | nil =>
          exfalso; rw [hm] at hlen1; exact absurd hlen1 (by decide)
      | cons tok rest =>
          have htok : MagicToken.IsCertifiedTFrom F tok := by
            apply hcert; rw [hm]; simp
          refine ⟨{ bits := Gate.applyNat (Gate.CCX a b c) s.bits,
                    magicUsed := s.magicUsed + 1, magicPool := rest,
                    failed := s.failed }, ?_, ?_⟩
          · refine MagicPPMProgramRel.cons ?_ (MagicPPMProgramRel.nil _)
            exact ⟨tok, rest, hm, htok, rfl, rfl, rfl, rfl⟩
          · simp [hcount, hm]
  | seq g₁ g₂ ih₁ ih₂ =>
      intro s hcert hlen
      have hcount :
          magicPPMRequestCount (compileArithmeticGateToMagicPPM (Gate.seq g₁ g₂))
            = magicPPMRequestCount (compileArithmeticGateToMagicPPM g₁)
              + magicPPMRequestCount (compileArithmeticGateToMagicPPM g₂) :=
        magicPPMRequestCount_compileArithmeticGateToMagicPPM_seq g₁ g₂
      rw [hcount] at hlen
      have hlen1 :
          magicPPMRequestCount (compileArithmeticGateToMagicPPM g₁) ≤ s.magicPool.length := by
        omega
      obtain ⟨mid, hrun₁, hpool₁⟩ := ih₁ s hcert hlen1
      have hcert_mid : AllCertifiedT F mid.magicPool := by
        rw [hpool₁]; exact AllCertifiedT_drop F _ s.magicPool hcert
      have hlen_mid :
          magicPPMRequestCount (compileArithmeticGateToMagicPPM g₂) ≤ mid.magicPool.length := by
        rw [hpool₁, List.length_drop]; omega
      obtain ⟨σ', hrun₂, hpool₂⟩ := ih₂ mid hcert_mid hlen_mid
      refine ⟨σ', ?_, ?_⟩
      · show MagicPPMProgramRel F
              (compileArithmeticGateToMagicPPM g₁ ++ compileArithmeticGateToMagicPPM g₂)
              s σ'
        exact (MagicPPMProgramRel_append F _ _ s σ').mpr ⟨mid, hrun₁, hrun₂⟩
      · rw [hcount, hpool₂, hpool₁, List.drop_drop, Nat.add_comm]

/-! ## §5. Total correctness at the PPM-with-factory layer.

    Executability (§4) ∧ observational soundness (E23,
    `compileArithmeticGateToMagicPPM_applyNat_sound_from_observed`)
    gives the headline statement: from a certified-T pool of
    sufficient size, the compiled program **runs** and its output
    **observes** `Gate.applyNat g input`. -/

theorem compileToMagicPPM_run_observe (F : TFactoryContract)
    (g : Gate) (input : Nat → Bool) (pool : List MagicToken)
    (hcert : AllCertifiedT F pool)
    (hlen : magicPPMRequestCount (compileArithmeticGateToMagicPPM g) ≤ pool.length) :
    ∃ σ',
      MagicPPMProgramRel F (compileArithmeticGateToMagicPPM g)
        (encodeWithPool input pool) σ'
      ∧ (magicBasisRefinesApplyNat F).observesBits σ' (Gate.applyNat g input) := by
  obtain ⟨σ', hrun, _hpool⟩ :=
    magicCompile_executable F g (encodeWithPool input pool) hcert hlen
  refine ⟨σ', hrun, ?_⟩
  exact compileArithmeticGateToMagicPPM_applyNat_sound_from_observed F g input
    (encodeWithPool input pool) σ' (encodeWithPool_observes F input pool) hrun

/-! ## §6. Factory provisioning: certified-T pool + system-call list. -/

/-- The magic demand of an arithmetic circuit: the number of certified-T
    teleportation requests its extended compilation issues (one per
    `Gate.CCX`). -/
def shorMagicDemand (g : Gate) : Nat :=
  magicPPMRequestCount (compileArithmeticGateToMagicPPM g)

/-- A single certified-T token issued by factory `F`. -/
def certifiedTToken (F : TFactoryContract) : MagicToken :=
  { tokenId := 0, factoryId := F.factoryId, kind := MagicStateKind.T, certified := true }

theorem certifiedTToken_isCertified (F : TFactoryContract) :
    MagicToken.IsCertifiedTFrom F (certifiedTToken F) :=
  ⟨rfl, rfl, rfl⟩

/-- A factory provision of `K` certified-T tokens. -/
def factoryProvision (F : TFactoryContract) (K : Nat) : List MagicToken :=
  List.replicate K (certifiedTToken F)

theorem factoryProvision_length (F : TFactoryContract) (K : Nat) :
    (factoryProvision F K).length = K := by
  unfold factoryProvision; rw [List.length_replicate]

theorem factoryProvision_allCertified (F : TFactoryContract) (K : Nat) :
    AllCertifiedT F (factoryProvision F K) := by
  intro tok htok
  have htok_eq : tok = certifiedTToken F := by
    unfold factoryProvision at htok
    exact List.eq_of_mem_replicate htok
  rw [htok_eq]; exact certifiedTToken_isCertified F

/-- The factory **system call** schedule: `K` `RequestMagicState` calls
    targeting `factoryZone`, pipelined back-to-back at the steady-state
    period `period_us` (one cultivation output per period). -/
def factoryRequestSchedule (factoryZone period_us K : Nat) : List SysCall :=
  (List.range K).map (fun i =>
    { kind     := SysCallKind.RequestMagicState factoryZone
      begin_us := i * period_us
      end_us   := (i + 1) * period_us })

theorem factoryRequestSchedule_length (factoryZone period_us K : Nat) :
    (factoryRequestSchedule factoryZone period_us K).length = K := by
  unfold factoryRequestSchedule
  rw [List.length_map, List.length_range]

/-- Every scheduled call is a `RequestMagicState` to the declared
    factory zone. -/
theorem factoryRequestSchedule_all_requestMagic (factoryZone period_us K : Nat) :
    ∀ sc ∈ factoryRequestSchedule factoryZone period_us K,
      sc.kind = SysCallKind.RequestMagicState factoryZone := by
  intro sc hsc
  unfold factoryRequestSchedule at hsc
  rw [List.mem_map] at hsc
  obtain ⟨i, _, rfl⟩ := hsc
  rfl

/-- Wallclock latency (µs) to provision `K` cultivation outputs, taken
    from the backend `AtomicFactorySpec` pipeline-latency model. -/
def factoryProvisionLatency (spec : AtomicFactorySpec) (K : Nat) : Nat :=
  spec.total_latency_for_n_outputs K

/-- **Loop closure**: number of factory `RequestMagicState` system calls
    = number of certified-T tokens provisioned = the circuit's magic
    demand.  Tokens supplied, requests issued, and demand all agree. -/
theorem factory_schedule_meets_demand (F : TFactoryContract)
    (factoryZone period_us : Nat) (g : Gate) :
    (factoryRequestSchedule factoryZone period_us (shorMagicDemand g)).length
        = shorMagicDemand g
    ∧ (factoryProvision F (shorMagicDemand g)).length = shorMagicDemand g :=
  ⟨factoryRequestSchedule_length _ _ _, factoryProvision_length _ _⟩

/-! ## §7. Connecting the PPM-layer factory contract to the backend
       `AtomicFactorySpec` (the E21 deferred connection). -/

/-- Build a PPM-layer `TFactoryContract` from a backend
    `AtomicFactorySpec`.  Output-error ppm is `1 - fidelity`. -/
def TFactoryContract.ofAtomic (spec : AtomicFactorySpec) (fid : Nat) :
    TFactoryContract :=
  { factoryId         := fid
    outputKind        := spec.kind
    latencyCycles     := spec.time_per_state_us
    footprintSites    := spec.factory_atoms
    successProbLB_ppm := spec.success_probability_ppm
    outputErrorUB_ppm := 1_000_000 - spec.output_fidelity_x1e6
    heraldedFailure   := false }

theorem TFactoryContract.ofAtomic_wellFormed (spec : AtomicFactorySpec) (fid : Nat)
    (hkind : spec.kind = MagicStateKind.T)
    (hsucc : spec.success_probability_ppm ≤ 1_000_000) :
    (TFactoryContract.ofAtomic spec fid).WellFormed := by
  refine ⟨hkind, hsucc, ?_⟩
  show 1_000_000 - spec.output_fidelity_x1e6 ≤ 1_000_000
  omega

/-! ## §8. Provisioned, total-correctness statement (generic). -/

/-- **Provisioned total correctness.**  Compile `g` to the extended
    magic-aware PPM program, provision exactly `shorMagicDemand g`
    certified-T tokens from `F`, and the program **runs** from the
    provisioned input state and **observes** `Gate.applyNat g input`.
    No external Toffoli obligation, no empty-pool vacuity. -/
theorem compileToMagicPPM_provisioned_run_observe (F : TFactoryContract)
    (g : Gate) (input : Nat → Bool) :
    ∃ σ',
      MagicPPMProgramRel F (compileArithmeticGateToMagicPPM g)
        (encodeWithPool input (factoryProvision F (shorMagicDemand g))) σ'
      ∧ (magicBasisRefinesApplyNat F).observesBits σ' (Gate.applyNat g input) := by
  refine compileToMagicPPM_run_observe F g input
    (factoryProvision F (shorMagicDemand g))
    (factoryProvision_allCertified F (shorMagicDemand g)) ?_
  rw [factoryProvision_length]
  exact Nat.le_refl _

/-- **Provisioned decoder transfer.**  Any `Gate.applyNat`-level
    decoder postcondition (the shape Shor's arithmetic correctness
    theorems take) transfers to the provisioned PPM run. -/
theorem compileToMagicPPM_provisioned_decoder_transfer (F : TFactoryContract)
    (g : Gate) (decode : (Nat → Bool) → Nat)
    (input : Nat → Bool) (expected : Nat)
    (hGateCorrect : decode (Gate.applyNat g input) = expected) :
    ∃ σ' output,
      MagicPPMProgramRel F (compileArithmeticGateToMagicPPM g)
        (encodeWithPool input (factoryProvision F (shorMagicDemand g))) σ'
      ∧ (magicBasisRefinesApplyNat F).observesBits σ' output
      ∧ decode output = expected := by
  obtain ⟨σ', hrun, hobs⟩ := compileToMagicPPM_provisioned_run_observe F g input
  exact ⟨σ', Gate.applyNat g input, hrun, hobs, hGateCorrect⟩

/-! ## §9. Magic demand = Toffoli count. -/

/-- Number of `Gate.CCX` (Toffoli) gates in a circuit. -/
def gateCCXCount : Gate → Nat
  | .I          => 0
  | .X _        => 0
  | .CX _ _     => 0
  | .CCX _ _ _  => 1
  | .seq g₁ g₂  => gateCCXCount g₁ + gateCCXCount g₂

/-- The circuit's magic demand equals its Toffoli count: the extended
    compiler issues exactly one teleported-CCX certified-T request per
    `Gate.CCX`. -/
theorem shorMagicDemand_eq_ccxCount (g : Gate) :
    shorMagicDemand g = gateCCXCount g := by
  unfold shorMagicDemand
  induction g with
  | I => rw [magicPPMRequestCount_compileArithmeticGateToMagicPPM_I]; rfl
  | X q => rw [magicPPMRequestCount_compileArithmeticGateToMagicPPM_X]; rfl
  | CX c t => rw [magicPPMRequestCount_compileArithmeticGateToMagicPPM_CX]; rfl
  | CCX a b c => rw [magicPPMRequestCount_compileArithmeticGateToMagicPPM_CCX]; rfl
  | seq g₁ g₂ ih₁ ih₂ =>
      rw [magicPPMRequestCount_compileArithmeticGateToMagicPPM_seq, ih₁, ih₂]; rfl

/-! ## §10. Status summary.

    Closed in this file:

    * `AllCertifiedT` (+ `_nil`, `_drop`).
    * `encodeWithPool` (+ `_bits` / `_magicPool` / `_failed` /
      `_observes`) — provisioned input encoder.
    * `magicBasisPPMGateRel_ICX_total` — ICX gate-relation totality.
    * `compileMagic_ICX_eq_base_map` — ICX compiler = base map.
    * `magicCompile_executable_ICX` — ICX run construction.
    * `magicCompile_executable` — **THE missing existence direction**:
      a successful run exists from a sufficiently-provisioned
      certified-T pool, with exact pool-consumption bookkeeping.
    * `compileToMagicPPM_run_observe` — executability ∧ soundness =
      total correctness at this layer.
    * `shorMagicDemand`, `certifiedTToken`, `factoryProvision`
      (+ `_length`, `_allCertified`).
    * `factoryRequestSchedule` (+ `_length`, `_all_requestMagic`) —
      the `RequestMagicState` system-call list.
    * `factoryProvisionLatency` — backend `AtomicFactorySpec` latency.
    * `factory_schedule_meets_demand` — #syscalls = #tokens = demand.
    * `TFactoryContract.ofAtomic` (+ `_wellFormed`) — PPM-layer ↔
      backend factory connection (E21 deferral).
    * `compileToMagicPPM_provisioned_run_observe` /
      `…_decoder_transfer` — provisioned total correctness, generic.
    * `gateCCXCount`, `shorMagicDemand_eq_ccxCount` — magic demand =
      Toffoli count.

    Deferred (explicit named contracts, not silent axioms):

    * The internal Clifford+T circuit realising `teleportCCXRel`.
    * Physical T-state distillation / cultivation correctness.
    * QEC / surgery / backend implementation of the factory.
    * Probabilistic success semantics (only the success branch + the
      request count are modelled here).
    * QPE / non-Clifford rotations. -/

end FormalRV.Framework.CircuitToPPMFactoryProvision
