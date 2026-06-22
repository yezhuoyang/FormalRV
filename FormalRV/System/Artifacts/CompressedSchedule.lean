/-
  FormalRV.System.Artifacts.CompressedSchedule — hierarchical
  schedules (`atom` / `seq` / `par` / `rep`) for scalable
  certification of full FT Shor schedules without materializing
  the entire `List SysCall`.  (Namespace
  `FormalRV.System.LayeredArtifactInterface`, shared with the
  sibling `LayeredArtifactCore.lean`.)

  * `CompressedSchedule.expand` — reference expansion semantics
    via `seqManySchedules` / `parManySchedules`.
  * `CompressedResourceSummary` + `CompressedSchedule.resource` —
    symbolic resource evaluator; `rep n body` SCALES
    `body.resource` by `n`, never expands.
  * `CompressedScheduleArtifact` / `VerifiedCompressedSchedule` +
    generic checker; external compressed certificates (Lean
    re-derives every claimed_* number).
  * `symbolic_rep_strict_ok` — O(|body|) sufficient check for an
    n-fold repeat.  The symbolic check is reps-independent BY
    DESIGN: it checks the body once; soundness for the expanded
    n-fold schedule is established separately in
    `CompressedRepeat/SymbolicRepeatSoundness.lean`.
  * Grounding theorems `symbolic_rep_ok_implies_body_ok` /
    `..._boundary_clean` plus accept/reject examples (incl. a
    rep-1000 certificate checked without expansion).
-/

import FormalRV.System.Artifacts.LayeredArtifactCore

namespace FormalRV.System.LayeredArtifactInterface

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.Framework.LDPC
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.SystemInvariantStrengthening
open FormalRV.System.AdderSystem

inductive CompressedSchedule where
  /-- A leaf: an explicit `List SysCall` block. -/
  | atom   : List SysCall      → CompressedSchedule
  /-- Sequential composition. -/
  | seq    : List CompressedSchedule → CompressedSchedule
  /-- Parallel composition. -/
  | par    : List CompressedSchedule → CompressedSchedule
  /-- Repeated composition: `repeat n body` ≈ `seq [body, …,
      body]` (n copies). -/
  | rep    : Nat → CompressedSchedule → CompressedSchedule
  deriving Inhabited

/-! ## §10.a Expansion semantics

    Expansion is the reference semantics: convert a
    `CompressedSchedule` to an explicit `List SysCall` by
    cascading the existing `seqSchedules` / `parSchedules`
    combinators.  Used only for small examples; for full FT
    Shor scale, the symbolic `resource` evaluator below
    avoids materialisation. -/

/-- Reference-semantics expansion of a `CompressedSchedule`
    into an explicit `List SysCall`.  Uses the existing
    `seqManySchedules` / `parManySchedules` combinators. -/
def CompressedSchedule.expand : CompressedSchedule → List SysCall
  | .atom xs    => xs
  | .seq blocks => seqManySchedules (blocks.map CompressedSchedule.expand)
  | .par blocks => parManySchedules (blocks.map CompressedSchedule.expand)
  | .rep n body => seqManySchedules (List.replicate n body.expand)

@[simp] theorem expand_atom (xs : List SysCall) :
    (CompressedSchedule.atom xs).expand = xs := by
  simp [CompressedSchedule.expand]

@[simp] theorem expand_seq_nil :
    (CompressedSchedule.seq []).expand = [] := by
  simp [CompressedSchedule.expand, seqManySchedules]

@[simp] theorem expand_par_nil :
    (CompressedSchedule.par []).expand = [] := by
  simp [CompressedSchedule.expand, parManySchedules]

@[simp] theorem expand_rep_zero (body : CompressedSchedule) :
    (CompressedSchedule.rep 0 body).expand = [] := by
  simp [CompressedSchedule.expand, seqManySchedules]

/-! ## §10.b Resource summary type -/

/-- Resource summary: wallclock + per-kind active counts.
    Computed symbolically from a `CompressedSchedule`
    structure (no expansion for `rep`). -/
structure CompressedResourceSummary where
  wallclock_us        : Nat
  syscall_count       : Nat
  gate2q_count        : Nat
  measure_count       : Nat
  decode_count        : Nat
  feedback_count      : Nat
  fresh_ancilla_count : Nat
  magic_req_count     : Nat
  deriving Repr, Inhabited, DecidableEq

namespace CompressedResourceSummary

/-- The all-zero summary, identity for `seqCombine` and
    `parCombine`. -/
def zero : CompressedResourceSummary :=
  { wallclock_us        := 0, syscall_count       := 0
    gate2q_count        := 0, measure_count       := 0
    decode_count        := 0, feedback_count      := 0
    fresh_ancilla_count := 0, magic_req_count     := 0 }

/-- Sequential combine: wallclocks SUM (back-to-back) and
    every per-kind count SUMS. -/
def seqCombine (a b : CompressedResourceSummary) : CompressedResourceSummary :=
  { wallclock_us        := a.wallclock_us        + b.wallclock_us
    syscall_count       := a.syscall_count       + b.syscall_count
    gate2q_count        := a.gate2q_count        + b.gate2q_count
    measure_count       := a.measure_count       + b.measure_count
    decode_count        := a.decode_count        + b.decode_count
    feedback_count      := a.feedback_count      + b.feedback_count
    fresh_ancilla_count := a.fresh_ancilla_count + b.fresh_ancilla_count
    magic_req_count     := a.magic_req_count     + b.magic_req_count }

/-- Parallel combine: wallclock = MAX (both start at t=0;
    finish at the later end); every per-kind count SUMS
    (parallel still ADDS operations). -/
def parCombine (a b : CompressedResourceSummary) : CompressedResourceSummary :=
  { wallclock_us        := Nat.max a.wallclock_us b.wallclock_us
    syscall_count       := a.syscall_count       + b.syscall_count
    gate2q_count        := a.gate2q_count        + b.gate2q_count
    measure_count       := a.measure_count       + b.measure_count
    decode_count        := a.decode_count        + b.decode_count
    feedback_count      := a.feedback_count      + b.feedback_count
    fresh_ancilla_count := a.fresh_ancilla_count + b.fresh_ancilla_count
    magic_req_count     := a.magic_req_count     + b.magic_req_count }

/-- Scale: multiply every field (wallclock + every count) by
    `n`.  Used for `rep n body`. -/
def scale (n : Nat) (r : CompressedResourceSummary) : CompressedResourceSummary :=
  { wallclock_us        := n * r.wallclock_us
    syscall_count       := n * r.syscall_count
    gate2q_count        := n * r.gate2q_count
    measure_count       := n * r.measure_count
    decode_count        := n * r.decode_count
    feedback_count      := n * r.feedback_count
    fresh_ancilla_count := n * r.fresh_ancilla_count
    magic_req_count     := n * r.magic_req_count }

end CompressedResourceSummary

/-- Explicit resource summary of a `List SysCall` — every field is THE
    canonical `Resource/SysCallCount` counter (the single-source rule:
    summaries never redefine their own walks). -/
def resourceOfSysCalls (xs : List SysCall) : CompressedResourceSummary :=
  { wallclock_us        := FormalRV.Resource.SysCallCount.wallclockUs xs
    syscall_count       := FormalRV.Resource.SysCallCount.opCountS xs
    gate2q_count        := FormalRV.Resource.SysCallCount.countGate2q xs
    measure_count       := FormalRV.Resource.SysCallCount.countMeasure xs
    decode_count        := FormalRV.Resource.SysCallCount.countDecode xs
    feedback_count      := FormalRV.Resource.SysCallCount.countFeedback xs
    fresh_ancilla_count := FormalRV.Resource.SysCallCount.countFreshAnc xs
    magic_req_count     := FormalRV.Resource.SysCallCount.countMagicReq xs }

/-! ## §10.c Symbolic resource evaluator -/

/-- Symbolic resource evaluator on `CompressedSchedule`.
    Key property: `rep n body` is evaluated by SCALING
    `body.resource` by `n` — no expansion to `n` copies. -/
def CompressedSchedule.resource : CompressedSchedule → CompressedResourceSummary
  | .atom xs    => resourceOfSysCalls xs
  | .seq blocks =>
      (blocks.map CompressedSchedule.resource).foldr
        CompressedResourceSummary.seqCombine CompressedResourceSummary.zero
  | .par blocks =>
      (blocks.map CompressedSchedule.resource).foldr
        CompressedResourceSummary.parCombine CompressedResourceSummary.zero
  | .rep n body => CompressedResourceSummary.scale n body.resource

@[simp] theorem resource_atom_def (xs : List SysCall) :
    (CompressedSchedule.atom xs).resource = resourceOfSysCalls xs := by
  simp [CompressedSchedule.resource]

@[simp] theorem resource_rep_def (n : Nat) (body : CompressedSchedule) :
    (CompressedSchedule.rep n body).resource
      = CompressedResourceSummary.scale n body.resource := by
  simp [CompressedSchedule.resource]


/-! ## §10.e Compressed-schedule artifact + verified
       certificate

    Mirrors `SysCallScheduleArtifact` /
    `VerifiedSysCallSchedule`.  `strict_ok_expanded` checks
    the strict bundle on the EXPANDED schedule — adequate
    for small examples; the scalable symbolic path for
    repeats is §10.j plus
    `CompressedRepeat/SymbolicRepeatSoundness.lean`. -/

/-- Compressed-schedule artifact. -/
structure CompressedScheduleArtifact where
  metadata : ArtifactMetadata
  schedule : CompressedSchedule
  deriving Inhabited

/-- Verified compressed-schedule certificate.  Carries the
    symbolic resource summary AND the proof that the
    expanded form passes the strict bundle. -/
structure VerifiedCompressedSchedule where
  artifact          : CompressedScheduleArtifact
  models            : SystemModels
  resources         : CompressedResourceSummary
  resources_derived : resources = artifact.schedule.resource
  strict_ok_expanded :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch models.opCap models.slotCap models.ancillaModel
        artifact.schedule.expand
        models.t_react_us models.window_us models.max_per_window = true

/-- **Generic checker for compressed schedules.**  If the
    strict bundle holds on the expanded form, the
    compressed artifact yields a verified cert with the
    symbolic resources. -/
theorem verified_compressed_schedule_of_expanded_strict_ok
    (artifact : CompressedScheduleArtifact) (models : SystemModels)
    (h : all_invariants_strict_with_slot_capacity_and_freshness_ok
            models.arch models.opCap models.slotCap models.ancillaModel
            artifact.schedule.expand
            models.t_react_us models.window_us models.max_per_window = true) :
    ∃ cert : VerifiedCompressedSchedule,
      cert.artifact = artifact
      ∧ cert.models = models
      ∧ cert.resources = artifact.schedule.resource :=
  ⟨ { artifact           := artifact
      models             := models
      resources          := artifact.schedule.resource
      resources_derived  := rfl
      strict_ok_expanded := h },
    rfl, rfl, rfl ⟩

/-! ## §10.f External compressed-schedule certificate -/

/-- External compressed-schedule certificate format.
    Producers emit a `CompressedSchedule` plus their own
    claimed resource numbers; Lean re-derives via the
    symbolic `resource` evaluator and rejects mismatches. -/
structure ExternalCompressedScheduleCertificate where
  producer              : String
  claimed_layer         : ArtifactLayer
  schedule              : CompressedSchedule
  claimed_wallclock_us  : Nat
  claimed_syscall_count : Nat
  claimed_gate2q_count  : Nat
  notes                 : String
  deriving Inhabited

/-- **External compressed checker.**  Three derived-resource
    checks (symbolic) + strict-bundle check on the expanded
    form.

    Lean accepts a compressed external cert iff this returns
    `true`.  Producers cannot lie about wallclock or
    operation counts: the `claimed_*` fields are compared
    against `schedule.resource.*`, NOT against producer
    self-reports. -/
def external_compressed_schedule_strict_ok
    (models : SystemModels) (c : ExternalCompressedScheduleCertificate) : Bool :=
  decide (c.claimed_wallclock_us  = c.schedule.resource.wallclock_us)
  && decide (c.claimed_syscall_count = c.schedule.resource.syscall_count)
  && decide (c.claimed_gate2q_count  = c.schedule.resource.gate2q_count)
  && all_invariants_strict_with_slot_capacity_and_freshness_ok
       models.arch models.opCap models.slotCap models.ancillaModel
       c.schedule.expand
       models.t_react_us models.window_us models.max_per_window

/-! ## §10.g Adder examples (atom + repeated) -/

/-- The adder skeleton wrapped as an `atom` compressed
    schedule.  Just a `List SysCall` lifted into
    `CompressedSchedule` — no symbolic structure. -/
def adder_n1_compressed_atom : CompressedSchedule :=
  CompressedSchedule.atom adder_n1_syscalls

/-- The expansion of `atom` is the original SysCalls. -/
theorem adder_n1_compressed_atom_expand :
    adder_n1_compressed_atom.expand = adder_n1_syscalls := by
  simp [adder_n1_compressed_atom]

theorem adder_n1_compressed_atom_resource_wallclock :
    adder_n1_compressed_atom.resource.wallclock_us = 48 := by native_decide

theorem adder_n1_compressed_atom_resource_syscall_count :
    adder_n1_compressed_atom.resource.syscall_count = 48 := by native_decide

theorem adder_n1_compressed_atom_resource_gate2q :
    adder_n1_compressed_atom.resource.gate2q_count = 18 := by native_decide

/-- A mock external compressed certificate.  Honest claims:
    accepted. -/
def python_generated_compressed_atom_example :
    ExternalCompressedScheduleCertificate :=
  { producer              := "python-compressed-atom-demo"
    claimed_layer         := ArtifactLayer.compressedSchedule
    schedule              := adder_n1_compressed_atom
    claimed_wallclock_us  := 48
    claimed_syscall_count := 48
    claimed_gate2q_count  := 18
    notes                 :=
      "External producer submits atom-shape compressed schedule with " ++
      "honest resource claims." }

theorem adder_n1_compressed_atom_checked :
    external_compressed_schedule_strict_ok
        adder_n1_system_models python_generated_compressed_atom_example = true := by
  native_decide

/-! ### §10.g.repeated  Repeated adder skeleton

    `rep n body` is the scalability test: the SYMBOLIC
    resource is `n × body.resource` (no expansion), while
    the strict bundle still checks the expanded form. -/

/-- Three sequential copies of the adder skeleton via
    `rep 3`. -/
def adder_n1_repeated_3 : CompressedSchedule :=
  CompressedSchedule.rep 3 adder_n1_compressed_atom

/-- Symbolic wallclock: `3 × 48 = 144` µs — derived
    WITHOUT expanding the schedule (uses
    `CompressedResourceSummary.scale`). -/
theorem adder_n1_repeated_3_resource_wallclock :
    adder_n1_repeated_3.resource.wallclock_us = 144 := by native_decide

/-- Symbolic Gate2q count: `3 × 18 = 54`. -/
theorem adder_n1_repeated_3_resource_gate2q :
    adder_n1_repeated_3.resource.gate2q_count = 54 := by native_decide

/-- Symbolic SysCall count: `3 × 48 = 144`. -/
theorem adder_n1_repeated_3_resource_syscall_count :
    adder_n1_repeated_3.resource.syscall_count = 144 := by native_decide

/-- The EXPANDED form's wallclock also equals 144 — the
    expansion of `rep 3 body` is the seqManySchedules of 3
    body copies, which the existing combinators time-shift
    correctly. -/
theorem adder_n1_repeated_3_expand_wallclock :
    scheduleWallclockUs adder_n1_repeated_3.expand = 144 := by native_decide

/-- An external compressed cert that uses `rep` symbolic
    structure.  Honest claims; accepted. -/
def python_generated_compressed_rep_example :
    ExternalCompressedScheduleCertificate :=
  { producer              := "python-compressed-rep-demo"
    claimed_layer         := ArtifactLayer.compressedSchedule
    schedule              := adder_n1_repeated_3
    claimed_wallclock_us  := 144
    claimed_syscall_count := 144
    claimed_gate2q_count  := 54
    notes                 :=
      "External producer submits a rep-shape compressed schedule with " ++
      "scaled resource claims; Lean re-derives via symbolic resource." }

theorem adder_n1_repeated_3_checked :
    external_compressed_schedule_strict_ok
        adder_n1_system_models python_generated_compressed_rep_example = true := by
  native_decide

/-! ## §10.h Bad compressed certificate examples -/

/-- A bad compressed cert with falsified wallclock claim. -/
def python_bad_compressed_wallclock_example :
    ExternalCompressedScheduleCertificate :=
  { producer              := "python-bad-compressed-wallclock-demo"
    claimed_layer         := ArtifactLayer.compressedSchedule
    schedule              := adder_n1_repeated_3
    claimed_wallclock_us  := 1                  -- ← false claim
    claimed_syscall_count := 144
    claimed_gate2q_count  := 54
    notes                 := "Falsified wallclock; Lean rejects." }

theorem python_bad_compressed_wallclock_rejected :
    external_compressed_schedule_strict_ok
        adder_n1_system_models python_bad_compressed_wallclock_example = false := by
  native_decide

/-- A bad compressed cert with falsified Gate2q count
    claim. -/
def python_bad_compressed_gate2q_example :
    ExternalCompressedScheduleCertificate :=
  { producer              := "python-bad-compressed-gate2q-demo"
    claimed_layer         := ArtifactLayer.compressedSchedule
    schedule              := adder_n1_repeated_3
    claimed_wallclock_us  := 144
    claimed_syscall_count := 144
    claimed_gate2q_count  := 1                  -- ← false claim
    notes                 := "Falsified Gate2q count; Lean rejects." }

theorem python_bad_compressed_gate2q_rejected :
    external_compressed_schedule_strict_ok
        adder_n1_system_models python_bad_compressed_gate2q_example = false := by
  native_decide

/-- A bad compressed SCHEDULE: two adder skeletons in
    parallel via `CompressedSchedule.par`.  Both blocks try
    to allocate the same ancilla zone simultaneously; the
    strict bundle rejects the expanded form (operation
    capacity exceeded under `max_gate2q_active = 1`). -/
def bad_parallel_compressed_adder_schedule : CompressedSchedule :=
  CompressedSchedule.par
    [ adder_n1_compressed_atom
    , adder_n1_compressed_atom ]

/-- An external cert for the bad parallel schedule.  We set
    `claimed_*` to whatever the symbolic resource computes —
    so that THIS test isolates the strict-bundle rejection
    (not a claim mismatch). -/
def bad_parallel_compressed_adder_example :
    ExternalCompressedScheduleCertificate :=
  { producer              := "python-bad-compressed-parallel-demo"
    claimed_layer         := ArtifactLayer.compressedSchedule
    schedule              := bad_parallel_compressed_adder_schedule
    claimed_wallclock_us  :=
      bad_parallel_compressed_adder_schedule.resource.wallclock_us
    claimed_syscall_count :=
      bad_parallel_compressed_adder_schedule.resource.syscall_count
    claimed_gate2q_count  :=
      bad_parallel_compressed_adder_schedule.resource.gate2q_count
    notes                 :=
      "Parallel composition causes operation-capacity violation on " ++
      "expanded schedule; Lean rejects via strict bundle." }

theorem bad_parallel_compressed_adder_rejected :
    external_compressed_schedule_strict_ok
        adder_n1_system_models bad_parallel_compressed_adder_example = false := by
  native_decide


/-! ## §10.j Symbolic repeat checker (the scalability repair)

    The expansion-based `strict_ok` check is NOT scalable to
    Shor-size schedules (`rep 10^6 body` would materialise
    10^6 SysCall copies).  This section adds a SUFFICIENT
    symbolic checker for the sequential-repeat case:

      If the body schedule is strict-valid AND satisfies a
      conservative boundary cleanliness condition,
      THEN `rep n body` is admissible at the resource level
      without expanding `n` copies.

    Proved here:
      * Grounding: symbolic acceptance implies body
        strict-validity (`symbolic_rep_ok_implies_body_ok`).
      * Resource scaling: `(rep n (atom body)).resource =
        scale n (resourceOfSysCalls body)`.
      * Instance-level cross-checks against the
        expansion-based checker (small `n`).

    The parametric "symbolic strict_ok ⇒ expanded strict_ok
    for arbitrary `n`" soundness theorem is proved in
    `CompressedRepeat/SymbolicRepeatSoundness.lean` (see
    §10.n). -/

/-! ### §10.j.1 Boundary cleanliness checker

    Conservative sufficient conditions for a body to repeat
    safely under `seqManySchedules (replicate n body)`:

      (i)  `0 < scheduleWallclockUs body`  — repetition
            progresses time;
      (ii) `magic_req_count body = 0`     — sidesteps
            factory-window aggregation issues at boundaries
            (relaxable once factory causal-supply is
            modelled).

    The ancilla "no dangling Live" condition is ALREADY
    enforced by `ancilla_freshness_ok` inside the strict
    bundle; the strict-bundle conjunct in
    `repeat_safe_block_ok` covers it.  Feedback-after-decode
    is similarly already covered (and is monotone under
    additional earlier DecodeSyndromes from previous
    copies). -/

/-- The conservative boundary-clean condition. -/
def repeat_boundary_clean (body : List SysCall) : Bool :=
  decide (0 < scheduleWallclockUs body)
  && decide ((body.filter (fun sc => kindIsMagicReq sc.kind)).length = 0)

/-- A repeat-safe block: body must pass the strict bundle AND
    be boundary-clean. -/
def repeat_safe_block_ok
    (models : SystemModels) (body : List SysCall) : Bool :=
  all_invariants_strict_with_slot_capacity_and_freshness_ok
      models.arch models.opCap models.slotCap models.ancillaModel
      body
      models.t_react_us models.window_us models.max_per_window
  && repeat_boundary_clean body

/-- The symbolic repeat checker.  The symbolic check is
    reps-independent BY DESIGN: it checks the body once
    (`O(|body|)`); the `_reps` argument deliberately does not
    enter the check.  Soundness for the expanded n-fold
    schedule is established separately in
    `CompressedRepeat/SymbolicRepeatSoundness.lean`. -/
def symbolic_rep_strict_ok
    (models : SystemModels) (body : List SysCall) (_reps : Nat) : Bool :=
  repeat_safe_block_ok models body

/-! ### §10.j.2 Proof-carrying repeat-safe block + cert -/

/-- Proof-carrying repeat-safe block.  Carries the body
    schedule, the system models it was certified under, the
    derived wallclock, AND the boundary-clean witness. -/
structure RepeatSafeBlock where
  body : List SysCall
  models : SystemModels
  wallclock_us : Nat
  wallclock_derived :
    wallclock_us = scheduleWallclockUs body
  wallclock_pos : 0 < wallclock_us
  body_strict_ok :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch models.opCap models.slotCap models.ancillaModel
        body
        models.t_react_us models.window_us models.max_per_window = true
  boundary_clean : Bool
  boundary_clean_ok : boundary_clean = true

/-- A symbolic-repeated certificate: a repeat-safe block,
    number of repetitions, and scaled resources.  Does NOT
    carry the expanded `List SysCall`. -/
structure RepeatedScheduleCertificate where
  block : RepeatSafeBlock
  reps : Nat
  resources : CompressedResourceSummary
  resources_derived :
    resources = CompressedResourceSummary.scale reps
        (resourceOfSysCalls block.body)

/-- Lift a `RepeatedScheduleCertificate` back into the
    canonical `CompressedSchedule` form (for serialization or
    cross-checking). -/
def RepeatedScheduleCertificate.toCompressedSchedule
    (c : RepeatedScheduleCertificate) : CompressedSchedule :=
  CompressedSchedule.rep c.reps (CompressedSchedule.atom c.block.body)

/-! ### §10.j.3 Resource soundness for repeat -/

/-- Symbolic wallclock under `rep n (atom body)` =
    `n × scheduleWallclockUs body`.  Pure simp on the
    @[simp]-tagged unfolders for `resource` plus `scale` and
    `resourceOfSysCalls`. -/
theorem repeated_schedule_resource_wallclock
    (body : List SysCall) (n : Nat) :
    (CompressedSchedule.rep n (CompressedSchedule.atom body)).resource.wallclock_us
      = n * scheduleWallclockUs body := by
  simp [CompressedResourceSummary.scale, resourceOfSysCalls]

theorem repeated_schedule_resource_syscall_count
    (body : List SysCall) (n : Nat) :
    (CompressedSchedule.rep n (CompressedSchedule.atom body)).resource.syscall_count
      = n * FormalRV.Resource.SysCallCount.opCountS body := by
  simp [CompressedResourceSummary.scale, resourceOfSysCalls]

theorem repeated_schedule_resource_gate2q
    (body : List SysCall) (n : Nat) :
    (CompressedSchedule.rep n (CompressedSchedule.atom body)).resource.gate2q_count
      = n * FormalRV.Resource.SysCallCount.countGate2q body := by
  simp [CompressedResourceSummary.scale, resourceOfSysCalls]

/-! ### §10.j.4 The grounding theorems

    Symbolic acceptance implies the body is strict-valid and
    boundary-clean.  The full "symbolic ⇒ expanded for
    arbitrary n" theorem lives in
    `CompressedRepeat/SymbolicRepeatSoundness.lean`. -/

theorem symbolic_rep_ok_implies_body_ok
    (models : SystemModels) (body : List SysCall) (n : Nat)
    (h : symbolic_rep_strict_ok models body n = true) :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        models.arch models.opCap models.slotCap models.ancillaModel
        body
        models.t_react_us models.window_us models.max_per_window = true := by
  unfold symbolic_rep_strict_ok repeat_safe_block_ok at h
  exact (Bool.and_eq_true _ _).mp h |>.1

theorem symbolic_rep_ok_implies_body_boundary_clean
    (models : SystemModels) (body : List SysCall) (n : Nat)
    (h : symbolic_rep_strict_ok models body n = true) :
    repeat_boundary_clean body = true := by
  unfold symbolic_rep_strict_ok repeat_safe_block_ok at h
  exact (Bool.and_eq_true _ _).mp h |>.2

/-! ## §10.k External symbolic-repeat certificate -/

/-- External symbolic-repeat certificate.  Producer emits a
    body, a repetition count `reps`, and claimed
    repeat-scaled resources.  Lean re-derives via the
    SYMBOLIC `resource` evaluator — never materialises
    `reps` copies. -/
structure ExternalRepeatedScheduleCertificate where
  producer              : String
  body                  : List SysCall
  reps                  : Nat
  claimed_wallclock_us  : Nat
  claimed_syscall_count : Nat
  claimed_gate2q_count  : Nat
  notes                 : String
  deriving Inhabited

/-- External symbolic-repeat checker.  Compares each
    `claimed_*` to the SYMBOLIC `resource` (no expansion) AND
    checks `symbolic_rep_strict_ok`. -/
def external_repeated_schedule_symbolic_ok
    (models : SystemModels) (c : ExternalRepeatedScheduleCertificate) : Bool :=
  let cs := CompressedSchedule.rep c.reps (CompressedSchedule.atom c.body)
  decide (c.claimed_wallclock_us  = cs.resource.wallclock_us)
  && decide (c.claimed_syscall_count = cs.resource.syscall_count)
  && decide (c.claimed_gate2q_count  = cs.resource.gate2q_count)
  && symbolic_rep_strict_ok models c.body c.reps

/-! ## §10.l Adder-block repeated examples -/

/-- The adder skeleton block passes the repeat-safe checker
    (it strict-passes and has no `RequestMagicState`). -/
theorem adder_n1_repeat_block_ok :
    repeat_safe_block_ok adder_n1_system_models adder_n1_syscalls = true := by
  native_decide

/-- The adder skeleton passes the symbolic-repeat checker
    for `reps = 3`. -/
theorem adder_n1_repeated_3_symbolic_ok :
    symbolic_rep_strict_ok adder_n1_system_models adder_n1_syscalls 3 = true := by
  native_decide

/-- **Cross-check**: the symbolic checker's acceptance for
    `reps = 3` matches the EXPANSION-based strict check.  This
    grounds the symbolic check against the existing expansion
    semantics on a concrete instance. -/
theorem adder_n1_repeated_3_expanded_strict_ok :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        adder_n1_system_models.arch
        adder_n1_system_models.opCap
        adder_n1_system_models.slotCap
        adder_n1_system_models.ancillaModel
        (CompressedSchedule.rep 3 (CompressedSchedule.atom adder_n1_syscalls)).expand
        adder_n1_system_models.t_react_us
        adder_n1_system_models.window_us
        adder_n1_system_models.max_per_window = true := by
  native_decide

/-! ## §10.m External symbolic-repeat examples -/

/-- An external symbolic-repeat cert claiming `1000`
    repetitions.  Resources scaled symbolically — no
    expansion of 1000 copies. -/
def python_repeated_adder_symbolic_example :
    ExternalRepeatedScheduleCertificate :=
  { producer              := "python-compressed-rep-1000-demo"
    body                  := adder_n1_syscalls
    reps                  := 1000
    claimed_wallclock_us  := 1000 * 48                  -- = 48_000
    claimed_syscall_count := 1000 * 48                  -- = 48_000
    claimed_gate2q_count  := 1000 * 18                  -- = 18_000
    notes                 :=
      "Compressed claim: rep 1000 × adder skeleton.  Lean does NOT " ++
      "expand 1000 copies; resources are scaled symbolically." }

/-- **The scalability headline**: Lean accepts a `rep 1000`
    certificate without materialising the 1000 SysCall copies —
    the symbolic check is reps-independent by design (it checks
    the body once); soundness for the expanded n-fold schedule
    is in `CompressedRepeat/SymbolicRepeatSoundness.lean`. -/
theorem python_repeated_adder_symbolic_example_checked :
    external_repeated_schedule_symbolic_ok
        adder_n1_system_models python_repeated_adder_symbolic_example = true := by
  native_decide

/-- Bad symbolic-repeat cert with falsified wallclock claim. -/
def python_repeated_adder_bad_wallclock_example :
    ExternalRepeatedScheduleCertificate :=
  { producer              := "python-compressed-rep-bad-wallclock-demo"
    body                  := adder_n1_syscalls
    reps                  := 1000
    claimed_wallclock_us  := 1                          -- ← false
    claimed_syscall_count := 1000 * 48
    claimed_gate2q_count  := 1000 * 18
    notes                 := "Falsified wallclock under rep 1000." }

theorem python_repeated_adder_bad_wallclock_rejected :
    external_repeated_schedule_symbolic_ok
        adder_n1_system_models python_repeated_adder_bad_wallclock_example = false := by
  native_decide

/-- A bad body: Gate2q on ancilla site 100 before any
    `RequestFreshAncilla` (the review's freshness violator
    shape).  Body fails strict bundle ⇒ repeat-safe checker
    fails ⇒ certificate rejected. -/
def python_repeated_bad_body : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 100 0, begin_us := 0, end_us := 1 } ]

/-- A symbolic-repeat cert wrapping the bad body.  The
    `claimed_*` numbers are set to the SYMBOLIC resource
    values so this test isolates the BODY-validity failure
    (not a claim mismatch). -/
def python_repeated_bad_body_example :
    ExternalRepeatedScheduleCertificate :=
  { producer              := "python-compressed-rep-bad-body-demo"
    body                  := python_repeated_bad_body
    reps                  := 5
    claimed_wallclock_us  := 5 * 1                      -- 1 µs body × 5
    claimed_syscall_count := 5 * 1
    claimed_gate2q_count  := 5 * 1
    notes                 :=
      "Body violates strict bundle (Gate2q on Free ancilla); rep 5 rejected." }

theorem python_repeated_bad_body_rejected :
    external_repeated_schedule_symbolic_ok
        adder_n1_system_models python_repeated_bad_body_example = false := by
  native_decide

/-! ## §10.n Parametric soundness (proved downstream)

    The symbolic repeat checker is a SUFFICIENT condition; the
    parametric theorem

      symbolic_rep_strict_ok models body n = true
      (+ `scheduleWithinWallclock body` for the pairwise /
         capacity conjuncts)
      →
      strict bundle on `(rep n (atom body)).expand`

    is proved in `CompressedRepeat/SymbolicRepeatSoundness.lean`
    (`symbolic_rep_implies_expanded_block_strict_ok` and the
    self-contained certificate form
    `hardware_generic_repeated_block_strict_soundness`), built
    on per-invariant shift / append / repeat lemmas in
    `CompressedRepeat/ShiftInvariance.lean`,
    `FeedbackAfterDecode.lean`, `FreshnessSoundness.lean`,
    `ExclusivitySeq.lean`, `CapacitySeq.lean`, and
    `InvariantChains.lean`.  The `window_throughput_ok`
    conjunct rides on `magic_req_count body = 0` from
    `repeat_boundary_clean`. -/

end FormalRV.System.LayeredArtifactInterface
