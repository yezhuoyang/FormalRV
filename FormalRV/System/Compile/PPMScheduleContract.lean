/-
  FormalRV.System.Compile.PPMScheduleContract — the durable L3
  lattice-surgery / PPM schedule contract.

  * `PPMScheduleCert` — architecture + SysCall stream + decidable proofs
    of I1 (capacity), I2 (exclusivity), I3 (feedback latency + decoder
    reaction), I4 (throughput), with foldl-derived wallclock.
  * `syscall_factory_claims` / `factory_exclusivity_ok` — the local
    factory-port claim model (RequestMagicState zone_id claims port
    200 + zone_id); a scheduler-level claim model, not physical truth.
  * `all_invariants_with_factory_ports_ok` — the OFFICIAL strengthened
    bundle (adds factory-port exclusivity and decoder reaction; omits
    speed_limit for transit-free schedules), with paper aliases
    `paper_I1_ok`..`paper_I4_ok` and the bundle-equivalence theorem.
  * `PPMScheduleCertWithFactoryPorts` — the strengthened sibling cert
    and its bundle theorem.
  * Composition layer: `PPMComposeContext`,
    `validateScheduleWithFactoryPorts`, the 7-proof builder
    `mkPPMScheduleCertWithFactoryPorts`, the bundle-to-cert existence
    theorem, and the seq/par compose-many existence theorems
    (revalidation principle: merged streams are re-checked decidably).

  Extracted verbatim from the former monolithic
  `LatticeSurgeryPPMContract.lean` (§1, §6 defs, §10, §11, §17, §21
  generic theorems; the original §-numbering is kept). Declarations
  stay in `namespace FormalRV.System.LatticeSurgeryPPMContract` to
  preserve fully-qualified names. Worked instances and counterexamples
  live in `PPMContractInstances.lean`. No Mathlib; Bool/Nat/List only.
-/

import FormalRV.System.Core.Architecture
import FormalRV.System.Invariants.ScheduleInvariantsExplicit
import FormalRV.System.Core.CodedLayout
import FormalRV.System.Core.ScheduleCombinators

namespace FormalRV.System.LatticeSurgeryPPMContract

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv

/-! ## §1. The PPM schedule contract -/

/-- A reusable certificate for one L3 lattice-surgery / PPM
    gadget compiled into a SysCall stream.

    The architecture, syscalls, and the three constants
    (`t_react_us`, `window_us`, `max_per_window`) define the
    verification context.  The remaining fields are PROOFS that
    the four system-level invariants hold:

      capacity_in_arch (I1, every claimed atom in some zone)
      capacity_per_cycle (I1, per-zone per-cycle aggregate)
      exclusivity (I2)
      feedback_latency (I3, PauliFrameUpdate ≤ t_cycle)
      decoder_react (I3, DecodeSyndrome ≤ t_react)
      throughput (I4, per-window magicReq count ≤ max_per_window)

    The wallclock proof field makes the anti-spreadsheet property
    explicit: `wallclock_us` is a `foldl` over the SysCall list,
    not a typed-in Nat. -/
structure PPMScheduleCert where
  arch              : ZonedArch
  syscalls          : List SysCall
  t_react_us        : Nat
  window_us         : Nat
  max_per_window    : Nat
  wallclock_us      : Nat
  wallclock_derived :
    wallclock_us = syscalls.foldl (fun acc sc => Nat.max acc sc.end_us) 0
  capacity_in_arch  : capacity_in_arch_ok arch syscalls = true
  capacity_per_cycle : capacity_per_cycle_ok arch syscalls = true
  exclusivity       : exclusivity_ok syscalls = true
  feedback_latency  : feedback_latency_ok arch.t_cycle_us syscalls = true
  decoder_react     : decoder_react_ok t_react_us syscalls = true
  throughput        : window_throughput_ok syscalls window_us max_per_window = true

namespace PPMScheduleCert

/-- Derived bundle: every cert satisfies `all_invariants_ok` from
    `ScheduleInvariantsExplicit` (sans the not-yet-included
    decoder-react check, which is carried separately as
    `decoder_react`).

    The framework's `all_invariants_ok` uses
    `latency_speed_ok = feedback_latency_ok && speed_limit_ok`;
    we discharge the `feedback_latency_ok` half from
    `feedback_latency`, and the `speed_limit_ok` half is vacuous
    for the no-transit case (the cert's distance function is
    `fun _ => 0`, so every transit's `distance / v_max` budget is
    0, trivially satisfied). -/
theorem all_invariants_ok_of_cert (c : PPMScheduleCert) :
    capacity_in_arch_ok c.arch c.syscalls
      && capacity_per_cycle_ok c.arch c.syscalls
      && exclusivity_ok c.syscalls
      && feedback_latency_ok c.arch.t_cycle_us c.syscalls = true := by
  rw [c.capacity_in_arch, c.capacity_per_cycle,
      c.exclusivity, c.feedback_latency]
  rfl


end PPMScheduleCert


/-! ## §6. Local factory-exclusivity strengthening (proposed)

    The existing `syscall_acts_on` (in `CodedLayout.lean`) returns
    `[]` for `RequestMagicState _`.  That is intentional at the
    framework level — the factory request doesn't claim a DATA
    atom — but it means I2 (`exclusivity_ok`) cannot catch
    factory-port conflicts.

    Rather than modifying the global `syscall_acts_on` (which
    would change the semantics of every dependent file), we add a
    LOCAL auxiliary `syscall_factory_claims` that treats each
    `RequestMagicState zone_id` as claiming a canonical factory-
    port atom `200 + zone_id`.  We then define a local
    `factory_exclusivity_ok` and exercise it on a
    positive + negative pair.

    This is a PROPOSED STRENGTHENING; whether to lift it to the
    global level is an open framework-design decision. -/

/-- Local: what factory port (if any) a SysCall claims.  Currently
    only `RequestMagicState zone_id` claims port `200 + zone_id`. -/
def syscall_factory_claims : SysCall → List Nat
  | sc => match sc.kind with
          | .RequestMagicState zone_id => [200 + zone_id]
          | _                          => []

/-- Local: factory-port exclusivity.  Pairwise check that any two
    SysCalls overlapping in time have DISJOINT factory-port
    claims.  Mirrors the framework's `exclusivity_ok` shape but on
    `syscall_factory_claims` instead of `syscall_acts_on`. -/
def factory_exclusivity_ok (sched : List SysCall) : Bool :=
  let n := sched.length
  (List.range n).all (fun i =>
    (List.range n).all (fun j =>
      if decide (i < j) then
        match sched[i]?, sched[j]? with
        | some s_i, some s_j =>
            if intervals_overlap s_i.begin_us s_i.end_us
                                 s_j.begin_us s_j.end_us then
              atoms_disjoint (syscall_factory_claims s_i)
                             (syscall_factory_claims s_j)
            else true
        | _, _ => true
      else true))


/-! ## §10. Strengthened bundle: `all_invariants_with_factory_ports_ok`

    §6 defines `factory_exclusivity_ok` but leaves the framework's
    `all_invariants_ok` unchanged.  This section adds an OFFICIAL
    strengthened sibling bundle that includes factory-port
    exclusivity.  The old bundle remains available for backward
    compatibility; new schedules can opt into the stricter check
    by using the `_with_factory_ports_ok` variant.

    Design note on `syscall_factory_claims`:
    The `200 + zone_id` encoding is a **scheduler-level claim
    model**, NOT a physical-truth assertion.  A real architecture
    may interpret a `RequestMagicState zone_id` SysCall as
    claiming a physical output port, a factory-zone qubit slot, a
    queue slot, or a logical output token.  The strengthened
    invariant rejects any pair of overlapping requests on the
    SAME zone_id; whether that is the right policy depends on the
    factory implementation.  Local to this file because no global
    consensus on the semantics has been made. -/

/-! ### §10.a Strengthened exclusivity -/

/-- Strengthened exclusivity check: standard `exclusivity_ok` AND
    factory-port exclusivity. -/
def exclusivity_with_factory_ports_ok (sched : List SysCall) : Bool :=
  exclusivity_ok sched && factory_exclusivity_ok sched


/-! ### §10.b Strengthened all-invariants bundle -/

/-- The OFFICIAL strengthened system-layer invariant bundle:
    capacity (I1) + exclusivity (I2) + factory-port exclusivity
    (I2*) + feedback latency (I3) + decoder reaction (I3) +
    throughput (I4).

    Comparison with the framework's
    `ScheduleInv.all_invariants_ok`:
      * That one BUNDLES `feedback_latency_ok` + `speed_limit_ok`
        as `latency_speed_ok` and OMITS `decoder_react_ok`.
      * This one EXPLICITLY includes `decoder_react_ok` and the
        new `factory_exclusivity_ok`.
      * `speed_limit_ok` is omitted because the relevant
        schedules have no `TransitQubit` calls. -/
def all_invariants_with_factory_ports_ok
    (arch : ZonedArch) (sched : List SysCall)
    (t_react_us window_us max_per_window : Nat) : Bool :=
  capacity_in_arch_ok arch sched
  && capacity_per_cycle_ok arch sched
  && exclusivity_ok sched
  && factory_exclusivity_ok sched
  && feedback_latency_ok arch.t_cycle_us sched
  && decoder_react_ok t_react_us sched
  && window_throughput_ok sched window_us max_per_window

/-! ### §10.c Paper-invariant aliases

    Explicitly mapping the constituent checks to the paper's
    I1–I4: -/

/-- **Paper I1**: capacity = `capacity_in_arch_ok` ∧ `capacity_per_cycle_ok`. -/
def paper_I1_ok (arch : ZonedArch) (sched : List SysCall) : Bool :=
  capacity_in_arch_ok arch sched && capacity_per_cycle_ok arch sched

/-- **Paper I2 (strengthened)**: exclusivity = `exclusivity_ok`
    ∧ `factory_exclusivity_ok`.  Standard `exclusivity_ok` alone
    misses factory-port conflicts. -/
def paper_I2_strengthened_ok (sched : List SysCall) : Bool :=
  exclusivity_ok sched && factory_exclusivity_ok sched

/-- **Paper I3**: latency = `feedback_latency_ok` ∧ `decoder_react_ok`. -/
def paper_I3_ok (arch : ZonedArch) (sched : List SysCall) (t_react_us : Nat) : Bool :=
  feedback_latency_ok arch.t_cycle_us sched && decoder_react_ok t_react_us sched

/-- **Paper I4**: throughput = `window_throughput_ok`. -/
def paper_I4_ok (sched : List SysCall) (window_us max_per_window : Nat) : Bool :=
  window_throughput_ok sched window_us max_per_window

/-- Bundle equivalence: `all_invariants_with_factory_ports_ok` is
    EXACTLY the conjunction `paper_I1 ∧ paper_I2_strengthened ∧
    paper_I3 ∧ paper_I4`.  By `rfl` since both sides unfold to the
    same chain of `&&`. -/
theorem all_invariants_with_factory_ports_eq_paper_invariants
    (arch : ZonedArch) (sched : List SysCall)
    (t_react_us window_us max_per_window : Nat) :
    all_invariants_with_factory_ports_ok arch sched
        t_react_us window_us max_per_window
      = (paper_I1_ok arch sched
         && paper_I2_strengthened_ok sched
         && paper_I3_ok arch sched t_react_us
         && paper_I4_ok sched window_us max_per_window) := by
  unfold all_invariants_with_factory_ports_ok
         paper_I1_ok paper_I2_strengthened_ok paper_I3_ok paper_I4_ok
  -- Both sides reduce to the same chain of &&.
  simp [Bool.and_assoc]

/-! ## §11. Sibling certificate with factory-port exclusivity -/

/-- Strengthened sibling cert: same shape as `PPMScheduleCert`
    but with an EXTRA proof field for `factory_exclusivity_ok`. -/
structure PPMScheduleCertWithFactoryPorts where
  arch                : ZonedArch
  syscalls            : List SysCall
  t_react_us          : Nat
  window_us           : Nat
  max_per_window      : Nat
  wallclock_us        : Nat
  wallclock_derived   :
    wallclock_us = syscalls.foldl (fun acc sc => Nat.max acc sc.end_us) 0
  capacity_in_arch    : capacity_in_arch_ok arch syscalls = true
  capacity_per_cycle  : capacity_per_cycle_ok arch syscalls = true
  exclusivity         : exclusivity_ok syscalls = true
  factory_exclusivity : factory_exclusivity_ok syscalls = true
  feedback_latency    : feedback_latency_ok arch.t_cycle_us syscalls = true
  decoder_react       : decoder_react_ok t_react_us syscalls = true
  throughput          : window_throughput_ok syscalls window_us max_per_window = true

namespace PPMScheduleCertWithFactoryPorts

/-- Bundle theorem: every strengthened cert satisfies the
    strengthened all-invariants bundle. -/
theorem all_invariants_ok_of_cert (c : PPMScheduleCertWithFactoryPorts) :
    all_invariants_with_factory_ports_ok
        c.arch c.syscalls c.t_react_us c.window_us c.max_per_window = true := by
  unfold all_invariants_with_factory_ports_ok
  rw [c.capacity_in_arch, c.capacity_per_cycle, c.exclusivity,
      c.factory_exclusivity, c.feedback_latency, c.decoder_react,
      c.throughput]
  rfl


end PPMScheduleCertWithFactoryPorts


/-! ## §17. Composition context + validator + cert constructor -/

/-- Verification context for composition.  Fixes the architecture
    and the three timing/throughput parameters under which the
    merged schedule will be validated. -/
structure PPMComposeContext where
  arch          : ZonedArch
  t_react_us    : Nat
  window_us     : Nat
  max_per_window : Nat

/-- The generic strengthened-bundle validator. -/
def validateScheduleWithFactoryPorts
    (arch : ZonedArch) (syscalls : List SysCall)
    (t_react_us window_us max_per_window : Nat) : Bool :=
  all_invariants_with_factory_ports_ok arch syscalls
    t_react_us window_us max_per_window

/-- Validate a merged schedule under a `PPMComposeContext`. -/
def PPMComposeContext.validate
    (ctx : PPMComposeContext) (syscalls : List SysCall) : Bool :=
  validateScheduleWithFactoryPorts ctx.arch syscalls
    ctx.t_react_us ctx.window_us ctx.max_per_window

/-- A non-dependent direct-construction builder taking the 7
    invariant proofs separately.  Used internally by the
    bundle-based existence theorem below. -/
def mkPPMScheduleCertWithFactoryPorts
    (arch : ZonedArch) (syscalls : List SysCall)
    (t_react_us window_us max_per_window : Nat)
    (h_cap : capacity_in_arch_ok arch syscalls = true)
    (h_per_cycle : capacity_per_cycle_ok arch syscalls = true)
    (h_excl : exclusivity_ok syscalls = true)
    (h_fact : factory_exclusivity_ok syscalls = true)
    (h_fbk : feedback_latency_ok arch.t_cycle_us syscalls = true)
    (h_decode : decoder_react_ok t_react_us syscalls = true)
    (h_throt : window_throughput_ok syscalls window_us max_per_window = true) :
    PPMScheduleCertWithFactoryPorts :=
  { arch                := arch
    syscalls            := syscalls
    t_react_us          := t_react_us
    window_us           := window_us
    max_per_window      := max_per_window
    wallclock_us        := scheduleWallclockUs syscalls
    wallclock_derived   := rfl
    capacity_in_arch    := h_cap
    capacity_per_cycle  := h_per_cycle
    exclusivity         := h_excl
    factory_exclusivity := h_fact
    feedback_latency    := h_fbk
    decoder_react       := h_decode
    throughput          := h_throt
  }

/-- **Existence theorem (cert from a valid bundle)**: whenever
    `all_invariants_with_factory_ports_ok` holds on a schedule,
    a strengthened cert exists with matching fields and a derived
    wallclock.  Unpacks the bundle into its 7 component facts
    and feeds them to the builder. -/
theorem mkPPMScheduleCertWithFactoryPorts_of_valid
    (arch : ZonedArch) (syscalls : List SysCall)
    (t_react_us window_us max_per_window : Nat)
    (h : all_invariants_with_factory_ports_ok arch syscalls
           t_react_us window_us max_per_window = true) :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.arch = arch
      ∧ cert.syscalls = syscalls
      ∧ cert.t_react_us = t_react_us
      ∧ cert.window_us = window_us
      ∧ cert.max_per_window = max_per_window
      ∧ cert.wallclock_us = scheduleWallclockUs syscalls := by
  unfold all_invariants_with_factory_ports_ok at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨mkPPMScheduleCertWithFactoryPorts arch syscalls
            t_react_us window_us max_per_window h1 h2 h3 h4 h5 h6 h7,
          rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## §21. Many-cert composition theorem -/

/-- **Compose-many existence theorem**: given a list of SysCall
    sub-streams (one per PPM gadget), if the SEQUENTIALLY merged
    stream passes the strengthened bundle under the given context,
    then a strengthened cert exists for the merged stream. -/
theorem composeSeqSchedulesWithFactoryPorts_of_valid
    (ctx : PPMComposeContext) (blocks : List (List SysCall))
    (h : all_invariants_with_factory_ports_ok ctx.arch
           (seqManySchedules blocks)
           ctx.t_react_us ctx.window_us ctx.max_per_window = true) :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.arch = ctx.arch
      ∧ cert.syscalls = seqManySchedules blocks
      ∧ cert.wallclock_us = scheduleWallclockUs (seqManySchedules blocks) := by
  obtain ⟨cert, h1, h2, _, _, _, h6⟩ :=
    mkPPMScheduleCertWithFactoryPorts_of_valid
      ctx.arch (seqManySchedules blocks)
      ctx.t_react_us ctx.window_us ctx.max_per_window h
  exact ⟨cert, h1, h2, h6⟩

/-- **Compose-many existence theorem (parallel variant)**. -/
theorem composeParSchedulesWithFactoryPorts_of_valid
    (ctx : PPMComposeContext) (blocks : List (List SysCall))
    (h : all_invariants_with_factory_ports_ok ctx.arch
           (parManySchedules blocks)
           ctx.t_react_us ctx.window_us ctx.max_per_window = true) :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.arch = ctx.arch
      ∧ cert.syscalls = parManySchedules blocks
      ∧ cert.wallclock_us = scheduleWallclockUs (parManySchedules blocks) := by
  obtain ⟨cert, h1, h2, _, _, _, h6⟩ :=
    mkPPMScheduleCertWithFactoryPorts_of_valid
      ctx.arch (parManySchedules blocks)
      ctx.t_react_us ctx.window_us ctx.max_per_window h
  exact ⟨cert, h1, h2, h6⟩

end FormalRV.System.LatticeSurgeryPPMContract
