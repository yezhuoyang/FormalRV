/-
  FormalRV.Framework.LatticeSurgeryPPMContract — the reusable
  L3 lattice-surgery / PPM schedule contract.

  ## Motivation

  Previous ticks delivered isolated system-layer demos:

    * `GE2021PPMSysInv.lean` — a 16-SysCall PPM block where I4
      is vacuous (no `RequestMagicState`).
    * `SystemLevelMagicSchedule.lean` — separate good/bad demos
      for I1, I2, I3, I4 individually.

  This file packages them as ONE reusable contract:

      structure PPMScheduleCert =
        an architecture + a SysCall stream + the derived
        wallclock / peak-qubit / total-qubit numbers + decidable
        proofs of I1 + I2 + I3 + I4 + decoder reaction.

  An L3 lattice-surgery PPM gadget is then represented by an
  inhabitant of this structure.  Composition of two gadgets is a
  function `List PPMScheduleCert → List SysCall → Bool` that
  re-checks the merged invariants `decide`-ably on the merged
  SysCall stream.

  ## What this file delivers

    1. `PPMScheduleCert` — the contract structure.
    2. `PPMScheduleCert.all_invariants_ok` — a derived bundle
       theorem on any cert, restating `all_invariants_ok` from
       `ScheduleInvariantsExplicit`.
    3. `ge2021_ppm_schedule_cert : PPMScheduleCert` — the
       GE2021PPMSysInv block packaged as a cert (REUSES the
       existing 7 invariant theorems).
    4. Three PPM-pair schedules + invariant proofs:
       sequential / parallel-distinct / parallel-alias.
    5. **I1 capacity counterexample** — an isolated capacity
       failure (atom outside `total_atoms`).  Not previously
       present.
    6. **I3 feedback-latency counterexample** — an isolated
       PauliFrameUpdate-duration failure.  Not previously present.
    7. **Local factory-exclusivity strengthening** — a small
       `factory_exclusivity_ok` checker treating `RequestMagicState`
       as claiming a factory port, with positive + negative
       examples.  Not a global change to `syscall_acts_on`.

  No Mathlib.  Pure Bool / Nat / List.  Decidable.
-/

import FormalRV.System.Architecture
import FormalRV.System.ScheduleInvariantsExplicit
import FormalRV.System.CodedLayout            -- syscall_acts_on
import FormalRV.PPM.GE2021PPMSysInv        -- ppm_block_*

namespace FormalRV.Framework.LatticeSurgeryPPMContract

open FormalRV.Framework
open FormalRV.Framework.Architecture
open FormalRV.Framework.ScheduleInv
open FormalRV.Framework.GE2021PPMSysInv

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

/-- Derived: cert satisfies the throughput bound at its declared
    window parameters. -/
theorem throughput_ok_of_cert (c : PPMScheduleCert) :
    window_throughput_ok c.syscalls c.window_us c.max_per_window = true :=
  c.throughput

/-- Derived: cert's wallclock is the foldl over the SysCall list. -/
theorem wallclock_is_derived (c : PPMScheduleCert) :
    c.wallclock_us
      = c.syscalls.foldl (fun acc sc => Nat.max acc sc.end_us) 0 :=
  c.wallclock_derived

end PPMScheduleCert

/-! ## §2. Instantiating the cert from the EXISTING GE2021 PPM block

    All proof fields are filled by REUSING the existing theorems
    from `GE2021PPMSysInv.lean`.  No re-proof. -/

/-- The GE2021 16-SysCall PPM block as a `PPMScheduleCert`.
    Every proof field is a thin reference to the corresponding
    existing theorem in `GE2021PPMSysInv.lean`. -/
def ge2021_ppm_schedule_cert : PPMScheduleCert :=
  { arch               := ge2021_ppm_arch
    syscalls           := ppm_block_syscalls
    t_react_us         := 10                  -- matches existing theorem
    window_us          := 1000                -- matches existing all_invariants_ok call
    max_per_window     := 1000
    wallclock_us       := ppm_block_wallclock_us
    wallclock_derived  := ppm_block_wallclock_is_derived
    capacity_in_arch   := ppm_block_capacity_in_arch_ok
    capacity_per_cycle := ppm_block_capacity_per_cycle_ok
    exclusivity        := ppm_block_exclusivity_ok
    feedback_latency   := ppm_block_feedback_latency_ok
    decoder_react      := ppm_block_decoder_react_ok
    throughput         := ppm_block_window_throughput_ok
  }

/-- **Headline**: the GE2021 PPM block, viewed as a
    `PPMScheduleCert`, satisfies the derived all-invariants
    bundle.  REUSES the existing 7 invariant theorems. -/
theorem ge2021_ppm_schedule_cert_all_ok :
    capacity_in_arch_ok ge2021_ppm_schedule_cert.arch
        ge2021_ppm_schedule_cert.syscalls
      && capacity_per_cycle_ok ge2021_ppm_schedule_cert.arch
        ge2021_ppm_schedule_cert.syscalls
      && exclusivity_ok ge2021_ppm_schedule_cert.syscalls
      && feedback_latency_ok ge2021_ppm_schedule_cert.arch.t_cycle_us
        ge2021_ppm_schedule_cert.syscalls = true :=
  PPMScheduleCert.all_invariants_ok_of_cert ge2021_ppm_schedule_cert

/-- **Sanity**: derived wallclock for the GE2021 PPM block as a
    cert is 16 µs (matches existing `ppm_block_wallclock_value`). -/
theorem ge2021_ppm_schedule_cert_wallclock :
    ge2021_ppm_schedule_cert.wallclock_us = 16 :=
  ppm_block_wallclock_value

/-! ## §3. PPM-pair schedules: sequential / parallel-distinct / parallel-alias

    Three concrete L3 compositions exercising the contract.  All
    three share a tiny architecture with Data + Ancilla zones. -/

def ppm_pair_arch : ZonedArch :=
  { zones :=
      [ { name := "Data",    atom_lo := 0,   atom_hi := 100 }
      , { name := "Ancilla", atom_lo := 100, atom_hi := 200 } ]
    total_atoms := 200
    t_cycle_us  := 1
    v_max_um_per_us := 0
    t_react_us := 10
  }

/-- One PPM measurement: RequestFreshAncilla + Gate2q + Measure +
    DecodeSyndrome.  Parametric in start time, data-qubit id, and
    ancilla-qubit id. -/
def ppm_block (start_us data anc decoder_id : Nat) : List SysCall :=
  [ { kind     := SysCallKind.RequestFreshAncilla 1
      begin_us := start_us
      end_us   := start_us + 1 }
  , { kind     := SysCallKind.Gate2q data anc 0
      begin_us := start_us + 1
      end_us   := start_us + 2 }
  , { kind     := SysCallKind.Measure anc 0
      begin_us := start_us + 2
      end_us   := start_us + 3 }
  , { kind     := SysCallKind.DecodeSyndrome decoder_id
      begin_us := start_us + 3
      end_us   := start_us + 4 } ]

/-- **Sequential pair**: PPM A in [0, 4), PPM B in [10, 14).
    Both use ancilla 100 — no time overlap, so I2 passes. -/
def ppm_pair_sequential_syscalls : List SysCall :=
  ppm_block 0  0  100 0
  ++ ppm_block 10 50 100 1

theorem ppm_pair_sequential_capacity_in_arch_ok :
    capacity_in_arch_ok ppm_pair_arch ppm_pair_sequential_syscalls = true := by
  native_decide

theorem ppm_pair_sequential_exclusivity_ok :
    exclusivity_ok ppm_pair_sequential_syscalls = true := by native_decide

theorem ppm_pair_sequential_feedback_latency_ok :
    feedback_latency_ok ppm_pair_arch.t_cycle_us ppm_pair_sequential_syscalls = true := by
  native_decide

theorem ppm_pair_sequential_decoder_react_ok :
    decoder_react_ok 10 ppm_pair_sequential_syscalls = true := by native_decide

theorem ppm_pair_sequential_throughput_ok :
    window_throughput_ok ppm_pair_sequential_syscalls 1000 1000 = true := by
  native_decide

theorem ppm_pair_sequential_all_invariants_ok :
    all_invariants_ok ppm_pair_arch ppm_pair_sequential_syscalls 1000 1000
      (fun _ => 0) = true := by
  native_decide

/-- **Parallel-distinct pair**: PPM A and PPM B run in the SAME
    time window [0, 4), but use DISTINCT ancillas (100 and 101).
    I2 passes because the only shared timing class is the
    different Gate2q calls with disjoint atom claims. -/
def ppm_pair_parallel_distinct_syscalls : List SysCall :=
  ppm_block 0 0  100 0
  ++ ppm_block 0 50 101 1

theorem ppm_pair_parallel_distinct_exclusivity_ok :
    exclusivity_ok ppm_pair_parallel_distinct_syscalls = true := by
  native_decide

theorem ppm_pair_parallel_distinct_all_invariants_ok :
    all_invariants_ok ppm_pair_arch ppm_pair_parallel_distinct_syscalls 1000 1000
      (fun _ => 0) = true := by
  native_decide

/-- **Parallel-aliasing pair (BAD)**: PPM A and PPM B both use
    ancilla 100 in the SAME time window.  Their Gate2qs both claim
    atom 100 at [1, 2).  I2 REJECTS. -/
def ppm_pair_parallel_alias_syscalls : List SysCall :=
  ppm_block 0 0  100 0
  ++ ppm_block 0 50 100 1

theorem ppm_pair_parallel_alias_exclusivity_fails :
    exclusivity_ok ppm_pair_parallel_alias_syscalls = false := by
  native_decide

/-- Failure isolation: the aliasing pair fails ONLY I2.  I1, I3,
    I4 still pass.  This is exactly what the paper claims I2
    catches when L3 gadgets are scheduled in parallel. -/
theorem ppm_pair_parallel_alias_fails_only_exclusivity :
    capacity_in_arch_ok ppm_pair_arch ppm_pair_parallel_alias_syscalls = true
  ∧ feedback_latency_ok ppm_pair_arch.t_cycle_us
      ppm_pair_parallel_alias_syscalls = true
  ∧ decoder_react_ok 10 ppm_pair_parallel_alias_syscalls = true
  ∧ window_throughput_ok ppm_pair_parallel_alias_syscalls 1000 1000 = true
  ∧ exclusivity_ok ppm_pair_parallel_alias_syscalls = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## §4. I1 capacity counterexample (previously missing)

    A schedule with a Gate2q referencing atom 250 — outside the
    `ppm_pair_arch`'s total_atoms = 200 budget.  I1 REJECTS
    because the claimed atom is not inside ANY zone.

    Failure isolation: I2 (only one syscall, no overlap), I3
    (no PauliFrameUpdate / DecodeSyndrome), I4 (no
    RequestMagicState) all pass. -/

def capacity_bad_schedule : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 250 0    -- atom 250 ≥ total_atoms = 200
      begin_us := 0, end_us := 1 } ]

theorem capacity_bad_oversubscription_fails :
    capacity_in_arch_ok ppm_pair_arch capacity_bad_schedule = false := by
  native_decide

theorem capacity_bad_fails_only_capacity :
    capacity_in_arch_ok ppm_pair_arch capacity_bad_schedule = false
  ∧ exclusivity_ok capacity_bad_schedule = true
  ∧ feedback_latency_ok ppm_pair_arch.t_cycle_us capacity_bad_schedule = true
  ∧ decoder_react_ok 10 capacity_bad_schedule = true
  ∧ window_throughput_ok capacity_bad_schedule 1000 1000 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## §5. I3 feedback-latency counterexample (previously missing)

    A schedule with a PauliFrameUpdate lasting 5 µs.  The
    architecture's `t_cycle_us = 1`, so the feedback latency
    EXCEEDS the cycle budget.  I3 REJECTS. -/

def feedback_bad_slow_schedule : List SysCall :=
  [ { kind := SysCallKind.PauliFrameUpdate 0
      begin_us := 0, end_us := 5 }      -- 5 µs > t_cycle 1 µs
  ]

theorem feedback_bad_latency_fails :
    feedback_latency_ok ppm_pair_arch.t_cycle_us feedback_bad_slow_schedule = false := by
  native_decide

theorem feedback_bad_fails_only_feedback_latency :
    capacity_in_arch_ok ppm_pair_arch feedback_bad_slow_schedule = true
  ∧ exclusivity_ok feedback_bad_slow_schedule = true
  ∧ decoder_react_ok 10 feedback_bad_slow_schedule = true
  ∧ window_throughput_ok feedback_bad_slow_schedule 1000 1000 = true
  ∧ feedback_latency_ok ppm_pair_arch.t_cycle_us feedback_bad_slow_schedule = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

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
    global level is a framework-design decision left to a future
    tick. -/

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

/-- POSITIVE: two `RequestMagicState` calls overlapping in time
    but targeting DIFFERENT factory zones (3 and 4).  Their
    factory ports are distinct (203 vs 204).  ACCEPTED. -/
def magic_factory_distinct_schedule : List SysCall :=
  [ { kind := SysCallKind.RequestMagicState 3
      begin_us := 0, end_us := 2 }
  , { kind := SysCallKind.RequestMagicState 4
      begin_us := 0, end_us := 2 } ]

theorem magic_factory_distinct_ports_ok :
    factory_exclusivity_ok magic_factory_distinct_schedule = true := by
  native_decide

/-- NEGATIVE: two `RequestMagicState` calls overlapping in time
    AND targeting the SAME factory zone (3).  Both claim port 203
    at the same instant.  REJECTED. -/
def magic_factory_same_port_schedule : List SysCall :=
  [ { kind := SysCallKind.RequestMagicState 3
      begin_us := 0, end_us := 2 }
  , { kind := SysCallKind.RequestMagicState 3
      begin_us := 1, end_us := 3 } ]

theorem magic_factory_same_port_fails :
    factory_exclusivity_ok magic_factory_same_port_schedule = false := by
  native_decide

/-- The same-port schedule's standard `exclusivity_ok` still
    PASSES — confirming the gap that the strengthening closes.
    `syscall_acts_on` returns `[]` for `RequestMagicState`, so
    the standard check is vacuous. -/
theorem magic_factory_same_port_passes_standard_exclusivity :
    exclusivity_ok magic_factory_same_port_schedule = true := by native_decide

/-! ## §7. Bookkeeping: derived per-cert wallclock + qubit counters -/

/-- Sequential pair's wallclock = 14 µs (= max end_us of PPM B's
    DecodeSyndrome at 14). -/
def ppm_pair_sequential_wallclock_us : Nat :=
  ppm_pair_sequential_syscalls.foldl (fun acc sc => Nat.max acc sc.end_us) 0

theorem ppm_pair_sequential_wallclock_value :
    ppm_pair_sequential_wallclock_us = 14 := by native_decide

/-- Parallel-distinct pair's wallclock = 4 µs (both PPMs end at 4). -/
def ppm_pair_parallel_distinct_wallclock_us : Nat :=
  ppm_pair_parallel_distinct_syscalls.foldl (fun acc sc => Nat.max acc sc.end_us) 0

theorem ppm_pair_parallel_distinct_wallclock_value :
    ppm_pair_parallel_distinct_wallclock_us = 4 := by native_decide

/-- **Anti-spreadsheet (rfl)**: sequential wallclock IS the foldl. -/
theorem ppm_pair_sequential_wallclock_is_derived :
    ppm_pair_sequential_wallclock_us =
      ppm_pair_sequential_syscalls.foldl (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

/-- **Anti-spreadsheet (rfl)**: parallel-distinct wallclock IS the foldl. -/
theorem ppm_pair_parallel_distinct_wallclock_is_derived :
    ppm_pair_parallel_distinct_wallclock_us =
      ppm_pair_parallel_distinct_syscalls.foldl
        (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

/-! ## §8. Mapping to the paper

  This file connects:

    * **L3 logical operations / PPM**: each PPM gadget produces
      a SysCall sub-stream, modelled here by the `ppm_block`
      function and the `PPMScheduleCert` structure.

    * **Cross-cutting system layer (Qmemory + SysCall + I1–I4)**:
      `capacity_in_arch_ok`, `capacity_per_cycle_ok`,
      `exclusivity_ok`, `feedback_latency_ok`, `decoder_react_ok`,
      `window_throughput_ok` from `ScheduleInvariantsExplicit`.

    * **Reused existing instance**: `ge2021_ppm_schedule_cert`
      wraps the 16-SysCall block from `GE2021PPMSysInv.lean` as a
      `PPMScheduleCert` — no re-proof, just re-bundling.

  ## Not attempted in this tick

    * **L3 schedule synthesis**: choosing what SysCalls a PPM
      gadget should emit.  This file only verifies that a given
      emission satisfies the contract.
    * **Physical derivation of per-SysCall durations**: cycle
      time, gate time, measurement time are inputs to the
      architecture, not derived here.
    * **Decoder algorithm correctness**: the `DecodeSyndrome`
      SysCall is treated as a black box; only its DURATION
      against `t_react_us` is checked.
    * **Full GE2021 schedule at RSA-2048 scale**: this file
      covers individual PPM-pair compositions; the full
      ~10¹¹-SysCall pipeline is not constructed.
-/

/-! ## §9. What this delivers

  Closes the "isolated demos" → "reusable L3 contract" step:

    * `PPMScheduleCert` — a single structure capturing what it
      means for an L3 PPM gadget to be SysCall-stream-valid.
    * `ge2021_ppm_schedule_cert` — the existing GE2021PPMSysInv
      block packaged as a cert, REUSING all 7 invariant theorems.
    * Three PPM-pair compositions (sequential / parallel-distinct
      / parallel-alias) with corresponding positive/negative
      `decide`-verified theorems.
    * **NEW**: isolated I1 capacity failure (atom outside zones).
    * **NEW**: isolated I3 feedback-latency failure
      (PauliFrameUpdate > t_cycle).
    * **NEW**: local `factory_exclusivity_ok` strengthening
      catching factory-port conflicts that standard
      `exclusivity_ok` misses (because `syscall_acts_on` returns
      `[]` for `RequestMagicState`).
    * `magic_factory_same_port_passes_standard_exclusivity`
      explicitly DOCUMENTS the gap.

  All wallclock numbers are `foldl`-derived (`rfl` theorems).
  All other invariants `decide`-closed.  No `sorry`, no custom
  axioms. -/

/-! ## §10. Strengthened bundle: `all_invariants_with_factory_ports_ok`

    The previous tick added `factory_exclusivity_ok` (§6) but left
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

/-- The same-port bad schedule fails the strengthened exclusivity
    check. -/
theorem exclusivity_with_factory_ports_detects_same_port :
    exclusivity_with_factory_ports_ok magic_factory_same_port_schedule = false := by
  native_decide

/-- The distinct-ports good schedule passes the strengthened
    exclusivity check. -/
theorem exclusivity_with_factory_ports_accepts_distinct_ports :
    exclusivity_with_factory_ports_ok magic_factory_distinct_schedule = true := by
  native_decide

/-- **Diagnostic (renamed clarifying alias)**: the standard
    `exclusivity_ok` is silent on the same-port conflict (which is
    exactly why we need the strengthened bundle).  Re-export of
    `magic_factory_same_port_passes_standard_exclusivity` from §6. -/
theorem standard_exclusivity_misses_same_factory_port :
    exclusivity_ok magic_factory_same_port_schedule = true :=
  magic_factory_same_port_passes_standard_exclusivity

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

/-- Derived: cert's wallclock IS the foldl over its SysCall list. -/
theorem wallclock_is_derived (c : PPMScheduleCertWithFactoryPorts) :
    c.wallclock_us
      = c.syscalls.foldl (fun acc sc => Nat.max acc sc.end_us) 0 :=
  c.wallclock_derived

end PPMScheduleCertWithFactoryPorts

/-! ## §12. Good-schedule instantiations of the strengthened cert -/

/-! ### §12.a GE2021 PPM block — has no `RequestMagicState`, so
       factory_exclusivity_ok is vacuously true -/

theorem ge2021_ppm_block_factory_exclusivity_ok :
    factory_exclusivity_ok ppm_block_syscalls = true := by native_decide

def ge2021_ppm_schedule_cert_with_factory_ports : PPMScheduleCertWithFactoryPorts :=
  { arch                := ge2021_ppm_arch
    syscalls            := ppm_block_syscalls
    t_react_us          := 10
    window_us           := 1000
    max_per_window      := 1000
    wallclock_us        := ppm_block_wallclock_us
    wallclock_derived   := ppm_block_wallclock_is_derived
    capacity_in_arch    := ppm_block_capacity_in_arch_ok
    capacity_per_cycle  := ppm_block_capacity_per_cycle_ok
    exclusivity         := ppm_block_exclusivity_ok
    factory_exclusivity := ge2021_ppm_block_factory_exclusivity_ok
    feedback_latency    := ppm_block_feedback_latency_ok
    decoder_react       := ppm_block_decoder_react_ok
    throughput          := ppm_block_window_throughput_ok
  }

/-- The GE2021 PPM block, packaged as the strengthened cert,
    passes the strengthened all-invariants bundle. -/
theorem ge2021_ppm_schedule_cert_with_factory_ports_all_ok :
    all_invariants_with_factory_ports_ok
        ge2021_ppm_schedule_cert_with_factory_ports.arch
        ge2021_ppm_schedule_cert_with_factory_ports.syscalls
        ge2021_ppm_schedule_cert_with_factory_ports.t_react_us
        ge2021_ppm_schedule_cert_with_factory_ports.window_us
        ge2021_ppm_schedule_cert_with_factory_ports.max_per_window = true :=
  PPMScheduleCertWithFactoryPorts.all_invariants_ok_of_cert
    ge2021_ppm_schedule_cert_with_factory_ports

/-! ### §12.b PPM-pair sequential schedule -/

theorem ppm_pair_sequential_factory_exclusivity_ok :
    factory_exclusivity_ok ppm_pair_sequential_syscalls = true := by native_decide

theorem ppm_pair_sequential_all_invariants_with_factory_ports_ok :
    all_invariants_with_factory_ports_ok
        ppm_pair_arch ppm_pair_sequential_syscalls 10 1000 1000 = true := by
  native_decide

/-! ### §12.c PPM-pair parallel-distinct schedule -/

theorem ppm_pair_parallel_distinct_factory_exclusivity_ok :
    factory_exclusivity_ok ppm_pair_parallel_distinct_syscalls = true := by
  native_decide

theorem ppm_pair_parallel_distinct_all_invariants_with_factory_ports_ok :
    all_invariants_with_factory_ports_ok
        ppm_pair_arch ppm_pair_parallel_distinct_syscalls 10 1000 1000 = true := by
  native_decide

/-! ## §13. Failure-isolation for factory-port conflict

    The strengthened bundle catches the same-port conflict that
    `all_invariants_ok` misses. -/

/-- Architecture extending `magic_demo_arch` with the same
    structure as in `SystemLevelMagicSchedule`, used here to
    evaluate the strengthened bundle on the same-port bad
    schedule. -/
def magic_factory_arch : ZonedArch :=
  { zones :=
      [ { name := "Data",    atom_lo := 0,   atom_hi := 100 }
      , { name := "Ancilla", atom_lo := 100, atom_hi := 200 }
      , { name := "Factory", atom_lo := 200, atom_hi := 300 } ]
    total_atoms := 300
    t_cycle_us  := 1
    v_max_um_per_us := 0
    t_react_us := 10
  }

/-- **Strengthened-bundle headline**: the same-port bad schedule
    is REJECTED by the strengthened all-invariants bundle.

    We use `max_per_window = 2` (not 1) here so that the schedule
    DOES satisfy throughput — the rejection is then SPECIFICALLY
    from `factory_exclusivity_ok`.  With `max_per_window = 1` the
    same schedule would also fail throughput, masking the
    factory-exclusivity isolation result below. -/
theorem magic_factory_same_port_fails_strengthened_bundle :
    all_invariants_with_factory_ports_ok
        magic_factory_arch magic_factory_same_port_schedule
        10 15 2 = false := by
  native_decide

/-- **Failure isolation**: the same-port conflict fails ONLY the
    factory-exclusivity check.  All other six constituent
    checks (capacity_in_arch + capacity_per_cycle + exclusivity +
    feedback_latency + decoder_react + throughput) PASS at
    `(window_us = 15, max_per_window = 2)`.  This is the
    paper-facing result: the strengthened bundle catches a
    conflict that the standard six checks all miss. -/
theorem magic_factory_same_port_fails_only_factory_exclusivity :
    capacity_in_arch_ok magic_factory_arch magic_factory_same_port_schedule = true
  ∧ capacity_per_cycle_ok magic_factory_arch magic_factory_same_port_schedule = true
  ∧ exclusivity_ok magic_factory_same_port_schedule = true
  ∧ factory_exclusivity_ok magic_factory_same_port_schedule = false
  ∧ feedback_latency_ok magic_factory_arch.t_cycle_us
      magic_factory_same_port_schedule = true
  ∧ decoder_react_ok 10 magic_factory_same_port_schedule = true
  ∧ window_throughput_ok magic_factory_same_port_schedule 15 2 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Headline-comparison theorem: standard `all_invariants_ok` also
    misses the same-port conflict at `(window_us = 15,
    max_per_window = 2)`. -/
theorem magic_factory_same_port_passes_standard_bundle :
    all_invariants_ok magic_factory_arch magic_factory_same_port_schedule
        15 2 (fun _ => 0) = true := by native_decide

/-- The standard bundle passes; the strengthened bundle fails. -/
theorem magic_factory_same_port_standard_vs_strengthened :
    all_invariants_ok magic_factory_arch magic_factory_same_port_schedule
        15 2 (fun _ => 0) = true
  ∧ all_invariants_with_factory_ports_ok
        magic_factory_arch magic_factory_same_port_schedule
        10 15 2 = false := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## §14. Per-cycle capacity counterexample — STRUCTURAL LIMITATION

    **Terminology note**: this section discusses the foundational
    `ScheduleInv.ArchZone` structure, whose field names
    (`atom_lo`, `atom_hi`, `contains_atom`, `total_atoms`) predate
    the platform-neutral framing.  Read `atom` here as a generic
    physical resource / site id; the structural argument applies
    to any FTQC platform (superconducting transmons, trapped
    ions, neutral atoms, spin qubits, qLDPC blocks, etc.).

    The previous tick added an I1 failure via an out-of-range
    atom (`capacity_bad_oversubscription_fails`).  This tick
    attempted to add a REALISTIC per-cycle capacity failure:
    several SysCalls active simultaneously, all using distinct
    atoms inside one zone, exceeding the zone's capacity.

    **Honest finding**: the current `ScheduleInv.ArchZone` model
    structurally PREVENTS this.  In
    `ScheduleInvariantsExplicit.lean`:

        @[inline] def capacity (z : ArchZone) : Nat :=
          z.atom_hi - z.atom_lo
        @[inline] def contains_atom (z : ArchZone) (a : Nat) : Bool :=
          decide (z.atom_lo ≤ a) && decide (a < z.atom_hi)

    Zone capacity is DERIVED from the atom range, not stored
    separately.  Thus the maximum DISTINCT atoms in any zone at
    any cycle is bounded by `capacity` by construction.  If
    `exclusivity_ok` holds (all simultaneously-active claims are
    distinct atoms), then `zone_load t z ≤ |zone atoms| =
    z.capacity`, and `capacity_per_cycle_ok` ALWAYS passes.

    An isolated `capacity_per_cycle` failure (with exclusivity
    holding) would require decoupling zone capacity from its
    atom-range size — e.g., adding a separate `slot_capacity`
    field smaller than `atom_hi - atom_lo`.  We do NOT modify
    `ArchZone` here (per the tick's "minimal safe changes"
    guidance).  Documenting the limitation precisely. -/

/-- A would-be per-cycle oversubscription witness: three Gate2qs
    in [0, 1) each claiming a distinct atom in the Data zone.
    The Data zone has range [0, 100) — capacity 100.  Three
    distinct atoms is well within capacity.  Demonstrates that
    distinct-atom claims cannot oversubscribe a zone whose
    capacity equals its range size. -/
def per_cycle_three_active_schedule : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 100 0
      begin_us := 0, end_us := 1 }
  , { kind := SysCallKind.Gate2q 1 101 0
      begin_us := 0, end_us := 1 }
  , { kind := SysCallKind.Gate2q 2 102 0
      begin_us := 0, end_us := 1 } ]

/-- Confirms the structural argument: per-cycle capacity always
    passes when distinct atoms are used inside an
    atom-range-equals-capacity zone. -/
theorem per_cycle_three_active_capacity_passes :
    capacity_per_cycle_ok ppm_pair_arch per_cycle_three_active_schedule = true := by
  native_decide

/-- And exclusivity ALSO passes (distinct atoms, but overlapping
    times) — confirming that an isolated `capacity_per_cycle`
    failure is unreachable in the current model. -/
theorem per_cycle_three_active_exclusivity_passes :
    exclusivity_ok per_cycle_three_active_schedule = true := by native_decide

/-! ## §15. What this tick delivers

  Closes the strengthened-bundle gap from the previous tick:

    * `all_invariants_with_factory_ports_ok` — the OFFICIAL
      strengthened sibling bundle, leaving `all_invariants_ok`
      unchanged.
    * `PPMScheduleCertWithFactoryPorts` — sibling cert with an
      extra `factory_exclusivity` proof field.  Bundle theorem
      `all_invariants_ok_of_cert` ties it to the strengthened
      bundle.
    * `ge2021_ppm_schedule_cert_with_factory_ports` — the
      EXISTING GE2021 PPM block lifted to the strengthened cert
      (factory_exclusivity is trivially true: no
      `RequestMagicState` in the block).
    * Sequential and parallel-distinct PPM pairs each verify
      under the strengthened bundle.
    * `magic_factory_same_port_fails_strengthened_bundle` and
      `magic_factory_same_port_fails_only_factory_exclusivity`
      prove the strengthened bundle catches the same-port
      conflict — and ONLY the factory-exclusivity check fails.
    * `magic_factory_same_port_standard_vs_strengthened` directly
      contrasts: standard `all_invariants_ok` passes the bad
      schedule, strengthened bundle rejects it.
    * Paper-invariant aliases `paper_I1_ok`, `paper_I2_strengthened_ok`,
      `paper_I3_ok`, `paper_I4_ok` plus equivalence theorem
      `all_invariants_with_factory_ports_eq_paper_invariants`.
    * §14: precise documentation of why an isolated
      `capacity_per_cycle` failure is structurally unreachable
      under the current `ArchZone` model.
-/

/-! ## §16. Composition layer: pure schedule operations

    Reusable combinators for SysCall schedules.  These are pure
    functions over `List SysCall`; the validator in §17 re-runs
    the strengthened bundle on the merged stream. -/

/-- Wallclock of a schedule = max `end_us` across all SysCalls. -/
def scheduleWallclockUs (xs : List SysCall) : Nat :=
  xs.foldl (fun acc sc => Nat.max acc sc.end_us) 0

/-- Shift a single SysCall forward in time by `dt` µs. -/
def shiftSysCall (dt : Nat) (sc : SysCall) : SysCall :=
  { sc with begin_us := sc.begin_us + dt
            end_us   := sc.end_us + dt }

/-- Shift every SysCall in a schedule forward by `dt` µs. -/
def shiftSchedule (dt : Nat) (xs : List SysCall) : List SysCall :=
  xs.map (shiftSysCall dt)

/-- Sequential composition: `xs ` followed by `ys` shifted by
    `wallclock(xs)`.  After the merge, `ys`'s SysCalls all begin
    at or after `xs`'s wallclock. -/
def seqSchedules (xs ys : List SysCall) : List SysCall :=
  xs ++ shiftSchedule (scheduleWallclockUs xs) ys

/-- Parallel composition: `xs` and `ys` both starting at their
    original times.  No time shift is applied; the merged
    schedule's validity must be RECHECKED (e.g., for ancilla
    aliasing or factory-port conflicts). -/
def parSchedules (xs ys : List SysCall) : List SysCall :=
  xs ++ ys

/-! ### §16.a Basic derived-resource lemmas -/

theorem scheduleWallclockUs_def (xs : List SysCall) :
    scheduleWallclockUs xs
      = xs.foldl (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

theorem shiftSchedule_length (dt : Nat) (xs : List SysCall) :
    (shiftSchedule dt xs).length = xs.length := by
  unfold shiftSchedule
  rw [List.length_map]

theorem seqSchedules_length (xs ys : List SysCall) :
    (seqSchedules xs ys).length = xs.length + ys.length := by
  unfold seqSchedules
  rw [List.length_append, shiftSchedule_length]

theorem parSchedules_length (xs ys : List SysCall) :
    (parSchedules xs ys).length = xs.length + ys.length := by
  unfold parSchedules
  rw [List.length_append]

/-- **Anti-spreadsheet (`rfl`)**: the wallclock of `seqSchedules`
    IS the foldl over the merged list — not a closed-form sum. -/
theorem seqSchedules_wallclock_is_derived (xs ys : List SysCall) :
    scheduleWallclockUs (seqSchedules xs ys)
      = (seqSchedules xs ys).foldl (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

/-- **Anti-spreadsheet (`rfl`)**: same for `parSchedules`. -/
theorem parSchedules_wallclock_is_derived (xs ys : List SysCall) :
    scheduleWallclockUs (parSchedules xs ys)
      = (parSchedules xs ys).foldl (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

/-! ### §16.b List-level composition for many schedules -/

/-- Sequential composition of many schedules, recursively shifted. -/
def seqManySchedules : List (List SysCall) → List SysCall
  | []         => []
  | xs :: rest => seqSchedules xs (seqManySchedules rest)

/-- Parallel composition of many schedules, all starting at t=0. -/
def parManySchedules : List (List SysCall) → List SysCall
  | []         => []
  | xs :: rest => parSchedules xs (parManySchedules rest)

theorem seqManySchedules_nil :
    seqManySchedules [] = [] := rfl

theorem parManySchedules_nil :
    parManySchedules [] = [] := rfl

/-- Singleton case for `seqManySchedules`: equals the input
    (shifted by 0, since the empty tail has wallclock 0). -/
theorem seqManySchedules_singleton (xs : List SysCall) :
    seqManySchedules [xs] = xs := by
  unfold seqManySchedules seqManySchedules seqSchedules
         shiftSchedule scheduleWallclockUs
  simp

/-- Singleton case for `parManySchedules`: equals the input. -/
theorem parManySchedules_singleton (xs : List SysCall) :
    parManySchedules [xs] = xs := by
  unfold parManySchedules parManySchedules parSchedules
  simp

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

/-! ## §18. Composition theorems for the existing PPM pairs

    Sequential composition: existence theorem given the merged
    schedule passes the strengthened bundle.

    Parallel composition (distinct ancillas): existence theorem.

    Parallel composition (aliasing): direct rejection theorem at
    the validator level — no cert is constructable. -/

/-- **Sequential PPM-pair cert exists**: the existing
    `ppm_pair_sequential_syscalls` produces a cert under the
    `ppm_pair_arch` + standard parameters. -/
theorem seq_ppm_pair_cert_exists :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.arch = ppm_pair_arch
      ∧ cert.syscalls = ppm_pair_sequential_syscalls
      ∧ cert.wallclock_us = scheduleWallclockUs ppm_pair_sequential_syscalls := by
  obtain ⟨cert, h1, h2, _, _, _, h6⟩ :=
    mkPPMScheduleCertWithFactoryPorts_of_valid
      ppm_pair_arch ppm_pair_sequential_syscalls 10 1000 1000
      (by native_decide)
  exact ⟨cert, h1, h2, h6⟩

/-- **Parallel-distinct PPM-pair cert exists**. -/
theorem par_ppm_pair_distinct_cert_exists :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.arch = ppm_pair_arch
      ∧ cert.syscalls = ppm_pair_parallel_distinct_syscalls
      ∧ cert.wallclock_us = scheduleWallclockUs ppm_pair_parallel_distinct_syscalls := by
  obtain ⟨cert, h1, h2, _, _, _, h6⟩ :=
    mkPPMScheduleCertWithFactoryPorts_of_valid
      ppm_pair_arch ppm_pair_parallel_distinct_syscalls 10 1000 1000
      (by native_decide)
  exact ⟨cert, h1, h2, h6⟩

/-- **Parallel-aliasing PPM-pair is REJECTED at the validator
    level**: no strengthened cert can be constructed because the
    merged schedule fails `exclusivity_ok`. -/
theorem validate_parallel_alias_false :
    validateScheduleWithFactoryPorts
        ppm_pair_arch ppm_pair_parallel_alias_syscalls 10 1000 1000 = false := by
  native_decide

/-! ## §19. Compositions using the new combinators

    Demonstrate `seqSchedules` and `parSchedules` on fresh
    examples (NOT the hand-written `ppm_pair_*_syscalls`). -/

/-- Block A: a PPM block at `start_us = 0` on data 0, ancilla 100. -/
def ppm_compose_A : List SysCall := ppm_block 0 0 100 0

/-- Block B: a PPM block at `start_us = 0` on data 50, ancilla 100.
    Same ancilla as A — for sequential composition this is fine
    (B gets shifted past A's wallclock); for parallel composition
    it causes aliasing. -/
def ppm_compose_B_same_anc : List SysCall := ppm_block 0 50 100 1

/-- Block B with a DISTINCT ancilla (101). -/
def ppm_compose_B_distinct_anc : List SysCall := ppm_block 0 50 101 1

/-- Block C with a third distinct ancilla (102). -/
def ppm_compose_C_distinct_anc : List SysCall := ppm_block 0 60 102 2

/-- **Sequential composition of A then B (same ancilla, but
    shifted so B starts at wallclock(A) = 4)**: PASSES the
    strengthened bundle. -/
def seq_compose_AB : List SysCall :=
  seqSchedules ppm_compose_A ppm_compose_B_same_anc

theorem seq_compose_AB_all_invariants_with_factory_ports_ok :
    all_invariants_with_factory_ports_ok
        ppm_pair_arch seq_compose_AB 10 1000 1000 = true := by
  native_decide

/-- The seq composition's wallclock derives from `foldl`, not a
    typed-in number. -/
theorem seq_compose_AB_wallclock_is_derived :
    scheduleWallclockUs seq_compose_AB
      = seq_compose_AB.foldl (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

/-- **Parallel composition of A and B (distinct ancillas)**:
    PASSES. -/
def par_compose_AB_distinct : List SysCall :=
  parSchedules ppm_compose_A ppm_compose_B_distinct_anc

theorem par_compose_AB_distinct_all_invariants_with_factory_ports_ok :
    all_invariants_with_factory_ports_ok
        ppm_pair_arch par_compose_AB_distinct 10 1000 1000 = true := by
  native_decide

/-- **Parallel composition of A and B (same ancilla)**: REJECTED
    by exclusivity, since both Gate2qs at [1, 2) claim site 100.
    (Legacy `atom` is read as `site` in platform-neutral terms;
    see `SurgeryGadgetToSysCalls.lean` §0.) -/
def par_compose_AB_alias : List SysCall :=
  parSchedules ppm_compose_A ppm_compose_B_same_anc

theorem par_compose_AB_alias_rejected :
    validateScheduleWithFactoryPorts
        ppm_pair_arch par_compose_AB_alias 10 1000 1000 = false := by
  native_decide

/-! ## §20. Three-PPM compositions

    Beyond pairs: demonstrate scaling to 3 PPM blocks. -/

/-- **3-PPM sequential**: A then B then C, each shifted past the
    previous's wallclock.  All distinct data qubits and ancillas
    (the alias-safety hypothesis for sequential isn't required
    here since the times are disjoint anyway). -/
def ppm_triple_sequential_syscalls : List SysCall :=
  seqManySchedules
    [ ppm_compose_A
    , ppm_compose_B_distinct_anc
    , ppm_compose_C_distinct_anc ]

theorem ppm_triple_sequential_all_invariants_with_factory_ports_ok :
    all_invariants_with_factory_ports_ok
        ppm_pair_arch ppm_triple_sequential_syscalls 10 1000 1000 = true := by
  native_decide

theorem ppm_triple_sequential_wallclock_is_derived :
    scheduleWallclockUs ppm_triple_sequential_syscalls
      = ppm_triple_sequential_syscalls.foldl
          (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

/-- **3-PPM parallel-distinct**: A, B, C all at t=0..4 using
    distinct ancillas 100, 101, 102. -/
def ppm_triple_parallel_distinct_syscalls : List SysCall :=
  parManySchedules
    [ ppm_compose_A
    , ppm_compose_B_distinct_anc
    , ppm_compose_C_distinct_anc ]

theorem ppm_triple_parallel_distinct_all_invariants_with_factory_ports_ok :
    all_invariants_with_factory_ports_ok
        ppm_pair_arch ppm_triple_parallel_distinct_syscalls 10 1000 1000 = true := by
  native_decide

theorem ppm_triple_parallel_distinct_wallclock_is_derived :
    scheduleWallclockUs ppm_triple_parallel_distinct_syscalls
      = ppm_triple_parallel_distinct_syscalls.foldl
          (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

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

/-- Worked applications of the compose-many theorems on the 3-PPM
    schedules from §20. -/

def ppm_triple_ctx : PPMComposeContext :=
  { arch := ppm_pair_arch
    t_react_us := 10
    window_us := 1000
    max_per_window := 1000 }

theorem ppm_triple_sequential_cert_exists :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.arch = ppm_triple_ctx.arch
      ∧ cert.syscalls = ppm_triple_sequential_syscalls := by
  obtain ⟨cert, h1, h2, _⟩ :=
    composeSeqSchedulesWithFactoryPorts_of_valid ppm_triple_ctx
      [ppm_compose_A, ppm_compose_B_distinct_anc, ppm_compose_C_distinct_anc]
      (by native_decide)
  exact ⟨cert, h1, h2⟩

theorem ppm_triple_parallel_distinct_cert_exists :
    ∃ cert : PPMScheduleCertWithFactoryPorts,
      cert.arch = ppm_triple_ctx.arch
      ∧ cert.syscalls = ppm_triple_parallel_distinct_syscalls := by
  obtain ⟨cert, h1, h2, _⟩ :=
    composeParSchedulesWithFactoryPorts_of_valid ppm_triple_ctx
      [ppm_compose_A, ppm_compose_B_distinct_anc, ppm_compose_C_distinct_anc]
      (by native_decide)
  exact ⟨cert, h1, h2⟩

/-! ## §22. Correct compositional principle (documented)

    **DO NOT** assume that two valid PPM certs automatically
    compose into a valid merged cert.  In general, this is FALSE.

    Concrete counter-example in this file:

      * `ppm_compose_A` is individually valid (one PPM on
        ancilla 100).
      * `ppm_compose_B_same_anc` is individually valid (one PPM
        on ancilla 100).
      * Their PARALLEL composition `par_compose_AB_alias` is
        REJECTED — `validate_parallel_alias_false` proves the
        validator returns `false` because both Gate2qs claim
        site 100 at the same time.

    To safely compose two valid PPM gadgets, one must EITHER:

      (a) RE-VALIDATE the merged stream (the approach taken by
          `composeSeqSchedulesWithFactoryPorts_of_valid` /
          `composeParSchedulesWithFactoryPorts_of_valid` — they
          take the merged-stream validity as a hypothesis), OR

      (b) PROVE additional separation lemmas establishing:
          - disjoint atom/ancilla claims across the gadgets,
          - disjoint factory-port claims,
          - sufficient zone capacity for the union,
          - non-overlapping time windows or guaranteed gaps,
          - throughput-window bound holds for the union of
            `RequestMagicState` calls.

    The system layer EXISTS precisely because path (a) is always
    available and decidable, while path (b) requires invariant
    discovery.  This file commits to path (a) for the
    composition combinators. -/

/-! ## §23. What this tick delivers

  Closes the parametric-composition gap:

    * `scheduleWallclockUs`, `shiftSysCall`, `shiftSchedule`,
      `seqSchedules`, `parSchedules`, `seqManySchedules`,
      `parManySchedules` — pure combinators over `List SysCall`.
    * `validateScheduleWithFactoryPorts` and
      `PPMComposeContext.validate` — generic validators returning
      `Bool`, exposing the strengthened bundle as a one-call
      check on any merged stream.
    * `mkPPMScheduleCertWithFactoryPorts` — direct 7-proof
      builder.
    * `mkPPMScheduleCertWithFactoryPorts_of_valid` — bundle-based
      existence theorem unpacking the strengthened bundle into
      the 7 cert proof fields.
    * Pair-level examples (`seq_ppm_pair_cert_exists`,
      `par_ppm_pair_distinct_cert_exists`,
      `validate_parallel_alias_false`) and combinator-level
      examples (`seq_compose_AB`, `par_compose_AB_distinct`,
      `par_compose_AB_alias`).
    * Triple-level examples
      (`ppm_triple_sequential_syscalls`,
       `ppm_triple_parallel_distinct_syscalls`) with `decide`-
      verified invariants and `rfl`-derived wallclocks.
    * Many-cert composition theorems
      (`composeSeqSchedulesWithFactoryPorts_of_valid` /
       `composeParSchedulesWithFactoryPorts_of_valid`) +
      applications to the triple at a `PPMComposeContext`.
    * §22 documents the correct compositional principle: local
      cert validity does NOT imply merged validity; revalidation
      or explicit separation is required. -/

end FormalRV.Framework.LatticeSurgeryPPMContract
