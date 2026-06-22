/-
  FormalRV.System.Compile.PPMContractInstances — worked instances and
  decide-verified positive/negative examples for the PPM schedule
  contract in `PPMScheduleContract.lean`:

  * The GE2021 16-SysCall PPM block packaged as `PPMScheduleCert` and
    as the strengthened cert (reusing the existing GE2021PPMSysInv
    theorems, no re-proof).
  * `ppm_block` and the PPM-pair / 3-PPM schedules (sequential,
    parallel-distinct, parallel-alias) with invariant proofs and
    failure-isolation theorems.
  * Isolated counterexamples: I1 capacity (atom outside zones), I3
    feedback latency (PauliFrameUpdate > t_cycle), and the factory-port
    conflict that standard `exclusivity_ok` misses but the strengthened
    bundle catches (`magic_factory_*`).
  * §14: documented structural limitation — an isolated
    `capacity_per_cycle` failure is unreachable while zone capacity is
    derived from the atom range.
  * §22: the compositional principle — two individually valid certs do
    NOT auto-compose; merged streams must be revalidated
    (`validate_parallel_alias_false` is the counterexample).

  Extracted verbatim from the former monolithic
  `LatticeSurgeryPPMContract.lean` (§2–§5, §6 examples, §7, §8,
  §12–§14, §18–§20, §21 applications, §22; the original §-numbering is
  kept). Declarations stay in
  `namespace FormalRV.System.LatticeSurgeryPPMContract` to preserve
  fully-qualified names. All invariants decide/native_decide-closed;
  wallclocks foldl-derived. No sorry, no custom axioms.
-/

import FormalRV.System.Compile.PPMScheduleContract
import FormalRV.System.Invariants.ScheduleInvariantsExplicit
import FormalRV.PPM.GE2021PPMSysInv

namespace FormalRV.System.LatticeSurgeryPPMContract

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.Framework.GE2021PPMSysInv

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
      [ { name := "Data",    site_lo := 0,   site_hi := 100 }
      , { name := "Ancilla", site_lo := 100, site_hi := 200 } ]
    total_sites := 200
    t_cycle_us  := 1
    v_max_um_per_us := 0
    t_react_us := 10
  }

/-- One PPM measurement: RequestFreshAncilla + Gate2q + Measure +
    DecodeSyndrome.  Parametric in start time, data-qubit id, and
    ancilla-qubit id. -/
def ppm_block (start_us data anc decoder_id : Nat) : List SysCall :=
  [ { kind     := SysCallKind.RequestFreshAncilla anc
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

/-! ## §4. I1 capacity counterexample

    A schedule with a Gate2q referencing atom 250 — outside the
    `ppm_pair_arch`'s total_sites = 200 budget.  I1 REJECTS
    because the claimed atom is not inside ANY zone.

    Failure isolation: I2 (only one syscall, no overlap), I3
    (no PauliFrameUpdate / DecodeSyndrome), I4 (no
    RequestMagicState) all pass. -/

def capacity_bad_schedule : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 250 0    -- atom 250 ≥ total_sites = 200
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

/-! ## §5. I3 feedback-latency counterexample

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

  ## Out of scope here

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
      [ { name := "Data",    site_lo := 0,   site_hi := 100 }
      , { name := "Ancilla", site_lo := 100, site_hi := 200 }
      , { name := "Factory", site_lo := 200, site_hi := 300 } ]
    total_sites := 300
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
    (`site_lo`, `site_hi`, `contains_atom`, `total_sites`) predate
    the platform-neutral framing.  Read `atom` here as a generic
    physical resource / site id; the structural argument applies
    to any FTQC platform (superconducting transmons, trapped
    ions, neutral atoms, spin qubits, qLDPC blocks, etc.).

    §4 gives an I1 failure via an out-of-range atom
    (`capacity_bad_oversubscription_fails`).  One might expect a
    REALISTIC per-cycle capacity failure to also be constructible:
    several SysCalls active simultaneously, all using distinct
    atoms inside one zone, exceeding the zone's capacity.

    **Honest finding**: the current `ScheduleInv.ArchZone` model
    structurally PREVENTS this.  In
    `ScheduleInvariantsExplicit.lean`:

        @[inline] def capacity (z : ArchZone) : Nat :=
          z.site_hi - z.site_lo
        @[inline] def contains_atom (z : ArchZone) (a : Nat) : Bool :=
          decide (z.site_lo ≤ a) && decide (a < z.site_hi)

    Zone capacity is DERIVED from the atom range, not stored
    separately.  Thus the maximum DISTINCT atoms in any zone at
    any cycle is bounded by `capacity` by construction.  If
    `exclusivity_ok` holds (all simultaneously-active claims are
    distinct atoms), then `zone_load t z ≤ |zone atoms| =
    z.capacity`, and `capacity_per_cycle_ok` ALWAYS passes.

    An isolated `capacity_per_cycle` failure (with exclusivity
    holding) would require decoupling zone capacity from its
    atom-range size — e.g., adding a separate `slot_capacity`
    field smaller than `site_hi - site_lo`.  We do NOT modify
    `ArchZone` here; this section documents the limitation
    precisely. -/

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

end FormalRV.System.LatticeSurgeryPPMContract
