/-
  FormalRV.System.Invariants.SystemInvariantStrengthening — strengthened
  decidable invariant bundles closing gaps documented by the system-checker
  review (namespace `FormalRV.System.SystemInvariantStrengthening`).

  `Checkers/SystemChecker.lean` documents abstraction gaps in the
  strengthened bundle `all_invariants_with_factory_ports_ok`
  (`Compile/LatticeSurgeryPPMContract.lean`), each paired with a tiny
  counterexample schedule whose acceptance is proven by `native_decide`.
  This file closes four of those gaps, as a chain of strictly-stronger
  sibling bundles (every older bundle remains available unchanged):

    1. **Operation capacity** (§1–§4): `OperationCapacityModel` +
       `operation_capacity_ok` — independent per-kind caps on
       simultaneously-active operations (e.g. at most 1 parallel `Gate2q`),
       which neither site/zone capacity nor exclusivity bounds.
    2. **Feedback-after-decode causality** (§5, review §4):
       `feedback_after_decode_ok` — every `PauliFrameUpdate cid` must be
       preceded by a completed matching `DecodeSyndrome cid`.
       → bundle `all_invariants_strict_ok` (§6).
    3. **Per-zone slot capacity** (§11): `SlotCapacityModel` +
       `slot_capacity_ok` — caps on simultaneously-active site claims per
       zone, independent of the zone's site range.
       → bundle `all_invariants_strict_with_slot_capacity_ok` (§13).
    4. **Ancilla freshness/reset lifecycle** (§14, review §6):
       `ancilla_freshness_ok` — a Free/Live/Dirty state machine enforcing
       allocate → use → measure → re-allocate, no dangling Live.
       → bundle `all_invariants_strict_with_slot_capacity_and_freshness_ok`
       (§16).

  Each repair carries FAILURE-ISOLATION theorems: the new check rejects a
  schedule the previous bundle provably accepts, and the known-good compiled
  stream (`compileSurgeryGadgetToSysCalls surgery_ppm_A`) still passes every
  bundle.

  ## Remaining review gaps (open; regression theorems preserved, see §10)

    * `target_pauli` ignored by the topology compiler (review §3);
    * routing-lane / coupler exclusivity for `Gate2q` (review §5);
    * `SiteId` / `FactoryPortId` type-level partition (review §7);
    * factory causal-supply prefix (review §8).

  ## Platform-neutral terminology

  All new identifiers use **site / physical resource /
  operation capacity / routing lane / factory port / decoder
  channel**.  No new generic identifier uses "atom".  Legacy
  fields like `total_sites`, `contains_atom`, `syscall_acts_on`
  appear only as references to pre-existing names; read them as
  site / physical-resource ids.

  No Mathlib.  No `sorry`.  No custom `axiom`.  Pure Bool / Nat.
  Decidable; `native_decide` closes all examples.
-/

import FormalRV.System.Invariants.ScheduleInvariantsExplicit
import FormalRV.System.Compile.LatticeSurgeryPPMContract
import FormalRV.System.Compile.SurgeryGadgetToSysCalls
import FormalRV.System.Checkers.SystemChecker

namespace FormalRV.System.SystemInvariantStrengthening

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv
open FormalRV.System.LatticeSurgeryPPMContract
open FormalRV.System.SurgeryGadgetToSysCalls
open FormalRV.System.SystemChecker

/-! ## §1. Operation-capacity model

    A platform-neutral declaration of per-kind operation
    capacity caps.  Independent of the site/zone capacity model
    (which bounds spatial occupancy); these bound temporal
    concurrency of operation kinds.

    Examples (qianxu hardware model):
      * `max_gate2q_active = 1`     — one CR/CZ pulse at a time
        in a globally-addressable single-laser zone;
      * `max_decode_active = 4`     — four decoder shards;
      * `max_magic_req_active = N`  — N parallel factory ports.

    Setting a field to a large value (e.g. 1000) effectively
    disables that cap. -/
structure OperationCapacityModel where
  max_gate1q_active        : Nat
  max_gate2q_active        : Nat
  max_measure_active       : Nat
  max_decode_active        : Nat
  max_feedback_active      : Nat
  max_magic_req_active     : Nat
  max_fresh_ancilla_active : Nat
  max_transit_active       : Nat
  deriving Repr, Inhabited

/-! ## §2. Active-interval semantics + kind predicates

    Half-open active intervals: a SysCall is "active at time
    `t`" iff `begin_us ≤ t < end_us`.  This matches the
    convention in `intervals_overlap`. -/

/-- A SysCall is active at time `t` (half-open
    `[begin_us, end_us)`). -/
@[inline] def syscallActiveAt (t : Nat) (sc : SysCall) : Bool :=
  decide (sc.begin_us ≤ t) && decide (t < sc.end_us)

/-- Kind predicate: matches `Gate1q`. -/
@[inline] def kindIsGate1q : SysCallKind → Bool
  | .Gate1q _ _ => true
  | _           => false

/-- Kind predicate: matches `Gate2q`. -/
@[inline] def kindIsGate2q : SysCallKind → Bool
  | .Gate2q _ _ _ => true
  | _             => false

/-- Kind predicate: matches `Measure`. -/
@[inline] def kindIsMeasure : SysCallKind → Bool
  | .Measure _ _ => true
  | _            => false

/-- Kind predicate: matches `DecodeSyndrome`. -/
@[inline] def kindIsDecode : SysCallKind → Bool
  | .DecodeSyndrome _ => true
  | _                 => false

/-- Kind predicate: matches `PauliFrameUpdate`. -/
@[inline] def kindIsFeedback : SysCallKind → Bool
  | .PauliFrameUpdate _ => true
  | _                   => false

/-- Kind predicate: matches `RequestMagicState`. -/
@[inline] def kindIsMagicReq : SysCallKind → Bool
  | .RequestMagicState _ => true
  | _                    => false

/-- Kind predicate: matches `RequestFreshAncilla`. -/
@[inline] def kindIsFreshAnc : SysCallKind → Bool
  | .RequestFreshAncilla _ => true
  | _                      => false

/-- Kind predicate: matches `TransitQubit`. -/
@[inline] def kindIsTransit : SysCallKind → Bool
  | .TransitQubit _ _ => true
  | _                 => false

/-! ## §3. Sampling strategy

    We sample at `begin_us` values: at any other time, the active
    set is a subset of the set at the most recent begin (the
    monotonic upper bound between two consecutive begins
    decreases as SysCalls end).  So sampling at begins is SOUND
    for upper-bounding concurrency.

    For schedules with `end_us` boundaries that do not coincide
    with any `begin_us`, max-concurrency is still attained at
    some begin time.  No undercounting. -/

/-- Distinct begin-times encountered in the schedule.  We don't
    dedupe — `List.all` over duplicates is still correct, just
    slower. -/
def scheduleEventTimes (sched : List SysCall) : List Nat :=
  sched.map (·.begin_us)

/-- Count SysCalls of the given kind active at time `t`. -/
def countActiveKindAt
    (predicate : SysCallKind → Bool) (t : Nat) (sched : List SysCall) : Nat :=
  (sched.filter (fun sc => syscallActiveAt t sc && predicate sc.kind)).length

/-! ## §4. The operation-capacity checker

    At every sampled time, each kind's active-count must not
    exceed its declared cap. -/

/-- **Headline operation-capacity check.**  Enforces independent
    operation-kind caps. -/
def operation_capacity_ok
    (cap : OperationCapacityModel) (sched : List SysCall) : Bool :=
  let ts := scheduleEventTimes sched
  ts.all fun t =>
    decide (countActiveKindAt kindIsGate1q t sched ≤ cap.max_gate1q_active)
    && decide (countActiveKindAt kindIsGate2q t sched ≤ cap.max_gate2q_active)
    && decide (countActiveKindAt kindIsMeasure t sched ≤ cap.max_measure_active)
    && decide (countActiveKindAt kindIsDecode t sched ≤ cap.max_decode_active)
    && decide (countActiveKindAt kindIsFeedback t sched ≤ cap.max_feedback_active)
    && decide (countActiveKindAt kindIsMagicReq t sched ≤ cap.max_magic_req_active)
    && decide (countActiveKindAt kindIsFreshAnc t sched ≤ cap.max_fresh_ancilla_active)
    && decide (countActiveKindAt kindIsTransit t sched ≤ cap.max_transit_active)

/-! ## §5. Feedback-after-decode causal ordering

    Every `PauliFrameUpdate cid` must find at least one
    `DecodeSyndrome cid` (same numeric channel id) whose
    `end_us ≤ begin_us` of the feedback.  Closes review §4. -/

/-- **Feedback-after-decode causal check.** -/
def feedback_after_decode_ok (sched : List SysCall) : Bool :=
  sched.all fun sc =>
    match sc.kind with
    | .PauliFrameUpdate cid =>
        sched.any fun sc' =>
          match sc'.kind with
          | .DecodeSyndrome rid =>
              decide (rid = cid) && decide (sc'.end_us ≤ sc.begin_us)
          | _ => false
    | _ => true

/-! ## §6. Strict invariant bundle

    Composes the existing strengthened bundle with the two new
    repairs.  Both old bundles remain available unchanged. -/

/-- **The strict bundle.**  Strictly stronger than
    `all_invariants_with_factory_ports_ok`: adds the
    operation-capacity check and the feedback-after-decode
    check. -/
def all_invariants_strict_ok
    (arch : ZonedArch)
    (cap : OperationCapacityModel)
    (sched : List SysCall)
    (t_react_us window_us max_per_window : Nat) : Bool :=
  all_invariants_with_factory_ports_ok
      arch sched t_react_us window_us max_per_window
  && operation_capacity_ok cap sched
  && feedback_after_decode_ok sched

/-! ## §7. Demo constants and operation-capacity examples -/

/-- Demo architecture — alias for the existing
    `surgery_arch` (4 zones × 100 sites = 400 sites). -/
def demo_arch : ZonedArch := surgery_arch

/-- Demo decoder-react budget. -/
def demo_t_react : Nat := 10

/-- Demo throughput window. -/
def demo_window : Nat := 1000

/-- Demo throughput cap. -/
def demo_max_per_window : Nat := 1000

/-- Demo operation cap with TIGHT `max_gate2q_active = 1` (the
    rest are slack so they don't accidentally fire).  This is
    the cap that catches the review's parallel-Gate2q gap. -/
def demo_operation_cap : OperationCapacityModel :=
  { max_gate1q_active        := 100
    max_gate2q_active        := 1
    max_measure_active       := 100
    max_decode_active        := 100
    max_feedback_active      := 100
    max_magic_req_active     := 100
    max_fresh_ancilla_active := 100
    max_transit_active       := 100 }

/-! ### §7.a Positive operation-capacity example -/

/-- Two SEQUENTIAL `Gate2q` calls on the same pair of sites.
    Each is active alone; max concurrency = 1.  Should pass
    `operation_capacity_ok` under `max_gate2q_active = 1`. -/
def operation_capacity_good_schedule : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 1 0
      begin_us := 0, end_us := 1 }
  , { kind := SysCallKind.Gate2q 2 3 0
      begin_us := 1, end_us := 2 } ]

theorem operation_capacity_good_ok :
    operation_capacity_ok demo_operation_cap
        operation_capacity_good_schedule = true := by
  native_decide

/-! ### §7.b Negative operation-capacity example -/

/-- Two PARALLEL `Gate2q` calls on ENDPOINT-DISJOINT sites.
    The old `exclusivity_ok` PASSES (atoms `[0,1]` and `[2,3]`
    are disjoint); `operation_capacity_ok` REJECTS because two
    Gate2qs are simultaneously active. -/
def operation_capacity_bad_parallel_gates : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 1 0
      begin_us := 0, end_us := 2 }
  , { kind := SysCallKind.Gate2q 2 3 0
      begin_us := 0, end_us := 2 } ]

theorem operation_capacity_bad_parallel_gates_fails :
    operation_capacity_ok demo_operation_cap
        operation_capacity_bad_parallel_gates = false := by
  native_decide

/-! ### §7.c Failure-isolation theorem (key contribution)

    The OLD bundle accepts `operation_capacity_bad_parallel_gates`;
    the NEW operation-capacity check rejects it.  This is the
    formal statement of "the strict checker catches a real gap
    in the old checker." -/

theorem operation_capacity_bad_parallel_gates_old_bundle_passes :
    all_invariants_with_factory_ports_ok
        demo_arch operation_capacity_bad_parallel_gates
        demo_t_react demo_window demo_max_per_window = true := by
  native_decide

/-! ## §8. Feedback-after-decode examples -/

/-- A schedule where `DecodeSyndrome 0` finishes at t=5 and
    `PauliFrameUpdate 0` starts at t=5.  Causal ordering
    satisfied (end ≤ begin). -/
def feedback_after_decode_good_schedule : List SysCall :=
  [ { kind := SysCallKind.DecodeSyndrome 0
      begin_us := 0, end_us := 5 }
  , { kind := SysCallKind.PauliFrameUpdate 0
      begin_us := 5, end_us := 6 } ]

theorem feedback_after_decode_good_ok :
    feedback_after_decode_ok feedback_after_decode_good_schedule = true := by
  native_decide

/-- **Review fix verified**: the review's
    `decoder_dependency_violator` (PauliFrameUpdate at t=0
    BEFORE matching DecodeSyndrome at t=10) is now REJECTED
    by `feedback_after_decode_ok`. -/
theorem decoder_dependency_violator_now_rejected :
    feedback_after_decode_ok decoder_dependency_violator = false := by
  native_decide

/-- A schedule with PauliFrameUpdate referencing a channel id
    that has NO matching DecodeSyndrome anywhere — also
    rejected. -/
def feedback_orphan_schedule : List SysCall :=
  [ { kind := SysCallKind.DecodeSyndrome 7
      begin_us := 0, end_us := 5 }
  , { kind := SysCallKind.PauliFrameUpdate 0  -- cid=0, but only rid=7 exists
      begin_us := 6, end_us := 7 } ]

theorem feedback_orphan_rejected :
    feedback_after_decode_ok feedback_orphan_schedule = false := by
  native_decide

/-! ## §9. Strict-bundle isolation theorems

    The strict bundle REJECTS the operation-capacity bad
    schedule AND the decoder-dependency violator — both of
    which the old strengthened bundle ACCEPTED. -/

theorem strict_rejects_operation_capacity_bad :
    all_invariants_strict_ok demo_arch demo_operation_cap
        operation_capacity_bad_parallel_gates
        demo_t_react demo_window demo_max_per_window = false := by
  native_decide

theorem strict_rejects_decoder_dependency_violator :
    all_invariants_strict_ok demo_arch demo_operation_cap
        decoder_dependency_violator
        demo_t_react demo_window demo_max_per_window = false := by
  native_decide

/-! ### §9.a Strict bundle still accepts a known-good schedule

    The existing `compileSurgeryGadgetToSysCalls surgery_ppm_A`
    (the topology demo's basic compiled stream, proven
    invariant-bundle-good in `SurgeryGadgetToSysCalls.lean`)
    must still pass the strict bundle.  Concretely:

      * 16 SysCalls: 3 rounds of (Request, Gate2q, Gate2q,
        Measure, DecodeSyndrome) plus 1 PauliFrameUpdate.
      * Inside each round, the two Gate2qs are sequential —
        max concurrency 1.
      * PauliFrameUpdate.correction_id = 0; DecodeSyndrome
        round_id = 0 is the first decoder and ends at t=5;
        PauliFrameUpdate fires at t=15.  Causal. -/

theorem strict_accepts_surgery_ppm_A :
    all_invariants_strict_ok demo_arch demo_operation_cap
        (compileSurgeryGadgetToSysCalls surgery_ppm_A)
        demo_t_react demo_window demo_max_per_window = true := by
  native_decide

/-! ## §10. Regression cross-references for the remaining open gaps

    The following counterexamples in `Checkers/SystemChecker.lean`
    are not closed by any bundle in this file.  Each is paired
    with the review theorem that proves its accepted-status —
    these are the regression tests a future strengthening must
    reject.

    | Gap | Review counterexample | Review theorem |
    |---|---|---|
    | target_pauli ignored | `topology_demo_target_mutated`
                          | `topology_compiler_ignores_target_pauli` |
    | routing-lane / coupler | `routing_lane_violator`
                          | `routing_lane_violator_accepted` |
    | SiteId partition | `site_id_conflation`
                          | `site_id_conflation_accepted` |
    | factory causal supply | `magic_no_startup_prefix`
                          | `magic_no_startup_prefix_accepted` |

    These acceptances hold verbatim for the larger bundles below
    as well (rerunning them with slot capacity would only require
    widening the demo `SlotCapacityModel` to cover the bad
    schedules' sites; it would not change the status).

    The ancilla-freshness gap (`freshness_use_before_reset`,
    `freshness_reuse_without_reset`) IS closed — by
    `ancilla_freshness_ok` (§14) and the freshness bundle (§16);
    the `strict_still_accepts_freshness_use_before_reset` theorem
    below remains as the isolation half: the plain strict bundle
    alone does not catch it. -/

/-- A "high-parallelism" operation cap that mirrors hardware
    with > 1 simultaneous Gate2q support.  Used to expose the
    residual routing-lane gap: with `max_gate2q_active = 10`,
    the operation-capacity check does NOT catch a routing-lane
    conflict between two parallel Gate2qs. -/
def high_parallel_operation_cap : OperationCapacityModel :=
  { max_gate1q_active        := 100
    max_gate2q_active        := 10        -- ← allows ≥ 2 parallel Gate2qs
    max_measure_active       := 100
    max_decode_active        := 100
    max_feedback_active      := 100
    max_magic_req_active     := 100
    max_fresh_ancilla_active := 100
    max_transit_active       := 100 }

/-- **Open-gap regression**: the strict bundle still accepts the
    review's `routing_lane_violator` because operation-capacity
    bounds GATE-KIND count, not coupler-lane occupancy.  Under
    `demo_operation_cap` (`max_gate2q_active = 1`), the strict
    bundle ACCIDENTALLY rejects this — not because of routing
    lanes but because of gate count — so we use
    `high_parallel_operation_cap` to keep the regression
    meaningful.  Closing this gap properly needs a routing-lane
    resource model. -/
theorem strict_still_accepts_routing_lane_violator :
    all_invariants_strict_ok demo_arch high_parallel_operation_cap
        routing_lane_violator
        demo_t_react demo_window demo_max_per_window = true := by
  native_decide

/-- **Isolation**: the plain strict bundle accepts
    `freshness_use_before_reset` — it has no lifecycle state
    machine.  The gap is closed by `ancilla_freshness_ok` (§14);
    see §16.a for the rejection by the freshness bundle. -/
theorem strict_still_accepts_freshness_use_before_reset :
    all_invariants_strict_ok demo_arch demo_operation_cap
        freshness_use_before_reset
        demo_t_react demo_window demo_max_per_window = true := by
  native_decide

/-- **Open-gap regression**: the strict bundle still accepts
    `magic_no_startup_prefix` (window throughput is aggregate,
    not causal prefix). -/
theorem strict_still_accepts_magic_no_startup_prefix :
    all_invariants_strict_ok demo_arch demo_operation_cap
        magic_no_startup_prefix
        demo_t_react demo_window 1 = true := by
  native_decide

/-! ## §11. Slot-capacity model

    The layer between "physical sites exist in a zone" and "the
    zone can sustain so-many simultaneous active site claims" —
    which neither the site-range capacity check nor the
    per-kind operation caps provide.

    ### Design choice: local `ZoneCapacitySpec` wrapper

    `ArchZone` has only a `name : String` identifier (no stable
    numeric `zone_id`), and extending it globally would touch
    every zone literal in the codebase (`ge2021_ppm_arch`,
    `surgery_arch`, `ppm_pair_arch`, every Architecture/Corpus
    demo).  So a SLOT-capacity zone is a separate local spec —
    independent of `ArchZone`, carrying its own
    `[site_lo, site_hi)` interval.  The schedule's site claims
    are matched against the SPEC's interval, not against
    `ArchZone.site_lo/site_hi`.  This decouples "where a site
    is" (`ArchZone`) from "how many active bookings a zone
    supports" (`ZoneCapacitySpec`); both models coexist without
    aliasing.

    ### Examples of finite slot capacity (platform-neutral)

      * superconducting device: limited simultaneous Gate2q
        regions (laser/microwave addressing zones);
      * trapped ions: limited per-chain operations;
      * neutral atoms: limited operation zone / AOD
        rearrangement slots;
      * qLDPC block architecture: limited ports / processing
        slots per code block. -/

/-- A slot-capacity zone spec.  Independent of `ArchZone`:
    carries its own site-interval `[site_lo, site_hi)` and a
    `slot_capacity` upper bound on the number of
    simultaneously-active site claims inside that interval.

    The `zone_id : Nat` field is the stable numeric identifier
    that `ArchZone` lacks; it is used only for documentation /
    error reporting on the spec side. -/
structure ZoneCapacitySpec where
  zone_id       : Nat
  site_lo       : Nat       -- inclusive
  site_hi       : Nat       -- exclusive (half-open)
  slot_capacity : Nat
  deriving Repr, Inhabited

/-- A slot-capacity model: a list of zone specs.  Multiple
    specs may overlap in their site intervals (e.g., a
    coarse-grained zone PLUS a finer-grained sub-zone), in
    which case all overlapping specs must pass — strictly
    cumulative semantics. -/
structure SlotCapacityModel where
  zones : List ZoneCapacitySpec
  deriving Repr, Inhabited

/-- Does the given site lie inside the spec's interval? -/
@[inline] def siteInZoneSpec (site : Nat) (z : ZoneCapacitySpec) : Bool :=
  decide (z.site_lo ≤ site) && decide (site < z.site_hi)

/-- All site occurrences claimed by syscalls active at time
    `t`.  Uses the existing `syscall_acts_on` helper from
    `CodedLayout.lean`; factory-port claims are NOT included
    here (they are handled by `factory_exclusivity_ok` in the
    old bundle).  Count is occurrence-based; under
    `exclusivity_ok` (already in the strict bundle), the count
    equals the count of distinct claimed sites. -/
def activeSitesAt (t : Nat) (sched : List SysCall) : List Nat :=
  (sched.filter (syscallActiveAt t)).flatMap syscall_acts_on

/-- Count of active site claims falling inside the spec's
    interval at time `t`. -/
def activeSiteCountInZoneAt
    (z : ZoneCapacitySpec) (t : Nat) (sched : List SysCall) : Nat :=
  (activeSitesAt t sched).filter (siteInZoneSpec · z) |>.length

/-- **Headline slot-capacity check.**  At every sampled begin
    time, every zone spec's active site-count must not exceed
    its declared `slot_capacity`. -/
def slot_capacity_ok
    (slotCap : SlotCapacityModel) (sched : List SysCall) : Bool :=
  let ts := scheduleEventTimes sched
  ts.all fun t =>
    slotCap.zones.all fun z =>
      decide (activeSiteCountInZoneAt z t sched ≤ z.slot_capacity)

/-! ## §12. Slot-capacity demo

    A two-zone architecture; the first zone has 100 sites in
    `[0, 100)` but a `slot_capacity` of only 2 (the data zone
    is a slow, narrow gate-application region).  The second
    zone is a 100-site ancilla zone with generous capacity. -/

/-- Demo architecture for the slot-capacity examples.  Two
    zones, 100 sites each.  Legacy `site_lo/site_hi` fields
    carry the site-interval bounds. -/
def slot_capacity_demo_arch : ZonedArch :=
  { zones :=
      [ { name := "Data",    site_lo := 0,   site_hi := 100 }
      , { name := "Ancilla", site_lo := 100, site_hi := 200 } ]
    total_sites := 200
    t_cycle_us  := 1
    v_max_um_per_us := 0
    t_react_us := 10 }

/-- Demo slot-capacity model.  The data zone supports only 2
    simultaneous active site claims; the ancilla zone is
    generous (100). -/
def slot_capacity_demo_model : SlotCapacityModel :=
  { zones :=
      [ { zone_id := 0, site_lo := 0,   site_hi := 100, slot_capacity := 2 }
      , { zone_id := 1, site_lo := 100, site_hi := 200, slot_capacity := 100 } ] }

/-! ### §12.a Positive example: 2 active sites in the data zone -/

/-- Two simultaneous `Gate1q`s on data sites 0 and 1.  Two
    active sites in data zone (slot_cap=2).  Passes. -/
def slot_capacity_good_schedule : List SysCall :=
  [ { kind := SysCallKind.Gate1q 0 0, begin_us := 0, end_us := 2 }
  , { kind := SysCallKind.Gate1q 1 0, begin_us := 0, end_us := 2 } ]

theorem slot_capacity_good_ok :
    slot_capacity_ok slot_capacity_demo_model
        slot_capacity_good_schedule = true := by
  native_decide

/-! ### §12.b Negative example: 3 active sites in the data zone

    Three distinct sites simultaneously in the data zone whose
    slot capacity is 2.  No aliasing, all in-range, in-budget
    per-kind. -/

/-- Three parallel `Gate1q`s on data sites 0, 1, 2.  All in
    data zone (slot_cap=2).  Fails. -/
def slot_capacity_bad_three_active_sites : List SysCall :=
  [ { kind := SysCallKind.Gate1q 0 0, begin_us := 0, end_us := 2 }
  , { kind := SysCallKind.Gate1q 1 0, begin_us := 0, end_us := 2 }
  , { kind := SysCallKind.Gate1q 2 0, begin_us := 0, end_us := 2 } ]

theorem slot_capacity_bad_three_active_sites_fails :
    slot_capacity_ok slot_capacity_demo_model
        slot_capacity_bad_three_active_sites = false := by
  native_decide

/-! ### §12.c The bad schedule passes the OLD checks

    Formal evidence that `slot_capacity_ok` catches a gap
    nothing else closes. -/

theorem slot_capacity_bad_old_capacity_passes :
    capacity_in_arch_ok slot_capacity_demo_arch
        slot_capacity_bad_three_active_sites = true := by
  native_decide

theorem slot_capacity_bad_capacity_per_cycle_passes :
    capacity_per_cycle_ok slot_capacity_demo_arch
        slot_capacity_bad_three_active_sites = true := by
  native_decide

theorem slot_capacity_bad_exclusivity_passes :
    exclusivity_ok slot_capacity_bad_three_active_sites = true := by
  native_decide

theorem slot_capacity_bad_operation_capacity_passes :
    operation_capacity_ok high_parallel_operation_cap
        slot_capacity_bad_three_active_sites = true := by
  native_decide

/-! ## §13. Strict bundle with slot capacity

    A new sibling bundle composing `all_invariants_strict_ok`
    with the slot-capacity check.  The previous strict bundle
    remains available and unchanged. -/

/-- **The strict-with-slot-capacity bundle.**  Strictly
    stronger than `all_invariants_strict_ok`: adds
    `slot_capacity_ok`. -/
def all_invariants_strict_with_slot_capacity_ok
    (arch : ZonedArch)
    (opCap : OperationCapacityModel)
    (slotCap : SlotCapacityModel)
    (sched : List SysCall)
    (t_react_us window_us max_per_window : Nat) : Bool :=
  all_invariants_strict_ok arch opCap sched
      t_react_us window_us max_per_window
  && slot_capacity_ok slotCap sched

/-! ### §13.a Failure-isolation theorems (key contribution) -/

/-- **The new bundle rejects the bad slot-capacity schedule.** -/
theorem strict_with_slot_capacity_rejects_bad_three_active_sites :
    all_invariants_strict_with_slot_capacity_ok
        slot_capacity_demo_arch
        high_parallel_operation_cap
        slot_capacity_demo_model
        slot_capacity_bad_three_active_sites
        demo_t_react demo_window demo_max_per_window = false := by
  native_decide

/-- **The PREVIOUS strict bundle ACCEPTS the bad slot-capacity
    schedule** — formal evidence that slot capacity is a
    distinct repair beyond operation capacity. -/
theorem strict_without_slot_capacity_accepts_bad_three_active_sites :
    all_invariants_strict_ok
        slot_capacity_demo_arch
        high_parallel_operation_cap
        slot_capacity_bad_three_active_sites
        demo_t_react demo_window demo_max_per_window = true := by
  native_decide

/-! ### §13.b Good schedule preservation

    The topology compiler's basic compiled stream
    (`compileSurgeryGadgetToSysCalls surgery_ppm_A`, 16
    SysCalls, already proven invariant-strict-ok in §9) must
    still pass under a GENEROUS slot-capacity model
    appropriate to `surgery_arch` (4 zones × 100 sites). -/

/-- Generous slot-capacity model matching `surgery_arch`: 100
    slots per zone, the full site interval. -/
def generous_slot_capacity_model : SlotCapacityModel :=
  { zones :=
      [ { zone_id := 0, site_lo := 0,   site_hi := 100, slot_capacity := 100 }
      , { zone_id := 1, site_lo := 100, site_hi := 200, slot_capacity := 100 }
      , { zone_id := 2, site_lo := 200, site_hi := 300, slot_capacity := 100 }
      , { zone_id := 3, site_lo := 300, site_hi := 400, slot_capacity := 100 } ] }

theorem strict_with_slot_capacity_accepts_surgery_ppm_A :
    all_invariants_strict_with_slot_capacity_ok
        surgery_arch demo_operation_cap generous_slot_capacity_model
        (compileSurgeryGadgetToSysCalls surgery_ppm_A)
        demo_t_react demo_window demo_max_per_window = true := by
  native_decide

/-! ## §14. Ancilla freshness / reset lifecycle

    Closes review §6 (freshness/reset lifecycle).  The
    existing checker has no notion that a `Gate2q` against an
    ancilla site requires a prior `RequestFreshAncilla` to
    have allocated it, nor that a site cannot be reused after
    `Measure` without a fresh allocation, nor that a schedule
    ending with a "live" ancilla represents a leaked
    resource.

    ### Explicit sites (no allocator)

    `SysCallKind.RequestFreshAncilla site` names the EXACT
    qubit being reset/allocated — qubits are never fungible in
    an executable schedule, so the earlier allocator-style
    `target_zone` form (checker picks the "next free site") is
    gone.  The `AncillaModel` now only declares WHICH site
    ranges are lifecycle-tracked; the checker validates the
    named site's lifecycle directly.

    ### Lifecycle states (platform-neutral)

      * `Free`  — site is not currently allocated as an
        ancilla resource.  Default state of any site.
      * `Live`  — `RequestFreshAncilla` has allocated this
        site; it MAY participate in subsequent `Gate2q` /
        `Measure` until measured.
      * `Dirty` — site has been measured and holds classical
        post-measurement state.  Cannot be used in
        `Gate2q`/`Measure` without a fresh allocation; CAN
        be re-allocated by another `RequestFreshAncilla`.

    ### Lifecycle rules

      * `RequestFreshAncilla site`: if `site` is tracked by
        the model, require it NOT `Live` (double allocation)
        and transition it to `Live`; untracked sites are a
        lifecycle no-op.
      * `Gate2q q1 q2 _`: for each endpoint `qi` that lies
        in some ancilla zone of the model, require lifecycle
        `Live`.  Endpoints outside any ancilla zone (data
        qubits) are not checked.  Multiple `Gate2q`s on the
        same `Live` ancilla are allowed (standard PPM
        stabilizer coupling).
      * `Measure q _`: if `q` is in an ancilla zone, require
        `Live`; transition to `Dirty`.  Measures of non-
        ancilla sites are uncheckered.
      * All other `SysCall` kinds: no lifecycle change.
      * **Final-state rule**: at end of schedule, NO site
        may be in `Live` state (dangling-live = resource
        leak).

    This is intentionally lightweight: it does not prove
    quantum-reset fidelity, decoder correctness, or
    physical-reset duration.  It enforces the SCHEDULE
    structural property that ancilla resources are
    allocated → used → measured → potentially re-allocated. -/

/-! ### §14.a Lifecycle states and model -/

/-- The three lifecycle states a tracked ancilla site can
    inhabit. -/
inductive SiteLifecycle where
  | Free
  | Live
  | Dirty
  deriving DecidableEq, Repr, Inhabited

/-- An ancilla zone spec: identifies a `target_zone` id and
    its `[site_lo, site_hi)` interval.  Independent of
    `ArchZone`/`ZoneCapacitySpec` to keep this module
    self-contained. -/
structure AncillaZoneSpec where
  zone_id : Nat
  site_lo : Nat
  site_hi : Nat
  deriving Repr, Inhabited

/-- A lifecycle model: which `target_zone`s the freshness
    checker is responsible for.  Sites outside every spec's
    range are treated as data sites and not lifecycle-tracked. -/
structure AncillaModel where
  zones : List AncillaZoneSpec
  deriving Repr, Inhabited

/-! ### §14.b State helpers

    Lifecycle state is `List (Nat × SiteLifecycle)`.  A site
    not present defaults to `Free`. -/

/-- Lookup a site's current lifecycle; defaults `Free`. -/
def lifecycleOf
    (state : List (Nat × SiteLifecycle)) (site : Nat) : SiteLifecycle :=
  match state.find? (fun p => decide (p.1 = site)) with
  | some (_, lc) => lc
  | none         => SiteLifecycle.Free

/-- Set a site's lifecycle; updates an existing entry or
    appends if absent. -/
def setLifecycle
    (state : List (Nat × SiteLifecycle))
    (site : Nat) (lc : SiteLifecycle) : List (Nat × SiteLifecycle) :=
  let filtered := state.filter (fun p => ¬ decide (p.1 = site))
  filtered ++ [(site, lc)]

/-- Is the given site inside any of the model's ancilla
    zones? -/
def siteInAncillaModel (model : AncillaModel) (site : Nat) : Bool :=
  model.zones.any fun z =>
    decide (z.site_lo ≤ site) && decide (site < z.site_hi)

/-! ### §14.c Step function and headline check -/

/-- One step of the freshness state machine.  Returns
    `some state'` on success, `none` on lifecycle violation. -/
def freshnessStep
    (model : AncillaModel)
    (state : List (Nat × SiteLifecycle)) (sc : SysCall) :
    Option (List (Nat × SiteLifecycle)) :=
  match sc.kind with
  | .RequestFreshAncilla site =>
      -- the request names its exact site: a tracked site must not
      -- currently be Live (double allocation); untracked sites are a
      -- lifecycle no-op (data-zone resets are not tracked here)
      if siteInAncillaModel model site then
        match lifecycleOf state site with
        | .Live => none
        | _     => some (setLifecycle state site SiteLifecycle.Live)
      else some state
  | .Gate2q q1 q2 _ =>
      let q1_ok :=
        if siteInAncillaModel model q1 then
          match lifecycleOf state q1 with
          | .Live => true
          | _     => false
        else true
      let q2_ok :=
        if siteInAncillaModel model q2 then
          match lifecycleOf state q2 with
          | .Live => true
          | _     => false
        else true
      if q1_ok && q2_ok then some state else none
  | .Measure q _ =>
      if siteInAncillaModel model q then
        match lifecycleOf state q with
        | .Live => some (setLifecycle state q SiteLifecycle.Dirty)
        | _     => none
      else some state                                            -- data measurement
  | _ => some state                                              -- no lifecycle effect

/-- Walk the schedule's SysCalls in list order, threading
    the lifecycle state.  Returns `none` on the first
    lifecycle violation. -/
def runFreshness
    (model : AncillaModel) (state : List (Nat × SiteLifecycle)) :
    List SysCall → Option (List (Nat × SiteLifecycle))
  | []        => some state
  | sc :: rest =>
      match freshnessStep model state sc with
      | none         => none
      | some state'  => runFreshness model state' rest

/-- Predicate: no site in the final state is `Live`
    (every allocated ancilla has been measured or never
    allocated). -/
def noDanglingLive (state : List (Nat × SiteLifecycle)) : Bool :=
  state.all fun p => match p.2 with
                     | .Live => false
                     | _     => true

/-- **Headline freshness check.**  Walks the schedule in
    list order under the given `AncillaModel`; rejects if
    any step violates the lifecycle OR if the final state
    has a dangling `Live` site.

    Note: assumes the schedule is already chronologically
    ordered by `begin_us`.  All schedules emitted by the
    framework's compilers
    (`compileSurgeryGadgetToSysCalls`,
    `compileTopologySurgeryToSysCalls`,
    `ppm_block_syscalls`) satisfy this. -/
def ancilla_freshness_ok
    (model : AncillaModel) (sched : List SysCall) : Bool :=
  match runFreshness model [] sched with
  | some finalState => noDanglingLive finalState
  | none            => false

/-! ## §15. Freshness demo

    Use the existing `surgery_arch` ancilla zone `[100, 200)`;
    the review's bad schedules and the framework's compilers
    request EXPLICIT sites in that range (e.g.
    `RequestFreshAncilla 100`). -/

/-- The demo `AncillaModel`: one tracked zone, sites
    `[100, 200)`.  Matches `surgery_arch`'s Ancilla zone; the
    compilers request their spec's explicit `ancilla_site`. -/
def demo_ancilla_model : AncillaModel :=
  { zones := [{ zone_id := 1, site_lo := 100, site_hi := 200 }] }

/-! ### §15.a Review counterexamples now rejected -/

/-- **Review fix verified**: `freshness_use_before_reset`
    (Gate2q on site 100 BEFORE any `RequestFreshAncilla`) is
    now REJECTED — the step function fails at the first
    `Gate2q` because site 100's default lifecycle is
    `Free`. -/
theorem freshness_use_before_reset_now_rejected :
    ancilla_freshness_ok demo_ancilla_model
        freshness_use_before_reset = false := by
  native_decide

/-- **Review fix verified**: `freshness_reuse_without_reset`
    (one allocation, two Gate2qs, no Measure) is now
    REJECTED by the dangling-Live rule — site 100 ends
    `Live` because no `Measure` consumed it. -/
theorem freshness_reuse_without_reset_now_rejected :
    ancilla_freshness_ok demo_ancilla_model
        freshness_reuse_without_reset = false := by
  native_decide

/-! ### §15.b Additional negative examples (post-measure reuse,
       orphan measure, double allocation) -/

/-- Reuse-after-Measure without a fresh allocation: site 100
    is measured (→ Dirty), then a Gate2q targets it again
    without `RequestFreshAncilla`.  Rejected at the second
    Gate2q. -/
def freshness_reuse_after_measure : List SysCall :=
  [ { kind := SysCallKind.RequestFreshAncilla 100, begin_us := 0, end_us := 1 }
  , { kind := SysCallKind.Gate2q 0 100 0,          begin_us := 1, end_us := 2 }
  , { kind := SysCallKind.Measure 100 0,           begin_us := 2, end_us := 3 }
  , { kind := SysCallKind.Gate2q 1 100 0,          begin_us := 3, end_us := 4 } ]

theorem freshness_reuse_after_measure_rejected :
    ancilla_freshness_ok demo_ancilla_model
        freshness_reuse_after_measure = false := by
  native_decide

/-- Orphan Measure: ancilla site 100 is measured with no
    prior `RequestFreshAncilla`.  Rejected. -/
def freshness_orphan_measure : List SysCall :=
  [ { kind := SysCallKind.Measure 100 0, begin_us := 0, end_us := 1 } ]

theorem freshness_orphan_measure_rejected :
    ancilla_freshness_ok demo_ancilla_model
        freshness_orphan_measure = false := by
  native_decide

/-- Double allocation: two `RequestFreshAncilla 100` calls on
    the SAME explicit site with no intervening Measure — the
    second request finds site 100 `Live` and is rejected
    directly (with explicit sites, no zone-exhaustion detour
    is needed). -/
def freshness_one_slot_model : AncillaModel :=
  { zones := [{ zone_id := 1, site_lo := 100, site_hi := 101 }] }    -- only site 100

def freshness_double_alloc : List SysCall :=
  [ { kind := SysCallKind.RequestFreshAncilla 100, begin_us := 0, end_us := 1 }
  , { kind := SysCallKind.RequestFreshAncilla 100, begin_us := 1, end_us := 2 } ]

theorem freshness_double_alloc_rejected :
    ancilla_freshness_ok freshness_one_slot_model
        freshness_double_alloc = false := by
  native_decide

/-! ### §15.c Positive examples -/

/-- A minimal valid PPM-shape sequence: Request site 100,
    Gate2q, Measure.  Site 100 ends `Dirty`. -/
def freshness_good_short : List SysCall :=
  [ { kind := SysCallKind.RequestFreshAncilla 100, begin_us := 0, end_us := 1 }
  , { kind := SysCallKind.Gate2q 0 100 0,          begin_us := 1, end_us := 2 }
  , { kind := SysCallKind.Measure 100 0,           begin_us := 2, end_us := 3 } ]

theorem freshness_good_short_ok :
    ancilla_freshness_ok demo_ancilla_model
        freshness_good_short = true := by
  native_decide

/-- **The simple compiler's basic PPM output stays
    accepted**: every round emits Request → Live, two
    Gate2qs (allowed, ancilla stays Live), Measure → Dirty;
    next round re-allocates the same site.  End state:
    Dirty.  No dangling Live. -/
theorem ancilla_freshness_accepts_surgery_ppm_A :
    ancilla_freshness_ok demo_ancilla_model
        (compileSurgeryGadgetToSysCalls surgery_ppm_A) = true := by
  native_decide

/-! ## §16. Strict bundle with freshness

    Composes `all_invariants_strict_with_slot_capacity_ok`
    with `ancilla_freshness_ok`.  Both prior bundles remain
    available. -/

/-- **The strict-with-slot-capacity-and-freshness bundle.**
    Strictly stronger than
    `all_invariants_strict_with_slot_capacity_ok`. -/
def all_invariants_strict_with_slot_capacity_and_freshness_ok
    (arch : ZonedArch)
    (opCap : OperationCapacityModel)
    (slotCap : SlotCapacityModel)
    (model : AncillaModel)
    (sched : List SysCall)
    (t_react_us window_us max_per_window : Nat) : Bool :=
  all_invariants_strict_with_slot_capacity_ok
      arch opCap slotCap sched t_react_us window_us max_per_window
  && ancilla_freshness_ok model sched

/-! ### §16.a Strict-with-freshness rejects review
       counterexamples -/

theorem strict_with_freshness_rejects_use_before_reset :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        demo_arch demo_operation_cap generous_slot_capacity_model
        demo_ancilla_model freshness_use_before_reset
        demo_t_react demo_window demo_max_per_window = false := by
  native_decide

theorem strict_with_freshness_rejects_reuse_without_reset :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        demo_arch demo_operation_cap generous_slot_capacity_model
        demo_ancilla_model freshness_reuse_without_reset
        demo_t_react demo_window demo_max_per_window = false := by
  native_decide

theorem strict_with_freshness_rejects_reuse_after_measure :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        demo_arch demo_operation_cap generous_slot_capacity_model
        demo_ancilla_model freshness_reuse_after_measure
        demo_t_react demo_window demo_max_per_window = false := by
  native_decide

/-! ### §16.b The previous strict-with-slot-capacity bundle
       ACCEPTS these schedules (formal isolation) -/

theorem strict_with_slot_capacity_accepts_freshness_use_before_reset :
    all_invariants_strict_with_slot_capacity_ok
        demo_arch demo_operation_cap generous_slot_capacity_model
        freshness_use_before_reset
        demo_t_react demo_window demo_max_per_window = true := by
  native_decide

theorem strict_with_slot_capacity_accepts_freshness_reuse_without_reset :
    all_invariants_strict_with_slot_capacity_ok
        demo_arch demo_operation_cap generous_slot_capacity_model
        freshness_reuse_without_reset
        demo_t_react demo_window demo_max_per_window = true := by
  native_decide

/-! ### §16.c Good compiled schedule still passes -/

theorem strict_with_freshness_accepts_surgery_ppm_A :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        surgery_arch demo_operation_cap generous_slot_capacity_model
        demo_ancilla_model
        (compileSurgeryGadgetToSysCalls surgery_ppm_A)
        demo_t_react demo_window demo_max_per_window = true := by
  native_decide

/-! ## §17. Boundary notes

    The lifecycle checker is intentionally lightweight.  It
    does NOT prove:
      * quantum-reset fidelity;
      * decoder correctness;
      * physical-reset duration;
      * cross-zone ancilla aliasing if the model overlaps
        zones (the framework treats overlapping ancilla zones
        as a model bug, not a schedule bug — fix the model).

    The review gaps that remain open across ALL bundles in
    this file are catalogued in §10, together with their
    regression theorems. -/

end FormalRV.System.SystemInvariantStrengthening
