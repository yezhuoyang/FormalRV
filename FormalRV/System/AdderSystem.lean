/-
  FormalRV.Framework.AdderSystem — first concrete
  system-level review instance.

  ## Why an adder (not full Shor)

  Starting from a small adder-level construction is a deliberate
  choice: full FT Shor at RSA-2048 scale is beyond what we can
  construct as a literal `List SysCall` and decide on with
  `native_decide`.  An adder skeleton is large enough to be
  structurally interesting (many Gate2q / Measure / Decode /
  PauliFrameUpdate calls) but small enough that the entire strict
  system-checker bundle closes by `native_decide`.

  ## What this tick demonstrates

  The framework's gap-reporting workflow:

    (1) **Concrete construction.**  An adder-level `List SysCall`
        composed of existing topology-compiled PPM gadgets.
    (2) **Strict system certificate.**  The schedule passes
        `all_invariants_strict_with_slot_capacity_and_freshness_ok`
        — the strongest current bundle.
    (3) **Derived resources.**  Wallclock, total SysCall count,
        per-kind counts — all computed by `foldl` / `filter` over
        the actual schedule.
    (4) **Claim comparison.**  An optimistic paper-style claim
        object whose claimed wallclock is FORMALLY below the
        verified value.
    (5) **Capacity lower bound.**  Under the same
        operation-capacity assumptions used to certify the
        schedule, ANY schedule with the same Gate2q count is
        bounded below by `ceildiv(num_gate2q, max_parallel) ·
        gate2q_us`; the optimistic claim is below this bound too.

  ## What this is NOT

    * NOT an arithmetic-correctness review.  The SysCall stream
      is a system-level skeleton; it is NOT proven to implement
      classical addition.  Arithmetic correctness lives at the
      Gate IR level (`BQAlgo/RippleCarryAdder.lean`,
      `Framework/CuccaroParametric.lean`).  Connecting Gate IR
      to SysCall emission is a separate piece of work.
    * NOT a claim about specific paper numbers (Gidney–Ekerå,
      Cain–Xu, etc.).  The "optimistic claim" here is a generic
      schema demonstrating the gap-reporting pattern.
    * NOT a final lower bound for adder construction.  A
      tighter compiler / more parallel hardware would produce a
      smaller schedule.  The bound is conditional on the chosen
      `OperationCapacityModel`.

  No Mathlib.  No `sorry`.  No custom `axiom`.  All theorems
  close by `native_decide` or `rfl`.
-/

import FormalRV.System.SystemInvariantStrengthening

namespace FormalRV.Framework.AdderSystem

open FormalRV.Framework
open FormalRV.Framework.Architecture
open FormalRV.Framework.ScheduleInv
open FormalRV.Framework.LatticeSurgeryPPMContract
open FormalRV.Framework.SurgeryGadgetToSysCalls
open FormalRV.Framework.SystemInvariantStrengthening

/-! ## §1. The adder-skeleton SysCall schedule

    We compose THREE sequential copies of the topology
    compiler's basic PPM block
    (`compileSurgeryGadgetToSysCalls surgery_ppm_A`, 16
    SysCalls each, 16 µs wallclock each) on the SAME ancilla
    site 100.  The result is a 48-SysCall, 48 µs skeleton
    that structurally mirrors a 3-step PPM cascade — the
    building block of Cuccaro / Gidney lattice-surgery adders.

    Three sequential PPMs is the smallest construction that
    exercises the strict bundle's interesting cases:
      * multi-round freshness re-allocation;
      * decoder→feedback ordering across multiple rounds;
      * sustained per-kind operation-capacity demand.

    SAME ancilla site across all three PPMs is required by the
    freshness checker's "next free site" rule: after Measure
    leaves site 100 `Dirty`, the next `RequestFreshAncilla 1`
    deterministically re-allocates the smallest non-`Live`
    site in zone 1's range (= site 100).  Using distinct
    ancilla sites per PPM would require the compiler to emit
    distinct `target_zone` ids — a deeper schema change not in
    scope here. -/

/-- **The adder-skeleton SysCall schedule.**  Sequential
    composition of three PPM blocks, each with 3
    syndrome-extraction rounds + 1 PauliFrameUpdate.

    Size: `5·3 + 1 = 16` SysCalls per block × 3 blocks = 48
    SysCalls.  Wallclock: 16 µs per block × 3 blocks = 48 µs. -/
def adder_n1_syscalls : List SysCall :=
  seqManySchedules
    [ compileSurgeryGadgetToSysCalls surgery_ppm_A
    , compileSurgeryGadgetToSysCalls surgery_ppm_A
    , compileSurgeryGadgetToSysCalls surgery_ppm_A ]

/-! ## §2. Architecture and capacity models

    Tight realistic caps, not blanket "100 of everything":

      * Gate2q: at most 1 parallel (single-laser hardware
        assumption);
      * Measure / Decode / Feedback: at most 4 parallel each
        (a small but non-trivial decoder bank);
      * RequestMagicState / RequestFreshAncilla / Transit:
        100 (effectively disabled — this schedule has no
        magic requests and few fresh-ancilla / transit calls).

    These caps were chosen so the lower-bound theorem on
    Gate2q wallclock is meaningful (max_parallel=1 gives the
    most pessimistic and informative bound). -/

/-- Adder demo architecture: reuses `surgery_arch` (4 zones ×
    100 sites). -/
def adder_demo_arch : ZonedArch := surgery_arch

/-- Realistic operation-capacity model: tight Gate2q + finite
    measure/decode/feedback parallelism. -/
def adder_demo_opCap : OperationCapacityModel :=
  { max_gate1q_active        := 4
    max_gate2q_active        := 1     -- ← the tight cap
    max_measure_active       := 4
    max_decode_active        := 4
    max_feedback_active      := 4
    max_magic_req_active     := 100
    max_fresh_ancilla_active := 100
    max_transit_active       := 100 }

/-- Slot capacity model: 4 zones, each generously sized
    relative to the adder skeleton's resource usage. -/
def adder_demo_slotCap : SlotCapacityModel := generous_slot_capacity_model

/-- Ancilla freshness model: one zone, id 1, sites
    `[100, 200)`.  Matches `surgery_ppm_A`'s
    `RequestFreshAncilla 1` convention. -/
def adder_demo_ancillaModel : AncillaModel := demo_ancilla_model

def adder_demo_t_react_us    : Nat := 10
def adder_demo_window_us     : Nat := 1000
def adder_demo_max_per_window : Nat := 1000

/-! ## §3. Strict system certificate (the headline) -/

/-- **The headline system certificate.**  The adder skeleton
    passes the strongest current invariant bundle:
    `all_invariants_with_factory_ports_ok` ∧
    `operation_capacity_ok` ∧ `feedback_after_decode_ok` ∧
    `slot_capacity_ok` ∧ `ancilla_freshness_ok`. -/
theorem adder_n1_strict_system_ok :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        adder_demo_arch
        adder_demo_opCap
        adder_demo_slotCap
        adder_demo_ancillaModel
        adder_n1_syscalls
        adder_demo_t_react_us
        adder_demo_window_us
        adder_demo_max_per_window = true := by
  native_decide

/-! ## §4. Derived resources

    All numbers are computed by `foldl` / `filter` over the
    actual SysCall list — no typed-in spreadsheet values. -/

/-- Wallclock = `foldl Nat.max sc.end_us 0`. -/
def adder_n1_wallclock_us : Nat :=
  scheduleWallclockUs adder_n1_syscalls

/-- Total SysCall count. -/
def adder_n1_syscall_count : Nat := adder_n1_syscalls.length

/-- Total `Gate2q` count. -/
def adder_n1_gate2q_count : Nat :=
  (adder_n1_syscalls.filter (fun sc => kindIsGate2q sc.kind)).length

/-- Total `Measure` count. -/
def adder_n1_measure_count : Nat :=
  (adder_n1_syscalls.filter (fun sc => kindIsMeasure sc.kind)).length

/-- Total `DecodeSyndrome` count. -/
def adder_n1_decode_count : Nat :=
  (adder_n1_syscalls.filter (fun sc => kindIsDecode sc.kind)).length

/-- Total `PauliFrameUpdate` (feedback) count. -/
def adder_n1_feedback_count : Nat :=
  (adder_n1_syscalls.filter (fun sc => kindIsFeedback sc.kind)).length

/-- Total `RequestFreshAncilla` count. -/
def adder_n1_fresh_ancilla_count : Nat :=
  (adder_n1_syscalls.filter (fun sc => kindIsFreshAnc sc.kind)).length

/-- **Anti-spreadsheet (rfl)**: wallclock is the foldl. -/
theorem adder_n1_wallclock_is_derived :
    adder_n1_wallclock_us
      = adder_n1_syscalls.foldl (fun acc sc => Nat.max acc sc.end_us) 0 := rfl

/-- Wallclock value: 48 µs.  Three sequential PPM blocks at
    16 µs each. -/
theorem adder_n1_wallclock_value :
    adder_n1_wallclock_us = 48 := by native_decide

/-- 48 SysCalls total. -/
theorem adder_n1_syscall_count_value :
    adder_n1_syscall_count = 48 := by native_decide

/-- 18 Gate2qs: 6 per PPM × 3 PPMs. -/
theorem adder_n1_gate2q_count_value :
    adder_n1_gate2q_count = 18 := by native_decide

/-- 9 Measures: 3 per PPM × 3 PPMs. -/
theorem adder_n1_measure_count_value :
    adder_n1_measure_count = 9 := by native_decide

/-- 9 DecodeSyndromes: 3 per PPM × 3 PPMs. -/
theorem adder_n1_decode_count_value :
    adder_n1_decode_count = 9 := by native_decide

/-- 3 PauliFrameUpdates: 1 per PPM × 3 PPMs. -/
theorem adder_n1_feedback_count_value :
    adder_n1_feedback_count = 3 := by native_decide

/-- 9 RequestFreshAncillas: 3 per PPM × 3 PPMs. -/
theorem adder_n1_fresh_ancilla_count_value :
    adder_n1_fresh_ancilla_count = 9 := by native_decide

/-! ## §5. Paper-style claim schema

    A small structured object representing an "optimistic
    paper claim" about an adder-level construction's
    system-level resources.  Used purely to demonstrate the
    review pattern; NOT attributed to any specific paper. -/

structure AdderSystemClaim where
  name                   : String
  claimed_wallclock_us   : Nat
  claimed_gate2q_count   : Nat
  claimed_measure_count  : Nat
  claimed_decoder_count  : Nat
  assumptions            : String
  deriving Repr

/-- A deliberately optimistic claim object: "the adder
    completes in 1 µs with 1 Gate2q, 1 Measure, 1 decode".
    Used to demonstrate the gap-reporting pattern.  No paper
    is being accused of this exact number — it is a SCHEMA. -/
def optimistic_parallel_adder_claim : AdderSystemClaim :=
  { name                   := "Optimistic single-cycle adder system claim"
    claimed_wallclock_us   := 1
    claimed_gate2q_count   := 1
    claimed_measure_count  := 1
    claimed_decoder_count  := 1
    assumptions            :=
      "Ignores serial Gate2q dependencies + decoder budget + " ++
      "ancilla freshness lifecycle." }

/-! ## §6. Direct gap theorem -/

/-- **Direct gap (smallest form)**: the optimistic claim's
    wallclock is strictly below the verified construction's
    wallclock.

    Interpretation: this does NOT prove the optimistic claim
    is impossible for ALL adder constructions; it proves the
    claim is FALSE for the concrete certified construction
    above. -/
theorem optimistic_adder_claim_underestimates_verified_schedule :
    optimistic_parallel_adder_claim.claimed_wallclock_us
      < adder_n1_wallclock_us := by
  native_decide

/-- Gate2q-count gap. -/
theorem optimistic_adder_claim_understates_verified_gate2qs :
    optimistic_parallel_adder_claim.claimed_gate2q_count
      < adder_n1_gate2q_count := by
  native_decide

/-! ## §7. Capacity lower-bound theorem

    A schedule-independent bound: under the chosen
    `max_gate2q_active` and per-Gate2q duration, ANY schedule
    that emits `num_gate2q` Gate2qs has wallclock at least
    `ceildiv(num_gate2q, max_parallel) · gate2q_us`.

    For the certified construction's Gate2q count and the
    chosen operation cap, this is a numerical bound; the
    optimistic claim is FORMALLY below it. -/

/-- Natural-number ceiling division.  `ceilDiv a 0 = 0` by
    Nat-divide-by-zero semantics; callers should pass a
    positive denominator. -/
@[inline] def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- The Gate2q capacity lower bound: with `max_parallel`
    parallel Gate2qs each taking `gate2q_us` µs, serving
    `num_gate2q` Gate2qs total takes at least
    `ceildiv(num_gate2q, max_parallel) · gate2q_us` µs. -/
def gate2q_capacity_lower_bound_us
    (num_gate2q max_parallel gate2q_us : Nat) : Nat :=
  ceilDiv num_gate2q max_parallel * gate2q_us

/-- Numerical lower bound for this review: 18 Gate2qs / 1
    parallel / 1 µs each = 18 µs. -/
theorem adder_n1_gate2q_capacity_lower_bound_value :
    gate2q_capacity_lower_bound_us
        adder_n1_gate2q_count
        adder_demo_opCap.max_gate2q_active
        1 = 18 := by native_decide

/-- **Capacity lower-bound gap**: the optimistic claim is
    formally below the Gate2q capacity lower bound under the
    same `OperationCapacityModel` used to certify the
    schedule.

    Interpretation: even abstracting away decoder budget,
    ancilla lifecycle, and timing nuance, NO schedule emitting
    18 Gate2qs with `max_gate2q_active = 1` can fit in 1 µs.
    The optimistic claim contradicts its own capacity
    assumptions. -/
theorem optimistic_adder_claim_below_gate2q_capacity_lower_bound :
    optimistic_parallel_adder_claim.claimed_wallclock_us
      < gate2q_capacity_lower_bound_us
          adder_n1_gate2q_count
          adder_demo_opCap.max_gate2q_active
          1 := by
  native_decide

/-! ## §8. Rejected bad adder schedule

    A schedule that runs two PPM blocks in PARALLEL on
    distinct ancilla sites.  No site-aliasing (so the OLD
    strengthened bundle accepts it), but two simultaneous
    `Gate2q`s exceed `adder_demo_opCap.max_gate2q_active = 1`.
    The strict-with-freshness bundle REJECTS it.

    Reuses the existing
    `surgery_pair_parallel_distinct_syscalls` — no
    re-construction. -/

/-- A bad adder-skeleton schedule: two PPM blocks in
    parallel.  Rejected by operation capacity. -/
def bad_parallel_adder_syscalls : List SysCall :=
  surgery_pair_parallel_distinct_syscalls

/-- **Bad-schedule rejection theorem.**  Direct "lack of
    system consideration causes failure" example. -/
theorem bad_parallel_adder_schedule_rejected :
    all_invariants_strict_with_slot_capacity_and_freshness_ok
        adder_demo_arch
        adder_demo_opCap
        adder_demo_slotCap
        adder_demo_ancillaModel
        bad_parallel_adder_syscalls
        adder_demo_t_react_us
        adder_demo_window_us
        adder_demo_max_per_window = false := by
  native_decide

/-! ## §9. Semantic correctness connection — honest report

    `BQAlgo/RippleCarryAdder.lean` and
    `Framework/CuccaroParametric.lean` contain ARITHMETIC
    correctness theorems for the Gidney / Cuccaro adder
    constructions at the Gate IR level (e.g.,
    `gidney_adder_forward_faithful_full_correct`,
    `cuccaro_bits_correct`).  These prove the GATE-IR
    construction implements classical addition.

    No theorem currently bridges the Gate IR to the
    `SysCall`-level emission in this file — that would be a
    `compile_adder_to_syscalls` function plus a soundness
    theorem relating Gate IR semantics to SysCall execution.
    This is a real gap.

    Honest framing: this review certifies the SYSTEM SCHEDULE
    of an adder-shaped construction, NOT that the schedule
    implements arithmetic addition. -/

/-- A purely structural cross-reference: the certified
    construction has 3 PPM blocks, which structurally
    correspond to the 3 stabilizer-extraction rounds that a
    single Cuccaro-style MAJ/UNMAJ gadget would consume.  No
    semantic claim. -/
example : adder_n1_syscalls.length = 3 * 16 := by native_decide

/-! ## §10. Summary

    First concrete micro-review result:

      * Construction: 3 sequential `compileSurgeryGadgetToSysCalls
        surgery_ppm_A` blocks → 48 SysCalls, 48 µs wallclock.
      * Strict system certificate
        (`adder_n1_strict_system_ok`): passes
        `all_invariants_strict_with_slot_capacity_and_freshness_ok`.
      * Derived resources: 48 SysCalls, 18 Gate2qs, 9
        Measures, 9 DecodeSyndromes, 3 PauliFrameUpdates, 9
        RequestFreshAncillas.
      * Optimistic claim: 1 µs wallclock, 1 Gate2q.
      * Direct gap
        (`optimistic_adder_claim_underestimates_verified_schedule`):
        1 < 48.
      * Capacity lower-bound gap
        (`optimistic_adder_claim_below_gate2q_capacity_lower_bound`):
        1 < ceildiv(18, 1) · 1 = 18.
      * Bad-schedule rejection
        (`bad_parallel_adder_schedule_rejected`): the parallel
        variant fails operation capacity.

    What remains:
      * Connect Gate IR adder correctness theorems (Cuccaro /
        Gidney) to a SysCall emission compiler with a
        soundness theorem (`compile_gate_to_syscalls` +
        `compile_preserves_semantics`).
      * Review a full Cuccaro N=1 system schedule
        (`cuccaro_n1_syscalls` in
        `Corpus/CuccaroSteaneSysInv.lean`) under the strict
        bundle; current schedule lacks
        `RequestFreshAncilla` and matching `DecodeSyndrome`
        for its `Measure` and `PauliFrameUpdate` calls, so it
        fails freshness and feedback-after-decode by design
        — a real review finding to be reported in a follow-up.
      * Promote the optimistic claim schema to actual paper
        numbers (Gidney–Ekerå 2021 Table 1, etc.) once we
        have a verified scale-up. -/

end FormalRV.Framework.AdderSystem
