/-
  FormalRV.Framework.SystemChecker — an honest review of
  what the system-layer checker accepts vs what it SHOULD reject
  under the paper's abstraction.

  ## Why this file exists

  The framework's strengthened system-layer checker
  (`all_invariants_with_factory_ports_ok` from
  `LatticeSurgeryPPMContract.lean`) accepts a schedule iff:

    capacity_in_arch_ok          ∧
    capacity_per_cycle_ok        ∧
    exclusivity_ok               ∧
    factory_exclusivity_ok       ∧
    feedback_latency_ok          ∧
    decoder_react_ok             ∧
    window_throughput_ok

  Each conjunct is decidable on concrete schedules; the bundle
  closes by `native_decide` on small schedules.  This file
  systematically probes the bundle for gaps between "passes the
  checker" and "is a physically/scheduler-valid schedule under
  the paper abstraction".

  We construct TINY concrete schedules that pass the checker
  but violate one or more intended invariants, and prove via
  `native_decide` that the checker accepts them.  Each
  counterexample is paired with a documentation block stating
  exactly which invariant the paper requires that the checker
  does not currently enforce.

  ## What this file is NOT

  This file does NOT introduce a strengthened replacement
  checker — that is a follow-up tick.  Each gap is documented
  with a precise specification of what a fix would look like.
  Counterexamples that the current checker correctly rejects
  also live here (positive control).

  No `sorry`, no custom `axiom`.  Pure Bool/Nat, `native_decide`.
-/

import FormalRV.System.ScheduleInvariantsExplicit
import FormalRV.LatticeSurgery.LatticeSurgeryPPMContract
import FormalRV.LatticeSurgery.SurgeryGadgetToSysCalls

namespace FormalRV.Framework.SystemChecker

open FormalRV.Framework
open FormalRV.Framework.Architecture
open FormalRV.Framework.ScheduleInv
open FormalRV.Framework.LDPC
open FormalRV.Framework.LatticeSurgeryPPMContract
open FormalRV.Framework.SurgeryGadgetToSysCalls

/-! ## §1. Interval-overlap boundary tests

    `intervals_overlap a_lo a_hi b_lo b_hi := a_lo < b_hi ∧
    b_lo < a_hi` treats both intervals as half-open
    `[a_lo, a_hi)`.  The boundary convention is:

      [0, 1) and [1, 2) do NOT overlap (touching only).
      [0, 2) and [1, 3) DO overlap.
      [0, 2) and [2, 4) do NOT overlap.

    These tests confirm there is NO off-by-one in the
    convention. -/

theorem intervals_overlap_touching_disjoint :
    intervals_overlap 0 1 1 2 = false := by decide

theorem intervals_overlap_strictly_disjoint :
    intervals_overlap 0 2 2 4 = false := by decide

theorem intervals_overlap_proper_overlap :
    intervals_overlap 0 2 1 3 = true := by decide

theorem intervals_overlap_contained :
    intervals_overlap 0 10 3 7 = true := by decide

theorem intervals_overlap_symmetric :
    intervals_overlap 1 3 0 2 = true := by decide

/-! ## §2. `connEdges` orientation tests

    `connEdges` extracts `(row, col)` pairs from a `BoolMat`.
    For the topology compiler, X-edge `(i, j)` ⟼ `Gate2q
    (dataSite j) (ancillaSite i)` (because `conn_x`'s rows
    index ancilla X-checks and columns index data qubits),
    while Z-edge `(i, j)` ⟼ `Gate2q (dataSite i) (ancillaSite
    j)` (rows = data Z-checks, cols = ancilla qubits).

    These tests pin the (row, col) orientation of `connEdges`
    so any future swap is caught immediately. -/

theorem connEdges_single_row_three_entries :
    connEdges [[true, false, true, false, true]] = [(0, 0), (0, 2), (0, 4)] := by
  decide

theorem connEdges_three_rows_one_entry :
    connEdges [[false, true], [false, false], [true, false]]
      = [(0, 1), (2, 0)] := by
  decide

theorem connEdges_all_false_empty :
    connEdges [[false, false], [false, false]] = [] := by decide

theorem connEdges_empty_matrix :
    connEdges ([] : BoolMat) = [] := by decide

/-! ## §3. `target_pauli` is ignored by the topology compiler

    `compileTopologySurgeryToSysCalls` reads only:
      * `gadget.tau_s`           — number of rounds;
      * `gadget.ancilla_n`       — number of Measure SysCalls;
      * `gadget.conn_x, conn_z`  — per-round Gate2q stream;
      * the schedulable spec's `start_us`, `dataSite`,
        `ancillaSite`, `decoderBase`.

    It does NOT read `target_pauli`.  Two gadgets that agree on
    all of the above but differ in `target_pauli` therefore
    compile to IDENTICAL SysCall streams — even though they
    claim to measure DIFFERENT logical Pauli operators.

    The qLDPC structural verifier `verify_surgery_gadget`
    consumes `target_pauli` via `targets_logical_correctly`,
    so this is not a verification bug: the framework correctly
    rejects a `target_pauli` outside the row span.  But the
    SysCall stream alone is insufficient to determine WHICH
    Pauli the surgery measures — that information lives only in
    the gadget, not in the SysCalls.

    Concretely:  if a paper claims "this SysCall stream
    implements PPM(P̄₁)" and an attacker substitutes a
    different target `P̄₂` that ALSO passes
    `verify_surgery_gadget` on the SAME `conn_x/conn_z`, the
    SysCall-level checker cannot tell them apart.

    The gap closes via the L3/system contract
    (`verify_surgery_gadget_with_schedule`) which RE-verifies
    the gadget alongside the SysCall stream — but a SysCall
    stream presented alone (without the gadget) carries no
    target_pauli information. -/

/-- A topology-schedulable gadget cloned from `topology_demo`
    but with `target_pauli` mutated to a DIFFERENT (still
    row-span-valid) Pauli.  Even with the mutation, the
    compiled SysCall stream is identical to `topology_demo`'s.

    We pick the same row-span witness so the mutated gadget
    still passes the kernel-condition check; this isolates the
    target_pauli-vs-SysCall gap. -/
def topology_demo_target_mutated_gadget : SurgeryGadget :=
  { topology_demo_gadget with
    -- Swap to a different valid target_pauli: use the trivial
    -- all-false vector with the empty span witness.  This is a
    -- DIFFERENT logical operator (the identity) than the
    -- original X̄-style operator, but the compiled SysCall
    -- stream remains identical because the compiler ignores
    -- `target_pauli`.
    target_pauli      := [false, false, false, false]
    span_witness      := [false] }

/-- The mutated gadget has a different `target_pauli`. -/
theorem topology_demo_target_mutated_differs :
    topology_demo_target_mutated_gadget.target_pauli
      ≠ topology_demo_gadget.target_pauli := by
  decide

/-- A wrapper around the mutated gadget with the SAME
    scheduling spec as `topology_demo`. -/
def topology_demo_target_mutated : TopologySchedulableSurgeryGadget :=
  { topology_demo with gadget := topology_demo_target_mutated_gadget }

/-- **The target_pauli gap, proven**: two gadgets with
    DIFFERENT target_pauli compile to the SAME SysCall stream.
    The SysCall-layer checker cannot tell which logical Pauli
    is being measured. -/
theorem topology_compiler_ignores_target_pauli :
    compileTopologySurgeryToSysCalls topology_demo_target_mutated
      = compileTopologySurgeryToSysCalls topology_demo := by
  rfl

/-! ## §4. Decoder → PauliFrameUpdate dependency ordering gap

    `decoder_react_ok` checks ONLY that each `DecodeSyndrome`
    call has duration ≤ `t_react_us`.  It does NOT enforce that
    a `PauliFrameUpdate` referencing decoder id `d` fires AFTER
    the matching `DecodeSyndrome d`.

    A schedule can therefore place `PauliFrameUpdate 0` at t=0
    and `DecodeSyndrome 0` at t=10 — the Pauli correction
    "happens" before the decoder has produced its output. -/

/-- A schedule with PauliFrameUpdate at t=0..1 BEFORE the
    matching DecodeSyndrome at t=10..11.  Physically the
    feedback cannot fire before the decoder runs, but the
    current checker is silent on this dependency. -/
def decoder_dependency_violator : List SysCall :=
  [ { kind := SysCallKind.PauliFrameUpdate 0
      begin_us := 0, end_us := 1 }
  , { kind := SysCallKind.DecodeSyndrome 0
      begin_us := 10, end_us := 11 } ]

/-- **Accepted-invalid schedule**: PauliFrameUpdate fires
    before the matching DecodeSyndrome, but the strengthened
    bundle accepts it. -/
theorem decoder_dependency_violator_accepted :
    all_invariants_with_factory_ports_ok
        surgery_arch decoder_dependency_violator
        10 1000 1000 = true := by
  native_decide

/-! ### Proposed strengthening (NOT implemented this tick)

      def feedback_after_decode_ok (sched : List SysCall) : Bool :=
        sched.all fun sc =>
          match sc.kind with
          | .PauliFrameUpdate cid =>
              -- there exists a DecodeSyndrome with id `cid`
              -- whose end_us ≤ sc.begin_us
              sched.any fun sc' =>
                match sc'.kind with
                | .DecodeSyndrome did =>
                    decide (did = cid) && decide (sc'.end_us ≤ sc.begin_us)
                | _ => false
          | _ => true

    Adding this as a conjunct would reject
    `decoder_dependency_violator`. -/

/-! ## §5. Routing/coupler gap for `Gate2q`

    `syscall_acts_on` returns `[q1, q2]` for `Gate2q q1 q2 _`.
    It does NOT include any routing-lane / coupler /
    control-channel id.  Two simultaneous `Gate2q`s on
    DISJOINT endpoint sites can therefore share a physical
    coupler in a real device while passing `exclusivity_ok`.

    This is a known abstraction limit: the framework's
    `Architecture` carries `channels` separately from sites,
    but the SysCall-level exclusivity checker doesn't consult
    them. -/

/-- Two simultaneous `Gate2q`s on endpoint-disjoint sites
    (0↔100 and 1↔101), but a real architecture might route
    both through the same intermediate qubit/coupler.  The
    checker cannot see the coupler conflict. -/
def routing_lane_violator : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 100 0
      begin_us := 0, end_us := 2 }
  , { kind := SysCallKind.Gate2q 1 101 0
      begin_us := 0, end_us := 2 } ]

/-- **Accepted-invalid schedule (in principle)**: the
    routing-lane gap is purely about what `syscall_acts_on`
    reports; the checker has no way to know coupler conflicts
    exist. -/
theorem routing_lane_violator_accepted :
    all_invariants_with_factory_ports_ok
        surgery_arch routing_lane_violator
        10 1000 1000 = true := by
  native_decide

/-! ### Proposed strengthening (NOT implemented this tick)

    Extend `syscall_acts_on` to a richer predicate that, for
    `Gate2q q1 q2 gate_id`, ALSO returns the routing-lane ids
    consumed by `gate_id` (from a separate
    `routing_lane_fn : gate_id → List RoutingSiteId`).  Then
    `exclusivity_ok` becomes a multi-resource check.

    Until then, schedules that pass `exclusivity_ok` are
    correct only on architectures with FULL connectivity (any
    two endpoints can fire simultaneously). -/

/-! ## §6. RequestFreshAncilla freshness gap

    `RequestFreshAncilla target_zone` has
    `syscall_acts_on = []`.  It claims no specific site, and
    nothing in the checker enforces:

      * that a Gate2q against an ancilla SITE is preceded by a
        recent `RequestFreshAncilla` for that site;
      * that two consecutive uses of the same ancilla site are
        separated by a `RequestFreshAncilla` reset between
        them. -/

/-- A schedule that uses ancilla site 100 in a `Gate2q` BEFORE
    issuing any `RequestFreshAncilla`.  The checker accepts.
    Physically the ancilla is undefined. -/
def freshness_use_before_reset : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 100 0
      begin_us := 0, end_us := 1 }
  , { kind := SysCallKind.RequestFreshAncilla 1
      begin_us := 2, end_us := 3 } ]

theorem freshness_use_before_reset_accepted :
    all_invariants_with_factory_ports_ok
        surgery_arch freshness_use_before_reset
        10 1000 1000 = true := by
  native_decide

/-- A schedule that REUSES ancilla site 100 across two Gate2qs
    WITHOUT a `RequestFreshAncilla` reset between them.
    Physically the second Gate2q operates on the post-Measure
    classical state of the ancilla, not a fresh zero state. -/
def freshness_reuse_without_reset : List SysCall :=
  [ { kind := SysCallKind.RequestFreshAncilla 1
      begin_us := 0, end_us := 1 }
  , { kind := SysCallKind.Gate2q 0 100 0
      begin_us := 1, end_us := 2 }
  , { kind := SysCallKind.Gate2q 1 100 0
      begin_us := 3, end_us := 4 } ]   -- no fresh reset between!

theorem freshness_reuse_without_reset_accepted :
    all_invariants_with_factory_ports_ok
        surgery_arch freshness_reuse_without_reset
        10 1000 1000 = true := by
  native_decide

/-! ### Proposed strengthening (NOT implemented this tick)

    Tag each ancilla-using SysCall with the expected lifetime:
    introduce a `freshness_ok` predicate that walks the
    schedule and tracks the "live ancilla" set as a state
    machine.

      `RequestFreshAncilla z` adds the next-free ancilla site
        (per `target_zone z`) to the live set with a `fresh`
        flag.
      `Gate2q _ a _` requires `a` to be live AND fresh; the
        flag may flip to `dirty` after use.
      `Measure a _` consumes `a` and removes it from the live
        set.

    Implementing this requires a stateful walk; the current
    purely-functional checker does not support it. -/

/-! ## §7. `SiteId` type-conflation gap

    All identifier aliases (`SiteId`, `PhysicalQubitId`,
    `PatchSlotId`, `FactoryPortId`, `RoutingSiteId`) are
    `abbrev`s for `Nat`.  Nothing prevents a schedule from
    using the same `Nat` value as a `Gate2q` endpoint AND as a
    `RequestMagicState` factory zone — they have the same
    representation and the checker treats them with disjoint
    bookkeeping (`syscall_acts_on` vs `syscall_factory_claims`). -/

/-- A schedule mixing `Gate2q` on qubit 203 and
    `RequestMagicState` on factory zone 3 (which claims port
    `200 + 3 = 203`).  These should refer to different
    resources, but both use the bare `Nat` 203.  The checker
    treats them as independent. -/
def site_id_conflation : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 203 0
      begin_us := 0, end_us := 2 }
  , { kind := SysCallKind.RequestMagicState 3
      begin_us := 0, end_us := 2 } ]

theorem site_id_conflation_accepted :
    all_invariants_with_factory_ports_ok
        surgery_arch site_id_conflation
        10 1000 1000 = true := by
  native_decide

/-! ### Proposed strengthening (NOT implemented this tick)

    Wrap each id family in a single-constructor inductive
    rather than `abbrev`:

      structure SiteId         where val : Nat
      structure FactoryPortId  where val : Nat
      ...

    This forces explicit conversions and prevents accidental
    cross-domain use at the type level.  Alternatively (less
    invasive): partition the `Nat` range by zone-role and
    review that no `Gate2q` argument lands in a
    factory-port-reserved subrange. -/

/-! ## §8. `window_throughput_ok` causal-prefix gap

    `window_throughput_ok` aggregates magicReq COUNT per
    `window_us`-wide window aligned with a magicReq begin
    time.  Two-window structure:

      Schedule A: 1 magicReq at t=0
      Schedule B: 1 magicReq at t=0, 1 magicReq at t=10000
                  (window_us = 1000, max_per_window = 1)

    Both pass: in any single 1000-µs window, count ≤ 1.  But
    the paper's intended factory model is a CAUSAL supply:
    `available(t) = floor(t / distillation_us)` magic states.
    A magicReq at t=0 demands 1 magic state that the factory
    has not yet produced.  The current checker doesn't
    enforce a startup-prefix lag. -/

/-- A schedule demanding a magic state at t=0 with no
    production prefix.  Passes the window check (1 ≤ 1) but
    violates the causal availability `available(0) = 0`. -/
def magic_no_startup_prefix : List SysCall :=
  [ { kind := SysCallKind.RequestMagicState 3
      begin_us := 0, end_us := 2 } ]

theorem magic_no_startup_prefix_accepted :
    all_invariants_with_factory_ports_ok
        surgery_arch magic_no_startup_prefix
        10 1000 1 = true := by
  native_decide

/-! ### Proposed strengthening (NOT implemented this tick)

      def factory_causal_supply_ok
          (sched : List SysCall) (distillation_us : Nat) : Bool :=
        let magic_reqs := sched.filter <fun sc => …RequestMagicState…>
        magic_reqs.zipIdx.all fun ⟨sc, idx⟩ =>
          -- the (idx+1)-th magic state is available only at
          -- t ≥ (idx + 1) · distillation_us
          decide (sc.begin_us ≥ (idx + 1) * distillation_us)

    This enforces a per-factory FIFO causal queue.  The current
    `window_throughput_ok` is a weaker AGGREGATE bound that
    accepts any distribution as long as no single window
    over-subscribes. -/

/-! ## §9. `capacity_per_cycle_ok` redundancy under exclusivity

    Claim: under `capacity_in_arch_ok ∧ exclusivity_ok`,
    `capacity_per_cycle_ok` is structurally implied.

    Argument: `capacity_per_cycle_ok` counts atom OCCURRENCES
    in `((active_at t).flatMap syscall_acts_on)`.  Under
    `exclusivity_ok`, all active SysCalls claim disjoint atoms,
    so the occurrence count equals the count of distinct atoms
    claimed.  Under `capacity_in_arch_ok`, every claimed atom
    lies in some zone of the architecture, so distinct atoms
    landing in zone `z` are bounded by `|atoms(z)| =
    z.atom_hi - z.atom_lo = z.capacity`.

    Conclusion: `capacity_per_cycle_ok` adds no constraints
    beyond `capacity_in_arch_ok ∧ exclusivity_ok` SO LONG AS
    architecture zones are disjoint intervals (the framework
    invariant we already assume).  It is kept in the bundle
    for cheap defence-in-depth; a structural proof of the
    implication is left as a follow-up. -/

/-- Documented limitation: under the current `ArchZone`
    semantics, `capacity_per_cycle_ok` is redundant given
    `capacity_in_arch_ok ∧ exclusivity_ok`.  A proof would
    need a List-disjointness lemma and a zone-disjointness
    hypothesis that the framework does not currently expose.
    Leaving this as a TODO does not weaken the checker, only
    its presentation. -/
example : True := trivial  -- placeholder for the TODO theorem

/-! ## §10. Positive controls (counterexamples the checker
       correctly rejects)

    To confirm the bundle still catches the failure modes it
    is DESIGNED to catch: -/

/-- Two `Gate2q`s overlapping in time on the SAME ancilla
    site are REJECTED (standard exclusivity catches it). -/
def positive_ancilla_alias : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 100 0
      begin_us := 0, end_us := 2 }
  , { kind := SysCallKind.Gate2q 1 100 0
      begin_us := 1, end_us := 3 } ]

theorem positive_ancilla_alias_rejected :
    all_invariants_with_factory_ports_ok
        surgery_arch positive_ancilla_alias
        10 1000 1000 = false := by
  native_decide

/-- Two overlapping `RequestMagicState`s on the SAME factory
    zone (port aliasing) are REJECTED. -/
def positive_factory_port_alias : List SysCall :=
  [ { kind := SysCallKind.RequestMagicState 3
      begin_us := 0, end_us := 5 }
  , { kind := SysCallKind.RequestMagicState 3
      begin_us := 1, end_us := 6 } ]

theorem positive_factory_port_alias_rejected :
    all_invariants_with_factory_ports_ok
        surgery_arch positive_factory_port_alias
        10 1000 1000 = false := by
  native_decide

/-- An off-architecture atom claim (site 500 with arch size
    400) is REJECTED by `capacity_in_arch_ok`. -/
def positive_off_arch_claim : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 500 0
      begin_us := 0, end_us := 1 } ]

theorem positive_off_arch_claim_rejected :
    all_invariants_with_factory_ports_ok
        surgery_arch positive_off_arch_claim
        10 1000 1000 = false := by
  native_decide

/-- A `DecodeSyndrome` exceeding its react budget is REJECTED. -/
def positive_decoder_too_slow : List SysCall :=
  [ { kind := SysCallKind.DecodeSyndrome 0
      begin_us := 0, end_us := 100 } ]   -- 100 µs > t_react_us=10

theorem positive_decoder_too_slow_rejected :
    all_invariants_with_factory_ports_ok
        surgery_arch positive_decoder_too_slow
        10 1000 1000 = false := by
  native_decide

/-! ## §11. Summary table (machine-readable)

    Counterexamples in this file:

      §3   target_pauli ignored                   gap
      §4   decoder → PauliFrame ordering          gap
      §5   Gate2q routing/coupler                 gap
      §6   RequestFreshAncilla freshness          gap
      §7   SiteId type-conflation                 gap
      §8   window_throughput causal-prefix        gap

    Boundary tests (no gap):

      §1   intervals_overlap                      OK
      §2   connEdges orientation                  OK

    Documented structural limitation:

      §9   capacity_per_cycle redundancy under
           exclusivity ∧ in-arch                  OK (kept
           for defence-in-depth)

    Positive controls (correctly rejected):

      §10  ancilla alias, factory-port alias,
           off-architecture claim, decoder too
           slow                                   OK

    The headline finding: **the current checker is sound for
    the resource categories it tracks (atom-site exclusivity,
    factory-port exclusivity, capacity, latency, throughput
    counts) but is silent on five distinct categories**:

      (i)   target_pauli ↔ SysCall stream correspondence;
      (ii)  decoder feedback dependency order;
      (iii) routing-lane / coupler exclusivity;
      (iv)  ancilla freshness/reset lifecycle;
      (v)   factory causal-supply prefix.

    All five gaps can be closed by additional invariants of the
    same SysCall-level shape.  Counterexamples in this file
    are the regression tests a strengthened checker must
    reject. -/

end FormalRV.Framework.SystemChecker
