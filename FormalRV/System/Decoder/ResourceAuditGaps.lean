/-
  FormalRV.System.ResourceAuditGaps — uncounted-cost findings from the resource
  self-audit.  The audit found no hidden fudge factor (`ReactionLimitedRuntime`
  proves the 2.5× time gap is exactly the 27 µs/10 µs cost-model ratio); the
  residual risk is OMISSION.  The checkable parts are encoded as theorems, the
  rest is recorded honestly as documentation:

    GAP 1  decoder THROUGHPUT — the missing `load ≤ lanes` invariant (encoded
           here as `decoderThroughputInv`; full queue dynamics with the
           provisioned/divergent dichotomy in `DecoderBacklogModel`).
    GAP 2  the reported runtime is ~100× above the critical-path depth floor,
           so GE2021 runs reaction-limited at the Toffoli COUNT, not the DEPTH;
           code-depth-limited (serial) lookups push the 7.5 h past 8 h (encoded
           as inequalities).
    GAP 3  magic-state factory undersize (~17×) and per-state delivery
           transport (~d cycles each) — documentation-level findings only, see
           the GAP 3 section.

  No `sorry`, no new `axiom`.
-/

import FormalRV.System.Invariants.InvariantFramework

namespace FormalRV.System.ResourceAuditGaps

open FormalRV.System.InvariantFramework

/-! ## GAP 1 — decoder THROUGHPUT: the missing `load ≤ capacity` invariant

    `decoderInv` bounds a SINGLE decode's latency.  It does NOT bound the
    aggregate: ~6200 patches each emit a syndrome every cycle, each needing
    `decodeLatencyCycles` to clear.  Below the worst-case (un-pipelined) capacity,
    the syndrome backlog grows unboundedly (Fowler/Terhal) and the reaction time
    degrades — toward or PAST the d-cycle ceiling. -/

/-- Worst-case decode lanes required: `patches · decodeLatencyCycles` (each patch's
    per-cycle syndrome occupies a lane for the full decode latency).  Streaming/
    pipelined decoders reduce this to `patches`. -/
def decoderThroughputOk (patches decodeLatencyCycles nLanes : Nat) : Bool :=
  decide (patches * decodeLatencyCycles ≤ nLanes)

/-- The decoder-throughput SpaceTimeInvariant — composes into `checkAll` like any
    other system constraint.  `nLanes` is a CLASSICAL co-processor count, NOT a
    qubit: the decoder fabric this invariant constrains is absent from the 20 M
    physical-qubit budget entirely. -/
def decoderThroughputInv (patches decodeLatencyCycles nLanes : Nat) : SpaceTimeInvariant :=
  { name := "decoder throughput (load ≤ lanes, no backlog)",
    check := fun _ => decoderThroughputOk patches decodeLatencyCycles nLanes }

/-- GE2021: 6200 patches, 10-cycle (10 µs) decode latency ⇒ worst-case **62 000
    parallel decode lanes** to avoid backlog. -/
theorem ge2021_decode_lanes_worstcase : 6200 * 10 = 62_000 := by decide

/-- A machine with only one decoder lane PER PATCH (6200, un-pipelined) is
    UNDER-PROVISIONED — backlog grows. -/
theorem ge2021_decoder_oneper_patch_fails :
    decoderThroughputOk 6200 10 6200 = false := by decide

/-- 62 000 lanes (or fully-pipelined streaming decoders) suffice. -/
theorem ge2021_decoder_provisioned_ok :
    decoderThroughputOk 6200 10 62_000 = true := by decide

/-! ## GAP 2 — critical-path floor vs runtime: ~100× headroom, or serial residue

    Our own modexp critical-path depth (6.19 M Toffoli layers) floors to ~4 min at
    1 µs/cycle, yet GE2021 reports ~7.5 h.  The runtime is ~100× ABOVE the depth
    floor — so GE2021 runs reaction-limited at the Toffoli COUNT (≈ sequential),
    NOT at the parallel DEPTH.  Two honest consequences:
    (a) huge TIME headroom — more factories ⇒ faster, down toward the floor;
    (b) the 74× we attribute to "other ops" is UNENUMERATED — if lookups run at
        code-depth (27 µs) rather than reaction-time (10 µs), that SERIAL residue
        adds to the floor and the 7.5 h reproduction is OPTIMISTIC. -/

/-- modexp critical-path depth × ~40 cycles/Toffoli = 247.7 M cycles ≈ 4.1 min. -/
def modexpDepthFloorCycles : Nat := 6_193_152 * 40
theorem modexpDepthFloor_value : modexpDepthFloorCycles = 247_726_080 := by decide

/-- GE2021's reaction-limited runtime (7.5 h = 27×10⁹ cycles at 1 µs) is ≥ 100× the
    critical-path depth floor — the computation is run NEAR-SEQUENTIALLY, leaving
    a ~100× space-time parallelism headroom (and hiding any serial-lookup residue). -/
theorem runtime_is_100x_depth_floor :
    100 * modexpDepthFloorCycles ≤ 27_000_000_000 := by decide

/-- If a fraction of Toffolis are code-depth-limited (lookups at 27 µs, not 10 µs),
    the reaction-limited 7.5 h is optimistic.  Worked (in µs): 15 % depth-limited
    gives per-op average 0.85·10 + 0.15·27 = 12.55 µs, so runtime = 12.55 µs ×
    2.7×10⁹ = 33.9×10⁹ µs ≈ 9.4 h — ABOVE the reported 8 h = 28.8×10⁹ µs. -/
theorem mixed_cost_pushes_above_8h :
    28_800_000_000 < (85 * 10 + 15 * 27) * 27_000_000 := by decide

/-! ## GAP 3 — magic-state factory undersize + delivery transport (documentation)

    Documentation-level findings — recorded here, NOT verified content:

    • FACTORY UNDERSIZE: `demoFactory` charges 100 k qubits per copy, while
      GE2021's distillation slice (~7 % of 20 M ≈ 1.4 M, over ~6 CCZ factories)
      implies ~1.7 M qubits per factory — the demo factory is ~17× too small
      for that slice.

    • DELIVERY UNCOUNTED: moving each magic state from the factory-zone
      boundary to its target data patch by lattice surgery costs ~d cycles PER
      STATE (≥ 27 at d = 27) and competes for the routing area — and appears in
      NEITHER `cyclesPerMagic` (production only) NOR any invariant. -/

end FormalRV.System.ResourceAuditGaps
