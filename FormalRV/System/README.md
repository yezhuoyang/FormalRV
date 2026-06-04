# FormalRV.System

System-level (L4) layer of FormalRV: a platform-neutral `Architecture` /
`SysCall` schedule model plus decidable invariant checkers that verify a
compiled fault-tolerant schedule is well-formed (capacity, exclusivity,
latency, decoder-feedback ordering, factory throughput). It also provides
code-aware logical layouts and **parametric soundness lemmas** that lift a
single-body check to an `n`-fold compressed repeat without expanding it.

## Layout
- `Architecture.lean` — `Zone`/`Channel`/`SysCall` IR, `Prop`-level verification predicates, occupancy/discard state machines, magic-state cost specs, logical↔physical layout bridge; neutral-atom / ion / superconducting instantiations (cited values).
- `ScheduleInvariantsExplicit.lean` — decidable `Bool` checkers for the four qianxu invariants (I1 capacity, I2 exclusivity, I3 latency/speed, I4 throughput) over a `ZonedArch`.
- `SystemInvariantStrengthening.lean` — strengthened checkers fixing two checker gaps: `operation_capacity_ok` (per-kind concurrency caps) and `feedback_after_decode_ok` (decoder→Pauli ordering); bundles `all_invariants_strict_ok` and its slot-capacity/freshness extensions.
- `SystemChecker.lean` — honest audit of the older bundle: tiny `native_decide` counterexamples documenting five categories the checker is silent on, plus positive controls it correctly rejects.
- `CodedLayout.lean` — `CodedLogicalLayout` binding logical qubits to `[[n,k,d]]` QEC code blocks with a consistency predicate.
- `CompressedRepeatSoundness.lean` — shift/append/sequence/repeat invariance lemmas pushing toward parametric symbolic-repeat soundness.
- `AdderSystem.lean` — concrete 48-SysCall adder-skeleton instance certified by the strict bundle (gap-reporting demo, not arithmetic correctness).
- `LayeredArtifactInterface.lean` — multi-layer artifact/certificate interface so Lean- or Python-generated schedules target the same checkers.
- `HardwareErrorParams.lean` — implementer-supplied per-SysCall error-rate inputs (ppm) consumed by inter-layer error budgeting.

## Key definitions
- `Architecture` / `SysCall` (`Architecture.lean`) — cross-platform zones+channels and the explicit schedulable-operation IR (gates, transit, measure, decode, Pauli-frame update).
- `all_invariants_ok` (`ScheduleInvariantsExplicit.lean`) — conjunction of the four decidable system invariants.
- `all_invariants_strict_ok` / `..._with_slot_capacity_and_freshness_ok` (`SystemInvariantStrengthening.lean`) — strictly stronger bundles adding operation-capacity, feedback-after-decode, slot-capacity, and ancilla-freshness checks.
- `CodedLogicalLayout.consistent` (`CodedLayout.lean`) — checks block sizes, local-index bounds, and that every gate target is bound.
- `symbolic_rep_strict_ok` (`LayeredArtifactInterface.lean`) — O(|body|) check of an n-fold repeat without materializing the n copies.

## Key theorems
- `intervals_overlap_*`, `connEdges_*` (`SystemChecker.lean`) — boundary/orientation tests pinning the half-open overlap and edge conventions — **Arithmetic-only** (`decide`).
- `*_violator_accepted` / `*_rejected` (`SystemChecker.lean`) — the older bundle accepts five classes of physically-invalid schedules and correctly rejects the four it tracks — **Arithmetic-only** (`native_decide`), documenting real audit gaps.
- `feedback_after_decode_ok_seqSchedules` / `..._repeated_atom_expand` (`CompressedRepeatSoundness.lean`) — decoder-feedback ordering is preserved under sequential composition and n-fold repeat — **Verified** (parametric, by induction).
- `symbolic_rep_implies_expanded_feedback_after_decode_ok` (`CompressedRepeatSoundness.lean`) — symbolic-repeat acceptance implies the expanded schedule passes the feedback check — **Verified** (parametric).
- `adder_n1_repeated_1000000_symbolic_ok` (`CompressedRepeatSoundness.lean`) — the strict bundle accepts a 10⁶-fold repeat via the symbolic checker — **Arithmetic-only** (`native_decide`, no expansion).
- `adder_seq{2,3}_obligation_A_ok` (`CompressedRepeatSoundness.lean`) — exclusivity + factory-exclusivity + operation/slot capacity hold on concatenated adder blocks — **Arithmetic-only** (concrete `native_decide`; full parametric proof still pending).

## Status
The decidable checkers and their cross-platform architecture model are complete; the strict bundle is proven strictly stronger than the older one, and several invariants (feedback-after-decode, capacity) have **Verified** parametric shift/sequence/repeat-invariance lemmas, while others (exclusivity, slot capacity) are confirmed only on concrete instances pending a long index-induction proof. `SystemChecker.lean` honestly records five abstraction gaps the SysCall-level checker does not yet enforce. These are well-formedness/resource checks, not semantic circuit-correctness proofs — the adder skeleton is a system-layer scaffold, not a verified adder.

## Worked examples

### 1. The zoned `Architecture` design (`neutral_atom_mini`)

![zone design](../../docs/diagrams/zone_design.png)

An `Architecture` is `zones + channels + {t_stab_cycle, t_react, t_coherence}`.
Each `Zone` has a `role` (Memory / Processor / Ancilla / Factory / Routing), a
`capacity`, and an average routing time; each `Channel` carries a `kind`
(`AncillaSupply` / `MagicSupply` / `MemoryLoad` / `InterRouting`), a latency, a
bandwidth, and a per-transit fidelity. The diagram is the literal `neutral_atom_mini`
instance (`Architecture.lean:856`): a 21-qubit Processor fed by a 100-qubit Memory,
a 10-qubit Ancilla zone, and a 5-qubit Factory, each over a 15 µs / 99.9% channel.
Sibling instances `trapped_ion_mini` and `superconducting_mini` fill the *same shape*
with Quantinuum-H1 and Sycamore-class numbers.

### 2. Scheduling the system calls

Everything schedulable is an explicit `SysCall` with begin/end timestamps —
`Gate1q` / `Gate2q`, `Measure`, `TransitQubit`, `RequestFreshAncilla`,
`RequestMagicState`, `DecodeSyndrome`, `PauliFrameUpdate`. `AdderSystem.adder_n1_syscalls`
composes three PPM blocks into a concrete **48-SysCall, 48 µs** schedule, and every
resource number is *computed by `foldl`/`filter` over the list*, not typed in:
`adder_n1_*_value` (`native_decide`) prove **48 SysCalls, 18 `Gate2q`, 9 `Measure`,
9 `DecodeSyndrome`, 3 `PauliFrameUpdate`, 9 `RequestFreshAncilla`, wallclock 48 µs**.

### 3. Checking the invariants — accept

The strict bundle conjoins capacity, exclusivity, latency, throughput,
**operation-capacity** (per-kind concurrency caps), **feedback-after-decode**
ordering, slot-capacity, and ancilla-freshness. `adder_n1_strict_system_ok`
(`AdderSystem.lean:156`, **Verified** by `native_decide`) proves the schedule above
passes `all_invariants_strict_with_slot_capacity_and_freshness_ok` under a realistic
cap model (`max_gate2q_active = 1`, decoder bank 4).

### 4. Checking the invariants — reject (and a capacity lower bound)

Run the *same* checker on a schedule that fires two PPM blocks in parallel:
`bad_parallel_adder_schedule_rejected` (`AdderSystem.lean:354`, `native_decide`)
proves it returns **`false`** — two simultaneous `Gate2q`s exceed
`max_gate2q_active = 1`. The framework also pins a schedule-independent floor: any
schedule emitting 18 `Gate2q`s one-at-a-time needs `≥ ⌈18/1⌉·1 = 18 µs`, so an
"optimistic 1 µs" claim is provably impossible
(`optimistic_adder_claim_below_gate2q_capacity_lower_bound`). This is the
**gap-reporting** pattern — a paper claim that ignores serial dependencies is
formally contradicted by its own capacity assumptions.

### 5. The verified resource ceiling, and the GE2021 gap

![scheduling invariants](../../docs/diagrams/scheduling_invariants.png)

*Left:* `scheduleFootprint_replicate` (`LatticeSurgery/ScheduleEmit.lean:66`,
**Verified**) — a schedule of `n` surgery merges occupies exactly `28·n` physical
qubits (`28 = merged_n + |hx| + |hz|`). *Right:* instantiating the verified
`surfaceModel` resource formula with Gidney–Ekerå 2021's own inputs (`2.7×10⁹`
Toffolis, 6200 logicals, `[[1568,1,27]]`, 1 µs) gives a derived ceiling of
**19.44M ≤ the reported 20M** qubits (~3%, the residual being the magic factory) and
a naive-sequential time ceiling of **20.25 h**, machine-checking that the reported
8 h sits **2–3×** below it — the gap is reaction-limited pipelining, pinned
explicitly by `gidney_ekera_2021_reproduced`.

### 6. T-state, ancilla, and qubit-routing scheduling — in detail

<p align="center"><img src="../../docs/diagrams/syscall_timeline.png" width="900" alt="SysCall scheduling timeline"></p>

The Gantt above is the verified 16-µs PPM block
(`compileSurgeryGadgetToSysCalls surgery_ppm_A`): three syndrome rounds of
`RequestFreshAncilla → Gate2q → Gate2q → Measure → DecodeSyndrome`, then a
`PauliFrameUpdate`. Three resource types are scheduled *explicitly*:

- **Ancilla (lifecycle).** `RequestFreshAncilla 1` allocates the smallest non-`Live`
  site in zone 1's range `[100,200)` (the `AncillaModel` "next free site" rule,
  `demo_ancilla_model`); after `Measure` the site goes `Dirty`, and the next round's
  request re-allocates it `Live`. `ancilla_freshness_ok` rejects use-before-reset,
  reuse-without-reset, and dangling-`Live` schedules.
- **T-states.** `RequestMagicState factory_zone` draws a `|T⟩`/`|CCZ⟩` from a Factory
  zone; `MagicStateSpec` (`Architecture.lean:548`) carries the factory's qubit cost,
  production time, success rate, and output fidelity, and `capacity_ok` bounds the
  per-zone request count. (This block makes no magic requests — the Factory zone of the
  [zone design](#worked-examples) sits idle here.)
- **Routing.** `TransitQubit q channel_id` moves a qubit through a `Channel`;
  `latency_ok` forces each transit to last ≥ the channel latency (15 µs neutral-atom /
  500 µs ion / 1 µs SC) and `channel_bandwidth_ok` caps transits per ms.

Two invariants are visible above: **operation-capacity** (`max_gate2q_active = 1` → the
`Gate2q`s never overlap) and **feedback-after-decode** (each `PauliFrameUpdate` begins
only after its `DecodeSyndrome` ends). The whole block passes `adder_n1_strict_system_ok`
by `native_decide`. *Honest scope:* per-SysCall durations are representative hand-coded
values (cited from hardware papers), and factory distillation correctness is assumed.

## Essential proof techniques

- **A ∀-size feasibility ceiling by induction.** `naivePeak_le_footprint`
  (`NaiveUpperBound.lean:86`) proves the one-Toffoli-at-a-time schedule's peak qubit
  demand never exceeds the static footprint, by a one-line induction on the step
  count (`max footprint (≤footprint) = footprint`) — so the bound holds for *every*
  problem size, not just the concrete instance.
- **Closed-form footprint via `foldl` over `replicate`.** `scheduleFootprint_replicate`
  reduces the symbolic sum of `n` identical gadget footprints to `n · gadgetFootprint g`
  (helper `foldl_add_replicate`), so parametric schedules cost out without
  materialising the list.
- **One formula, pluggable cost model.** `estimateWith` is polymorphic over the
  `CostModel`; swapping `surfaceModel ↔ qldpcModel` is a parameter substitution proven
  once by `rfl`, and the concrete GE2021 numbers are then `decide`-level arithmetic
  over that verified formula.

Honest scope: the GE2021 reproduction is a verified-*formula* result over recorded
inputs (**Arithmetic-only** at the literal level), not a whole-circuit semantic
closure; the cost-model rules and the `demoCtx` feasibility witness are illustrative,
and several invariants are confirmed only on concrete instances pending full
index-induction.
