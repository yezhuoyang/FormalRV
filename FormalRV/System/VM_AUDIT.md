# System/ ↔ FTQ-VM Audit — 2026-06-11

> **RESOLUTION NOTE (same day, second pass).** The cleanup recommendations below have
> been **executed**: the three tick-accretion monsters are split
> (`CompressedRepeatSoundness` → `Artifacts/CompressedRepeat/` ×9 modules;
> `LatticeSurgeryPPMContract` → `Core/ScheduleCombinators` + `Compile/PPMScheduleContract`
> + `Compile/PPMContractInstances`; `LayeredArtifactInterface` →
> `Artifacts/LayeredArtifactCore` + `Artifacts/CompressedSchedule`; the original module
> names remain as re-exporting umbrellas); all System namespaces are normalized to
> `FormalRV.System.*`; `StabilizerScheduleVerify` moved to `QEC/`; dead
> `HardwareErrorParams` deleted; the RSA-2048/GE2021 constants are canonical in
> `Params/RSA2048.lean`; and the flagged tautological/vacuous theorems named in §1
> (`audit_verdict_no_cheat_only_omission`, `ge2021_magic_delivery_uncounted`,
> `sensitivity_complete`, `naive_opcount_eq_three_toff`, `verified_toff_le_reported`,
> `adder_n1_wallclock_is_derived`, `disjoint_no_shared_atom`,
> `windowed_factory_share_positive`, `idle_patch_still_measures`, and the
> `FTSystem.wellFormed` dead API) are **deleted** with their substantive claims folded
> into honest doc-comments; the stale headers/status blocks/tick retrospectives are
> rewritten.  One Lean 4 lesson from the split: `match`-pattern `rw` requires the
> auxiliary matcher to live in the SAME module — the freshness equivalence/repeat pair
> is therefore one file (`CompressedRepeat/FreshnessSoundness.lean`).  Theorem-name
> citations below reflect the pre-cleanup state; deleted names are kept here as the
> audit record.

Third-party audit of `FormalRV/System/` (40 files, ~700 KB, 345 theorems) against the
FTQ-VM (`ftq_vm/`), the independent Python discrete-event checker. Cross-validation
artifacts: `ftq_vm/out/audit_system/cross_check.py` (13 cases) and
`backlog_check.py` (quantitative queue-law check). Full per-file mapping data:
workflow `w165dpz13` output (10 parallel readers).

## 1. Verdict on the proofs: real, but ~74/345 oversell

**No false theorems were found** — and the five worked verdicts of
`SystemInvariantExamples.lean` plus the backlog dichotomy of
`DecoderBacklogModel.lean` were **independently reproduced by the VM**:

| Lean theorem (native_decide)        | VM verdict | agreement |
|-------------------------------------|------------|-----------|
| `passSequential_ok` (PASS)          | PASS       | ✓ |
| `passParallelDistinct_ok` (PASS)    | PASS       | ✓ |
| `failAlias_fails` (I2)              | FAIL `ResourceConflict` on the aliased ancilla | ✓ |
| `failThroughput_fails` (I4)         | FAIL batch-slot collision on the factory | ✓ |
| `failDecodeSlow_fails` (I3-decoder) | FAIL `DeadlineMiss` (20 us > 10 us) | ✓ |
| `provisioned_no_backlog` / `underprovisioned_unbounded_backlog` | VM FIFO queue equals `backlogAfter k = k·(arrivals−services)` **number-for-number** at every window boundary | ✓ |

The real failure mode is **comment/statement gaps**: 74 theorems whose formal
content is far weaker than their names/doc-comments claim. Categories:

* **Tautologies by construction** (≈30): `rfl` on a definition sold as verification —
  e.g. `ResourceAuditGaps.ge2021_magic_delivery_uncounted` is literally `27 = 27`;
  `reaction_limited_assumes_decoder` restates its own definition (no iff, no decoder
  condition); the `resource_atom_sound` family in `LayeredArtifactInterface`.
* **Vacuous statements**: `HardwareSensitivity.sensitivity_complete` is `0 ≤ n : Nat`;
  `NaiveSchedule.depsRespected_naive` quantifies over empty dep lists;
  `NaiveUpperBound.naivePeak_le_footprint`'s "peak" can never exceed the footprint by
  construction.
* **Headline overclaims**: `adder_n1_repeated_1000000_symbolic_ok` (README headline) —
  `symbolic_rep_strict_ok` provably **ignores its reps argument** (param `_reps`), so
  the n=10⁶ statement is definitionally identical to n=0; the soundness link to the
  expanded schedule is an open obligation (admitted in §10.n).
* **Fragile-by-coincidence**: `ancilla_freshness_accepts_surgery_ppm_A` passes only
  because the compiler hard-codes site 100 and the checker's hidden "next free site"
  allocator happens to pick 100.
* **Stale self-description**: `CompressedRepeatSoundness`'s header + trailing §8 declare
  obligations open that the file itself closes; `SystemChecker`'s "proposed, NOT
  implemented" blocks are implemented in `SystemInvariantStrengthening`;
  `FaultTolerantSchedule`'s scope notes contradict the current `all_invariants_ok`.

**Highest-risk file for "hallucinated-looking" proofs**: `ResourceAuditGaps.lean` —
findings-documentation encoded as verdict-named tautologies
(`audit_verdict_no_cheat_only_omission`). Recommend renaming to `*_doc`/demoting to
comments.

**Genuinely strong files** (real parametric proofs, honest scope):
`DecoderBacklogModel`, `NaiveSchedule`, `ScheduleLowerBound`,
`CompressedRepeatSoundness`'s shift/seq/repeat lemma core, `SystemChecker` (honest
adversarial self-audit), `SystemInvariantExamples`.

## 2. Syntax/semantics vs the VM

**Agreements** (foundations align): integer µs, absolute times, half-open
`[begin, end)` (pinned by `SystemChecker` boundary tests = VM convention); I2
exclusivity ≡ VM `ResourceConflict`; `SysCall` kinds map onto VM ops/services/tokens;
`MagicStateSpec` ≈ `FactorySpec`; `feedback_after_decode_ok` ≈ result-token chaining;
`ancilla_freshness` ≈ reset discipline (after the lifecycle fix below).

**Lean-side defects the VM exposed (P0 — fix in Lean):**
1. **Declared-duration-only decoder check.** `decoder_react_ok` /
   `DeviceSchedule.reactionRespected` bound each decode's *own declared width*; no
   finite workers, no queue, no submission→completion. 20 simultaneous "1 us" decodes
   on a 1-worker pool pass Lean, miss deadlines in the VM (probe P1).
2. **Zero-duration escape + no well-formedness.** `begin = end` ops are active at no
   instant and escape *every* concurrency check; `end < begin` silently truncates to
   duration 0 (Nat subtraction). Nothing enforces gate durations at all (VM: hardware
   gate table, schedule cannot claim otherwise).
3. **`decoder_queue_depth_at` sampling bug** (`Architecture.lean`): depth is sampled
   only at *transit* boundaries — concurrent decodes with no transits are checked only
   at t=0.
4. **`DependencyGraph.respectsCausality` is index-based**, not id-based: reordering
   the list silently changes which ops the edges denote.
5. **Strict bundles are not supersets**: they build on
   `all_invariants_with_factory_ports_ok`, which *drops* `speed_limit_ok`.
6. **Two sources of truth** for `t_react_us` (ZonedArch field vs free parameter).

**Model-level divergences confirmed by running the VM** (each a `PASS` under the Lean
headline, a violation in the VM):

| probe | Lean blind spot | VM error |
|---|---|---|
| P1 | finite decoder contention | `DeadlineMiss` |
| P2 | syndrome-bus bandwidth/buffer (Channel bandwidth touches only transits, whole-schedule average with +1 ms slack) | `ServiceQueueOverflow` + `DeadlineMiss` |
| P3 | headline has no ancilla freshness | `QubitReuseViolation` |
| P4 / gap§8 | `window_throughput_ok` is demand-rate, not causal supply — magic consumed before distillation completes passes | `TokenUnavailable` |
| gap§4 | Pauli frame before its decode (old bundle) | `TokenUnavailable` |
| gap§6 | ancilla used before any request | `QubitReuseViolation` |

**The fungible-pool conflict.** `RequestFreshAncilla zone` / `RequestMagicState zone`
name a zone, not a site (`syscall_acts_on = []`), and `ancilla_freshness_ok` allocates
by a hidden "next free site" convention — exactly the allocator pattern the VM's
explicit-qubit discipline forbids (`QubitExplicitnessViolation`). Decision needed:
either the SysCall IR gains explicit site arguments (recommended — matches the
stricter design rule "the VM checks concrete schedules, not allocator requests"), or
a compilation pass resolves sites before checking.

**The audit cut both ways — two VM bugs found and fixed via Lean comparison:**
the VM's reset rule was coarser than `AncillaModel`'s clean/dirty lifecycle (gate →
measure inside one block wrongly flagged; fixed with `ZoneSpec.dirty_kinds`), and the
VM missed *use-before-first-request* (fixed with `ZoneSpec.start_dirty`).

**Lean-only concepts the VM lacks** (candidates to adopt or keep Lean-side):
transit/movement with v_max speed limits and channels; per-transit/gate fidelity
accounting (`schedule_fidelity_ppm`); logical↔physical bridge (`LogicalLayout`);
`noDanglingLive` leak detection; derived lower bounds/sensitivity (complementary by
design — the VM checks, Lean derives).

## 3. Where the new system considerations live (and what's missing)

| consideration | exists in Lean | gap |
|---|---|---|
| finite decoders | `DecoderBacklogModel` (steady-state dichotomy — **VM-validated**), `decoderConcurrencyInv`, `operation_capacity_ok` | no transient FIFO/queue checker (the VM's `check_certificate` replay is the blueprint) |
| syndrome bandwidth | `Channel.bandwidth_per_ms` (transits only, broken averaging), `SyndromeMeasurementLatency` (workload counts, no bus) | no service-as-pipe / buffer model |
| ancilla reset | `ancilla_freshness_ok` (§17–19 Strengthening) | order-based not time-based; no reset duration; fungible sites |
| feedforward chaining | `feedback_after_decode_ok` | id-existential; no token identity/ttl/double-consume |
| factory supply | `window_throughput_ok` (demand), `MagicStateReadiness` (supply math) | no causal-supply schedule checker (sketched in SystemChecker §8, unimplemented) |
| gate durations / parallel caps | per-kind caps in `OperationCapacityModel` | **nothing enforces durations**; no global cap |

## 4. Organization: yes, it is too messy — reorganization proposal

> **STATUS: EXECUTED 2026-06-11** (same day, on request). All 38 files moved into the
> folders below (pure moves — no proof or namespace changes; `import` paths rewritten
> in 52 files repo-wide; umbrella `System.lean` regrouped). `lake build` green.
> Deferred to follow-ups: file *splits* (CompressedRepeatSoundness,
> LatticeSurgeryPPMContract, LayeredArtifactInterface), namespace normalization,
> cross-folder moves (StabilizerScheduleVerify → QEC/), constants dedup.

Problems: (a) **namespace drift** — many files declare `FormalRV.Framework.*` or
`FormalRV.LatticeSurgery.*` while living in `System/`; (b) **two parallel checker
stacks** (SysCall lane vs DeviceOp lane) duplicating five concerns, "connected by
theorems, not merged"; (c) **tick-accretion monsters**: `CompressedRepeatSoundness`
(4 517 lines, scrambled §-numbering, stale header+status), `LatticeSurgeryPPMContract`
(1 329 lines, 3 topics, 3 retrospectives), `LayeredArtifactInterface` (1 244 lines,
§10 subsystem dwarfs the file's topic), `SurgeryGadgetToSysCalls` (stray §14 after
§19); (d) RSA-2048 constants re-typed in ≥3 files; demo objects mirrored in 2;
(e) **dead code**: `HardwareErrorParams` is never consumed; several lineage-only
imports; (f) `StabilizerScheduleVerify` is QEC content, not scheduling.

Proposed layout (≈9 folders, no proofs change, imports + namespaces normalized to
`FormalRV.System.*`):

```
System/
  Core/        Architecture, CodedLayout, ScheduleCombinators (extract from PPMContract)
  Invariants/  ScheduleInvariantsExplicit, InvariantFramework,
               SystemInvariantStrengthening (restructured, stale headers fixed)
  Checkers/    SystemChecker (gap audit), FaultTolerantSchedule
  DeviceLane/  DeviceSchedule, RoutingResourceModel, DependencyGraph(checker half)
               — or better: merge into Invariants/ behind one IR
  Decoder/     DecoderBacklogModel, DecodeLatencySensitivity,
               ReactionLimitedRuntime, SyndromeMeasurementLatency
  Magic/       MagicStateReadiness, MagicScheduleComplete
  Bounds/      ScheduleLowerBound, NaiveSchedule, NaiveUpperBound, ScheduleBounds,
               HardwareSensitivity, DependencyGraph(critical-path half), ScheduleAdvance
  Compile/     SurgeryGadgetToSysCalls, LatticeSurgeryPPMContract(cert core),
               SurfaceSystemCompile, SurfaceShorFullSchedule
  Artifacts/   LayeredArtifactInterface(core), CompressedSchedule (split out),
               CompressedRepeatSoundness, ExternalCertificates
               ← natural home for the future Lean checker of the FTQ-VM certificate
  Examples/    SystemInvariantExamples, AdderSystem, ParallelismVerification(demos),
               CostModelWeightDemo
  Params/      HardwareParams (single source), ZoneBudget;
               HardwareErrorParams: move to Framework/ with a consumer, or delete
StabilizerScheduleVerify → QEC/ or PPM/.
Shared RSA-2048 constants → one module.
```

**Strategic recommendation.** The convergence point is the **VM certificate**:
`LayeredArtifactInterface` already exists so "Lean- or Python-generated schedules
target the same checkers". Port `ftq_vm/backend/check_certificate.py` (deliberately
boring stdlib loops) into `System/Artifacts/` as the Lean predicate
`CheckCertificate`, and retire the per-invariant Bool bundles in favor of
re-verifying the closed certificate — that gives `CheckCertificate cert = true →
ValidFiniteServiceSchedule` with the VM as the fast untrusted producer and Lean as
the small trusted checker, which was the design goal all along.
