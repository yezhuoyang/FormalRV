# FTQ-VM — a Fault-Tolerant Quantum Virtual Machine

A **discrete-event simulator / checker for finite-service resource contracts**
in fault-tolerant quantum computation.

FTQ-VM is **not** a quantum-amplitude simulator. It never touches state
vectors. It is closer to *QEMU + an OS scheduler + a resource profiler* for
fault-tolerant quantum programs: it executes a concurrent trace of
logical/QEC/system calls against a backend description of finite resources,
checks every finite-service constraint, and reports *where and why* a
resource estimate fails — decoder queues, token freshness, factory ports,
correction storage, feedforward deadlines — not just whether average rates
balance.

```
Compiler / scheduler ──► FTQ-VM execution & profiling ──► certificate.json
                                                              │
                                       check_certificate.py / Lean checker
                                                              │
                                  theorem: finite-service constraints satisfied
```

## What it checks

| constraint                  | error kind                                  |
|-----------------------------|---------------------------------------------|
| exclusive resource conflicts | `ResourceConflict`                          |
| capacity overuse (zones, buses, storage, ancilla pools) | `CapacityExceeded` |
| token consumed before production | `TokenUnavailable`                      |
| token consumed after its freshness window | `TokenFreshnessViolation`      |
| token buffer overflow (e.g. T-state buffer) | `TokenBufferOverflow`        |
| token consumed twice        | `DoubleConsume`                             |
| service queue overflow (e.g. decoder backlog) | `ServiceQueueOverflow`     |
| service bandwidth violations | `ServiceCapacityExceeded`                  |
| feedforward / decode deadline misses | `DeadlineMiss`                     |
| dependency ordering         | `DependencyViolation`, `UnknownDependency`  |
| anonymous / fungible qubit requests | `QubitExplicitnessViolation` (rejected at load) |
| qubit reused without an explicit timed reset | `QubitReuseViolation`      |
| malformed/impossible requests | `InvalidInterval`, `AllocationError`, `UnknownResource` |

## Design philosophy

The core VM is **architecture-neutral**: it only understands generic finite
resources (`exclusive` / `capacity` / `shared` use over half-open time
intervals), finite-worker FIFO **services** (workers, latency deadline,
queue capacity, bandwidth), **tokens** produced/consumed over time (buffers,
ttl), and **dependencies**. Surface code, QLDPC, superconducting and
neutral-atom hardware are all just backend YAML files. Nothing
surface-code-specific is hard-coded in the simulator.

Even **T factories are compiled down** to these primitives (`factory.py`):
every factory run becomes a generic op that occupies a batch slot, reserves
the factory's exact qubit footprint, holds an output port and (on success)
produces a token — so footprint collisions, port conflicts, slot
oversubscription and buffer overflows are caught by the same generic
checkers.

## Qubits are never fungible

> **The VM checks concrete schedules, not allocator requests. Qubits are
> non-fungible named resources. Zone/array declarations are allowed only as
> source syntax for declaring arrays — never as executable qubit
> allocation.**

A syndrome-extraction step is not "use one syndrome qubit"; it is *s₇
interacts with d₃, d₄, d₁₀, d₁₁ at this exact time*. Likewise a T factory is
not "consume 20 000 physical qubits from a pool"; it *occupies this exact
region for this time interval*. The input system enforces this as a hard
validity rule:

* qubits live in **zones**; a zone of count *n* expands to explicit
  capacity-1 resources `data[0] … data[n-1]`;
* every op that touches qubits must name exactly which ones
  (`qubits: [data[3], syndrome[7]]`) — they are held **exclusively**;
* `uses: {some_qubit_pool: 1}` ("give me one ancilla") is rejected at load
  time with a `QubitExplicitnessViolation`, as is any resource declaring a
  qubit-like kind (`*qubit*`, `*ancilla*`) with capacity > 1;
* the backend lists which `do:` kinds are qubit-touching
  (`qubit_touching_kinds`); an op of such a kind without explicit qubit IDs
  is invalid;
* factories must declare an explicit fixed `footprint` (see below);
* non-qubit resources (decoder pools, buses, classical storage, token
  buffers) remain abstract capacity pools — only qubits are special.

Runtime exclusivity is then checked per qubit by the ordinary sweep: two ops
overlapping on `syndrome[7]`, or a workload op touching `magic[17]` while a
factory run holds it, are reported as `ResourceConflict` with the exact ops
and interval.

## System-level modeling patterns

Three patterns the model is built to express (all live in
`demo_system_backend.yaml` + `demo_system_bugs.yaml`):

* **Finite decoders with latency** — a `kind: service` resource: `workers`
  decoders, per-job `processing_time_us`, FIFO queue bounded by
  `queue_capacity`, and a `max_latency_us` reaction deadline. A worker is
  OCCUPIED for the full decode latency and freed exactly when it finishes
  (half-open), then reusable by the next syscall. With
  `queue_capacity: 0` the service becomes a strict-occupancy contract —
  semantically identical to the Lean checker's `active decodes ≤ workers`
  — and both tools report `DECODER_OVERLOAD` on the same schedules:
  corpus e21 (6 × 1 ms decodes through 2 workers in back-to-back pairs,
  PASS — reuse at exactly t=1000 works), e22 (a third decode mid-flight,
  FAIL), e23 (reuse 1 µs early at t=999, FAIL); proven live in Lean by
  `decoder_paced_reuse_accepted` / `decoder_premature_reuse_rejected`
  on the `adder_d3_strictDecoder` catalog machine.
* **Finite-bandwidth syndrome bus + syndrome buffer** — a bus is *also* a
  service, used as a pipe: `workers` = parallel lanes, `processing_time_us`
  = transfer time per syndrome packet, and the service queue **is** the
  syndrome buffer (`queue_capacity` = buffer slots). When many logical
  qubits are measured at once, packets pile up in the buffer
  (`ServiceQueueOverflow`) and arrive late (`DeadlineMiss`) — even while the
  decoders behind the bus sit idle. Stage chaining is explicit: a job with
  `result_token: SyndromeAtDecoder` produces that token *at its computed
  completion time*, so a decode op consuming it earlier is caught by the
  token ledger (`TokenUnavailable: ... produced at t=...`). Chain
  bus → decoder → controller this way to check end-to-end reaction times.
* **Qubit reuse needs explicit, timed reset** — a zone with
  `reset_required: true`, `reset_kinds: [reset]`, `min_reset_us: N`:
  between two different ops using the same qubit there must be a reset op
  holding that qubit for at least `N` us, or the run reports
  `QubitReuseViolation` (also when the reset is too short). No qubit is
  reusable "immediately".
* **Syndrome-stream bandwidth (bit accounting)** — QEC produces a
  continuous stream of syndrome data; the classical link to the decoder is
  finite. The backend declares a windowed data-volume cap
  (`throughput_caps`: e.g. `{"op_kinds": ["measure"], "weight_per_op": 64,
  "window_us": 1000, "max_weight": 32768}` = **4 KB/ms**, with 64 bits =
  8 stabilizers × 8-bit soft readout per d=3-patch measurement). The VM
  *counts the actual bits* injected by measurements in every
  measurement-anchored window and reports `ThroughputExceeded`
  (canonical code `SYNDROME_BANDWIDTH`) with the arithmetic spelled out
  ("40 × 16 × 64 = 40960 bits in [0,1000)us exceeds 32768"). The Lean
  System layer runs the IDENTICAL check (`syndrome_bandwidth_ok`, invariant
  I5, same window-anchoring rule), proven live by
  `HardwareCatalog.syndrome_flood_rejected` / `syndrome_paced_accepted`;
  corpus rows e19/e20 assert both checkers agree literally (a 4×4 d=3
  surface tile at a 25 µs round cadence breaks the 4 KB/ms link; at 40 µs
  it fits).
* **Hardware gate times + finite control parallelism** (see
  `demo_gates_backend.yaml` + `demo_gates_bugs.yaml` / `demo_gates_fixed.yaml`)
  — the backend's `gates:` table sets each gate kind's hardware duration
  (`CNOT: {duration_us: 1000, qubits: 2}`): an op `do: CNOT` gets its
  duration from the table, the reported runtime honestly includes it, and a
  schedule claiming a different duration is **rejected** — gate times are
  hardware facts, not schedule choices. `qubits: 2` also forces exact arity
  in explicit qubits. Finite control electronics are modeled by
  `max_parallel_gates: N` (one FPGA cannot drive gates on a million qubits
  at once) and per-kind `max_parallel` (e.g. the number of AODs / lattice
  sites per AOD in neutral atoms), plus per-gate `uses:` (readout lines,
  AWG channels) charged for the gate's duration. All of it lowers to
  capacity resources, so violations surface as `CapacityExceeded` on
  `gates.parallel` / `gate.CNOT.parallel` / `readout_lines` naming the
  colliding ops. Omit the caps and parallelism is unconstrained — the user
  models the bottleneck only if their hardware has one.

## Units

One global time unit: **integer microseconds**. Every time field carries the
`_us` suffix (`at_us`, `duration_us`, `max_latency_us`, `ttl_us`, ...).
Backend files must declare `unit: {time: us}`; bare time keys without `_us`
are rejected at load time. No silent unit mixing, ever.

All intervals are half-open `[start_us, end_us)` — a use ending at `t` does
not overlap a use starting at `t`.

## T factories are really simulated

A factory run takes **space** (its exact, fixed qubit footprint plus one of
`max_parallel_batches` batch slots), **time** (`duration_us`, optional
`cooldown_us`) and **fails stochastically** (`success_probability`):

* **stochastic mode** (default): outcomes drawn from a seeded PRNG
  (`--seed`, default 0). The same seed always reproduces the same trace.
* **conservative mode** (`--factory-mode conservative`): no randomness — a
  factory with success probability `p` succeeds exactly on every
  `ceil(1/p)`-th attempt, a pessimistic guaranteed-production contract.

Failed runs emit `factory_failed` events and (with `auto_retry`) retry after
the cooldown, up to `max_retries` times. The run report distinguishes the
*average* factory rate, the *realized stochastic trace*, and the
*conservative contract* — exactly the gap where average-rate resource
estimates go wrong (see `demo_factory_starvation.yaml`).

Every factory must declare a fixed **footprint**: each run reserves
`footprint.qubits` (and `footprint.buffer`) **exclusively for the whole
run**, and on success holds `footprint.output_ports` during the emission
microsecond. If any workload op or other factory touches a footprint qubit
mid-run, the exclusivity checker reports the conflict. `physical_qubits` /
`logical_slots` are statistics annotations only — execution never charges a
fungible pool.

## Quick start

```bash
pip install -r ftq_vm/requirements.txt

# colorful run summary + trace/stats/certificate JSON
python -m ftq_vm run ftq_vm/backend/examples/backend_simple.yaml \
                     ftq_vm/backend/examples/program_buggy.yaml --out out/

# interactive terminal UI (tabs, timeline, trace search, error inspector)
python -m ftq_vm tui ftq_vm/backend/examples/backend_simple.yaml \
                     ftq_vm/backend/examples/program_fixed.yaml

# independently re-verify a certificate (no simulator involved)
python -m ftq_vm check-cert out/certificate.json

# list bundled examples
python -m ftq_vm examples
```

(Run from the directory *containing* `ftq_vm/`. On legacy Windows consoles
set `PYTHONUTF8=1` for crisp box drawing.)

Exit codes: `0` pass, `1` violations found, `2` could not load inputs.

### The TUI

`python -m ftq_vm tui ...` opens a Textual app with tabs:

* **Dashboard** — pass/fail, runtime, factory/token/resource/service tables;
* **Timeline** — one sparkline lane per op-kind / resource / service queue /
  token buffer over time, red `✖` markers for errors, `←/→` pan, `+/-` zoom;
  below it an op table — select a row to inspect details and related errors;
* **Trace** — every event (time, kind, severity, op, component, message)
  with live substring filtering, `e` toggles errors-only, row select shows
  full details;
* **Resources** — pick a resource, see its usage sparkline against the
  capacity line with overloads in red, plus its errors;
* **Tokens** — buffer occupancy over time, production/consumption counts,
  freshness/starvation errors;
* **Services** — queue length and busy-worker sparklines, overflow and
  deadline misses;
* **Factories** — per-run strip (`■` success / `✖` failure), full run table;
* **Errors** — every violation as a colored panel with explanation and a
  suggested fix.

## Input format

### Backend (what the machine offers)

```yaml
unit:
  time: us                     # mandatory; MVP supports microseconds only

zones:                         # qubit arrays -> explicit capacity-1 resources
  data:     {kind: data_qubit, count: 64}        # data[0] ... data[63]
  syndrome: {kind: syndrome_qubit, count: 16}
  magic:    {kind: factory_qubit, count: 72}
  tport:    {kind: output_port, count: 4}

resources:                     # NON-qubit resources; 'kind' discriminates
  measurement_bus: {kind: bus, capacity: 64}
  t_buffer:       {kind: token_buffer, token_kind: TState, capacity: 512}
  decoder_pool:   {kind: service, workers: 256, max_latency_us: 10,
                   queue_capacity: 100000, processing_time_us: 2}

qubit_touching_kinds: [magic_inject, syndrome_round, logical_measure]

factories:
  F0:
    kind: T_factory
    produces: TState
    duration_us: 50
    success_probability: 0.9
    footprint:                 # REQUIRED: the exact region each run occupies
      qubits: ["magic[0:18]"]
      output_ports: ["tport[0]"]
    physical_qubits: 20000     # statistics annotation only
    max_parallel_batches: 1
    auto_retry: false          # retry after cooldown_us, up to max_retries

tokens:
  TState: {initial_inventory: 8, ttl_us: 10000}
```

`kind: service` entries become finite-worker FIFO services; `kind:
token_buffer` entries bound a token kind's buffer; everything else is a
countable (non-qubit) resource. Resources with qubit-like kinds and
capacity > 1 are rejected — qubits go in `zones:`.

### Program (the declared schedule)

The MVP checks **declared schedules**: every op has an explicit `at_us` and
`duration_us` (≥ 1). Automatic scheduling can come later.

```yaml
program: toy_shor_like
ops:
  - {id: run_F0, do: start_factory, factory: F0, at_us: 0,
     repeat: {every_us: 50, until_us: 450}}      # instances run_F0@0..@9

  - id: t_inject
    do: magic_inject
    at_us: 60
    duration_us: 10
    consume: TState             # oldest fresh token, FIFO
    qubits:                     # EXPLICIT qubits, held exclusively;
      target: ["data[0]"]       # role mapping (roles -> metadata) ...
      routing: ["data[1]"]
    repeat: {every_us: 20, until_us: 360}

  - id: syndrome_round
    do: syndrome_round
    at_us: 100
    duration_us: 10
    qubits: ["syndrome[0:16]"]  # ... or a flat list; zone[a:b] is half-open
    service: {service: decoder_pool, count: 1024, processing_time_us: 1}
    repeat: {every_us: 10, until_us: 190}

  - id: final_readout
    do: logical_measure
    at_us: 200
    duration_us: 10
    deps: [syndrome_round@9]    # dep must end at or before at_us
    qubits: ["data[8:24]"]
    uses: {measurement_bus: 16} # non-qubit resources: amount-based is fine;
                                # naming a service submits that many jobs
```

Qubit references: `data[3]`, `data[0:16]` (half-open, like every interval in
the VM), `data[0,2,5]`. Quote them inside YAML flow lists (`["data[3]"]`).
Richer forms when you need them: `uses` as a list of
`{resource, mode: exclusive|capacity|shared, amount, start_us, end_us}`
(offsets relative to the op; zone refs allowed and default to exclusive),
`consume: [{kind: TState, count: 2}]` or `{id: specific_token}`,
`produce: [{kind: X, count: 16, at_us: 5, ttl_us: 100}]`. Unknown op keys
land in `op.metadata`.

## Examples

| files | what they show |
|---|---|
| `backend_simple.yaml` + `program_buggy.yaml` | toy Shor-like workload with three intentional bugs: TState starvation, a decoder-queue overflow (`queue length 100001 exceeds capacity 100000`) with deadline-miss cascade, and a measurement-bus capacity violation (65 > 64) |
| `backend_simple.yaml` + `program_fixed.yaml` | the same workload repaired — passes |
| `backend_simple.yaml` + `program_invalid.yaml` | asks for "one syndrome qubit" anonymously — rejected at load with `QubitExplicitnessViolation` (exit 2) |
| `demo_backend.yaml` + `demo_factory_starvation.yaml` | **average T throughput is sufficient** (1 per ~29.4us produced vs 1 per 29us consumed) yet seeded factory failure streaks starve the buffer — the gap between average-rate estimates and finite-service contracts |
| `demo_backend.yaml` + `demo_buffer_overflow.yaml` | healthy factories overflow an undersized 12-token T buffer |
| `demo_backend.yaml` + `demo_fixed.yaml` | the starvation workload repaired by delaying/spacing consumers — passes |

## Outputs

`python -m ftq_vm run ... --out out/` writes:

* **`trace.json`** — every event, sorted: `op_start/op_end`,
  `resource_reserved/released`, `token_produced/consumed`,
  `service_job_submitted/started/completed`,
  `factory_started/succeeded/failed/retry_scheduled`, `error`; each with
  `time_us`, `severity`, the involved op/resource/token/service/factory and
  a human message. (Services with >500 jobs aggregate to batch events.)
* **`stats.json`** — `total_runtime_us`, per-resource peak/utilization,
  token produced/consumed/peak-buffer, service utilization / max queue /
  deadline misses, factory attempts/successes/failures/retries/utilization,
  errors by kind, bottlenecks.
* **`certificate.json`** — see below.

## The shared DEVICE-PROGRAM syntax (Lean ↔ VM interop)

Programs can also be written in **DEVICE-PROGRAM 1.0** — the timestamped
textual schedule syntax that the Lean System layer natively emits
(`FormalRV/Codegen/SysCallEmit.lean`) *and parses back*
(`FormalRV/Codegen/DeviceProgramParse.lean`), and that this VM loads
directly (`.dp` files or content sniff):

```
DEVICE-PROGRAM 1.0;
// adder-2bit-cuccaro d=3 surgery schedule
[0,1)us  SYS   request_ancilla    q[100]
[1,2)us  PHYS  gate2q             q[0],q[100] gate=CNOT
[2,3)us  PHYS  gate2q             q[50],q[100] gate=CNOT
[3,4)us  PHYS  measure            q[100] basis=Z
[4,5)us  SYS   decode_syndrome    round=0
...
[15,16)us  SYS   pauli_frame_update corr=0
```

Three explicitness rules are enforced by BOTH parsers: **gates are named**
(`gate=CNOT`, `basis=Z` — never a numeral), so each checker verifies the
gate is *supported* by the backend gate table and takes exactly its
hardware time; **ancilla requests name their exact qubit**
(`request_ancilla q[100]` — the fungible `zone=` form does not exist; the
Lean `SysCallKind.RequestFreshAncilla` itself carries the site); and
**parallel layers are recognized after parsing** — ops sharing the same
`[b,e)us` window form one simultaneous layer (Lean `parallelGroups` /
VM `parallel_groups`, identical exact-interval rule; grouped ops carry
`metadata.parallel_group`).

One schedule file, two independent checkers: the Lean decidable invariant
bundle (the same `Bool` functions the `native_decide` theorems certify, run
on the parsed file) and this VM's discrete-event finite-service check.
`q[s]` sites are global Lean site numbers; each backend zone declares
`site_lo`, so they lower to explicit zone qubits.
`decode_syndrome round=r` becomes a decoder-service job producing the token
`decode<r>` at its computed completion; `pauli_frame_update corr=c` consumes
it — feedforward causality via the ledger.

The worked cross-checked example (the 2-bit Cuccaro adder on distance-3
surface code, 12 surgery merge blocks × 3 syndrome rounds, 192 SysCalls):

```bash
# generate from the Lean schedule objects (also writes the bad variant)
lake env lean --run scripts/EmitAdderDeviceProgram.lean
# Lean side: parse the SAME files, run the strict bundle  → PASS / FAIL
lake env lean --run scripts/CheckDeviceProgram.lean
# VM side: same files                                      → PASS / FAIL
python -m ftq_vm run ftq_vm/backend/examples/adder_d3_backend.json \
                     ftq_vm/backend/examples/adder_d3.dp
python -m ftq_vm run ftq_vm/backend/examples/adder_d3_backend.json \
                     ftq_vm/backend/examples/adder_d3_bad.dp
```

Verdicts agree on both files (PASS / FAIL), with matching runtime (192 µs),
op counts, parallel-layer statistics, and — on the bad variant — the same
single failure reason (two simultaneous CNOTs exceed the CNOT cap of 1).

**Hardware is configured in ONE place**: the backend JSONs above are
GENERATED from `FormalRV/System/Params/HardwareCatalog.lean` (the single
file holding every hardware assumption — zones, gate tables, decoder,
windows; `HardwareSpec.toBackendJson` renders the VM file, and the same
spec derives every Lean checker input). Reconfiguration is live in both
tools: the parallel-adder schedule fails on `adder_d3` (CNOT cap 1) and
passes on `adder_d3_dualRail` (cap 2) — proven in Lean by `native_decide`
and reproduced by the VM on `adder_d3_dualrail_backend.json`.

### The differential error corpus

`ftq_vm/backend/examples/corpus/` holds 18 concrete examples over 5
hardware configurations whose triggered errors range over the shared error
space, run through BOTH checkers (`scripts/EmitErrorCorpus.lean` generates;
`scripts/CheckErrorCorpus.lean` asserts the Lean side;
`tests/test_error_corpus.py` the VM side).

**Both checkers report violations in ONE shared vocabulary** — the
canonical contract codes (`device_program.CONTRACT_CODES`, mirrored in
`Codegen/DeviceProgramParse.lean` §4), named after the violated hardware
contract: `QUBIT_EXCLUSIVITY`, `GATE_PARALLELISM`, `GATE_UNSUPPORTED`,
`GATE_DURATION`, `ARCH_BOUNDS`, `QUBIT_LIFECYCLE`, `DECODER_OVERLOAD`,
`DECODER_REACTION`, `FEEDFORWARD_CAUSALITY` / `_LATENCY` / `_FRESHNESS`,
`MAGIC_DEMAND_WINDOW`, `ZONE_CAPACITY`, `FACTORY_PORT_EXCLUSIVITY`,
`MAGIC_SUPPLY`, `SYNTAX`. The corpus asserts the reported reasons are
LITERALLY IDENTICAL on every example outside the five documented model
gaps (`test_reasons_identical_outside_known_gaps`): Lean-only checks
`QUBIT_LIFECYCLE` leak/double-alloc (e13/e14), `MAGIC_DEMAND_WINDOW`
(e15), `FEEDFORWARD_LATENCY` (e16); VM-only check
`FEEDFORWARD_FRESHNESS` (e17). One code keeps a documented mechanism
nuance: `DECODER_OVERLOAD` is concurrency-vs-workers in Lean and queue
overflow in the VM — the same finite-decoder contract, checked two ways.
Known deltas (each checker is stronger somewhere): the VM additionally
enforces decoder queueing/deadlines; Lean additionally checks the
dangling-Live (leaked-ancilla) rule, double-allocation of a Live ancilla,
and the factory window-throughput demand cap.  Gate support + durations are
now checked by BOTH (Lean `gate_support_ok`, VM gate table).

## The certificate and Lean

`certificate.json` is a self-contained, fully-resolved description of the
run: canonical sha256 hashes of the inputs, every op interval **with its
declared uses/consumes/produces/service-jobs at absolute times**, every
per-resource use interval, the chronological token event order, every
service batch, every factory run with its (already-resolved) outcome, the
claimed peaks/queue bounds, the error list and the verdict.

`check_certificate.py` re-verifies all of it **independently of the
simulator** with deliberately boring loops — sweep the resource intervals,
replay the token ledger, replay the FIFO queue recurrence, and cross-check
that declarations and realized events agree exactly (a *pass* certificate is
"closed": no hidden or dropped work). Every check is designed to have a
direct Lean predicate later:

```
theorem checked_certificate_sound :
  CheckCertificate cert = true →
  ValidFiniteServiceSchedule backend cert.schedule
```

The fast Python VM is untrusted; the small checker (and later its Lean port)
is the trusted part. The intended claim is deliberately scoped: *if the
backend's service contract is valid, this program respects all
finite-service constraints and has runtime T* — backend contracts themselves
(surface code, QLDPC, hardware) are justified separately.

## Tests

```bash
python -m pytest ftq_vm/backend/tests -q
```

Covers exclusive-overlap detection, capacity overuse, token
freshness/double-consume/starvation/buffer bounds, FIFO service schedules,
queue overflow, deadline misses, factory determinism/retry/ports/space,
loader syntax (including `_us` enforcement), certificate round-trips and
tampering, the bundled examples end-to-end, the CLI exit codes and the
FastAPI endpoint.

## Repo layout

```
ftq_vm/
  __main__.py                  # python -m ftq_vm
  backend/
    models.py                  # typed pydantic models (the data contract)
    loader.py                  # friendly YAML -> internal models; unit enforcement
    factory.py                 # stochastic factory layer (compiles to generic ops)
    checker.py                 # resource / token / service / dependency checkers
    simulator.py               # orchestration: expand, check, merge trace
    stats.py                   # runtime & resource statistics
    certificate.py             # closed, Lean-checkable certificate export
    check_certificate.py       # small independent re-checker (Lean blueprint)
    report.py                  # colorful Rich console report
    tui.py                     # interactive Textual TUI
    cli.py                     # run / tui / check-cert / examples
    main.py                    # optional FastAPI (programmatic access)
    examples/                  # backends, buggy/fixed programs, factory demos
    tests/
  requirements.txt
  README.md
```

## Scope honesty

FTQ-VM verifies **finite-service feasibility under an explicit backend
contract**. It does not prove physical implementability on a real chip, does
not simulate amplitudes or Pauli noise, and (in this MVP) checks declared
schedules rather than synthesizing them — the OS/VM is not an allocator.
Layer-1 physical gates (pulses, shuttling) are expressible as backend
configs but intentionally not built in, and connectivity correctness (which
data qubit couples to which syndrome qubit) belongs to a per-architecture
backend plug-in / layout checker, not the architecture-neutral core.

One scaling note: explicit qubits multiply event counts (a zone of 10⁵
qubits × 10⁴ rounds is 10⁹ intervals). Model the contended regions you are
debugging at qubit granularity and keep truly classical bulk (decoder jobs,
classical storage) as services/pools; periodic-interval compression for
steady-state QEC rounds is future work.
