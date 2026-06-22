"""Typed data models for the FTQ-VM.

Design philosophy
-----------------
The core VM is *architecture neutral*.  It only understands generic finite
resources, finite services, tokens produced/consumed over time, dependencies
and time intervals.  Surface-code lattice surgery, QLDPC, superconducting or
neutral-atom hardware are all expressed as *backend configurations* built out
of these primitives -- never hard-coded here.  Even T factories are a thin
layer that *compiles down* to generic ops, uses and token productions (see
``factory.py``).

Units
-----
Time is a single global unit: **integer microseconds**.  Every field that
represents a time carries the ``_us`` suffix; the backend config must declare
``unit: {time: us}`` (the loader rejects anything else).  Mixed units are
never silently converted.

Conventions
-----------
* All intervals are half-open ``[start_us, end_us)``: a use ending at ``t``
  does not overlap a use starting at ``t``.
* Inside an :class:`Op`, resource-use and token times are *relative to the
  op's start*; the simulator resolves them to absolute times.
"""

from __future__ import annotations

import enum
import re
from typing import Any, Literal, Optional

from pydantic import BaseModel, ConfigDict, Field, model_validator


# --------------------------------------------------------------------------
# Primitives
# --------------------------------------------------------------------------


class TimeInterval(BaseModel):
    """Half-open time interval ``[start_us, end_us)``.  Invariant: start < end."""

    start_us: int = Field(ge=0)
    end_us: int = Field(ge=0)

    @model_validator(mode="after")
    def _check_order(self) -> "TimeInterval":
        if self.start_us >= self.end_us:
            raise ValueError(
                f"TimeInterval requires start < end, got [{self.start_us}, {self.end_us})")
        return self

    def overlaps(self, other: "TimeInterval") -> bool:
        return self.start_us < other.end_us and other.start_us < self.end_us

    @property
    def duration_us(self) -> int:
        return self.end_us - self.start_us


class UseMode(str, enum.Enum):
    """How an op uses a resource.

    * ``exclusive`` -- the op needs the whole resource; conflicts with ANY
      other concurrent use of the same resource (any mode).
    * ``capacity``  -- the op uses ``amount`` units; the sum of concurrent
      capacity amounts must stay within capacity.
    * ``shared``    -- read-only style use; never counts against capacity,
      but still conflicts with an exclusive hold.
    """

    exclusive = "exclusive"
    capacity = "capacity"
    shared = "shared"


class UnitSpec(BaseModel):
    """Global unit declaration.  The MVP supports microseconds only."""

    time: Literal["us"] = "us"


# --------------------------------------------------------------------------
# Backend configuration
# --------------------------------------------------------------------------


class ResourceSpec(BaseModel):
    """A finite, countable resource (port, bus, storage, classical pool, ...)."""

    id: str
    kind: str
    capacity: int = Field(default=1, ge=1)
    description: Optional[str] = None


#: ``zone[3]``, ``zone[0:5]`` (HALF-OPEN, like every interval in the VM:
#: qubits 0..4) or ``zone[0,2,5]``
_QUBIT_REF_RE = re.compile(r"^([A-Za-z_][\w.-]*)\[([0-9:,\s]+)\]$")


#: refuse to materialize absurd ranges (typo guard: data[0:999999999])
MAX_QUBIT_REF_INDICES = 1_000_000


def parse_qubit_ref(ref: str) -> Optional[tuple[str, list[int]]]:
    """Parse an explicit qubit reference into ``(zone, indices)``.

    ``'anc[3]'`` -> ``('anc', [3])``; ``'anc[0:5]'`` -> ``('anc',
    [0,1,2,3,4])`` (half-open, consistent with time intervals);
    ``'anc[0,2,5]'`` -> ``('anc', [0,2,5])``.  Returns ``None`` if ``ref``
    is not a qubit reference or spans more than
    :data:`MAX_QUBIT_REF_INDICES` indices (sizes are checked before any
    range is materialized).
    """
    m = _QUBIT_REF_RE.match(ref)
    if m is None:
        return None
    zone = m.group(1)
    parts: list[tuple[int, int]] = []  # half-open (a, b) pieces
    total = 0
    for part in m.group(2).split(","):
        part = part.strip()
        if not part:
            return None
        if ":" in part:
            try:
                a_str, b_str = part.split(":")
                a, b = int(a_str), int(b_str)
            except ValueError:
                return None
            if b <= a:
                return None
        else:
            try:
                a = int(part)
                b = a + 1
            except ValueError:
                return None
        parts.append((a, b))
        total += b - a
        if total > MAX_QUBIT_REF_INDICES:
            return None
    if not parts:
        return None
    indices: list[int] = []
    for a, b in parts:
        indices.extend(range(a, b))
    return (zone, indices)


class ZoneSpec(BaseModel):
    """A named array of individually-addressable capacity-1 resources.

    Zones are THE way to model qubits (and other addressable units such as
    factory output ports).  Every element becomes its own capacity-1
    resource named ``<zone>[<i>]``.  **Qubits are never fungible in the
    executable schedule**: any operation that touches qubits must name
    explicit indices (``qubits: [data[3], anc[0:5]]``) and holds them
    exclusively.  Anonymous, amount-based use of a zone is invalid -- the
    scheduling program must say *which* qubit, in *which* zone, at *which*
    time.  Zone declarations are source-level sugar only; after loading,
    everything is explicit capacity-1 resources.
    """

    id: str
    kind: str = "qubit"
    count: int = Field(ge=1)
    #: interop metadata: the Lean System layer numbers sites globally
    #: (``q[137]``); a zone with ``site_lo = 100`` owns sites
    #: ``[site_lo, site_lo + count)`` and ``q[137]`` maps to ``<zone>[37]``.
    #: Used by the DEVICE-PROGRAM loader; ignored elsewhere.
    site_lo: Optional[int] = Field(default=None, ge=0)
    #: if true, this zone's qubits follow a clean/dirty lifecycle: an op whose
    #: kind is in dirty_kinds leaves the qubit dirty, and any LATER op may not
    #: touch it until an explicit reset op (kind in reset_kinds, holding the
    #: qubit for at least min_reset_us) has run -- helper/ancilla qubits
    #: cannot be reused immediately
    reset_required: bool = False
    #: op kinds that count as reset/reload for this zone's qubits
    reset_kinds: list[str] = Field(default_factory=lambda: ["reset"])
    #: op kinds that leave the qubit dirty.  None (default) = EVERY non-reset
    #: op dirties the qubit (most conservative); ["measure"] gives the
    #: measurement-collapses lifecycle where gates on a live qubit are fine.
    dirty_kinds: Optional[list[str]] = None
    #: if true, qubits start DIRTY: they may not be used at all before a
    #: first reset/request op (an unrequested ancilla is undefined)
    start_dirty: bool = False
    #: a reset op must hold the qubit for at least this long
    min_reset_us: int = Field(default=1, ge=1)
    description: Optional[str] = None

    def qubit_id(self, i: int) -> str:
        return f"{self.id}[{i}]"


def is_qubit_like_kind(kind: str) -> bool:
    """Resource kinds that denote qubits (and therefore must be zones)."""
    k = kind.lower()
    return "qubit" in k or "ancilla" in k


class ServiceSpec(BaseModel):
    """A finite-worker service (decoder pool, routing engine, ...).

    Jobs submitted to the service wait in a FIFO queue, are processed by one
    of ``workers`` identical workers, and must complete within
    ``max_latency_us`` of submission or a :class:`VMErrorKind.DeadlineMiss`
    is reported.  The queue (jobs submitted but not yet started) may hold at
    most ``queue_capacity`` jobs.
    """

    id: str
    kind: str = "service"
    workers: int = Field(ge=1)
    max_latency_us: int = Field(ge=0)
    queue_capacity: int = Field(ge=0)
    input_bandwidth: Optional[int] = Field(default=None, ge=1,
                                           description="max jobs accepted per microsecond")
    output_bandwidth: Optional[int] = Field(default=None, ge=1,
                                            description="max jobs completed per microsecond")
    description: Optional[str] = None


class FactoryFootprint(BaseModel):
    """The exact, fixed set of resources a factory run occupies.

    A T factory is not "20000 physical qubits from a pool" -- it is *this
    exact region for this time interval*.  Entries are explicit qubit
    references (``factory_F0[0:18]``) or capacity-1 resource ids:

    * ``qubits``       -- reserved exclusively for the WHOLE run (required);
    * ``buffer``       -- ditto (e.g. staging/buffer slots modeled as a zone);
    * ``output_ports`` -- reserved exclusively during the final microsecond
      of a SUCCESSFUL run (the emission claims the port).
    """

    qubits: list[str] = Field(min_length=1)
    output_ports: list[str] = Field(default_factory=list)
    buffer: list[str] = Field(default_factory=list)


class FactorySpec(BaseModel):
    """An active, simulated token factory (e.g. a T-state factory).

    A factory *run* (one batch attempt):

    * occupies one of ``max_parallel_batches`` batch slots for
      ``duration_us``;
    * reserves every resource in its explicit ``footprint`` (exact qubits,
      not pool amounts) exclusively for the whole run;
    * after ``duration_us``, succeeds with ``success_probability`` (seeded,
      reproducible) and on success emits one ``produces`` token through its
      output port(s);
    * on failure optionally retries after ``cooldown_us`` (``auto_retry``),
      at most ``max_retries`` times per scheduled run.

    ``physical_qubits`` / ``logical_slots`` are *statistics annotations
    only*: execution reserves the explicit footprint, never a fungible
    charge.  Runs are scheduled by ``do: start_factory`` ops.  The whole
    factory layer compiles down to generic ops + resource uses + token
    productions, so every constraint (footprint overlap, ports, batch
    slots, buffers) is checked by the same architecture-neutral core.
    """

    id: str
    kind: str = "T_factory"
    produces: str
    duration_us: int = Field(ge=1)
    success_probability: float = Field(default=1.0, ge=0.0, le=1.0)
    #: the exact resources each run occupies; the loader REQUIRES this
    #: (programs built directly from models may omit it, e.g. in unit tests)
    footprint: Optional[FactoryFootprint] = None
    #: statistics annotations only -- never a fungible execution charge
    physical_qubits: int = Field(default=0, ge=0)
    logical_slots: int = Field(default=0, ge=0)
    output_ports: int = Field(default=1, ge=1)
    cooldown_us: int = Field(default=0, ge=0)
    max_parallel_batches: int = Field(default=1, ge=1)
    auto_retry: bool = False
    max_retries: int = Field(default=4, ge=0)
    deterministic_seed: Optional[int] = None
    description: Optional[str] = None

    def batch_slot_resource(self) -> str:
        return f"{self.id}.batch_slots"

    def port_resource(self) -> str:
        return f"{self.id}.output_ports"


class GateSpec(BaseModel):
    """A physical (or logical) gate-level operation the hardware offers.

    Gate times are hardware facts, not schedule choices: an op whose ``do:``
    matches a gate kind gets its duration from this table, and a schedule
    claiming a different duration is invalid -- the VM honestly reports the
    hardware time.  Gates lower to the generic core:

    * ``qubits``       -- if set, the op must name EXACTLY this many explicit
      qubits (a CNOT acts on 2, not "about 2");
    * ``uses``         -- control resources (readout lines, AWG channels, ...)
      charged for the gate's duration;
    * ``max_parallel`` -- at most this many gates of this kind at once
      (auto-resource ``gate.<kind>.parallel``), e.g. one AOD's tweezer count;
    * the backend-wide ``max_parallel_gates`` additionally bounds ALL
      simultaneous gate ops (auto-resource ``gates.parallel``), e.g. a finite
      FPGA's channel count.

    Omit the caps and parallelism is unconstrained -- the user models the
    control bottleneck only if their hardware has one.
    """

    kind: str
    duration_us: int = Field(ge=1)
    qubits: Optional[int] = Field(default=None, ge=1)
    uses: dict[str, int] = Field(default_factory=dict)
    max_parallel: Optional[int] = Field(default=None, ge=1)
    description: Optional[str] = None

    def parallel_resource(self) -> str:
        return f"gate.{self.kind}.parallel"


#: id of the global gate-parallelism auto-resource
GLOBAL_GATE_CHANNELS = "gates.parallel"


class ThroughputCap(BaseModel):
    """A windowed data-volume cap over an op class — e.g. the syndrome
    stream: every op of a kind in ``op_kinds`` injects ``weight_per_op``
    units (bits) into the stream; any ``window_us`` window may carry at
    most ``max_weight``.  4 KB/ms over measurements:

        {"id": "syndrome_stream", "op_kinds": ["measure"],
         "weight_per_op": 64, "window_us": 1000, "max_weight": 32768,
         "unit": "bits"}

    Window anchoring matches the Lean checker (`syndrome_bandwidth_ok`):
    windows anchored at matching ops' start times dominate all windows.
    """

    id: str
    op_kinds: list[str]
    weight_per_op: int = Field(default=1, ge=1)
    window_us: int = Field(ge=1)
    max_weight: int = Field(ge=0)
    unit: str = "bits"


class BackendConfig(BaseModel):
    """Description of a fault-tolerant backend as generic finite resources."""

    name: str = "backend"
    description: str = ""
    unit: UnitSpec = Field(default_factory=UnitSpec)
    resources: list[ResourceSpec] = Field(default_factory=list)
    #: qubit (and other addressable-unit) arrays; each element becomes an
    #: explicit capacity-1 resource ``<zone>[<i>]``
    zones: list[ZoneSpec] = Field(default_factory=list)
    services: list[ServiceSpec] = Field(default_factory=list)
    factories: list[FactorySpec] = Field(default_factory=list)
    #: hardware gate table: op kinds with hardware-set durations and
    #: control-parallelism constraints
    gates: list[GateSpec] = Field(default_factory=list)
    #: windowed data-volume caps (e.g. the syndrome-stream bandwidth)
    throughput_caps: list[ThroughputCap] = Field(default_factory=list)
    #: max simultaneous gate ops across ALL gate kinds (None = unconstrained)
    max_parallel_gates: Optional[int] = Field(default=None, ge=1)
    #: op kinds (the ``do:`` field) that touch qubits: ops of these kinds
    #: MUST list explicit qubits or the program is invalid
    #: (QubitExplicitnessViolation).  Gate kinds are always included.
    qubit_touching_kinds: list[str] = Field(default_factory=list)
    #: tokens of each kind already in the buffer at t = 0
    token_initial_inventory: dict[str, int] = Field(default_factory=dict)
    #: max tokens of each kind that may sit in the buffer at once (absent = unbounded)
    token_buffer_capacity: dict[str, int] = Field(default_factory=dict)
    #: freshness window: a token of kind k is consumable in
    #: [produced_at_us, produced_at_us + ttl_us)
    token_ttl_us: dict[str, int] = Field(default_factory=dict)
    #: default service processing times by service id (used when a job omits
    #: processing_time_us)
    default_latencies_us: dict[str, int] = Field(default_factory=dict)

    @model_validator(mode="after")
    def _check_unique_ids(self) -> "BackendConfig":
        seen: set[str] = set()
        for spec in [*self.resources, *self.zones, *self.services, *self.factories]:
            if spec.id in seen:
                raise ValueError(f"duplicate resource/zone/service/factory id {spec.id!r}")
            seen.add(spec.id)
        gate_kinds: set[str] = set()
        for g in self.gates:
            if g.kind in gate_kinds:
                raise ValueError(f"duplicate gate kind {g.kind!r}")
            gate_kinds.add(g.kind)
        reserved_ids = [f.batch_slot_resource() for f in self.factories]
        reserved_ids += [f.port_resource() for f in self.factories]
        reserved_ids += [g.parallel_resource() for g in self.gates
                         if g.max_parallel is not None]
        if self.gates and self.max_parallel_gates is not None:
            reserved_ids.append(GLOBAL_GATE_CHANNELS)
        for reserved in reserved_ids:
            if reserved in seen:
                raise ValueError(
                    f"id {reserved!r} is reserved for an auto-resource "
                    f"(factory slots/ports or gate-parallelism caps); rename "
                    f"the conflicting entry")
        for z in self.zones:
            prefix = z.id + "["
            for r in self.resources:
                if r.id.startswith(prefix):
                    raise ValueError(
                        f"resource id {r.id!r} collides with zone {z.id!r}'s "
                        f"qubit names; rename one of them")
        # gate ops always touch qubits: enforce explicit qubit ids for them
        touching = set(self.qubit_touching_kinds)
        missing = [g.kind for g in self.gates if g.kind not in touching]
        if missing:
            self.qubit_touching_kinds = [*self.qubit_touching_kinds, *missing]
        return self

    def resource_map(self) -> dict[str, ResourceSpec]:
        return {r.id: r for r in self.resources}

    def zone_map(self) -> dict[str, ZoneSpec]:
        return {z.id: z for z in self.zones}

    def service_map(self) -> dict[str, ServiceSpec]:
        return {s.id: s for s in self.services}

    def factory_map(self) -> dict[str, FactorySpec]:
        return {f.id: f for f in self.factories}

    def zone_resources(self) -> list[ResourceSpec]:
        """The explicit capacity-1 resources every zone expands to."""
        return [
            ResourceSpec(id=z.qubit_id(i), kind=z.kind, capacity=1,
                         description=f"element {i} of zone {z.id}")
            for z in self.zones for i in range(z.count)
        ]

    def gate_map(self) -> dict[str, GateSpec]:
        return {g.kind: g for g in self.gates}

    def gate_resources(self) -> list[ResourceSpec]:
        """Auto-resources realizing the gate-parallelism caps."""
        out: list[ResourceSpec] = []
        if self.gates and self.max_parallel_gates is not None:
            out.append(ResourceSpec(
                id=GLOBAL_GATE_CHANNELS, kind="control_channel",
                capacity=self.max_parallel_gates,
                description="global cap on simultaneous gate-level operations"))
        for g in self.gates:
            if g.max_parallel is not None:
                out.append(ResourceSpec(
                    id=g.parallel_resource(), kind="control_channel",
                    capacity=g.max_parallel,
                    description=f"max simultaneous {g.kind} gates"))
        return out


# --------------------------------------------------------------------------
# Program (ops)
# --------------------------------------------------------------------------


class ResourceUse(BaseModel):
    """A resource use declared inside an op, with op-relative times.

    ``start_us``/``end_us`` are offsets from the op's start.  ``end_us =
    None`` means "until the end of the op".  The resolved absolute interval
    is ``[op.at_us + start_us, op.at_us + end_us)``.
    """

    resource: str
    mode: UseMode = UseMode.capacity
    amount: int = Field(default=1, ge=1)
    start_us: int = Field(default=0, ge=0)
    end_us: Optional[int] = Field(default=None, ge=1)


class TokenConsume(BaseModel):
    """Consumption of tokens by an op at time ``op.at_us + at_us``.

    Either ``kind`` (consume the oldest fresh token of that kind, FIFO) or
    ``id`` (consume one specific token, for double-consume detection) must be
    given.  ``count`` only applies to kind-based consumption.
    """

    kind: Optional[str] = None
    id: Optional[str] = None
    count: int = Field(default=1, ge=1)
    at_us: int = Field(default=0, ge=0)

    @model_validator(mode="after")
    def _check_target(self) -> "TokenConsume":
        if (self.kind is None) == (self.id is None):
            raise ValueError("TokenConsume needs exactly one of 'kind' or 'id'")
        if self.id is not None and self.count != 1:
            raise ValueError("TokenConsume with explicit 'id' must have count == 1")
        return self


class TokenProduce(BaseModel):
    """Production of tokens by an op.

    Tokens appear at ``op.at_us + at_us`` if ``at_us`` is given, else at
    ``op.end_us``.  ``id`` names the single produced token (count must be 1);
    otherwise ids are generated as ``<op_id>/<kind>/<n>``.  ``ttl_us``
    overrides the backend's ``token_ttl_us`` for these tokens.
    """

    kind: str
    count: int = Field(default=1, ge=1)
    at_us: Optional[int] = Field(default=None, ge=0)
    id: Optional[str] = None
    ttl_us: Optional[int] = Field(default=None, ge=1)

    @model_validator(mode="after")
    def _check_id(self) -> "TokenProduce":
        if self.id is not None and self.count != 1:
            raise ValueError("TokenProduce with explicit 'id' must have count == 1")
        return self


class ServiceJobRequest(BaseModel):
    """A batch of identical jobs submitted to a service by an op.

    All ``count`` jobs are submitted at ``op.at_us + submit_at_us``.  Each
    takes ``processing_time_us`` on one worker (default: the backend's
    ``default_latencies_us[service]``, else 1).

    If ``result_token`` is set, every job produces one token of that kind at
    its *computed completion time*.  This chains pipeline stages: a decode op
    that consumes the result token before the job actually completes is
    caught by the token ledger (``TokenUnavailable: ... produced at t=...``)
    -- the feedforward / transport reaction time is checked, not assumed.
    """

    service: str
    count: int = Field(default=1, ge=1)
    submit_at_us: int = Field(default=0, ge=0)
    processing_time_us: Optional[int] = Field(default=None, ge=1)
    result_token: Optional[str] = None


class Op(BaseModel):
    """One operation in the declared schedule.

    The MVP execution model is *checking a declared schedule*: every op has
    an explicit start time (``at_us``) and ``duration_us``; the VM verifies
    the schedule is consistent with the backend's finite resources.
    """

    model_config = ConfigDict(validate_assignment=True)

    id: str
    kind: str = "op"
    at_us: int = Field(ge=0)
    duration_us: int = Field(default=1, ge=1)
    deps: list[str] = Field(default_factory=list)
    uses: list[ResourceUse] = Field(default_factory=list)
    consumes: list[TokenConsume] = Field(default_factory=list)
    produces: list[TokenProduce] = Field(default_factory=list)
    service: list[ServiceJobRequest] = Field(default_factory=list)
    metadata: dict[str, Any] = Field(default_factory=dict)

    @property
    def end_us(self) -> int:
        return self.at_us + self.duration_us

    @property
    def interval(self) -> TimeInterval:
        return TimeInterval(start_us=self.at_us, end_us=self.end_us)


class Program(BaseModel):
    """A named list of ops forming the declared schedule."""

    name: str = "program"
    description: str = ""
    ops: list[Op] = Field(default_factory=list)

    @model_validator(mode="after")
    def _check_unique_op_ids(self) -> "Program":
        seen: set[str] = set()
        for op in self.ops:
            if op.id in seen:
                raise ValueError(f"duplicate op id {op.id!r} in program")
            seen.add(op.id)
        return self

    def op_map(self) -> dict[str, Op]:
        return {op.id: op for op in self.ops}


# --------------------------------------------------------------------------
# Run configuration (seeding / factory modes)
# --------------------------------------------------------------------------


class RunConfig(BaseModel):
    """Reproducibility knobs for one simulation run.

    * ``stochastic`` factory mode: every factory run succeeds with its
      ``success_probability`` under a seeded PRNG -- the same seed always
      gives the same trace.
    * ``conservative`` mode: no randomness; a factory with success
      probability p succeeds exactly on every ceil(1/p)-th attempt (a
      pessimistic guaranteed-production contract).
    """

    seed: int = 0
    factory_mode: Literal["stochastic", "conservative"] = "stochastic"


# --------------------------------------------------------------------------
# Runtime objects: tokens, events, errors
# --------------------------------------------------------------------------


class Token(BaseModel):
    """A concrete token instance tracked by the token ledger."""

    id: str
    kind: str
    produced_at_us: int
    consumed_at_us: Optional[int] = None
    producer_op: Optional[str] = None
    consumer_op: Optional[str] = None
    #: token is consumable while t < expires_at_us (None = never expires)
    expires_at_us: Optional[int] = None


class VMErrorKind(str, enum.Enum):
    ResourceConflict = "ResourceConflict"
    CapacityExceeded = "CapacityExceeded"
    UnknownResource = "UnknownResource"
    UnknownDependency = "UnknownDependency"
    DependencyViolation = "DependencyViolation"
    TokenFreshnessViolation = "TokenFreshnessViolation"
    TokenUnavailable = "TokenUnavailable"
    TokenBufferOverflow = "TokenBufferOverflow"
    ServiceQueueOverflow = "ServiceQueueOverflow"
    ServiceCapacityExceeded = "ServiceCapacityExceeded"
    DeadlineMiss = "DeadlineMiss"
    InvalidInterval = "InvalidInterval"
    DoubleConsume = "DoubleConsume"
    AllocationError = "AllocationError"
    #: a qubit-touching op without explicit qubit ids, or an anonymous /
    #: amount-based use of qubits -- qubits are never fungible
    QubitExplicitnessViolation = "QubitExplicitnessViolation"
    #: a qubit of a reset-required zone reused without an explicit reset op
    #: (or with a reset shorter than the zone's min_reset_us)
    QubitReuseViolation = "QubitReuseViolation"
    #: a windowed data-volume cap exceeded (e.g. syndrome bits vs the
    #: classical link bandwidth)
    ThroughputExceeded = "ThroughputExceeded"


class VMError(BaseModel):
    """A human-readable, machine-locatable constraint violation."""

    kind: VMErrorKind
    time_us: int
    interval: Optional[TimeInterval] = None
    op_ids: list[str] = Field(default_factory=list)
    resource: Optional[str] = None
    token: Optional[str] = None
    service: Optional[str] = None
    factory: Optional[str] = None
    message: str
    suggestion: Optional[str] = None

    def headline(self) -> str:
        return f"[{self.kind.value}] t={self.time_us}us {self.message}"


class EventKind(str, enum.Enum):
    op_start = "op_start"
    op_end = "op_end"
    resource_reserved = "resource_reserved"
    resource_released = "resource_released"
    token_produced = "token_produced"
    token_consumed = "token_consumed"
    service_job_submitted = "service_job_submitted"
    service_job_started = "service_job_started"
    service_job_completed = "service_job_completed"
    factory_started = "factory_started"
    factory_succeeded = "factory_succeeded"
    factory_failed = "factory_failed"
    factory_retry_scheduled = "factory_retry_scheduled"
    error = "error"


#: display order of simultaneous events: ends/releases first, then factory
#: outcomes and productions, then starts/reservations/consumptions, errors last.
EVENT_ORDER: dict[EventKind, int] = {
    EventKind.op_end: 0,
    EventKind.factory_failed: 1,
    EventKind.factory_succeeded: 2,
    EventKind.resource_released: 3,
    EventKind.service_job_completed: 4,
    EventKind.token_produced: 5,
    EventKind.op_start: 6,
    EventKind.factory_started: 7,
    EventKind.factory_retry_scheduled: 8,
    EventKind.resource_reserved: 9,
    EventKind.token_consumed: 10,
    EventKind.service_job_submitted: 11,
    EventKind.service_job_started: 12,
    EventKind.error: 13,
}

Severity = Literal["info", "warning", "error"]


class Event(BaseModel):
    """One entry in the sorted trace."""

    time_us: int
    kind: EventKind
    severity: Severity = "info"
    op_id: Optional[str] = None
    resource: Optional[str] = None
    token_id: Optional[str] = None
    token_kind: Optional[str] = None
    service: Optional[str] = None
    factory: Optional[str] = None
    job_id: Optional[str] = None
    amount: Optional[int] = None
    message: str = ""
    details: dict[str, Any] = Field(default_factory=dict)

    @property
    def component(self) -> str:
        """The resource/service/factory/token this event is about."""
        return (self.resource or self.service or self.factory
                or self.token_kind or self.token_id or self.op_id or "")


# --------------------------------------------------------------------------
# Service runtime record
# --------------------------------------------------------------------------


class ServiceJobRecord(BaseModel):
    """Resolved lifecycle of one service job (for trace + certificate)."""

    job_id: str
    service: str
    op_id: str
    submit_time_us: int
    start_time_us: int
    complete_time_us: int
    processing_time_us: int
    deadline_us: int  # submit_time_us + max_latency_us

    @property
    def latency_us(self) -> int:
        return self.complete_time_us - self.submit_time_us

    @property
    def missed_deadline(self) -> bool:
        return self.complete_time_us > self.deadline_us
