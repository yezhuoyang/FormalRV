"""Runtime / resource statistics computed from one simulation run."""

from __future__ import annotations

from typing import Optional

from pydantic import BaseModel, Field

from .checker import ResourceCheckResult, ServiceCheckResult, TokenCheckResult
from .factory import FactoryExpansion
from .models import BackendConfig, Program, VMError


class ResourceStats(BaseModel):
    id: str
    kind: str
    capacity: int
    peak_usage: int
    #: time-averaged usage / capacity over the whole run, in [0, ...]
    utilization: float


class ServiceStats(BaseModel):
    id: str
    kind: str
    workers: int
    total_jobs: int
    #: total processing time / (workers * runtime)
    utilization: float
    max_queue_length: int
    queue_capacity: int
    peak_busy_workers: int
    deadline_misses: int


class TokenStats(BaseModel):
    kind: str
    initial_inventory: int
    produced: int  # includes initial inventory
    consumed: int
    peak_buffer: int
    buffer_capacity: Optional[int] = None
    leftover: int


class FactoryStats(BaseModel):
    id: str
    kind: str
    produces: str
    attempts: int
    successes: int
    failures: int
    retries: int
    empirical_success_rate: float
    tokens_produced: int
    #: busy batch-slot time / (max_parallel_batches * runtime)
    utilization: float
    physical_qubits: int
    logical_slots: int


class ZoneStats(BaseModel):
    """Rollup over a zone's explicit capacity-1 qubits."""

    id: str
    kind: str
    count: int
    #: max number of qubits of this zone busy at the same time
    peak_busy: int
    #: time-averaged busy qubits / count
    utilization: float


class Bottleneck(BaseModel):
    id: str
    type: str  # "resource" | "zone" | "service" | "factory"
    utilization: float


class Stats(BaseModel):
    verdict: str  # "pass" | "fail"
    total_runtime_us: int
    num_ops: int
    error_count: int
    errors_by_kind: dict[str, int]
    resources: list[ResourceStats]
    zones: list[ZoneStats] = Field(default_factory=list)
    services: list[ServiceStats]
    tokens: list[TokenStats]
    factories: list[FactoryStats]
    bottlenecks: list[Bottleneck] = Field(default_factory=list)


def _runtime(program: Program, services: ServiceCheckResult,
             tokens: TokenCheckResult) -> int:
    """Makespan: last op end, last job completion or last token event."""
    candidates = [0]
    candidates.extend(op.end_us for op in program.ops)
    for batches in services.batches.values():
        candidates.extend(b.last_complete_us for b in batches)
    candidates.extend(ev["t_us"] for ev in tokens.token_event_order)
    return max(candidates)


def compute_stats(backend: BackendConfig, program: Program,
                  resources: ResourceCheckResult, tokens: TokenCheckResult,
                  services: ServiceCheckResult, expansion: FactoryExpansion,
                  errors: list[VMError]) -> Stats:
    runtime = _runtime(program, services, tokens)

    resource_stats = []
    for spec in backend.resources:
        area = resources.busy_area.get(spec.id, 0)
        util = area / (spec.capacity * runtime) if runtime > 0 else 0.0
        resource_stats.append(ResourceStats(
            id=spec.id, kind=spec.kind, capacity=spec.capacity,
            peak_usage=resources.peak_usage.get(spec.id, 0),
            utilization=round(util, 6),
        ))

    # zone rollups: peak concurrent busy qubits + time-averaged utilization
    zone_ids = {z.id for z in backend.zones}
    zone_stats = []
    for z in backend.zones:
        qubit_ids = [z.qubit_id(i) for i in range(z.count)]
        area = sum(resources.busy_area.get(q, 0) for q in qubit_ids)
        deltas: list[tuple[int, int]] = []
        for q in qubit_ids:
            prev = 0
            for t, v in resources.usage_series.get(q, ()):  # capacity-1 steps
                if v != prev:
                    deltas.append((t, v - prev))
                    prev = v
        deltas.sort()
        peak = level = 0
        for _t, d in deltas:
            level += d
            peak = max(peak, level)
        util = area / (z.count * runtime) if runtime > 0 else 0.0
        zone_stats.append(ZoneStats(id=z.id, kind=z.kind, count=z.count,
                                    peak_busy=peak, utilization=round(util, 6)))

    service_stats = []
    for spec in backend.services:
        area = services.busy_area.get(spec.id, 0)
        util = area / (spec.workers * runtime) if runtime > 0 else 0.0
        misses = sum(b.deadline_misses for b in services.batches.get(spec.id, []))
        service_stats.append(ServiceStats(
            id=spec.id, kind=spec.kind, workers=spec.workers,
            total_jobs=services.total_jobs.get(spec.id, 0),
            utilization=round(util, 6),
            max_queue_length=services.max_queue_length.get(spec.id, 0),
            queue_capacity=spec.queue_capacity,
            peak_busy_workers=services.peak_busy_workers.get(spec.id, 0),
            deadline_misses=misses,
        ))

    kinds = sorted(set(tokens.produced) | set(tokens.consumed)
                   | set(backend.token_initial_inventory)
                   | set(backend.token_buffer_capacity))
    token_stats = []
    for kind in kinds:
        produced = tokens.produced.get(kind, 0)
        consumed = tokens.consumed.get(kind, 0)
        token_stats.append(TokenStats(
            kind=kind,
            initial_inventory=backend.token_initial_inventory.get(kind, 0),
            produced=produced, consumed=consumed,
            peak_buffer=tokens.peak_occupancy.get(kind, 0),
            buffer_capacity=backend.token_buffer_capacity.get(kind),
            leftover=produced - consumed,
        ))

    factory_stats = []
    for spec in backend.factories:
        c = expansion.counters.get(spec.id)
        if c is None:
            continue
        util = (c.busy_area_us / (spec.max_parallel_batches * runtime)
                if runtime > 0 else 0.0)
        factory_stats.append(FactoryStats(
            id=spec.id, kind=spec.kind, produces=spec.produces,
            attempts=c.attempts, successes=c.successes, failures=c.failures,
            retries=c.retries,
            empirical_success_rate=round(c.empirical_success_rate, 6),
            tokens_produced=c.tokens_produced,
            utilization=round(util, 6),
            physical_qubits=spec.physical_qubits,
            logical_slots=spec.logical_slots,
        ))

    errors_by_kind: dict[str, int] = {}
    for e in errors:
        errors_by_kind[e.kind.value] = errors_by_kind.get(e.kind.value, 0) + 1

    def _zone_of(rid: str) -> str | None:
        zone = rid.split("[", 1)[0] if "[" in rid else None
        return zone if zone in zone_ids else None

    candidates = (
        # individual zone qubits are rolled up into their zone's entry
        [Bottleneck(id=r.id, type="resource", utilization=r.utilization)
         for r in resource_stats if _zone_of(r.id) is None]
        + [Bottleneck(id=z.id, type="zone", utilization=z.utilization)
           for z in zone_stats]
        + [Bottleneck(id=s.id, type="service", utilization=s.utilization)
           for s in service_stats]
        + [Bottleneck(id=f.id, type="factory", utilization=f.utilization)
           for f in factory_stats]
    )
    bottlenecks = sorted((b for b in candidates if b.utilization > 0),
                         key=lambda b: -b.utilization)[:3]

    return Stats(
        verdict="pass" if not errors else "fail",
        total_runtime_us=runtime,
        num_ops=len(program.ops),
        error_count=len(errors),
        errors_by_kind=errors_by_kind,
        resources=resource_stats,
        zones=zone_stats,
        services=service_stats,
        tokens=token_stats,
        factories=factory_stats,
        bottlenecks=bottlenecks,
    )
