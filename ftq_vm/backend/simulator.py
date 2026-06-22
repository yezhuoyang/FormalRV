"""The FTQ-VM execution engine.

Pipeline of one run:

1. :func:`factory.expand_factories` -- compile ``start_factory`` ops into
   concrete, outcome-decided ``factory_run`` ops (seeded, reproducible) plus
   auto-resources for batch slots / output ports;
2. the five generic checkers (static, dependencies, resources, tokens,
   services) over the augmented program;
3. merge all events into a single sorted trace, compute stats, and build the
   Lean-checkable certificate.
"""

from __future__ import annotations

from dataclasses import asdict
from typing import Any, Optional

from pydantic import BaseModel

from . import checker
from .certificate import build_certificate
from .factory import FactoryExpansion, expand_factories
from .gates import lower_gates
from .models import (
    BackendConfig,
    Event,
    EventKind,
    EVENT_ORDER,
    Program,
    RunConfig,
    ServiceJobRecord,
    Token,
    VMError,
    VMErrorKind,
)
from .stats import Stats, compute_stats

#: order in which error kinds are listed at equal times (severity-ish)
_ERROR_KIND_ORDER = {k: i for i, k in enumerate(VMErrorKind)}


class RunResult(BaseModel):
    """Everything one simulation run produces."""

    backend_name: str
    program_name: str
    seed: int
    factory_mode: str
    ok: bool
    events: list[Event]
    errors: list[VMError]
    tokens: list[Token]
    #: per-service per-job records (only for services with few jobs)
    job_records: dict[str, list[ServiceJobRecord]]
    #: per-service batch summaries (always present)
    service_batches: dict[str, list[dict[str, Any]]]
    #: per-factory run records
    factory_runs: dict[str, list[dict[str, Any]]]
    #: step series: value at (t) holds until the next point
    resource_usage_series: dict[str, list[tuple[int, int]]]
    token_occupancy_series: dict[str, list[tuple[int, int]]]
    service_queue_series: dict[str, list[tuple[int, int]]]
    service_busy_series: dict[str, list[tuple[int, int]]]
    #: resolved op intervals for the timeline UI (includes factory runs)
    op_intervals: list[dict[str, Any]]
    #: resource capacities (incl. factory auto-resources) for the UI
    resource_capacities: dict[str, int]
    stats: Stats
    certificate: dict[str, Any]

    def trace_dict(self) -> dict[str, Any]:
        """Content of trace.json."""
        return {
            "backend": self.backend_name,
            "program": self.program_name,
            "seed": self.seed,
            "factory_mode": self.factory_mode,
            "ok": self.ok,
            "events": [e.model_dump(mode="json", exclude_none=True) for e in self.events],
            "errors": [e.model_dump(mode="json", exclude_none=True) for e in self.errors],
        }


def _op_events(program: Program) -> list[Event]:
    events = []
    for op in program.ops:
        if op.kind == "factory_run":
            continue  # factory.py emits richer factory_* events instead
        events.append(Event(
            time_us=op.at_us, kind=EventKind.op_start, op_id=op.id,
            message=f"{op.id} ({op.kind}) starts",
            details={"duration_us": op.duration_us}))
        events.append(Event(
            time_us=op.end_us, kind=EventKind.op_end, op_id=op.id,
            message=f"{op.id} ({op.kind}) ends"))
    return events


def _error_events(errors: list[VMError]) -> list[Event]:
    return [
        Event(
            time_us=e.time_us, kind=EventKind.error, severity="error",
            op_id=(e.op_ids[0] if e.op_ids else None),
            resource=e.resource, token_id=e.token, service=e.service,
            factory=e.factory,
            message=e.headline(),
            details={"error_kind": e.kind.value, "suggestion": e.suggestion},
        )
        for e in errors
    ]


def run_simulation(backend: BackendConfig, program: Program,
                   run_config: Optional[RunConfig] = None) -> RunResult:
    """Execute the declared schedule against the backend and check it."""
    cfg = run_config or RunConfig()

    # ---- lower zones/gates to generic resources; compile factories ---------
    expansion: FactoryExpansion = expand_factories(backend, program, cfg)
    full_backend = backend.model_copy(update={
        "resources": [*backend.resources, *backend.zone_resources(),
                      *backend.gate_resources(), *expansion.extra_resources]})
    full_program = Program.model_construct(
        name=program.name, description=program.description,
        ops=[*program.ops, *expansion.ops])
    full_program, gate_errors = lower_gates(full_backend, full_program)

    # ---- generic checkers ---------------------------------------------------
    static = checker.check_static(full_backend, full_program)
    dep_errors = checker.check_dependencies(full_program)
    reuse_errors = checker.check_qubit_reuse(full_backend, full_program,
                                             static.resolved_uses)
    throughput_errors = checker.check_throughput(full_backend, full_program)
    resources = checker.check_resources(full_backend, static.resolved_uses)
    services = checker.check_services(full_backend, full_program)
    # services run first: completed jobs may produce result tokens at their
    # computed completion times, which the ledger then replays
    tokens = checker.check_tokens(full_backend, full_program,
                                  services.result_token_productions)

    errors: list[VMError] = [
        *expansion.errors, *gate_errors, *static.errors, *dep_errors,
        *reuse_errors, *throughput_errors,
        *resources.errors, *tokens.errors, *services.errors,
    ]
    errors.sort(key=lambda e: (e.time_us, _ERROR_KIND_ORDER[e.kind], e.message))

    events: list[Event] = [
        *_op_events(full_program),
        *expansion.events,
        *resources.events, *tokens.events, *services.events,
        *_error_events(errors),
    ]
    # stable sort: time, then canonical kind order, then insertion order
    events.sort(key=lambda e: (e.time_us, EVENT_ORDER[e.kind]))

    stats = compute_stats(full_backend, full_program, resources, tokens, services,
                          expansion, errors)
    certificate = build_certificate(
        backend, program, full_backend, full_program, resources, tokens, services,
        expansion, stats, errors, cfg)

    op_intervals = [
        {
            "id": op.id, "kind": op.kind, "start_us": op.at_us, "end_us": op.end_us,
            "duration_us": op.duration_us, "deps": op.deps,
            "resources": sorted({u.resource for u in op.uses}),
            "services": sorted({j.service for j in op.service}),
            "consumes": sorted({c.kind or c.id or "?" for c in op.consumes}),
            "produces": sorted({p.kind for p in op.produces}),
            "metadata": op.metadata,
        }
        for op in full_program.ops
    ]

    return RunResult(
        backend_name=backend.name,
        program_name=program.name,
        seed=cfg.seed,
        factory_mode=cfg.factory_mode,
        ok=not errors,
        events=events,
        errors=errors,
        tokens=tokens.tokens,
        job_records=services.job_records,
        service_batches={sid: [asdict(b) for b in bs]
                         for sid, bs in services.batches.items()},
        factory_runs={fid: [asdict(r) for r in rs]
                      for fid, rs in expansion.runs.items()},
        resource_usage_series=resources.usage_series,
        token_occupancy_series=tokens.occupancy_series,
        service_queue_series=services.queue_series,
        service_busy_series=services.busy_series,
        op_intervals=op_intervals,
        resource_capacities={r.id: r.capacity for r in full_backend.resources},
        stats=stats,
        certificate=certificate,
    )
