"""Certificate export.

The certificate is a self-contained JSON document with enough *resolved* data
for an independent checker (``check_certificate.py`` today, a Lean program
later) to re-verify the run without re-running the simulator:

* hashes of the canonical backend / program JSON (binding the certificate);
* every op's absolute interval and dependencies (factory runs included --
  their stochastic outcomes are already resolved, so the certificate is
  fully deterministic data);
* every resolved resource-use interval, per resource, with capacities
  (a checker replays the sweep and confirms the claimed peaks / verdict);
* the full chronological token production/consumption order (a checker
  replays the ledger: consume-after-produce, freshness, buffer bounds);
* every service job batch (submit time, count, processing time) plus the
  claimed queue bounds (a checker replays the FIFO queue recurrence);
* factory run records (intervals + outcomes);
* the final stats and the error list (for a *fail* certificate, the claimed
  violations; for a *pass* certificate, the absence of any).

All integers, strings, booleans, lists and string-keyed maps only --
trivially parseable from Lean.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict
from typing import Any

from .checker import ResourceCheckResult, ServiceCheckResult, TokenCheckResult
from .factory import FactoryExpansion
from .models import BackendConfig, Program, RunConfig, VMError
from .stats import Stats

CERTIFICATE_FORMAT = "ftqvm-certificate"
CERTIFICATE_VERSION = 2


def canonical_json(obj: Any) -> str:
    """Deterministic JSON encoding used for hashing."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def sha256_hex(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _op_section(full_backend: BackendConfig, full_program: Program,
                resources: ResourceCheckResult) -> list[dict[str, Any]]:
    """Per-op declarations with *absolute* times, so an independent checker
    can cross-check them against the per-resource intervals, the token event
    order and the service batches (the certificate is closed: declarations
    and realized events must agree)."""
    uses_by_op: dict[str, list[dict[str, Any]]] = {}
    for rid, intervals in resources.intervals.items():
        for u in intervals:
            uses_by_op.setdefault(u.op_id, []).append({
                "resource": rid, "mode": u.mode.value, "amount": u.amount,
                "start_us": u.start_us, "end_us": u.end_us,
            })
    section = []
    for op in full_program.ops:
        section.append({
            "id": op.id, "kind": op.kind, "start_us": op.at_us, "end_us": op.end_us,
            "deps": list(op.deps),
            "uses": sorted(uses_by_op.get(op.id, []),
                           key=lambda u: (u["resource"], u["start_us"], u["end_us"])),
            "consumes": [
                {"kind": c.kind, "id": c.id, "count": c.count,
                 "t_us": op.at_us + c.at_us}
                for c in op.consumes
            ],
            "produces": [
                {"kind": p.kind, "id": p.id, "count": p.count,
                 "t_us": (op.at_us + p.at_us if p.at_us is not None else op.end_us)}
                for p in op.produces
            ],
            "service_jobs": [
                {"service": j.service, "count": j.count,
                 "submit_us": op.at_us + j.submit_at_us,
                 "processing_time_us": (
                     j.processing_time_us if j.processing_time_us is not None
                     else full_backend.default_latencies_us.get(j.service, 1)),
                 "result_token": j.result_token}
                for j in op.service
            ],
        })
    return section


def build_certificate(backend: BackendConfig, program: Program,
                      full_backend: BackendConfig, full_program: Program,
                      resources: ResourceCheckResult, tokens: TokenCheckResult,
                      services: ServiceCheckResult, expansion: FactoryExpansion,
                      stats: Stats, errors: list[VMError],
                      cfg: RunConfig) -> dict[str, Any]:
    """``backend``/``program`` are the user's inputs (hashed); the ``full_*``
    versions additionally contain factory auto-resources and expanded runs
    (the data the checks actually ran on)."""
    backend_doc = backend.model_dump(mode="json")
    program_doc = program.model_dump(mode="json")

    resource_section = []
    for spec in full_backend.resources:
        resource_section.append({
            "id": spec.id,
            "kind": spec.kind,
            "capacity": spec.capacity,
            "peak_usage": resources.peak_usage.get(spec.id, 0),
            "intervals": [
                {"op": u.op_id, "mode": u.mode.value, "amount": u.amount,
                 "start_us": u.start_us, "end_us": u.end_us}
                for u in resources.intervals.get(spec.id, [])
            ],
        })

    service_section = []
    for spec in full_backend.services:
        service_section.append({
            "id": spec.id,
            "kind": spec.kind,
            "workers": spec.workers,
            "max_latency_us": spec.max_latency_us,
            "queue_capacity": spec.queue_capacity,
            "max_queue_length": services.max_queue_length.get(spec.id, 0),
            "peak_busy_workers": services.peak_busy_workers.get(spec.id, 0),
            "total_jobs": services.total_jobs.get(spec.id, 0),
            "batches": [asdict(b) for b in services.batches.get(spec.id, [])],
        })

    factory_section = []
    for spec in full_backend.factories:
        factory_section.append({
            "id": spec.id,
            "kind": spec.kind,
            "produces": spec.produces,
            "duration_us": spec.duration_us,
            "success_probability": spec.success_probability,
            "max_parallel_batches": spec.max_parallel_batches,
            "output_ports": spec.output_ports,
            "runs": [asdict(r) for r in expansion.runs.get(spec.id, [])],
        })

    return {
        "format": CERTIFICATE_FORMAT,
        "version": CERTIFICATE_VERSION,
        "backend_name": backend.name,
        "program_name": program.name,
        "backend_hash": sha256_hex(canonical_json(backend_doc)),
        "program_hash": sha256_hex(canonical_json(program_doc)),
        "seed": cfg.seed,
        "factory_mode": cfg.factory_mode,
        "verdict": stats.verdict,
        "total_runtime_us": stats.total_runtime_us,
        "ops": _op_section(full_backend, full_program, resources),
        "resources": resource_section,
        "zones": [{"id": z.id, "kind": z.kind, "count": z.count}
                  for z in full_backend.zones],
        "token_events": list(tokens.token_event_order),
        "token_buffer_capacity": dict(backend.token_buffer_capacity),
        "token_ttl_us": dict(backend.token_ttl_us),
        "token_peak_occupancy": dict(tokens.peak_occupancy),
        "services": service_section,
        "factories": factory_section,
        "errors": [e.model_dump(mode="json", exclude_none=True) for e in errors],
        "stats": stats.model_dump(mode="json"),
    }
