"""Active factory simulation.

Factories (e.g. T-state factories) are simulated components that take space
and time and fail stochastically -- not abstract average token rates.  To
keep the core VM architecture-neutral, this module *compiles* factories down
to generic primitives before checking:

* every scheduled run becomes a ``factory_run`` op that

  - holds one of ``max_parallel_batches`` batch slots (auto-resource
    ``<id>.batch_slots``) for ``duration_us``,
  - reserves the factory's explicit ``footprint`` (exact named qubits and
    buffer slots -- never a fungible pool charge) EXCLUSIVELY for the whole
    run, so any other op touching a footprint qubit is a ResourceConflict,
  - on success holds its declared output port(s) (or the auto-resource
    ``<id>.output_ports`` if none are declared) during the final
    microsecond and produces one token at the run's end;

* outcomes are decided here, reproducibly:

  - ``stochastic`` mode: seeded PRNG (global seed mixed with the factory id,
    or the factory's ``deterministic_seed``) -- same seed, same trace;
  - ``conservative`` mode: no randomness; with success probability p, exactly
    every ceil(1/p)-th attempt succeeds (a pessimistic guaranteed-production
    contract);

* failures emit ``factory_failed`` events; with ``auto_retry`` a failed run
  is retried after ``cooldown_us``, at most ``max_retries`` times per
  scheduled run.

Everything downstream (port conflicts, batch-slot oversubscription, buffer
overflow, starvation of consumers) is then caught by the ordinary generic
checkers.
"""

from __future__ import annotations

import hashlib
import math
import random
from dataclasses import dataclass, field
from typing import Optional

from .models import (
    BackendConfig,
    Event,
    EventKind,
    FactorySpec,
    Op,
    Program,
    ResourceSpec,
    ResourceUse,
    RunConfig,
    TokenProduce,
    UseMode,
    VMError,
    VMErrorKind,
    parse_qubit_ref,
)


@dataclass
class FactoryRunRecord:
    """One concrete (attempted) factory run."""

    run_id: str
    factory: str
    scheduled_by: str          # id of the start_factory op
    attempt: int               # 1 = first try of this scheduled run
    start_us: int
    end_us: int
    success: bool
    retry_of: Optional[str] = None


@dataclass
class FactoryCounters:
    attempts: int = 0
    successes: int = 0
    failures: int = 0
    retries: int = 0
    busy_area_us: int = 0      # sum of run durations
    last_complete_us: int = 0

    @property
    def tokens_produced(self) -> int:
        return self.successes

    @property
    def empirical_success_rate(self) -> float:
        return self.successes / self.attempts if self.attempts else 0.0


@dataclass
class FactoryExpansion:
    ops: list[Op] = field(default_factory=list)
    events: list[Event] = field(default_factory=list)
    errors: list[VMError] = field(default_factory=list)
    extra_resources: list[ResourceSpec] = field(default_factory=list)
    runs: dict[str, list[FactoryRunRecord]] = field(default_factory=dict)
    counters: dict[str, FactoryCounters] = field(default_factory=dict)


def _stable_seed(global_seed: int, factory_id: str) -> int:
    digest = hashlib.sha256(f"{global_seed}/{factory_id}".encode("utf-8")).digest()
    return int.from_bytes(digest[:8], "big")


class _OutcomeSource:
    """Decides run outcomes for one factory, reproducibly."""

    def __init__(self, spec: FactorySpec, cfg: RunConfig):
        self.p = spec.success_probability
        self.mode = cfg.factory_mode
        self.attempt_no = 0
        if self.mode == "stochastic":
            seed = (spec.deterministic_seed if spec.deterministic_seed is not None
                    else _stable_seed(cfg.seed, spec.id))
            self.rng = random.Random(seed)
        else:  # conservative: every ceil(1/p)-th attempt succeeds
            self.period = math.ceil(1.0 / self.p) if self.p > 0 else None

    def next_outcome(self) -> bool:
        self.attempt_no += 1
        if self.p <= 0.0:
            return False
        if self.mode == "stochastic":
            return self.rng.random() < self.p
        if self.period is None:
            return False
        return self.attempt_no % self.period == 0


def _expand_refs(backend: BackendConfig, spec: FactorySpec, refs: list[str],
                 group: str, errors: list[VMError]) -> list[str]:
    """Expand footprint references into explicit resource ids.

    Each ref is either a zone qubit reference (``factory_F0[0:18]``) or the
    id of a declared resource.  Unknown refs are reported once and skipped.
    """
    zones = backend.zone_map()
    resources = backend.resource_map()
    out: list[str] = []
    seen: set[str] = set()
    for ref in refs:
        parsed = parse_qubit_ref(ref)
        if parsed is not None and parsed[0] in zones:
            zone = zones[parsed[0]]
            bad = [i for i in parsed[1] if not 0 <= i < zone.count]
            if bad:
                errors.append(VMError(
                    kind=VMErrorKind.UnknownResource, time_us=0, factory=spec.id,
                    resource=ref,
                    message=f"factory {spec.id}: footprint.{group} index {bad} out "
                            f"of range for zone {zone.id!r} (count {zone.count}).",
                    suggestion="Fix the footprint indices.",
                ))
                continue
            ids = [zone.qubit_id(i) for i in parsed[1]]
        elif ref in resources:
            ids = [ref]
        else:
            errors.append(VMError(
                kind=VMErrorKind.UnknownResource, time_us=0, factory=spec.id,
                resource=ref,
                message=f"factory {spec.id}: footprint.{group} entry {ref!r} names "
                        f"no declared zone or resource.",
                suggestion="Declare the zone/resource or fix the reference.",
            ))
            continue
        for rid in ids:
            if rid not in seen:
                seen.add(rid)
                out.append(rid)
    return out


def _resolve_footprint(backend: BackendConfig, spec: FactorySpec,
                       errors: list[VMError]) -> tuple[list[str], list[str]]:
    """Returns (resources held for the whole run, port resources held during
    the emission microsecond of a successful run).

    Deduplicated across groups: a resource listed under both ``qubits`` and
    ``buffer`` is held once; a port already held for the whole run is
    dropped from the emission-window list (the whole-run hold subsumes it).
    An op may not reserve the same exclusive resource twice.
    """
    if spec.footprint is None:
        return [], []
    whole_run = _expand_refs(backend, spec, spec.footprint.qubits, "qubits", errors)
    in_whole_run = set(whole_run)
    for rid in _expand_refs(backend, spec, spec.footprint.buffer, "buffer", errors):
        if rid not in in_whole_run:
            in_whole_run.add(rid)
            whole_run.append(rid)
    ports = [rid for rid in _expand_refs(backend, spec, spec.footprint.output_ports,
                                         "output_ports", errors)
             if rid not in in_whole_run]
    return whole_run, ports


def expand_factories(backend: BackendConfig, program: Program,
                     cfg: RunConfig) -> FactoryExpansion:
    """Turn ``start_factory`` ops into concrete, outcome-decided run ops."""
    result = FactoryExpansion()
    fmap = backend.factory_map()

    # auto-resources exist for every declared factory (visible in stats/UI)
    for spec in backend.factories:
        result.extra_resources.append(ResourceSpec(
            id=spec.batch_slot_resource(), kind="factory_batch_slot",
            capacity=spec.max_parallel_batches,
            description=f"parallel batch slots of factory {spec.id}"))
        result.extra_resources.append(ResourceSpec(
            id=spec.port_resource(), kind="factory_port",
            capacity=spec.output_ports,
            description=f"output ports of factory {spec.id}"))
        result.runs[spec.id] = []
        result.counters[spec.id] = FactoryCounters()

    outcome_sources = {spec.id: _OutcomeSource(spec, cfg) for spec in backend.factories}
    run_counter: dict[str, int] = {fid: 0 for fid in fmap}
    footprints = {spec.id: _resolve_footprint(backend, spec, result.errors)
                  for spec in backend.factories}
    #: generated run ids must never collide with user op ids (the merged
    #: program skips re-validation)
    taken_ids = {op.id for op in program.ops}

    def fresh_run_id(fid: str) -> tuple[str, int]:
        while True:
            n = run_counter[fid]
            run_counter[fid] += 1
            run_id = f"{fid}.run{n}"
            if run_id not in taken_ids:
                taken_ids.add(run_id)
                return run_id, n

    requests = [op for op in program.ops if op.kind == "start_factory"]
    requests.sort(key=lambda op: op.at_us)

    for req in requests:
        fid = req.metadata.get("factory")
        if not isinstance(fid, str) or fid not in fmap:
            result.errors.append(VMError(
                kind=VMErrorKind.UnknownResource, time_us=req.at_us,
                op_ids=[req.id], factory=str(fid) if fid is not None else None,
                message=f"op={req.id} starts unknown factory {fid!r}.",
                suggestion="Declare it under 'factories' or fix the name.",
            ))
            continue
        spec = fmap[fid]
        counters = result.counters[fid]
        whole_run_ids, port_ids = footprints[fid]

        start = req.at_us
        attempt = 1
        prev_run_id: Optional[str] = None
        while True:
            run_id, n = fresh_run_id(fid)
            end = start + spec.duration_us
            success = outcome_sources[fid].next_outcome()

            counters.attempts += 1
            counters.busy_area_us += spec.duration_us
            counters.last_complete_us = max(counters.last_complete_us, end)
            if success:
                counters.successes += 1
            else:
                counters.failures += 1
            if attempt > 1:
                counters.retries += 1

            uses = [ResourceUse(resource=spec.batch_slot_resource(), amount=1)]
            # the explicit footprint is held exclusively for the WHOLE run
            uses.extend(ResourceUse(resource=rid, mode=UseMode.exclusive)
                        for rid in whole_run_ids)
            if success:
                # the finished token leaves through the output port(s) at the end
                if port_ids:
                    uses.extend(ResourceUse(resource=rid, mode=UseMode.exclusive,
                                            start_us=spec.duration_us - 1)
                                for rid in port_ids)
                else:
                    uses.append(ResourceUse(resource=spec.port_resource(), amount=1,
                                            start_us=spec.duration_us - 1))
            produces = [TokenProduce(kind=spec.produces)] if success else []

            result.ops.append(Op(
                id=run_id, kind="factory_run", at_us=start,
                duration_us=spec.duration_us, uses=uses, produces=produces,
                metadata={"factory": fid, "scheduled_by": req.id,
                          "attempt": attempt, "outcome": "success" if success else "failure",
                          **({"retry_of": prev_run_id} if prev_run_id else {})},
            ))
            result.runs[fid].append(FactoryRunRecord(
                run_id=run_id, factory=fid, scheduled_by=req.id, attempt=attempt,
                start_us=start, end_us=end, success=success, retry_of=prev_run_id))

            result.events.append(Event(
                time_us=start, kind=EventKind.factory_started, factory=fid,
                op_id=run_id,
                message=f"{fid} starts a {spec.produces} batch "
                        f"(run {n}, attempt {attempt})",
                details={"scheduled_by": req.id}))
            if success:
                result.events.append(Event(
                    time_us=end, kind=EventKind.factory_succeeded, factory=fid,
                    op_id=run_id,
                    message=f"{fid} run {n} succeeds; 1 {spec.produces} emitted",
                    details={"attempt": attempt}))
                break
            result.events.append(Event(
                time_us=end, kind=EventKind.factory_failed, factory=fid,
                op_id=run_id, severity="warning",
                message=f"{fid} run {n} FAILS (attempt {attempt}, "
                        f"p={spec.success_probability})",
                details={"attempt": attempt}))
            if not spec.auto_retry or attempt > spec.max_retries:
                break
            retry_start = end + spec.cooldown_us
            result.events.append(Event(
                time_us=end, kind=EventKind.factory_retry_scheduled, factory=fid,
                op_id=run_id, severity="warning",
                message=f"{fid} schedules retry at t={retry_start}us "
                        f"(cooldown {spec.cooldown_us}us)"))
            prev_run_id = run_id
            start = retry_start
            attempt += 1

    return result
