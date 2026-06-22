"""Constraint checkers for the FTQ-VM.

Five independent checkers, each consuming the (backend, program) pair and
producing events, errors and time series:

* :func:`check_static`        -- references, intervals, single-op allocation
* :func:`check_dependencies`  -- declared deps finish before dependents start
* :func:`check_resources`     -- exclusive conflicts + capacity sweeps
* :func:`check_tokens`        -- token ledger: freshness, availability, buffers
* :func:`check_services`      -- finite-worker FIFO queues: overflow, deadlines

All times are integer microseconds; all intervals are half-open
``[start_us, end_us)``.  Simultaneous token events are ordered *productions
before consumptions*, so a token produced at ``t`` is consumable by an op
starting at ``t``; buffer occupancy is checked after each production (a
same-tick consumption cannot rescue a momentary overflow).

To keep reports readable, contiguous violations of the same constraint are
merged into a single error covering the whole violating interval.
"""

from __future__ import annotations

import heapq
import itertools
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Optional

from .models import (
    BackendConfig,
    Event,
    EventKind,
    Op,
    Program,
    ServiceJobRecord,
    TimeInterval,
    Token,
    TokenProduce,
    UseMode,
    VMError,
    VMErrorKind,
    is_qubit_like_kind,
    parse_qubit_ref,
)

#: above this many jobs per service, per-job trace events collapse to batch events
EVENT_DETAIL_LIMIT = 500
#: above this many jobs per service, per-job records are not materialized
JOB_RECORD_LIMIT = 2000
#: above this many tokens in one production, per-token trace events collapse
TOKEN_EVENT_LIMIT = 100


# --------------------------------------------------------------------------
# Resolved structures (internal, lightweight)
# --------------------------------------------------------------------------


@dataclass
class ResolvedUse:
    """A resource use with absolute times, after static validation."""

    resource: str
    mode: UseMode
    amount: int
    start_us: int
    end_us: int
    op_id: str
    use_id: str


@dataclass
class StaticCheckResult:
    errors: list[VMError] = field(default_factory=list)
    #: uses that passed validation, ready for the sweep
    resolved_uses: list[ResolvedUse] = field(default_factory=list)


def resolve_op_uses(op: Op, backend: BackendConfig) -> tuple[list[ResolvedUse], list[VMError]]:
    """Resolve one op's relative resource uses to absolute intervals.

    Returns (valid_uses, errors).  Invalid uses are reported and excluded
    from further checking so one bad declaration doesn't cascade.
    """
    resources = backend.resource_map()
    zones = backend.zone_map()
    valid: list[ResolvedUse] = []
    errors: list[VMError] = []
    for i, use in enumerate(op.uses):
        use_id = f"{op.id}/use{i}"
        rel_end = use.end_us if use.end_us is not None else op.duration_us
        if use.resource in zones:
            errors.append(VMError(
                kind=VMErrorKind.QubitExplicitnessViolation, time_us=op.at_us,
                op_ids=[op.id], resource=use.resource,
                message=(f"op={op.id} uses zone {use.resource!r} anonymously; qubits "
                         f"are never fungible in an executable schedule."),
                suggestion=f"Name explicit qubits, e.g. {use.resource}[3] or "
                           f"{use.resource}[0:4].",
            ))
            continue
        if use.resource not in resources:
            ref = parse_qubit_ref(use.resource)
            if ref is not None and ref[0] in zones:
                z = zones[ref[0]]
                bad = [i for i in ref[1] if not 0 <= i < z.count]
                msg = (f"op={op.id}: qubit index {bad} out of range for zone "
                       f"{z.id!r} (count {z.count}).")
            else:
                msg = (f"op={op.id}: resource {use.resource!r} is not declared "
                       f"in the backend config.")
            errors.append(VMError(
                kind=VMErrorKind.UnknownResource, time_us=op.at_us, op_ids=[op.id],
                resource=use.resource, message=msg,
                suggestion=f"Declare {use.resource!r} (or its zone) in the backend "
                           f"or fix the index.",
            ))
            continue
        spec_kind = resources[use.resource].kind
        if (is_qubit_like_kind(spec_kind) and resources[use.resource].capacity > 1):
            errors.append(VMError(
                kind=VMErrorKind.QubitExplicitnessViolation, time_us=op.at_us,
                op_ids=[op.id], resource=use.resource,
                message=(f"op={op.id} draws from fungible qubit pool "
                         f"{use.resource!r} (kind {spec_kind}); qubit resources "
                         f"must be explicit capacity-1 resources."),
                suggestion=f"Declare {use.resource!r} as a zone and name explicit "
                           f"qubit indices.",
            ))
            continue
        ref = parse_qubit_ref(use.resource)
        if (ref is not None and ref[0] in zones and use.mode != UseMode.exclusive):
            errors.append(VMError(
                kind=VMErrorKind.QubitExplicitnessViolation, time_us=op.at_us,
                op_ids=[op.id], resource=use.resource,
                message=(f"op={op.id} uses qubit {use.resource} in "
                         f"{use.mode.value} mode; qubits are always held "
                         f"exclusively."),
                suggestion="Use exclusive mode for every qubit.",
            ))
            continue
        if use.start_us >= rel_end or rel_end > op.duration_us:
            errors.append(VMError(
                kind=VMErrorKind.InvalidInterval, time_us=op.at_us, op_ids=[op.id],
                resource=use.resource,
                message=(f"op={op.id}: use of {use.resource} has relative interval "
                         f"[{use.start_us}, {rel_end}) which is empty or exceeds the op "
                         f"duration {op.duration_us}us."),
                suggestion="Make 0 <= start_us < end_us <= duration_us for every resource use.",
            ))
            continue
        spec = resources[use.resource]
        if use.mode == UseMode.capacity and use.amount > spec.capacity:
            errors.append(VMError(
                kind=VMErrorKind.AllocationError, time_us=op.at_us, op_ids=[op.id],
                resource=use.resource,
                interval=TimeInterval(start_us=op.at_us + use.start_us,
                                      end_us=op.at_us + rel_end),
                message=(f"op={op.id} requests {use.amount} of {use.resource} but total "
                         f"capacity is only {spec.capacity}; this can never be satisfied."),
                suggestion=f"Reduce the requested amount to at most {spec.capacity} "
                           f"or increase the capacity of {use.resource}.",
            ))
            continue
        valid.append(ResolvedUse(
            resource=use.resource, mode=use.mode, amount=use.amount,
            start_us=op.at_us + use.start_us, end_us=op.at_us + rel_end,
            op_id=op.id, use_id=use_id,
        ))
    return valid, errors


def check_static(backend: BackendConfig, program: Program) -> StaticCheckResult:
    """Validate references and intervals; resolve uses to absolute times."""
    result = StaticCheckResult()
    services = backend.service_map()
    zones = backend.zone_map()
    touching = set(backend.qubit_touching_kinds)
    for op in program.ops:
        valid, errors = resolve_op_uses(op, backend)
        result.errors.extend(errors)
        result.resolved_uses.extend(valid)

        if op.kind in touching:
            names_qubit = any(
                (ref := parse_qubit_ref(u.resource)) is not None and ref[0] in zones
                for u in op.uses)
            if not names_qubit:
                result.errors.append(VMError(
                    kind=VMErrorKind.QubitExplicitnessViolation, time_us=op.at_us,
                    op_ids=[op.id],
                    message=(f"op={op.id} (do: {op.kind}) touches qubits but does "
                             f"not list explicit qubit IDs; fungible qubit-pool "
                             f"requests are not allowed in executable schedules."),
                    suggestion="Add a 'qubits:' list naming every qubit the op "
                               "touches, e.g. qubits: [data[3], syndrome[7]].",
                ))

        # Same-op exclusive self-overlap can never be scheduled.
        excl = [u for u in valid if u.mode == UseMode.exclusive]
        by_res: dict[str, list[ResolvedUse]] = defaultdict(list)
        for u in excl:
            by_res[u.resource].append(u)
        for res, uses in by_res.items():
            uses.sort(key=lambda u: u.start_us)
            for a, b in zip(uses, uses[1:]):
                if b.start_us < a.end_us:
                    result.errors.append(VMError(
                        kind=VMErrorKind.AllocationError, time_us=b.start_us,
                        op_ids=[op.id], resource=res,
                        interval=TimeInterval(start_us=b.start_us,
                                              end_us=min(a.end_us, b.end_us)),
                        message=(f"op={op.id} declares two overlapping exclusive uses of "
                                 f"{res}; an op cannot hold an exclusive resource twice."),
                        suggestion="Merge the two uses or make the intervals disjoint.",
                    ))

        # Token / service offsets must lie inside the op.
        for c in op.consumes:
            if c.at_us > op.duration_us:
                result.errors.append(VMError(
                    kind=VMErrorKind.InvalidInterval, time_us=op.at_us, op_ids=[op.id],
                    token=c.kind or c.id,
                    message=(f"op={op.id}: token consumption offset {c.at_us}us exceeds "
                             f"the op duration {op.duration_us}us."),
                    suggestion="Consume tokens at an offset within [0, duration_us].",
                ))
        for p in op.produces:
            if p.at_us is not None and p.at_us > op.duration_us:
                result.errors.append(VMError(
                    kind=VMErrorKind.InvalidInterval, time_us=op.at_us, op_ids=[op.id],
                    token=p.kind,
                    message=(f"op={op.id}: token production offset {p.at_us}us exceeds "
                             f"the op duration {op.duration_us}us."),
                    suggestion="Produce tokens at an offset within [0, duration_us].",
                ))
        for j in op.service:
            if j.service not in services:
                result.errors.append(VMError(
                    kind=VMErrorKind.UnknownResource, time_us=op.at_us, op_ids=[op.id],
                    service=j.service,
                    message=f"op={op.id}: service {j.service!r} is not declared in the backend config.",
                    suggestion=f"Declare {j.service!r} under 'resources' with kind: service, or fix the spelling.",
                ))
            elif j.submit_at_us > op.duration_us:
                result.errors.append(VMError(
                    kind=VMErrorKind.InvalidInterval, time_us=op.at_us, op_ids=[op.id],
                    service=j.service,
                    message=(f"op={op.id}: service submission offset {j.submit_at_us}us "
                             f"exceeds the op duration {op.duration_us}us."),
                    suggestion="Submit service jobs at an offset within [0, duration_us].",
                ))
    return result


# --------------------------------------------------------------------------
# Qubit reuse: explicit, timed resets between users
# --------------------------------------------------------------------------


def check_qubit_reuse(backend: BackendConfig, program: Program,
                      uses: list[ResolvedUse]) -> list[VMError]:
    """Qubits of reset-required zones follow a clean/dirty lifecycle.

    Per qubit, replay its uses chronologically as a state machine:

    * a *reset* op (kind in ``reset_kinds``) makes the qubit clean -- and
      must hold it for at least ``min_reset_us`` or it is itself a
      violation (the qubit is then treated as cleaned to avoid cascades);
    * a *dirtying* op (kind in ``dirty_kinds``; default: every non-reset
      op) leaves the qubit dirty when it releases it;
    * any op touching a dirty qubit -- other than the op that dirtied it,
      which may keep using its own qubit -- is a QubitReuseViolation: no
      qubit is reusable without an explicit, timed reset.

    Overlapping uses are left to the exclusivity checker.
    """
    errors: list[VMError] = []
    reset_zones = {z.id: z for z in backend.zones if z.reset_required}
    if not reset_zones:
        return errors
    op_kinds = {op.id: op.kind for op in program.ops}

    by_qubit: dict[str, list[ResolvedUse]] = defaultdict(list)
    for u in uses:
        zone = u.resource.split("[", 1)[0] if "[" in u.resource else None
        if zone in reset_zones:
            by_qubit[u.resource].append(u)

    for rid, q_uses in sorted(by_qubit.items()):
        zone = reset_zones[rid.split("[", 1)[0]]
        q_uses.sort(key=lambda u: (u.start_us, u.end_us))

        def dirties(kind: Optional[str]) -> bool:
            if kind in zone.reset_kinds:
                return False
            return zone.dirty_kinds is None or kind in zone.dirty_kinds

        dirty_by: Optional[ResolvedUse] = None  # the use that left it dirty
        initially_dirty = zone.start_dirty
        for u in q_uses:
            kind = op_kinds.get(u.op_id)
            if kind in zone.reset_kinds:
                initially_dirty = False
                if u.end_us - u.start_us < zone.min_reset_us:
                    errors.append(VMError(
                        kind=VMErrorKind.QubitReuseViolation, time_us=u.start_us,
                        op_ids=[u.op_id], resource=rid,
                        interval=TimeInterval(start_us=u.start_us, end_us=u.end_us),
                        message=(f"op={u.op_id} resets {rid} in only "
                                 f"{u.end_us - u.start_us}us; zone {zone.id!r} "
                                 f"requires resets of at least "
                                 f"{zone.min_reset_us}us."),
                        suggestion=f"Extend the reset to >= {zone.min_reset_us}us.",
                    ))
                dirty_by = None
                continue
            if initially_dirty:
                errors.append(VMError(
                    kind=VMErrorKind.QubitReuseViolation, time_us=u.start_us,
                    op_ids=[u.op_id], resource=rid,
                    interval=TimeInterval(start_us=u.start_us, end_us=u.end_us),
                    message=(f"op={u.op_id} uses {rid} at t={u.start_us}us before "
                             f"any reset/request; zone {zone.id!r} qubits start "
                             f"dirty and are undefined until first reset."),
                    suggestion=f"Issue a {zone.reset_kinds[0]!r} op of >= "
                               f"{zone.min_reset_us}us on {rid} first.",
                ))
                initially_dirty = False  # report once
            if dirty_by is not None and u.op_id != dirty_by.op_id:
                errors.append(VMError(
                    kind=VMErrorKind.QubitReuseViolation, time_us=u.start_us,
                    op_ids=[dirty_by.op_id, u.op_id], resource=rid,
                    interval=TimeInterval(start_us=dirty_by.end_us,
                                          end_us=max(u.start_us,
                                                     dirty_by.end_us + 1)),
                    message=(f"{rid} is used by op={u.op_id} at t={u.start_us}us "
                             f"without a reset after op={dirty_by.op_id} left it "
                             f"dirty at t={dirty_by.end_us}us; qubits of zone "
                             f"{zone.id!r} cannot be reused immediately."),
                    suggestion=(f"Insert a {zone.reset_kinds[0]!r} op of >= "
                                f"{zone.min_reset_us}us on {rid} between them, "
                                f"or retarget {u.op_id} to a fresh qubit."),
                ))
                dirty_by = None  # report once per dirtying, avoid cascades
            if dirties(kind):
                dirty_by = u
    return errors


# --------------------------------------------------------------------------
# Windowed throughput caps (e.g. syndrome-stream bandwidth, in bits)
# --------------------------------------------------------------------------


def check_throughput(backend: BackendConfig, program: Program) -> list[VMError]:
    """Audit windowed data-volume caps: for every cap, the total weight
    (bits) of matching ops STARTING in any ``window_us`` window must stay
    within ``max_weight``.  Windows anchored at matching ops' start times
    dominate all windows (the same decidable-anchoring rule as the Lean
    ``syndrome_bandwidth_ok``), so verdicts agree exactly.  One error per
    cap reports the WORST window with the counted volume.
    """
    errors: list[VMError] = []
    for cap in backend.throughput_caps:
        starts = sorted(op.at_us for op in program.ops if op.kind in cap.op_kinds)
        if not starts:
            continue
        worst_t0, worst_n = None, 0
        for t0 in starts:
            n = sum(1 for t in starts if t0 <= t < t0 + cap.window_us)
            if n > worst_n:
                worst_t0, worst_n = t0, n
        volume = worst_n * cap.weight_per_op
        if volume > cap.max_weight:
            errors.append(VMError(
                kind=VMErrorKind.ThroughputExceeded, time_us=worst_t0,
                interval=TimeInterval(start_us=worst_t0,
                                      end_us=worst_t0 + cap.window_us),
                resource=cap.id,
                message=(f"{cap.id}: {worst_n} {'/'.join(cap.op_kinds)} op(s) x "
                         f"{cap.weight_per_op} {cap.unit} = {volume} {cap.unit} "
                         f"in [{worst_t0}, {worst_t0 + cap.window_us})us exceeds "
                         f"the link's {cap.max_weight} {cap.unit} per "
                         f"{cap.window_us}us."),
                suggestion=(f"Spread the readouts (at most "
                            f"{cap.max_weight // cap.weight_per_op} such ops per "
                            f"{cap.window_us}us fit), reduce the per-op data "
                            f"volume, or widen the link."),
            ))
    return errors


# --------------------------------------------------------------------------
# Dependencies
# --------------------------------------------------------------------------


def check_dependencies(program: Program) -> list[VMError]:
    """Every dependency must exist and finish at or before the dependent starts."""
    errors: list[VMError] = []
    ops = program.op_map()
    for op in program.ops:
        for dep_id in op.deps:
            if dep_id not in ops:
                errors.append(VMError(
                    kind=VMErrorKind.UnknownDependency, time_us=op.at_us, op_ids=[op.id],
                    message=f"op={op.id} depends on unknown op {dep_id!r}.",
                    suggestion="Fix the dependency id or add the missing op. Note that "
                               "an op with 'repeat' becomes instances id@0, id@1, ...",
                ))
                continue
            dep = ops[dep_id]
            if dep_id == op.id or dep.end_us > op.at_us:
                errors.append(VMError(
                    kind=VMErrorKind.DependencyViolation, time_us=op.at_us,
                    op_ids=[op.id, dep_id],
                    interval=TimeInterval(start_us=min(op.at_us, dep.at_us),
                                          end_us=dep.end_us),
                    message=(f"op={op.id} starts at t={op.at_us}us but its dependency "
                             f"{dep_id} only finishes at t={dep.end_us}us."),
                    suggestion=f"Delay {op.id} by {dep.end_us - op.at_us}us "
                               f"(start it at t={dep.end_us}us or later).",
                ))
    return errors


# --------------------------------------------------------------------------
# Resources: sweep-line over each resource
# --------------------------------------------------------------------------


@dataclass
class ResourceCheckResult:
    errors: list[VMError] = field(default_factory=list)
    events: list[Event] = field(default_factory=list)
    #: per resource: step series [(t, usage), ...]; usage holds until next point
    usage_series: dict[str, list[tuple[int, int]]] = field(default_factory=dict)
    peak_usage: dict[str, int] = field(default_factory=dict)
    #: integral of usage over time (for utilization)
    busy_area: dict[str, int] = field(default_factory=dict)
    #: all resolved intervals, for the certificate
    intervals: dict[str, list[ResolvedUse]] = field(default_factory=dict)


def check_resources(backend: BackendConfig, uses: list[ResolvedUse]) -> ResourceCheckResult:
    """Sweep every resource's timeline for conflicts and capacity overuse.

    Usage accounting: a ``capacity`` use contributes its amount; an
    ``exclusive`` use contributes the whole capacity (it owns the resource);
    a ``shared`` use contributes nothing but conflicts with exclusive holds.
    """
    result = ResourceCheckResult()
    by_resource: dict[str, list[ResolvedUse]] = defaultdict(list)
    for u in uses:
        by_resource[u.resource].append(u)

    for spec in backend.resources:
        rid = spec.id
        r_uses = by_resource.get(rid, [])
        result.intervals[rid] = sorted(r_uses, key=lambda u: (u.start_us, u.end_us, u.op_id))
        result.usage_series[rid] = [(0, 0)]
        result.peak_usage[rid] = 0
        result.busy_area[rid] = 0
        if not r_uses:
            continue

        for u in r_uses:
            result.events.append(Event(
                time_us=u.start_us, kind=EventKind.resource_reserved, op_id=u.op_id,
                resource=rid, amount=u.amount,
                message=f"{u.op_id} reserves {u.amount} of {rid} ({u.mode.value})",
                details={"mode": u.mode.value, "until_us": u.end_us},
            ))
            result.events.append(Event(
                time_us=u.end_us, kind=EventKind.resource_released, op_id=u.op_id,
                resource=rid, amount=u.amount,
                message=f"{u.op_id} releases {u.amount} of {rid}",
            ))

        starts: dict[int, list[ResolvedUse]] = defaultdict(list)
        ends: dict[int, list[ResolvedUse]] = defaultdict(list)
        for u in r_uses:
            starts[u.start_us].append(u)
            ends[u.end_us].append(u)
        points = sorted(set(starts) | set(ends))

        active: dict[str, ResolvedUse] = {}
        cap_demand = 0
        excl_count = 0
        series = result.usage_series[rid]
        prev_usage = 0
        # open violation accumulators: None or dict(start, max_demand, ops)
        open_conflict: Optional[dict] = None
        open_capacity: Optional[dict] = None

        def close_conflict(at: int) -> None:
            nonlocal open_conflict
            v = open_conflict
            open_conflict = None
            if v is None:
                return
            ops = sorted(v["ops"])
            result.errors.append(VMError(
                kind=VMErrorKind.ResourceConflict, time_us=v["start"],
                interval=TimeInterval(start_us=v["start"], end_us=at),
                op_ids=ops, resource=rid,
                message=(f"resource={rid}: exclusive use overlaps other uses during "
                         f"[{v['start']}, {at})us; involved ops: {', '.join(ops)}."),
                suggestion="Serialize the conflicting ops or use capacity mode if the "
                           "resource is actually divisible.",
            ))

        def close_capacity(at: int) -> None:
            nonlocal open_capacity
            v = open_capacity
            open_capacity = None
            if v is None:
                return
            ops = sorted(v["ops"])
            result.errors.append(VMError(
                kind=VMErrorKind.CapacityExceeded, time_us=v["start"],
                interval=TimeInterval(start_us=v["start"], end_us=at),
                op_ids=ops, resource=rid,
                message=(f"resource={rid}: demand {v['max_demand']} exceeds capacity "
                         f"{spec.capacity} during [{v['start']}, {at})us."),
                suggestion=f"Reschedule one of: {', '.join(ops[:6])}"
                           f"{', ...' if len(ops) > 6 else ''} or increase capacity.",
            ))

        for idx, t in enumerate(points):
            for u in ends.get(t, ()):  # releases first (half-open intervals)
                del active[u.use_id]
                if u.mode == UseMode.capacity:
                    cap_demand -= u.amount
                elif u.mode == UseMode.exclusive:
                    excl_count -= 1
            for u in starts.get(t, ()):
                active[u.use_id] = u
                if u.mode == UseMode.capacity:
                    cap_demand += u.amount
                elif u.mode == UseMode.exclusive:
                    excl_count += 1

            usage = cap_demand + excl_count * spec.capacity
            if usage != prev_usage:
                if series[-1][0] == t:
                    series[-1] = (t, usage)
                else:
                    series.append((t, usage))
                prev_usage = usage
            result.peak_usage[rid] = max(result.peak_usage[rid], usage)
            if idx + 1 < len(points):
                result.busy_area[rid] += usage * (points[idx + 1] - t)

            in_conflict = (excl_count >= 1 and len(active) >= 2) or excl_count >= 2
            over_capacity = cap_demand > spec.capacity
            if in_conflict:
                if open_conflict is None:
                    open_conflict = {"start": t, "ops": set()}
                open_conflict["ops"].update(u.op_id for u in active.values())
            else:
                close_conflict(t)
            if over_capacity:
                if open_capacity is None:
                    open_capacity = {"start": t, "max_demand": 0, "ops": set()}
                open_capacity["max_demand"] = max(open_capacity["max_demand"], cap_demand)
                open_capacity["ops"].update(
                    u.op_id for u in active.values() if u.mode == UseMode.capacity)
            else:
                close_capacity(t)

        # all uses end at the last point, so violations are closed by then;
        # close defensively anyway.
        close_conflict(points[-1])
        close_capacity(points[-1])

    return result


# --------------------------------------------------------------------------
# Tokens: chronological ledger per kind
# --------------------------------------------------------------------------


@dataclass
class TokenCheckResult:
    errors: list[VMError] = field(default_factory=list)
    events: list[Event] = field(default_factory=list)
    tokens: list[Token] = field(default_factory=list)
    #: per kind: step series [(t, buffer occupancy), ...]
    occupancy_series: dict[str, list[tuple[int, int]]] = field(default_factory=dict)
    produced: dict[str, int] = field(default_factory=dict)   # includes initial inventory
    consumed: dict[str, int] = field(default_factory=dict)
    peak_occupancy: dict[str, int] = field(default_factory=dict)
    #: flat chronological token event order, for the certificate
    token_event_order: list[dict] = field(default_factory=list)


def check_tokens(backend: BackendConfig, program: Program,
                 extra_productions: Optional[list[tuple[int, str, str]]] = None
                 ) -> TokenCheckResult:
    """Replay all token productions/consumptions in chronological order.

    Semantics:
      * a token produced at ``t`` with ttl ``d`` is consumable while
        ``t <= now < t + d`` (no ttl = never expires);
      * kind-based consumption takes the oldest *fresh* token (FIFO);
      * tokens occupy buffer space from production until consumption --
        expired tokens still occupy space until (if ever) discarded, which
        the MVP never does;
      * at equal times productions are processed before consumptions, and
        buffer capacity is checked after each production.

    ``extra_productions`` carries productions whose times were *computed*
    rather than declared -- service-job ``result_token`` completions --
    as (time, kind, producing op id) triples.
    """
    result = TokenCheckResult()
    seq = itertools.count()

    # ---- gather happenings -------------------------------------------------
    PRODUCE, CONSUME = 0, 1
    happenings: list[tuple[int, int, int, object, object]] = []  # (t, phase, seq, op-like, spec)
    planned_kind_times: dict[str, list[int]] = defaultdict(list)
    planned_ids: dict[str, tuple[int, str]] = {}  # explicit id -> (time, op)
    id_collisions: set[str] = set()

    @dataclass
    class _JobProducer:  # op-like stand-in for a completed service job
        id: str

    for t, kind, op_id in (extra_productions or []):
        happenings.append((t, PRODUCE, next(seq), _JobProducer(id=op_id),
                           TokenProduce(kind=kind)))
        planned_kind_times[kind].append(t)

    for op in program.ops:
        for p in op.produces:
            t = op.at_us + p.at_us if p.at_us is not None else op.end_us
            happenings.append((t, PRODUCE, next(seq), op, p))
            planned_kind_times[p.kind].extend([t] * p.count)
            if p.id is not None:
                if p.id in planned_ids:
                    id_collisions.add(p.id)
                    result.errors.append(VMError(
                        kind=VMErrorKind.AllocationError, time_us=t, op_ids=[op.id],
                        token=p.id,
                        message=(f"op={op.id} produces token id {p.id!r} which is already "
                                 f"produced by op={planned_ids[p.id][1]}."),
                        suggestion="Give every explicitly named token a unique id.",
                    ))
                else:
                    planned_ids[p.id] = (t, op.id)
        for c in op.consumes:
            happenings.append((op.at_us + c.at_us, CONSUME, next(seq), op, c))

    happenings.sort(key=lambda h: (h[0], h[1], h[2]))

    # ---- ledger state ------------------------------------------------------
    buffers: dict[str, list[Token]] = defaultdict(list)  # FIFO order per kind
    all_tokens: dict[str, Token] = {}
    occupancy: dict[str, int] = defaultdict(int)
    counter: dict[str, int] = defaultdict(int)

    known_kinds = set(backend.token_initial_inventory) | set(planned_kind_times)

    def series_for(kind: str) -> list[tuple[int, int]]:
        return result.occupancy_series.setdefault(kind, [(0, 0)])

    def record_occupancy(kind: str, t: int) -> None:
        s = series_for(kind)
        if s and s[-1][0] == t:
            s[-1] = (t, occupancy[kind])
        else:
            s.append((t, occupancy[kind]))
        result.peak_occupancy[kind] = max(result.peak_occupancy.get(kind, 0), occupancy[kind])

    def add_token(kind: str, t: int, producer: Optional[str], explicit_id: Optional[str],
                  ttl_override: Optional[int], emit_event: bool) -> Token:
        if explicit_id is not None and explicit_id not in id_collisions:
            tok_id = explicit_id
        elif explicit_id is not None:
            tok_id = f"{explicit_id}#dup{counter[explicit_id]}"
            counter[explicit_id] += 1
        else:
            owner = producer or "init"
            # auto ids must never collide with explicit ids (past or planned)
            while True:
                tok_id = f"{owner}/{kind}/{counter[owner + '/' + kind]}"
                counter[owner + "/" + kind] += 1
                if tok_id not in all_tokens and tok_id not in planned_ids:
                    break
        ttl = ttl_override if ttl_override is not None else backend.token_ttl_us.get(kind)
        token = Token(
            id=tok_id, kind=kind, produced_at_us=t, producer_op=producer,
            expires_at_us=(t + ttl) if ttl is not None else None,
        )
        buffers[kind].append(token)
        all_tokens[tok_id] = token
        result.tokens.append(token)
        occupancy[kind] += 1
        result.produced[kind] = result.produced.get(kind, 0) + 1
        result.token_event_order.append(
            {"t_us": t, "type": "produce", "kind": kind, "id": tok_id, "op": producer,
             "expires_at_us": token.expires_at_us})
        if emit_event:
            result.events.append(Event(
                time_us=t, kind=EventKind.token_produced, op_id=producer,
                token_id=tok_id, token_kind=kind,
                message=f"token {tok_id} ({kind}) produced"
                        + (f" by {producer}" if producer else " (initial inventory)"),
                details={"expires_at_us": token.expires_at_us},
            ))
        return token

    def check_buffer(kind: str, t: int, producer_op: Optional[str]) -> None:
        cap = backend.token_buffer_capacity.get(kind)
        if cap is not None and occupancy[kind] > cap:
            result.errors.append(VMError(
                kind=VMErrorKind.TokenBufferOverflow, time_us=t,
                op_ids=[producer_op] if producer_op else [], token=kind,
                message=(f"token buffer for {kind} holds {occupancy[kind]} tokens at "
                         f"t={t}us, exceeding capacity {cap}."),
                suggestion="Consume tokens sooner, slow the producers, or increase "
                           f"the {kind} buffer capacity.",
            ))

    def fresh(token: Token, t: int) -> bool:
        return token.expires_at_us is None or t < token.expires_at_us

    def consume_token(token: Token, t: int, op: Op) -> None:
        token.consumed_at_us = t
        token.consumer_op = op.id
        buffers[token.kind].remove(token)
        occupancy[token.kind] -= 1
        result.consumed[token.kind] = result.consumed.get(token.kind, 0) + 1
        record_occupancy(token.kind, t)
        result.token_event_order.append(
            {"t_us": t, "type": "consume", "kind": token.kind, "id": token.id, "op": op.id})
        result.events.append(Event(
            time_us=t, kind=EventKind.token_consumed, op_id=op.id,
            token_id=token.id, token_kind=token.kind,
            message=f"{op.id} consumes token {token.id} ({token.kind})",
            details={"age_us": t - token.produced_at_us},
        ))

    def next_production_after(kind: str, t: int) -> Optional[int]:
        times = [x for x in planned_kind_times.get(kind, []) if x > t]
        return min(times) if times else None

    def starvation_suggestion(kind: str, t: int) -> str:
        nxt = next_production_after(kind, t)
        if nxt is not None:
            return (f"Delay the op by {nxt - t}us (next {kind} is produced at t={nxt}us), "
                    f"add producers/factories, or increase the initial {kind} inventory.")
        return (f"No future {kind} production is scheduled; add producer ops/factories "
                f"or initial {kind} inventory.")

    # ---- initial inventory -------------------------------------------------
    for kind, count in backend.token_initial_inventory.items():
        emit = count <= TOKEN_EVENT_LIMIT
        for _ in range(count):
            add_token(kind, 0, None, None, None, emit)
        record_occupancy(kind, 0)
        check_buffer(kind, 0, None)

    # ---- replay ------------------------------------------------------------
    for t, phase, _, op, spec in happenings:
        if phase == PRODUCE:
            emit = spec.count <= TOKEN_EVENT_LIMIT
            for _ in range(spec.count):
                add_token(spec.kind, t, op.id, spec.id, spec.ttl_us, emit)
            if not emit:
                result.events.append(Event(
                    time_us=t, kind=EventKind.token_produced, op_id=op.id,
                    token_kind=spec.kind, amount=spec.count,
                    message=f"{op.id} produces {spec.count} {spec.kind} tokens (batch)",
                ))
            record_occupancy(spec.kind, t)
            check_buffer(spec.kind, t, op.id)
            continue

        # ---- consumption ----
        if spec.id is not None:
            token = all_tokens.get(spec.id)
            if token is None:
                planned = planned_ids.get(spec.id)
                if planned is not None and planned[0] > t:
                    msg = (f"op={op.id} consumes token {spec.id!r} at t={t}us, but it is "
                           f"only produced at t={planned[0]}us by op={planned[1]}.")
                    sugg = f"Delay {op.id} by {planned[0] - t}us."
                else:
                    msg = f"op={op.id} consumes token {spec.id!r}, which is never produced."
                    sugg = "Fix the token id or add a producer op."
                result.errors.append(VMError(
                    kind=VMErrorKind.TokenUnavailable, time_us=t, op_ids=[op.id],
                    token=spec.id, message=msg, suggestion=sugg,
                ))
            elif token.consumed_at_us is not None:
                result.errors.append(VMError(
                    kind=VMErrorKind.DoubleConsume, time_us=t,
                    op_ids=[op.id, token.consumer_op], token=spec.id,
                    message=(f"op={op.id} consumes token {spec.id!r} at t={t}us, but it "
                             f"was already consumed by op={token.consumer_op} at "
                             f"t={token.consumed_at_us}us."),
                    suggestion="Tokens are single-use; produce another token or remove "
                               "one of the consumers.",
                ))
            elif not fresh(token, t):
                result.errors.append(VMError(
                    kind=VMErrorKind.TokenFreshnessViolation, time_us=t, op_ids=[op.id],
                    token=spec.id,
                    message=(f"op={op.id} consumes token {spec.id!r} at t={t}us, but it "
                             f"expired at t={token.expires_at_us}us (produced at "
                             f"t={token.produced_at_us}us)."),
                    suggestion=f"Consume it before t={token.expires_at_us}us, or "
                               f"increase the ttl.",
                ))
            else:
                consume_token(token, t, op)
            continue

        kind = spec.kind
        needed = spec.count
        taken = 0
        while taken < needed:
            candidate = next((tok for tok in buffers[kind] if fresh(tok, t)), None)
            if candidate is None:
                break
            consume_token(candidate, t, op)
            taken += 1
        if taken < needed:
            shortfall = needed - taken
            stale = [tok for tok in buffers[kind] if not fresh(tok, t)]
            if stale:
                newest = max(stale, key=lambda tok: tok.expires_at_us or 0)
                result.errors.append(VMError(
                    kind=VMErrorKind.TokenFreshnessViolation, time_us=t, op_ids=[op.id],
                    token=kind,
                    message=(f"op={op.id} needs {shortfall} more {kind} token(s) at "
                             f"t={t}us; {len(stale)} are in the buffer but all expired "
                             f"(newest expired at t={newest.expires_at_us}us)."),
                    suggestion="Consume tokens sooner after production or increase "
                               f"the {kind} ttl_us.",
                ))
            elif kind not in known_kinds:
                result.errors.append(VMError(
                    kind=VMErrorKind.TokenUnavailable, time_us=t, op_ids=[op.id], token=kind,
                    message=(f"op={op.id} consumes token kind {kind!r}, which no op "
                             f"produces and which has no initial inventory."),
                    suggestion=f"Add a producer of {kind} or declare initial inventory.",
                ))
            else:
                result.errors.append(VMError(
                    kind=VMErrorKind.TokenUnavailable, time_us=t, op_ids=[op.id], token=kind,
                    message=(f"op={op.id} consumes {needed} {kind} token(s) at t={t}us, "
                             f"but only {taken} {'was' if taken == 1 else 'were'} "
                             f"available."),
                    suggestion=starvation_suggestion(kind, t),
                ))

    return result


# --------------------------------------------------------------------------
# Services: finite-worker FIFO queue simulation
# --------------------------------------------------------------------------


@dataclass
class BatchRecord:
    """Summary of one op's batch of identical service jobs."""

    batch_id: str
    service: str
    op_id: str
    submit_time_us: int
    count: int
    processing_time_us: int
    first_start_us: int
    last_complete_us: int
    max_latency_observed_us: int
    deadline_misses: int
    result_token: Optional[str] = None


@dataclass
class ServiceCheckResult:
    errors: list[VMError] = field(default_factory=list)
    events: list[Event] = field(default_factory=list)
    #: per-job records (only materialized for services with few jobs)
    job_records: dict[str, list[ServiceJobRecord]] = field(default_factory=dict)
    batches: dict[str, list[BatchRecord]] = field(default_factory=dict)
    queue_series: dict[str, list[tuple[int, int]]] = field(default_factory=dict)
    busy_series: dict[str, list[tuple[int, int]]] = field(default_factory=dict)
    max_queue_length: dict[str, int] = field(default_factory=dict)
    peak_busy_workers: dict[str, int] = field(default_factory=dict)
    total_jobs: dict[str, int] = field(default_factory=dict)
    busy_area: dict[str, int] = field(default_factory=dict)  # sum of processing times
    #: tokens produced by completed jobs: (completion time, kind, producing op)
    result_token_productions: list[tuple[int, str, str]] = field(default_factory=list)


def check_services(backend: BackendConfig, program: Program) -> ServiceCheckResult:
    """Simulate each service's FIFO queue with finite identical workers.

    Jobs are served in submission order (ties broken by program order).  A
    job submitted at ``t`` starts as soon as a worker is free (possibly at
    ``t``), runs ``processing_time_us``, and must finish by
    ``t + max_latency_us``.  The queue holds jobs submitted but not yet
    started; its length must stay within ``queue_capacity``.
    """
    result = ServiceCheckResult()
    op_index = {op.id: i for i, op in enumerate(program.ops)}

    # ---- gather job batches per service ------------------------------------
    @dataclass
    class _Batch:
        batch_id: str
        op_id: str
        submit: int
        count: int
        pt: int
        bidx: int  # numeric request index within the op (tie-break, NOT the id string)
        result_token: Optional[str] = None

    batches_by_service: dict[str, list[_Batch]] = defaultdict(list)
    for op in program.ops:
        per_service_idx: dict[str, int] = defaultdict(int)
        for req in op.service:
            if req.service not in backend.service_map():
                continue  # reported by check_static
            pt = (req.processing_time_us if req.processing_time_us is not None
                  else backend.default_latencies_us.get(req.service, 1))
            bidx = per_service_idx[req.service]
            per_service_idx[req.service] += 1
            batches_by_service[req.service].append(_Batch(
                batch_id=f"{op.id}/{req.service}/{bidx}",
                op_id=op.id, submit=op.at_us + req.submit_at_us, count=req.count,
                pt=pt, bidx=bidx, result_token=req.result_token,
            ))

    for spec in backend.services:
        sid = spec.id
        batches = sorted(batches_by_service.get(sid, []),
                         key=lambda b: (b.submit, op_index[b.op_id], b.bidx))
        total = sum(b.count for b in batches)
        result.total_jobs[sid] = total
        result.queue_series[sid] = [(0, 0)]
        result.busy_series[sid] = [(0, 0)]
        result.max_queue_length[sid] = 0
        result.peak_busy_workers[sid] = 0
        result.busy_area[sid] = 0
        result.batches[sid] = []
        if not batches:
            continue

        detail_events = total <= EVENT_DETAIL_LIMIT
        keep_job_records = total <= JOB_RECORD_LIMIT
        if keep_job_records:
            result.job_records[sid] = []

        # ---- FIFO multi-worker simulation ----
        workers = [0] * spec.workers  # next-free times
        heapq.heapify(workers)
        # queue/busy step series via +-1 deltas; -1 sorts before +1 at equal t
        queue_deltas: list[tuple[int, int]] = []
        busy_deltas: list[tuple[int, int]] = []
        submissions_per_us: dict[int, int] = defaultdict(int)
        completions_per_us: dict[int, int] = defaultdict(int)

        for batch in batches:
            first_start = None
            last_complete = 0
            worst_latency = 0
            misses = 0
            submissions_per_us[batch.submit] += batch.count
            for j in range(batch.count):
                free = heapq.heappop(workers)
                start = max(batch.submit, free)
                complete = start + batch.pt
                heapq.heappush(workers, complete)
                completions_per_us[complete] += 1
                if batch.result_token is not None:
                    result.result_token_productions.append(
                        (complete, batch.result_token, batch.op_id))
                if start > batch.submit:
                    queue_deltas.append((batch.submit, +1))
                    queue_deltas.append((start, -1))
                busy_deltas.append((start, +1))
                busy_deltas.append((complete, -1))
                result.busy_area[sid] += batch.pt
                latency = complete - batch.submit
                worst_latency = max(worst_latency, latency)
                if latency > spec.max_latency_us:
                    misses += 1
                first_start = start if first_start is None else min(first_start, start)
                last_complete = max(last_complete, complete)
                job_id = f"{batch.batch_id}#{j}"
                if keep_job_records:
                    result.job_records[sid].append(ServiceJobRecord(
                        job_id=job_id, service=sid, op_id=batch.op_id,
                        submit_time_us=batch.submit, start_time_us=start,
                        complete_time_us=complete, processing_time_us=batch.pt,
                        deadline_us=batch.submit + spec.max_latency_us,
                    ))
                if detail_events:
                    result.events.append(Event(
                        time_us=batch.submit, kind=EventKind.service_job_submitted,
                        op_id=batch.op_id, service=sid, job_id=job_id,
                        message=f"{batch.op_id} submits job {job_id} to {sid}"))
                    result.events.append(Event(
                        time_us=start, kind=EventKind.service_job_started,
                        op_id=batch.op_id, service=sid, job_id=job_id,
                        message=f"job {job_id} starts on {sid}"))
                    result.events.append(Event(
                        time_us=complete, kind=EventKind.service_job_completed,
                        op_id=batch.op_id, service=sid, job_id=job_id,
                        message=f"job {job_id} completes on {sid} "
                                f"(latency {complete - batch.submit}us)",
                        details={"latency_us": complete - batch.submit,
                                 "deadline_us": batch.submit + spec.max_latency_us}))

            record = BatchRecord(
                batch_id=batch.batch_id, service=sid, op_id=batch.op_id,
                submit_time_us=batch.submit, count=batch.count,
                processing_time_us=batch.pt,
                first_start_us=first_start if first_start is not None else batch.submit,
                last_complete_us=last_complete,
                max_latency_observed_us=worst_latency,
                deadline_misses=misses,
                result_token=batch.result_token,
            )
            result.batches[sid].append(record)
            if not detail_events:
                result.events.append(Event(
                    time_us=batch.submit, kind=EventKind.service_job_submitted,
                    op_id=batch.op_id, service=sid, job_id=batch.batch_id,
                    amount=batch.count,
                    message=f"{batch.op_id} submits {batch.count} jobs to {sid} (batch)"))
                result.events.append(Event(
                    time_us=last_complete, kind=EventKind.service_job_completed,
                    op_id=batch.op_id, service=sid, job_id=batch.batch_id,
                    amount=batch.count,
                    message=f"batch {batch.batch_id} fully completes on {sid} "
                            f"(worst latency {worst_latency}us)",
                    details={"worst_latency_us": worst_latency, "misses": misses}))

            if misses:
                example = (f" e.g. a job submitted at t={batch.submit}us completes at "
                           f"t={batch.submit + worst_latency}us.")
                result.errors.append(VMError(
                    kind=VMErrorKind.DeadlineMiss, time_us=batch.submit,
                    interval=TimeInterval(start_us=batch.submit, end_us=last_complete),
                    op_ids=[batch.op_id], service=sid,
                    message=(f"service={sid}: {misses} of {batch.count} job(s) from "
                             f"{batch.op_id} exceed max_latency_us={spec.max_latency_us} "
                             f"(worst latency {worst_latency}us);" + example),
                    suggestion="Add workers, reduce the job processing time, or spread "
                               "submissions over time.",
                ))

        # ---- queue / busy step series + overflow detection ----
        def build_series(deltas: list[tuple[int, int]]) -> list[tuple[int, int]]:
            deltas.sort()  # (t, -1) sorts before (t, +1)
            series = [(0, 0)]
            level = 0
            for t, d in deltas:
                level += d
                if series[-1][0] == t:
                    series[-1] = (t, level)
                else:
                    series.append((t, level))
            return series

        qseries = build_series(queue_deltas)
        bseries = build_series(busy_deltas)
        result.queue_series[sid] = qseries
        result.busy_series[sid] = bseries
        result.max_queue_length[sid] = max((v for _, v in qseries), default=0)
        result.peak_busy_workers[sid] = max((v for _, v in bseries), default=0)

        open_overflow: Optional[dict] = None
        for t, level in qseries:
            if level > spec.queue_capacity:
                if open_overflow is None:
                    open_overflow = {"start": t, "max": level}
                open_overflow["max"] = max(open_overflow["max"], level)
            elif open_overflow is not None:
                result.errors.append(VMError(
                    kind=VMErrorKind.ServiceQueueOverflow, time_us=open_overflow["start"],
                    interval=TimeInterval(start_us=open_overflow["start"], end_us=t),
                    service=sid,
                    message=(f"service={sid}: queue length {open_overflow['max']} exceeds "
                             f"capacity {spec.queue_capacity} during "
                             f"[{open_overflow['start']}, {t})us."),
                    suggestion="Add workers, increase queue_capacity, or spread job "
                               "submissions over time.",
                ))
                open_overflow = None
        if open_overflow is not None:  # queue never drained below capacity
            result.errors.append(VMError(
                kind=VMErrorKind.ServiceQueueOverflow, time_us=open_overflow["start"],
                service=sid,
                message=(f"service={sid}: queue length {open_overflow['max']} exceeds "
                         f"capacity {spec.queue_capacity} from t={open_overflow['start']}us "
                         f"onwards."),
                suggestion="Add workers, increase queue_capacity, or spread job "
                           "submissions over time.",
            ))

        # ---- bandwidth checks (ServiceCapacityExceeded) ----
        if spec.input_bandwidth is not None:
            for t in sorted(submissions_per_us):
                n = submissions_per_us[t]
                if n > spec.input_bandwidth:
                    result.errors.append(VMError(
                        kind=VMErrorKind.ServiceCapacityExceeded, time_us=t, service=sid,
                        message=(f"service={sid}: {n} jobs submitted at t={t}us exceeds "
                                 f"input bandwidth {spec.input_bandwidth} per us."),
                        suggestion="Stagger submissions or raise input_bandwidth.",
                    ))
        if spec.output_bandwidth is not None:
            for t in sorted(completions_per_us):
                n = completions_per_us[t]
                if n > spec.output_bandwidth:
                    result.errors.append(VMError(
                        kind=VMErrorKind.ServiceCapacityExceeded, time_us=t, service=sid,
                        message=(f"service={sid}: {n} jobs complete at t={t}us exceeds "
                                 f"output bandwidth {spec.output_bandwidth} per us."),
                        suggestion="Stagger submissions or raise output_bandwidth.",
                    ))

    return result
