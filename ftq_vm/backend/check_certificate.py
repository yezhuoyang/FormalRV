"""Independent certificate checker.

Re-verifies a ``certificate.json`` WITHOUT the simulator: only stdlib json,
sorting and plain loops.  Deliberately small and boring -- every check here
is meant to have a direct Lean predicate later:

    theorem checked_certificate_sound :
      CheckCertificate cert = true ->
      ValidFiniteServiceSchedule backend cert.schedule

Checks performed:

* structure        -- format / version / required keys;
* ops              -- well-formed half-open intervals, unique ids;
* dependencies     -- every dep exists and finishes before the dependent;
* resources        -- replay the boundary sweep over the resolved intervals:
                      capacity sums, exclusive overlaps, claimed peaks;
* declarations     -- the per-op declared uses/consumes/produces/jobs agree
                      exactly with the per-resource intervals, the token
                      event order and the service batches (the certificate
                      is *closed*: no hidden or dropped work);
* tokens           -- replay the ledger: produce-before-consume, single
                      consumption, freshness, buffer bounds, claimed peaks;
* services         -- replay the FIFO multi-worker recurrence over the
                      batches: claimed starts/completions/misses, queue
                      bounds, deadline misses;
* verdict          -- a "pass" certificate must re-verify with zero
                      violations and an empty error list; a "fail"
                      certificate must claim at least one error.

Usage:
    python -m ftq_vm check-cert out/certificate.json
"""

from __future__ import annotations

import heapq
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

SUPPORTED_FORMAT = "ftqvm-certificate"
SUPPORTED_VERSION = 2


class CertLoadError(Exception):
    """The certificate file could not be read or parsed as JSON."""


def _load_cert(path: str):
    """Read and JSON-parse a certificate file, turning every filesystem/parse
    failure into a clean :class:`CertLoadError` (kept stdlib-only so this
    checker stays independent of the loader, mirroring the Lean predicate)."""
    p = Path(path)
    if not p.exists():
        raise CertLoadError(f"file not found: {p}")
    if p.is_dir():
        raise CertLoadError(f"expected a file but found a directory: {p}")
    try:
        text = p.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise CertLoadError(f"could not read {p}: {exc}") from exc
    try:
        return json.loads(text)
    except json.JSONDecodeError as exc:
        raise CertLoadError(f"{p}: not valid JSON: {exc}") from exc


def _check_structure(cert: dict, defects: list[str]) -> None:
    if cert.get("format") != SUPPORTED_FORMAT:
        defects.append(f"format is {cert.get('format')!r}, expected {SUPPORTED_FORMAT!r}")
    if cert.get("version") != SUPPORTED_VERSION:
        defects.append(f"version is {cert.get('version')!r}, expected {SUPPORTED_VERSION}")
    for key in ("ops", "resources", "token_events", "services", "errors",
                "verdict", "total_runtime_us"):
        if key not in cert:
            defects.append(f"missing key {key!r}")


def _check_ops(cert: dict, defects: list[str]) -> dict[str, dict]:
    ops = {}
    for op in cert.get("ops", []):
        if op["id"] in ops:
            defects.append(f"duplicate op id {op['id']!r}")
        if not (0 <= op["start_us"] < op["end_us"]):
            defects.append(f"op {op['id']}: bad interval "
                           f"[{op['start_us']}, {op['end_us']})")
        ops[op["id"]] = op
    return ops


def _check_dependencies(ops: dict[str, dict], violations: list[str]) -> None:
    for op in ops.values():
        for dep in op.get("deps", []):
            if dep not in ops:
                violations.append(f"op {op['id']}: unknown dependency {dep!r}")
            elif ops[dep]["end_us"] > op["start_us"]:
                violations.append(
                    f"op {op['id']} starts at {op['start_us']}us before its "
                    f"dependency {dep} ends at {ops[dep]['end_us']}us")


def _check_resources(cert: dict, defects: list[str], violations: list[str]) -> None:
    for res in cert.get("resources", []):
        rid, capacity = res["id"], res["capacity"]
        intervals = res.get("intervals", [])
        for u in intervals:
            if not (0 <= u["start_us"] < u["end_us"]):
                defects.append(f"resource {rid}: bad use interval "
                               f"[{u['start_us']}, {u['end_us']}) by op {u['op']}")
            if u["amount"] < 1:
                defects.append(f"resource {rid}: non-positive amount by op {u['op']}")
        boundaries = sorted({u["start_us"] for u in intervals}
                            | {u["end_us"] for u in intervals})
        peak = 0
        for t in boundaries:
            active = [u for u in intervals if u["start_us"] <= t < u["end_us"]]
            cap_sum = sum(u["amount"] for u in active if u["mode"] == "capacity")
            excl = sum(1 for u in active if u["mode"] == "exclusive")
            usage = cap_sum + excl * capacity
            peak = max(peak, usage)
            if cap_sum > capacity:
                violations.append(
                    f"resource {rid}: demand {cap_sum} > capacity {capacity} at t={t}us")
            if (excl >= 1 and len(active) >= 2) or excl >= 2:
                ops_involved = sorted(u["op"] for u in active)
                violations.append(
                    f"resource {rid}: exclusive overlap at t={t}us "
                    f"({', '.join(ops_involved)})")
        if peak != res.get("peak_usage"):
            defects.append(f"resource {rid}: claimed peak {res.get('peak_usage')} "
                           f"!= recomputed {peak}")


def _check_use_declarations(cert: dict, defects: list[str]) -> None:
    """Per-op declared uses and per-resource intervals must be the same multiset."""
    def key(rid: str, u: dict) -> tuple:
        return (u.get("op") or u.get("_op"), rid, u["mode"], u["amount"],
                u["start_us"], u["end_us"])

    from_resources: Counter = Counter()
    for res in cert.get("resources", []):
        for u in res.get("intervals", []):
            from_resources[key(res["id"], u)] += 1
    from_ops: Counter = Counter()
    for op in cert.get("ops", []):
        for u in op.get("uses", []):
            from_ops[(op["id"], u["resource"], u["mode"], u["amount"],
                      u["start_us"], u["end_us"])] += 1
    if from_resources != from_ops:
        diff = (from_resources - from_ops) + (from_ops - from_resources)
        sample = list(diff)[:3]
        defects.append(f"op use declarations and resource intervals disagree on "
                       f"{sum(diff.values())} entries, e.g. {sample}")


def _check_tokens(cert: dict, defects: list[str], violations: list[str]) -> None:
    buffer_cap = cert.get("token_buffer_capacity", {})
    produced: dict[str, dict] = {}   # token id -> produce event
    consumed: set[str] = set()
    occupancy: dict[str, int] = defaultdict(int)
    peaks: dict[str, int] = defaultdict(int)
    prev_t = 0
    for ev in cert.get("token_events", []):
        t, typ, kind, tok = ev["t_us"], ev["type"], ev["kind"], ev["id"]
        if t < prev_t:
            defects.append(f"token events not in chronological order at t={t}us")
        prev_t = t
        if typ == "produce":
            if tok in produced:
                defects.append(f"token {tok!r} produced twice")
            produced[tok] = ev
            occupancy[kind] += 1
            peaks[kind] = max(peaks[kind], occupancy[kind])
            cap = buffer_cap.get(kind)
            if cap is not None and occupancy[kind] > cap:
                violations.append(f"token buffer {kind}: occupancy "
                                  f"{occupancy[kind]} > capacity {cap} at t={t}us")
        elif typ == "consume":
            if tok not in produced:
                violations.append(f"token {tok!r} consumed at t={t}us before "
                                  f"any production")
                continue
            if tok in consumed:
                violations.append(f"token {tok!r} consumed twice (t={t}us)")
                continue
            src = produced[tok]
            if t < src["t_us"]:
                violations.append(f"token {tok!r} consumed at t={t}us before its "
                                  f"production at t={src['t_us']}us")
            expires = src.get("expires_at_us")
            if expires is not None and t >= expires:
                violations.append(f"token {tok!r} consumed at t={t}us after its "
                                  f"expiry at t={expires}us")
            consumed.add(tok)
            occupancy[kind] -= 1
        else:
            defects.append(f"unknown token event type {typ!r}")
    for kind, claimed in cert.get("token_peak_occupancy", {}).items():
        if peaks.get(kind, 0) != claimed:
            defects.append(f"token {kind}: claimed peak occupancy {claimed} "
                           f"!= recomputed {peaks.get(kind, 0)}")


def _check_token_declarations(cert: dict, defects: list[str],
                              job_productions: Counter) -> None:
    """Every declared consume/produce must appear in the token event order
    (only meaningful for pass certificates: a failed consume has no event).
    Declarations are SUMMED per (op, kind, time) before comparing -- one op
    may legally declare several same-kind productions at the same time.
    ``job_productions`` carries the result-token productions recomputed from
    the FIFO replay of the service batches; they count as declarations."""
    consume_events: Counter = Counter()
    produce_events: Counter = Counter()
    for ev in cert.get("token_events", []):
        if ev.get("op") is None:
            continue  # initial inventory
        k = (ev["op"], ev["kind"], ev["t_us"])
        if ev["type"] == "consume":
            consume_events[k] += 1
        else:
            produce_events[k] += 1
    declared_consumes: Counter = Counter()
    declared_produces: Counter = Counter(job_productions)
    for op in cert.get("ops", []):
        for c in op.get("consumes", []):
            if c.get("kind") is None:
                continue  # id-based consumes are covered by the ledger replay
            declared_consumes[(op["id"], c["kind"], c["t_us"])] += c["count"]
        for p in op.get("produces", []):
            declared_produces[(op["id"], p["kind"], p["t_us"])] += p["count"]
    for k, count in declared_consumes.items():
        if consume_events[k] < count:
            defects.append(
                f"op {k[0]} declares consuming {count} {k[1]} at t={k[2]}us "
                f"but only {consume_events[k]} consume event(s) exist")
    for k in set(declared_produces) | set(produce_events):
        if produce_events[k] != declared_produces[k]:
            defects.append(
                f"op {k[0]} declares producing {declared_produces[k]} {k[1]} at "
                f"t={k[2]}us but {produce_events[k]} produce event(s) exist")


def _check_services(cert: dict, defects: list[str], violations: list[str],
                    job_productions: Counter) -> None:
    """Replays the FIFO recurrence; also recomputes the (op, kind, t) result
    tokens completed jobs must have produced, into ``job_productions``."""
    for svc in cert.get("services", []):
        sid = svc["id"]
        workers = [0] * svc["workers"]
        heapq.heapify(workers)
        queue_deltas: list[tuple[int, int]] = []
        for batch in svc.get("batches", []):
            submit, count, pt = (batch["submit_time_us"], batch["count"],
                                 batch["processing_time_us"])
            result_token = batch.get("result_token")
            first_start = None
            last_complete = 0
            worst = 0
            misses = 0
            for _ in range(count):
                free = heapq.heappop(workers)
                start = submit if submit > free else free
                complete = start + pt
                heapq.heappush(workers, complete)
                if result_token is not None:
                    job_productions[(batch["op_id"], result_token, complete)] += 1
                if start > submit:
                    queue_deltas.append((submit, +1))
                    queue_deltas.append((start, -1))
                latency = complete - submit
                worst = max(worst, latency)
                if latency > svc["max_latency_us"]:
                    misses += 1
                first_start = start if first_start is None else min(first_start, start)
                last_complete = max(last_complete, complete)
            recomputed = {
                "first_start_us": first_start if first_start is not None else submit,
                "last_complete_us": last_complete,
                "max_latency_observed_us": worst,
                "deadline_misses": misses,
            }
            for field_name, value in recomputed.items():
                if batch.get(field_name) != value:
                    defects.append(f"service {sid} batch {batch['batch_id']}: claimed "
                                   f"{field_name}={batch.get(field_name)} != "
                                   f"recomputed {value}")
            if misses:
                violations.append(f"service {sid}: {misses} deadline miss(es) in "
                                  f"batch {batch['batch_id']}")
        queue_deltas.sort()
        level = 0
        max_queue = 0
        over = False
        for _t, d in queue_deltas:
            level += d
            max_queue = max(max_queue, level)
            if level > svc["queue_capacity"]:
                over = True
        if over:
            violations.append(f"service {sid}: queue length {max_queue} exceeds "
                              f"capacity {svc['queue_capacity']}")
        if max_queue != svc.get("max_queue_length"):
            defects.append(f"service {sid}: claimed max queue "
                           f"{svc.get('max_queue_length')} != recomputed {max_queue}")


def _check_service_declarations(cert: dict, defects: list[str]) -> None:
    """Declared job batches and simulated batches must be the same multiset
    (only meaningful for pass certificates)."""
    declared: Counter = Counter()
    for op in cert.get("ops", []):
        for j in op.get("service_jobs", []):
            declared[(op["id"], j["service"], j["submit_us"], j["count"],
                      j["processing_time_us"], j.get("result_token"))] += 1
    simulated: Counter = Counter()
    for svc in cert.get("services", []):
        for b in svc.get("batches", []):
            simulated[(b["op_id"], svc["id"], b["submit_time_us"], b["count"],
                       b["processing_time_us"], b.get("result_token"))] += 1
    if declared != simulated:
        diff = (declared - simulated) + (simulated - declared)
        defects.append(f"declared service jobs and simulated batches disagree on "
                       f"{sum(diff.values())} entries, e.g. {list(diff)[:3]}")


def check_certificate(cert: dict) -> tuple[bool, list[str], list[str]]:
    """Returns (valid, defects, violations).

    * ``defects``    -- the certificate is internally inconsistent or claims
      wrong numbers (always fatal);
    * ``violations`` -- finite-service constraint violations recomputed from
      the certificate data (fatal for a "pass" verdict; expected for "fail").
    """
    defects: list[str] = []
    violations: list[str] = []

    if not isinstance(cert, dict):
        return False, [f"certificate is not a JSON object (got "
                       f"{type(cert).__name__})"], []

    try:
        _check_structure(cert, defects)
        ops = _check_ops(cert, defects)
        _check_dependencies(ops, violations)
        _check_resources(cert, defects, violations)
        _check_tokens(cert, defects, violations)
        job_productions: Counter = Counter()
        _check_services(cert, defects, violations, job_productions)

        verdict = cert.get("verdict")
        claimed_errors = cert.get("errors", [])
        if verdict == "pass":
            # a pass certificate must also be *closed*: every declaration realized
            _check_use_declarations(cert, defects)
            _check_token_declarations(cert, defects, job_productions)
            _check_service_declarations(cert, defects)
            if claimed_errors:
                defects.append(f"verdict is 'pass' but {len(claimed_errors)} errors are claimed")
            valid = not defects and not violations
        elif verdict == "fail":
            if not claimed_errors:
                defects.append("verdict is 'fail' but no errors are claimed")
            valid = not defects
        else:
            defects.append(f"unknown verdict {verdict!r}")
            valid = False
    except (KeyError, IndexError, TypeError, AttributeError) as exc:
        # a truncated / hand-edited certificate (missing required keys, wrong
        # value types) is INVALID, not a crash.
        defects.append(f"malformed certificate ({type(exc).__name__}: {exc})")
        valid = False
    return valid, defects, violations


def main(path: str) -> int:
    try:
        cert = _load_cert(path)
    except CertLoadError as exc:
        print(f"error: {exc}")
        return 2  # could not load the inputs
    valid, defects, violations = check_certificate(cert)
    meta = cert if isinstance(cert, dict) else {}
    verdict = meta.get("verdict")
    print(f"certificate: {path}")
    print(f"verdict claimed: {verdict}; backend={meta.get('backend_name')!r} "
          f"program={meta.get('program_name')!r}")
    for d in defects:
        print(f"  DEFECT: {d}")
    for v in violations[:20]:
        print(f"  violation recomputed: {v}")
    if len(violations) > 20:
        print(f"  ... and {len(violations) - 20} more violations")
    if valid and verdict == "pass":
        print("OK: independently re-verified -- the schedule satisfies all "
              "finite-service constraints in the certificate.")
    elif valid:
        print(f"OK: consistent FAIL certificate ({len(meta.get('errors', []))} "
              f"claimed error(s), {len(violations)} recomputed violation(s)).")
    else:
        print("INVALID certificate.")
    return 0 if valid else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1]))
