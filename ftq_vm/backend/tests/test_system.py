"""Tests for the system-level pieces: syndrome-bus backlog via services,
result-token chaining (jobs produce tokens at computed completion times),
and the qubit reset/reuse discipline.  Also regression tests for the
zone-layer review fixes (footprint dedup, huge-range guard, exclusivity
enforcement on zone refs).
"""

from __future__ import annotations

import pytest

from ftq_vm.backend.loader import LoadError, backend_from_obj, program_from_obj
from ftq_vm.backend.models import (
    BackendConfig,
    Op,
    Program,
    ResourceUse,
    ServiceJobRequest,
    ServiceSpec,
    UseMode,
    VMErrorKind,
    ZoneSpec,
    parse_qubit_ref,
)
from ftq_vm.backend.simulator import run_simulation


def run(backend, ops):
    return run_simulation(backend, Program(name="p", ops=list(ops)))


def errors_of(result, kind):
    return [e for e in result.errors if e.kind == kind]


# --------------------------------------------------------------------------
# Result-token chaining: bus -> buffer -> decoder pipelines
# --------------------------------------------------------------------------


BUS = ServiceSpec(id="bus", workers=1, max_latency_us=100, queue_capacity=50)


def test_result_token_produced_at_computed_completion():
    # one lane, 4us per packet: completions at 4, 8, 12
    backend = BackendConfig(services=[BUS])
    submit = Op(id="m", at_us=0, duration_us=1, service=[
        ServiceJobRequest(service="bus", count=3, processing_time_us=4,
                          result_token="Packet")])
    result = run(backend, [submit])
    assert result.ok
    times = sorted(t.produced_at_us for t in result.tokens)
    assert times == [4, 8, 12]
    assert all(t.kind == "Packet" for t in result.tokens)
    assert all(t.producer_op == "m" for t in result.tokens)


def test_consuming_result_token_before_completion_is_caught():
    backend = BackendConfig(services=[BUS])
    submit = Op(id="m", at_us=0, duration_us=1, service=[
        ServiceJobRequest(service="bus", count=1, processing_time_us=4,
                          result_token="Packet")])
    eager = Op(id="eager", at_us=2, duration_us=1,
               consumes=[{"kind": "Packet"}])
    result = run(backend, [submit, eager])
    errs = errors_of(result, VMErrorKind.TokenUnavailable)
    assert len(errs) == 1
    assert "produced at t=4us" in errs[0].suggestion or "4us" in errs[0].suggestion


def test_consuming_result_token_at_completion_passes():
    backend = BackendConfig(services=[BUS])
    submit = Op(id="m", at_us=0, duration_us=1, service=[
        ServiceJobRequest(service="bus", count=1, processing_time_us=4,
                          result_token="Packet")])
    patient = Op(id="patient", at_us=4, duration_us=1,
                 consumes=[{"kind": "Packet"}])
    assert run(backend, [submit, patient]).ok


def test_bus_backlog_queue_overflow_and_deadline():
    """8 packets per round into a 1-lane 4us/packet bus with a 6-slot buffer."""
    bus = ServiceSpec(id="bus", workers=1, max_latency_us=10, queue_capacity=6)
    backend = BackendConfig(services=[bus])
    submit = Op(id="m", at_us=0, duration_us=1, service=[
        ServiceJobRequest(service="bus", count=8, processing_time_us=4,
                          result_token="Packet")])
    result = run(backend, [submit])
    assert errors_of(result, VMErrorKind.ServiceQueueOverflow)
    assert errors_of(result, VMErrorKind.DeadlineMiss)


# --------------------------------------------------------------------------
# Qubit reset / reuse discipline
# --------------------------------------------------------------------------


def reset_backend(**zone_overrides):
    zone = dict(id="anc", kind="helper_qubit", count=2, reset_required=True,
                reset_kinds=["reset"], min_reset_us=3)
    zone.update(zone_overrides)
    return BackendConfig(zones=[ZoneSpec(**zone)])


def helper(op_id, at, dur=5, qubit="anc[0]", kind="helper_op"):
    return Op(id=op_id, kind=kind, at_us=at, duration_us=dur,
              uses=[ResourceUse(resource=qubit, mode=UseMode.exclusive)])


def test_reuse_without_reset_is_caught():
    result = run(reset_backend(), [helper("a", 0), helper("b", 10)])
    errs = errors_of(result, VMErrorKind.QubitReuseViolation)
    assert len(errs) == 1
    assert errs[0].resource == "anc[0]"
    assert errs[0].op_ids == ["a", "b"]


def test_reuse_with_sufficient_reset_passes():
    ops = [helper("a", 0),
           helper("r", 6, dur=3, kind="reset"),
           helper("b", 10)]
    assert run(reset_backend(), ops).ok


def test_too_short_reset_is_caught():
    ops = [helper("a", 0),
           helper("r", 6, dur=2, kind="reset"),   # < min_reset_us = 3
           helper("b", 10)]
    result = run(reset_backend(), ops)
    errs = errors_of(result, VMErrorKind.QubitReuseViolation)
    assert len(errs) == 1
    assert "at least 3us" in errs[0].message


def test_same_op_repeated_use_is_not_reuse():
    op = Op(id="a", kind="helper_op", at_us=0, duration_us=10, uses=[
        ResourceUse(resource="anc[0]", mode=UseMode.exclusive, start_us=0, end_us=3),
        ResourceUse(resource="anc[0]", mode=UseMode.exclusive, start_us=5, end_us=8),
    ])
    assert run(reset_backend(), [op]).ok


def test_zone_without_reset_required_allows_immediate_reuse():
    backend = BackendConfig(zones=[ZoneSpec(id="anc", count=2)])
    assert run(backend, [helper("a", 0), helper("b", 10)]).ok


def test_dirty_kinds_lifecycle_gate_then_measure():
    """With dirty_kinds=['measure'], gates on a live qubit are fine; only a
    measurement forces the next user through a reset (the Lean AncillaModel
    lifecycle, confirmed by the System/ cross-validation audit)."""
    backend = BackendConfig(zones=[ZoneSpec(
        id="anc", count=2, reset_required=True, reset_kinds=["reset"],
        dirty_kinds=["measure"], min_reset_us=2)])
    block = [helper("g1", 0, dur=2, kind="gate2q"),
             helper("g2", 3, dur=2, kind="gate2q"),     # gate after gate: live, fine
             helper("m1", 6, dur=2, kind="measure")]    # dirties anc[0]
    # reuse after the measurement without reset -> violation
    bad = run(backend, [*block, helper("g3", 10, dur=2, kind="gate2q")])
    errs = errors_of(bad, VMErrorKind.QubitReuseViolation)
    assert len(errs) == 1 and errs[0].op_ids == ["m1", "g3"]
    # same reuse after an explicit reset -> clean
    good = run(backend, [*block, helper("r", 9, dur=2, kind="reset"),
                         helper("g3", 12, dur=2, kind="gate2q")])
    assert good.ok


# --------------------------------------------------------------------------
# Review-fix regressions
# --------------------------------------------------------------------------


def test_footprint_overlap_between_groups_is_deduped():
    doc = {
        "unit": {"time": "us"},
        "zones": {"fab": {"kind": "factory_qubit", "count": 4}},
        "factories": {"F0": {"produces": "T", "duration_us": 5,
                             "footprint": {"qubits": ["fab[0:4]"],
                                           "buffer": ["fab[2]"]}}},
    }
    backend = backend_from_obj(doc)
    program = program_from_obj(
        {"ops": [{"id": "go", "do": "start_factory", "factory": "F0", "at_us": 0}]},
        backend)
    assert run_simulation(backend, program).ok


def test_huge_range_rejected_without_materializing():
    assert parse_qubit_ref("data[0:999999999]") is None


def test_non_exclusive_zone_ref_rejected_at_load_and_runtime():
    backend = backend_from_obj({
        "unit": {"time": "us"},
        "zones": {"anc": {"kind": "helper_qubit", "count": 2}},
    })
    with pytest.raises(LoadError, match="exclusively"):
        program_from_obj({"ops": [
            {"id": "a", "do": "x", "at_us": 0, "duration_us": 5,
             "uses": [{"resource": "anc[0]", "mode": "shared"}]}]}, backend)
    result = run(backend, [Op(id="a", at_us=0, duration_us=5, uses=[
        ResourceUse(resource="anc[0]", mode=UseMode.shared)])])
    assert errors_of(result, VMErrorKind.QubitExplicitnessViolation)


def test_backend_none_zone_ref_lowers_to_exclusive():
    program = program_from_obj({"ops": [
        {"id": "a", "do": "x", "at_us": 0, "duration_us": 5,
         "uses": {"anc[0]": 1}}]}, None)
    assert program.ops[0].uses[0].mode == UseMode.exclusive


def test_result_token_certificate_closure_and_tamper():
    from ftq_vm.backend.check_certificate import check_certificate
    backend = BackendConfig(services=[BUS])
    program = Program(ops=[
        Op(id="m", at_us=0, duration_us=1, service=[
            ServiceJobRequest(service="bus", count=2, processing_time_us=4,
                              result_token="Packet")]),
        Op(id="c", at_us=8, duration_us=1, consumes=[{"kind": "Packet"}]),
    ])
    res = run_simulation(backend, program)
    assert res.ok
    valid, defects, violations = check_certificate(res.certificate)
    assert valid and not defects and not violations

    # tamper: claim a packet arrived before its FIFO completion time
    import copy
    cert = copy.deepcopy(res.certificate)
    for ev in cert["token_events"]:
        if ev["type"] == "produce" and ev["t_us"] == 8:
            ev["t_us"] = 5
    cert["token_events"].sort(key=lambda e: e["t_us"])
    valid2, defects2, _ = check_certificate(cert)
    assert not valid2 and defects2


# --------------------------------------------------------------------------
# End-to-end: the system demo
# --------------------------------------------------------------------------


def test_demo_system_bugs_outcomes():
    from pathlib import Path
    from ftq_vm.backend.loader import load_backend, load_program
    ex = Path(__file__).parent.parent / "examples"
    backend = load_backend(ex / "demo_system_backend.yaml")
    program = load_program(ex / "demo_system_bugs.yaml", backend)
    result = run_simulation(backend, program)
    kinds = result.stats.errors_by_kind
    assert kinds.get("ServiceQueueOverflow", 0) >= 1
    assert kinds.get("DeadlineMiss", 0) >= 1
    assert kinds.get("TokenUnavailable") == 1
    assert kinds.get("QubitReuseViolation") == 2
    assert set(kinds) == {"ServiceQueueOverflow", "DeadlineMiss",
                          "TokenUnavailable", "QubitReuseViolation"}
