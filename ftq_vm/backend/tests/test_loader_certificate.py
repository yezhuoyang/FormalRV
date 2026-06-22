"""Tests for the friendly loader syntax and the certificate / checker pair.

Loader: friendly backend mapping syntax (service / token_buffer / plain
resource discrimination, tokens section), unit and bare-time-key rejection,
repeat expansion, uses-mapping service sugar, metadata spill, do/kind and
auto ids, missing at_us.

Certificate: a passing run independently re-verifies; tampering (capacity,
token events, batch counts, verdict) is detected; failing runs give a
consistent FAIL certificate; hashes are stable 64-hex; version 2.
"""

from __future__ import annotations

import copy
import re

import pytest

from ftq_vm.backend.check_certificate import check_certificate
from ftq_vm.backend.loader import LoadError, backend_from_obj, program_from_obj
from ftq_vm.backend.models import RunConfig, ServiceJobRequest, UseMode
from ftq_vm.backend.simulator import run_simulation


# --------------------------------------------------------------------------
# Helpers: tiny backend / program in the friendly on-disk syntax
# --------------------------------------------------------------------------


def tiny_backend_obj() -> dict:
    return {
        "name": "tiny",
        "unit": {"time": "us"},
        "resources": {
            "zone": {"kind": "storage_zone", "capacity": 4},
            "decoder": {"kind": "service", "workers": 2, "max_latency_us": 100,
                        "queue_capacity": 10, "processing_time_us": 2},
            "t_buffer": {"kind": "token_buffer", "token_kind": "TState",
                         "capacity": 8},
        },
        "tokens": {"TState": {"initial_inventory": 1, "ttl_us": 1000}},
    }


def tiny_passing_program_obj() -> dict:
    return {
        "program": "tiny_prog",
        "ops": [
            {"id": "prep", "do": "magic_prep", "at_us": 0, "duration_us": 5,
             "produce": "TState", "uses": {"zone": 2}},
            {"id": "use", "do": "logical_T", "at_us": 10, "duration_us": 3,
             "deps": ["prep"], "consume": "TState",
             "uses": {"zone": 1, "decoder": 2}},
        ],
    }


def run_tiny_passing():
    backend = backend_from_obj(tiny_backend_obj())
    program = program_from_obj(tiny_passing_program_obj(), backend)
    return run_simulation(backend, program, RunConfig(seed=0))


def run_tiny_failing():
    """One op consumes a token kind that is never produced anywhere."""
    backend = backend_from_obj(tiny_backend_obj())
    program = program_from_obj({
        "program": "tiny_fail",
        "ops": [{"id": "bad", "do": "logical_T", "at_us": 0, "duration_us": 1,
                 "consume": "NeverMade"}],
    }, backend)
    return run_simulation(backend, program, RunConfig(seed=0))


# --------------------------------------------------------------------------
# Loader: friendly backend syntax
# --------------------------------------------------------------------------


def test_backend_friendly_mapping_syntax():
    b = backend_from_obj(tiny_backend_obj())

    # plain resource (kind neither service nor token_buffer) -> ResourceSpec
    assert [r.id for r in b.resources] == ["zone"]
    zone = b.resource_map()["zone"]
    assert zone.kind == "storage_zone" and zone.capacity == 4

    # kind: service -> ServiceSpec; processing_time_us -> default_latencies_us
    assert [s.id for s in b.services] == ["decoder"]
    decoder = b.service_map()["decoder"]
    assert decoder.workers == 2
    assert decoder.max_latency_us == 100
    assert decoder.queue_capacity == 10
    assert b.default_latencies_us == {"decoder": 2}

    # kind: token_buffer -> token_buffer_capacity[token_kind]
    assert b.token_buffer_capacity == {"TState": 8}

    # tokens section -> initial inventory + ttl
    assert b.token_initial_inventory == {"TState": 1}
    assert b.token_ttl_us == {"TState": 1000}


def test_unit_must_be_us():
    bad = dict(tiny_backend_obj(), unit={"time": "ms"})
    with pytest.raises(LoadError, match="unit"):
        backend_from_obj(bad)
    with pytest.raises(LoadError, match="unit"):
        program_from_obj({"unit": {"time": "ms"}, "ops": []})


def test_bare_time_key_in_op_rejected():
    with pytest.raises(LoadError, match="_us"):
        program_from_obj({"ops": [{"do": "x", "at_us": 0, "duration": 5}]})


def test_bare_time_key_in_backend_rejected():
    bad = dict(tiny_backend_obj())
    bad["tokens"] = {"TState": {"ttl": 1000}}
    with pytest.raises(LoadError, match="_us"):
        backend_from_obj(bad)


def test_repeat_expansion_ids_and_times():
    prog = program_from_obj({
        "ops": [{"id": "tick", "do": "pulse", "at_us": 50, "duration_us": 1,
                 "repeat": {"every_us": 100, "until_us": 260}}],
    })
    # instances at base + k*every while <= until: 50, 150, 250 (350 > 260)
    assert [op.id for op in prog.ops] == ["tick@0", "tick@1", "tick@2"]
    assert [op.at_us for op in prog.ops] == [50, 150, 250]
    assert all(op.kind == "pulse" for op in prog.ops)


def test_uses_mapping_service_name_becomes_job_request():
    backend = backend_from_obj(tiny_backend_obj())
    prog = program_from_obj({
        "ops": [{"id": "op0", "do": "x", "at_us": 0,
                 "uses": {"decoder": 3, "zone": 2}}],
    }, backend)
    op = prog.ops[0]
    # service name in the mapping form submits that many jobs ...
    assert op.service == [ServiceJobRequest(service="decoder", count=3)]
    # ... while non-service names are plain resource uses
    assert len(op.uses) == 1
    assert op.uses[0].resource == "zone"
    assert op.uses[0].amount == 2
    assert op.uses[0].mode == UseMode.capacity


def test_unknown_op_keys_land_in_metadata():
    prog = program_from_obj({
        "ops": [{"do": "logical_T", "at_us": 0, "qubit": "q17", "round": 3}],
    })
    assert prog.ops[0].metadata == {"qubit": "q17", "round": 3}


def test_do_kind_and_auto_ids():
    prog = program_from_obj({
        "ops": [
            {"do": "gate", "at_us": 0},
            {"do": "gate", "at_us": 1},
            {"kind": "meas", "at_us": 2},
            {"do": "alpha", "kind": "beta", "at_us": 3},  # 'do' wins
        ],
    })
    assert [op.id for op in prog.ops] == ["gate_0", "gate_1", "meas_0", "alpha_0"]
    assert [op.kind for op in prog.ops] == ["gate", "gate", "meas", "alpha"]


def test_missing_at_us_is_load_error():
    with pytest.raises(LoadError, match="at_us"):
        program_from_obj({"ops": [{"do": "x", "duration_us": 1}]})


# --------------------------------------------------------------------------
# Certificate: independent re-verification
# --------------------------------------------------------------------------


def test_passing_run_certificate_is_valid():
    result = run_tiny_passing()
    assert result.ok
    cert = result.certificate
    assert cert["verdict"] == "pass"
    valid, defects, violations = check_certificate(cert)
    assert valid, f"defects={defects}, violations={violations}"
    assert defects == []
    assert violations == []


def test_certificate_version_and_stable_hashes():
    cert1 = run_tiny_passing().certificate
    cert2 = run_tiny_passing().certificate
    assert cert1["format"] == "ftqvm-certificate"
    assert cert1["version"] == 2
    for key in ("backend_hash", "program_hash"):
        assert re.fullmatch(r"[0-9a-f]{64}", cert1[key]), cert1[key]
        assert cert1[key] == cert2[key]
    # same seed -> identical run -> identical certificate
    assert cert1 == cert2


def test_tampered_capacity_is_detected():
    cert = copy.deepcopy(run_tiny_passing().certificate)
    zone = next(r for r in cert["resources"] if r["id"] == "zone")
    zone["capacity"] = 1  # 'prep' holds 2 of zone during [0, 5)
    valid, defects, violations = check_certificate(cert)
    assert not valid
    assert violations  # demand 2 > capacity 1 recomputed by the sweep
    assert any("zone" in v for v in violations)


def test_tampered_token_events_are_detected():
    cert = copy.deepcopy(run_tiny_passing().certificate)
    before = len(cert["token_events"])
    cert["token_events"] = [ev for ev in cert["token_events"]
                            if ev["type"] != "consume"]
    assert len(cert["token_events"]) == before - 1  # exactly one consume dropped
    valid, defects, violations = check_certificate(cert)
    # the pass certificate is no longer closed: op 'use' declares a consume
    # for which no event exists
    assert not valid
    assert any("consum" in d for d in defects)


def test_tampered_batch_count_is_detected():
    cert = copy.deepcopy(run_tiny_passing().certificate)
    decoder = next(s for s in cert["services"] if s["id"] == "decoder")
    assert decoder["batches"], "expected at least one batch on the decoder"
    decoder["batches"][0]["count"] += 1
    valid, defects, violations = check_certificate(cert)
    assert not valid
    assert defects  # recomputed batch fields / declarations disagree


def test_failing_run_yields_consistent_fail_certificate():
    result = run_tiny_failing()
    assert not result.ok
    cert = result.certificate
    assert cert["verdict"] == "fail"
    assert len(cert["errors"]) >= 1
    assert any(e["kind"] == "TokenUnavailable" for e in cert["errors"])
    valid, defects, violations = check_certificate(cert)
    # consistent FAIL: internally coherent and claiming >= 1 error
    assert valid, f"defects={defects}"
    assert defects == []


def test_fail_verdict_flipped_to_pass_is_invalid():
    cert = copy.deepcopy(run_tiny_failing().certificate)
    cert["verdict"] = "pass"
    valid, defects, violations = check_certificate(cert)
    assert not valid
    assert any("pass" in d and "error" in d for d in defects)
