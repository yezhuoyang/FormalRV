"""Tests for the strict explicit-qubit discipline.

Zones expand to explicit capacity-1 resources; every qubit-touching op must
name exact qubits (QubitExplicitnessViolation otherwise); factories must
declare fixed footprints; the certificate stays closed under all of it.
"""

from __future__ import annotations

import pytest

from ftq_vm.backend.check_certificate import check_certificate
from ftq_vm.backend.loader import LoadError, backend_from_obj, program_from_obj
from ftq_vm.backend.models import (
    BackendConfig,
    FactoryFootprint,
    FactorySpec,
    Op,
    Program,
    ResourceSpec,
    ResourceUse,
    UseMode,
    VMErrorKind,
    ZoneSpec,
    parse_qubit_ref,
)
from ftq_vm.backend.simulator import run_simulation


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------


BACKEND_DOC = {
    "unit": {"time": "us"},
    "name": "zb",
    "zones": {
        "data": {"kind": "data_qubit", "count": 8},
        "syndrome": {"kind": "syndrome_qubit", "count": 4},
        "fab": {"kind": "factory_qubit", "count": 6},
    },
    "resources": {
        "bus": {"kind": "bus", "capacity": 2},
        "decoder": {"kind": "service", "workers": 2, "max_latency_us": 100,
                    "queue_capacity": 10},
    },
    "qubit_touching_kinds": ["syndrome_extract", "magic_inject"],
    "factories": {
        "F0": {"produces": "T", "duration_us": 5,
               "footprint": {"qubits": ["fab[0:4]"]}},
    },
}


def load_backend_doc(**overrides):
    import copy
    doc = copy.deepcopy(BACKEND_DOC)
    doc.update(overrides)
    return backend_from_obj(doc)


def run(backend, ops):
    return run_simulation(backend, Program(name="p", ops=list(ops)))


# --------------------------------------------------------------------------
# Qubit reference parser
# --------------------------------------------------------------------------


def test_parse_qubit_ref_forms():
    assert parse_qubit_ref("data[3]") == ("data", [3])
    assert parse_qubit_ref("data[0:5]") == ("data", [0, 1, 2, 3, 4])  # half-open
    assert parse_qubit_ref("data[0,2,5]") == ("data", [0, 2, 5])
    assert parse_qubit_ref("data[1:3,7]") == ("data", [1, 2, 7])
    assert parse_qubit_ref("data") is None
    assert parse_qubit_ref("data[]") is None
    assert parse_qubit_ref("data[5:5]") is None  # empty range
    assert parse_qubit_ref("data[b]") is None


# --------------------------------------------------------------------------
# Zone expansion + explicit exclusivity at runtime
# --------------------------------------------------------------------------


def test_zones_expand_to_capacity1_resources():
    backend = load_backend_doc()
    result = run(backend, [])
    for i in range(8):
        assert result.resource_capacities[f"data[{i}]"] == 1
    assert result.certificate["zones"] == [
        {"id": "data", "kind": "data_qubit", "count": 8},
        {"id": "syndrome", "kind": "syndrome_qubit", "count": 4},
        {"id": "fab", "kind": "factory_qubit", "count": 6},
    ]


def test_same_syndrome_qubit_overlap_conflicts():
    backend = load_backend_doc()
    program = program_from_obj({
        "program": "p",
        "ops": [
            {"id": "ez", "do": "syndrome_extract", "at_us": 0, "duration_us": 4,
             "qubits": {"data": ["data[3]", "data[4]"], "syndrome": ["syndrome[1]"]}},
            {"id": "ex", "do": "syndrome_extract", "at_us": 2, "duration_us": 4,
             "qubits": {"data": ["data[5]"], "syndrome": ["syndrome[1]"]}},
        ],
    }, backend)
    result = run_simulation(backend, program)
    conflicts = [e for e in result.errors if e.kind == VMErrorKind.ResourceConflict]
    assert len(conflicts) == 1
    assert conflicts[0].resource == "syndrome[1]"
    assert set(conflicts[0].op_ids) == {"ez", "ex"}
    # role mapping is preserved for inspection
    assert program.ops[0].metadata["qubit_roles"] == {
        "data": ["data[3]", "data[4]"], "syndrome": ["syndrome[1]"]}


def test_disjoint_qubits_do_not_conflict():
    backend = load_backend_doc()
    program = program_from_obj({
        "program": "p",
        "ops": [
            {"id": "a", "do": "syndrome_extract", "at_us": 0, "duration_us": 4,
             "qubits": ["data[0:2]", "syndrome[0]"]},
            {"id": "b", "do": "syndrome_extract", "at_us": 0, "duration_us": 4,
             "qubits": ["data[2:4]", "syndrome[1]"]},
        ],
    }, backend)
    assert run_simulation(backend, program).ok


# --------------------------------------------------------------------------
# QubitExplicitnessViolation at load time
# --------------------------------------------------------------------------


def test_fungible_zone_request_rejected_at_load():
    backend = load_backend_doc()
    with pytest.raises(LoadError, match="QubitExplicitnessViolation"):
        program_from_obj({
            "program": "p",
            "ops": [{"id": "e", "do": "syndrome_extract", "at_us": 0,
                     "duration_us": 4, "uses": {"syndrome": 1}}],
        }, backend)


def test_qubit_touching_kind_without_qubits_rejected_at_load():
    backend = load_backend_doc()
    with pytest.raises(LoadError, match="does not list explicit qubit IDs"):
        program_from_obj({
            "program": "p",
            "ops": [{"id": "e", "do": "magic_inject", "at_us": 0,
                     "duration_us": 2, "uses": {"bus": 1}}],
        }, backend)


def test_qubit_pool_resource_rejected_at_backend_load():
    doc = {"unit": {"time": "us"},
           "resources": {"anc_pool": {"kind": "syndrome_ancilla", "capacity": 100}}}
    with pytest.raises(LoadError, match="QubitExplicitnessViolation"):
        backend_from_obj(doc)


def test_factory_without_footprint_rejected_at_load():
    import copy
    doc = copy.deepcopy(BACKEND_DOC)
    doc["factories"]["F0"] = {"produces": "T", "duration_us": 5,
                              "physical_qubits": 20000}
    with pytest.raises(LoadError, match="explicit fixed footprint"):
        backend_from_obj(doc)


def test_out_of_range_qubit_index_rejected_at_load():
    backend = load_backend_doc()
    with pytest.raises(LoadError, match="out of range"):
        program_from_obj({
            "program": "p",
            "ops": [{"id": "e", "do": "syndrome_extract", "at_us": 0,
                     "duration_us": 4, "qubits": ["syndrome[9]"]}],
        }, backend)


def test_duplicate_qubit_listed_twice_rejected_at_load():
    backend = load_backend_doc()
    with pytest.raises(LoadError, match="listed twice"):
        program_from_obj({
            "program": "p",
            "ops": [{"id": "e", "do": "syndrome_extract", "at_us": 0,
                     "duration_us": 4, "qubits": ["data[1]", "data[0:2]"]}],
        }, backend)


# --------------------------------------------------------------------------
# Runtime-side enforcement for directly-built models
# --------------------------------------------------------------------------


def test_bare_zone_use_flagged_at_runtime():
    backend = BackendConfig(zones=[ZoneSpec(id="anc", count=4)])
    op = Op(id="x", at_us=0, duration_us=2,
            uses=[ResourceUse(resource="anc")])
    result = run(backend, [op])
    kinds = [e.kind for e in result.errors]
    assert VMErrorKind.QubitExplicitnessViolation in kinds


def test_qubit_pool_use_flagged_at_runtime():
    backend = BackendConfig(
        resources=[ResourceSpec(id="pool", kind="physical_qubit", capacity=50)])
    op = Op(id="x", at_us=0, duration_us=2,
            uses=[ResourceUse(resource="pool", amount=3)])
    result = run(backend, [op])
    kinds = [e.kind for e in result.errors]
    assert VMErrorKind.QubitExplicitnessViolation in kinds


def test_qubit_touching_kind_flagged_at_runtime():
    backend = BackendConfig(zones=[ZoneSpec(id="anc", count=4)],
                            qubit_touching_kinds=["magic_inject"])
    op = Op(id="x", kind="magic_inject", at_us=0, duration_us=2)
    result = run(backend, [op])
    kinds = [e.kind for e in result.errors]
    assert VMErrorKind.QubitExplicitnessViolation in kinds


# --------------------------------------------------------------------------
# Factory footprints
# --------------------------------------------------------------------------


def test_factory_reserves_exact_footprint_and_collision_caught():
    backend = load_backend_doc()
    program = program_from_obj({
        "program": "p",
        "ops": [
            {"id": "go", "do": "start_factory", "factory": "F0", "at_us": 0},
            # touches fab[2] while the factory run [0, 5) holds it
            {"id": "probe", "do": "calibrate", "at_us": 2, "duration_us": 1,
             "qubits": ["fab[2]"]},
        ],
    }, backend)
    result = run_simulation(backend, program)
    conflicts = [e for e in result.errors if e.kind == VMErrorKind.ResourceConflict]
    assert len(conflicts) == 1
    assert conflicts[0].resource == "fab[2]"
    assert set(conflicts[0].op_ids) == {"F0.run0", "probe"}
    # qubits outside the footprint stay free
    assert result.resource_usage_series["fab[4]"] == [(0, 0)]


def test_certificate_closed_under_footprints_and_tamper_detected():
    backend = load_backend_doc()
    program = program_from_obj({
        "program": "p",
        "ops": [
            {"id": "go", "do": "start_factory", "factory": "F0", "at_us": 0},
            {"id": "inj", "do": "magic_inject", "at_us": 5, "duration_us": 2,
             "qubits": ["data[0]"], "consume": "T"},
        ],
    }, backend)
    result = run_simulation(backend, program)
    assert result.ok
    valid, defects, violations = check_certificate(result.certificate)
    assert valid and not defects and not violations

    # tampering: silently drop one footprint qubit's reservation interval
    import copy
    cert = copy.deepcopy(result.certificate)
    for res in cert["resources"]:
        if res["id"] == "fab[1]":
            assert res["intervals"], "footprint qubit must have an interval"
            res["intervals"] = []
    valid2, defects2, _ = check_certificate(cert)
    assert not valid2
    assert any("disagree" in d for d in defects2)
