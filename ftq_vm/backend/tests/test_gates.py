"""Tests for the hardware gate table and finite gate-level parallelism.

Gate times are hardware facts (the schedule cannot claim otherwise); gates
must name exactly their arity in explicit qubits; per-kind and global
parallelism caps lower to capacity uses and surface as CapacityExceeded.
"""

from __future__ import annotations

import pytest

from ftq_vm.backend.check_certificate import check_certificate
from ftq_vm.backend.loader import LoadError, backend_from_obj, program_from_obj
from ftq_vm.backend.models import (
    GLOBAL_GATE_CHANNELS,
    BackendConfig,
    GateSpec,
    Op,
    Program,
    ResourceSpec,
    ResourceUse,
    UseMode,
    VMErrorKind,
    ZoneSpec,
)
from ftq_vm.backend.simulator import run_simulation


BACKEND_DOC = {
    "unit": {"time": "us"},
    "name": "gb",
    "zones": {"q": {"kind": "data_qubit", "count": 8}},
    "resources": {"readout_lines": {"kind": "control_line", "capacity": 2}},
    "gates": {
        "H": {"duration_us": 100, "qubits": 1},
        "CNOT": {"duration_us": 1000, "qubits": 2, "max_parallel": 2},
        "measure": {"duration_us": 5000, "qubits": 1,
                    "uses": {"readout_lines": 1}},
    },
    "max_parallel_gates": 4,
}


def load_backend_doc():
    import copy
    return backend_from_obj(copy.deepcopy(BACKEND_DOC))


def run(backend, ops):
    return run_simulation(backend, Program(name="p", ops=list(ops)))


def errors_of(result, kind):
    return [e for e in result.errors if e.kind == kind]


# --------------------------------------------------------------------------
# Hardware durations are honest
# --------------------------------------------------------------------------


def test_gate_duration_filled_from_table_and_runtime_honest():
    backend = load_backend_doc()
    program = program_from_obj({"ops": [
        {"id": "h", "do": "H", "at_us": 0, "qubits": ["q[0]"]},
        {"id": "cx", "do": "CNOT", "at_us": 100, "qubits": ["q[0]", "q[1]"],
         "deps": ["h"]},
        {"id": "m", "do": "measure", "at_us": 1100, "qubits": ["q[0]"],
         "deps": ["cx"]},
    ]}, backend)
    assert [op.duration_us for op in program.ops] == [100, 1000, 5000]
    result = run_simulation(backend, program)
    assert result.ok
    assert result.stats.total_runtime_us == 1100 + 5000


def test_explicit_equal_duration_accepted():
    backend = load_backend_doc()
    program = program_from_obj({"ops": [
        {"id": "h", "do": "H", "at_us": 0, "duration_us": 100,
         "qubits": ["q[0]"]}]}, backend)
    assert run_simulation(backend, program).ok


def test_lying_about_duration_rejected_at_load():
    backend = load_backend_doc()
    with pytest.raises(LoadError, match="contradicts the hardware gate table"):
        program_from_obj({"ops": [
            {"id": "cx", "do": "CNOT", "at_us": 0, "duration_us": 5,
             "qubits": ["q[0]", "q[1]"]}]}, backend)


def test_lying_about_duration_caught_at_runtime_for_direct_models():
    backend = BackendConfig(
        zones=[ZoneSpec(id="q", count=4)],
        gates=[GateSpec(kind="CNOT", duration_us=1000, qubits=2)])
    op = Op(id="cx", kind="CNOT", at_us=0, duration_us=5, uses=[
        ResourceUse(resource="q[0]", mode=UseMode.exclusive),
        ResourceUse(resource="q[1]", mode=UseMode.exclusive)])
    result = run(backend, [op])
    errs = errors_of(result, VMErrorKind.InvalidInterval)
    assert len(errs) == 1
    assert "1000us" in errs[0].message


# --------------------------------------------------------------------------
# Exact arity in explicit qubits
# --------------------------------------------------------------------------


def test_gate_with_wrong_qubit_count_is_caught():
    backend = BackendConfig(
        zones=[ZoneSpec(id="q", count=4)],
        gates=[GateSpec(kind="CNOT", duration_us=1000, qubits=2)])
    op = Op(id="cx", kind="CNOT", at_us=0, duration_us=1000, uses=[
        ResourceUse(resource="q[0]", mode=UseMode.exclusive)])
    result = run(backend, [op])
    errs = errors_of(result, VMErrorKind.QubitExplicitnessViolation)
    assert any("exactly 2" in e.message for e in errs)


def test_gate_without_qubits_rejected_at_load():
    backend = load_backend_doc()  # gate kinds auto-join qubit_touching_kinds
    with pytest.raises(LoadError, match="explicit qubit IDs"):
        program_from_obj({"ops": [
            {"id": "h", "do": "H", "at_us": 0}]}, backend)


# --------------------------------------------------------------------------
# Parallelism caps
# --------------------------------------------------------------------------


def test_global_gate_cap_exceeded():
    backend = load_backend_doc()
    program = program_from_obj({"ops": [
        {"id": f"h{i}", "do": "H", "at_us": 0, "qubits": [f"q[{i}]"]}
        for i in range(6)]}, backend)
    result = run_simulation(backend, program)
    errs = errors_of(result, VMErrorKind.CapacityExceeded)
    assert len(errs) == 1
    assert errs[0].resource == GLOBAL_GATE_CHANNELS
    assert "demand 6 exceeds capacity 4" in errs[0].message


def test_per_kind_cap_exceeded():
    backend = load_backend_doc()
    program = program_from_obj({"ops": [
        {"id": f"cx{i}", "do": "CNOT", "at_us": 0,
         "qubits": [f"q[{2*i}]", f"q[{2*i+1}]"]}
        for i in range(3)]}, backend)
    result = run_simulation(backend, program)
    by_resource = {e.resource for e in errors_of(result, VMErrorKind.CapacityExceeded)}
    assert f"gate.CNOT.parallel" in by_resource
    assert GLOBAL_GATE_CHANNELS not in by_resource  # 3 <= 4


def test_gate_control_uses_charged():
    backend = load_backend_doc()
    program = program_from_obj({"ops": [
        {"id": f"m{i}", "do": "measure", "at_us": 0, "qubits": [f"q[{i}]"]}
        for i in range(3)]}, backend)
    result = run_simulation(backend, program)
    by_resource = {e.resource for e in errors_of(result, VMErrorKind.CapacityExceeded)}
    assert "readout_lines" in by_resource


def test_no_caps_means_unconstrained():
    backend = BackendConfig(
        zones=[ZoneSpec(id="q", count=8)],
        gates=[GateSpec(kind="H", duration_us=100, qubits=1)])
    ops = [Op(id=f"h{i}", kind="H", at_us=0, duration_us=100, uses=[
        ResourceUse(resource=f"q[{i}]", mode=UseMode.exclusive)])
        for i in range(8)]
    assert run(backend, ops).ok


def test_staying_within_caps_passes_with_honest_serialization():
    backend = load_backend_doc()
    program = program_from_obj({"ops": [
        {"id": "m0", "do": "measure", "at_us": 0, "qubits": ["q[0]"]},
        {"id": "m1", "do": "measure", "at_us": 0, "qubits": ["q[1]"]},
        {"id": "m2", "do": "measure", "at_us": 5000, "qubits": ["q[2]"]},
    ]}, backend)
    result = run_simulation(backend, program)
    assert result.ok
    assert result.stats.total_runtime_us == 10000  # serialization is visible


# --------------------------------------------------------------------------
# Certificate closure + reserved ids
# --------------------------------------------------------------------------


def test_gate_program_certificate_closure():
    backend = load_backend_doc()
    program = program_from_obj({"ops": [
        {"id": "h", "do": "H", "at_us": 0, "qubits": ["q[0]"]},
        {"id": "m", "do": "measure", "at_us": 100, "qubits": ["q[0]"],
         "deps": ["h"]},
    ]}, backend)
    result = run_simulation(backend, program)
    assert result.ok
    valid, defects, violations = check_certificate(result.certificate)
    assert valid and not defects and not violations
    cert_resources = {r["id"] for r in result.certificate["resources"]}
    assert GLOBAL_GATE_CHANNELS in cert_resources  # caps visible to Lean too


def test_reserved_gate_resource_id_rejected():
    with pytest.raises(ValueError, match="reserved"):
        BackendConfig(
            resources=[ResourceSpec(id=GLOBAL_GATE_CHANNELS, kind="x", capacity=1)],
            gates=[GateSpec(kind="H", duration_us=100)],
            max_parallel_gates=4)
