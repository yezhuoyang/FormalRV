"""End-to-end tests over the bundled example YAML files.

Pairings (taken from the headers of the example files themselves):

* ``backend_simple.yaml``  + ``program_fixed.yaml`` / ``program_buggy.yaml``
* ``demo_backend.yaml``    + ``demo_factory_starvation.yaml`` /
  ``demo_buffer_overflow.yaml`` / ``demo_fixed.yaml``

All runs use the default ``RunConfig`` (seed 0, stochastic factories), for
which the expected outcomes are documented and stable.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from collections import Counter
from pathlib import Path

import pytest

from ftq_vm.backend.loader import load_backend, load_program
from ftq_vm.backend.models import VMErrorKind
from ftq_vm.backend.simulator import RunResult, run_simulation

EXAMPLES = Path(__file__).resolve().parent.parent / "examples"
REPO_ROOT = Path(__file__).resolve().parents[3]

EXAMPLE_NAMES = [
    "backend_simple.yaml",
    "demo_backend.yaml",
    "demo_buffer_overflow.yaml",
    "demo_factory_starvation.yaml",
    "demo_fixed.yaml",
    "program_buggy.yaml",
    "program_fixed.yaml",
]


# --------------------------------------------------------------------------
# Helpers / fixtures
# --------------------------------------------------------------------------


def run_example(backend_name: str, program_name: str) -> RunResult:
    """Load an example backend/program pair and simulate with defaults."""
    backend = load_backend(EXAMPLES / backend_name)
    program = load_program(EXAMPLES / program_name, backend)
    return run_simulation(backend, program)


def error_kind_counts(result: RunResult) -> Counter:
    return Counter(e.kind for e in result.errors)


def run_cli(*args: str) -> subprocess.CompletedProcess:
    """Run ``python -m ftq_vm <args>`` from the repo root with UTF-8 output."""
    env = {**os.environ, "PYTHONUTF8": "1"}
    return subprocess.run(
        [sys.executable, "-m", "ftq_vm", *args],
        cwd=str(REPO_ROOT), env=env,
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )


@pytest.fixture(scope="module")
def buggy_result() -> RunResult:
    return run_example("backend_simple.yaml", "program_buggy.yaml")


@pytest.fixture(scope="module")
def fixed_cli_run(tmp_path_factory: pytest.TempPathFactory):
    """CLI run of the passing example; yields (CompletedProcess, out_dir)."""
    out_dir = tmp_path_factory.mktemp("fixed_out")
    proc = run_cli("run", str(EXAMPLES / "backend_simple.yaml"),
                   str(EXAMPLES / "program_fixed.yaml"), "--out", str(out_dir))
    return proc, out_dir


@pytest.fixture(scope="module")
def buggy_cli_run(tmp_path_factory: pytest.TempPathFactory):
    """CLI run of the failing example; yields (CompletedProcess, out_dir)."""
    out_dir = tmp_path_factory.mktemp("buggy_out")
    proc = run_cli("run", str(EXAMPLES / "backend_simple.yaml"),
                   str(EXAMPLES / "program_buggy.yaml"), "--out", str(out_dir))
    return proc, out_dir


# --------------------------------------------------------------------------
# In-process simulation of the examples (seed 0 defaults)
# --------------------------------------------------------------------------


def test_program_fixed_passes():
    result = run_example("backend_simple.yaml", "program_fixed.yaml")
    assert result.ok is True
    assert result.errors == []
    assert result.stats.verdict == "pass"


def test_program_buggy_error_kinds_exact(buggy_result: RunResult):
    assert buggy_result.ok is False
    assert buggy_result.stats.verdict == "fail"
    assert error_kind_counts(buggy_result) == {
        VMErrorKind.TokenUnavailable: 19,
        VMErrorKind.ServiceQueueOverflow: 4,
        VMErrorKind.DeadlineMiss: 5,
        VMErrorKind.CapacityExceeded: 1,
    }


def test_program_buggy_queue_overflow_message(buggy_result: RunResult):
    queue_msgs = [e.message for e in buggy_result.errors
                  if e.kind is VMErrorKind.ServiceQueueOverflow]
    assert any("queue length 100001 exceeds capacity 100000" in m
               for m in queue_msgs)


def test_program_buggy_capacity_error_is_measurement_bus(buggy_result: RunResult):
    cap_errors = [e for e in buggy_result.errors
                  if e.kind is VMErrorKind.CapacityExceeded]
    assert len(cap_errors) == 1
    err = cap_errors[0]
    assert err.resource == "measurement_bus"
    assert "demand 65" in err.message


def test_demo_factory_starvation_only_token_unavailable():
    result = run_example("demo_backend.yaml", "demo_factory_starvation.yaml")
    assert result.ok is False
    kinds = set(error_kind_counts(result))
    assert kinds == {VMErrorKind.TokenUnavailable}


def test_demo_buffer_overflow_only_buffer_overflow():
    result = run_example("demo_backend.yaml", "demo_buffer_overflow.yaml")
    assert result.ok is False
    kinds = set(error_kind_counts(result))
    assert kinds == {VMErrorKind.TokenBufferOverflow}


def test_demo_fixed_passes():
    result = run_example("demo_backend.yaml", "demo_fixed.yaml")
    assert result.ok is True
    assert result.errors == []
    assert result.stats.verdict == "pass"


# --------------------------------------------------------------------------
# CLI subprocess tests
# --------------------------------------------------------------------------


def test_cli_run_fixed_exits_zero_and_writes_outputs(fixed_cli_run):
    proc, out_dir = fixed_cli_run
    assert proc.returncode == 0, proc.stdout + proc.stderr
    for name in ("trace.json", "stats.json", "certificate.json"):
        path = out_dir / name
        assert path.is_file(), f"{name} not written"
        json.loads(path.read_text(encoding="utf-8"))  # must parse
    trace = json.loads((out_dir / "trace.json").read_text(encoding="utf-8"))
    assert trace["ok"] is True
    assert trace["errors"] == []
    stats = json.loads((out_dir / "stats.json").read_text(encoding="utf-8"))
    assert stats["verdict"] == "pass"


def test_cli_run_buggy_exits_one_and_writes_outputs(buggy_cli_run):
    proc, out_dir = buggy_cli_run
    assert proc.returncode == 1, proc.stdout + proc.stderr
    for name in ("trace.json", "stats.json", "certificate.json"):
        path = out_dir / name
        assert path.is_file(), f"{name} not written"
        json.loads(path.read_text(encoding="utf-8"))  # must parse
    stats = json.loads((out_dir / "stats.json").read_text(encoding="utf-8"))
    assert stats["verdict"] == "fail"
    assert stats["errors_by_kind"] == {
        "TokenUnavailable": 19,
        "ServiceQueueOverflow": 4,
        "DeadlineMiss": 5,
        "CapacityExceeded": 1,
    }


def test_cli_run_missing_file_exits_two(tmp_path: Path):
    proc = run_cli("run", str(EXAMPLES / "backend_simple.yaml"),
                   str(tmp_path / "no_such_program.yaml"),
                   "--out", str(tmp_path / "out"))
    assert proc.returncode == 2, proc.stdout + proc.stderr


def test_cli_check_cert_passes_on_fixed_certificate(fixed_cli_run):
    _, out_dir = fixed_cli_run
    proc = run_cli("check-cert", str(out_dir / "certificate.json"))
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "OK" in proc.stdout


def test_cli_check_cert_passes_on_buggy_certificate(buggy_cli_run):
    _, out_dir = buggy_cli_run
    proc = run_cli("check-cert", str(out_dir / "certificate.json"))
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "OK" in proc.stdout


def test_cli_examples_lists_bundled_yaml_files():
    proc = run_cli("examples")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    for name in EXAMPLE_NAMES:
        assert name in proc.stdout, f"{name} missing from examples listing"


# --------------------------------------------------------------------------
# FastAPI /run endpoint
# --------------------------------------------------------------------------


def test_fastapi_run_endpoint_with_yaml_text():
    from fastapi.testclient import TestClient

    from ftq_vm.backend.main import app

    client = TestClient(app)
    payload = {
        "backend_text": (EXAMPLES / "backend_simple.yaml").read_text(encoding="utf-8"),
        "program_text": (EXAMPLES / "program_fixed.yaml").read_text(encoding="utf-8"),
    }
    resp = client.post("/run", json=payload)
    assert resp.status_code == 200
    data = resp.json()
    assert data["ok"] is True
    assert data["errors"] == []
    assert data["stats"]["verdict"] == "pass"
