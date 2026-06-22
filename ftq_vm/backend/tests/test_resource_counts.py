"""Lean ↔ VM resource-counting consistency (the L4 design principle).

``scripts/EmitResourceCounts.lean`` runs THE canonical Lean counters
(`Resource/SysCallCount`: wallclock, busy time, per-kind op counts, qubit
footprint as a SET of global sites, peak site occupancy) on parsed
DEVICE-PROGRAM files and writes ``lean_resource_counts.json``.

This test recomputes every quantity INDEPENDENTLY from the FTQ-VM's parse
of the same files — different parser, different language, different data
structures — and asserts EXACT agreement.  Neither side's number is
copied from the other; agreement means the time/qubit counting systems
are consistent, per the design rule that resource counts are predefined
tree-walks over the concrete syntactic object.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from ftq_vm.backend.loader import load_backend, load_program
from ftq_vm.backend.simulator import run_simulation

EXAMPLES = Path(__file__).parent.parent / "examples"
CORPUS = EXAMPLES / "corpus"

CASES = {
    "qec_compiled":       (CORPUS / "qec_compiled.dp",       CORPUS / "backend_magicstock.json"),
    "e01_clean":          (CORPUS / "e01_clean.dp",          CORPUS / "backend_std.json"),
    "e19_syndrome_flood": (CORPUS / "e19_syndrome_flood.dp", CORPUS / "backend_surfacestream.json"),
    "e21_decoder_paced":  (CORPUS / "e21_decoder_paced.dp",  CORPUS / "backend_strictdecode.json"),
    "adder_d3":           (EXAMPLES / "adder_d3.dp",         EXAMPLES / "adder_d3_backend.json"),
}

#: VM op kind -> Lean per-kind counter, derived from the backend gate
#: table for named gates (arity 1 -> gate1q, 2 -> gate2q).
FIXED_KINDS = {
    "measure": "measure", "transit": "transit",
    "request_ancilla": "fresh_ancilla", "request_magic": "magic_req",
    "decode_syndrome": "decode", "pauli_frame_update": "feedback",
}


def _site_map(backend_path: Path):
    doc = json.loads(backend_path.read_text(encoding="utf-8"))
    return {zid: z["site_lo"] for zid, z in doc["zones"].items()}, doc


def _op_sites(op, site_lo):
    """Global Lean site ids of the qubits an op touches (zone refs only)."""
    sites = []
    for use in op.uses:
        if "[" in use.resource:
            zone, idx = use.resource[:-1].split("[")
            if zone in site_lo:
                sites.append(site_lo[zone] + int(idx))
    return sites


@pytest.mark.parametrize("name", sorted(CASES))
def test_counts_match_lean(name):
    lean = json.loads((CORPUS / "lean_resource_counts.json")
                      .read_text(encoding="utf-8"))[name]
    program_path, backend_path = CASES[name]
    backend = load_backend(backend_path)
    program = load_program(program_path, backend)
    site_lo, doc = _site_map(backend_path)
    gate_arity = {g: spec.get("qubits", 1) for g, spec in doc["gates"].items()}

    # TIME — wallclock (also = the VM run's reported runtime) and busy time
    wallclock = max(op.end_us for op in program.ops)
    assert wallclock == lean["wallclock_us"]
    result = run_simulation(backend, program)
    assert result.stats.total_runtime_us == lean["wallclock_us"]
    assert sum(op.duration_us for op in program.ops) == lean["busy_us"]

    # TIME — op counts per class
    counts = {k: 0 for k in
              ("gate1q", "gate2q", "measure", "transit", "fresh_ancilla",
               "magic_req", "decode", "feedback")}
    for op in program.ops:
        if op.kind in FIXED_KINDS:
            counts[FIXED_KINDS[op.kind]] += 1
        elif op.kind in gate_arity:
            counts["gate1q" if gate_arity[op.kind] == 1 else "gate2q"] += 1
        else:
            pytest.fail(f"unclassified op kind {op.kind!r}")
    assert len(program.ops) == lean["syscall_count"]
    for key, value in counts.items():
        assert value == lean[key], f"{name}: {key} VM={value} Lean={lean[key]}"

    # SPACE — the exact SET of touched sites, footprint, and peak occupancy
    all_sites = sorted({s for op in program.ops
                        for s in _op_sites(op, site_lo)})
    assert all_sites == lean["sites"]
    assert len(all_sites) == lean["qubit_footprint"]
    peak = 0
    for op in program.ops:
        t = op.at_us
        active = {s for other in program.ops
                  if other.at_us <= t < other.end_us
                  for s in _op_sites(other, site_lo)}
        peak = max(peak, len(active))
    assert peak == lean["peak_sites"]
