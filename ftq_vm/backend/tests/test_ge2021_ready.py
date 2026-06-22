"""GE2021 readiness — the VM half.

``backend_ge2021.json`` is the patch-granular Gidney–Ekerå 2021 machine
(arXiv 1905.09749), generated from ``HardwareCatalog.ge2021_logical``:
6200 d=27 data patches + 6200 routing/bus patches + 1093 CCZ factory
ports; 62 000 decode lanes with the paper's 10 µs reaction budget; the
6200-patch × 728-bit/round syndrome link; a 2-state prepared buffer plus
the 1093-factory production curve (Lean-side I6.b).

``ge2021_probe.dp`` is the W2-compiled d=27 probe (every merge runs the
paper's tau_s = 27 syndrome rounds).  Lean: ``ge2021_probe_passes`` etc.
(native_decide) and the audit pin ``catalog_ge2021_arch_eq`` (the
catalog's physical twin IS the audited 20 M-qubit ``ge2021Arch``).

When the other lane's QEC-level compilation of the paper lands, its
``QECProgram`` drives the SAME compiler onto the SAME backend — these
tests pin that the lane is open.
"""

from __future__ import annotations

from pathlib import Path

from ftq_vm.backend.device_program import contract_codes
from ftq_vm.backend.loader import load_backend, load_program
from ftq_vm.backend.simulator import run_simulation

CORPUS = Path(__file__).parent.parent / "examples" / "corpus"


def test_ge2021_probe_passes():
    backend = load_backend(CORPUS / "backend_ge2021.json")
    program = load_program(CORPUS / "ge2021_probe.dp", backend)
    result = run_simulation(backend, program)
    assert result.ok, [e.headline() for e in result.errors][:5]
    # the paper's distance is real: 5 merge gadgets x 27 rounds each
    decodes = [op for op in program.ops if op.kind == "decode_syndrome"]
    assert len(decodes) == 5 * 27
    rounds = [op.metadata["round"] for op in decodes]
    assert rounds == list(range(135))          # globally unique, d=27 blocks
    assert sum(1 for op in program.ops if op.kind == "request_magic") == 1


def test_ge2021_machine_parameters_bite():
    """The backend really carries the paper's numbers: 62 000 decode
    lanes, 10 us reaction, 13 493 patch sites, the 4.51 Gbit/ms syndrome
    link sized to 6200 patches x 728 bits."""
    import json
    doc = json.loads((CORPUS / "backend_ge2021.json").read_text(encoding="utf-8"))
    assert doc["resources"]["decoder_pool"]["workers"] == 62_000
    assert doc["resources"]["decoder_pool"]["max_latency_us"] == 10
    assert sum(z["count"] for z in doc["zones"].values()) == 13_493
    cap = doc["throughput_caps"][0]
    assert cap["weight_per_op"] == 728                       # d^2 - 1 at d=27
    assert cap["max_weight"] == 1000 * 6200 * 728            # full-board rate
    assert doc["x-lean"]["window_us"] == 12_000              # CCZ window
    assert doc["x-lean"]["max_per_window"] == 1093           # factories
    assert doc["x-lean"]["magic_per_period"] == 1093


def test_ge2021_probe_needs_prepared_magic():
    """Causality on the GE2021 machine: with the prepared buffer emptied,
    the probe's CCZ injection has no state behind it — MAGIC_SUPPLY (the
    Lean twin rejects via the I6.b production curve at t < 12 000)."""
    import json
    doc = json.loads((CORPUS / "backend_ge2021.json").read_text(encoding="utf-8"))
    doc["tokens"]["MagicState"]["initial_inventory"] = 0
    drained = CORPUS / "backend_ge2021_drained.json"
    drained.write_text(json.dumps(doc), encoding="utf-8")
    try:
        backend = load_backend(drained)
        program = load_program(CORPUS / "ge2021_probe.dp", backend)
        result = run_simulation(backend, program)
        assert not result.ok
        assert contract_codes(result, backend) == {"MAGIC_SUPPLY"}
    finally:
        drained.unlink()
