"""The VM half of the differential error corpus — CANONICAL CONTRACT CODES.

Both checkers report violations in ONE shared vocabulary (the canonical
contract codes, defined in ``device_program.CONTRACT_CODES`` and mirrored
in ``FormalRV/Codegen/DeviceProgramParse.lean`` §4), so the reasons are
compared by LITERAL EQUALITY, not by a hand-maintained mapping table.

18 examples over 5 hardware configurations (all generated from Lean:
schedules in ``scripts/EmitErrorCorpus.lean``, backends from
``System/Params/HardwareCatalog.lean``).  ``LEAN_CODES`` below mirrors the
expectation table of ``scripts/CheckErrorCorpus.lean`` (which asserts the
Lean side); ``VM_CODES`` is what this file asserts the VM reports.  For
every example the two columns are IDENTICAL except the five documented
model-gap rows:

  e13/e14 QUBIT_LIFECYCLE, e15 MAGIC_DEMAND_WINDOW, e16
  FEEDFORWARD_LATENCY — Lean-only checks (the VM has no end-of-schedule
  leak rule, no double-allocation rule, no demand-window cap, no classical-
  op duration table);
  e17 FEEDFORWARD_FRESHNESS — VM-only check (Lean's feedback rule is
  order-only, no freshness window).

VM error kinds outside the shared DEVICE-PROGRAM surface
(TokenBufferOverflow, DoubleConsume, ServiceCapacityExceeded,
DependencyViolation, AllocationError, QubitExplicitnessViolation, factory
footprint/stochastic errors) are exercised by the native-format suites.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from ftq_vm.backend.device_program import (CONTRACT_CODES,
                                           DeviceProgramError,
                                           contract_codes)
from ftq_vm.backend.loader import LoadError, load_backend, load_program
from ftq_vm.backend.simulator import run_simulation

CORPUS = Path(__file__).parent.parent / "examples" / "corpus"

#: example -> (backend tag, Lean codes, VM codes).
#: "parse"/"load:CODE" mark rejection stage; sets are runtime codes.
MATRIX = {
    "e01_clean":              ("std",        set(),                      set()),
    "e02_qubit_conflict":     ("dualrail",   {"QUBIT_EXCLUSIVITY"},      {"QUBIT_EXCLUSIVITY"}),
    "e03_cnot_cap":           ("std",        {"GATE_PARALLELISM"},       {"GATE_PARALLELISM"}),
    "e04_cap_reconfigured":   ("dualrail",   set(),                      set()),
    "e05_slow_decode":        ("std",        {"DECODER_REACTION"},       {"DECODER_REACTION"}),
    "e06_pfu_before_decode":  ("std",        {"FEEDFORWARD_CAUSALITY"},  {"FEEDFORWARD_CAUSALITY"}),
    "e07_reuse_after_measure": ("std",       {"QUBIT_LIFECYCLE"},        {"QUBIT_LIFECYCLE"}),
    "e08_use_before_request": ("std",        {"QUBIT_LIFECYCLE"},        {"QUBIT_LIFECYCLE"}),
    "e09_unknown_site":       ("std",        {"ARCH_BOUNDS"},            "load:ARCH_BOUNDS"),
    "e10_unsupported_gate":   ("std",        {"GATE_UNSUPPORTED"},       "load:GATE_UNSUPPORTED"),
    "e11_wrong_duration":     ("std",        {"GATE_DURATION"},          "load:GATE_DURATION"),
    "e12_decoder_burst":      ("tinyqueue",  {"DECODER_OVERLOAD"},       {"DECODER_OVERLOAD"}),
    "e13_dangling_live":      ("std",        {"QUBIT_LIFECYCLE"},        set()),   # model gap
    "e14_double_request":     ("std",        {"QUBIT_LIFECYCLE"},        set()),   # model gap
    "e15_magic_window":       ("magicstock", {"MAGIC_DEMAND_WINDOW"},    set()),   # model gap
    "e16_slow_feedforward":   ("std",        {"FEEDFORWARD_LATENCY"},    set()),   # model gap
    "e17_stale_feedforward":  ("staledecode", set(),                     {"FEEDFORWARD_FRESHNESS"}),  # model gap
    "e18_empty_interval":     ("std",        "parse",                    "load:SYNTAX"),
    "e19_syndrome_flood":     ("surfacestream", {"SYNDROME_BANDWIDTH"},  {"SYNDROME_BANDWIDTH"}),
    "e20_syndrome_paced":     ("surfacestream", set(),                   set()),
    "e21_decoder_paced":      ("strictdecode", set(),                    set()),
    "e22_decoder_oversubscribed": ("strictdecode", {"DECODER_OVERLOAD"}, {"DECODER_OVERLOAD"}),
    "e23_decoder_premature_reuse": ("strictdecode", {"DECODER_OVERLOAD"}, {"DECODER_OVERLOAD"}),
    "e24_decode_before_measure": ("std",        {"SYNDROME_CAUSALITY"},  {"SYNDROME_CAUSALITY"}),
    "e25_magic_unprepared":   ("magicscarce",  {"MAGIC_SUPPLY"},         {"MAGIC_SUPPLY"}),
}

#: the five rows where the two checkers legitimately differ (model gaps)
KNOWN_GAPS = {"e13_dangling_live", "e14_double_request", "e15_magic_window",
              "e16_slow_feedforward", "e17_stale_feedforward"}


@pytest.mark.parametrize("name", sorted(MATRIX))
def test_corpus_example(name):
    tag, _lean, vm_expected = MATRIX[name]
    backend = load_backend(CORPUS / f"backend_{tag}.json")
    program_path = CORPUS / f"{name}.dp"

    if isinstance(vm_expected, str) and vm_expected.startswith("load:"):
        code = vm_expected.removeprefix("load:")
        with pytest.raises((LoadError, DeviceProgramError)) as exc:
            load_program(program_path, backend)
        cause = exc.value if isinstance(exc.value, DeviceProgramError) \
            else exc.value.__cause__
        assert isinstance(cause, DeviceProgramError)
        assert cause.code == code
        return

    program = load_program(program_path, backend)
    result = run_simulation(backend, program)
    codes = contract_codes(result, backend)
    assert codes == vm_expected, \
        f"{name}: VM reported {codes}, expected {vm_expected}: " \
        + "; ".join(e.headline() for e in result.errors)


def test_reasons_identical_outside_known_gaps():
    """THE unification check: for every corpus example outside the five
    documented model gaps, the VM's contract codes equal Lean's literally
    (treating load-stage rejection of code X as reporting X)."""
    for name, (_tag, lean, vm) in MATRIX.items():
        if name in KNOWN_GAPS:
            continue
        lean_set = {"SYNTAX"} if lean == "parse" else lean
        vm_set = {vm.removeprefix("load:")} if isinstance(vm, str) else vm
        assert lean_set == vm_set, f"{name}: Lean {lean_set} != VM {vm_set}"


def test_all_codes_canonical():
    """Every code in the matrix is a registered canonical contract code."""
    for _tag, lean, vm in MATRIX.values():
        for cell in (lean, vm):
            if isinstance(cell, set):
                assert cell <= set(CONTRACT_CODES)
            elif cell.startswith("load:"):
                assert cell.removeprefix("load:") in CONTRACT_CODES


def test_corpus_is_complete():
    """Every emitted error-corpus example (eNN_*) has a matrix row, and
    vice versa.  (Compiled-pipeline artifacts like qec_compiled.dp live in
    the same directory but are covered by their own suites.)"""
    programs = {p.stem for p in CORPUS.glob("e*.dp")}
    assert programs == set(MATRIX)
    backends = {p.stem.removeprefix("backend_") for p in CORPUS.glob("backend_*.json")}
    assert {tag for tag, _, _ in MATRIX.values()} <= backends


def test_corpus_code_coverage():
    """The corpus exercises every contract code expressible on the shared
    surface (CONTROL_PARALLELISM, FACTORY_PORT_EXCLUSIVITY, ZONE_CAPACITY
    and MAGIC_SUPPLY are constructible but subsumed by stronger checks in
    these minimal examples; the rest of CONTRACT_CODES is the documented
    model-gap / native-surface remainder)."""
    seen = set()
    for _tag, lean, vm in MATRIX.values():
        for cell in (lean, vm):
            if isinstance(cell, set):
                seen |= cell
            elif cell.startswith("load:"):
                seen.add(cell.removeprefix("load:"))
            elif cell == "parse":
                seen.add("SYNTAX")
    assert seen == {"SYNTAX", "GATE_UNSUPPORTED", "GATE_DURATION",
                    "ARCH_BOUNDS", "QUBIT_EXCLUSIVITY", "QUBIT_LIFECYCLE",
                    "GATE_PARALLELISM", "DECODER_OVERLOAD",
                    "DECODER_REACTION", "FEEDFORWARD_CAUSALITY",
                    "FEEDFORWARD_LATENCY", "FEEDFORWARD_FRESHNESS",
                    "MAGIC_DEMAND_WINDOW", "SYNDROME_BANDWIDTH",
                    "SYNDROME_CAUSALITY", "MAGIC_SUPPLY"}


def test_decoder_latency_and_worker_reuse():
    """Decoder-occupancy semantics, both directions.  On the strict
    machine (2 workers, 1 ms decode latency, no queue):

    * e21: 6 decodes in back-to-back pairs PASS — each worker is freed at
      the END of its 1 ms decode (half-open at t=1000) and immediately
      reused by the next decode;
    * e23: identical except the third decode starts at t=999, 1 µs before
      a worker is freed — REJECTED.  The only difference between the two
      programs is that 1 µs, so this pins 'the service is freed after the
      decoding finishes, then can be reused'.
    """
    backend = load_backend(CORPUS / "backend_strictdecode.json")

    paced = load_program(CORPUS / "e21_decoder_paced.dp", backend)
    result = run_simulation(backend, paced)
    assert result.ok
    assert sum(1 for op in paced.ops if op.kind == "decode_syndrome") == 6

    premature = load_program(CORPUS / "e23_decoder_premature_reuse.dp", backend)
    bad = run_simulation(backend, premature)
    assert not bad.ok
    assert contract_codes(bad, backend) == {"DECODER_OVERLOAD"}
    assert {e.kind.value for e in bad.errors} == {"ServiceQueueOverflow"}

    # finiteness, mid-flight: a third decode at t=500 against 2 busy workers
    over = load_program(CORPUS / "e22_decoder_oversubscribed.dp", backend)
    res = run_simulation(backend, over)
    assert not res.ok and contract_codes(res, backend) == {"DECODER_OVERLOAD"}


def test_syndrome_bandwidth_counts_actual_bits():
    """The audit really COUNTS syndrome bits against the link: on the
    4 KB/ms machine (32768 bits / 1000 µs), the 25 µs-cadence flood packs
    40 rounds × 16 patches × 64 bits = 40960 bits into one window, and the
    error message carries that arithmetic."""
    backend = load_backend(CORPUS / "backend_surfacestream.json")
    program = load_program(CORPUS / "e19_syndrome_flood.dp", backend)
    result = run_simulation(backend, program)
    errs = [e for e in result.errors if e.kind.value == "ThroughputExceeded"]
    assert len(errs) == 1
    msg = errs[0].message
    assert "40960 bits" in msg and "32768 bits" in msg and "1000us" in msg
    # the paced variant fits: 25 rounds x 1024 = 25600 <= 32768
    paced = load_program(CORPUS / "e20_syndrome_paced.dp", backend)
    assert run_simulation(backend, paced).ok
