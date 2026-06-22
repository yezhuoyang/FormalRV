"""VM half of the W2-driver cross-check.

``qec_compiled.dp`` is emitted by ``scripts/EmitQECCompiled.lean`` from
``QECScheduleToSystem.demoCompiled`` — a heterogeneous QEC-layer surgery
program (X-merge, CCZ magic injection = 1 magic state + 3 different
merges, Z-merge) compiled by the whole-program W2 driver: every SysCall is
derived from the gadgets' connection matrices, the clock and the decoder
round counter are threaded globally.

Lean half (native_decide): ``demoCompiled_passes`` (full bundle on
``adder_d3_magicStock``), ``demoCompiled_decode_ids_unique``,
``demoCompiled_fails_without_reaction_budget``, and the parametric laws
``compileQECProgram_decodeIds_nodup`` / ``compileQECProgram_length``.
"""

from __future__ import annotations

from pathlib import Path

from ftq_vm.backend.device_program import contract_codes, parallel_groups
from ftq_vm.backend.loader import load_backend, load_program
from ftq_vm.backend.simulator import run_simulation

CORPUS = Path(__file__).parent.parent / "examples" / "corpus"


def test_qec_compiled_passes_on_stocked_machine():
    backend = load_backend(CORPUS / "backend_magicstock.json")
    program = load_program(CORPUS / "qec_compiled.dp", backend)
    result = run_simulation(backend, program)
    assert result.ok, [e.headline() for e in result.errors]
    # count = the Lean closed form programSyscallCount (44) and wallclock 44us
    assert len(program.ops) == 44
    assert result.stats.total_runtime_us == 44
    # heterogeneous shape: one magic consumption, 8 decode jobs
    assert sum(1 for op in program.ops if op.kind == "request_magic") == 1
    decodes = [op for op in program.ops if op.kind == "decode_syndrome"]
    assert len(decodes) == 8


def test_qec_compiled_decode_rounds_globally_unique():
    """The id-aliasing gap is closed at the compiler: decode rounds are
    consecutive and unique, so each frame update consumes exactly its own
    round's result token (Lean: decodeIds = range' — same law)."""
    backend = load_backend(CORPUS / "backend_magicstock.json")
    program = load_program(CORPUS / "qec_compiled.dp", backend)
    rounds = [op.metadata["round"] for op in program.ops
              if op.kind == "decode_syndrome"]
    assert rounds == list(range(8))
    tokens = [op.service[0].result_token for op in program.ops
              if op.kind == "decode_syndrome"]
    assert len(set(tokens)) == 8
    # fully sequential by construction (safe under every per-kind cap)
    assert all(len(ids) == 1 for _, ids in parallel_groups(program))


def test_qec_compiled_needs_magic_supply():
    """On a machine WITHOUT magic-state stock the same compiled program
    fails causally (MAGIC_SUPPLY).  Both checkers now enforce this: the
    VM via its token ledger, Lean via the I6.b supply-causality check
    (`magic_supply_ok` — stock + factory production curve), so the
    formerly-documented supply-side gap is CLOSED on the shared
    surface."""
    backend = load_backend(CORPUS / "backend_std.json")
    program = load_program(CORPUS / "qec_compiled.dp", backend)
    result = run_simulation(backend, program)
    assert not result.ok
    assert contract_codes(result, backend) == {"MAGIC_SUPPLY"}
