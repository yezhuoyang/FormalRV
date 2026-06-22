"""DEVICE-PROGRAM 1.0 loader — the shared Lean ↔ VM program syntax.

One textual schedule format that BOTH checkers parse directly:

* the Lean System layer emits it (``FormalRV/Codegen/SysCallEmit.lean``) and
  parses it back (``FormalRV/Codegen/DeviceProgramParse.lean``), running the
  decidable invariant bundle on the result;
* this module parses the SAME text into an FTQ-VM :class:`Program` against a
  backend config, so ``python -m ftq_vm run backend.json program.dp`` checks
  the identical schedule.

Grammar (line-oriented; emitted by ``emitSchedule``)::

    DEVICE-PROGRAM 1.0;
    // <name>  (free comment)
    [<begin>,<end>)us  <PHYS|SYS>  <op>  <args>
    -- trailing comments allowed

Ops and their args (one per ``SysCallKind``).  Gates and bases are NAMED —
``gate=CNOT``, ``basis=Z``, never an opaque numeral — so both checkers can
verify the gate is SUPPORTED by the backend and takes its hardware time;
the ancilla request names its EXACT qubit (qubits are never fungible)::

    gate1q             q[i] gate=<H|X|Z|S|T|...>
    gate2q             q[i],q[j] gate=<CNOT|CZ|SWAP|...>
    measure            q[i] basis=<Z|X|Y>
    transit            q[i] via channel=<c>
    request_ancilla    q[i]
    request_magic      factory=<f>
    decode_syndrome    round=<r>
    pauli_frame_update corr=<c>

Site mapping: ``q[s]`` uses the GLOBAL Lean site number; each backend zone
declares ``site_lo``, so ``q[s]`` lowers to the explicit qubit
``<zone>[s - site_lo]`` — the VM's explicit-qubit discipline.

Gate lowering: a ``gate2q ... gate=CNOT`` line becomes an op of kind
``CNOT``; the backend's gate table must contain that kind (else
"unsupported by this system") with matching arity and duration.

Parallel layers: ops sharing the same exact ``[begin, end)`` window form
one simultaneous layer, recognized after parsing (:func:`parallel_groups`);
each grouped op carries ``metadata.parallel_group`` / ``group_size``.

``decode_syndrome round=r`` submits one job to the backend's decoder service
producing the result token ``decode<r>`` at its computed completion;
``pauli_frame_update corr=c`` consumes ``decode<c>`` — so feedforward
causality is checked by the token ledger.
"""

from __future__ import annotations

import re
from typing import Optional

from .models import BackendConfig, Op, Program, ResourceUse, UseMode, ZoneSpec

HEADER = "DEVICE-PROGRAM"

_INTERVAL_RE = re.compile(r"^\[(\d+),(\d+)\)us$")
_QREF_RE = re.compile(r"^q\[(\d+)\]$")
_KV_NUM_RE = re.compile(r"^(\w+)=(\d+)$")
_KV_NAME_RE = re.compile(r"^(\w+)=([A-Za-z]\w*)$")

#: measurement bases are named, mirroring Lean's ``basisNames``
BASIS_NAMES = ("Z", "X", "Y")


#: The CANONICAL CONTRACT CODES — the shared error vocabulary of the two
#: checkers, named after the violated hardware contract.  The Lean side
#: emits the same codes (`FormalRV/Codegen/DeviceProgramParse.lean` §4 —
#: keep the two lists in sync); the differential corpus compares reasons
#: by literal equality.
CONTRACT_CODES = (
    "SYNTAX", "GATE_UNSUPPORTED", "GATE_DURATION", "ARCH_BOUNDS",
    "QUBIT_EXCLUSIVITY", "QUBIT_LIFECYCLE", "GATE_PARALLELISM",
    "CONTROL_PARALLELISM", "DECODER_OVERLOAD", "DECODER_REACTION",
    "FEEDFORWARD_CAUSALITY", "FEEDFORWARD_LATENCY", "FEEDFORWARD_FRESHNESS",
    "MAGIC_DEMAND_WINDOW", "MAGIC_SUPPLY", "FACTORY_PORT_EXCLUSIVITY",
    "ZONE_CAPACITY", "SYNDROME_BANDWIDTH", "SYNDROME_CAUSALITY",
)


class DeviceProgramError(Exception):
    """Raised when DEVICE-PROGRAM text cannot be parsed or lowered.

    ``code`` carries the canonical contract code (load-stage rejections:
    SYNTAX / GATE_UNSUPPORTED / GATE_DURATION / ARCH_BOUNDS).
    """

    def __init__(self, message: str, code: str = "SYNTAX"):
        super().__init__(message)
        self.code = code


def is_device_program(text: str) -> bool:
    return text.lstrip().startswith(HEADER)


def _kv_num(token: str, key: str, lineno: int) -> int:
    m = _KV_NUM_RE.match(token)
    if not m or m.group(1) != key:
        raise DeviceProgramError(f"line {lineno}: expected {key}=<n>, got {token!r}")
    return int(m.group(2))


def _kv_name(token: str, key: str, lineno: int) -> str:
    m = _KV_NAME_RE.match(token)
    if not m or m.group(1) != key:
        raise DeviceProgramError(
            f"line {lineno}: expected {key}=<NAME> (explicit names, e.g. "
            f"gate=CNOT / basis=Z), got {token!r}")
    return m.group(2)


def _qref(token: str, lineno: int) -> int:
    m = _QREF_RE.match(token)
    if not m:
        raise DeviceProgramError(f"line {lineno}: expected q[<site>], got {token!r}")
    return int(m.group(1))


class _SiteMap:
    """Global Lean site numbers <-> explicit VM zone qubits."""

    def __init__(self, backend: BackendConfig):
        self.zones: list[tuple[int, int, ZoneSpec]] = []  # (lo, hi, spec)
        lo_seen = set()
        for z in backend.zones:
            if z.site_lo is None:
                raise DeviceProgramError(
                    f"zone {z.id!r} has no site_lo; DEVICE-PROGRAM interop needs "
                    f"every zone to declare its global Lean site range")
            if z.site_lo in lo_seen:
                raise DeviceProgramError(f"duplicate site_lo {z.site_lo}")
            lo_seen.add(z.site_lo)
            self.zones.append((z.site_lo, z.site_lo + z.count, z))
        self.zones.sort(key=lambda t: t[0])

    def ref(self, site: int, lineno: int) -> str:
        for lo, hi, z in self.zones:
            if lo <= site < hi:
                return f"{z.id}[{site - lo}]"
        raise DeviceProgramError(
            f"line {lineno}: site q[{site}] lies in no declared zone",
            code="ARCH_BOUNDS")


def _decoder_service(backend: BackendConfig) -> Optional[str]:
    for s in backend.services:
        return s.id
    return None


def contract_code(error, backend: BackendConfig) -> str:
    """Map a runtime :class:`VMError` to its canonical contract code.

    The mapping is contextual: the VM's mechanism-level error kinds refine
    to contract codes using the involved resource/token/service.  Returns
    one of :data:`CONTRACT_CODES`; unmapped combinations fall back to the
    VM kind name (none arise on the DEVICE-PROGRAM surface).
    """
    kind = error.kind.value
    res = error.resource or ""
    zone_ids = {z.id for z in backend.zones}

    def is_zone_qubit(r: str) -> bool:
        return "[" in r and r.split("[", 1)[0] in zone_ids

    def is_factory_resource(r: str) -> bool:
        return r.endswith(".batch_slots") or r.endswith(".output_ports")

    if kind == "ResourceConflict":
        if is_factory_resource(res):
            return "FACTORY_PORT_EXCLUSIVITY"
        return "QUBIT_EXCLUSIVITY"
    if kind == "CapacityExceeded":
        if res.startswith("gate.") or res == "gates.parallel":
            return "GATE_PARALLELISM"
        if is_factory_resource(res):
            return "FACTORY_PORT_EXCLUSIVITY"
        if is_zone_qubit(res):
            return "ZONE_CAPACITY"
        return "CONTROL_PARALLELISM"
    if kind == "QubitReuseViolation":
        return "QUBIT_LIFECYCLE"
    if kind == "DeadlineMiss":
        return "DECODER_REACTION"
    if kind == "ServiceQueueOverflow":
        return "DECODER_OVERLOAD"
    if kind in ("TokenUnavailable", "TokenFreshnessViolation"):
        token = error.token or ""
        if token == "syndrome":
            return "SYNDROME_CAUSALITY"
        if token.startswith("decode"):
            return ("FEEDFORWARD_CAUSALITY" if kind == "TokenUnavailable"
                    else "FEEDFORWARD_FRESHNESS")
        if token == "MagicState":
            return "MAGIC_SUPPLY"
        return kind
    if kind == "UnknownResource":
        return "ARCH_BOUNDS"
    if kind == "ThroughputExceeded":
        return "SYNDROME_BANDWIDTH" if "syndrome" in res else kind
    return kind


def contract_codes(result, backend: BackendConfig) -> set[str]:
    """The set of canonical contract codes a run violated."""
    return {contract_code(e, backend) for e in result.errors}


def parallel_groups(program: Program) -> list[tuple[tuple[int, int], list[str]]]:
    """Group ops into parallel layers by exact ``[at_us, end_us)`` window,
    preserving first-occurrence order (mirrors Lean's ``parallelGroups``)."""
    order: list[tuple[int, int]] = []
    groups: dict[tuple[int, int], list[str]] = {}
    for op in program.ops:
        key = (op.at_us, op.end_us)
        if key not in groups:
            groups[key] = []
            order.append(key)
        groups[key].append(op.id)
    return [(key, groups[key]) for key in order]


def max_simultaneous(program: Program) -> int:
    """Widest simultaneous layer (1 = fully sequential)."""
    return max((len(ids) for _, ids in parallel_groups(program)), default=0)


def load_device_program(text: str, backend: BackendConfig,
                        source: str = "device program") -> Program:
    """Parse DEVICE-PROGRAM text into a :class:`Program` for ``backend``."""
    lines = text.splitlines()
    if not lines or not lines[0].strip().startswith(HEADER):
        raise DeviceProgramError(f"{source}: missing 'DEVICE-PROGRAM 1.0;' header")

    sitemap = _SiteMap(backend)
    decoder = _decoder_service(backend)
    gate_table = backend.gate_map()

    def supported_gate(name: str, arity: int, lineno: int) -> None:
        gate = gate_table.get(name)
        if gate is None:
            raise DeviceProgramError(
                f"line {lineno}: gate {name!r} is not supported by this system "
                f"(backend gate table: {sorted(gate_table)})",
                code="GATE_UNSUPPORTED")
        if gate.qubits is not None and gate.qubits != arity:
            raise DeviceProgramError(
                f"line {lineno}: gate {name!r} acts on {gate.qubits} qubit(s), "
                f"used here with {arity}", code="GATE_UNSUPPORTED")

    name = "device_program"
    ops: list[Op] = []
    n = 0

    for lineno, raw in enumerate(lines[1:], start=2):
        line = raw.strip()
        if not line or line.startswith("--"):
            continue
        if line.startswith("//"):
            if n == 0:  # first comment carries the program name
                name = line.lstrip("/ ").split("(")[0].strip() or name
            continue

        tokens = [t for t in line.split(" ") if t]
        if len(tokens) < 3:
            raise DeviceProgramError(f"line {lineno}: malformed op line {line!r}")
        m = _INTERVAL_RE.match(tokens[0])
        if not m:
            raise DeviceProgramError(
                f"line {lineno}: expected [begin,end)us, got {tokens[0]!r}")
        begin, end = int(m.group(1)), int(m.group(2))
        if end <= begin:
            raise DeviceProgramError(
                f"line {lineno}: empty/inverted interval [{begin},{end})")
        # tokens[1] is the PHYS/SYS category tag — redundant, ignored
        op_name, args = tokens[2], tokens[3:]
        duration = end - begin
        n += 1
        op_id = f"l{lineno}_{op_name}"
        doc: dict = {"id": op_id, "kind": op_name, "at_us": begin,
                     "duration_us": duration, "uses": [], "consumes": [],
                     "produces": [], "service": [], "metadata": {"line": lineno}}

        if op_name == "gate1q":
            site = _qref(args[0], lineno)
            gname = _kv_name(args[1], "gate", lineno)
            supported_gate(gname, 1, lineno)
            doc["kind"] = gname
            doc["id"] = f"l{lineno}_{gname}"
            doc["uses"] = [ResourceUse(resource=sitemap.ref(site, lineno),
                                       mode=UseMode.exclusive)]
        elif op_name == "gate2q":
            a_str, b_str = args[0].split(",", 1)
            sa, sb = _qref(a_str, lineno), _qref(b_str, lineno)
            gname = _kv_name(args[1], "gate", lineno)
            supported_gate(gname, 2, lineno)
            doc["kind"] = gname
            doc["id"] = f"l{lineno}_{gname}"
            doc["uses"] = [ResourceUse(resource=sitemap.ref(sa, lineno),
                                       mode=UseMode.exclusive),
                           ResourceUse(resource=sitemap.ref(sb, lineno),
                                       mode=UseMode.exclusive)]
        elif op_name == "measure":
            site = _qref(args[0], lineno)
            basis = _kv_name(args[1], "basis", lineno)
            if basis not in BASIS_NAMES:
                raise DeviceProgramError(
                    f"line {lineno}: unknown basis {basis!r} (named bases: "
                    f"{'/'.join(BASIS_NAMES)})")
            supported_gate("measure", 1, lineno)
            doc["metadata"]["basis"] = basis
            doc["uses"] = [ResourceUse(resource=sitemap.ref(site, lineno),
                                       mode=UseMode.exclusive)]
            # CAUSALITY: the measurement PRODUCES one unit of syndrome
            # data at its completion; decodes consume it (I6.a)
            doc["produces"] = [{"kind": "syndrome"}]
        elif op_name == "transit":
            site = _qref(args[0], lineno)
            if len(args) < 3 or args[1] != "via":
                raise DeviceProgramError(f"line {lineno}: transit needs 'via channel=<c>'")
            chan = _kv_num(args[2], "channel", lineno)
            doc["metadata"]["channel"] = chan
            doc["uses"] = [ResourceUse(resource=sitemap.ref(site, lineno),
                                       mode=UseMode.exclusive)]
            chan_res = f"channel{chan}"
            if chan_res in backend.resource_map():
                doc["uses"].append(ResourceUse(resource=chan_res))
        elif op_name == "request_ancilla":
            # the request names its EXACT qubit — no fungible zone form
            site = _qref(args[0], lineno)
            supported_gate("request_ancilla", 1, lineno)
            doc["uses"] = [ResourceUse(resource=sitemap.ref(site, lineno),
                                       mode=UseMode.exclusive)]
        elif op_name == "request_magic":
            doc["metadata"]["factory"] = _kv_num(args[0], "factory", lineno)
            doc["consumes"] = [{"kind": "MagicState"}]
        elif op_name == "decode_syndrome":
            rnd = _kv_num(args[0], "round", lineno)
            doc["metadata"]["round"] = rnd
            if decoder is None:
                raise DeviceProgramError(
                    f"line {lineno}: decode_syndrome but the backend declares "
                    f"no decoder service")
            # CAUSALITY: decoding consumes syndrome data that must already
            # EXIST — a completed measurement (I6.a / SYNDROME_CAUSALITY)
            doc["consumes"] = [{"kind": "syndrome"}]
            doc["service"] = [{"service": decoder, "count": 1,
                               "processing_time_us": duration,
                               "result_token": f"decode{rnd}"}]
        elif op_name == "pauli_frame_update":
            corr = _kv_num(args[0], "corr", lineno)
            doc["metadata"]["corr"] = corr
            doc["consumes"] = [{"kind": f"decode{corr}"}]
        else:
            raise DeviceProgramError(f"line {lineno}: unknown op {op_name!r}")

        gate = gate_table.get(doc["kind"])
        if gate is not None and duration != gate.duration_us:
            raise DeviceProgramError(
                f"line {lineno}: {doc['kind']} declares {duration}us but the "
                f"hardware gate table says {gate.duration_us}us; gate times "
                f"are hardware facts, not schedule choices",
                code="GATE_DURATION")
        ops.append(Op.model_validate(doc))

    program = Program(name=name, ops=ops)
    # annotate recognized parallel layers (exact-interval grouping)
    for gidx, (_, ids) in enumerate(parallel_groups(program)):
        if len(ids) > 1:
            for op in program.ops:
                if op.id in ids:
                    op.metadata["parallel_group"] = gidx
                    op.metadata["group_size"] = len(ids)
    return program
