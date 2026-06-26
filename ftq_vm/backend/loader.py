"""Load backend configs and programs from the friendly YAML/JSON syntax.

The on-disk syntax is designed so a quantum-algorithms researcher can write
files by hand; the loader compiles it into the strict internal models of
``models.py``.

Backend file
------------
.. code-block:: yaml

    unit:
      time: us                  # mandatory unit declaration (MVP: us only)

    resources:                  # one mapping; the 'kind' discriminates
      compute_slots:  {kind: logical_slot, capacity: 4096}
      t_buffer:       {kind: token_buffer, token_kind: TState, capacity: 512}
      decoder_pool:   {kind: service, workers: 128, max_latency_us: 10,
                       queue_capacity: 100000, processing_time_us: 2}

    factories:
      F0: {kind: T_factory, produces: TState, duration_us: 100,
           success_probability: 0.95, output_ports: 1, auto_retry: true}

    tokens:
      TState: {initial_inventory: 8, ttl_us: 10000}

Program file
------------
.. code-block:: yaml

    program: toy_shor_like
    ops:
      - at_us: 0
        do: start_factory
        factory: F0
        repeat: {every_us: 100, until_us: 1000}

      - at_us: 250
        do: logical_T
        qubit: q17                 # unknown keys land in op.metadata
        consume: TState
        uses:                      # mapping form: resource -> amount;
          correction_storage: 1    # naming a service submits that many jobs
          decoder_pool: 1

Every time field uses the ``_us`` suffix; nothing else is accepted.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Union

import yaml
from pydantic import ValidationError

from .models import (
    BackendConfig,
    FactorySpec,
    Op,
    Program,
    ResourceSpec,
    ServiceSpec,
    is_qubit_like_kind,
    parse_qubit_ref,
)


class LoadError(Exception):
    """Raised when an input file cannot be parsed or validated."""


#: op keys that are interpreted by the loader; everything else -> metadata
_OP_KNOWN_KEYS = {
    "id", "do", "kind", "at_us", "duration_us", "deps", "uses", "qubits",
    "consume", "consumes", "produce", "produces", "service", "repeat",
    "factory", "metadata",
}


def _read_text_or_raise(path: Path) -> str:
    """Read a file as UTF-8, converting filesystem errors into ``LoadError``.

    Guards the failure modes that otherwise escape ``read_text`` as a raw
    traceback: a path that does not exist, a path that exists but is a
    directory (e.g. a stray ``\\`` argument, which resolves to the drive root
    on Windows), an unreadable file, or non-UTF-8 bytes.  Callers convert
    ``LoadError`` into the CLI's documented exit code 2.
    """
    if not path.exists():
        raise LoadError(f"file not found: {path}")
    if path.is_dir():
        raise LoadError(f"expected a file but found a directory: {path}")
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise LoadError(f"could not read {path}: {exc}") from exc


def _load_raw(path: Union[str, Path]) -> Any:
    path = Path(path)
    text = _read_text_or_raise(path)
    try:
        if path.suffix.lower() == ".json":
            return json.loads(text)
        # YAML is a superset of JSON, so .yaml/.yml/anything else goes here.
        return yaml.safe_load(text)
    except (yaml.YAMLError, json.JSONDecodeError) as exc:
        raise LoadError(f"could not parse {path}: {exc}") from exc
    except RecursionError as exc:
        raise LoadError(f"{path}: input is nested too deeply to parse") from exc


def _validation_message(exc: ValidationError, what: str, source: str) -> str:
    lines = [f"invalid {what} ({source}):"]
    for err in exc.errors():
        loc = ".".join(str(p) for p in err["loc"])
        lines.append(f"  - {loc}: {err['msg']}")
    return "\n".join(lines)


def _check_unit(raw: dict, source: str) -> None:
    unit = raw.get("unit", {"time": "us"})
    if not isinstance(unit, dict) or unit.get("time", "us") != "us":
        raise LoadError(
            f"{source}: unsupported unit {unit!r}. The MVP uses a single global "
            f"time unit: microseconds. Declare 'unit: {{time: us}}' and use "
            f"*_us field names.")


def _reject_legacy_time_keys(obj: Any, source: str, path: str = "") -> None:
    """Mixed/implicit units are never silently accepted: any bare time-ish key
    (start/end/duration/at/max_latency/ttl/cooldown/every/until without _us)
    is rejected with a pointer at the offending location."""
    bare = {"start", "end", "duration", "at", "max_latency", "ttl", "cooldown",
            "every", "until", "submit_at", "processing_time"}
    if isinstance(obj, dict):
        for k, v in obj.items():
            if k in bare:
                raise LoadError(
                    f"{source}: time field {path + str(k)!r} must carry the _us "
                    f"suffix (all times are integer microseconds).")
            _reject_legacy_time_keys(v, source, f"{path}{k}.")
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            _reject_legacy_time_keys(v, source, f"{path}{i}.")


# --------------------------------------------------------------------------
# Backend
# --------------------------------------------------------------------------


def _require_mapping(value: Any, what: str, source: str) -> dict:
    """``value`` must be a YAML/JSON mapping (or absent -> empty).  A scalar or
    list here would otherwise crash later as a raw ``.items()`` / ``dict()``
    AttributeError/TypeError; turn it into a clean LoadError instead."""
    if value is None:
        return {}
    if not isinstance(value, dict):
        raise LoadError(f"{source}: {what} must be a mapping, got "
                        f"{type(value).__name__}")
    return value


def backend_from_obj(raw: Any, source: str = "backend config") -> BackendConfig:
    if not isinstance(raw, dict):
        raise LoadError(f"{source} must be a mapping at top level")
    _check_unit(raw, source)
    _reject_legacy_time_keys(raw, source)

    resources: list[dict] = []
    services: list[dict] = []
    token_buffer_capacity: dict[str, int] = {}
    default_latencies: dict[str, int] = dict(
        _require_mapping(raw.get("default_latencies_us"), "'default_latencies_us'", source))

    raw_resources = raw.get("resources", {}) or {}
    if isinstance(raw_resources, list):
        raise LoadError(f"{source}: 'resources' must be a mapping of id -> spec "
                        f"(e.g. measurement_bus: {{kind: bus, capacity: 64}})")
    raw_resources = _require_mapping(raw_resources, "'resources'", source)
    for rid, spec in raw_resources.items():
        if not isinstance(spec, dict):
            raise LoadError(f"{source}: resource {rid!r} must be a mapping")
        spec = dict(spec)
        kind = spec.get("kind", "resource")
        if kind == "service":
            pt = spec.pop("processing_time_us", None)
            if pt is not None:
                default_latencies.setdefault(rid, pt)
            services.append({"id": rid, **spec})
        elif kind == "token_buffer":
            token_kind = spec.get("token_kind")
            if not token_kind:
                raise LoadError(f"{source}: token_buffer {rid!r} needs 'token_kind'")
            token_buffer_capacity[token_kind] = spec.get("capacity", 1)
        else:
            if is_qubit_like_kind(kind) and spec.get("capacity", 1) > 1:
                raise LoadError(
                    f"{source}: QubitExplicitnessViolation: resource {rid!r} (kind "
                    f"{kind!r}) declares a fungible qubit pool; qubits are never "
                    f"fungible in an executable schedule. Declare it under 'zones:' "
                    f"-- zones expand to explicit capacity-1 qubits {rid}[0], "
                    f"{rid}[1], ...")
            resources.append({"id": rid, **spec})

    zones: list[dict] = []
    for zid, spec in _require_mapping(raw.get("zones"), "'zones'", source).items():
        if not isinstance(spec, dict):
            raise LoadError(f"{source}: zone {zid!r} must be a mapping "
                            f"(e.g. data: {{kind: data_qubit, count: 49}})")
        zones.append({"id": zid, **spec})

    gates: list[dict] = []
    for gkind, spec in _require_mapping(raw.get("gates"), "'gates'", source).items():
        if not isinstance(spec, dict) or "duration_us" not in spec:
            raise LoadError(
                f"{source}: gate {gkind!r} must be a mapping with duration_us "
                f"(gate times are hardware facts, e.g. "
                f"CNOT: {{duration_us: 1000, qubits: 2}})")
        gates.append({"kind": gkind, **spec})

    factories: list[dict] = []
    raw_factories = _require_mapping(raw.get("factories"), "'factories'", source)
    for fid, spec in raw_factories.items():
        if not isinstance(spec, dict):
            raise LoadError(f"{source}: factory {fid!r} must be a mapping")
        fp = spec.get("footprint")
        if not isinstance(fp, dict) or not fp.get("qubits"):
            raise LoadError(
                f"{source}: QubitExplicitnessViolation: factory {fid!r} must "
                f"declare an explicit fixed footprint "
                f"(footprint: {{qubits: [<zone>[a:b], ...]}}); a factory occupies "
                f"exact qubits, never a fungible charge. "
                f"('physical_qubits' remains allowed as a statistics annotation.)")
        factories.append({"id": fid, **spec})

    token_initial_inventory: dict[str, int] = {}
    token_ttl: dict[str, int] = {}
    for kind, spec in _require_mapping(raw.get("tokens"), "'tokens'", source).items():
        if not isinstance(spec, dict):
            raise LoadError(f"{source}: tokens.{kind} must be a mapping")
        if "initial_inventory" in spec:
            token_initial_inventory[kind] = spec["initial_inventory"]
        if "ttl_us" in spec:
            token_ttl[kind] = spec["ttl_us"]

    doc = {
        "name": raw.get("name", "backend"),
        "description": raw.get("description", ""),
        "unit": raw.get("unit", {"time": "us"}),
        "resources": resources,
        "zones": zones,
        "services": services,
        "factories": factories,
        "gates": gates,
        "throughput_caps": raw.get("throughput_caps", []) or [],
        "max_parallel_gates": raw.get("max_parallel_gates"),
        "qubit_touching_kinds": raw.get("qubit_touching_kinds", []) or [],
        "token_initial_inventory": token_initial_inventory,
        "token_buffer_capacity": token_buffer_capacity,
        "token_ttl_us": token_ttl,
        "default_latencies_us": default_latencies,
    }
    try:
        cfg = BackendConfig.model_validate(doc)
    except ValidationError as exc:
        raise LoadError(_validation_message(exc, "backend config", source)) from exc
    _validate_footprints(cfg, source)
    return cfg


def _validate_footprints(cfg: BackendConfig, source: str) -> None:
    """Every footprint reference must resolve to declared zones/resources."""
    zone_map = cfg.zone_map()
    resources = cfg.resource_map()
    for f in cfg.factories:
        if f.footprint is None:
            continue
        groups = (("qubits", f.footprint.qubits),
                  ("output_ports", f.footprint.output_ports),
                  ("buffer", f.footprint.buffer))
        for group, refs in groups:
            for ref in refs:
                parsed = parse_qubit_ref(ref)
                if parsed is not None and parsed[0] in zone_map:
                    z = zone_map[parsed[0]]
                    bad = [i for i in parsed[1] if not 0 <= i < z.count]
                    if bad:
                        raise LoadError(
                            f"{source}: factory {f.id}: footprint.{group} {ref!r}: "
                            f"index {bad} out of range (zone {z.id!r} has count "
                            f"{z.count}).")
                elif ref not in resources:
                    raise LoadError(
                        f"{source}: factory {f.id}: footprint.{group} entry {ref!r} "
                        f"names no declared zone or resource.")


def load_backend(path: Union[str, Path]) -> BackendConfig:
    return backend_from_obj(_load_raw(path), str(path))


# --------------------------------------------------------------------------
# Program
# --------------------------------------------------------------------------


def _qubit_ids_for_ref(ref: str, backend: BackendConfig | None, op_label: str,
                       source: str) -> list[str]:
    """Expand one explicit qubit reference, validating against the backend's
    zones when available.  Raises LoadError on malformed/out-of-range refs."""
    parsed = parse_qubit_ref(ref)
    if parsed is None:
        raise LoadError(
            f"{source}: op {op_label}: {ref!r} is not an explicit qubit reference "
            f"(expected zone[i], zone[a:b] (half-open) or zone[i,j,k]).")
    zone, indices = parsed
    if backend is not None:
        zmap = backend.zone_map()
        if zone not in zmap:
            raise LoadError(f"{source}: op {op_label}: unknown zone {zone!r} "
                            f"in qubit reference {ref!r}.")
        z = zmap[zone]
        bad = [i for i in indices if not 0 <= i < z.count]
        if bad:
            raise LoadError(f"{source}: op {op_label}: qubit index {bad} out of "
                            f"range in {ref!r} (zone {zone!r} has count {z.count}).")
    return [f"{zone}[{i}]" for i in indices]


def _expand_qubits_field(value: Any, backend: BackendConfig | None, op_label: str,
                         source: str) -> tuple[list[dict], dict[str, list[str]] | None]:
    """Lower the ``qubits:`` op field to exclusive capacity-1 resource uses.

    Accepts a flat list (``qubits: [data[3], anc[0:5]]``) or a role mapping
    (``qubits: {data: [data[3], data[4]], syndrome: [syndrome[7]]}``).
    Returns (rich use dicts, role mapping or None).
    """
    if value is None:
        return [], None
    if isinstance(value, list):
        groups: dict[str, Any] = {"qubits": value}
        keep_roles = False
    elif isinstance(value, dict):
        groups = value
        keep_roles = True
    else:
        raise LoadError(f"{source}: op {op_label}: 'qubits' must be a list of "
                        f"qubit references or a mapping of role -> list.")
    uses: list[dict] = []
    roles: dict[str, list[str]] = {}
    seen: set[str] = set()
    for role, refs in groups.items():
        if isinstance(refs, str):
            refs = [refs]
        if not isinstance(refs, list):
            raise LoadError(f"{source}: op {op_label}: qubits.{role} must be a "
                            f"list of qubit references.")
        ids: list[str] = []
        for ref in refs:
            for qid in _qubit_ids_for_ref(ref, backend, op_label, source):
                if qid in seen:
                    raise LoadError(f"{source}: op {op_label}: qubit {qid!r} is "
                                    f"listed twice.")
                seen.add(qid)
                ids.append(qid)
                uses.append({"resource": qid, "mode": "exclusive"})
        roles[role] = ids
    return uses, (roles if keep_roles else None)


def _normalize_uses(uses: Any, backend: BackendConfig | None, op_label: str,
                    source: str) -> tuple[list[dict], list[dict]]:
    """Returns (resource_uses, service_jobs) from either syntax form.

    Qubits are never fungible: a bare zone name in ``uses`` is invalid, and
    zone-indexed references lower to exclusive capacity-1 uses.
    """
    if uses is None:
        return [], []
    service_ids = set(backend.service_map()) if backend else set()
    zone_ids = set(backend.zone_map()) if backend else set()
    resource_uses: list[dict] = []
    service_jobs: list[dict] = []

    def reject_bare_zone(name: str) -> None:
        if name in zone_ids:
            raise LoadError(
                f"{source}: QubitExplicitnessViolation: op {op_label} uses zone "
                f"{name!r} anonymously; qubits are never fungible in an executable "
                f"schedule. Name explicit qubits, e.g. {name}[3] or {name}[0:4].")

    def is_zone_ref(name: str) -> bool:
        parsed = parse_qubit_ref(name)
        return parsed is not None and (backend is None or parsed[0] in zone_ids)

    if isinstance(uses, dict):
        # simple form: resource -> amount; service names submit jobs
        for name, amount in uses.items():
            reject_bare_zone(name)
            if not isinstance(amount, int) or amount < 1:
                raise LoadError(f"{source}: op {op_label}: uses.{name} must be a "
                                f"positive integer amount, got {amount!r}")
            if is_zone_ref(name):
                if amount != 1:
                    raise LoadError(
                        f"{source}: op {op_label}: uses.{name}: qubits are held "
                        f"exclusively, one at a time; use a range like "
                        f"{name.split('[')[0]}[a:b] instead of an amount.")
                for qid in _qubit_ids_for_ref(name, backend, op_label, source):
                    resource_uses.append({"resource": qid, "mode": "exclusive"})
            elif name in service_ids:
                service_jobs.append({"service": name, "count": amount})
            else:
                resource_uses.append({"resource": name, "amount": amount})
    elif isinstance(uses, list):
        # rich form: list of {resource, mode, amount, start_us, end_us}
        for entry in uses:
            if not isinstance(entry, dict) or "resource" not in entry:
                raise LoadError(f"{source}: op {op_label}: rich 'uses' entries must "
                                f"be mappings with a 'resource' key, got {entry!r}")
            name = entry["resource"]
            reject_bare_zone(name)
            if name in service_ids:
                raise LoadError(f"{source}: op {op_label}: {name!r} is a "
                                f"service; submit jobs via the mapping form of 'uses' "
                                f"or the 'service' field, not a rich resource use.")
            if is_zone_ref(name):
                if entry.get("mode", "exclusive") != "exclusive":
                    raise LoadError(
                        f"{source}: QubitExplicitnessViolation: op {op_label}: "
                        f"qubit use {name!r} declares mode "
                        f"{entry['mode']!r}; qubits are always held exclusively.")
                if entry.get("amount", 1) != 1:
                    raise LoadError(f"{source}: op {op_label}: qubit use "
                                    f"{name!r} must have amount 1.")
                for qid in _qubit_ids_for_ref(name, backend, op_label, source):
                    expanded = dict(entry)
                    expanded["resource"] = qid
                    expanded["mode"] = "exclusive"
                    resource_uses.append(expanded)
            else:
                resource_uses.append(entry)
    else:
        raise LoadError(f"{source}: op {op_label}: 'uses' must be a mapping or a list")
    return resource_uses, service_jobs


def _normalize_tokens(value: Any, what: str, op_label: str, source: str) -> list[dict]:
    """Accepts ``TState``, ``[TState, {kind: X, count: 2}]`` etc."""
    if value is None:
        return []
    if isinstance(value, (str, dict)):
        value = [value]
    if not isinstance(value, list):
        raise LoadError(f"{source}: op {op_label}: {what!r} must be a token kind, "
                        f"a mapping, or a list of those")
    return [{"kind": v} if isinstance(v, str) else v for v in value]


def _expand_repeat(entry: dict, op_label: str, source: str) -> list[dict]:
    """Expand ``repeat: {every_us, until_us}`` into concrete instances."""
    repeat = entry.pop("repeat", None)
    if repeat is None:
        return [entry]
    if not isinstance(repeat, dict) or "every_us" not in repeat or "until_us" not in repeat:
        raise LoadError(f"{source}: op {op_label}: 'repeat' needs every_us and until_us")
    every = repeat["every_us"]
    until = repeat["until_us"]
    if not isinstance(every, int) or every < 1:
        raise LoadError(f"{source}: op {op_label}: repeat.every_us must be >= 1")
    if not isinstance(until, int):
        raise LoadError(f"{source}: op {op_label}: repeat.until_us must be an "
                        f"integer (got {until!r})")
    base_at = entry.get("at_us", 0)
    if not isinstance(base_at, int):
        raise LoadError(f"{source}: op {op_label}: at_us must be an integer "
                        f"(got {base_at!r})")
    instances = []
    k = 0
    while base_at + k * every <= until:
        inst = dict(entry)
        inst["at_us"] = base_at + k * every
        inst["id"] = f"{entry['id']}@{k}"
        instances.append(inst)
        k += 1
    if not instances:
        raise LoadError(f"{source}: op {op_label}: repeat produces no instances "
                        f"(until_us={until} < at_us={base_at})")
    return instances


def program_from_obj(raw: Any, backend: BackendConfig | None = None,
                     source: str = "program") -> Program:
    """Compile the friendly program syntax into the internal :class:`Program`.

    ``backend`` is needed to tell services apart from resources in the
    mapping form of ``uses``; pass the backend the program will run against.
    """
    if not isinstance(raw, dict):
        raise LoadError(f"{source} must be a mapping at top level")
    _check_unit(raw, source)
    _reject_legacy_time_keys(raw.get("ops"), source)
    touching = set(backend.qubit_touching_kinds) if backend else set()
    zone_ids = set(backend.zone_map()) if backend else set()
    gate_table = backend.gate_map() if backend else {}

    name = raw.get("program") or raw.get("name") or "program"
    ops_raw = raw.get("ops", []) or []
    if not isinstance(ops_raw, list):
        raise LoadError(f"{source}: 'ops' must be a list")

    kind_counters: dict[str, int] = {}
    normalized: list[dict] = []
    for i, entry in enumerate(ops_raw):
        if not isinstance(entry, dict):
            raise LoadError(f"{source}: ops[{i}] must be a mapping")
        entry = dict(entry)
        kind = entry.pop("do", None) or entry.pop("kind", None)
        if not kind:
            raise LoadError(f"{source}: ops[{i}] needs a 'do' (or 'kind') field")
        entry.pop("kind", None)  # if both were given, 'do' wins
        n = kind_counters.get(kind, 0)
        kind_counters[kind] = n + 1
        op_id = entry.pop("id", None) or f"{kind}_{n}"
        if "at_us" not in entry:
            raise LoadError(f"{source}: op {op_id}: missing 'at_us' start time")

        metadata = dict(_require_mapping(entry.pop("metadata", None),
                                         f"op {op_id}: 'metadata'", source))
        for key in list(entry.keys()):
            if key not in _OP_KNOWN_KEYS:
                metadata[key] = entry.pop(key)

        uses_res, uses_jobs = _normalize_uses(entry.pop("uses", None), backend,
                                              op_id, source)
        qubit_uses, qubit_roles = _expand_qubits_field(entry.pop("qubits", None),
                                                       backend, op_id, source)
        # 'qubits:' entries must not double-book what 'uses' already holds
        listed = {u["resource"] for u in uses_res}
        for u in qubit_uses:
            if u["resource"] in listed:
                raise LoadError(f"{source}: op {op_id}: qubit {u['resource']!r} "
                                f"appears in both 'qubits' and 'uses'.")
        uses_res = [*uses_res, *qubit_uses]
        if qubit_roles is not None:
            metadata["qubit_roles"] = qubit_roles

        if kind in touching:
            def _is_zone_qubit(rid: str) -> bool:
                parsed = parse_qubit_ref(rid)
                return parsed is not None and (not zone_ids or parsed[0] in zone_ids)
            if not any(_is_zone_qubit(u["resource"]) for u in uses_res):
                raise LoadError(
                    f"{source}: QubitExplicitnessViolation: op {op_id} "
                    f"(do: {kind}) touches qubits but does not list explicit "
                    f"qubit IDs. Fungible qubit-pool requests are not allowed in "
                    f"executable schedules. Add e.g. "
                    f"qubits: [data[3], syndrome[7]].")

        consumes = _normalize_tokens(
            entry.pop("consume", None) or entry.pop("consumes", None),
            "consume", op_id, source)
        produces = _normalize_tokens(
            entry.pop("produce", None) or entry.pop("produces", None),
            "produce", op_id, source)
        service = entry.pop("service", None)
        if service is None:
            service = []
        elif isinstance(service, dict):
            service = [service]
        service = [*service, *uses_jobs]

        factory = entry.pop("factory", None)
        if kind == "start_factory":
            if not factory:
                raise LoadError(f"{source}: op {op_id}: start_factory needs 'factory'")
            metadata["factory"] = factory
        elif factory is not None:
            metadata["factory"] = factory

        duration = entry.pop("duration_us", None)
        gate = gate_table.get(kind)
        if gate is not None:
            if duration is None:
                duration = gate.duration_us   # hardware fact fills it in
            elif duration != gate.duration_us:
                raise LoadError(
                    f"{source}: op {op_id}: duration_us {duration} contradicts "
                    f"the hardware gate table ({kind} takes "
                    f"{gate.duration_us}us); omit duration_us or set it to "
                    f"{gate.duration_us}.")
        elif duration is None:
            duration = 1

        doc = {
            "id": op_id,
            "kind": kind,
            "at_us": entry.pop("at_us"),
            "duration_us": duration,
            "deps": entry.pop("deps", []) or [],
            "uses": uses_res,
            "consumes": consumes,
            "produces": produces,
            "service": service,
            "metadata": metadata,
        }
        leftovers = set(entry) - {"repeat"}
        if leftovers:
            raise LoadError(f"{source}: op {op_id}: unhandled keys {sorted(leftovers)}")
        doc["repeat"] = entry.get("repeat")
        if doc["repeat"] is None:
            doc.pop("repeat")
        normalized.extend(_expand_repeat(doc, op_id, source))

    try:
        return Program.model_validate({
            "name": name,
            "description": raw.get("description", ""),
            "ops": normalized,
        })
    except ValidationError as exc:
        raise LoadError(_validation_message(exc, "program", source)) from exc


def load_program(path: Union[str, Path],
                 backend: BackendConfig | None = None) -> Program:
    path = Path(path)
    text = _read_text_or_raise(path)
    from .device_program import (DeviceProgramError, is_device_program,
                                 load_device_program)
    if path.suffix.lower() == ".dp" or is_device_program(text):
        if backend is None:
            raise LoadError(f"{path}: DEVICE-PROGRAM files need the backend "
                            f"(site map + gate table) to load")
        try:
            return load_device_program(text, backend, str(path))
        except DeviceProgramError as exc:
            raise LoadError(str(exc)) from exc
    return program_from_obj(_load_raw(path), backend, str(path))


def parse_text(text: str) -> Any:
    """Parse a YAML or JSON string into a plain object."""
    try:
        return yaml.safe_load(text)
    except yaml.YAMLError as exc:
        raise LoadError(f"could not parse input text: {exc}") from exc
