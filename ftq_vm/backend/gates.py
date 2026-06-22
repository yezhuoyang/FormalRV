"""Gate-table lowering.

Physical (and logical) gate-level operations take hardware-specific time and
contend for finite control electronics.  The backend's ``gates:`` table
declares those facts; this module *lowers* every op whose kind matches a
gate onto the generic core, so the existing checkers do all the work:

* **honest durations** -- the op's duration must equal the gate's
  ``duration_us`` (the loader fills it in when omitted; a schedule claiming
  ``CNOT`` takes 5us on 1000us hardware is reported, not believed);
* **exact arity** -- a gate with ``qubits: 2`` must name exactly 2 explicit
  qubits;
* **control contention** -- the gate's ``uses`` (readout lines, AWG
  channels, ...) are charged for the gate's duration, and the parallelism
  caps become capacity-1 uses of the ``gate.<kind>.parallel`` /
  ``gates.parallel`` auto-resources, so oversubscription surfaces as
  ordinary ``CapacityExceeded`` errors naming the colliding ops.
"""

from __future__ import annotations

from .models import (
    GLOBAL_GATE_CHANNELS,
    BackendConfig,
    Op,
    Program,
    ResourceUse,
    TimeInterval,
    VMError,
    VMErrorKind,
    parse_qubit_ref,
)


def lower_gates(backend: BackendConfig, program: Program
                ) -> tuple[Program, list[VMError]]:
    """Attach gate semantics to every op whose kind is in the gate table.

    Returns the lowered program and the validity errors found (wrong
    duration, wrong qubit count).  Ops with errors still get their control
    uses attached so the rest of the schedule is checked realistically.
    """
    gate_table = backend.gate_map()
    if not gate_table:
        return program, []
    zone_ids = set(backend.zone_map())
    errors: list[VMError] = []
    lowered: list[Op] = []

    for op in program.ops:
        gate = gate_table.get(op.kind)
        if gate is None:
            lowered.append(op)
            continue

        if op.duration_us != gate.duration_us:
            errors.append(VMError(
                kind=VMErrorKind.InvalidInterval, time_us=op.at_us,
                op_ids=[op.id],
                interval=TimeInterval(start_us=op.at_us, end_us=op.end_us),
                message=(f"op={op.id} declares duration {op.duration_us}us, but "
                         f"{op.kind} takes {gate.duration_us}us on this hardware; "
                         f"gate times are hardware facts, not schedule choices."),
                suggestion=f"Omit duration_us (the loader fills in "
                           f"{gate.duration_us}) or set it to {gate.duration_us}.",
            ))

        if gate.qubits is not None:
            named = {u.resource for u in op.uses
                     if (ref := parse_qubit_ref(u.resource)) is not None
                     and ref[0] in zone_ids}
            if len(named) != gate.qubits:
                errors.append(VMError(
                    kind=VMErrorKind.QubitExplicitnessViolation, time_us=op.at_us,
                    op_ids=[op.id],
                    message=(f"op={op.id}: {op.kind} acts on exactly "
                             f"{gate.qubits} qubit(s); the op names {len(named)} "
                             f"({', '.join(sorted(named)) or 'none'})."),
                    suggestion=f"List exactly {gate.qubits} explicit qubit(s) "
                               f"under 'qubits:'.",
                ))

        extra = [ResourceUse(resource=rid, amount=amount)
                 for rid, amount in gate.uses.items()]
        if gate.max_parallel is not None:
            extra.append(ResourceUse(resource=gate.parallel_resource()))
        if backend.max_parallel_gates is not None:
            extra.append(ResourceUse(resource=GLOBAL_GATE_CHANNELS))
        lowered.append(op.model_copy(update={"uses": [*op.uses, *extra]})
                       if extra else op)

    return Program.model_construct(name=program.name,
                                   description=program.description,
                                   ops=lowered), errors
