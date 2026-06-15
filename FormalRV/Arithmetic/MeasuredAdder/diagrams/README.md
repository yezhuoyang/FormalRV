# MeasuredAdder diagrams

The measured Gidney adder is an **`EGate`** (the measurement-augmented IR): each
carry-AND uncompute in the reverse sweep is a **mid-circuit measurement `mz`**, not
a unitary.  The repo's `Codegen.toQasm` emitter renders the unitary `Gate` IR and
has no OpenQASM symbol for the `mz` reset channel, so a faithful QASM render of the
*measured* reverse cannot be produced from this IR.

The authoritative circuit picture therefore lives as an **ASCII diagram in the
parent `README.md`** (`## Circuit diagram`): the forward CCX carry cascade, the
T-free final-CX sum stamp, and the measured reverse where each per-step
`CCX(read i, target i, carry i)` is replaced by a measurement `mz(carry i)`.

If you want a *unitary* picture for intuition, the **reversible** sibling adder
`gidney_adder_full_faithful_no_measurement` (identical except the reverse uses CCX
instead of `mz`) is pure `Gate` and renders through `Codegen.toQasm` like the other
adders — but that is the `2n`-Toffoli version, not this measured `n`-Toffoli one.
