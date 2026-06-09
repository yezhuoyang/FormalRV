#!/usr/bin/env python3
"""Render a MODULARIZED circuit schematic (functional blocks as boxes) from a
JSON spec, using standard Qiskit. For gadgets whose fully-decomposed circuit is
too large to draw flat, this emphasizes the key functional sub-gadgets and the
input encoding instead.

Usage:
    python scripts/draw_modular.py <spec.json> <output.png>

Spec format:
{
  "title": "...",
  "registers": [{"name": "x", "size": 3}, {"name": "anc", "size": 9}],
  "blocks":    [{"label": "encode", "qubits": [0,1,2]},
                {"label": "c-(+a mod N)", "qubits": [0,3,4,5]},
                {"label": "mod-add", "qubits": [3,4,5,6,7,8,9], "qasm": "adder.qasm"}],
  "init":      ["x = multiplier", "anc = |0>"]   # optional encoding notes
}
A block is either a label-only box, or (with "qasm") a REAL sub-circuit loaded
from emitted QASM and shown as a Qiskit `to_gate` box (decomposable). Qubit
indices are global, into the concatenated registers (top to bottom).
"""
import sys
import json


def main() -> int:
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    spec = json.load(open(sys.argv[1], "r", encoding="utf-8"))
    png = sys.argv[2]

    from qiskit import QuantumCircuit, QuantumRegister, qasm2
    from qiskit.circuit import Gate as QGate

    regs = [QuantumRegister(r["size"], r["name"]) for r in spec["registers"]]
    qc = QuantumCircuit(*regs)
    qubits = [q for reg in regs for q in reg]

    for blk in spec["blocks"]:
        qs = [qubits[i] for i in blk["qubits"]]
        if blk.get("qasm"):
            sub = qasm2.load(blk["qasm"],
                             custom_instructions=qasm2.LEGACY_CUSTOM_INSTRUCTIONS)
            qc.append(sub.to_gate(label=blk["label"]), qs)
        else:
            qc.append(QGate(name=blk["label"], num_qubits=len(qs), params=[]), qs)

    fig = qc.draw(output="mpl", fold=-1, idle_wires=True)
    if spec.get("title"):
        fig.suptitle(spec["title"], fontsize=11)
    legend = []
    if spec.get("input") or spec.get("init"):
        legend.append("INPUT:   " + "    ".join(spec.get("input") or spec.get("init")))
    if spec.get("output"):
        legend.append("OUTPUT:  " + "    ".join(spec["output"]))
    if legend:
        fig.text(0.01, 0.005, "\n".join(legend), fontsize=9, family="monospace",
                 va="bottom", ha="left")
    fig.savefig(png, dpi=150, bbox_inches="tight")
    print(f"wrote {png}  ({qc.num_qubits} qubits, {len(spec['blocks'])} blocks)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
