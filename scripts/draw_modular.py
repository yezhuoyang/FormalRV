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
  "fontsize": 20,                       # optional, default 20
  "registers": [{"name": "x", "size": 3}, {"name": "anc", "size": 9}],
  "palette":  {"compute": "#82B366", ...},   # optional kind -> hex fill
  "blocks":   [{"label": "encode", "kind": "encode", "qubits": [0,1,2],
                "qasm": "adder.qasm"}],       # qasm => real to_gate box (decomposable)
  "input":  ["x = multiplier", ...],
  "output": ["x = a*x mod N", ...]
}
Each block's "kind" picks its color (so different block types look different).
"""
import sys
import json

DEFAULT_PALETTE = {
    "encode": "#6C8EBF", "decode": "#6C8EBF",   # blue: data movement
    "compute": "#82B366",                         # green: build a*x
    "swap": "#D79B00",                            # orange: swap
    "uncompute": "#B85450",                       # red: clear old x
    "other": "#9673A6",                           # purple
}


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

    palette = dict(DEFAULT_PALETTE)
    palette.update(spec.get("palette", {}))
    displaycolor = {}

    for i, blk in enumerate(spec["blocks"]):
        qs = [qubits[j] for j in blk["qubits"]]
        kind = blk.get("kind", "other")
        # unique gate name per block (so each label shows) but colored by kind
        name = f"{kind}__{i}"
        if blk.get("qasm"):
            sub = qasm2.load(blk["qasm"],
                             custom_instructions=qasm2.LEGACY_CUSTOM_INSTRUCTIONS)
            g = sub.to_gate(label=blk["label"])
            g.name = name
            qc.append(g, qs)
        else:
            qc.append(QGate(name=name, num_qubits=len(qs), params=[], label=blk["label"]), qs)
        displaycolor[name] = (palette.get(kind, palette["other"]), "#ffffff")

    fs = spec.get("fontsize", 20)
    style = {"displaycolor": displaycolor, "fontsize": fs, "subfontsize": max(10, fs - 4)}
    fig = qc.draw(output="mpl", fold=-1, idle_wires=True, style=style)

    if spec.get("title"):
        fig.suptitle(spec["title"], fontsize=fs - 2)
    legend = []
    if spec.get("input") or spec.get("init"):
        legend.append("INPUT:   " + "    ".join(spec.get("input") or spec.get("init")))
    if spec.get("output"):
        legend.append("OUTPUT:  " + "    ".join(spec["output"]))
    if legend:
        fig.text(0.01, 0.005, "\n".join(legend), fontsize=max(11, fs - 6),
                 family="monospace", va="bottom", ha="left")
    fig.savefig(png, dpi=150, bbox_inches="tight")
    print(f"wrote {png}  ({qc.num_qubits} qubits, {len(spec['blocks'])} blocks)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
