#!/usr/bin/env python3
"""Render an OpenQASM 2.0 file to a circuit-diagram PNG using standard Qiskit,
with optional named wires and an INPUT/OUTPUT encoding legend.

Usage:
    python scripts/draw_qasm.py <input.qasm> <output.png> [iospec.json]

iospec.json (all optional):
{
  "title":  "Cuccaro 2-bit adder (a+b mod 4)",
  "wires":  ["c_in", "b0", "a0", "b1", "a1"],   # per-qubit names (input encoding)
  "input":  ["c_in = 0", "b1b0 = b (target)", "a1a0 = a (read)"],
  "output": ["c_in = 0 (restored)", "b1b0 = (a+b) mod 4", "a1a0 = a (restored)"]
}
"""
import sys
import json


def main() -> int:
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    qasm_path, png_path = sys.argv[1], sys.argv[2]
    spec = json.load(open(sys.argv[3], "r", encoding="utf-8")) if len(sys.argv) > 3 else {}

    from qiskit import qasm2, QuantumCircuit, QuantumRegister

    qc = qasm2.loads(open(qasm_path, "r", encoding="utf-8").read(),
                     custom_instructions=qasm2.LEGACY_CUSTOM_INSTRUCTIONS)

    wires = spec.get("wires")
    if wires:
        # Re-label wires with their encoding role via single-qubit named registers.
        named = QuantumCircuit(*[QuantumRegister(1, name=w) for w in wires])
        named.compose(qc, qubits=list(range(qc.num_qubits)), inplace=True)
        qc = named

    fs = spec.get("fontsize", 14)
    fig = qc.draw(output="mpl", fold=spec.get("fold", -1),
                  idle_wires=spec.get("idle_wires", True),
                  style={"fontsize": fs, "subfontsize": max(8, fs - 2)})
    if spec.get("title"):
        fig.suptitle(spec["title"], fontsize=fs)
    legend = []
    if spec.get("input"):
        legend.append("INPUT:   " + "    ".join(spec["input"]))
    if spec.get("output"):
        legend.append("OUTPUT:  " + "    ".join(spec["output"]))
    if legend:
        fig.text(0.01, 0.01, "\n".join(legend), fontsize=max(9, fs - 3),
                 family="monospace", va="bottom", ha="left")
    fig.savefig(png_path, dpi=150, bbox_inches="tight")
    print(f"wrote {png_path}  ({qc.num_qubits} qubits, {len(qc.data)} ops)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
