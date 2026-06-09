#!/usr/bin/env python3
"""Render an OpenQASM 2.0 file to a circuit-diagram PNG using standard Qiskit.

Usage:
    python scripts/draw_qasm.py <input.qasm> <output.png> [title]

The QASM is produced by FormalRV's verified `Gadget.toQASMNative` emitter
(native CX/CCX/X basis, which draws cleanly). This is the standard Qiskit
matplotlib drawer (`QuantumCircuit.draw('mpl')`).
"""
import sys


def main() -> int:
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    qasm_path, png_path = sys.argv[1], sys.argv[2]
    title = sys.argv[3] if len(sys.argv) > 3 else None

    from qiskit import qasm2

    with open(qasm_path, "r", encoding="utf-8") as f:
        src = f.read()
    qc = qasm2.loads(src, custom_instructions=qasm2.LEGACY_CUSTOM_INSTRUCTIONS)

    fig = qc.draw(output="mpl", fold=-1, idle_wires=True)
    if title:
        fig.suptitle(title)
    fig.savefig(png_path, dpi=150, bbox_inches="tight")
    print(f"wrote {png_path}  ({qc.num_qubits} qubits, {len(qc.data)} ops)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
