#!/usr/bin/env python3
"""Test the EMITTED babbush unary-iteration QROM by running it in Qiskit.

Loads C:/tmp/qasm_demo/babbush_qrom_w2.qasm (emitted by WindowedEmitDemo.lean),
prepares each w=2 address on the control+address qubits, runs the emitted circuit
(including its mid-circuit measurement-uncompute), and checks the output register
holds T[a]=a.  This is an independent, external check that the emitted code — not
just the Lean model — computes the lookup.

Run:  python FormalRV/Codegen/verify_emitted_qrom.py
"""
from qiskit import QuantumCircuit, transpile

try:
    from qiskit_aer import AerSimulator
    sim = AerSimulator()
except Exception:
    from qiskit.providers.basic_provider import BasicSimulator
    sim = BasicSimulator()

PATH = "C:/tmp/qasm_demo/babbush_qrom_w2.qasm"
qrom = QuantumCircuit.from_qasm_file(PATH)
print(f"Loaded emitted QROM: {qrom.num_qubits} qubits, {qrom.size()} ops")
# layout: ctrl=q[0], address bits q[1] (bit0), q[2] (bit1); output bits q[5],q[6] (T<=3)

ok = True
for a in range(4):
    qc = QuantumCircuit(7, 7)
    qc.x(0)                      # control = 1
    if a & 1: qc.x(1)            # address bit 0
    if a & 2: qc.x(2)            # address bit 1
    qc.compose(qrom, inplace=True)
    qc.measure([5, 6], [5, 6])   # read output (bit 2 always 0 for T = id <= 3)
    counts = sim.run(transpile(qc, sim), shots=64).result().get_counts()
    vals = {((int(k, 2) >> 5) & 0b11) for k in counts}
    got = vals.pop() if len(vals) == 1 else vals
    status = "OK" if got == a else "FAIL"
    if got != a:
        ok = False
    print(f"  address a={a}: emitted QROM output = {got}   [{status}]")

print("RESULT:", "ALL PASS - emitted code computes T[a]" if ok else "FAIL")
raise SystemExit(0 if ok else 1)
