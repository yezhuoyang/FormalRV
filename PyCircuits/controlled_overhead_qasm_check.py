"""
Qiskit justification of the CONTROL-OVERHEAD count inputs (FormalRV.Shor.ControlledModExpCount).

The verified Shor mod-exp is `controlled_powers` of the oracle, and the proved control formula
  ucApp2 (control q (toUCom g)) = 2·(numI+numX+9·numCCX) + 6·(numCX+6·numCCX)
is driven by the oracle's Toffoli-DECOMPOSITION CNOT count `numCX + 6·numCCX` (each Gate.CCX
decomposes to the 7-T Toffoli = 6 CNOT).  Here we confirm, by decomposing the EMITTED oracle
QASM's Toffolis in Qiskit, that the decomposed CNOT count equals `numCX + 6·numCCX` — i.e. the
key input to the proved control formula matches the actual circuit.
"""
import sys, os
try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass
from qiskit import QuantumCircuit, transpile

QDIR = os.path.join(os.path.dirname(__file__), "qasm")
results = []
def check(name, ok, detail):
    results.append((name, ok)); print(f"[{'PASS' if ok else '**FAIL**'}] {name}\n        {detail}")

# (file, Lean numCX, numCCX)  — numX=0 for these; identities (Gate.I) are dropped by the emitter.
CASES = [
    ("modmult_const_2_15_7",  76, 32),
    ("modmult_const_3_21_5", 165, 72),
    ("modmult_MCP_2_15_7_13", 168, 64),
]

for name, numCX, numCCX in CASES:
    qc = QuantumCircuit.from_qasm_file(os.path.join(QDIR, f"{name}.qasm"))
    # decompose every ccx into its standard 7-T Toffoli (6 CNOT) form
    dec = transpile(qc, basis_gates=["cx", "h", "t", "tdg", "x"], optimization_level=0)
    n_cx = dec.count_ops().get("cx", 0)
    expected = numCX + 6 * numCCX
    check(f"{name}: decomposed CNOT count == numCX + 6·numCCX", n_cx == expected,
          f"Qiskit cx after Toffoli-decompose = {n_cx} | Lean numCX+6·numCCX = "
          f"{numCX}+6·{numCCX} = {expected}")

print("\n" + "=" * 70)
n_pass = sum(1 for _, p in results if p)
print(f"SUMMARY: {n_pass}/{len(results)} checks passed.")
print("THE CONTROL-FORMULA INPUT (decomposed-Toffoli CNOT count) MATCHES THE ACTUAL CIRCUIT."
      if n_pass == len(results) else "SOME CHECKS FAILED.")
