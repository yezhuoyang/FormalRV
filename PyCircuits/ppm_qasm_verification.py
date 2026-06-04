"""
Numerical verification (Qiskit) of the PPM->QASM emitter
(FormalRV.PPM.PPMToQASM).

We take the OpenQASM 3 emitted by the Lean `toQASM` off the verified gadgets,
parse it with qiskit.qasm3, simulate it (density-matrix, with mid-circuit
measurement + classically-controlled feed-forward), and confirm:

  * the T-gadget QASM implements the T gate on the data qubit, and
  * the CCZ-gadget QASM implements the CCZ gate on the 3 data qubits,

for arbitrary input states — i.e. the data reduced density matrix equals
U|psi><psi|U^dag, DETERMINISTICALLY across all measurement outcomes (the
feed-forward S / CZ corrections remove the branch dependence).

Note: the CCZ check exercises ALL 8 measurement outcomes incl. their CZ
corrections — so it numerically confirms the 7 corrected branches that the
Lean proof (CCZGadgetTeleport) left to future work (it proved the 000 branch).
"""
import sys
try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass
import numpy as np
from qiskit import qasm3, QuantumCircuit, transpile
from qiskit.quantum_info import random_statevector
from qiskit_aer import AerSimulator

SIM = AerSimulator(method="density_matrix")

TOL = 1e-9
results = []

# ---- the EXACT OpenQASM 3 emitted by Lean FormalRV.PPM.PPMToQASM ----
T_QASM = """OPENQASM 3.0;
include "stdgates.inc";
qubit[2] q;
bit[1] c;
h q[1];
t q[1];
cx q[0], q[1];
c[0] = measure q[1];
if (c[0] == true) s q[0];
"""

CCZ_QASM = """OPENQASM 3.0;
include "stdgates.inc";
qubit[6] q;
bit[3] c;
h q[3];
h q[4];
h q[5];
h q[5]; ccx q[3], q[4], q[5]; h q[5];
cx q[0], q[3];
cx q[1], q[4];
cx q[2], q[5];
c[0] = measure q[3];
c[1] = measure q[4];
c[2] = measure q[5];
if (c[0] == true) cz q[1], q[2];
if (c[1] == true) cz q[0], q[2];
if (c[2] == true) cz q[0], q[1];
if (c[0] == true) if (c[1] == true) z q[2];
if (c[0] == true) if (c[2] == true) z q[1];
if (c[1] == true) if (c[2] == true) z q[0];
"""

T_MAT = np.array([[1, 0], [0, np.exp(1j * np.pi / 4)]], dtype=complex)
CCZ_MAT = np.diag([1, 1, 1, 1, 1, 1, 1, -1]).astype(complex)


def check(name, ok, detail):
    results.append((name, ok))
    print(f"[{'PASS' if ok else '**FAIL**'}] {name}\n        {detail}")


def expected_dm(U, psi):
    out = U @ psi
    return np.outer(out, out.conj())


def run_gadget_check(qasm_str, U, n_data, n_total, n_inputs=6):
    """Reduced DM on the data qubits after running the gadget QASM on the Aer
    density-matrix simulator (averages over measurement outcomes, executes the
    classically-controlled feed-forward). Compared to U|psi><psi|U^dag."""
    qc = qasm3.loads(qasm_str)
    data = list(range(n_data))
    worst = 0.0
    states = [random_statevector(2 ** n_data, seed=s).data for s in range(n_inputs)]
    basis0 = np.zeros(2 ** n_data, dtype=complex); basis0[0] = 1.0
    states.append(basis0)
    for psi in states:
        prep = QuantumCircuit(n_total, qc.num_clbits)
        prep.prepare_state(psi, data)        # StatePreparation (unitary; no reset)
        full = prep.compose(qc)
        full.save_density_matrix(qubits=data)
        tfull = transpile(full, SIM)          # decompose StatePreparation to basis gates
        res = SIM.run(tfull).result()
        dm = np.asarray(res.data(0)["density_matrix"].data)
        worst = max(worst, float(np.max(np.abs(dm - expected_dm(U, psi)))))
    return worst


print("=== (1) parse the emitted OpenQASM 3 ===")
try:
    tqc = qasm3.loads(T_QASM)
    cqc = qasm3.loads(CCZ_QASM)
    check("QASM parses (qiskit.qasm3.loads)", True,
          f"T-gadget: {tqc.num_qubits}q/{tqc.num_clbits}c; CCZ-gadget: {cqc.num_qubits}q/{cqc.num_clbits}c")
except Exception as e:
    check("QASM parses (qiskit.qasm3.loads)", False, f"parse error: {e}")
    raise

print("\n=== (2) T-gadget QASM implements T on the data qubit ===")
wT = run_gadget_check(T_QASM, T_MAT, n_data=1, n_total=2)
check("emitted T-gadget == T  (data reduced DM, all outcomes)", wT < TOL,
      f"max |rho_data - T|psi><psi|T^dag| over random+basis inputs = {wT:.2e}")

print("\n=== (3) CCZ-gadget QASM implements CCZ on the 3 data qubits ===")
print("    (exercises ALL 8 outcomes incl. the CZ feed-forward corrections —")
print("     numerically confirms the 7 corrected branches Lean left to future work)")
wC = run_gadget_check(CCZ_QASM, CCZ_MAT, n_data=3, n_total=6)
check("emitted CCZ-gadget == CCZ  (data reduced DM, all outcomes)", wC < TOL,
      f"max |rho_data - CCZ|psi><psi|CCZ^dag| over random+basis inputs = {wC:.2e}")

print("\n" + "=" * 70)
n_pass = sum(1 for _, p in results if p)
print(f"SUMMARY: {n_pass}/{len(results)} checks passed.")
print("EMITTED PPM QASM SIMULATES TO THE CORRECT LOGICAL GATES."
      if n_pass == len(results) else "SOME CHECKS FAILED.")
