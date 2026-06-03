"""
Qiskit cross-check that the EMITTED QASM of the verified Gate IR circuits has exactly the
gate counts Lean computed/proved.  The .qasm files are produced by
`lake env lean --run scripts/EmitQASM.lean` (which also prints the Lean counts).

For each circuit we confirm, by loading the QASM into Qiskit and counting ops:
  * #ccx (Toffolis) == Lean numCCX, and == the proved closed form
        const_gate: 8·bits²   MCP gate: 16·bits²
  * 7·#ccx == Lean tcount (the proved 56·bits² / 112·bits²)
  * #cx, #x, total gate count == Lean numCX / numX / gcount
This justifies the counting empirically: the real, Qiskit-loadable circuit has exactly the
counted gates — the Lean number is not a bookkeeping artefact.
"""
import sys, os
try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass
from qiskit import QuantumCircuit

QDIR = os.path.join(os.path.dirname(__file__), "qasm")
results = []

def check(name, ok, detail):
    results.append((name, ok))
    print(f"[{'PASS' if ok else '**FAIL**'}] {name}\n        {detail}")

# (file, Lean numCCX, numCX, numX, gcount, tcount, formula-description)
CASES = [
    ("toffoli",               1,   0, 0,   1,   7, "bare Toffoli: 1 ccx, tcount 7"),
    ("modmult_const_2_15_7",  32,  76, 0, 108, 224, "const bits=2: 8·2²=32 ccx, 56·2²=224 T"),
    ("modmult_const_3_21_5",  72, 165, 0, 237, 504, "const bits=3: 8·3²=72 ccx, 56·3²=504 T"),
    ("modmult_MCP_2_15_7_13", 64, 168, 0, 232, 448, "MCP  bits=2: 16·2²=64 ccx, 112·2²=448 T"),
]

for name, ccx, cx, x, gc, tc, desc in CASES:
    qc = QuantumCircuit.from_qasm_file(os.path.join(QDIR, f"{name}.qasm"))
    ops = qc.count_ops()
    q_ccx, q_cx, q_x = ops.get("ccx", 0), ops.get("cx", 0), ops.get("x", 0)
    total = sum(ops.values())
    ok = (q_ccx == ccx and q_cx == cx and q_x == x and total == gc and 7 * q_ccx == tc)
    check(f"{name}: emitted QASM gate counts == Lean", ok,
          f"Qiskit ccx={q_ccx} cx={q_cx} x={q_x} total={total} | "
          f"Lean ccx={ccx} cx={cx} x={x} gcount={gc} | 7·ccx={7*q_ccx} vs tcount={tc}  [{desc}]")

# Confirm the closed-form Toffoli formulas directly from the Qiskit counts.
def ccx_of(name):
    return QuantumCircuit.from_qasm_file(os.path.join(QDIR, f"{name}.qasm")).count_ops().get("ccx", 0)

check("const_gate Toffoli count == 8·bits²  (bits=2 and bits=3)",
      ccx_of("modmult_const_2_15_7") == 8 * 2**2 and ccx_of("modmult_const_3_21_5") == 8 * 3**2,
      f"8·2²={8*4} vs {ccx_of('modmult_const_2_15_7')}; 8·3²={8*9} vs {ccx_of('modmult_const_3_21_5')}")
check("MCP oracle Toffoli count == 16·bits²  (= 2× const, in-place)",
      ccx_of("modmult_MCP_2_15_7_13") == 16 * 2**2,
      f"16·2²={16*4} vs {ccx_of('modmult_MCP_2_15_7_13')}; "
      f"and MCP({ccx_of('modmult_MCP_2_15_7_13')}) = 2·const({ccx_of('modmult_const_2_15_7')})")

print("\n" + "=" * 70)
n_pass = sum(1 for _, p in results if p)
print(f"SUMMARY: {n_pass}/{len(results)} checks passed.")
print("THE EMITTED VERIFIED CIRCUITS' GATE COUNTS MATCH THE LEAN-PROVED NUMBERS."
      if n_pass == len(results) else "SOME CHECKS FAILED.")
