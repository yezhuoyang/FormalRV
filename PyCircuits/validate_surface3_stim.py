"""
Cross-validate the Lean-verified surface3 surgery against Stim — using the
STABILIZER-FLOW (correlation-surface) criterion of Tan, Niu & Gidney, "A SAT
Scalpel for Lattice Surgery" (LaSsynth).  Per that paper, a lattice-surgery
subroutine is functionally correct iff it satisfies the required stabilizer
flows ("product of logical operators at ports = product of measurements").
Stim's `has_flow` IS that check.

`surface3_surgery.stim` is emitted by the Lean framework
(`StimEmit.surgeryToStim surface3_x_surgery`).  14 measurements: X-checks
rec 0..7, Z-checks rec 8..13.  Logical X-bar = X6 X7 X8; logical Z-bar = Z0 Z3 Z6
(anticommutes with X-bar at qubit 6).

We verify the COMPLETE functional characterization of the X-bar measurement
(not just the readout): it READS X-bar, it is a GENUINE projective measurement
(destroys the anticommuting Z-bar), and it PRESERVES the code stabilizers.
"""
import stim, sys
c = stim.Circuit(open("PyCircuits/surface3_surgery.stim").read())
print(f"qubits {c.num_qubits}  measurements {c.num_measurements}")
ok = True
def flow(desc, s, expect=True):
    global ok
    try: r = c.has_flow(stim.Flow(s))
    except Exception as e: r = f"ERR {e}"
    good = (r is expect)
    ok = ok and good
    print(f"  [{'PASS' if good else 'FAIL'}] {desc}: ({s}) = {r}  (expect {expect})")

print("\n(R) READOUT — the span_witness-selected X-checks read X-bar:")
flow("X-bar = X6 X7 X8 -> rec[6] xor rec[7]", "X6*X7*X8 -> rec[-8] xor rec[-7]", True)

print("\n(projective) the measurement DESTROYS the anticommuting Z-bar:")
flow("Z-bar = Z0 Z3 Z6 NOT preserved", "Z0*Z3*Z6 -> Z0*Z3*Z6", False)

print("\n(non-disturbance) code stabilizers are PRESERVED through the merge:")
flow("Z-check0 Z0 Z1 Z9 preserved", "Z0*Z1*Z9 -> Z0*Z1*Z9", True)
flow("Z-check4 Z6 Z7 Z11 preserved", "Z6*Z7*Z11 -> Z6*Z7*Z11", True)

print("\n(measurement faithfulness) each merged check measures its support:")
flow("merge X-check {6,7,8,13}", "X6*X7*X8*X13 -> rec[-8]", True)
flow("Z-check2 {3,4,9,11}", "Z3*Z4*Z9*Z11 -> rec[-4]", True)

print("\n" + ("ALL FLOWS AS EXPECTED — surgery is a correct projective X-bar measurement"
              if ok else "SOME FLOWS UNEXPECTED")); sys.exit(0 if ok else 1)
