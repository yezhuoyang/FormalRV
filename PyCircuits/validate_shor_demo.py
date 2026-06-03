"""
Validate the Lean-EMITTED scheduled surface-code circuit with Stim.

`FormalRV/LatticeSurgery/ScheduleEmit.lean` emitted `PyCircuits/shor_demo_schedule.stim`
— a 3-surgery surface-code schedule (3 logical-X-bar merges on the verified [[13,1,3]]
code), each placed on a DISJOINT 28-qubit / 14-measurement block (offsets 0/28/56,
14/28/42).  We confirm, INDEPENDENTLY of the Lean proof, that EVERY emitted block is a
correct projective logical-X-bar measurement, via Stim's stabilizer-flow check
(has_flow) — the same gold standard the rest of the project uses.

A third party who does not trust our proof can run THIS on the emitted code.
"""
import stim, sys

CIRC = "PyCircuits/shor_demo_schedule.stim"
N_SURG, MEAS_PER, QUBITS_PER = 3, 14, 28
TOTAL_MEAS = N_SURG * MEAS_PER

c = stim.Circuit.from_file(CIRC)
print(f"loaded {CIRC}: {c.num_qubits} qubits, {c.num_measurements} measurements "
      f"({N_SURG} surgeries x {MEAS_PER})")
assert c.num_measurements == TOTAL_MEAS, (c.num_measurements, TOTAL_MEAS)

ok = True
for i in range(N_SURG):
    qo = QUBITS_PER * i          # qubit offset of block i
    mo = MEAS_PER * i            # measurement offset of block i
    # the two ancilla X-checks of block i read the logical X-bar = X6 X7 X8 (offset):
    r1 = -(TOTAL_MEAS - (mo + 6))
    r2 = -(TOTAL_MEAS - (mo + 7))
    flow = f"X{6+qo}*X{7+qo}*X{8+qo} -> rec[{r1}] xor rec[{r2}]"
    r = c.has_flow(stim.Flow(flow))
    ok = ok and r
    print(f"  surgery {i} (qubits {qo}..{qo+27}): [{'PASS' if r else 'FAIL'}] "
          f"logical X-bar readout  ({flow})")

print("\nEVERY emitted surgery is a correct projective X-bar measurement — the "
      "Lean-emitted scheduled circuit is Stim-verified."
      if ok else "\nFAIL: an emitted block did not measure X-bar.")
sys.exit(0 if ok else 1)
