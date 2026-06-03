"""
Cross-validate the Lean-verified surface3 surgery gadget against Stim.

`surface3_surgery.stim` is emitted by the Lean framework via
`FormalRV.LatticeSurgery.StimEmit.surgeryToStim surface3_x_surgery`
(regenerate with: `#eval IO.FS.writeFile "PyCircuits/surface3_surgery.stim"
(surgeryToStim surface3_x_surgery)` after importing StimEmit + SurgeryDemoSurface).

It is the DETAILED merged-code syndrome circuit: per merged X-check an ancilla
|+>, CX anc->support, MX; per merged Z-check an ancilla |0>, CX support->anc, M.
14 measurements: X-checks rec 0..7, Z-checks rec 8..13.

Stim's flow analysis (the reference Gottesman-Knill oracle) independently
confirms the Lean theorem `surface3_x_surgery_measures_logicalX`: the
span_witness-selected X-checks (rows 6,7 = rec[-8] xor rec[-7]) read the logical
X-bar = X6 X7 X8.
"""
import stim, sys
c = stim.Circuit(open("PyCircuits/surface3_surgery.stim").read())
print("qubits:", c.num_qubits, " measurements:", c.num_measurements)
all_pass = True
def ok(desc, flow_str):
    global all_pass
    try: r = c.has_flow(stim.Flow(flow_str))
    except Exception as e: r = f"ERR {e}"
    all_pass = all_pass and (r is True)
    print(f"  [{'PASS' if r is True else 'FAIL'}] {desc}: {flow_str} -> {r}")

print("\n== logical X-bar readout (span_witness rows 6,7 = rec[-8] xor rec[-7]) ==")
ok("X-bar = X6 X7 X8 read by selected X-checks", "X6*X7*X8 -> rec[-8] xor rec[-7]")
print("\n== each merged X-check measures its support ==")
ok("X-check0 {0,3,9}",   "X0*X3*X9 -> rec[-14]")
ok("X-check6 {6,7,8,13}", "X6*X7*X8*X13 -> rec[-8]")
ok("X-check7 {13}",       "X13 -> rec[-7]")
print("\n== merged Z-checks measure their supports ==")
ok("Z-check0 {0,1,9}",    "Z0*Z1*Z9 -> rec[-6]")
ok("Z-check2 {3,4,9,11}", "Z3*Z4*Z9*Z11 -> rec[-4]")
print("\nALL PASS" if all_pass else "\nSOME FAILED"); sys.exit(0 if all_pass else 1)
