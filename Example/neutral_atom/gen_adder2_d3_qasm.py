"""
Build the PHYSICAL distance-3 surface-code lattice-surgery circuit for the SAME 2-bit Cuccaro
adder used in the main example (Example/Adder2EndToEnd.lean), for compilation onto a neutral-atom
machine by ZAC.

The adder's 5 logical qubits become 5 surface-code [[13,1,3]] patches (13 data atoms each, the
verified FormalRV `surfaceHGP 3` code). Its lattice surgery is the adder's PPM program
(PyCircuits/ppm/adder2_ppm.txt): each joint Pauli-Z measurement `M Z [qs]` is a surface-code
MERGE, realized by an ancilla coupled (CX) to the logical-Z̄ boundary {0,3,6} of each involved
patch; each `T` (one per Toffoli) consumes a |CCZ> magic state from a factory atom. Emits the
unitary entangling skeleton (CX; ZAC transpiles to CZ+U3) plus a sidecar of per-atom zone roles
(data / merge-ancilla / magic), so the compiler can place atoms in Memory / Ancilla / Factory.

Usage:  python gen_adder2_d3_qasm.py
Out:    surface3_adder2_d3.qasm , surface3_adder2_d3.roles.json
"""
import json
import os

# surface3 = surfaceHGP 3 = [[13,1,3]] (dumped from FormalRV scripts/DumpSurface3.lean)
HZ = [[0, 1, 9], [1, 2, 10], [3, 4, 9, 11], [4, 5, 10, 12], [6, 7, 11], [7, 8, 12]]
Z_BDRY = [0, 3, 6]          # logical Z̄ support of a surface3 patch (Z0 Z3 Z6)
PATCH = 13
N_PATCH = 5                 # the 2-bit Cuccaro adder is 5 logical qubits

HERE = os.path.dirname(os.path.abspath(__file__))
PPM = os.path.join(HERE, "..", "..", "PyCircuits", "ppm", "adder2_ppm.txt")


def main():
    ops = []
    for ln in open(PPM):
        p = ln.split()
        if not p or p[0].startswith("#"):
            continue
        if p[0] == "M" and p[1] == "Z":
            ops.append(("M", [int(x) for x in p[2].split(",")]))
        elif p[0] == "T":
            ops.append(("T", int(p[1])))

    ndata = N_PATCH * PATCH                  # 65 data atoms (5 patches)
    roles = ["data"] * ndata
    body = []
    nxt = ndata

    def new_atom(role):
        nonlocal nxt
        roles.append(role); nxt += 1
        return nxt - 1

    def cx(a, b):
        body.append(f"cx q[{a}],q[{b}];")

    # the lattice surgery: one merge (or magic injection) per PPM op, in order
    for kind, arg in ops:
        if kind == "M":                      # joint-Z̄ MERGE of the involved patches
            anc = new_atom("merge")
            for q in arg:                    # q = logical qubit = patch index (0..4)
                for s in Z_BDRY:
                    cx(q * PATCH + s, anc)    # couple patch q's Z̄-boundary into the merge ancilla
        else:                                # kind == "T": consume a |CCZ> magic state
            fac = new_atom("magic")
            cx(arg * PATCH + Z_BDRY[0], fac)  # bind the magic atom to the target patch (injection)

    qasm = ["OPENQASM 2.0;", 'include "qelib1.inc";', f"qreg q[{nxt}];"] + body
    open(os.path.join(HERE, "surface3_adder2_d3.qasm"), "w").write("\n".join(qasm) + "\n")
    json.dump({"n_atoms": nxt, "n_data": ndata, "n_patch": N_PATCH, "patch": PATCH, "roles": roles},
              open(os.path.join(HERE, "surface3_adder2_d3.roles.json"), "w"))
    nmerge = roles.count("merge"); nmagic = roles.count("magic")
    print(f"surface3_adder2_d3.qasm: {nxt} atoms ({ndata} data = {N_PATCH} d=3 patches, "
          f"{nmerge} merge ancillae, {nmagic} magic atoms), {len(body)} cx (merges)")


if __name__ == "__main__":
    main()
