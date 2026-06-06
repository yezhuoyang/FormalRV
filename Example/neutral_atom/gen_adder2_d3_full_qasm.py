"""
FULL-MERGE version: the 2-bit Cuccaro adder's distance-3 surface-code lattice surgery where EACH of
the adder's 12 joint-Z measurements is the COMPLETE merged-code syndrome circuit (not just the
joint-Z̄ readout) — exactly the verified `surface3_zz_merge` (88 CX) / `surface3_zzz_merge` (131 CX)
gadgets, remapped onto the 5 SHARED [[13,1,3]] patches.

Each PPM `M Z [qs]` instantiates the matching template (zz for 2 patches, zzz for 3); the template's
data qubits are remapped to the global atoms of the involved patches, and its surgery+syndrome
ancillae are mapped to a REUSED ancilla pool (the ancillae are measured+reset between merges — ZAC
ignores measurement and routes the gates, so the same atoms serve every merge). Each `T` (Toffoli)
binds a |CCZ> magic atom (FACTORY). Emits the unitary entangling skeleton (CX + H) for ZAC.

Usage:  python gen_adder2_d3_full_qasm.py
Out:    surface3_adder2_d3_full.qasm , surface3_adder2_d3_full.roles.json
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
PPM = os.path.join(HERE, "..", "..", "PyCircuits", "ppm", "adder2_ppm.txt")
PATCH = 13
N_PATCH = 5
NDATA = N_PATCH * PATCH          # 65 data atoms
TEMPLATE_NDATA = {2: 26, 3: 39}  # data qubits in the zz / zzz templates (2 or 3 patches)
TEMPLATES = {2: "surface3_zz_merge.stim", 3: "surface3_zzz_merge.stim"}


def load_template(path):
    return [ln.split() for ln in open(path) if ln.split()]


def main():
    # parse the adder's PPM (joint-Z measurements + magic-T), in order
    ops = []
    for ln in open(PPM):
        p = ln.split()
        if not p or p[0].startswith("#"):
            continue
        if p[0] == "M" and p[1] == "Z":
            ops.append(("M", [int(x) for x in p[2].split(",")]))
        elif p[0] == "T":
            ops.append(("T", int(p[1])))

    tmpl = {w: load_template(os.path.join(HERE, TEMPLATES[w])) for w in (2, 3)}
    pool_size = max(1 + max(int(t) for r in tmpl[w] for t in r[1:] if t.isdigit()) - TEMPLATE_NDATA[w]
                    for w in (2, 3))           # ancilla-pool size = largest template's ancilla count
    ANC_BASE = NDATA
    MAGIC_BASE = ANC_BASE + pool_size

    MAGIC = [MAGIC_BASE + j for j in range(3)]   # 3 reused |CCZ> magic atoms (Factory)
    roles = ["data"] * NDATA + ["merge"] * pool_size + ["magic"] * 3
    body = []
    n_tof = 0

    def remap(q, w, qs):
        if q < TEMPLATE_NDATA[w]:               # data: template patch (q//13) -> adder patch qs[i]
            return qs[q // PATCH] * PATCH + q % PATCH
        return ANC_BASE + (q - TEMPLATE_NDATA[w])   # ancilla -> reused pool

    def emit_merge(qs):                         # the FULL merged-code syndrome (zz 88 / zzz 131 CX)
        w = len(qs)
        for r in tmpl[w]:
            if r[0] in ("RX", "MX"):
                body.append(f"h q[{remap(int(r[1]), w, qs)}];")
            elif r[0] == "CX":
                body.append(f"cx q[{remap(int(r[1]), w, qs)}],q[{remap(int(r[2]), w, qs)}];")
            # R / M (reset / measure) are SPAM -> controller-side (ZAC routes the unitary part)

    i = 0
    while i < len(ops):
        kind, arg = ops[i]
        if kind == "T":                         # TOFFOLI = real |CCZ> magic injection (T + next M Z)
            qs = ops[i + 1][1]                   # the paired joint measurement M Z qs (weight 3)
            body.append(f"h q[{MAGIC[0]}];"); body.append(f"h q[{MAGIC[1]}];")
            body.append(f"ccx q[{MAGIC[0]}],q[{MAGIC[1]}],q[{MAGIC[2]}];")
            body.append(f"h q[{MAGIC[2]}];")    # |CCZ> = CCZ|+++>  (= H0 H1 . CCX . H2 on |000>)
            emit_merge(qs)                       # full merged-code joint measurement on the 3 data patches
            for j, p in enumerate(qs):           # inject: couple the |CCZ> into the 3 data patches
                body.append(f"cx q[{p * PATCH}],q[{MAGIC[j]}];")
            n_tof += 1
            i += 2
        else:                                   # standalone M Z = CNOT (Clifford merge)
            emit_merge(arg)
            i += 1

    nq = MAGIC_BASE + 3
    qasm = ["OPENQASM 2.0;", 'include "qelib1.inc";', f"qreg q[{nq}];"] + body
    open(os.path.join(HERE, "surface3_adder2_d3_full.qasm"), "w").write("\n".join(qasm) + "\n")
    json.dump({"n_atoms": nq, "n_data": NDATA, "n_patch": N_PATCH, "patch": PATCH,
               "pool_size": pool_size, "roles": roles},
              open(os.path.join(HERE, "surface3_adder2_d3_full.roles.json"), "w"))
    ncx = sum(1 for b in body if b.startswith("cx"))
    print(f"surface3_adder2_d3_full.qasm: {nq} atoms ({NDATA} data = {N_PATCH} d=3 patches, "
          f"{pool_size} reused merge ancillae, 3 |CCZ> magic), {ncx} cx + {n_tof} real |CCZ> "
          f"magic injections (FULL merged-code syndrome per merge)")


if __name__ == "__main__":
    main()
