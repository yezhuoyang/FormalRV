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

    roles = ["data"] * NDATA + ["merge"] * pool_size
    body = []
    magic_k = 0

    def remap(q, w, qs):
        if q < TEMPLATE_NDATA[w]:               # data: template patch (q//13) -> adder patch qs[i]
            return qs[q // PATCH] * PATCH + q % PATCH
        return ANC_BASE + (q - TEMPLATE_NDATA[w])   # ancilla -> reused pool

    for kind, arg in ops:
        if kind == "M":
            w = len(arg)
            for r in tmpl[w]:                   # the full merged-code syndrome (88 / 131 CX)
                op = r[0]
                if op in ("RX", "MX"):
                    body.append(f"h q[{remap(int(r[1]), w, arg)}];")
                elif op == "CX":
                    body.append(f"cx q[{remap(int(r[1]), w, arg)}],q[{remap(int(r[2]), w, arg)}];")
                # R / M (reset / measure) are SPAM -> dropped (ZAC routes the unitary part)
        else:                                   # T: bind a |CCZ> magic atom to the target patch
            m = MAGIC_BASE + magic_k; magic_k += 1
            roles.append("magic")
            body.append(f"cx q[{arg * PATCH}],q[{m}];")

    nq = MAGIC_BASE + magic_k
    qasm = ["OPENQASM 2.0;", 'include "qelib1.inc";', f"qreg q[{nq}];"] + body
    open(os.path.join(HERE, "surface3_adder2_d3_full.qasm"), "w").write("\n".join(qasm) + "\n")
    json.dump({"n_atoms": nq, "n_data": NDATA, "n_patch": N_PATCH, "patch": PATCH,
               "pool_size": pool_size, "roles": roles},
              open(os.path.join(HERE, "surface3_adder2_d3_full.roles.json"), "w"))
    ncx = sum(1 for b in body if b.startswith("cx"))
    print(f"surface3_adder2_d3_full.qasm: {nq} atoms ({NDATA} data = {N_PATCH} d=3 patches, "
          f"{pool_size} reused merge ancillae, {magic_k} magic), {ncx} cx "
          f"(FULL merged-code syndrome per merge)")


if __name__ == "__main__":
    main()
