"""
Convert the FormalRV-emitted surface-code surgery Stim circuit into the unitary OpenQASM 2.0
that ZAC compiles ({CZ, U3} after Qiskit transpilation).

The surgery circuit is a syndrome round: per X-check `RX anc; CX anc->data...; MX anc`, per
Z-check `R anc; CX data->anc...; M anc`. ZAC routes UNITARY gates onto atom movements, so we keep
the entangling skeleton (the CX gates — what actually determines the atom moves / Rydberg CZs) and
the basis-setting H's, and drop the mid-circuit reset/measure SPAM (done in place / a readout
zone). Mapping:  RX a -> h q[a]   (|0> -> |+>);  R a -> (|0> default);  CX a b -> cx;
                 MX a -> h q[a]   (rotate back);  M a -> (drop).

Usage:  python stim_to_qasm.py surface3_xx_merge.stim surface3_xx_merge.qasm
"""
import sys


def convert(stim_path, qasm_path):
    rows = [ln.split() for ln in open(stim_path) if ln.split()]
    nq = 1 + max(int(t) for r in rows for t in r[1:] if t.lstrip("-").isdigit())
    out = ["OPENQASM 2.0;", 'include "qelib1.inc";', f"qreg q[{nq}];"]
    ncx = 0
    for r in rows:
        op = r[0]
        if op == "RX":
            out.append(f"h q[{r[1]}];")
        elif op == "MX":
            out.append(f"h q[{r[1]}];")
        elif op == "CX":
            out.append(f"cx q[{r[1]}],q[{r[2]}];"); ncx += 1
        # R (reset to |0>, the default) and M (Z-measure) are SPAM -> dropped for the unitary route
    open(qasm_path, "w").write("\n".join(out) + "\n")
    print(f"{qasm_path}: {nq} qubits, {ncx} cx (entangling) gates")


if __name__ == "__main__":
    a = sys.argv[1] if len(sys.argv) > 1 else "surface3_xx_merge.stim"
    b = sys.argv[2] if len(sys.argv) > 2 else "surface3_xx_merge.qasm"
    convert(a, b)
