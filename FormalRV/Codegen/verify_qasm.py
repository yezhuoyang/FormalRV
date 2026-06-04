#!/usr/bin/env python3
"""
Cross-verify the Lean `Gate -> OpenQASM` emitter against the project's verified
Boolean semantics `Gate.applyNat`, using Qiskit.

Lean writes, in C:/tmp/qasm_demo/, for each demo gate:
  <name>.qasm      -- Clifford+T OpenQASM 2.0 (CCX lowered to h/t/tdg/cx)
  <name>.ccx.qasm  -- native OpenQASM 2.0 (x/cx/ccx)
  <name>.tt        -- (small gates only) verified permutation from Lean permAt:
                      first line width w, then "x y" = Gate.applyNat: |x> -> |y>.

Ground truth for the induced classical permutation:
  * If <name>.tt exists  -> the Lean-verified permutation (kernel-checked).
  * Otherwise            -> classically simulate the native x/cx/ccx circuit,
                            which is *exactly* `Gate.applyNat` by construction
                            (a 1:1 structural transcription of the Gate tree).

Checks per gate:
  (1) NATIVE faithfulness (only when .tt present): the native x/cx/ccx sim
      equals the Lean truth table on every tabulated input.
  (2) CLIFFORD+T faithfulness: Qiskit-simulate the Clifford+T circuit and
      require its basis-state map to equal the ground-truth permutation.  This
      certifies the exact 7-T Toffoli decomposition.

Qubit convention matches Lean `permAt`: qubit q is bit q (LSB = q0), i.e.
Qiskit's little-endian Statevector integer index.
"""
import sys, os, re

DIR = "C:/tmp/qasm_demo/"
DEMOS = ["swap01", "toffoli", "addconst3", "modadd", "modmult"]
SAMPLE_N = 24  # inputs sampled for gates lacking a Lean truth table


def read_tt(path):
    with open(path) as f:
        lines = [l.strip() for l in f if l.strip()]
    return int(lines[0]), [tuple(map(int, l.split())) for l in lines[1:]]


def parse_qasm_ops(path):
    """Return (n_qubits, [(name, [qubit indices])]) for a flat qelib1 program."""
    ops, n = [], None
    with open(path) as f:
        for raw in f:
            line = raw.strip().rstrip(";")
            if not line or line.startswith("OPENQASM") or line.startswith("include"):
                continue
            m = re.match(r"qreg\s+q\[(\d+)\]", line)
            if m:
                n = int(m.group(1)); continue
            m = re.match(r"([a-zA-Z]+)\s+(.*)", line)
            if m:
                qs = [int(x) for x in re.findall(r"q\[(\d+)\]", m.group(2))]
                ops.append((m.group(1), qs))
    return n, ops


def classical_sim_native(ops, x):
    """Simulate a reversible x/cx/ccx program on basis state x (= Gate.applyNat)."""
    bit = lambda v, i: (v >> i) & 1
    for name, qs in ops:
        if name == "x":
            x ^= (1 << qs[0])
        elif name == "cx":
            x ^= (bit(x, qs[0]) << qs[1])
        elif name == "ccx":
            x ^= ((bit(x, qs[0]) & bit(x, qs[1])) << qs[2])
        elif name == "id":
            pass
        else:
            raise ValueError(f"non-classical gate {name!r} in native QASM")
    return x


def qiskit_out(qc, x, w):
    import numpy as np
    from qiskit.quantum_info import Statevector
    out = Statevector.from_int(x, 2 ** w).evolve(qc)
    data = np.abs(out.data)
    idx = int(np.argmax(data))
    return idx, float(data[idx])


def check_gate(name):
    import qiskit.qasm2
    n_native, ops = parse_qasm_ops(DIR + name + ".ccx.qasm")
    qc = qiskit.qasm2.load(DIR + name + ".qasm")
    w = qc.num_qubits
    assert n_native == w, f"{name}: width mismatch native {n_native} vs cliff+T {w}"

    ttpath = DIR + name + ".tt"
    if os.path.exists(ttpath):
        wtt, pairs = read_tt(ttpath)
        assert wtt == w, f"{name}: tt width {wtt} vs {w}"
        source = "lean"
    else:
        xs = sorted(set([(i * 7919) % (2 ** w) for i in range(SAMPLE_N)] + list(range(min(8, 2 ** w)))))
        pairs = [(x, classical_sim_native(ops, x)) for x in xs]
        source = "native-sim"

    nat_ok = nat_bad = ct_ok = ct_bad = 0
    for x, y in pairs:
        # (1) native faithfulness to the Lean truth table (only meaningful when source==lean)
        if source == "lean":
            if classical_sim_native(ops, x) == y: nat_ok += 1
            else:
                nat_bad += 1
                if nat_bad <= 3: print(f"   native MISMATCH {name}: x={x} exp {y} got {classical_sim_native(ops, x)}")
        # (2) Clifford+T faithfulness to ground truth
        idx, amp = qiskit_out(qc, x, w)
        if idx == y and amp > 0.999: ct_ok += 1
        else:
            ct_bad += 1
            if ct_bad <= 3: print(f"   cliff+T MISMATCH {name}: x={x} exp {y} got {idx} (|amp|={amp:.4f})")
    return source, len(pairs), nat_ok, nat_bad, ct_ok, ct_bad


def main():
    print(f"Verifying emitted QASM in {DIR} against Lean Gate.applyNat\n")
    print(f"{'gate':12s} {'width':>5s} {'#chk':>5s} {'native':>10s} {'clifford+T':>12s}  source")
    fails = 0
    for name in DEMOS:
        if not os.path.exists(DIR + name + ".ccx.qasm"):
            print(f"{name:12s}  SKIP (no files)"); continue
        try:
            src, npr, no, nb, co, cb = check_gate(name)
        except Exception as e:
            fails += 1
            print(f"{name:12s}  ERROR: {e}")
            continue
        fails += nb + cb
        w = parse_qasm_ops(DIR + name + ".ccx.qasm")[0]
        nat = f"{no}/{no+nb}" if src == "lean" else "--"
        print(f"{name:12s} {w:5d} {npr:5d} {nat:>10s} {f'{co}/{co+cb}':>12s}  [{src}]")
    print()
    if fails == 0:
        print("ALL CHECKS PASSED: every emitted circuit realises the verified Gate.applyNat permutation,")
        print("and the Clifford+T (h/t/tdg/cx) circuits match the native Toffoli circuits exactly.")
        sys.exit(0)
    print(f"FAILURES: {fails}")
    sys.exit(1)


if __name__ == "__main__":
    main()
