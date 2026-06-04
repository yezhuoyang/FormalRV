#!/usr/bin/env python3
"""
Demonstration: the emitted Clifford+T OpenQASM for the project's *verified*
modular multiplier `modMultConstGate 2 3 2 2` computes  x -> (2*x) mod 3.

Layout (from `modMultConstGate_correct` + the Cuccaro register layout):
  * adder block occupies qubits [0, adder_n_qubits(bits+1)) = [0, 11);
  * the multiplier register holds x at qubits [11, 11+multBits) = [11, 13)
    (little-endian);  the flag is at qubit 13.
  * `mult_state_init` starts the adder target at 0; after the gate the target
    holds (a*x) mod N, read off at adder positions 3*i+1 (bit i).

We run the emitted circuit two ways and compare to the arithmetic:
  * native x/cx/ccx classical simulation (= the verified `Gate.applyNat`);
  * Qiskit statevector simulation of the Clifford+T (h/t/tdg/cx) circuit.
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from verify_qasm import parse_qasm_ops, classical_sim_native, qiskit_out, DIR
import qiskit.qasm2

BITS, N, A_CONST, MULTBITS = 2, 3, 2, 2
ADDER = 3 * (BITS + 1) + 2  # adder_n_qubits(bits+1) = 11

encode_x = lambda x: sum(((x >> j) & 1) << (ADDER + j) for j in range(MULTBITS))
read_target = lambda out: sum(((out >> (3 * i + 1)) & 1) << i for i in range(BITS))


def main():
    _, ops = parse_qasm_ops(DIR + "modmult.ccx.qasm")
    qc = qiskit.qasm2.load(DIR + "modmult.qasm")
    w = qc.num_qubits
    print(f"emitted modMultConstGate(bits={BITS}, N={N}, a={A_CONST}, multBits={MULTBITS})"
          f"  ->  x -> {A_CONST}*x mod {N}")
    print(f"  width={w} qubits, T-count={sum(1 for ln in open(DIR+'modmult.qasm') if ln[:2] in ('t ','td'))}")
    print(f"  {'x':>3} | {'native':>6} | {'cliff+T':>7} | {'2x mod 3':>8}")
    ok = True
    for x in range(N):
        nat = read_target(classical_sim_native(ops, encode_x(x)))
        ct, _ = qiskit_out(qc, encode_x(x), w)
        ctv = read_target(ct)
        exp = (A_CONST * x) % N
        ok &= (nat == exp and ctv == exp)
        print(f"  {x:>3} | {nat:>6} | {ctv:>7} | {exp:>8}")
    print("\n" + ("OK: emitted Clifford+T modular multiplier matches 2x mod 3." if ok else "MISMATCH"))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
