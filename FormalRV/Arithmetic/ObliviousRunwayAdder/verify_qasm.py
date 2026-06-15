#!/usr/bin/env python3
"""Numerically verify the GENERATED QASM of the oblivious-runway adder is a real adder.
Classical-reversible simulation on computational basis states (exact for X/CX/CCX)."""
import re, sys, itertools

def parse(path):
    gates = []
    for ln in open(path):
        ln = ln.strip()
        m = re.match(r'(x|cx|ccx)\s+(.*);', ln)
        if not m: continue
        op = m.group(1)
        qs = [int(q) for q in re.findall(r'q\[(\d+)\]', m.group(2))]
        gates.append((op, qs))
    return gates

def apply(gates, bits):
    b = bits[:]
    for op, qs in gates:
        if op == 'x': b[qs[0]] ^= 1
        elif op == 'cx':
            if b[qs[0]]: b[qs[1]] ^= 1
        elif op == 'ccx':
            if b[qs[0]] and b[qs[1]]: b[qs[2]] ^= 1
    return b

def n_qubits(gates):
    return max(q for _, qs in gates for q in qs) + 1

def augIdx(base, i): return base + 2*i + 1
def addIdx(base, i): return base + 2*i + 2
def segBase(gSep, m): return m*(2*gSep+3)

def test_adder(path, gSep, k, exhaustive_upto=None):
    gates = parse(path)
    nq = n_qubits(gates)
    n = gSep*k
    # detect adjacent cancelling CCX pairs (the redundancy)
    cancel = sum(1 for i in range(len(gates)-1)
                 if gates[i][0]=='ccx' and gates[i+1]==gates[i])
    print(f"\n=== {path}  (gSep={gSep}, k={k}, n={n}, qubits={nq}, gates={len(gates)}) ===")
    print(f"  adjacent identical-CCX pairs (cancel to I): {cancel}")
    rng = range(1 << n)
    if exhaustive_upto and (1<<n) > exhaustive_upto:
        rng = list(range(0, 1<<n, max(1,(1<<n)//exhaustive_upto)))
    fails = 0; checked = 0; addend_broken = 0
    for a in rng:
        for b in rng:
            checked += 1
            bits = [0]*nq
            for m in range(k):
                a_m = (a >> (m*gSep)) & ((1<<gSep)-1)
                b_m = (b >> (m*gSep)) & ((1<<gSep)-1)
                base = segBase(gSep, m)
                for i in range(gSep):
                    bits[augIdx(base, i)] = (a_m >> i) & 1   # augend data
                    bits[addIdx(base, i)] = (b_m >> i) & 1   # addend data
                # runway (augend bit gSep), addend-top (addend bit gSep), carry-in (base) all 0
            out = apply(gates, bits)
            # contiguous value: sum_m (segReg_m, the full (gSep+1)-bit augend reg) * 2^(m*gSep)
            contiguous = 0
            for m in range(k):
                base = segBase(gSep, m)
                seg = sum(out[augIdx(base, i)] << i for i in range(gSep+1))
                contiguous += seg << (m*gSep)
            if contiguous != a + b:
                fails += 1
                if fails <= 3:
                    print(f"  FAIL a={a} b={b}: got {contiguous}, want {a+b}")
            # addend register restored?
            for m in range(k):
                base = segBase(gSep, m)
                b_m = (b >> (m*gSep)) & ((1<<gSep)-1)
                got_b = sum(out[addIdx(base, i)] << i for i in range(gSep))
                if got_b != b_m: addend_broken += 1
    print(f"  checked {checked} (a,b) pairs: {'ALL PASS' if fails==0 else str(fails)+' FAILS'} "
          f"(contiguous == a+b)")
    print(f"  addend register restored in all cases: {'YES' if addend_broken==0 else 'NO ('+str(addend_broken)+' broken)'}")
    return fails

d = "FormalRV/Arithmetic/ObliviousRunwayAdder/diagrams"
total_fail = 0
total_fail += test_adder(f"{d}/runway_g4_k1.qasm", 4, 1)            # 256 pairs
total_fail += test_adder(f"{d}/runway_g4_k2.qasm", 4, 2, exhaustive_upto=64)  # sampled
total_fail += test_adder(f"{d}/oblivious_runway_adder_g2_k2.qasm", 2, 2)      # 256 pairs (committed/diagram)
print(f"\n==== OVERALL: {'ALL ADDERS CORRECT' if total_fail==0 else str(total_fail)+' TOTAL FAILURES'} ====")
