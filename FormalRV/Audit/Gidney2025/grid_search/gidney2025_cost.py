#!/usr/bin/env python3
"""Gidney 2025 (arXiv:2505.15917) logical Toffoli cost model + grid search.

NUMERICAL optimization half of the audit: reproduce the paper's grid scan
(main.tex L1006-1016) over (s, ell, w1, w3, w4, f) to find the params minimizing
q^3*t, and reproduce the 6.5e9 Toffoli headline at the RSA-2048 optimum.
Lean then VERIFIES the circuit Toffoli count at these FIXED optimal params
(the per-gadget counts come from EGate.toffoli on the verified syntactic objects).

The paper ships only the reference ALGORITHM code (assets/gen/detailed_example_code.py,
needs the external `scatter_script`), not the cost/grid script - so this is a
self-contained reimplementation from the symbolic subroutine-tallies (tbl:subroutine-tallies).
"""
import math

def ceil_div(a, b): return -(-a // b)
def lenm(m): return m.bit_length()                 # ceil(log2 m); 1280 -> 11

# --- per-operation Toffoli costs (the three primitives, main.tex L995-998) ---
def lookup_cost(w): return 2**w - w - 1            # Babbush QROM (paper)
def phaseup_cost(w): return round(math.sqrt(2**w)) # Berry qubitization sqrt(2^w)
# "addition" primitive (paper L996 region) = PLAIN Gidney adder, n-1 Toffoli.
# (The modular reduction is NOT a costed add - it surfaces as the lookup/phaseup
#  columns.)  mult selects the model: 'plain' = r-1; else mult*r (modular brackets).
def add_cost(r, mult):
    if mult == 'plain': return max(r - 1, 0)
    return mult * r

# --- |P|: number of residue primes, tbl:symbols  |P| ~ n*m/(ell*w1) ---
def num_primes(n, m, ell, w1): return ceil_div(n * m, ell * w1)

# --- the per-shot modexp Toffoli, summing tbl:subroutine-tallies (8 rows) ---
def per_shot_toffoli(n, s, ell, w1, w3, w4, f, m, mult):
    P  = num_primes(n, m, ell, w1)
    LM = lenm(m)
    W1 = ceil_div(m, w1); W3 = ceil_div(ell, w3); W4 = ceil_div(ell, w4)
    aC = lambda r: add_cost(r, mult)
    # mixed model: loop1/2/3 additions are PLAIN (dlog accumulation, reduced once);
    # loop4 + unloop3 (the truncated mod-N / mod-p accumulators) use the MODULAR adder.
    aMod = lambda r: add_cost(r, 2.0) if mult == 'mixed' else aC(r)
    aPln = lambda r: add_cost(r, 'plain') if mult == 'mixed' else aC(r)
    rows = [
        # (iterations,                 add#, addReg,  look#, lookAddr, phase#, phaseAddr, addModular?)
        ((P + 1) * W1,                 1,    ell+LM,  1,     w1,       0,      0,     False),  # loop1
        (P * LM,                       2,    ell+LM,  0,     0,        0,      0,     False),  # loop2
        (P,                            0,    0,       1,     2*w3,     0,      0,     False),  # loop3 startup
        (P * (W3-2) * W3,              2,    ell,     1,     w3,       0,      0,     False),  # loop3 body
        (P * W4,                       1.5,  f,       2.5,   w4,       1,      w4,    True ),  # loop4
        (P * (W3-2) * 2 * W3,          2.5,  ell,     1.5,   w3,       1,      w3,    True ),  # unloop3 body
        (P,                            0,    0,       0,     0,        1,      2*w3,  False),  # unloop3 cleanup
        (P * LM,                       2,    ell+LM,  0,     0,        0,      0,     False),  # unloop2
    ]
    total = 0.0
    for it, na, ar, nl, la, npu, pa, modular in rows:
        ac = (aMod(ar) if modular else aPln(ar)) if mult == 'mixed' else aC(ar)
        per_it = na*ac + nl*lookup_cost(la) + npu*(phaseup_cost(pa) if npu else 0)
        total += it * per_it
    return total

def logical_qubits(n, ell, w1, w3, w4, f, m):
    # tbl:subroutine-qubit-tallies peak ~ m + 3f + 2ell + len m (loop4 region) — approximate
    LM = lenm(m)
    return m + 3*f + 2*ell + LM

def shots(s, p_dev=0.0125): return (s + 1) / (1 - p_dev) / 0.99

def toffoli_per_factoring(n, s, ell, w1, w3, w4, f, m, mult):
    return per_shot_toffoli(n, s, ell, w1, w3, w4, f, m, mult) * shots(s)

if __name__ == "__main__":
    n = 2048
    # ---- (1) reproduce the headline at the paper's stated RSA-2048 optimum ----
    opt = dict(s=8, ell=21, w1=6, w3=3, w4=5, f=33, m=1280)
    print("=== RSA-2048 at paper's stated optimum (s=8,ell=21,w1=6,w3=3,w4=5,f=33,m=1280) ===")
    print(f"  |P| = {num_primes(n, opt['m'], opt['ell'], opt['w1'])},  W1={ceil_div(opt['m'],opt['w1'])}, "
          f"W3={ceil_div(opt['ell'],opt['w3'])}, W4={ceil_div(opt['ell'],opt['w4'])}, E(shots)={shots(opt['s']):.2f}")
    for mult in ('plain', 'mixed', 2.0, 2.5):
        t = toffoli_per_factoring(n, **opt, mult=mult)
        lbl = {'plain':'plain r-1','mixed':'mixed (L1-3 plain, L4/u3 mod-2n)'}.get(mult, f"{mult}*r")
        print(f"  add={lbl:32s}: {t:.3e}  ({t/1e9:.2f}e9)   [headline 6.5e9]")

    # ---- (2) the grid scan (paper ranges) minimizing q^3 * t ----
    print("\n=== grid scan (minimize q^3 * t), add=mixed (faithful per-loop) ===")
    best = None
    for s in range(2, 15):
        m = math.ceil(n/2 + n/s)
        for ell in range(18, 26):
            for w1 in range(2, 9):
                for w3 in range(2, 7):
                    for w4 in range(2, 9):
                        for f in range(24, 60):
                            # feasibility: prod P >= N^(m/w1) i.e. |P|*ell >= n*m/w1 (by construction of num_primes)
                            t = toffoli_per_factoring(n, s, ell, w1, w3, w4, f, m, mult='mixed')
                            q = logical_qubits(n, ell, w1, w3, w4, f, m)
                            score = q**3 * t
                            if best is None or score < best[0]:
                                best = (score, dict(s=s, ell=ell, w1=w1, w3=w3, w4=w4, f=f, m=m, q=q, t=t))
    sc, b = best
    print(f"  optimum: s={b['s']} ell={b['ell']} w1={b['w1']} w3={b['w3']} w4={b['w4']} f={b['f']} m={b['m']}")
    print(f"           q={b['q']}  t={b['t']:.3e} ({b['t']/1e9:.2f}e9)   [paper: s=8,ell=21,w1=6,w3=3,w4=5,f=33; 6.5e9]")
