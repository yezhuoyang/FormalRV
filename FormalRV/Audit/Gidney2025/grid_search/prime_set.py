#!/usr/bin/env python3
"""Reconstruct the ACTUAL residue prime-set size |P| = len(conf.periods) for RSA-2048,
the way Gidney 2025's reference code does (assets/gen/simple_example_code.py: take
ell-bit primes until their product clears the no-wraparound bound L), instead of the
symbolic approximation |P| ~ nm/(ell*w1).  Then feed the true |P| into the verified
schedule and see how close the derived Toffoli count gets to the 6.5e9 headline.

Bounds considered (the windowed/optimized residue product, main.tex eq:bound-L + tbl:symbols):
  - L >= N^(m/w1)   (windowed: w1 multiplications batched per lookup)  -> |P| ~ nm/(ell w1)
  - L >= N^m        (simple form)  -> infeasible with ell-bit primes (not enough primes)
"""
import math

def sieve_primes(lo, hi):
    """All primes in [lo, hi)."""
    sieve = bytearray([1]) * hi
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(hi**0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
    return [i for i in range(lo, hi) if sieve[i]]

def primes_needed(log2_bound, ell, largest_first=True):
    """How many ell-bit primes to make their product >= 2^log2_bound."""
    primes = sieve_primes(1 << (ell-1), 1 << ell)        # ell-bit primes
    order = sorted(primes, reverse=largest_first)
    acc, k = 0.0, 0
    for p in order:
        acc += math.log2(p)
        k += 1
        if acc >= log2_bound:
            return k, len(primes)
    return None, len(primes)                              # not enough ell-bit primes

# --- the verified schedule cost (same model as gidney2025_cost.py), parameterised by P ---
def ceil_div(a, b): return -(-a // b)
def lookup_cost(w): return 2**w - w - 1
def phaseup_cost(w): return round(math.sqrt(2**w))
def add_plain(r): return max(r - 1, 0)
def add_mod(r, mult): return mult * r

def per_shot(P, n, s, ell, w1, w3, w4, f, m, add_mode):
    LM = m.bit_length()
    W1 = ceil_div(m, w1); W3 = ceil_div(ell, w3); W4 = ceil_div(ell, w4)
    def aC(r, modular):
        if add_mode == 'plain': return add_plain(r)
        if add_mode == 'mixed': return add_mod(r, 2.0) if modular else add_plain(r)
        return add_mod(r, add_mode)                        # numeric mult
    rows = [
        ((P+1)*W1,          1,   ell+LM, 1,   w1,   0, 0,    False),
        (P*LM,              2,   ell+LM, 0,   0,    0, 0,    False),
        (P,                 0,   0,      1,   2*w3, 0, 0,    False),
        (P*(W3-2)*W3,       2,   ell,    1,   w3,   0, 0,    False),
        (P*W4,              1.5, f,      2.5, w4,   1, w4,   True ),
        (P*(W3-2)*2*W3,     2.5, ell,    1.5, w3,   1, w3,   True ),
        (P,                 0,   0,      0,   0,    1, 2*w3, False),
        (P*LM,              2,   ell+LM, 0,   0,    0, 0,    False),
    ]
    tot = 0.0
    for it, na, ar, nl, la, npu, pa, modular in rows:
        tot += it * (na*aC(ar, modular) + nl*lookup_cost(la) + npu*(phaseup_cost(pa) if npu else 0))
    return tot

def shots(s, p_dev=0.0125): return (s+1)/(1-p_dev)/0.99

if __name__ == "__main__":
    n, s, ell, w1, w3, w4, f, m = 2048, 8, 21, 6, 3, 5, 33, 1280
    E = shots(s)
    sym_P = ceil_div(n*m, ell*w1)
    print(f"symbolic |P| = ceil(nm/(ell*w1)) = {sym_P}")

    # generate the actual prime set for the windowed bound L >= N^(m/w1) ~ 2^(n*m/w1)
    log2_bound = n * (m / w1)                              # log2(N^(m/w1)), N ~ 2^n
    print(f"windowed bound: log2(L) >= n*m/w1 = {log2_bound:.0f}")
    for lf, name in [(True, "largest ell-bit primes first (min |P|)"),
                     (False, "smallest ell-bit primes first (ref-code style)")]:
        k, navail = primes_needed(log2_bound, ell, largest_first=lf)
        print(f"  {name}: |P| = {k}   (of {navail} available {ell}-bit primes)")

    # use the ref-code style (ascending) as the actual |P|
    actual_P, navail = primes_needed(log2_bound, ell, largest_first=False)
    print(f"\nACTUAL |P| (generated) = {actual_P}  vs symbolic {sym_P}  (ratio {sym_P/actual_P:.3f})")

    print(f"\n=== per-factoring Toffoli at the ACTUAL |P|={actual_P}  [headline 6.5e9] ===")
    for mode, lbl in [('plain','plain r-1'), ('mixed','mixed L1-3/L4-u3'), (2.0,'2n'), (2.5,'2.5n')]:
        t = per_shot(actual_P, n, s, ell, w1, w3, w4, f, m, mode) * E
        print(f"  add={lbl:18s}: {t:.3e} ({t/1e9:.2f}e9)   ratio to 6.5e9 = {t/6.5e9:.2f}")
