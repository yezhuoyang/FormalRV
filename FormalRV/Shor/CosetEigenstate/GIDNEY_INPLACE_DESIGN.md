# Faithful Gidney in-place coset multiplier — design + regression note

**Decision (2026-06-15, user):** build the in-place coset modular multiplier as Gidney's
*actual* two-register construction, prove the in-place spec for THAT, and only afterward
(optionally) relate the old `accYSwap ; mulFwd(N−aInv)` variant as an equivalence/optimization.
Do NOT continue proving the old variant as the main construction.

Source papers in `Library/` (gitignored): Gidney–Ekerå `1905.09749`, Gidney `1905.08488`
(approximate encoded permutations / coset / oblivious runways / deviation), Gidney `1905.07682`
(windowed arithmetic + the actual in-place modexp code), Zalka `quant-ph/0601097` (coset origin).

────────────────────────────────────────────────────────────────────────────
## §1. REGRESSION NOTE — why the naive `accYSwap ; mulFwd(N−aInv)` separable proof was invalid

The old `inplaceCosetGate = mulFwd(a) ; accYSwap ; mulFwd(N−aInv)` (one register, physical
quantum swap) was attacked with a per-runway-term basis analysis (`inplaceCosetGate_per_term`,
proven) lifted to the coset input. **Machine-checked counterexample** (`N=3, w=1, numWin=4,
a=2, aInv=2, y=1`): the output accumulator runway index is

  `q(j) = m₀ + (N−aInv)·j − Q(j) = 1, 1, 1, 2, 2`  for `j = 0,1,2,3,4`   (a STAIRCASE, not constant)

where `Q(j)` is the windowed reduction quotient (`#eval` confirmed; `j=5` overflows `2^bits`,
breaking `% N = 0`). Consequence: applying the (proven) per-term map to `cosetInput(0,y)` gives

  `Σ_j |q(j)·N⟩_acc ⊗ |S_a+jN⟩_y-register`

which is **entangled** between the two registers' runways whenever `q(j)` is non-constant.

**Why this invalidated the naive separable proof:** I was trying to prove the accumulator
"clears to `cosetState 0`" as a clean separable factor — i.e. EXACT clearing. Zalka
(`quant-ph/0601097`:180-203) shows precisely why that fails: the 2-step clear-to-zero
`|α,0⟩ → … → |0,a·α⟩` **only works if the auxiliary register is initialized to `|0⟩`**. The
coset ancilla is `cosetState(0)` (a runway *superposition*), NOT `|0⟩`, so naive clearing
entangles. The `q(j)` staircase is exactly that failure.

**The correct reading (NOT "obstruction resolved" as a theorem):** the `q(j)` shift is *not
necessarily fatal*, because coset states are designed to tolerate shifts by multiples of `N` up
to bounded bad mass (`cosetState(q·N) ≈ cosetState(0)` off the wrap — the oblivious-runway
approximate-`+N`-eigenvector property, `1905.08488`:615-626). But this MUST be proved as an
**approximate encoded-permutation statement** (off-bad correctness + Born-mass bound), never as
exact finite-basis clearing.

────────────────────────────────────────────────────────────────────────────
## §2. THE FAITHFUL CONSTRUCTION (Gidney `1905.07682` `times_equal_exp_mod`, lines 459-500)

Two SEPARATE registers `a` (data, a coset) and `b` (fresh ancilla), per exponent/factor window:

```
  b += a · k        (mod N)     -- windowed product-add, reads a (coset);  (x, 0) ↦ (x, x·k)
  a -= b · kInv     (mod N)     -- windowed product-SUBTRACT, reads b (coset); (x, x·k) ↦ (0, x·k)
  (a, b) := (b, a)              -- LOGICAL RELABEL (a free pointer rename — NOT a quantum gate)
```

Result: `a` holds `x·k` (the in-place result), `b` is restored to `cosetState(0)` (freed).
Key faithfulness points vs the old variant:
  * **fresh ancilla `b`** (so Zalka's clear-to-0 *does* apply: `b` starts as a fresh coset-0);
  * the "swap" is a **logical relabel**, not a physical `accYSwap`;
  * the uncompute is `a -= b·kInv` (**subtract**, reading the coset `b`), not `+ (N−aInv)` on
    the post-swap register.

────────────────────────────────────────────────────────────────────────────
## §3. DELIVERABLES (the user's required next steps)

1. Define a NEW gate/spec on SEPARATE registers `a`, `b`: `b += a·k` ; `a −= b·kInv` ;
   logical relabel `(a,b) := (b,a)`. (The relabel is interface-level, not a gate.)
2. Do NOT use the old quantum-`accYSwap` variant as the main construction.
3. State the **subtract leg explicitly**. If implemented as adding `N − kInv` (the additive
   complement), PROVE its equivalence to subtraction in the coset/windowed framework.
4. Prove clearing ONLY through the **approximate encoded-permutation framework**: off-bad
   correctness + Born-mass bound (`cosetState_multiWrap_agree_off` is the repo's deviation
   lemma), NOT exact `cosetState` factorization. Deviation is subadditive (`1905.08488`),
   trace distance `≤ 2√ε`.
5. This file IS deliverable 5 (the `q(j)` regression/design note).

────────────────────────────────────────────────────────────────────────────
## §4. LAYOUT CONSIDERATION (to resolve before defining the gate)

Gidney's `a` and `b` are **symmetric contiguous** modular-int registers (each serves as
*accumulator* in one pass and *address/multiplicand* in the other), with the lookup output in a
*separate* addend temp. The repo's `cuccaroAdder` windowed multiplier uses an **interleaved**
accumulator (`augendIdx = q+2i+1`, `addendIdx = q+2i+2`) + a contiguous multiplicand `yBase`,
read by `copyWindow` (contiguous). So a register in the interleaved adder layout is NOT
contiguously window-readable — the repo's asymmetric layout does not directly give Gidney's
symmetric two-register product-adds in both directions (`a→b` and `b→a`).

OPEN QUESTION for the build: instantiate the existing `windowedMulTOf`/`Adder` machinery for
two separate registers in both directions (resolving the interleave-vs-contiguous mismatch), or
introduce a contiguous-accumulator + separate-addend adder layout matching Gidney. Resolved by
the layout investigation; determines how deliverable 1's gate is defined.
