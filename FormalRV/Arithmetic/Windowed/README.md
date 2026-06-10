# Windowed arithmetic — adder-generic lookup-based multiplication & exponentiation

Gidney–Ekerå-style windowed arithmetic (arXiv:1905.07682, 1905.09749): instead of
one controlled operation per bit, group bits into **windows** and do one QROM
table-lookup + one addition per window. This folder realizes it **generically
over the adder and the window size**, with kernel-level value theorems.

## The interface story (what plugs into what)

```
ANY  Adder            ──┐
  (Arithmetic/Adder)    ├──>  windowedMulCircuitOf A w …      verified product-multiplier
ANY  window size w    ──┘       (windowedMulCircuitOf_correct: decodeAcc = (a·y) mod 2^bits)

ANY  modular multiplier (EncodeRoundTripModMul)
                        ──>  .toVerifiedModMulFamily → QPE → Shor success bound
                              (Shor/MultiplierInstances: cuccaroMultiplier, gidneyMultiplier)

windowed EXPONENT      ──>  expWindowPassOf A wE wM …          two-level concatenated lookup
  (this folder)               (expWindowPassOf_correct: acc·= g_k^{e-window} · y mod 2^bits)
```

- **`Adder`** (`Arithmetic/Adder.lean`): a layout-parametric reversible adder —
  index functions (`augendIdx`/`addendIdx`), an `ancClean` precondition, and a
  decode-level correctness contract. **Encoding is unified by the index
  functions**: windowed code writes the looked-up table row at `A.addendIdx` and
  reads the running sum at `A.augendIdx`, never knowing the adder's internals.
  Two proven instances: `cuccaroAdder` (block span `2n+1`) and `gidneyAdder`
  (span `3n+2`; the base-0 Gidney gate is rebased by a generic `Gate.shiftBy`).
- **Window size `w`** is a plain `Nat` parameter everywhere. `w = 1` is the
  bit-serial degenerate case.
- **`EncodeRoundTripModMul`** (`Shor/WindowedShorConnection.lean`) is THE
  modular-multiplier interface (`gate c` : multiply-by-`c` with
  `|x⟩|0⟩ ↦ |(c·x) mod N⟩|0⟩`); `Shor/MultiplierInstances.lean` instantiates it
  for both ripple lineages, and `toVerifiedModMulFamily` →
  `shor_correct_of_encodeRoundTrip` is the generic "multiplier → Shor" payoff.

## The headline theorems (all kernel-clean, no `sorry`/`native_decide`)

| Theorem | Statement (informal) | File |
|---|---|---|
| `windowedMulCircuitOf_correct` | for ANY `A : Adder`, `w > 0`: the windowed multiplier decodes the accumulator to `(a·y) mod 2^bits` | `WindowedCircuitCorrect.lean` |
| `windowedMulCircuit_correct_cuccaro` / `_gidney` | the same circuit, instantiated at each adder | `WindowedCircuitCorrect.lean` |
| `expWindowPassOf_correct` | one exponent-window pass multiply-accumulates by the **exponent-window-selected** constant: `acc = (g_k^{window wE e k} · y) mod 2^bits` | `WindowedExpStep.lean` |
| `tcount_windowedMulCircuitOf` | T-count `= numWin · (28·w·2^w + tcount(A.circuit))`, generic over `A` | `WindowedCircuit.lean` |
| `lookupReadAt_selects` | the QROM reads exactly the addressed table row | `WindowedLookupSelect.lean` |

Supporting: `WindowedCopySemantics.lean` (window-copy CX-cascade semantics),
`WindowedArith.lean` (the pure number theory), `WindowedCostModel.lean` (the
GE2021 paper-accounting formulas), `WindowedWidth.lean` (structural qubit counts).

### Why the windowed *exponent* is a concatenated address (design note)

A black-box "add a control to any multiplier" is **impossible** in the
`X/CX/CCX` Gate IR (there is no controlled-everything combinator — controlling
`CCX` needs `CCCX`). So windowed exponentiation is faithfully formalized the way
Gidney's paper actually does it: the exponent window and the multiplier window
are **concatenated into one QROM address** (`addr = v + 2^wM·e_k`,
`WindowedArith.address_concat`), and the table row already contains
`g_k^{e_k} · (2^wM)^j · v`. One pass = the quantum-selected constant multiply.

## Concrete head-to-head: same circuit, two adders (`bits = 4`, `a = 3`)

Computed by `#eval` from the actual `Gate` terms (`Example.lean`):

| `w` | windows | **Cuccaro**: Toffoli / gates / qubits | **Gidney**: Toffoli / gates / qubits |
|---|---|---|---|
| 1 | 4 | 64 / 166 / **16** | 64 / 206 / **21** |
| 2 | 2 | 80 / 172 / **18** | 80 / 192 / **23** |
| 3 | 2 | 208 / 386 / **22** | 208 / 406 / **27** |
| 4 | 1 | 264 / 480 / **22** | 264 / 490 / **27** |

Both adders cost **identical Toffolis** (each is a 2-Toffoli-per-bit ripple);
they differ in T-free CX/X overhead and in **qubit width** (Cuccaro's `2n+1`
block vs Gidney's `3n+2`) — the trade is read off the verified structure, not
asserted. At this toy `bits = 4` the lookup term `4·w·2^w` dominates, so larger
windows *cost* more; windowing pays at production sizes, where the per-window
adder term `2·bits` dominates (at `bits = 2048`, `w = 11 ≈ lg n` minimizes
`numWin·(4·w·2^w + 2·bits)` — the paper's `O(n²/lg n)` per multiply).

## Worked example: `acc ← (3·y) mod 4` at `w = 2` (1 window)

The exact compiled circuit on **both** adders — same table, same lookup, same
y-copy; only the adder block differs. Verified instance:
`windowedMulCircuit_correct_cuccaro 2 2 3 1 y …` (and `_gidney`).

**Cuccaro** (12 qubits, 72 gates, 36 Toffoli):

![windowed multiplier, Cuccaro adder](diagrams/windowed_mul_cuccaro_w2.png)

**Gidney** (15 qubits, 74 gates, 36 Toffoli):

![windowed multiplier, Gidney adder](diagrams/windowed_mul_gidney_w2.png)

Reading the (Cuccaro) picture left-to-right: CX-copy of the `y`-window into the
address wires `a0,a1` → the four unary-iteration QROM rows (X-flips on the
address, `CCX` prefix-AND cascade through `s0,s1`, word-CNOTs into the table-word
wires `r0,r1` — only the row matching the address fires) → the Cuccaro ripple
(`cin,t*,r*`) adds the looked-up row `3·(2²)⁰·v = 3v` into the accumulator `t*`
→ the second QROM read clears `r*` → the uncopy clears the address. Output:
`acc (t1,t0) = (3·y) mod 4`, everything else restored.

| port | input | output |
|---|---|---|
| `ctrl` | 1 | 1 |
| `y1,y0` | `y` | `y` (preserved) |
| `t1,t0` (acc) | 0 | `(3·y) mod 4` |
| addr `a*`, AND `s*`, word `r*`, `cin` | 0 | 0 (restored) |

Reproduce: `lake env lean …/Windowed/Example.lean` writes the `.qasm` files,
then `python scripts/draw_qasm.py diagrams/windowed_mul_cuccaro_w2.qasm
diagrams/windowed_mul_cuccaro_w2.png diagrams/windowed_mul_cuccaro_w2.io.json`.

## Honest scope notes

- The windowed multiplier here is the **product-adder** `acc += a·y mod 2^bits`
  (Gidney's coset/deferred-modular-reduction design); it is NOT a per-window
  mod-`N` reducer. The exactly-modular in-place multiplier feeding the verified
  Shor pipeline is the separate `windowedInplaceModMulGate` /
  `modmult_MCP_gate` lineage (see `Shor/WindowedShorConnection.lean` and
  `Arithmetic/ModMult/`).
- The QROM here is the faithful no-measurement unary iteration
  (`2·w·2^w` Toffolis per read). The paper's `2^w`-Toffoli lookup additionally
  needs Gray-code amortization + measurement-based uncompute — costed in
  `WindowedCostModel.lean`/`UnaryLookup`, deliberately not gate-level here; the
  gap is tracked in `System/ResourceAuditGaps`.
- `expWindowPassOf_correct` is the per-pass theorem; composing passes over all
  exponent windows into the full windowed modexp (and into QPE) remains the
  known-open composition flagged at `WindowedExpCorrect`/`BabbushLookupAddValueSpec`.
