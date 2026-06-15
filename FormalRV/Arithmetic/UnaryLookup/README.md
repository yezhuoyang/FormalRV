# Unary-iteration QROM lookup (Babbush et al.)

The **table lookup** ("QROM read", Babbush et al. 1805.03662 §3A) that windowed
arithmetic is built on: given a `w`-bit address register, XOR the addressed
table row `T[addr]` into a `W`-bit word register, touching nothing else. This
folder contains **two verified variants** — the faithful per-row unary
iteration, and the Gray-code/sawtooth read that removes the per-row address
re-decode — plus the exact identity relating their costs.

## Spine

| Concern | File | Headline |
|---|---|---|
| **Definition (faithful)** | [`UnaryLookupDefinitions.lean`](UnaryLookupDefinitions.lean) | `unary_lookup_iteration`, `unary_lookup_multi_iteration` (+ the qubit indexing `ulookup_*_idx`, post-state machinery) |
| **Resource (faithful)** | [`UnaryLookupGateDerivations.lean`](UnaryLookupGateDerivations.lean) | `tcount_unary_lookup_multi_iteration` (= `14·n_addr` T per iteration), `unary_lookup_two_factor_gap`, `unary_lookup_tcount_matches_PaperClaims` |
| **Correctness (faithful)** | [`UnaryLookupIterationCorrectness.lean`](UnaryLookupIterationCorrectness.lean) | `Lookup.unary_lookup_iteration_correct`, `Lookup.unary_lookup_multi_iteration_correct` |
| **Definition + Correctness + Resource (Gray-code)** | [`UnaryLookupGrayCode.lean`](UnaryLookupGrayCode.lean) | `grayLookupReadAt`, `grayLookupReadAt_selects_word` / `_selects` / `_frame`, `tcount_grayLookupReadAt`, `toffoliCount_grayLookupReadAt`, exact gap `tcount_lookupReadAt_eq_w_mul_gray` |

> The umbrella `import FormalRV.Arithmetic.UnaryLookup` pulls in the three
> faithful-variant files; `UnaryLookupGrayCode` must be imported directly
> (`import FormalRV.Arithmetic.UnaryLookup.UnaryLookupGrayCode`).

## The two variants

**Faithful unary iteration** (`unary_lookup_multi_iteration`): one iteration per
address value — X-flip the address bits to match the row, run the prefix-AND
`CCX` cascade through the AND-ancillas, fire the word-CNOTs for that row's table
bits, uncompute the cascade, unflip. Each iteration costs `2·n_addr` Toffolis
(`14·n_addr` T, cascade + uncompute), so a full `2^w`-row read costs
`2·w·2^w` Toffolis. Headline:
`Lookup.unary_lookup_multi_iteration_correct` — the post-state at every word
position is `f p ⊕ (cumulative XOR of the triggered rows' contributions)`, with
ctrl/address/AND bits preserved (per-register preservation lemmas alongside).

**Gray-code / sawtooth read** (`grayLookupReadAt w pos W T`): walks the address
space in Gray-code order so consecutive rows differ in one ladder step — the
address is decoded once, not per row. Headlines:
`grayLookupReadAt_selects_word` (reads exactly the addressed row, at positions
`pos j`), `grayLookupReadAt_frame`, and
`toffoliCount_grayLookupReadAt` `= 2·(2^w − 1)` Toffolis.

**The exact gap** (`tcount_lookupReadAt_eq_w_mul_gray`, T-count;
`toffoliCount_lookupReadAt_eq_w_mul_gray`, Toffolis): the faithful read costs
exactly `w` times the Gray-code read plus `w` ENTER/EXIT pairs —
`2·w·2^w = w·(2·(2^w − 1) + 2)`. The two reads are **contract-identical**
(same selection + frame statements, same address/ancilla layout), so consumers
swap between them mechanically.

## Qubit layout (faithful read; `unary_lookup_n_qubits n_addr n_word` qubits)

```
ctrl                    = 0
address[i]              = 1 + 2·i            (i = 0 … n_addr−1)
and[i]   (AND ancilla)  = 1 + 2·i + 1
word[j]                 = 1 + 2·n_addr + j   (faithful default; both reads
                                              also take a position map `pos`)
```

`grayLookupReadAt` (and the Gate-level faithful wrapper `lookupReadAt`, below)
take the word positions as a map `pos : Nat → Nat`, so the looked-up word can be
written **directly onto an adder's addend register** — this is how the windowed
multiplier consumes it.

## Who consumes this folder

- `Windowed/WindowedCircuit.lean` — defines the table-indexed Gate-level read
  `lookupReadAt w pos W T := unary_lookup_multi_iteration w (rows of T)` and the
  windowed multiplier on top of it.
- `Windowed/WindowedLookupSelect.lean` — proves `lookupReadAt_selects` (the
  faithful read selects exactly the addressed table row) from this folder's
  iteration correctness.
- `Windowed/WindowedGrayLookup.lean` — the windowed multiplier over the
  Gray-code read (`grayWindowedMulCircuitOf_correct`).
- `Shor/MeasUncompute.lean` / `Shor/MeasUncomputeAt.lean` — the **EGate
  merged-AND-tree QROM variant** (`unaryQROM` / position-parameterized
  `unaryQROMAt`) used by the *measurement-based-uncompute* lookup-add
  (`babbushLookupAdd(At)`); `(2^w − 1)`-Toffoli read, measure-cleared instead of
  unitarily uncomputed.
- `Shor/PhaseLookupFixup.lean` — the concrete phase-lookup fixup for measured
  uncompute, built on the Gray-code read.

For which variant to import when auditing a specific paper claim, use the
**auditor's routing table** in [`../Windowed/README.md`](../Windowed/README.md).

## Honest notes

- `unary_lookup_stub` (`UnaryLookupDefinitions.lean`) and the "Stub" comment
  above it are **historical leftovers** from before the circuit landed; the real
  circuit is `unary_lookup_multi_iteration` and everything below it. The stub is
  not used by any proof.
- `unary_lookup_multi_iteration` is parameterized by explicit per-row
  `(addr_flips, word_cnots)` data; the table-driven instantiation (rows computed
  from `T`) is `lookupReadAt` in `Windowed/WindowedCircuit.lean`.
- The paper's headline `2^w` Toffolis per lookup needs BOTH optimizations on top
  of the faithful `2·w·2^w`: the Gray-code factor `w` (proven here, exact-gap
  identity) and the measurement-based-uncompute factor 2 (proven at the logical
  density layer — see `Shor/MeasuredLookupUncompute` and the routing table).
