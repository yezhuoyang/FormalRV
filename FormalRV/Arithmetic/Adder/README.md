# The `Adder` interface — any adder, one contract

A **layout-parametric, reversible, in-place binary adder interface** over the
`Gate` IR (`../Adder.lean`), with two proven instances in this folder. The point
is that higher gadgets — the windowed multiplier and exponent — compose **ANY**
adder without knowing its internal qubit layout, and their correctness and
resource theorems are stated once, generically over `A : Adder`.

## Spine

| Concern | File | Headline |
|---|---|---|
| **Interface** | [`../Adder.lean`](../Adder.lean) | `structure Adder`, `decodeReg`, `inBlock` |
| **Cuccaro instance** | [`Cuccaro.lean`](Cuccaro.lean) | `cuccaroAdder` (block span `2n+1`) |
| **Gidney instance** | [`Gidney.lean`](Gidney.lean) | `gidneyAdder` (block span `3n+2`) + the generic relabelling `Gate.shiftBy` |

## The interface (fields + contract)

At base offset `q` and width `n`, `circuit n q` runs on the block
`[q, q + span n)` and computes `augend ← (augend + addend) mod 2^n` in place.

Data fields: `span` (qubits used), `augendIdx q i` (where running-sum bit `i`
lives; modified in place), `addendIdx q i` (where addend bit `i` lives;
restored), `ancClean f n q` (the internal carry/ancilla block is 0), `circuit`.

Contract obligations (all proof fields of the structure):
`sumCorrect` (the augend register decodes to `(augend + addend) mod 2^n`),
`addendRestored`, `ancRestored` (cleanliness is returned, so repeated adds stay
in-contract — this is what lets one adder run once per window, inductively),
`frame` (nothing outside the block moves), `wellTyped`, plus position sanity
(`augendIdx_inBlock`/`addendIdx_inBlock`/`addendIdx_inj`/
`augend_addend_disjoint`/`ancClean_ext`).

**Why index functions unify encodings:** there is no global re-layout. A
consumer writes its data at `A.addendIdx`, runs `A.circuit`, and reads the
result at `A.augendIdx` — the windowed code writes the looked-up QROM table row
onto the addend positions and reads the running product off the augend
positions, never seeing whether the adder interleaves stride-2 or stride-3.

## The two instances

| | `cuccaroAdder` | `gidneyAdder` |
|---|---|---|
| Base circuit | `cuccaro_n_bit_adder_full` (MAJ/UMA, `Arithmetic/Cuccaro`) | `gidney_adder_full_faithful_no_measurement_patched` (`Arithmetic/RippleCarryAdder`) |
| Span | `2n+1` | `3n+2` |
| Layout | `q` carry-in; `q+2i+1` augend; `q+2i+2` addend | `q+3i` addend; `q+3i+1` augend; `q+3i+2` carry |
| `ancClean` | carry-in qubit is 0 | all carry bits are 0 |
| Quirk | base-parametric already | base circuit is hard-wired at base 0, so it is rebased by the generic **`Gate.shiftBy k`** (add `k` to every qubit index; transfer lemmas `Gate.shiftBy_applyNat`, `Gate.shiftBy_applyNat_below`, `Gate.shiftBy_wellTyped`, all in `Gidney.lean`); widths `n ≤ 1` get bespoke correct circuits (the degenerate base adder is not a 1-bit adder) |

## Who consumes it

The windowed-arithmetic files in `../Windowed/` take `(A : Adder)` as their
first argument: `WindowedCircuit.lean` (`windowedMulCircuitOf A w …`),
`WindowedCircuitCorrect.lean` (`windowedMulCircuitOf_correct` — the value
theorem for ANY `A`, instantiated as `windowedMulCircuit_correct_cuccaro` /
`_gidney`), `WindowedGrayLookup.lean`, `WindowedExpStep.lean`, and
`WindowedInPlace.lean`.

## Resource counts are `A`-parametric

The generic count theorems leave the adder's own cost as a parameter, e.g.

```
tcount_windowedMulCircuitOf :
  tcount (windowedMulCircuitOf A w bits a numWin)
    = numWin * (28·w·2^w + tcount (A.circuit bits (1 + 2·w)))
```

(`Windowed/WindowedCircuit.lean`) — plugging in `tcount (cuccaro_… ) = 14·bits`
gives the closed Cuccaro corollaries. Both instances cost identical Toffolis
(each is a 2-Toffoli-per-bit ripple); they differ in T-free CX/X overhead and in
qubit width — see the head-to-head table in
[`../Windowed/README.md`](../Windowed/README.md).
