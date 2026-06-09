# Gidney ripple-carry adder

The **Gidney** in-place ripple-carry adder (arXiv:1709.06648; Qrisp
`qq_gidney_adder.py`), encoded as concrete `Gate`-IR data.

> **TL;DR** — `gidney_adder n` is THE n-bit adder. It runs a faithful forward
> cascade, a final-CX cascade (stamps the sum), then a reverse cascade, on
> `3n+2` qubits, leaving the **target register holding `(a + b) mod 2ⁿ`** and
> the read register restored to `a`. The base adder leaves the carry register
> **dirty**; the carry-clearing **patched** variant
> (`gidney_adder_full_faithful_no_measurement_patched`) returns it to 0 and is
> the one the modular-adder layer builds on.

## Where everything lives (the spine)

| Concern | File | Headline |
|---|---|---|
| **Definition** | [`RippleCarryAdderDef.lean`](RippleCarryAdderDef.lean) | `gidney_adder` (+ `…_patched`) |
| **Correctness** | [`RippleCarryAdderCorrectness.lean`](RippleCarryAdderCorrectness.lean) | `gidney_adder_correct`, `gidney_adder_correct_full` |
| **Resource** | [`RippleCarryAdderResource.lean`](RippleCarryAdderResource.lean) | `gidney_adder_tcount` (= 14·n), `gidney_adder_verified` |
| **Example + QASM** | [`RippleCarryAdderExample.lean`](RippleCarryAdderExample.lean) | `GidneyAdder : Gadget`, `emitQASM GidneyAdder n` |

Definition support (one file per job, no proofs): `RippleCarryAdderSpec.lean`
(classical `carry`/`sumfb`, `adder_sum_bit_classical`, `adder_input_F`,
decoders, test fixtures), `RippleCarryAdderPostStates.lean` (basis-state
post-state functions + invariant predicates), and
`RippleCarryAdderCostSkeleton.lean` (the deliberately-wrong cost-only skeleton).

Heavy supporting proofs (read only if auditing the proofs) live in
`RippleCarryAdderForwardAndCost.lean` (forward correctness, per-step/cascade
reversibility, T-counts), `RippleCarryAdderClassicalBridge.lean` (the classical
`carry`/`sumfb` → `testBit` bridge + cascade invariants),
`RippleCarryAdderDecideWitnesses.lean` (reverse-cascade lemmas + smoke
witnesses), `RippleCarryAdderPropagationReverse.lean` (assembled headline +
`applyNat` bridge + patched carry-clearing), and
`RippleCarryAdderUncomputeCascade.lean` (packaged primitive + WellTyped).
Auditors should read the spine files; the proofs are pushed out of the way.

## Qubit layout (`3n + 2` qubits, interleaved LSB-first)

```
read[i]   = 3·i      : bit i of a        (read register, preserved)
target[i] = 3·i + 1  : bit i of b  →  bit i of (a+b) mod 2ⁿ   (target register)
carry[i]  = 3·i + 2  : carry chain  (dirty in the base adder; cleared by …_patched)
```

## The size parameter `n` (= bits per addend)

`n` is the number of bits of each addend `a` and `b`. The adder acts on
`adder_n_qubits n = 3·n + 2` qubits and computes `(a+b) mod 2ⁿ`. To change the
size, pass a different `n` everywhere — e.g. `emitQASM GidneyAdder 8`, or
`gidney_adder_tcount 6` for the 8-bit adder's T-count.

## Correctness (the theorems to audit)

`gidney_adder_correct (n a b) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n)`:

```
∀ i, i < n →
  Gate.applyNat (gidney_adder n) (adder_input_F n a b) (target_idx i)
    = adder_sum_bit_classical a b i            -- = (a + b).testBit i
```

`gidney_adder_read_preserved` additionally gives `read_idx i = a.testBit i`.

`gidney_adder_correct_full` is the **carry-clean patched bundle** (the reusable
primitive `gidney_adder_patched_primitive`): for `bits ≥ 2`, the patched adder
is `WellTyped` on `3·bits + 2` qubits, decodes the target to `(a+b) mod 2^bits`,
preserves the read register, **and clears the carry register**.

## Resource (after correctness)

- `gidney_adder_tcount` : T-count = **14·n** (n forward + n reverse Toffolis,
  7 T each; the final-CX cascade is T-free).
- `gidney_adder_tcount_vs_measurement` : that `14·n` is exactly **twice** the
  `7·n` figure achievable with Gidney's measurement-based uncomputation (qianxu
  Eq. E3). This factor-of-2 is the honestly-surfaced no-measurement vs.
  measurement gap (the optimization is costed but not gate-level formalized).
- `gidney_adder_RSA2048_tcount` : at `q_A = 33` (RSA-2048), T-count = **462**,
  matching the `gidney_adder_RSA2048_T_count_verified` paper-claim anchor.
- `gidney_adder_patched_wellTyped` : the patched adder is WellTyped on `3n+2`
  qubits.
- `gidney_adder_verified` : resource **after** correctness — the one circuit is
  simultaneously sum-correct, read-preserving, and `14·n` T-gates.

## Emit OpenQASM for any N (uniform framework)

The adder exposes a `Gadget` descriptor (`GidneyAdder`) and emits through the
project-wide `emitQASM` framework in
[`Codegen/QASMEmit.lean`](../../Codegen/QASMEmit.lean):

```lean
#eval IO.println (emitQASM GidneyAdder 3)   -- 3-bit adder as OpenQASM 2.0
```

`GidneyAdder : Gadget := { name := "gidney_adder", circuit := fun n => gidney_adder n }`,
and `GidneyAdder.tcount n` is *exactly* the proven closed form `14·n`. Every
other arithmetic gadget defines its own `Gadget` and emits identically.

## Circuit diagram (2-bit adder)

Reproduce from the verified native-basis QASM (`GidneyAdder.toQASMNative 2`):
`lake env lean …/RippleCarryAdderExample.lean` (writes
`diagrams/gidney_adder_2bit.qasm`), then
`python scripts/draw_qasm.py diagrams/gidney_adder_2bit.qasm diagrams/gidney_adder_2bit.png`.

## ⚠️ Cost-only skeleton (`RippleCarryAdderCostSkeleton.lean`)

A deliberately-WRONG `gidney_adder_bit_step` / `gidney_adder_forward` /
`gidney_adder_uncompute` / `gidney_adder_full` family lives in its own file,
`RippleCarryAdderCostSkeleton.lean`. It has the right Toffoli count but the
wrong logical action (it omits the carry-propagation CXs) and is kept ONLY for
T-count accounting (it underlies the measurement-gap theorems). It is **not**
the correct adder — do not build on it.
