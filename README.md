# FormalRV

**Formally-verified resource estimation for fault-tolerant Shor's algorithm.**

FormalRV is a [Lean 4](https://leanprover.github.io/) library that builds a
machine-checkable framework for *benchmarking the resources* of fault-tolerant
Shor's algorithm, and applies it to seven state-of-the-art cost estimates. It
puts the algorithm, the arithmetic circuits, the logical operations, and the
error-correction stack into Lean, proves the parts that *can* be proven, and
makes the residue that *cannot* be proven explicit and quantifiable.

[![Lean 4](https://img.shields.io/badge/Lean-4.29.1-blue.svg)](https://github.com/leanprover/lean4/releases/tag/v4.29.1)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.29.1-orange.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://github.com/yezhuoyang/FormalRV/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/yezhuoyang/FormalRV/actions)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](./LICENSE)

📖 **API documentation:** **<https://yezhuoyang.github.io/FormalRV/>** — generated
by [`doc-gen4`](https://github.com/leanprover/doc-gen4) and deployed to GitHub
Pages by the [`docs.yml`](.github/workflows/docs.yml) Actions workflow on every
push to `main`.

---

## The headline result

A machine-checked, **axiom-free** lower bound on Shor's order-finding success
probability — its full `#print axioms` dependency set is *only* Lean's three
standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`), with no
project-specific axioms and no `sorry`:

- **`FormalRV.Shor_correct_var`** — for any modular-multiplier oracle satisfying
  the `ModMulImpl` interface, order-finding succeeds with probability
  `≥ κ / (log₂ N)⁴`, `κ = 4·e⁻²/π²`.
- **`FormalRV.Shor_correct_verified_no_modmult_axioms`** — the end-to-end
  statement, instantiated with a *constructively-defined*, SQIR-faithful modular
  multiplier (no oracle placeholder).

Both are re-exported from **[`FormalRV/Shor/Main.lean`](FormalRV/Shor/Main.lean)**
— start there. This is a from-scratch Lean port of the order-finding argument
from [SQIR](https://github.com/inQWIRE/SQIR) (Peng et al. 2022, Coq).

## The four-layer stack

```
  L1  Algorithm        Shor + QPE + modular exponentiation + Ekerå–Håstad   ┐
  L2  Logical gadgets  adder · controlled adder · unary lookup · QFT        │ error
  L3  PPM / logical    Pauli-product measurement · magic-state cultivation  │ bounds
  L4  QEC code         parity-check matrices · stabilizer schedule · surgery ┘ propagate up
```

Each layer is a Lean structure with an explicit **inter-layer contract**; three
error mechanisms (logical/random, approximation, algorithmic-uncertainty)
propagate bounds upward toward the success-probability theorem.

## Repository layout

Each concern is a folder **with its own `README.md`** (purpose + key definitions
+ key theorems + honest status):

| Folder | What it holds |
|---|---|
| [`Core/`](FormalRV/Core) | Gate IR + classical/quantum (matrix) semantics; the 7-T Toffoli = CCX proof |
| [`Arithmetic/`](FormalRV/Arithmetic) | adders, modular multiplier, unary lookup — with semantic-correctness proofs |
| [`Shor/`](FormalRV/Shor) | ★ the main theorem + QPE, phase kickback, inverse-QFT |
| [`QEC/`](FormalRV/QEC) | qLDPC parity-check matrices and code instances |
| [`PPM/`](FormalRV/PPM) | Pauli-product measurement, Pauli algebra, magic factories |
| [`LatticeSurgery/`](FormalRV/LatticeSurgery) | surgery merge/split + system-call contracts |
| [`System/`](FormalRV/System) | scheduling / layout / architecture invariants |
| [`Framework/`](FormalRV/Framework) | the four inter-layer contract interfaces (L1–L4) |
| [`Corpus/`](FormalRV/Corpus) | the seven corpus-paper bindings + paper-claim constants |
| [`Qualtran/`](FormalRV/Qualtran) | Qualtran `PhysicalParameters` data bridge |

Large proof files are split into a `<Name>/` sub-folder of shorter modules —
`Defs.lean` + `Proofs1..N.lean` where definitions and theorems separate cleanly,
or `Part1..N.lean` (order-preserving) otherwise.

## The seven corpus papers

`Corpus/` binds each estimate to one `(ShorAlgorithm × QECCode ×
QualtranPhysicalParameters)` tuple and records the headline numbers the paper
reports. These are **recorded paper claims**, not derivations (parity matrices
are stubbed); the genuine semantic content lives in `Core/`, `Arithmetic/`,
`Shor/`, and `PPM/`.

| Bibkey | Code family / hardware | Headline figure(s) |
|---|---|---|
| `cain-xu-2026` (qianxu, focus) | LP / bivariate-bicycle qLDPC, neutral atoms | RSA-2048 in **~10⁴ qubits**, ~1 week |
| `gidney-ekera-2021` | rotated surface code (d=27), superconducting | **20M qubits**, ~8 h, ~2.7×10⁹ Toffolis |
| `gidney-2025` | yoked surface code + cultivation | **< 1M qubits**, < 1 week |
| `webster-2026` (Pinnacle) | generalised-bicycle qLDPC, neutral atoms | code `[[1620, 16, 24]]` |
| `babbush-2026` | surface code (d≈14), superconducting | **ECC-256** in **< 500k qubits**, 18–23 min |
| `xu-2024` | HGP / LP qLDPC, neutral atoms | `[[544, 80, 12]]`, **24 ms** cycle |
| `peng-2022` (SQIR/Coq) | *no QEC stack* | machine-checked gate-count bound |

## What is proven vs. assumed

A strict honesty taxonomy is used throughout (a gate count on an unverified
circuit is just counting symbols — only semantic-correctness theorems are
"Verified"):

| Status | Meaning |
|:--:|---|
| ✅ **Verified** | a proven *semantic* correctness theorem |
| 🟦 **Scaffolded** | structure present, deep proof deferred |
| ➗ **Arithmetic-only** | a `Nat`/`decide`-level fact |
| ⬜ **Assumed** | an `axiom` or value imported by citation |

**Genuinely machine-checked, no custom axioms:** the Shor success-probability
chain, the corrected Cuccaro / patched Gidney adders, the constant modular
multiplier, the 7-T Toffoli identity, the QPE peak bound, and the Pauli /
stabilizer-PVM algebra. **Deliberately out of scope** (assumed by citation):
decoder correctness & runtime, hardware physics, magic-state distillation
internals, and merged-code distance for lattice surgery. A handful of
SQIR-ported placeholder axioms remain in the tree but are deprecated or unused
by the verified chain. See each folder's `README.md` for per-area status.

## Building

Lean 4 via [`elan`](https://github.com/leanprover/elan); the toolchain
(`leanprover/lean4:v4.29.1`) is selected automatically from `lean-toolchain`.

```bash
git clone https://github.com/yezhuoyang/FormalRV
cd FormalRV
lake exe cache get      # prebuilt mathlib (≈ minutes)
lake build              # build the whole library (one build covers all 10 concern umbrellas)
```

Inspect a theorem's axioms with `#print axioms FormalRV.Shor_correct_var`
(expected: `propext, Classical.choice, Quot.sound`).

**Docs:** `lake -R -Kenv=docs build FormalRV:docs` regenerates the API site into
`.lake/build/doc/` (doc-gen4 is an optional dependency, gated so plain `lake
build` never pulls it in). CI does this and publishes to GitHub Pages.

## License

[MIT](./LICENSE) © 2026 John ye. Built on
[mathlib](https://github.com/leanprover-community/mathlib4); the Shor layer ports
[SQIR](https://github.com/inQWIRE/SQIR); `Qualtran/` bridges
[Qualtran](https://github.com/quantumlib/Qualtran).
