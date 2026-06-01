# FormalRV

**Formally-verified resource estimation for fault-tolerant Shor's algorithm.**

FormalRV is a [Lean 4](https://leanprover.github.io/) library that builds a
machine-checkable framework for *benchmarking the resources* of fault-tolerant
Shor's algorithm — and applies it to seven state-of-the-art cost estimates.
Where most resource estimates live in spreadsheets and prose, FormalRV puts the
algorithm, the arithmetic circuits, the logical operations, and the error-correction
stack into Lean, proves the parts that *can* be proven, and makes the residue that
*cannot* be proven explicit and quantifiable.

[![Lean 4](https://img.shields.io/badge/Lean-4.29.1-blue.svg)](https://github.com/leanprover/lean4/releases/tag/v4.29.1)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.29.1-orange.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://github.com/yezhuoyang/FormalRV/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/yezhuoyang/FormalRV/actions)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](./LICENSE)

---

## Table of contents

- [Why this exists](#why-this-exists)
- [Headline results](#headline-results)
- [The four-layer stack](#the-four-layer-stack)
- [The seven corpus papers](#the-seven-corpus-papers)
- [What is proven, scaffolded, and assumed](#what-is-proven-scaffolded-and-assumed)
- [Repository layout](#repository-layout)
- [Building](#building)
- [How to read a verification claim](#how-to-read-a-verification-claim)
- [Background and related work](#background-and-related-work)
- [License](#license)

---

## Why this exists

A modern Shor estimate ("RSA-2048 in *N* physical qubits and *T* wall-clock
hours") is the output of a long compilation chain:

```
   Number theory  →  quantum circuit  →  logical gadgets  →  QEC code + surgery  →  hardware
```

Every link multiplies in assumptions — a per-Toffoli cycle cost here, a code
distance there, an approximation bound somewhere else. FormalRV's thesis is that
this chain is *partially* formalizable, and that the act of formalizing it,
layer by layer, reveals exactly **where the gap actually lies**. The goal is not
to "catch" any single paper, but to provide a reusable framework in which a
reviewer can plug in their own inputs and see which conclusions are theorems,
which are scaffolds awaiting a proof, and which rest irreducibly on physics or
on an unfinished proof effort.

The library is organized around a **four-layer software stack** (L1–L4, below),
with explicit inter-layer contracts, and a **corpus** of seven published Shor
estimates bound to that stack as concrete parameter instances.

---

## Headline results

Each claim below is a Lean theorem in this repository. Throughout, **"no custom
axioms"** means the theorem's full transitive dependency set, as reported by
Lean's `#print axioms`, contains *only* Lean's three standard logical axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no project-specific axioms and
no `sorry`.

| Status | Meaning |
|:------:|---------|
| ✅ **Verified** | A proven *semantic* correctness theorem (the circuit actually computes the spec), not just a gate count. |
| 🟦 **Scaffolded** | Structure (Gate IR / decidable contract / data) is present and type-checks, but the deep correctness theorem is deferred. |
| ➗ **Arithmetic-only** | A `Nat`/`decide`-level relationship between numbers; no circuit semantics behind it. |
| ⬜ **Assumed** | An `axiom` or a value imported by citation (e.g. hardware physics, decoder cost). |

### ✅ A machine-checked, axiom-free lower bound on Shor's success probability

The analytic heart of Shor's algorithm — order-finding succeeds with
non-negligible probability — is proven, not assumed:

- **`FormalRV.SQIRPort.Shor_correct_var`** *(`FormalRV/Shor/PostQFT.lean`)* —
  for any modular-multiplier oracle family satisfying the `ModMulImpl` interface,
  order-finding succeeds with probability `≥ κ / (log₂ N)⁴`, with
  `κ = 4·e⁻² / π²`. **Verified, no custom axioms.**
- **`FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms`** *(`FormalRV/Arithmetic/SQIRModMult.lean`)* —
  the *end-to-end* statement, instantiated with a constructively-defined,
  SQIR-faithful modular multiplier (no oracle placeholder). **Verified, no custom axioms.**
- **`FormalRV.SQIRPort.QPE_MMI_correct`** — the deep quantum-phase-estimation +
  modular-multiplication peak bound (`≥ 4 / (π²·r)`). **Verified, no custom axioms.**
- **`FormalRV.SQIRPort.qpe_prob_peak_bound`** *(`FormalRV/Shor/QPEAmplitude.lean`)* —
  the ideal QPE outcome probability is `≥ 4/π²`, proven from mathlib Dirichlet-kernel
  `sin`-ratio bounds. **Verified.**

This is a from-scratch Lean port of the success-probability argument from
[SQIR](https://github.com/inQWIRE/SQIR) (Peng et al. 2022, Coq). The historical,
oracle-placeholder version `Shor_correct` is retained but `@[deprecated]`; it
*does* still depend on three placeholder axioms (`f_modmult_circuit{,_MMI,_uc_well_typed}`),
which is exactly why the constructive `…_no_modmult_axioms` chain supersedes it.

All three live results are re-exported from **`FormalRV/Shor/Main.lean`** as
`FormalRV.Shor_correct_var`, `FormalRV.Shor_correct_verified_no_modmult_axioms`,
and `FormalRV.QPE_MMI_correct` — the single entry point for the headline theorem.

### ✅ Verified arithmetic gadgets (semantic correctness, not just gate counts)

- **Corrected Cuccaro ripple-carry adder** — `cuccaro_n_bit_adder_full_correct`
  / `cuccaro_n_bit_adder_full_primitive` *(`FormalRV/Arithmetic/Cuccaro/CuccaroFull.lean`,
  `…/CuccaroDecoded.lean`)*: the target register decodes to `(a + b) mod 2ⁿ`,
  the addend register is preserved, and the carry-in is restored. **Verified, kernel-clean.**
- **Patched Gidney adder** — `gidney_classical_action_with_reverse_assembled`
  and the decoded variant *(`FormalRV/Arithmetic/RippleCarryAdder.lean`)*: same
  `(a + b) mod 2ⁿ` specification, proven by induction on the carry chain. **Verified.**
- **Constant modular multiplier** *(`FormalRV/Arithmetic/SQIRModMult.lean`)*: the
  accumulator decodes to `(a · m) mod N`, with the read register zeroed and all
  control bits preserved. **Verified.**
- **Flag-controlled modular add-back** `conditionalAddConstGate_clean`
  *(`FormalRV/Arithmetic/ModularAdder.lean`)*: writes `(x + flag·N) mod 2ⁿ`,
  built without any 3-control gate. **Verified.**
- **Unary lookup** `Lookup.unary_lookup_multi_iteration_correct`
  *(`FormalRV/Arithmetic/UnaryLookup.lean`)*: the proven classical action on the
  word register (qianxu Fig. 4(b)). **Verified.**

### ✅ The 7-T Toffoli, the Pauli algebra, and the stabilizer PVM

- **`f_to_vec_CCX` / `CCX_eq_toffoliMatrix`** *(`FormalRV/Core/GateDecompositions.lean`)*:
  the textbook 7-T Toffoli decomposition equals the Toffoli matrix and acts
  correctly on computational basis states. **Verified.**
- **Pauli involution, commutation, and the eigenspace PVM**
  *(`FormalRV/PPM/LogicalState.lean`)*: `P·P = I`; commutation of Kronecker
  products from position-wise commutation; and the complete projector identities
  (idempotency, orthogonality, resolution of identity) for `{Π₊, Π₋}`. **Verified.**

### 🔎 Two findings the framework surfaced

The framework is adversarial by construction — it has already falsified two
plausible-looking constructions:

- The **original** forward-MAJ + forward-UMA Cuccaro skeleton (count-correct,
  `T = 14n`) is **provably not a correct adder** for `n ≥ 2` (Python-falsified on
  606 of 680 cases). Correctness holds only for the *reversed*-UMA variant above.
  The skeleton is retained as a stepping-stone, explicitly marked incorrect.
- The candidate `[[4,2,2]]` lattice-surgery CNOT schedule (a 5-PPM merge/split
  sequence) **provably does not implement a CNOT** — its logical conjugation
  action is the identity. Retained as a syntactic placeholder with the finding
  documented in-source *(`FormalRV/PPM/PPM.lean`)*.

---

## The four-layer stack

```
  ┌───────────────────────────────────────────────────────────────────────┐
  │  L1  Algorithm        Shor + QPE + modular exponentiation               │
  │                       + Ekerå–Håstad post-processing                    │
  ├───────────────────────────────────────────────────────────────────────┤   error
  │  L2  Logical gadgets  adder · controlled adder · unary lookup ·         │   bounds
  │                       QFT · modular reduction                           │   propagate
  ├───────────────────────────────────────────────────────────────────────┤   upward
  │  L3  PPM / logical    Pauli-product-measurement gadget set ·            │   via
  │      operations       magic-state cultivation · 15-to-1 + 8T→CCZ        │   inter-layer
  ├───────────────────────────────────────────────────────────────────────┤   contracts
  │  L4  QEC code         parity-check matrices · stabilizer schedule ·     │
  │                       (lattice surgery) · decoder [out of scope]        │
  └───────────────────────────────────────────────────────────────────────┘
```

Each layer is a Lean structure (`ShorAlgorithm`, `LogicalGateSet`, `PPMGadget`,
`QECCode`) and each adjacent pair has an **inter-layer contract** that carries an
error bound upward. Three error mechanisms are modeled in
`FormalRV/Framework/Errors.lean`:

1. **Logical / random** error (the QEC layer's residual logical error rate),
2. **Approximation** error (deterministic gate-synthesis + truncation),
3. **Algorithmic uncertainty** (Ekerå–Håstad post-processing success).

> **Honest scope note.** The eight *interface* files (`L1_Algorithm`,
> `L2_Gadgets`, `L3_PPM`, `L4_QECCode`, `Errors`, `Contracts`, …) are deliberately
> thin **contract scaffolds**: they freeze the contract surfaces and types, but
> the headline algorithm theorem `rsa_correct` is currently a `: True`
> placeholder, only the `L4 → L3` contract is stated (and proven on stub
> definitions), and the error mechanisms are `Nat` stand-ins pending `Real`
> refinements. The *substantive* proofs (the axiom-free Shor bound, the verified
> adders) live in adjacent modules and are re-exported into the stack; wiring them
> through the L1→L4 contracts is ongoing work. The genuinely-proven content at the
> framework level is the **structural scheduling / layout layer**
> (`FormalRV/System/Architecture.lean`, `…/CodedLayout.lean`): decidable
> capacity / latency / bandwidth / well-formedness invariants over zones,
> channels, syscalls and code-block layouts, instantiated with paper-cited
> neutral-atom, trapped-ion and superconducting hardware.

---

## The seven corpus papers

`FormalRV/Corpus/` binds each estimate to one tuple
`(ShorAlgorithm × QECCode × QualtranPhysicalParameters)` and records the headline
numbers the paper reports. These bindings are **recorded paper claims**, not
derivations: the tuple stores the paper's parameters and smoke `example`s confirm
storage. (Selected numbers are then connected by `decide`-checked arithmetic in
`FormalRV/Corpus/PaperClaims.lean`, e.g. the 95× qubit-hours ratio.)

| Bibkey | Paper | Code family / hardware | Headline figure(s) | Status |
|---|---|---|---|:--:|
| `cain-xu-2026` | Cain, Xu, *et al.* 2026 (**qianxu**, focus paper) | LP / bivariate-bicycle qLDPC, neutral atoms | RSA-2048 in **~10⁴ qubits**, ~1 week; ~95× lower qubit-time than GE-2021 | 🟦 |
| `gidney-ekera-2021` | Gidney & Ekerå 2021 | rotated surface code (d=27), superconducting | RSA-2048 in **20M qubits**, ~8 h, ~2.7×10⁹ Toffolis | 🟦 |
| `gidney-2025` | Gidney 2025 | yoked surface code + cultivation, superconducting | RSA-2048 in **< 1M qubits**, < 1 week | 🟦 |
| `webster-2026` | Webster *et al.* 2026 (**Pinnacle**) | generalised-bicycle qLDPC, neutral atoms | code `[[1620, 16, 24]]` (16 logical qubits) | 🟦 |
| `babbush-2026` | Babbush *et al.* 2026 | surface code (d≈14), superconducting | **ECC-256** in **< 500k qubits**, 18–23 min | 🟦 |
| `xu-2024` | Xu *et al.* 2024 | HGP / LP qLDPC, neutral atoms | code `[[544, 80, 12]]`, **24 ms** cycle (24,000× baseline) | ➗ |
| `peng-2022` | Peng *et al.* 2022 (**SQIR/Coq**) | *no QEC stack* | machine-checked gate-count bound; the L1 anchor | 🟦 |

The `FormalRV/Qualtran/Bridge.lean` module mirrors
[Qualtran](https://github.com/quantumlib/Qualtran)'s `PhysicalParameters` as Lean
data (error rate, cycle time) so corpus instances can name canonical hardware
models without round-tripping through Python. Qualtran has no qLDPC support, so
the qLDPC content here (Cain–Xu, Webster, Xu) is novel to this framework.

---

## What is proven, scaffolded, and assumed

This is the section that matters most for trusting the rest. The library applies
a strict honesty taxonomy: **a gate count on an unverified circuit is just
counting symbols in a term** — only the semantic correctness theorems above are
"Verified."

### Verified, with no custom axioms

The arithmetic / matrix-algebra core is genuinely machine-checked: the Shor
success-probability chain, the corrected Cuccaro and Gidney adders, the constant
modular multiplier, the 7-T Toffoli identity, the QPE peak bound, and the Pauli /
stabilizer PVM algebra. Each was confirmed with `#print axioms` to depend on only
`propext`, `Classical.choice`, `Quot.sound`.

### The axiom catalogue

The repository still declares the following `axiom`s, **none of which the
verified chain above depends on**. They are catalogued here precisely because
making them visible is the point of the project.

| Axiom | File | What it assumes | Live? |
|---|---|---|---|
| `f_modmult_circuit` (+ `_MMI`, `_uc_well_typed`) | `Shor/Shor.lean` | the SQIR RCIR modular-multiplier oracle exists / is correct / well-typed | `@[deprecated]`; used only by the deprecated `Shor_correct` |
| `QPE_semantics_full` | `Shor/QPE.lean` | the *general* QPE peak bound (faithful SQIR statement) | declared but **unreferenced** — the Shor chain proves the circuit-specific version constructively |
| `f_modmult_circuit`, `probability_of_success` | `Core/QuantumLib.lean` | older parallel copies of the oracle / a measurement-probability function | not used by the active chain |

In short: the genuine quantum-semantic content for Shor is *proven*; the custom
axioms are either deprecated placeholders or dead code retained for provenance.

### Deliberately out of scope (assumed by citation)

These remain `axiom`s-by-citation or supplied inputs, by design — formalizing
them is a separate multi-year effort:

- **Decoder correctness and runtime** (BP / lookup / neural decoders).
- **Hardware physics** — trap fidelity, transport error, optical addressing.
- **Magic-state distillation internals** — factories are costed black boxes;
  `EightTToCCZSpec.verifies` checks scheduling windows, not that the Clifford glue
  produces `|CCZ⟩`.
- **Merged-code distance for lattice surgery** — `verify_surgery_gadget` checks
  qLDPC degree bounds, `τ_s ≥ ⌈2d/3⌉`, and a GF(2) row-span condition, but accepts
  the merged distance `d̃ = Θ(d)` as implementer-supplied.

### A note on `sorry`

Fifteen published files contain the token `sorry` — but in the current tree
**every one is inside a comment, docstring, or section header** (often literally
the words "No sorry"), left over from the project's axiom-closure history. The CI
build is clean and the headline theorems are `sorry`-free, as the axiom checks
confirm.

---

## Repository layout

Every top-level folder is one concern, with an umbrella module
(e.g. `FormalRV/Core.lean`) that imports its whole subtree; the root
`FormalRV.lean` imports those ten umbrellas. **Start at `Shor/Main.lean`.**

```
FormalRV/
├── FormalRV.lean             ← library root: imports the 10 concern umbrellas
├── lakefile.toml             ← Lake config; depends on mathlib v4.29.1
├── lean-toolchain            ← pins leanprover/lean4:v4.29.1
└── FormalRV/
    ├── Shor/Main.lean        ★ the main theorem, re-exported (start here)
    ├── Core/                 definitions: Gate IR + classical/quantum semantics
    │     Gate · Semantics · QuantumGate · UnitarySem · PadAction · GateDecompositions
    ├── Arithmetic/           logical arithmetic gadgets + correctness
    │     Cuccaro/… · RippleCarryAdder · ModularAdder · SQIRModMult · UnaryLookup
    ├── Shor/                 ★ Shor order-finding correctness + QPE
    │     PostQFT (Shor_correct_var) · QPE · QPEAmplitude · ControlledGates · …
    ├── QEC/                  QEC code definitions (qLDPC parity matrices)
    ├── PPM/                  Pauli-product measurement, Pauli algebra, magic factory
    ├── LatticeSurgery/       surgery merge/split + PPM / system-call contracts
    ├── System/               invariants, scheduling, architecture
    ├── Framework/            the four inter-layer contracts (L1–L4, Errors, Contracts)
    ├── Corpus/               the seven corpus-paper bindings + PaperClaims
    └── Qualtran/             Qualtran PhysicalParameters bridge
```

90 source files; separating definitions from theorems within each folder is
ongoing.

## Building

**Prerequisites.** Lean 4 via [`elan`](https://github.com/leanprover/elan); the
exact toolchain (`leanprover/lean4:v4.29.1`) is selected automatically from
`lean-toolchain`.

```bash
git clone https://github.com/yezhuoyang/FormalRV
cd FormalRV
lake exe cache get      # download prebuilt mathlib (≈ minutes; avoids a long compile)
lake build              # build the whole library
```

`lake build` builds the root module, which imports the ten per-concern
umbrellas (`Core`, `Arithmetic`, `Shor`, `QEC`, `PPM`, `LatticeSurgery`,
`System`, `Framework`, `Corpus`, `Qualtran`), so one build exercises the whole
library (90 source files). A clean clone builds successfully end-to-end
(warnings only — unused-variable lints).
Continuous integration runs the same build via
[`leanprover/lean-action`](https://github.com/leanprover/lean-action) on every push.

To inspect a single theorem's axiom dependencies:

```bash
# in any file, add `#print axioms FormalRV.Shor_correct_var`
# expected: 'depends on axioms: [propext, Classical.choice, Quot.sound]'
```

---

## How to read a verification claim

Every headline number should be traceable from claim → theorem → construction
→ axioms. For example, the Shor success bound:

1. **Claim** — order-finding succeeds with probability `≥ κ/(log₂ N)⁴`.
2. **Theorem** — `FormalRV.SQIRPort.Shor_correct_var` *(`Shor/PostQFT.lean`)*.
3. **Construction** — built on `Shor_final_state = uc_eval (QPE_var_lsb) …`, the
   `controlled_R` decomposition, and `qpe_prob_peak_bound`; the end-to-end variant
   uses the constructively-defined multiplier in `Arithmetic/SQIRModMult.lean`.
4. **Axioms** — `#print axioms` reports only `propext, Classical.choice, Quot.sound`.

If a claim cannot be walked down to a `Verified` theorem this way, the taxonomy
above tells you whether it is `Scaffolded`, `Arithmetic-only`, or `Assumed`.

---

## Background and related work

- **SQIR / Peng et al. 2022** — *A Formally Certified End-to-End Implementation of
  Shor's Factorization Algorithm* (Coq). FormalRV's Shor success-probability layer
  is a Lean re-port; SQIR is the citation source for the order-finding argument.
- **Qualtran** (Google Quantum AI) — engineering-layer scaffolding for L2 gadgets;
  wrapped here as a data bridge.
- **mathlib4** — the analytic backbone (Dirichlet-kernel `sin`-ratio bounds,
  complex-matrix algebra, number theory).
- The seven corpus papers are cited in full in `FormalRV/Corpus/`.

This repository contains the Lean formalization only; the accompanying research
notes, gap analyses, and the paper draft live in a separate working repository.

---

## License

Released under the [MIT License](./LICENSE), © 2026 John ye.
