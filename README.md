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

📖 **API documentation:** **<https://yezhuoyang.github.io/FormalRV/>** — a
FormalRV-only static site (definitions, theorems, and their docstrings, grouped
by concern) produced by [`scripts/gen_docs.py`](scripts/gen_docs.py), which parses
this project's `.lean` sources directly. It builds in **seconds** and documents
**only FormalRV** (mathlib is intentionally excluded), and is deployed to GitHub
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

## Device programs: one syntax for physical operations **and** system calls

The L4 `SysCall` IR unifies **physical operations** (`gate1q`, `gate2q`, `measure`, `transit`) and
**system calls** (`request_ancilla`, `request_magic`, `decode_syndrome`, `pauli_frame_update`) in a
single `Schedule`. `Codegen/SysCallEmit.lean` emits it as a timestamped `DEVICE-PROGRAM` stream, and
the schedule is *checked* against four system invariants — **I1** capacity, **I2** exclusivity,
**I3** latency / speed / decoder-reaction, **I4** factory throughput
(`System/ScheduleInvariantsExplicit.lean`, `all_invariants_ok`; the decoder-reaction budget lives in
`ZonedArch.t_react_us`). The whole flow is **build → check → emit**, and every verdict is a
`native_decide` theorem (`System/SystemInvariantExamples.lean`, checked by `lake build`).

```
DEVICE-PROGRAM 1.0;                          // one magic-state Toffoli (π/8) — PHYS + SYS
[0,12)us  SYS   request_magic      factory=3        // distill the magic state
[12,13)us PHYS  transit            q[100] via channel=1
[13,14)us PHYS  gate2q             q[0],q[100] gate=0   // lattice-surgery teleport
[14,15)us PHYS  measure            q[100] basis=0
[15,16)us SYS   decode_syndrome    round=7
[16,17)us SYS   pauli_frame_update corr=7
```

Five worked examples (two that **pass** the invariants, three that **fail**, each with a proof of its
verdict and the reason) are in [`System/README.md`](FormalRV/System#checking-system-invariants--four-worked-examples)
— e.g. two parity measurements on **distinct** ancillas pass exclusivity, but the *same* schedule
**aliasing one ancilla** is rejected by I2, two magic requests inside one distillation window are
rejected by I4, and a decode slower than the reaction budget is rejected by I3. The verdicts are
checked by `lake build`; emit the programs with `lake env lean FormalRV/Codegen/SysCallEmitDemo.lean`.

The schedule layer also carries a verified **full-scale schedule** (`NaiveSchedule.lean`, valid for
all ~10⁹ ops), a resource **lower bound** (`ScheduleLowerBound.lean`: `Q·T ≥ K·fq·prod`, ≈ 22.4M
qubit-hours for RSA-2048), and a **hardware-sensitivity** analysis proving the bound responds to
every hardware parameter (decoding speed, architecture size, routing latency, measurement time, max
parallelism — `HardwareSensitivity.lean`), instantiated for both Gidney papers.

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

**Docs:** `python scripts/gen_docs.py` regenerates the API site into `site/`
(open `site/index.html`). It needs only Python — no Lean or mathlib build — and
documents only FormalRV. CI runs the same command and publishes to GitHub Pages.

## License

[MIT](./LICENSE) © 2026 John ye. Built on
[mathlib](https://github.com/leanprover-community/mathlib4); the Shor layer ports
[SQIR](https://github.com/inQWIRE/SQIR); `Qualtran/` bridges
[Qualtran](https://github.com/quantumlib/Qualtran).
