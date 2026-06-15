# FormalRV

**Formally-verified resource estimation for fault-tolerant Shor's algorithm — from the logical algorithm down to the physical surface-code device.**

[![Lean 4](https://img.shields.io/badge/Lean-4.29.1-blue.svg)](https://github.com/leanprover/lean4/releases/tag/v4.29.1)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.29.1-orange.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://github.com/yezhuoyang/FormalRV/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/yezhuoyang/FormalRV/actions)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](./LICENSE)

📖 **API docs:** <https://yezhuoyang.github.io/FormalRV/>

▶ **New here?** Start with [`FormalRV.Shor.StandardShor`](FormalRV/Shor/StandardShor.lean) — the standard,
textbook Shor + surface-code lattice surgery, curated as a four-step learning path
([guide](FormalRV/Shor/StandardShor/README.md)). Read it before the advanced low-overhead papers.

---

## Goal

Put Shor's algorithm, its arithmetic circuits, the logical (Pauli-product) layer, and the
quantum-error-correction stack into [Lean 4](https://leanprover.github.io/); **prove what can be
proven, emit the verified circuits as runnable code, and benchmark seven state-of-the-art resource
estimates against machine-checked bounds** — making the residue that *cannot* be proven explicit.

## Achievements

- **Axiom-free success bound.** `Shor_correct_var` / `Shor_correct_verified_no_modmult_axioms`
  (start at [`Shor/Main.lean`](FormalRV/Shor/Main.lean)): order-finding succeeds with probability
  `≥ κ/(log₂N)⁴`, `κ = 4·e⁻²/π²`. Its `#print axioms` is *only* Lean's three standard axioms — no
  project axioms, no `sorry` — instantiated with a **constructive** modular multiplier (no oracle).
- **Proof → runnable code.** The same circuits FormalRV *proves* correct are *emitted* as OpenQASM
  2/3 and Stim, and an **independent** tool (Qiskit, Stim) re-verifies the artifact without trusting
  Lean — emitted gate counts match the proved counts; Stim `has_flow` re-checks each surgery. The
  verified schedule also renders to **3D surface-code lattice-surgery layouts** (`.glb` / ray-traced)
  via [`PyCircuits/ls_compile.py`](PyCircuits/ls_compile.py) — which emits its own conflict-free
  certificate — and is translated into a `tqec`-validated `BlockGraph` by
  [`PyCircuits/draw_tqec_blocks.py`](PyCircuits/draw_tqec_blocks.py) /
  [`draw_tqec_translator.py`](PyCircuits/draw_tqec_translator.py).
- **Device scheduling + hard resource bounds.** A unified FT-scheduling framework
  ([`System/FTFramework`](FormalRV/System/FTFramework.lean)): the full ~10⁹-op RSA-2048 schedule
  defined recursively and **proven valid for all sizes** — this is the `naiveSchedule`, the
  provably-correct fully-**serial** baseline (one op at a time, no parallelism, no factory sharing;
  parallel/optimized scheduling is future work *on top of* it); a kernel-clean lower bound
  `Q·T ≥ K·fq·prod` (≈ 22.4M qubit-hours for RSA-2048) that no schedule can beat — the genuine hard
  floor; a hardware
  sensitivity analysis monotone in every device parameter; and a device-program emitter unifying
  physical operations + system calls, checked against four system invariants.
- **Seven-paper corpus.** Each estimate is bound to one typed tuple, with a machine-checked bound
  where the framework allows (table below).

## The four-layer stack

```
  L1  Algorithm        Shor + QPE + modular exponentiation + Ekerå–Håstad   ┐
  L2  Logical gadgets  adder · controlled adder · unary lookup · QFT        │ error
  L3  PPM / logical    Pauli-product measurement · magic-state cultivation  │ bounds
  L4  QEC code         parity-check matrices · stabilizer schedule · surgery ┘ propagate up
```

Each layer is a Lean structure with an explicit **inter-layer contract**; three error mechanisms
(logical/random, approximation, algorithmic-uncertainty) propagate bounds up to the success theorem.

## Worked example — the 2-bit adder, end to end

The smallest non-trivial slice of the whole stack: the verified **2-bit Cuccaro adder**
`cuccaro_n_bit_adder_full 2 0` (proven by `cuccaro_n_bit_adder_full_correct`: target `:= a+b`, read
restored), pushed through **every layer** onto a zoned hardware architecture, ending in a
**re-runnable, machine-checked resource verdict**. Full detail — the complete OpenQASM, the full
PPM program, the 192-SysCall schedule, and a self-verifying parameterized Lean file — lives in
**[`Example/`](Example/)**. Run it (and re-run it for *your own* hardware) with:

```bash
lake env lean --run Example/Adder2EndToEnd.lean   # machine-checks `schedule_fits` (native_decide) + prints the table below
```

**Architecture** — 4 zones × 100 logical-patch sites: `Data[0,100)` · `Ancilla[100,200)` ·
`Factory[200,300)` (`|C̄CZ̄⟩` magic) · `Routing[300,400)`; `Gate2q‖=1`, decoder `‖=4`, `t_react=10µs`
— **all editable** in the `EDIT HERE` block (change them, re-run, get a new verified verdict).

**Verified resource on that architecture** — every row machine-checked, nothing taken on trust:

| Layer | Resource | Value | Verified by |
|---|---|---:|---|
| L2 logical | qubits / Toffoli / T-count | 5 / 4 / 28 | `cuccaro_n_bit_adder_full_correct` (counts re-emitted by `Core/GateQASM`; the Qiskit script re-checks the modmult/Toffoli family, not this adder) |
| L3 PPM | `\|C̄CZ̄⟩` magic / joint measurements | 4 / 12 | `compileArithmeticGateToPPM` |
| System | SysCalls / **wall-clock** | 192 / **192 µs** | `scheduleWallclockUs`; **accepted by the FT invariant engine** via `schedule_fits` (proved `by native_decide` — a kernel-trusted ➗ arithmetic-tier check, *not* an axiom-clean ✅ like the Shor bound) |
| System | **wall-clock lower bound** | **≥ 72 µs** | `gate2q_capacity_lower_bound_us` (⌈72 Gate2q / 1‖⌉·1µs) |
| L4 surgery | conflict-free layout / volume | ✓ / 60 | `ls_compile` certificate |

If you tighten the hardware past feasibility, `schedule_fits` is *rejected* — that is the verdict.
(`schedule_fits` and `merge_blocks_match_ppm` are `by native_decide`: real kernel-evaluated Boolean
decisions, but ➗ arithmetic-tier — they would *not* pass the `#verify_clean` gate the headline Shor
bound passes. The 192-SysCall schedule is 12 replicas of one representative scheduling block
`surgery_ppm_A` — a trivial τ_s=3 surgery-IR timing template, so this layer checks the schedule's
timing/zone/capacity *shape*, not a syndrome-level merge (the real d=3 surface-code merge syndrome
is the neutral-atom version below) — count-matched to the 12 PPM measurements; the counts are
faithful, the 12 blocks are identical copies, not 12 independently-derived gadgets.)

<p align="center"><img src="docs/diagrams/ls_adder2_blender.png" width="440" alt="2-bit Cuccaro adder compiled to surface-code lattice surgery, ray-traced"></p>

### …and the FULL adder, end to end, on real neutral-atom hardware

The *same* 2-bit adder runs as a **complete** d=3 surface-code lattice-surgery computation on a
**neutral-atom** machine ([`Example/neutral_atom/`](Example/neutral_atom)) — every layer present, no
placeholders:

1. **It really computes `a+b`** — the measurement-based realization (real `|C̄CZ̄⟩` magic by gate
   teleportation, measurement-driven Pauli feed-forward) is simulated and matches the adder on **all
   32 inputs × 30 random measurement branches** ([`logical_adder/verify_mb_adder.py`](Example/neutral_atom/logical_adder/verify_mb_adder.py)).
2. **d=3 lattice surgery** — each of the 5 logical qubits is a `[[13,1,3]]` patch; every gate is the
   **full merged-code syndrome** (verified `surface3_zz_merge` 88 CX / `surface3_zzz_merge` 131 CX),
   each Toffoli a **real `|C̄CZ̄⟩` injection**.
3. **Detailed system schedule** — 192 SysCalls, accepted by the FT invariant engine
   (`schedule_fits`, `by native_decide` — ➗ arithmetic-tier, not an axiom-clean ✅), wall-clock 192 µs.
4. **Neutral-atom compile (ZAC, HPCA 2025)** — **107 atoms** (Memory / Ancilla / Factory / Reservoir
   zones), **1240 `CZ`**, 95 Rydberg stages, **ZAC-verified**, invariants re-proven under
   neutral-atom capacities. The GIF shows the atoms physically moving to do it:

<p align="center"><img src="Example/neutral_atom/surface3_adder2_d3_neutral_atom.gif" width="560" alt="neutral-atom atoms implementing the full distance-3 surface-code lattice-surgery 2-bit adder"></p>

## Repository layout

Each concern is a folder **with its own `README.md`** (purpose, key definitions, key theorems,
honest status):

| Folder | What it holds |
|---|---|
| [`Core/`](FormalRV/Core) | Gate IR + classical/quantum (matrix) semantics; the 7-T Toffoli = CCX proof |
| [`Arithmetic/`](FormalRV/Arithmetic) | adders, modular multiplier, unary lookup — with correctness proofs |
| [`Shor/`](FormalRV/Shor) | ★ the main theorem ([`MainAlgorithm/`](FormalRV/Shor/MainAlgorithm)), QPE, phase kickback, IQFT; the reusable Shor→PPM/emit + windowed pipeline |
| [`QEC/`](FormalRV/QEC) | qLDPC parity-check matrices, code instances, and `derivedK` (k = n − rank Hₓ − rank H_z) |
| [`PPM/`](FormalRV/PPM) | Pauli-product measurement, Pauli algebra, magic factories |
| [`LatticeSurgery/`](FormalRV/LatticeSurgery) | surgery merge/split + system-call contracts; the reusable surgery gadgets + surface-code Shor pipeline |
| [`System/`](FormalRV/System) | scheduling / device / resource-bound framework (`FTFramework`); the reusable cost / decoder / zone / latency models |
| [`Framework/`](FormalRV/Framework) | the four inter-layer contract interfaces (L1–L4) |
| [`Audit/`](FormalRV/Audit) | one folder per paper (uniform Hardware/Zones/L1–L4/Verifier) — paper-specific only; all general/reusable code lives in the framework folders above |
| [`Qualtran/`](FormalRV/Qualtran) | Qualtran `PhysicalParameters` data bridge |
| [`Codegen/`](FormalRV/Codegen) | the verified QASM / device-program emitters |

Files are named for their content and kept small (topical modules behind a `<Name>.lean` umbrella).

## Per-paper audit — claim vs. verified

Each paper has its **own folder** under [`FormalRV/Audit/`](FormalRV/Audit) with a **uniform
structure** — `Hardware` · `SystemZones` · `L1_Algorithm` · `L2_Arithmetic` · `L3_PPM` · `L4_Code` ·
`Verifier` · `README`. **All general/reusable code lives in the framework folders** (`LatticeSurgery`,
`Shor`, `System`, `QEC`, `PPM`, `Framework`, …); a paper folder holds **only that paper's specific
implementation + scheduling** and imports *only* general code — never another paper. Rigor is
**enforced on build**: each folder's `Verifier.lean` runs
`#verify_clean`, the gate that ACCEPTS a theorem only if its transitive axioms ⊆
`{propext, Classical.choice, Quot.sound}` — so a `sorry` or native-tainted axiom makes the build
**fail**. Each layer is exactly one of ✅ *verify-clean semantic* · ➗ *arithmetic-only* (`decide`) ·
⬜ *documented GAP* (never a counted number masquerading as a proof). Verify one paper with, e.g.,
`lake build FormalRV.Audit.Gidney2025`. The one cross-cutting ✅ result — order-finding success
`≥ κ/(log₂N)⁴`, N-parametric — lives in `Audit/Peng2022` and is reused by every paper's L1.

| Paper folder | Headline claim | What is machine-checked (✅ semantic · ➗ arithmetic · ⬜ gap) |
|---|---|---|
| [`CainXu2026`](FormalRV/Audit/CainXu2026) (focus) — [2603.28627](https://arxiv.org/abs/2603.28627) | RSA-2048 in ~10⁴ qubits, ~1 week | ✅ modexp PRESERVES the LP code (induction, scale-free) + LP-surgery gadget + lower≤upper soundness + verified resource upper bound + 10⁹-PPM schedule; ➗ k DERIVED from matrices, Eqs E3/E4/E9; ⬜ factory-sharing/parallelism gaps sized |
| [`GidneyEkera2021`](FormalRV/Audit/GidneyEkera2021) — [1905.09749](https://arxiv.org/abs/1905.09749) | 20M qubits, ~8 h | ✅ CAPSTONE axiom-free: 19.44M ≤ 20M, 8 h sits 2–3× under the verified time ceiling; ✅ finite-zone invariants (over-budget rejected) |
| [`Gidney2025`](FormalRV/Audit/Gidney2025) — [2505.15917](https://arxiv.org/abs/2505.15917) | <1M qubits, <1 week | ✅ CFS residue-arithmetic engine axiom-clean (faithful RNS, exact CRT, bounded truncation, Ekerå–Håstad); ✅ tally 897,864 < 10⁶; ⬜ Assumption 1 stated-never-asserted; ⬜ quantum half |
| [`Pinnacle`](FormalRV/Audit/Pinnacle) (webster-2026) — [2602.11457](https://arxiv.org/abs/2602.11457) | RSA-2048 in <100k qubits | ➗ GB code k=12 DERIVED from matrices ([[72,12,6]]); ✅ RSA instance recorded; ⬜ measurement gadget / magic engine / <100k bound (roadmap, OPEN) |
| [`Babbush2026`](FormalRV/Audit/Babbush2026) — [2603.28846](https://arxiv.org/abs/2603.28846) | ECC-256 in <500k qubits, 18–23 min | ✅ shared bound (confirms modulus-agnostic L1); ➗ verified magic-state spacetime floor; ⬜ first non-RSA, end-to-end OPEN |
| [`Xu2024`](FormalRV/Audit/Xu2024) — [2308.08648](https://arxiv.org/abs/2308.08648) | constant-overhead FTQC, 24 ms cycle | ➗ the 24,000× cycle-time outlier cross-check; ⬜ tuple (the arch the neutral-atom demo realizes) |
| [`Peng2022`](FormalRV/Audit/Peng2022) (SQIR/Coq) — [2204.07112](https://arxiv.org/abs/2204.07112) | machine-checked Shor | ✅ **the cross-cutting bound lives here** — order-finding success ≥ κ/(log₂N)⁴, N-parametric (axiom-clean) |

Legend: ✅ *Verified* semantic theorem · ➗ *Arithmetic-only* (`decide`) · ⬜ *Recorded/Assumed*.

## What is proven vs. assumed

Strict honesty taxonomy — only semantic-correctness theorems count as **Verified** (a gate count on
an unverified circuit is just counting symbols):

**Machine-checked, no custom axioms:** the Shor success-probability chain, the Cuccaro/Gidney
adders, the constant modular multiplier, the 7-T Toffoli identity, the QPE peak bound, the
Pauli/stabilizer algebra, and the schedule resource lower bound. **Out of scope (assumed by
citation):** decoder correctness & runtime, hardware physics, magic-state distillation internals,
and merged-code distance. See each folder's `README.md` for per-area status.

## Build

```bash
git clone https://github.com/yezhuoyang/FormalRV && cd FormalRV
lake exe cache get      # prebuilt mathlib (≈ minutes)
lake build              # builds the whole library
```

Check a theorem's axioms with `#print axioms FormalRV.Shor_correct_var`
(expected: `propext, Classical.choice, Quot.sound`). Emit + independently re-verify the circuits:
`lake env lean --run scripts/EmitQASM.lean` (→ Qiskit re-counts gates) and
`lake env lean --run emit_shor_demo.lean` (→ Stim `has_flow`).

## License

[MIT](./LICENSE) © 2026 John ye. Built on [mathlib](https://github.com/leanprover-community/mathlib4);
the Shor layer ports [SQIR](https://github.com/inQWIRE/SQIR); `Qualtran/` bridges
[Qualtran](https://github.com/quantumlib/Qualtran).
