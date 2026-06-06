# `FormalRV/Audit/` — per-paper audit, reader-verifiable

One file per paper. Each file **redefines nothing** — it `import`s the real
definitions and theorems from [`Corpus/`](../Corpus) (and the shared
[`Framework/`](../Framework) · [`Shor/`](../Shor) folders) and exposes them with
`#check` / `#print axioms`, wrapped in a docstring that states, for that paper:

1. **the headline claim**,
2. **the settings a reader should check** match the paper (the recorded inputs),
3. **our approach** to verifying it,
4. **the gap we determined** (claim vs. what is machine-checked), and
5. **what is still unsolved**.

So a reader can: confirm each cited theorem **type-checks** (the file compiles),
see the **exact trust base** (`#print axioms`), check that each paper's **settings
are recorded correctly**, and understand **our approach + the gap** — per paper.

## How to verify one paper

```bash
lake build FormalRV.Audit.Gidney2025      # or any paper below
```

Compilation = every `#check`'d theorem exists and type-checks. The `#print axioms`
lines print the actual axioms each headline result depends on (the honest trust base
— e.g. `propext`/`Quot.sound` for axiom-clean results, or the QPE axiom block for the
order-finding bound). The whole `Audit/` folder is part of the default build
(`lake build`), so any drift breaks CI.

## Index (legend: ✅ verified-semantic · ➗ arithmetic-only `decide` · ⬜ recorded/assumed)

| Audit file | Paper | Headline | What the audit shows |
|---|---|---|---|
| [`Peng2022`](Peng2022.lean) | peng-2022 ([2204.07112](https://arxiv.org/abs/2204.07112)) | machine-checked end-to-end Shor | ✅ **the cross-cutting result lives here** — order-finding success `≥ κ/(log₂N)⁴`, N-parametric; `#print axioms` reveals the QPE axiom block |
| [`Gidney2025`](Gidney2025.lean) | gidney-2025 ([2505.15917](https://arxiv.org/abs/2505.15917)) | RSA-2048, <1M qubits, <1 week | ✅ CFS residue-arithmetic engine axiom-clean (RNS/CRT/modexp/Ekerå–Håstad); ➗ resource tally 897,864 < 10⁶; Assumption 1 stated, never asserted |
| [`GidneyEkera2021`](GidneyEkera2021.lean) | gidney-ekera-2021 ([1905.09749](https://arxiv.org/abs/1905.09749)) | 20M qubits, ~8 h | ✅ reproduced as a verified ceiling (19.44M ≤ 20M); ➗ invariants machine-checked, over-budget rejected; 8 h sits 2–3× under the verified time ceiling |
| [`CainXu2026`](CainXu2026.lean) | cain-xu-2026 ([2603.28627](https://arxiv.org/abs/2603.28627)) | RSA-2048, ~10⁴ qubits, ~1 week | ✅ modexp-on-LP code-preservation (induction, scale-free) + LP-code surgery; ➗ k derived from parity matrices, Eqs E3/E4/E9, the ~10⁴ q claim **bracketed** between verified bounds; gaps (parallelism, factory-sharing) sized |
| [`Webster2026`](Webster2026.lean) | webster-2026 ([2602.11457](https://arxiv.org/abs/2602.11457)) | RSA-2048, <100k qubits | ⬜ parameter-binding tuple through the shared interface (framework slot; GB matrices stubbed) |
| [`Babbush2026`](Babbush2026.lean) | babbush-2026 ([2603.28846](https://arxiv.org/abs/2603.28846)) | ECC-256, <500k qubits, 18–23 min | ⬜ tuple (first **non-RSA** stress test of the modulus-agnostic interface); ➗ verified magic-state spacetime floor |
| [`Xu2024`](Xu2024.lean) | xu-2024 ([2308.08648](https://arxiv.org/abs/2308.08648)) | constant-overhead FTQC, 24 ms cycle | ⬜ tuple; ➗ cross-checks the 24,000× cycle-time outlier (the arch the neutral-atom demo realizes) |

The two **Gidney** papers are the most complete (verified semantic cores). The two
**LDPC-Shor** papers (cain-xu-2026, webster-2026) and the neutral-atom papers
(xu-2024, babbush-2026) still have open problems — each named under *STILL UNSOLVED*
in its file. This folder is the framework; the gaps are explicit and sized.
