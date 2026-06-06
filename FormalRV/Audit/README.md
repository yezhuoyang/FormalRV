# `FormalRV/Audit/` — per-paper audit, reader-verifiable, one folder per paper

Each paper has its **own folder** with the **same uniform structure**, and `Audit/Common/` holds the
shared machinery (surface-code surgery gadgets, the Shor/Surface/Windowed pipeline, cost/decoder/zone
models, paper-claim constants) that several papers reuse. A paper folder **redefines nothing** — it
imports the real theorems and re-presents them by layer.

```
Audit/
  Common/                     -- shared infrastructure (FormalRV.Audit.Common.*)
  <Paper>/                    -- CainXu2026 · GidneyEkera2021 · Gidney2025 · Pinnacle · Babbush2026 · Xu2024 · Peng2022
    Hardware.lean             -- physical assumptions (error, cycle, reaction)
    SystemZones.lean          -- zoned architecture + invariant checks (or a documented GAP)
    L1_Algorithm.lean         -- the ShorAlgorithm instance + the shared success bound
    L2_Arithmetic.lean        -- verified adders/lookups/modexp (or GAP)
    L3_PPM.lean               -- Pauli-product-measurement correctness (or GAP)
    L4_Code.lean              -- the QEC code + k derived from matrices (or GAP)
    Verifier.lean             -- the end-to-end obligation + #verify_clean (the anti-cheat gate)
    README.md                 -- claim · settings-to-check · approach · gap · still-unsolved
  <Paper>.lean                -- the folder index (imports the seven structure files)
```

## The rigor / anti-cheating contract (enforced on build)

`Verifier.lean` (and each layer file) runs **`#verify_clean`** — it ACCEPTS a theorem only if its
transitive axioms ⊆ `{propext, Classical.choice, Quot.sound}`; a `sorry` or a native-tainted axiom
makes the **build fail**. So a folder cannot pass by "counting numbers". Every layer is exactly one of:

- ✅ **verified** — a semantic-correctness theorem the gate ACCEPTS, or
- ➗ **arithmetic-only** — a `decide`/`native_decide` numeric bound, labelled as *not* semantic, or
- ⬜ **GAP** — a documented note with **no** theorem (never a number passed off as a proof).

## How to verify one paper

```bash
lake build FormalRV.Audit.CainXu2026      # or any folder below
```

## Index (✅ verify-clean · ➗ arithmetic-only · ⬜ recorded/GAP)

| Folder | Paper | Status in one line |
|---|---|---|
| [`Peng2022`](Peng2022) | peng-2022 ([2204.07112](https://arxiv.org/abs/2204.07112)) | ✅ **the cross-cutting bound** — order finding ≥ κ/(log₂N)⁴, N-parametric; the rest is honest GAP (algorithm-level paper) |
| [`Gidney2025`](Gidney2025) | gidney-2025 ([2505.15917](https://arxiv.org/abs/2505.15917)) | ✅ CFS residue engine axiom-clean; ✅ tally < 10⁶; ⬜ Assumption 1 / quantum half |
| [`GidneyEkera2021`](GidneyEkera2021) | GE-2021 ([1905.09749](https://arxiv.org/abs/1905.09749)) | ✅ capstone axiom-free (19.44M ≤ 20M; 8 h under the ceiling); ✅ finite-zone invariants |
| [`CainXu2026`](CainXu2026) | cain-xu-2026 ([2603.28627](https://arxiv.org/abs/2603.28627)) | ✅ modexp-on-LP code-preservation + LP surgery + verified resource bounds; ➗ k derived; ⬜ optimisation gaps sized |
| [`Pinnacle`](Pinnacle) | webster-2026 ([2602.11457](https://arxiv.org/abs/2602.11457)) | ➗ GB code k derived; ✅ RSA instance recorded; ⬜ gadget/engine/<100k bound (roadmap) |
| [`Babbush2026`](Babbush2026) | babbush-2026 ([2603.28846](https://arxiv.org/abs/2603.28846)) | ✅ shared bound (modulus-agnostic); ➗ magic-state floor; ⬜ first non-RSA, end-to-end open |
| [`Xu2024`](Xu2024) | xu-2024 ([2308.08648](https://arxiv.org/abs/2308.08648)) | ➗ 24,000× cycle-time outlier; ⬜ tuple (the arch the neutral-atom demo realizes) |

The two Gidney papers + cain-xu have substantial ✅ stacks; the LDPC-Shor/neutral-atom papers
(Pinnacle, Babbush2026, Xu2024) have open problems, each named under *STILL UNSOLVED* in its folder.
