# FormalRV.Corpus

This folder is the Phase-C application layer: it binds the seven state-of-the-art
fault-tolerant Shor estimates into the FormalRV four-layer framework as
`(ShorAlgorithm × QECCode × QualtranPhysicalParameters)` tuples, records every
page-cited resource claim as a `paper_claim_*` constant, and carries two concrete
end-to-end demos (a verified modular-multiplier-to-PPM closure and a Steane
lattice-surgery gadget). The tuple files mostly establish that each paper's stated
parameters type-check and read back through the shared interface; deep semantic
verification lives only in the two demo files.

## Layout
- `PaperClaims.lean` — canonical, citation-anchored `def`s for every major resource number across all corpus papers, plus `decide`-level cross-checks.
- `CainXu.lean` — Cain–Xu/qianxu tuple (q_A=33, BB `[[144,12,12]]`, neutral-atom HW) + one explicit BB X-check row.
- `GidneyEkera2021.lean` — GE2021 tuple (surface `[[1568,1,27]]`, `gidney_fowler_realistic`).
- `Gidney2025.lean` — Gidney 2025 tuple (surface `[[1352,1,25]]`).
- `Babbush2026.lean` — Babbush ECC-256 tuple (first non-RSA paper; tests modulus-agnostic L1).
- `Webster2026.lean` — Webster/Pinnacle tuple (GB `[[1620,16,24]]`).
- `Xu2024.lean` — Xu 2024 tuple (LP `[[544,80,12]]`; the 24 ms slow-cycle outlier).
- `Peng2022.lean` — Peng/SQIR tuple (verified L1, degenerate `(1,1,1)` L4).
- `ShorModMulPPMFactoryE2E.lean` — verified modular multiplier compiled to PPM + T-factory, run to a correct Boolean output.
- `SurgeryDemoSteane.lean` — concrete LDPC lattice-surgery gadget on Steane `[[7,1,3]]`.

## Key definitions
- `cainxu_instance` (`CainXu.lean`) — the qianxu paper as a full framework tuple; siblings `ge2021_instance`, `gidney2025_instance`, `babbush_instance`, `webster_instance`, `xu2024_instance`, `peng_instance`.
- `bb_first_x_check` (`CainXu.lean`) — one weight-6 BB `[[144,12,12]]` X-stabilizer as a length-144 `Bool` row (parity matrices are otherwise stubbed `[]`).
- `qianxu_E9_evaluated q_w k_p` (`PaperClaims.lean`) — the lookup per-Toffoli cost formula `15·q_w/(k_p-3)`.
- `gidney_total_tau_s_n_bit_adder` (`PaperClaims.lean`) — gate-derived τ_s cost of an n-bit Gidney adder.
- `steane_x_surgery` (`SurgeryDemoSteane.lean`) — `SurgeryGadget` measuring logical X̄ on Steane via a 1-qubit ancilla tree.

## Key theorems
- `shorModMul_compiles_to_PPM_with_factory` (`ShorModMulPPMFactoryE2E.lean`) — the verified modular multiplier compiles to a factory-provisioned PPM program that runs and observes `(a·x) mod N`. **Verified** (PPM/logical layer; relies on named factory/teleport contracts, see below — **Axiom**).
- `steane_x_surgery_verifies` (`SurgeryDemoSteane.lean`) — the Steane X̄ gadget passes the full structural surgery verifier; `steane_x_surgery_WRONG_rejected` rejects a bogus target. **Verified** (structural, `decide`).
- `gidney_n_bit_adder_meets_qianxu_E3` (`PaperClaims.lean`) — `gidney_total_tau_s_n_bit_adder n = 25·n`, recovering qianxu Eq. E3. **Arithmetic-only**.
- `ctl_adder_n_bit_meets_qianxu_E4` (`PaperClaims.lean`) — controlled-adder cost `= 30·n`, recovering Eq. E4. **Arithmetic-only**.
- `qianxu_qubit_hours_95x_lower_than_gidney_ekera` (`PaperClaims.lean`) — qianxu's qubit·hour product is ≥95× below GE2021. **Arithmetic-only**.
- The `*_instance` smoke `example`s in each paper file — paper parameters read back through the tuple. **Arithmetic-only** (`rfl`/`decide` parameter binding).

## Status
The seven tuple files are parameter bindings: their `example`s only confirm that paper-stated numbers type-check and read back through the shared interface (parity matrices are stubbed `[]`, so no QEC semantics are verified here), and `PaperClaims.lean` is citation data with `decide`-level Nat cross-checks. Genuine semantic correctness exists only in `ShorModMulPPMFactoryE2E.lean` (modular-multiplier-to-PPM run, **Verified** modulo explicit factory/Toffoli-teleportation contracts) and the structural verifier closures in `SurgeryDemoSteane.lean`.
