# FormalRV.QEC

The L4 (QEC-code) data layer of FormalRV. Provides binary-field (GF(2)) parity-check-matrix primitives used to express qLDPC lattice-surgery structural constraints, plus a catalogue of concrete code instances (Steane, surface-code distances, bivariate-bicycle / lifted-product qLDPC) carrying their `[[n, k, d]]` parameters. The `QECCode` structure itself is defined upstream in `Framework/L4_QECCode.lean`; this folder supplies the matrix toolkit and the instances built on it.

## Layout
- `LDPCMatrix.lean` — `List (List Bool)` GF(2) matrix/vector ops (XOR, row combination, block concat, shape/weight predicates) with no Mathlib dependency.
- `QECCodeInstances.lean` — concrete `QECCode` values (Steane, surface d=3..25, qLDPC `[[144,18,12]]`) plus the one fully-populated Steane parity matrix.

## Key definitions
- `BoolVec` / `BoolMat` (`LDPCMatrix.lean`) — GF(2) row vector / matrix as `List Bool` / `List (List Bool)`.
- `vec_xor`, `row_combination` (`LDPCMatrix.lean`) — GF(2) vector sum and selection-weighted row combination (`selᵀ · mat`); the core of row-span membership checks for merged surgery codes.
- `hcat` / `vcat` (`LDPCMatrix.lean`) — horizontal/vertical block concatenation, building a merged code's `H̃_X` from data, ancilla, and connection blocks.
- `max_row_weight`, `max_column_weight`, `is_qldpc` (`LDPCMatrix.lean`) — row/column weights and the bounded-degree (qLDPC) predicate at parameter `Δ`.
- `steane_713`, `surface_d3`..`surface_d25`, `lp_144_18_12` (`QECCodeInstances.lean`) — code instances carrying `(n, k, d)`; parity matrices left empty except Steane.
- `steane_713_with_parity` (`QECCodeInstances.lean`) — Steane `[[7,1,3]]` with both `hx`, `hz` set to the `[7,4]` Hamming parity check.

## Key theorems
- `vec_xor`/`row_combination` smoke checks (`LDPCMatrix.lean`) — concrete GF(2) sums and row spans evaluate as claimed — **Arithmetic-only** (`rfl`/`decide`-level `example`s).
- `is_qldpc ... = true/false` smoke checks (`LDPCMatrix.lean`) — bounded-degree predicate accepts/rejects sample matrices correctly — **Arithmetic-only**.
- `matrix_has_n_cols`, `max_*_weight` smoke checks (`LDPCMatrix.lean`) — shape and weight functions compute the expected values on examples — **Arithmetic-only**.

## Status
The GF(2) matrix toolkit is complete and exercised only by `decide`/`rfl` smoke checks (**Arithmetic-only**); there are no semantic-correctness theorems here. Code instances are **Scaffolded**: they record `[[n,k,d]]` parameters, but parity matrices are empty placeholders except `steane_713_with_parity`, and no code's distance or stabilizer-commutation property is proven. Per the L4→L3 contract, cycle-level logical error rates are framework *inputs*, not derived here.

## Worked example — the surface [[13,1,3]] parity-check matrices

![surface3 parity-check matrices Hx and Hz](../../docs/diagrams/surface3_parity.png)

A CSS code is two GF(2) parity-check matrices. The heatmap above is the merged
surface `[[13,1,3]]` surgery code from `Corpus/SurgeryDemoSurface.lean`, drawn
directly from the Lean-emitted `surface3_surgery.stim`: `Hx` has 8 X-checks, `Hz`
has 6 Z-checks, each a sparse weight-≤4 row over the 14 data/ancilla qubits —
exactly the bounded-degree structure the `is_qldpc` predicate checks. This folder
supplies the GF(2) toolkit those checks run on: `vec_xor`, `row_combination`
(`selᵀ·mat`, the core of the surgery row-span membership test), `hcat`/`vcat`
(assembling a merged `H̃_X` from data / ancilla / connection blocks), and
`max_row_weight` / `is_qldpc`.

## Essential proof techniques

- **GF(2) linear algebra as `List Bool` with decidable checks.** Matrices are
  `List (List Bool)`; `row_combination` is the selection-weighted row sum, and
  membership of a logical operator in the stabilizer row span is a `decide`-checkable
  equation (`row_combination sel H = target`) — the exact obligation the
  `LatticeSurgery` verifier discharges.
- **Instances carry `[[n,k,d]]`; parities are mostly inputs.** Honest scope: the
  catalogue (`surface_d3..d25`, `lp_144_18_12`) records parameters with parity
  matrices left empty *except* `steane_713_with_parity` (the `[7,4]` Hamming check).
  The one fully populated, structurally verified parity matrix exercised end-to-end
  is the surface `[[13,1,3]]` surgery code shown above; no code's distance or decoder
  is proven here — per the L4→L3 contract, logical error rates are framework *inputs*.
