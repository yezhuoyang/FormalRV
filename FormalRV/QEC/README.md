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
