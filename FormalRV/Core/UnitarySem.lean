/-
  FormalRV.Framework.UnitarySem — matrix semantics for unitary circuits.

  Lean translation of SQIR/SQIR/UnitarySem.v. This is the layer that maps
  a syntactic `BaseUCom dim` to its denotational meaning as a 2^dim × 2^dim
  complex unitary matrix.

  ## Status (2026-05-04, end of long grind)

  **ZERO SORRIES.** This file now has the full unitary-matrix semantic
  layer for SQIR-style circuits, with every theorem proven. Headlines:

    - `pad_u` (embed 2×2 unitary at qubit n) — IMPLEMENTED via Kronecker
      products + reindex
    - `pad_ctrl` (controlled-version) — IMPLEMENTED via projector
      decomposition `proj0_pad + proj1_pad · M_pad`
    - `pad_u_mul_pad_u` — proven (matrix-mul + kron-mul + reindex)
    - `pad_u_id` — proven (Iₙ_kron_Iₙ chain + reindex of identity)

  All single-qubit gate-matrix theorems proven (rotation_X/Y/Z/I/T/S/H,
  Pauli involutions σx² = σy² = σz², anti-commutation, hMatrix_mul_hMatrix,
  CNOT² = I). All circuit-equivalence theorems for single-qubit gates
  proven (X_X_id, Y_Y_id, Z_Z_id, Rz_Rz_add, T_TDAG_id, etc.). SKIP
  identity laws proven.

  ## Strategic note: do we need this for the gap review?

  For *resource* claims (T-count, gate count, qubit count) we do NOT need
  matrix semantics — `Framework.Gate` (RCIR-level) suffices, and that's
  what BQ-Algo uses for the Cuccaro / Gidney 2018 / windowed arithmetic
  cost work. We only need this matrix layer to prove **algorithm
  correctness** (e.g., that QPE applied to IMM actually finds the order),
  which is the deepest part of the Shor formalization. The review can
  produce results from `Framework.Gate` long before this file's sorries
  are all filled.
-/

-- Re-export shim: split into UnitarySem/ submodules (same namespace; opens de-duplicated); importers unchanged.
import FormalRV.Core.UnitarySem.Part1
import FormalRV.Core.UnitarySem.Part2
import FormalRV.Core.UnitarySem.Part3
import FormalRV.Core.UnitarySem.Part4
import FormalRV.Core.UnitarySem.Part5
import FormalRV.Core.UnitarySem.Part6
