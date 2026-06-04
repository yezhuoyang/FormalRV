/-
  FormalRV.QEC.Addressing — the LOGICAL ADDRESSING layer.

  In a qLDPC block the `k` logical qubits are not physically separable;
  addressing a SUBSET `S` (e.g. {2,5,7} of a `[[144,12,12]]` block) for a
  PPM is a compilation concern.  This file makes the split explicit:

  (a) the `LogicalBasis` is the TRUSTED address book the user provides
      (index `i ↦` physical support of X̄_i / Z̄_i; its `valid` /
      `pairs_delta` δ_ij invariant is what makes index `i` a genuine
      separable logical qubit);

  (b) `selectZ S` forms the addressed operator `∏_{i∈S} Z̄_i` (EASY —
      GF(2) sum of supports), and `addressedTargetZ` is the surgery
      `target_pauli`;

  (c) SYNTHESIZING the ancilla system + connection `f_X'` so that
      `ker(H_X'^T)` addresses exactly `S` is the HARD compilation (qianxu
      dynamic ancilla, `O(exp k)` gadgets) — done by the implementer, NOT
      here;

  (d) VERIFYING a provided gadget measures exactly the addressed product
      is DECIDABLE via `SurgeryGadget.targets_logical_correctly`
      (`row_combination span_witness merged_hx = addressedTargetZ S anc`)
      plus `surgery_readout_operator` / `surgery_eigenvalue`.

  So: the user provides the logical-Z definitions ⟹ addressed-PPM
  verification is decidable.  Synthesis hard, verification easy.

  No Mathlib.  Pure Bool / Nat / List + `decide`.
-/

import FormalRV.QEC.Logical
import FormalRV.QEC.Instances

namespace FormalRV.QEC

open FormalRV.Framework.LDPC       -- BoolVec, vec_xor, zero_vec
open FormalRV.Framework.PauliSem   -- PauliString

namespace LogicalBasis

/-! ## 1. Subset selection = GF(2) sum of the selected logical supports

    Addressing a subset `S ⊆ {0,…,k-1}` of the block's logical qubits is
    the support of the Pauli PRODUCT of the addressed logicals.  Because
    every logical-Z operator is a Z/I string, their product's support is
    the componentwise GF(2) sum (`vec_xor`) of the individual supports. -/

/-- Support of `∏_{i∈S} Z̄_i`: the GF(2) sum of the selected logical-Z
    supports.  `foldr` over `S` with base `zero_vec c.n`, so that
    `selectZ (i :: S) = vec_xor (lz i) (selectZ S)` holds definitionally. -/
def selectZ {c k} (L : LogicalBasis c k) (S : List (Fin k)) : BoolVec :=
  S.foldr (fun i acc => vec_xor (L.lz i) acc) (zero_vec c.n)

/-- Support of `∏_{i∈S} X̄_i`: the GF(2) sum of the selected logical-X
    supports. -/
def selectX {c k} (L : LogicalBasis c k) (S : List (Fin k)) : BoolVec :=
  S.foldr (fun i acc => vec_xor (L.lx i) acc) (zero_vec c.n)

/-! ## 2. Addressed surgery targets

    The `target_pauli` a `SurgeryGadget` must match in order to measure the
    addressed product, zero-extended onto an `ancilla_n`-qubit ancilla
    block (the dynamic-ancilla system synthesised by the implementer). -/

/-- The surgery `target_pauli` for measuring `∏_{i∈S} Z̄_i`: the addressed
    Z-support, zero-extended onto an `ancilla_n`-qubit ancilla block. -/
def addressedTargetZ {c k} (L : LogicalBasis c k) (S : List (Fin k))
    (ancilla_n : Nat) : BoolVec :=
  L.selectZ S ++ zero_vec ancilla_n

/-- The surgery `target_pauli` for measuring `∏_{i∈S} X̄_i`: the addressed
    X-support, zero-extended onto an `ancilla_n`-qubit ancilla block. -/
def addressedTargetX {c k} (L : LogicalBasis c k) (S : List (Fin k))
    (ancilla_n : Nat) : BoolVec :=
  L.selectX S ++ zero_vec ancilla_n

/-! ## 3. Characterization lemmas

    These justify calling `selectZ` "the addressed operator": the empty
    address book selects the identity (zero support), and prepending an
    index XORs in that logical's support. -/

/-- Addressing the empty subset yields the identity (zero support). -/
theorem selectZ_nil {c k} (L : LogicalBasis c k) :
    L.selectZ [] = zero_vec c.n := rfl

/-- Prepending index `i` to the address list XORs in `Z̄_i`'s support. -/
theorem selectZ_cons {c k} (L : LogicalBasis c k) (i : Fin k)
    (S : List (Fin k)) :
    L.selectZ (i :: S) = vec_xor (L.lz i) (L.selectZ S) := rfl

/-- Addressing the empty subset (X side) yields the identity. -/
theorem selectX_nil {c k} (L : LogicalBasis c k) :
    L.selectX [] = zero_vec c.n := rfl

/-- Prepending index `i` to the address list XORs in `X̄_i`'s support. -/
theorem selectX_cons {c k} (L : LogicalBasis c k) (i : Fin k)
    (S : List (Fin k)) :
    L.selectX (i :: S) = vec_xor (L.lx i) (L.selectX S) := rfl

/-- Single-qubit addressing is `vec_xor` of the chosen support with zero.
    (The general `vec_xor a (zero_vec a.length) = a` cancellation needs a
    length-indexed induction in a later module; here the `rfl` form plus
    `decide`-checked instances at concrete bases suffice.) -/
theorem selectZ_single {c k} (L : LogicalBasis c k) (i : Fin k) :
    L.selectZ [i] = vec_xor (L.lz i) (zero_vec c.n) := rfl

/-- Single-qubit addressing on the X side. -/
theorem selectX_single {c k} (L : LogicalBasis c k) (i : Fin k) :
    L.selectX [i] = vec_xor (L.lx i) (zero_vec c.n) := rfl

end LogicalBasis

/-! ## 4. Worked demo — addressing a subset of the `[[4,2,2]]` block

    Using `code422` (n = 4) and its valid `k = 2` logical basis
    `Instances.code422Logical`:
      lz 0 = [T,F,T,F]  (X̄₀ = XXII, Z̄₀ = XIXI read as Z)
      lz 1 = [T,T,F,F]  (X̄₁ = XIXI, Z̄₁ = XXII read as Z)
    so the addressed product `Z̄₀Z̄₁` has support
      lz0 ⊕ lz1 = [F,T,T,F]. -/

open FormalRV.QEC.Instances

/-- The basis is a valid address book: each index is a genuine logical
    qubit (commutes with stabilizers, realises the δ_ij pairing). -/
example : code422Logical.valid = true := by decide

/-- Addressing the subset {0,1}: the operator is `Z̄₀Z̄₁`, whose support is
    the GF(2) sum `lz 0 ⊕ lz 1`. -/
example :
    code422Logical.selectZ [0, 1]
      = vec_xor (code422Logical.lz 0) (code422Logical.lz 1) := by decide

/-- The concrete support of `Z̄₀Z̄₁` on the `[[4,2,2]]` block:
    `lz0 ⊕ lz1 = [T,F,T,F] ⊕ [T,T,F,F] = [F,T,T,F]`. -/
example : code422Logical.selectZ [0, 1] = [false, true, true, false] := by decide

/-- Single-qubit addressing {0}: the operator is `Z̄₀`, support `lz 0`. -/
example : code422Logical.selectZ [0] = code422Logical.lz 0 := by decide

/-- The surgery `target_pauli` for measuring `Z̄₀Z̄₁` with a 2-qubit ancilla
    block has length 4 + 2 = 6. -/
example : (code422Logical.addressedTargetZ [0, 1] 2).length = 6 := by decide

/-- The X-side addressed product `X̄₀X̄₁` on the same block:
    `lx0 ⊕ lx1 = [T,T,F,F] ⊕ [T,F,T,F] = [F,T,T,F]`. -/
example : code422Logical.selectX [0, 1] = [false, true, true, false] := by decide

/-- Demo anchor for `#print axioms`: the addressed-{0,1} Z target on a
    2-qubit ancilla block is the concrete length-6 vector. -/
theorem addressing_demo :
    code422Logical.addressedTargetZ [0, 1] 2
      = [false, true, true, false, false, false] := by decide

end FormalRV.QEC
