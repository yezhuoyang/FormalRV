/-
  FormalRV.QEC.Logical — the LOGICAL-OPERATOR layer of the QEC
  code-construction framework.

  This level lets a user DEFINE a code's logical operators — especially
  the logical Z̄ — and fix the logical-qubit INDEX `i : Fin k` within a
  code block, with a fully DECIDABLE validity predicate.

  A CSS code (`FormalRV.QEC.CSSCode`) is specified by its check matrices
  `(hx, hz)`.  Those pin the *stabilizer* group, but NOT which Pauli
  operators play the role of the encoded logical X̄_i / Z̄_i.  A user must
  declare those.  This file is the type + decidable contract for that
  declaration:

    * `LogicalBasis c k` — the user's declared `lx`/`lz` supports,
      indexed by the logical-qubit index `Fin k`.
    * `LogicalBasis.valid` — a `Bool` that holds iff the declared
      operators commute with every stabilizer and satisfy the symplectic
      δ_ij pairing (X̄_i anticommutes Z̄_j iff i = j).
    * a worked, `decide`-checked instance: the Steane [[7,1,3]] code.
    * connectors producing the `BoolVec` a `SurgeryGadget.target_pauli`
      must equal when measuring a logical Z̄_i / X̄_i.

  RESIDUE (flagged honestly): `valid` captures commute-with-stabilizers
  plus the δ_ij pairing.  It does NOT check *independence modulo
  stabilizers* — i.e. that no declared logical is a product of stabilizers
  (which would make it act trivially) — because that needs a GF(2) rank /
  nullspace computation living in a later module (`GF2Linear` provides the
  inner-product layer; rank/echelon is deferred).  When `k` equals the
  code's true logical dimension and the δ_ij pairing holds, the δ pairing
  already forces the declared logicals to be genuinely independent
  nontrivial logical operators, so `valid` is sufficient for the worked
  small instances here; the rank check is the one residue at this layer.

  No Mathlib.  Pure Bool / Nat / List + `decide`.
-/

import FormalRV.QEC.CSSCode

namespace FormalRV.QEC

open FormalRV.Framework.LDPC       -- BoolVec, BoolMat, dotBit, zero_vec
open FormalRV.Framework.PauliSem   -- Pauli, PauliString

/-! ## The logical basis -/

/-- A user-declared logical basis for a CSS code `c` with `k` logical qubits.
    `lx i` / `lz i` are the GF(2) supports (length `c.n`) of the logical
    X̄_i / Z̄_i operators — the i-th logical qubit's operators.  This is how a
    user "defines the logical Z operation" and fixes the logical-qubit INDEX
    within the code block. -/
structure LogicalBasis (c : CSSCode) (k : Nat) where
  lx : Fin k → BoolVec
  lz : Fin k → BoolVec

namespace LogicalBasis

/-! ## Lowerings to Pauli strings (the operators themselves) -/

/-- The logical X̄_i operator as an X/I `PauliString`, via the canonical
    check-matrix→Pauli lowering `CSSCode.xStab`. -/
def xbar {c k} (L : LogicalBasis c k) (i : Fin k) : PauliString := CSSCode.xStab (L.lx i)

/-- The logical Z̄_i operator as a Z/I `PauliString`, via the canonical
    check-matrix→Pauli lowering `CSSCode.zStab`. -/
def zbar {c k} (L : LogicalBasis c k) (i : Fin k) : PauliString := CSSCode.zStab (L.lz i)

/-! ## Decidable validity predicates -/

/-- X̄_i commutes with every Z-check: `lx i` ⟂ every row of `hz`
    (even overlap, `dotBit = false`). -/
def x_in_ker_hz {c k} (L : LogicalBasis c k) : Bool :=
  (List.finRange k).all (fun i => c.hz.all (fun row => ! dotBit (L.lx i) row))

/-- Z̄_j commutes with every X-check: `lz j` ⟂ every row of `hx`
    (even overlap, `dotBit = false`). -/
def z_in_ker_hx {c k} (L : LogicalBasis c k) : Bool :=
  (List.finRange k).all (fun j => c.hx.all (fun row => ! dotBit (L.lz j) row))

/-- Symplectic pairing δ_ij: X̄_i anticommutes Z̄_j iff `i = j`.
    `dotBit (lx i) (lz j)` is the GF(2) overlap bit = the symplectic
    anticommutation indicator (see `CSSCode.xStab_zStab_commutes`). -/
def pairs_delta {c k} (L : LogicalBasis c k) : Bool :=
  (List.finRange k).all (fun i => (List.finRange k).all (fun j =>
    dotBit (L.lx i) (L.lz j) == decide (i = j)))

/-- Headline decidable validity.  Independence-mod-stabilizers (GF(2) rank)
    is deferred to a later module; this captures commute-with-stabilizers
    (`x_in_ker_hz` ∧ `z_in_ker_hx`) plus the δ_ij pairing (`pairs_delta`),
    which already pins the declared `lx`/`lz` as genuine independent logical
    operators when `k` matches the code's true logical dimension. -/
def valid {c k} (L : LogicalBasis c k) : Bool :=
  L.x_in_ker_hz && L.z_in_ker_hx && L.pairs_delta

/-! ## Connection to lattice surgery -/

/-- The surgery `target_pauli` for measuring logical Z̄_i: the i-th Z-logical
    support, zero-extended onto an `ancilla_n`-qubit ancilla block.  This is
    exactly the vector a `SurgeryGadget.target_pauli` must equal (its
    `targets_logical_correctly` row-span identity is qianxu's kernel
    condition ⟨ℒ⟩ = f_X'ᵀ ker(H_X'ᵀ) with this target). -/
def toSurgeryTargetZ {c k} (L : LogicalBasis c k) (i : Fin k) (ancilla_n : Nat) : BoolVec :=
  L.lz i ++ zero_vec ancilla_n

/-- The surgery `target_pauli` for measuring logical X̄_i: the i-th X-logical
    support, zero-extended onto an `ancilla_n`-qubit ancilla block. -/
def toSurgeryTargetX {c k} (L : LogicalBasis c k) (i : Fin k) (ancilla_n : Nat) : BoolVec :=
  L.lx i ++ zero_vec ancilla_n

end LogicalBasis

/-! ## Worked instance: the Steane [[7,1,3]] code -/

/-- The Steane [[7,1,3]] CSS code.  Both `hx` and `hz` are the three
    weight-4 rows of the `[7,4]` Hamming parity-check matrix. -/
def steaneCSS : CSSCode :=
  { n := 7
    hx := [ [false, false, false, true,  true,  true,  true ],
            [false, true,  true,  false, false, true,  true ],
            [true,  false, true,  false, true,  false, true ] ]
    hz := [ [false, false, false, true,  true,  true,  true ],
            [false, true,  true,  false, false, true,  true ],
            [true,  false, true,  false, true,  false, true ] ] }

/-- The Steane code is well-shaped (all rows length 7). -/
example : steaneCSS.well_shaped = true := by decide

/-- The Steane code satisfies the CSS commutation condition `H_X H_Z^T = 0`
    (every pair of weight-4 Hamming rows overlaps in an even number of
    positions). -/
example : steaneCSS.css_condition = true := by decide

/-- A logical basis for Steane, `k = 1`.  The single logical qubit uses the
    all-ones weight-7 vector for BOTH X̄ and Z̄:
      * overlap with each weight-4 Hamming row = 4 (even) ⇒ commutes with
        every X- and Z-check;
      * overlap of X̄ with Z̄ = 7 (odd) ⇒ they anticommute, giving δ_00. -/
def steaneLogical : LogicalBasis steaneCSS 1 :=
  { lx := fun _ => List.replicate 7 true
    lz := fun _ => List.replicate 7 true }

/-- **Worked-instance validity**: the declared Steane logical basis is valid
    (commutes with all stabilizers and realises the δ_ij pairing). -/
theorem steaneLogical_valid : steaneLogical.valid = true := by decide

/-- Smoke: the Z̄_0 surgery target, zero-extended onto a 2-qubit ancilla
    block, has length 7 + 2 = 9. -/
example : (steaneLogical.toSurgeryTargetZ 0 2).length = 9 := by decide

/-- Smoke: the X̄_0 surgery target on the same ancilla block also has
    length 9. -/
example : (steaneLogical.toSurgeryTargetX 0 2).length = 9 := by decide

end FormalRV.QEC
