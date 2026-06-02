/-
  FormalRV.QEC.GF2Rank — GF(2) Gaussian elimination over `BoolMat`.

  This is the rank / rowspace-membership layer flagged as the one RESIDUE
  in `Logical.lean`: deciding whether a declared logical operator is a
  *product of stabilizers* (i.e. lies INSIDE the stabilizer group) needs a
  GF(2) rank computation absent from `GF2Linear.lean` (which provides only
  the inner-product / orthogonality layer).

  We build a textbook GF(2) row reduction: fold the rows of a matrix,
  reducing each against the pivots collected so far, and keeping it as a
  new pivot iff it stays nonzero.  `rank` = number of pivots.
  `inRowspace mat v` = `v` reduces to all-zero against the echelon pivots.

  The MATHEMATICAL key fact this layer exposes: every element of the
  GF(2) rowspace of the Steane Hamming matrix has EVEN weight, so the
  weight-7 all-ones logical operator is OUTSIDE the stabilizer rowspace —
  precisely the property that distinguishes a genuine logical (in N(S)\S)
  from a stabilizer.

  Correctness here is `decide`-verified at the instance level (the smoke
  tests below are the oracle), not proven parametrically.  That is
  sufficient for the per-instance audit: the smokes pin the algorithm to
  the mathematically-true answers.

  Extends the SAME namespace `FormalRV.Framework.LDPC` as `GF2Linear`.
  No Mathlib.  Pure Bool / Nat / List + `decide`.
-/

import FormalRV.QEC.GF2Linear

namespace FormalRV.Framework.LDPC

/-! ## Leading column -/

/-- The first column index where `v` is `true` (its "leading 1"), or `none`
    if `v` is all-zero. -/
def leadIdx (v : BoolVec) : Option Nat := v.findIdx? id

/-! ## Reduction of a vector against echelon pivots -/

/-- Reduce `v` against a list of echelon `pivots`: for each pivot `p` whose
    leading column `j` is also set in `v`, xor `p` into `v`, clearing that
    column.  When `pivots` is in row-echelon form (distinct leading
    columns, each pivot's leading bit clear in every later pivot), the
    result is `v`'s canonical remainder modulo the rowspace of `pivots`. -/
def reduceVec (pivots : BoolMat) (v : BoolVec) : BoolVec :=
  pivots.foldl
    (fun acc p =>
      match leadIdx p with
      | none   => acc
      | some j => if acc.getD j false then vec_xor acc p else acc)
    v

/-! ## Gaussian elimination -/

/-- GF(2) Gaussian elimination.  Folds over `mat`'s rows, building a pivot
    list; each row is first reduced against the current pivots, and kept as
    a new pivot iff the remainder is nonzero.  The returned `BoolMat` is the
    list of nonzero pivot rows (one per independent direction). -/
def rowReduce (mat : BoolMat) : BoolMat :=
  mat.foldl
    (fun acc row =>
      let r := reduceVec acc row
      if r.any id then acc ++ [r] else acc)
    []

/-- GF(2) rank = number of pivots in the echelon form. -/
def rank (mat : BoolMat) : Nat := (rowReduce mat).length

/-- `v` is in the GF(2) rowspace of `mat` iff it reduces to all-zero against
    `mat`'s echelon pivots. -/
def inRowspace (mat : BoolMat) (v : BoolVec) : Bool :=
  (reduceVec (rowReduce mat) v).all (fun b => ! b)

/-! ## Smoke tests — the Steane Hamming matrix is the oracle -/

/-- The Steane `[7,4]` Hamming parity-check matrix (`hx = hz` for Steane). -/
def steaneH : BoolMat :=
  [ [false, false, false, true,  true,  true,  true ],
    [false, true,  true,  false, false, true,  true ],
    [true,  false, true,  false, true,  false, true ] ]

-- The three Hamming rows are linearly independent over GF(2): rank 3.
example : rank steaneH = 3 := by decide

-- Row 0 itself is in the rowspace.
example : inRowspace steaneH [false, false, false, true, true, true, true] = true := by decide

-- A GF(2) combination (row 0 ⊕ row 1) is in the rowspace.
example :
    inRowspace steaneH
      (vec_xor [false, false, false, true, true, true, true]
               [false, true,  true,  false, false, true, true]) = true := by decide

-- THE DISCRIMINATING FACT: the all-ones weight-7 vector is NOT in the
-- rowspace.  Every rowspace element is even weight; all-ones is odd weight.
-- This is exactly why the all-ones Steane logical is OUTSIDE the stabilizer.
example : inRowspace steaneH [true, true, true, true, true, true, true] = false := by decide

-- Appending the all-ones logical raises the rank by 1: it is INDEPENDENT
-- modulo the stabilizer rows (a genuine new direction in N(S)\S).
example : rank (steaneH ++ [[true, true, true, true, true, true, true]]) = 4 := by decide

end FormalRV.Framework.LDPC
