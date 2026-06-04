/-
  FormalRV.QEC.GF2Linear — GF(2) linear-algebra primitives over the
  `BoolVec`/`BoolMat` carrier of `LDPCMatrix`.

  This is the missing primitive flagged by the code-framework design
  (`notes/topic-qec-code-framework.md`): everything downstream — the CSS
  commutation condition `H_X H_Z^T = 0`, the logical-qubit count
  `k = n − rank H_X − rank H_Z`, kernel/logical extraction — needs GF(2)
  linear algebra absent from `LDPCMatrix.lean`.

  This file provides the inner-product / orthogonality layer (the part
  the CSS condition needs); rank/echelon/nullspace are a later module.

  Extends the SAME namespace `FormalRV.Framework.LDPC` as `LDPCMatrix`.
  No Mathlib.  Pure Bool / Nat / List + `decide`.
-/

import FormalRV.QEC.LDPCMatrix

namespace FormalRV.Framework.LDPC

/-! ## GF(2) inner product -/

/-- GF(2) inner product bit of two vectors: `1` (`true`) iff the number of
    positions where BOTH are `1` is odd.  This is `Σ_i a_i·b_i mod 2`.
    `dotBit a b = false` means `a` and `b` are orthogonal over GF(2). -/
def dotBit (a b : BoolVec) : Bool :=
  decide (((a.zip b).countP (fun p => p.1 && p.2)) % 2 = 1)

@[simp] theorem dotBit_nil_left (b : BoolVec) : dotBit [] b = false := by
  simp [dotBit]

@[simp] theorem dotBit_nil_right (a : BoolVec) : dotBit a [] = false := by
  cases a <;> simp [dotBit]

/-! ## Matrix transpose and A·Bᵀ -/

/-- GF(2) transpose of a matrix with `ncols` columns: row `j` of the
    result is column `j` of `mat`. -/
def transpose (mat : BoolMat) (ncols : Nat) : BoolMat :=
  (List.range ncols).map (fun j => mat.map (fun row => row.getD j false))

/-- The GF(2) product `A · Bᵀ`, as a `BoolMat`: entry `(i, j)` is the inner
    product of row `i` of `A` with row `j` of `B`. -/
def mat_mul_transpose (a b : BoolMat) : BoolMat :=
  a.map (fun ra => b.map (fun rb => dotBit ra rb))

/-! ## Orthogonality (the CSS commutation test) -/

/-- `orthogonal a b = true` iff every row of `a` is GF(2)-orthogonal to
    every row of `b`, i.e. `A · Bᵀ = 0`.  This is the CSS commutation
    test `H_X · H_Z^T = 0`. -/
def orthogonal (a b : BoolMat) : Bool :=
  a.all (fun ra => b.all (fun rb => ! dotBit ra rb))

/-- `orthogonal a b = true` iff every (row-of-`a`, row-of-`b`) pair is
    GF(2)-orthogonal — the per-pair unfolding used downstream. -/
theorem orthogonal_iff (a b : BoolMat) :
    orthogonal a b = true ↔
      ∀ ra ∈ a, ∀ rb ∈ b, dotBit ra rb = false := by
  simp [orthogonal, List.all_eq_true]

/-! ## Smoke tests -/

-- GF(2) dot: [1,0,1]·[1,1,1] = 1+0+1 = 0 (even overlap → orthogonal).
example : dotBit [true, false, true] [true, true, true] = false := by decide
-- [1,1,0]·[1,1,1] = 1+1+0 = 0.
example : dotBit [true, true, false] [true, true, true] = false := by decide
-- [1,0,0]·[1,1,1] = 1 (odd → non-orthogonal).
example : dotBit [true, false, false] [true, true, true] = true := by decide

-- The Steane X/Z checks (equal Hamming-code rows) are mutually orthogonal
-- (each pair overlaps in an even number of positions): the CSS condition.
example :
    orthogonal
      [ [false, false, false, true,  true,  true,  true ]
      , [false, true,  true,  false, false, true,  true ]
      , [true,  false, true,  false, true,  false, true ] ]
      [ [false, false, false, true,  true,  true,  true ]
      , [false, true,  true,  false, false, true,  true ]
      , [true,  false, true,  false, true,  false, true ] ] = true := by decide

end FormalRV.Framework.LDPC
