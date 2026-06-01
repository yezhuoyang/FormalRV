/-
  FormalRV.Framework.LDPCMatrix — GF(2) matrix primitives for
  LDPC lattice surgery.

  We need a handful of GF(2) (binary-field) matrix operations
  to verify the structural constraints of qLDPC surgery gadgets
  per qianxu Appendix C:

    * vector XOR (= addition in GF(2))
    * linear combination of matrix rows by a Bool selection vector
    * horizontal concatenation of two row blocks
    * vertical concatenation
    * dimension and parity-check-matrix consistency

  We represent a GF(2) matrix as `List (List Bool)` with no
  Mathlib dependency.  All ops are decidable on concrete matrices.

  ## Why this matters for surgery verification

  A surgery gadget's merged-code parity matrix `H̃_X` is built
  by block concatenation of the data code's `H_X`, the
  ancilla's `H_X'`, and the connection matrix `f_X'`.  The
  framework verifies that the target logical `P̄` lies in the
  row span of `H̃_X` — a one-line equality `row_combination
  span_witness merged_hx = target_pauli` over GF(2).

  This is the structural correctness condition (the "kernel of
  H_X'^T" condition in the paper, restated as a row-span
  membership of the merged matrix).
-/

namespace FormalRV.Framework.LDPC

/-! ## Vectors over GF(2) -/

/-- Row vector as a `List Bool`.  `true` ↦ 1, `false` ↦ 0. -/
abbrev BoolVec := List Bool

/-- Matrix as a `List` of rows.  Each row is a `BoolVec` of the
    same length (matrix-shape consistency is checked separately
    by `matrix_well_shaped`). -/
abbrev BoolMat := List BoolVec

/-! ## Vector arithmetic -/

/-- Component-wise XOR (= GF(2) sum) of two equal-length vectors.
    On unequal lengths, truncates to the shorter — but in our
    use the caller is responsible for matching lengths. -/
def vec_xor : BoolVec → BoolVec → BoolVec
  | [],          _           => []
  | _,           []          => []
  | h1 :: t1,    h2 :: t2    => (h1 != h2) :: vec_xor t1 t2

/-- The all-zero vector of length `n`. -/
def zero_vec (n : Nat) : BoolVec := List.replicate n false

/-! ## Matrix-vector operations -/

/-- Linear combination of the rows of `mat` selected by the Bool
    vector `sel`.  Row `i` is XOR'ed into the accumulator iff
    `sel[i] = true`.  Returns the zero vector if `sel` is shorter
    than `mat` (truncates).

    This is the GF(2) version of `selᵀ · mat` (vector-matrix
    multiplication) producing a row vector. -/
def row_combination (sel : BoolVec) (mat : BoolMat) : BoolVec :=
  match sel, mat with
  | [],            _            => []  -- nothing to combine
  | _,             []           => []  -- empty matrix → empty result
  | false :: ts,   _   :: tm    => row_combination ts tm
  | true  :: ts,   row :: tm    =>
      match row_combination ts tm with
      | []       => row  -- remaining selection is empty, just return the row
      | acc      => vec_xor row acc

/-! ## Block concatenation -/

/-- Horizontal concatenation of two same-row-count matrices,
    producing a wider matrix. -/
def hcat (left right : BoolMat) : BoolMat :=
  List.zipWith (· ++ ·) left right

/-- Vertical concatenation of two same-column-count matrices,
    producing a taller matrix. -/
def vcat (top bot : BoolMat) : BoolMat := top ++ bot

/-! ## Matrix shape predicates -/

/-- Every row of `mat` has length exactly `n`. -/
def matrix_has_n_cols (mat : BoolMat) (n : Nat) : Bool :=
  mat.all (fun row => decide (row.length = n))

/-- The matrix is well-shaped iff every row has the same length
    (which we read off the first row). -/
def matrix_well_shaped (mat : BoolMat) : Bool :=
  match mat with
  | []         => true
  | row :: _   => matrix_has_n_cols mat row.length

/-- Maximum number of `true` entries in any column of `mat`.
    Used to check the qLDPC degree bound on the merged code. -/
def max_column_weight (mat : BoolMat) (n_cols : Nat) : Nat :=
  let col_weight (j : Nat) : Nat :=
    mat.foldl (fun acc row =>
      match row[j]? with
      | some true  => acc + 1
      | _          => acc) 0
  (List.range n_cols).foldl (fun acc j => Nat.max acc (col_weight j)) 0

/-- Maximum number of `true` entries in any row of `mat`. -/
def max_row_weight (mat : BoolMat) : Nat :=
  mat.foldl (fun acc row =>
    Nat.max acc (row.filter id).length) 0

/-- The matrix is qLDPC (parameter `Δ`) iff every row and every
    column has weight ≤ `Δ`. -/
def is_qldpc (mat : BoolMat) (n_cols Δ : Nat) : Bool :=
  decide (max_row_weight mat ≤ Δ) && decide (max_column_weight mat n_cols ≤ Δ)

/-! ## Smoke checks -/

example : vec_xor [true, false, true] [false, true, true] = [true, true, false] := by rfl

example :
    row_combination [true, false, true]
      [ [true,  false, false]
      , [false, true,  false]
      , [false, false, true] ]
      = [true, false, true] := by rfl

example :
    row_combination [true, true]
      [ [true,  false, false]
      , [false, true,  false] ]
      = [true, true, false] := by rfl

example :
    hcat [[true, false]] [[true]] = [[true, false, true]] := by rfl

example :
    vcat [[true, false]] [[false, true]]
      = [[true, false], [false, true]] := by rfl

example :
    matrix_has_n_cols [[true, false], [false, true]] 2 = true := by rfl

example :
    matrix_has_n_cols [[true, false], [false]] 2 = false := by rfl

example :
    max_row_weight [[true, false, true], [false, false, false]] = 2 := by rfl

example :
    max_column_weight [[true, false, true], [true, false, true]] 3 = 2 := by rfl

example :
    is_qldpc [[true, false, true], [true, true, false]] 3 2 = true := by rfl

example :
    is_qldpc [[true, true, true]] 3 2 = false := by rfl

end FormalRV.Framework.LDPC
