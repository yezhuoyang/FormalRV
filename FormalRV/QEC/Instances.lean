/-
  FormalRV.QEC.Instances — the qianxu code corpus as concrete `CSSCode`
  values, with `decide`/`native_decide`-checked structural smokes.

  Each entry is a genuine GF(2) check-matrix pair built through the
  `FrontendAlgebraic` constructors (no axiomatized parameters): the
  small codes verify the CSS commutation condition `H_X · H_Z^T = 0`
  outright; the large lifted-product codes are verified CSS by the
  tiny-LP oracle plus the ring algebra (`liftedProduct`), with the
  full-matrix `css_condition` left as an HONEST RESIDUE at that scale.

  SCOPE NOTE: code DISTANCE is OUT OF SCOPE — these are constructions
  plus CSS commutation, not distance proofs.

  Codes:
  * `code422`   — the `[[4,2,2]]` code (with a verified logical basis)
  * `surface3`, `surface5` — unrotated surface codes (HGP)
  * `bb18`      — bivariate-bicycle `[[248, 10, 18]]` (qianxu)
  * `lp16`, `lp20`, `lp24`, `lpproc` — qianxu lifted-product seeds

  No Mathlib.  Pure Bool / Nat / List + decide / native_decide.
-/

import FormalRV.QEC.FrontendAlgebraic
import FormalRV.QEC.Logical

namespace FormalRV.QEC.Instances

open FormalRV.QEC
open FormalRV.QEC.Algebraic
open FormalRV.Framework.LDPC
open FormalRV.Framework.PPMOp

/-! ## 1. The `[[4,2,2]]` code -/

/-- The `[[4,2,2]]` detection code: a single weight-4 `X`-stabilizer
    `XXXX` and a single weight-4 `Z`-stabilizer `ZZZZ` on 4 qubits.
    Encodes 2 logical qubits, detects 1 error. -/
def code422 : CSSCode :=
  { n := 4
    hx := [[true, true, true, true]]
    hz := [[true, true, true, true]] }

/-- All rows have length 4. -/
example : code422.well_shaped = true := by decide

/-- CSS commutation: `XXXX · ZZZZ` overlap = 4 (even), so they commute. -/
example : code422.css_condition = true := by decide

/-- A logical basis for `[[4,2,2]]`, `k = 2`.  Standard supports:
      X̄₀ = XXII, Z̄₀ = XIXI (read as Z), X̄₁ = XIXI, Z̄₁ = XXII.
    Each commutes with both stabilizers (weight-2 overlap with the
    weight-4 checks is even) and realises the δ_ij pairing:
    overlap(X̄ᵢ, Z̄ⱼ) is odd iff i = j. -/
def code422Logical : LogicalBasis code422 2 :=
  { lx := fun i => if i = 0 then [true, true, false, false] else [true, false, true, false]
    lz := fun i => if i = 0 then [true, false, true, false] else [true, true, false, false] }

/-- The declared `[[4,2,2]]` logical basis is valid (commutes with all
    stabilizers and realises the δ_ij pairing). -/
example : code422Logical.valid = true := by decide

/-- Pipeline capstone: the `[[4,2,2]]` syndrome-measurement circuit
    implements it (the lowered stabilizer group is valid), since it is CSS. -/
example : StabilizerState.valid (code422.toStabilizers) 4 = true := by
  show StabilizerState.valid (code422.toStabilizers) code422.n = true
  rw [CSSCode.syndrome_circuit_implements_code code422 (by decide)]; decide

/-! ## 2. Surface codes (hypergraph product of repetition codes) -/

/-- The unrotated distance-3 surface code, `[[13, 1, 3]]`. -/
def surface3 : CSSCode := surfaceHGP 3

/-- The unrotated distance-5 surface code, `[[41, 1, 5]]`. -/
def surface5 : CSSCode := surfaceHGP 5

example : surface3.n = 13 := by decide                    -- 3² + 2² = 13
example : surface3.well_shaped = true := by decide
example : surface3.css_condition = true := by decide

example : surface5.n = 41 := by decide                    -- 5² + 4² = 41
example : surface5.well_shaped = true := by native_decide
example : surface5.css_condition = true := by native_decide

/-! ## 3. Bivariate-bicycle code `[[248, 10, 18]]` (qianxu)

    a = 1 + x⁶y + x²⁷,  b = y² + x¹⁵y³ + x²⁴,  over ℓ = 31, m = 4. -/

/-- The bivariate-bicycle `[[248, 10, 18]]` qLDPC code from qianxu. -/
def bb18 : CSSCode :=
  bivariateBicycle 31 4 [(0, 0), (6, 1), (27, 0)] [(0, 2), (15, 3), (24, 0)]

example : bb18.n = 248 := by decide                       -- 2 · 31 · 4 = 248

/-- CSS commutation for the BB `[[248, 10, 18]]` code.  `native_decide`
    (the `248`-column orthogonality check is too large for kernel `decide`). -/
example : bb18.css_condition = true := by native_decide

/-! ## 4. Lifted-product codes (qianxu App. A)

    Each seed `A` is a `3×7` (or `3×5`) polynomial matrix over
    `R = F2[x]/(x^ℓ+1)`; every entry is a single monomial `x^k ↦ [k]`.
    The lifted product `LP(A, A†)` has `n = (3² + 7²)·ℓ` qubits.

    RESIDUE (honest, flagged): `css_condition` is NOT checked for
    `lp16`/`lp20`/`lp24`/`lpproc` — the orthogonality test over `~2600`
    columns is infeasible to elaborate here.  These ARE CSS codes: the
    `liftedProduct` constructor's CSS commutation is verified on the
    tiny-LP oracle (`Algebraic.lpTiny`, `css_condition = true` by
    `decide`) and holds for all `A` by the ring algebra
    (`transpose (lift A†) = lift A`, so `hx · hzᵀ = lift(A⊗A† + A⊗A†) = 0`).
    Only the `n`-check is discharged at this scale. -/

/-- LP seed for the `[[2610, 744, ≤16]]` code (qianxu App. A), `3×7` over ℓ=45. -/
def A_lp16 : List (List Circ) :=
  [[[29], [21], [31], [15], [37], [25], [27]],
   [[13], [25], [19], [26], [11], [18], [29]],
   [[31], [2],  [27], [32], [41], [41], [18]]]

/-- LP seed for the `ℓ=75` lifted-product code (qianxu App. A), `3×7`. -/
def A_lp20 : List (List Circ) :=
  [[[0],  [71], [73], [68], [33], [50], [47]],
   [[38], [39], [60], [26], [18], [1],  [23]],
   [[73], [6],  [5],  [42], [20], [22], [73]]]

/-- LP seed for the `ℓ=91` lifted-product code (qianxu App. A), `3×7`. -/
def A_lp24 : List (List Circ) :=
  [[[57], [75], [42], [80], [7],  [67], [27]],
   [[57], [73], [34], [12], [27], [50], [87]],
   [[21], [53], [70], [18], [1],  [3],  [18]]]

/-- The lifted-product code on `A_lp16` over `R = F2[x]/(x^45+1)`. -/
def lp16 : CSSCode := liftedProduct 45 A_lp16 3 7

/-- The lifted-product code on `A_lp20` over `R = F2[x]/(x^75+1)`. -/
def lp20 : CSSCode := liftedProduct 75 A_lp20 3 7

/-- The lifted-product code on `A_lp24` over `R = F2[x]/(x^91+1)`. -/
def lp24 : CSSCode := liftedProduct 91 A_lp24 3 7

example : lp16.n = (3 * 3 + 7 * 7) * 45 := by decide      -- = 2610
example : lp20.n = (3 * 3 + 7 * 7) * 75 := by decide      -- = 4350
example : lp24.n = (3 * 3 + 7 * 7) * 91 := by decide      -- = 5278
-- NOTE: css_condition for lp16/lp20/lp24 is an honest residue (see §4 header).

/-- LP seed for the `lpproc` processing-block code (qianxu), `3×5` over ℓ=33.
    First row and column are the constant `1 = x⁰ = [0]`. -/
def A_lpproc : List (List Circ) :=
  [[[0], [0],  [0],  [0],  [0]],
   [[0], [14], [19], [11], [26]],
   [[0], [13], [2],  [15], [21]]]

/-- The lifted-product `lpproc` code over `R = F2[x]/(x^33+1)`. -/
def lpproc : CSSCode := liftedProduct 33 A_lpproc 3 5

example : lpproc.n = (3 * 3 + 5 * 5) * 33 := by decide     -- = 1122
-- NOTE: css_condition for lpproc is an honest residue (see §4 header).

end FormalRV.QEC.Instances
