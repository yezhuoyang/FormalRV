/-
  FormalRV.QEC.Codes.Surface.RotatedLogical
  ─────────────────────────────────────────
  **The logical X̄ and Z̄ operators of the rotated surface code.**

  On the `d × d` data grid (`ridx d r c = r·d + c`):
    • X̄ = X on COLUMN 0  — `{ridx d r 0 : r < d}` = `{0, d, 2d, …}`;
    • Z̄ = Z on ROW 0     — `{ridx d 0 c : c < d}` = `{0, 1, …, d−1}`.

  Each is a boundary-to-boundary string of its type.  Validity (it commutes
  with every opposite-type check and is NOT a product of same-type checks) is
  `native_decide`-checked at `d = 3, 5, 7, 27`.  X̄ and Z̄ intersect at exactly
  one qubit (the corner `0`), so they anticommute — a genuine logical pair.
-/
import FormalRV.QEC.Codes.Surface.RotatedSurface
import FormalRV.QEC.LogicalFinder
import FormalRV.QEC.GF2Rank

namespace FormalRV.QEC.Codes.Surface

open FormalRV.Framework.LDPC
open FormalRV.QEC FormalRV.QEC.LogicalFinder

/-! ## §1. The logical-operator supports. -/

/-- Column `col` of the `d×d` grid: `{ridx d r col : r < d}`. -/
def colSupp (d col : Nat) : List Nat := (List.range d).map (fun r => ridx d r col)

/-- Row `row` of the `d×d` grid: `{ridx d row c : c < d}`. -/
def rowSupp' (d row : Nat) : List Nat := (List.range d).map (fun c => ridx d row c)

/-- **The logical X̄ support**: column 0. -/
def logicalXSupp (d : Nat) : List Nat := colSupp d 0

/-- **The logical Z̄ support**: row 0. -/
def logicalZSupp (d : Nat) : List Nat := rowSupp' d 0

/-- X̄ as a length-`d²` Boolean row. -/
def logicalX (d : Nat) : BoolVec := suppRow d (logicalXSupp d)

/-- Z̄ as a length-`d²` Boolean row. -/
def logicalZ (d : Nat) : BoolVec := suppRow d (logicalZSupp d)

/-! ## §2. Validity predicates. -/

/-- A support is a valid X-LOGICAL of code `d`: it commutes with every
Z-check (`gf2dot = 0`) and is NOT in the row-space of the X-checks. -/
def isXLogical (d : Nat) (v : BoolVec) : Bool :=
  ((rotatedSurface d).hz.all (fun r => ! gf2dot r v))
    && ! inRowspace (rotatedSurface d).hx v

/-- A support is a valid Z-LOGICAL of code `d`: commutes with every X-check
and is NOT in the row-space of the Z-checks. -/
def isZLogical (d : Nat) (v : BoolVec) : Bool :=
  ((rotatedSurface d).hx.all (fun r => ! gf2dot r v))
    && ! inRowspace (rotatedSurface d).hz v

/-! ## §3. Validity at the GE2021 distance and small distances. -/

theorem logicalX3_valid : isXLogical 3 (logicalX 3) = true := by decide
theorem logicalZ3_valid : isZLogical 3 (logicalZ 3) = true := by decide
theorem logicalX5_valid : isXLogical 5 (logicalX 5) = true := by native_decide
theorem logicalZ5_valid : isZLogical 5 (logicalZ 5) = true := by native_decide
theorem logicalX7_valid : isXLogical 7 (logicalX 7) = true := by native_decide
theorem logicalZ7_valid : isZLogical 7 (logicalZ 7) = true := by native_decide

/-- **X̄ of the GE2021 distance-27 patch is a valid logical operator.** -/
theorem logicalX27_valid : isXLogical 27 (logicalX 27) = true := by native_decide

/-- **Z̄ of the GE2021 distance-27 patch is a valid logical operator.** -/
theorem logicalZ27_valid : isZLogical 27 (logicalZ 27) = true := by native_decide

/-- X̄ and Z̄ anticommute (they meet at exactly one qubit, the corner) — a
genuine logical pair. -/
theorem logicalXZ27_anticommute : gf2dot (logicalX 27) (logicalZ 27) = true := by
  native_decide

/-- The X̄ support has the code distance `d` (a length-`d` string). -/
theorem logicalXSupp27_length : (logicalXSupp 27).length = 27 := by decide

end FormalRV.QEC.Codes.Surface
