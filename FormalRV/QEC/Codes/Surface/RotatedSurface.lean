/-
  FormalRV.QEC.Codes.Surface.RotatedSurface
  ─────────────────────────────────────────
  **THE ROTATED SURFACE CODE `[[d², 1, d]]`** — the footprint-exact patch
  Gidney–Ekerå (and every lattice-surgery layout) actually use: `d²` data
  qubits and `d² − 1` syndrome qubits, versus the unrotated HGP's
  `d² + (d−1)²` data.

  Construction (the standard rotated planar lattice, verified orthogonal in
  `PyCircuits`-style enumeration before porting): data qubits on a `d × d`
  grid `idx r c = r·d + c`; one stabilizer per active dual-lattice face
  `(a, b)`, `a, b ∈ [0, d]`, supported on the in-grid corners
  `{(a−1,b−1), (a−1,b), (a,b−1), (a,b)}`.  A face is X-type iff `a + b` is
  even (Z-type iff odd); the boundary trim — drop corner faces, keep only
  X on the top/bottom face-edges and only Z on the left/right — is EXACTLY
  what forces every X·Z overlap even (an adjacent X–Z pair on a clipped
  boundary would share one qubit; the trim deletes precisely those).

  Reuses the existing `CSSCode` / `orthogonal` / `BoolMat` layer; validity
  is `decide` at `d = 3` and `native_decide` at the distances an audit
  needs (the parametric CSS proof is the geometric even-overlap argument,
  tracked as the remaining step).
-/
import FormalRV.QEC.CSSCode

namespace FormalRV.QEC.Codes.Surface

open FormalRV.QEC
open FormalRV.Framework.LDPC

/-! ## §1. The face → support construction. -/

/-- Linear index of data qubit `(r, c)` in the `d × d` grid. -/
def ridx (d r c : Nat) : Nat := r * d + c

/-- The in-grid data qubits supported by dual face `(a, b)` (its four
corner data qubits `{(a−1,b−1),(a−1,b),(a,b−1),(a,b)}` clipped to the
grid).  `Nat` underflow is guarded by the `1 ≤ a` / `1 ≤ b` tests. -/
def faceSupp (d a b : Nat) : List Nat :=
  (if 1 ≤ a ∧ 1 ≤ b then [ridx d (a - 1) (b - 1)] else [])
    ++ (if 1 ≤ a ∧ b < d then [ridx d (a - 1) b] else [])
    ++ (if a < d ∧ 1 ≤ b then [ridx d a (b - 1)] else [])
    ++ (if a < d ∧ b < d then [ridx d a b] else [])

/-- A face carries a stabilizer: nonempty support, not a corner face, and
the boundary trim (top/bottom face-edges keep only X-type `(a+b)` even;
left/right keep only Z-type `(a+b)` odd). -/
def faceActive (d a b : Nat) : Bool :=
  let onTB := a == 0 || a == d
  let onLR := b == 0 || b == d
  !(faceSupp d a b).isEmpty
    && !(onTB && onLR)
    && (!onTB || (a + b) % 2 == 0)
    && (!onLR || (a + b) % 2 == 1)

/-- Active faces of a given checkerboard colour (`xColour = true` ⇒ X-type,
`a+b` even). -/
def colourFaces (d : Nat) (xColour : Bool) : List (Nat × Nat) :=
  ((List.range (d + 1)).flatMap (fun a =>
    (List.range (d + 1)).map (fun b => (a, b)))).filter
      (fun p => faceActive d p.1 p.2
        && ((p.1 + p.2) % 2 == 0) == xColour)

/-- A support as a length-`d²` Boolean row. -/
def suppRow (d : Nat) (supp : List Nat) : BoolVec :=
  (List.range (d * d)).map (fun q => decide (q ∈ supp))

/-- The check matrix of one colour. -/
def colourChecks (d : Nat) (xColour : Bool) : BoolMat :=
  (colourFaces d xColour).map (fun p => suppRow d (faceSupp d p.1 p.2))

/-- **The rotated surface code `[[d², 1, d]]`.** -/
def rotatedSurface (d : Nat) : CSSCode :=
  { n := d * d
    hx := colourChecks d true
    hz := colourChecks d false }

/-! ## §2. Structural facts. -/

/-- `d²` data qubits — the footprint-exact count (vs the unrotated
`d² + (d−1)²`). -/
@[simp] theorem rotatedSurface_n (d : Nat) : (rotatedSurface d).n = d * d := rfl

/-- Every check row has length `d²` (well-shaped by construction). -/
theorem suppRow_length (d : Nat) (supp : List Nat) :
    (suppRow d supp).length = d * d := by
  unfold suppRow
  rw [List.length_map, List.length_range]

theorem colourChecks_rows_len (d : Nat) (xColour : Bool) :
    ∀ row ∈ colourChecks d xColour, row.length = d * d := by
  intro row hrow
  unfold colourChecks at hrow
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hrow
  exact suppRow_length d _

/-- **The rotated patch is well-shaped at every distance** (parametric). -/
theorem rotatedSurface_well_shaped (d : Nat) :
    (rotatedSurface d).well_shaped = true := by
  unfold CSSCode.well_shaped FormalRV.Framework.LDPC.matrix_has_n_cols
  rw [Bool.and_eq_true]
  constructor <;> rw [List.all_eq_true] <;> intro row hrow <;>
    rw [decide_eq_true_eq]
  · exact colourChecks_rows_len d true row hrow
  · exact colourChecks_rows_len d false row hrow

/-! ## §3. Validity at concrete distances (the audit instances). -/

/-- `d = 3`: the [[9,1,3]] rotated code is a valid CSS code (kernel). -/
theorem rotatedSurface3_valid : (rotatedSurface 3).valid = true := by decide

/-- `d = 3`: 8 stabilizers (`d² − 1`), 4 X + 4 Z. -/
theorem rotatedSurface3_counts :
    (rotatedSurface 3).hx.length = 4 ∧ (rotatedSurface 3).hz.length = 4 := by
  decide

/-- `d = 5`: the [[25,1,5]] rotated code is valid CSS. -/
theorem rotatedSurface5_valid : (rotatedSurface 5).valid = true := by
  native_decide

/-- `d = 7`: the [[49,1,7]] rotated code is valid CSS. -/
theorem rotatedSurface7_valid : (rotatedSurface 7).valid = true := by
  native_decide

/-! ## §4. Syndrome-qubit accounting (footprint-exact). -/

/-- Total syndrome qubits of the rotated patch: `|hx| + |hz|`. -/
def rotatedSyndromeQubits (d : Nat) : Nat :=
  (rotatedSurface d).hx.length + (rotatedSurface d).hz.length

/-- Total physical qubits of one syndrome-extraction round of the rotated
patch: `d²` data `+` syndrome ancillas. -/
def rotatedPhysicalQubits (d : Nat) : Nat :=
  (rotatedSurface d).n + rotatedSyndromeQubits d

/-- `d = 3`: 9 data + 8 syndrome = 17 physical. -/
theorem rotated3_physical : rotatedPhysicalQubits 3 = 17 := by decide

/-- `d = 5`: 25 data + 24 syndrome = 49 physical. -/
theorem rotated5_physical : rotatedPhysicalQubits 5 = 49 := by native_decide

/-! ## §5. The GE2021 audit instance: the rotated `[[729, 1, 27]]` patch. -/

/-- **The GE2021 data patch — the ACTUAL rotated surface code the paper
uses, VERIFIED valid CSS at distance 27** (`native_decide`, ≈7 s). -/
theorem rotatedSurface27_valid : (rotatedSurface 27).valid = true := by
  native_decide

/-- `d = 27`: 729 data qubits, 364 X-checks + 364 Z-checks = 728 syndrome
(`= d² − 1`). -/
theorem rotatedSurface27_counts :
    (rotatedSurface 27).n = 729
      ∧ (rotatedSurface 27).hx.length = 364
      ∧ (rotatedSurface 27).hz.length = 364 := by
  refine ⟨rfl, ?_, ?_⟩ <;> native_decide

/-- **The footprint-exact GE2021 patch**: 729 data + 728 syndrome = 1457
physical qubits per extraction round — the paper's rotated `[[729,1,27]]`
patch BEFORE inter-patch spacing (`2(d+1)² = 1568` adds the 111-qubit
routing border). -/
theorem rotated27_physical : rotatedPhysicalQubits 27 = 1457 := by
  unfold rotatedPhysicalQubits rotatedSyndromeQubits
  rw [(rotatedSurface27_counts).2.1, (rotatedSurface27_counts).2.2]
  rfl

/-- The paper's per-patch footprint `2(d+1)²` decomposes EXACTLY as the
rotated patch (data + syndrome) plus the routing border. -/
theorem rotated27_vs_paper_footprint :
    rotatedPhysicalQubits 27 = 1457        -- data + syndrome (this code)
      ∧ 2 * (27 + 1) * (27 + 1) = 1568     -- paper per-patch (with spacing)
      ∧ 1568 - 1457 = 111 := by            -- the routing border
  exact ⟨rotated27_physical, by decide, by decide⟩

end FormalRV.QEC.Codes.Surface
