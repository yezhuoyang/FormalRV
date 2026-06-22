/-
  FormalRV.QEC.CodeBuilders — generic code constructors: block-diagonal
  DIRECT SUM and CSS DUAL, with validity-preservation theorems.

  ## Why (refactor goal 4)

  The multi-patch surgery demos hand-rolled both constructions twice:
  `SurgeryDemoMerge.surface3x2_qec` / `surface3x3_qec` build block-diagonal
  direct sums by hand, and `SurgeryDemoCNOT.surface3x2_dual` /
  `surface3x3_dual` hand-swap `hx`/`hz`.  Here both become generic helpers
  with PARAMETRIC validity preservation:

    * `CSSCode.directSum`  — `[[n₁+n₂, k₁+k₂]]` two independent patches as
      one code; preserves `well_shaped` and `css_condition` (the cross-block
      orthogonality is proven, not assumed);
    * `CSSCode.dual`       — swap X/Z checks; preserves both (via the
      GF(2) `dotBit` symmetry).

  The corpus hand-rolled instances are pinned equal to the generic builders
  (`decide` on the matrices), so the demos can be re-pointed at will.

  No Mathlib.  No `sorry`, no `axiom`.
-/

import FormalRV.QEC.CSSCode
import FormalRV.QEC.LogicalMeasurementGeneral
import FormalRV.QEC.LatticeSurgery.SurgeryDemoCNOT

namespace FormalRV.QEC

open FormalRV.Framework.LDPC

/-! ## GF(2) padding lemmas -/

private theorem countP_zip_zero_right (a : BoolVec) (m : Nat) :
    (a.zip (zero_vec m)).countP (fun p => p.1 && p.2) = 0 := by
  rw [List.countP_eq_zero]
  intro p hp
  have h2 := (List.of_mem_zip hp).2
  have : p.2 = false := by
    have := List.eq_of_mem_replicate (by simpa [zero_vec] using h2)
    exact this
  simp [this]

private theorem countP_zip_zero_left (a : BoolVec) (m : Nat) :
    ((zero_vec m).zip a).countP (fun p => p.1 && p.2) = 0 := by
  rw [List.countP_eq_zero]
  intro p hp
  have h1 := (List.of_mem_zip hp).1
  have : p.1 = false := by
    have := List.eq_of_mem_replicate (by simpa [zero_vec] using h1)
    exact this
  simp [this]

/-- Suffix-padding both vectors with zeros does not change the GF(2) dot. -/
private theorem dotBit_pad_suffix (a b : BoolVec) (m : Nat)
    (h : a.length = b.length) :
    dotBit (a ++ zero_vec m) (b ++ zero_vec m) = dotBit a b := by
  unfold dotBit
  rw [List.zip_append h, List.countP_append, countP_zip_zero_right]
  simp

/-- Prefix-padding both vectors with zeros does not change the GF(2) dot. -/
private theorem dotBit_pad_prefix (a b : BoolVec) (m : Nat) :
    dotBit (zero_vec m ++ a) (zero_vec m ++ b) = dotBit a b := by
  unfold dotBit
  rw [List.zip_append (by simp [zero_vec]), List.countP_append,
      countP_zip_zero_left]
  simp

/-- Cross-block rows are automatically orthogonal: one vector is supported
    on the first block, the other on the second. -/
private theorem dotBit_cross (a b : BoolVec) (n₁ m₂ : Nat)
    (h : a.length = n₁) :
    dotBit (a ++ zero_vec m₂) (zero_vec n₁ ++ b) = false := by
  unfold dotBit
  rw [List.zip_append (by simp [zero_vec, h]), List.countP_append,
      countP_zip_zero_left]
  -- a.zip (zero_vec n₁): right components all false
  rw [List.countP_eq_zero.mpr]
  · simp
  · intro p hp
    have h2 := (List.of_mem_zip hp).2
    have : p.2 = false := List.eq_of_mem_replicate (by simpa [zero_vec] using h2)
    simp [this]

/-! ## The builders -/

/-- Block-diagonal direct sum: two independent code patches as one CSS code
    (the generic form of the hand-rolled `surface3x2_qec`). -/
def CSSCode.directSum (c₁ c₂ : CSSCode) : CSSCode :=
  { n  := c₁.n + c₂.n
    hx := c₁.hx.map (fun r => r ++ zero_vec c₂.n)
            ++ c₂.hx.map (fun r => zero_vec c₁.n ++ r)
    hz := c₁.hz.map (fun r => r ++ zero_vec c₂.n)
            ++ c₂.hz.map (fun r => zero_vec c₁.n ++ r) }

/-- CSS dual: swap the X- and Z-check matrices (the generic form of the
    hand-rolled `surface3x2_dual`). -/
def CSSCode.dual (c : CSSCode) : CSSCode := ⟨c.n, c.hz, c.hx⟩

/-! ## Validity preservation -/

private theorem rows_have_n_cols (mat : BoolMat) (n : Nat)
    (h : matrix_has_n_cols mat n = true) :
    ∀ row ∈ mat, row.length = n := by
  rw [matrix_has_n_cols, List.all_eq_true] at h
  intro row hr
  have := h row hr
  simpa using this

/-- The dual of a well-shaped code is well-shaped. -/
theorem CSSCode.dual_well_shaped (c : CSSCode) (h : c.well_shaped = true) :
    c.dual.well_shaped = true := by
  rw [CSSCode.well_shaped, Bool.and_eq_true] at h ⊢
  exact ⟨h.2, h.1⟩

/-- The dual of a CSS code is CSS (GF(2) `dotBit` symmetry). -/
theorem CSSCode.dual_css_condition (c : CSSCode) (h : c.css_condition = true) :
    c.dual.css_condition = true := by
  rw [CSSCode.css_condition, orthogonal_iff] at h ⊢
  intro ra hra rb hrb
  rw [FormalRV.QEC.LogicalMeasurementGeneral.dotBit_comm]
  exact h rb hrb ra hra

/-- Duality preserves full validity. -/
theorem CSSCode.dual_valid (c : CSSCode) (h : c.valid = true) :
    c.dual.valid = true := by
  rw [CSSCode.valid, Bool.and_eq_true] at h ⊢
  exact ⟨c.dual_well_shaped h.1, c.dual_css_condition h.2⟩

/-- The direct sum of well-shaped codes is well-shaped (rows have length
    `n₁ + n₂`). -/
theorem CSSCode.directSum_well_shaped (c₁ c₂ : CSSCode)
    (h₁ : c₁.well_shaped = true) (h₂ : c₂.well_shaped = true) :
    (c₁.directSum c₂).well_shaped = true := by
  rw [CSSCode.well_shaped, Bool.and_eq_true] at h₁ h₂ ⊢
  have hx1 := rows_have_n_cols c₁.hx c₁.n h₁.1
  have hz1 := rows_have_n_cols c₁.hz c₁.n h₁.2
  have hx2 := rows_have_n_cols c₂.hx c₂.n h₂.1
  have hz2 := rows_have_n_cols c₂.hz c₂.n h₂.2
  constructor
  · rw [matrix_has_n_cols, List.all_eq_true]
    intro row hrow
    simp only [CSSCode.directSum, List.mem_append, List.mem_map] at hrow
    rcases hrow with ⟨r, hr, hre⟩ | ⟨r, hr, hre⟩ <;> subst hre <;>
      simp only [CSSCode.directSum, List.length_append, zero_vec,
                 List.length_replicate, decide_eq_true_eq]
    · rw [hx1 r hr]
    · rw [hx2 r hr]
  · rw [matrix_has_n_cols, List.all_eq_true]
    intro row hrow
    simp only [CSSCode.directSum, List.mem_append, List.mem_map] at hrow
    rcases hrow with ⟨r, hr, hre⟩ | ⟨r, hr, hre⟩ <;> subst hre <;>
      simp only [CSSCode.directSum, List.length_append, zero_vec,
                 List.length_replicate, decide_eq_true_eq]
    · rw [hz1 r hr]
    · rw [hz2 r hr]

/-- **The direct sum of CSS codes is CSS.**  Same-block pairs reduce to the
    component CSS conditions; cross-block pairs are orthogonal because their
    supports live on different blocks. -/
theorem CSSCode.directSum_css_condition (c₁ c₂ : CSSCode)
    (h₁ws : c₁.well_shaped = true) (h₂ws : c₂.well_shaped = true)
    (h₁ : c₁.css_condition = true) (h₂ : c₂.css_condition = true) :
    (c₁.directSum c₂).css_condition = true := by
  rw [CSSCode.well_shaped, Bool.and_eq_true] at h₁ws h₂ws
  have hx1 := rows_have_n_cols c₁.hx c₁.n h₁ws.1
  have hz1 := rows_have_n_cols c₁.hz c₁.n h₁ws.2
  have hx2 := rows_have_n_cols c₂.hx c₂.n h₂ws.1
  have hz2 := rows_have_n_cols c₂.hz c₂.n h₂ws.2
  rw [CSSCode.css_condition, orthogonal_iff] at h₁ h₂ ⊢
  intro ra hra rb hrb
  simp only [CSSCode.directSum, List.mem_append, List.mem_map] at hra hrb
  rcases hra with ⟨rx, hrx, hrxe⟩ | ⟨rx, hrx, hrxe⟩ <;>
    rcases hrb with ⟨rz, hrz, hrze⟩ | ⟨rz, hrz, hrze⟩ <;>
    subst hrxe <;> subst hrze
  · rw [dotBit_pad_suffix rx rz c₂.n (by rw [hx1 rx hrx, hz1 rz hrz])]
    exact h₁ rx hrx rz hrz
  · exact dotBit_cross rx rz c₁.n c₂.n (hx1 rx hrx)
  · rw [FormalRV.QEC.LogicalMeasurementGeneral.dotBit_comm]
    exact dotBit_cross rz rx c₁.n c₂.n (hz1 rz hrz)
  · rw [dotBit_pad_prefix rx rz c₁.n]
    exact h₂ rx hrx rz hrz

/-- Direct sum preserves full validity. -/
theorem CSSCode.directSum_valid (c₁ c₂ : CSSCode)
    (h₁ : c₁.valid = true) (h₂ : c₂.valid = true) :
    (c₁.directSum c₂).valid = true := by
  rw [CSSCode.valid, Bool.and_eq_true] at h₁ h₂ ⊢
  exact ⟨CSSCode.directSum_well_shaped c₁ c₂ h₁.1 h₂.1,
         CSSCode.directSum_css_condition c₁ c₂ h₁.1 h₂.1 h₁.2 h₂.2⟩

/-! ## Corpus pins: the hand-rolled instances ARE the generic builders -/

open FormalRV.LatticeSurgery.SurgeryDemoMerge
open FormalRV.LatticeSurgery.SurgeryDemoCNOT
open FormalRV.QEC.Instances

/-- The hand-rolled two-patch code of `SurgeryDemoMerge` is exactly the
    generic direct sum of two surface3 patches (matrix-level identity). -/
theorem surface3x2_hx_eq_directSum :
    surface3x2_qec.hx = ((surface3.directSum surface3).hx) := by decide

theorem surface3x2_hz_eq_directSum :
    surface3x2_qec.hz = ((surface3.directSum surface3).hz) := by decide

/-- The hand-rolled CSS dual of `SurgeryDemoCNOT` is exactly the generic
    dual of the two-patch code. -/
theorem surface3x2_dual_hx_eq :
    surface3x2_dual.hx = ((surface3.directSum surface3).dual.hx) := by decide

theorem surface3x2_dual_hz_eq :
    surface3x2_dual.hz = ((surface3.directSum surface3).dual.hz) := by decide

theorem surface3x2_n_eq :
    surface3x2_qec.n = (surface3.directSum surface3).n := by decide

theorem surface3x2_dual_n_eq :
    surface3x2_dual.n = ((surface3.directSum surface3).dual).n := by decide

end FormalRV.QEC
