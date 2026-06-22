/-
  FormalRV.PauliRotation.Compiler.ToPPM.CCZLane
  ────────────────────────────────────
  **THE 1-CCZ LOWERING MODE — statements, recognizer, economics.**

  `cczBlock d₁ d₂ d₃ a c` is THE PPM program of the CCZ-state teleport
  (Qiskit-validated branch-exact on all 64 branches):

      useCCZ[a,a+1,a+2];
      c   = Measure Z[d₁]Z[a];   c+1 = Measure Z[d₂]Z[a+1];
      c+2 = Measure Z[d₃]Z[a+2];
      c+3 = MeasureSel2 (c+2; c+1) X[a]…          (CZ-conjugated bases)
      c+4 = MeasureSel2 (c+2; c)   X[a+1]…
      c+5 = MeasureSel2 (c+1; c)   X[a+2]…
      if c+3 ^^ (c+1)*(c+2) == 1 then Z[d₁];      (quadratic corrections)
      if c+4 ^^ c*(c+2)     == 1 then Z[d₂];
      if c+5 ^^ c*(c+1)     == 1 then Z[d₃]

  `isCCZRots` recognizes the dictionary's seven-π/8 CCZ phase polynomial,
  and the count theorems give THE VERIFIED 8T-vs-1CCZ ECONOMICS:
  route A consumes 7 |T⟩; route B consumes 1 |CCZ⟩ (factory: 8 |T⟩).
-/
import FormalRV.PauliRotation.Compiler.ToPPM.CCZBlock

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource
open Matrix

/-! ## §1. The block program. -/

/-- The CCZ-state teleport block on data `d₁ d₂ d₃`, resource ancillas
`a, a+1, a+2`, outcome slots `c..c+5`. -/
def cczBlock (d₁ d₂ d₃ a c : Nat) : PPMProg :=
  [.useCCZ a (a + 1) (a + 2),
   .measure c       [⟨d₁, .z⟩, ⟨a, .z⟩],
   .measure (c + 1) [⟨d₂, .z⟩, ⟨a + 1, .z⟩],
   .measure (c + 2) [⟨d₃, .z⟩, ⟨a + 2, .z⟩],
   .measureSel2 [c + 2] [c + 1] (c + 3)
     [⟨a, .x⟩] [⟨a, .x⟩, ⟨a + 2, .z⟩]
     [⟨a, .x⟩, ⟨a + 1, .z⟩] [⟨a, .x⟩, ⟨a + 1, .z⟩, ⟨a + 2, .z⟩],
   .measureSel2 [c + 2] [c] (c + 4)
     [⟨a + 1, .x⟩] [⟨a + 1, .x⟩, ⟨a + 2, .z⟩]
     [⟨a, .z⟩, ⟨a + 1, .x⟩] [⟨a, .z⟩, ⟨a + 1, .x⟩, ⟨a + 2, .z⟩],
   .measureSel2 [c + 1] [c] (c + 5)
     [⟨a + 2, .x⟩] [⟨a + 1, .z⟩, ⟨a + 2, .x⟩]
     [⟨a, .z⟩, ⟨a + 2, .x⟩] [⟨a, .z⟩, ⟨a + 1, .z⟩, ⟨a + 2, .x⟩],
   .correctQ [[c + 3], [c + 1, c + 2]] [⟨d₁, .z⟩] [],
   .correctQ [[c + 4], [c, c + 2]]     [⟨d₂, .z⟩] [],
   .correctQ [[c + 5], [c, c + 1]]     [⟨d₃, .z⟩] []]

/-! ## §2. Counts: THE VERIFIED 8T-vs-1CCZ ECONOMICS. -/

/-- Route B consumes EXACTLY ONE CCZ magic state. -/
theorem cczBlock_magicCCZ (d₁ d₂ d₃ a c : Nat) :
    countMagicCCZ (cczBlock d₁ d₂ d₃ a c) = 1 := rfl

/-- Route B consumes NO T states. -/
theorem cczBlock_magicT (d₁ d₂ d₃ a c : Nat) :
    countMagicT (cczBlock d₁ d₂ d₃ a c) = 0 := rfl

/-- Route B: six measurements, six outcome slots. -/
theorem cczBlock_meas (d₁ d₂ d₃ a c : Nat) :
    countMeas (cczBlock d₁ d₂ d₃ a c) = 6 := rfl

theorem cczBlock_cwidth (d₁ d₂ d₃ a c : Nat) :
    PPMProg.cwidth (cczBlock d₁ d₂ d₃ a c) = 6 := rfl

/-- Route A (the dictionary's seven-π/8 phase polynomial, lowered
rotation-by-rotation) consumes EXACTLY SEVEN T states. -/
theorem cczRoute7T_magicT (x y z a c : Nat) :
    countMagicT (lowerFlat a c (cczGate x y z).flatten) = 7 := by
  rw [lowerFlat_magicT]
  rfl

/-- **THE 8T-vs-1CCZ TRADE, VERIFIED**: per CCZ layer, route A costs
7 |T⟩ and 0 |CCZ⟩; route B costs 0 |T⟩ and 1 |CCZ⟩ (one factory output;
the standard factory distills it from 8 |T⟩).  Which is cheaper is now an
AUDIT-LEVEL knob on verified numbers, not a modelling assumption. -/
theorem ccz_route_tradeoff (x y z a c d₁ d₂ d₃ a' c' : Nat) :
    countMagicT (lowerFlat a c (cczGate x y z).flatten) = 7
      ∧ countMagicCCZ (lowerFlat a c (cczGate x y z).flatten) = 0
      ∧ countMagicT (cczBlock d₁ d₂ d₃ a' c') = 0
      ∧ countMagicCCZ (cczBlock d₁ d₂ d₃ a' c') = 1 :=
  ⟨cczRoute7T_magicT x y z a c, lowerFlat_magicCCZ _ a c,
   cczBlock_magicT d₁ d₂ d₃ a' c', cczBlock_magicCCZ d₁ d₂ d₃ a' c'⟩

/-! ## §3. The recognizer. -/

/-- Recognize the dictionary's CCZ phase polynomial (the exact
seven-rotation pattern `cczGate x y z` emits, `x < y < z`). -/
def isCCZRots : List Rot → Option (Nat × Nat × Nat)
  | [⟨false, .piEighth, [⟨x₁, .z⟩]⟩,
     ⟨false, .piEighth, [⟨y₁, .z⟩]⟩,
     ⟨false, .piEighth, [⟨z₁, .z⟩]⟩,
     ⟨true,  .piEighth, [⟨x₂, .z⟩, ⟨y₂, .z⟩]⟩,
     ⟨true,  .piEighth, [⟨x₃, .z⟩, ⟨z₂, .z⟩]⟩,
     ⟨true,  .piEighth, [⟨y₃, .z⟩, ⟨z₃, .z⟩]⟩,
     ⟨false, .piEighth, [⟨x₄, .z⟩, ⟨y₄, .z⟩, ⟨z₄, .z⟩]⟩] =>
      if x₁ = x₂ ∧ x₁ = x₃ ∧ x₁ = x₄ ∧ y₁ = y₂ ∧ y₁ = y₃ ∧ y₁ = y₄
          ∧ z₁ = z₂ ∧ z₁ = z₃ ∧ z₁ = z₄ ∧ x₁ < y₁ ∧ y₁ < z₁
      then some (x₁, y₁, z₁) else none
  | _ => none

/-- The recognizer is SOUND: a hit IS the dictionary's CCZ polynomial. -/
theorem isCCZRots_sound (rs : List Rot) (x y z : Nat)
    (h : isCCZRots rs = some (x, y, z)) :
    rs = (cczGate x y z).flatten ∧ x < y ∧ y < z := by
  unfold isCCZRots at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hc
      injection h with h'
      obtain ⟨hx, hy, hz⟩ : _ ∧ _ ∧ _ := by
        simpa [Prod.ext_iff] using h'
      subst hx hy hz h2 h3 h4 h5 h6 h7 h8 h9 h10
      exact ⟨rfl, h11, h12⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The recognizer FIRES on every dictionary CCZ (completeness on the
compiler's own output). -/
theorem isCCZRots_complete (x y z : Nat) (hxy : x < y) (hyz : y < z) :
    isCCZRots (cczGate x y z).flatten = some (x, y, z) := by
  simp [isCCZRots, cczGate, hxy, hyz]

end FormalRV.PauliRotation
