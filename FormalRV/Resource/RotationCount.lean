/-
  FormalRV.Resource.RotationCount
  ───────────────────────────────
  The canonical, INDEPENDENT resource counters for the Pauli-rotation IR
  (`PauliRotation/Syntax.lean` — the Litinski layer between circuits and PPM).

  Same discipline as the rest of `Resource/`: imports ONLY the leaf IR, never
  a semantics, compiler, or gadget builder, so a count theorem cannot fudge —
  the number is forced by the program's syntax tree, and a skeptic can `#eval`
  the counters on any constructed rotation program without reading a proof.

  TIME readouts:
    • `countPi8`   — π/8 (T-level) rotations: THE T-count of the program
                     (the only non-Clifford angle).
    • `countAngle` — rotations at any given angle level.
    • `countRot`   — all rotations.
    • `depth`      — number of parallel layers: the PARALLEL logical depth
                     (the whole point of the layer structure — grouped
                     commuting rotations cost ONE time step, not many).
  SPACE: the IR's own `RotProg.width` (logical data qubits; this layer has
  no ancillas) is the space readout.
-/
import FormalRV.PauliRotation.Syntax

namespace FormalRV.Resource

open FormalRV.PauliRotation

/-! ## §1. Per-layer counters (honest structural walks). -/

/-- Rotations at angle `a` in one layer. -/
def countAngleL (a : RAngle) (L : RotLayer) : Nat :=
  L.countP (fun r => r.angle == a)

/-- All rotations in one layer. -/
def countRotL (L : RotLayer) : Nat := L.length

/-! ## §2. Program counters. -/

/-- **Rotations at angle `a`** in a program. -/
def countAngle (a : RAngle) : RotProg → Nat
  | []     => 0
  | L :: p => countAngleL a L + countAngle a p

/-- **The T-count**: π/8 rotations are the only non-Clifford content. -/
def countPi8 (p : RotProg) : Nat := countAngle .piEighth p

/-- **Total rotation count.** -/
def countRot : RotProg → Nat
  | []     => 0
  | L :: p => countRotL L + countRot p

/-- **Parallel logical depth**: each layer of pairwise-commuting rotations is
one parallel time step. -/
def rotDepth (p : RotProg) : Nat := p.length

/-! ## §3. Compositional laws. -/

theorem countAngle_append (a : RAngle) (p q : RotProg) :
    countAngle a (p ++ q) = countAngle a p + countAngle a q := by
  induction p with
  | nil => simp [countAngle]
  | cons L t ih =>
      show countAngleL a L + countAngle a (t ++ q) = _
      rw [ih]
      show countAngleL a L + (countAngle a t + countAngle a q)
          = countAngleL a L + countAngle a t + countAngle a q
      omega

theorem countPi8_append (p q : RotProg) :
    countPi8 (p ++ q) = countPi8 p + countPi8 q :=
  countAngle_append .piEighth p q

theorem countRot_append (p q : RotProg) :
    countRot (p ++ q) = countRot p + countRot q := by
  induction p with
  | nil => simp [countRot]
  | cons L t ih =>
      show countRotL L + countRot (t ++ q) = _
      rw [ih]
      show countRotL L + (countRot t + countRot q)
          = countRotL L + countRot t + countRot q
      omega

theorem rotDepth_append (p q : RotProg) :
    rotDepth (p ++ q) = rotDepth p + rotDepth q := by
  simp [rotDepth]

/-! ## §4. Reconciliation: the four angle counters partition the total.

Two independent walks (per-angle vs total) agree — `countRot` is exactly the
sum over the four angle levels, for every program. -/

private theorem countAngleL_partition (L : RotLayer) :
    countAngleL .pi L + countAngleL .piHalf L
      + countAngleL .piQuarter L + countAngleL .piEighth L = countRotL L := by
  induction L with
  | nil => rfl
  | cons r t ih =>
      simp only [countAngleL, countRotL, List.countP_cons, List.length_cons] at ih ⊢
      cases r.angle <;> simp <;> omega

theorem countRot_eq_angle_partition (p : RotProg) :
    countAngle .pi p + countAngle .piHalf p
      + countAngle .piQuarter p + countAngle .piEighth p = countRot p := by
  induction p with
  | nil => rfl
  | cons L t ih =>
      show countAngleL .pi L + countAngle .pi t
            + (countAngleL .piHalf L + countAngle .piHalf t)
            + (countAngleL .piQuarter L + countAngle .piQuarter t)
            + (countAngleL .piEighth L + countAngle .piEighth t)
          = countRotL L + countRot t
      have := countAngleL_partition L
      omega

/-! ## §5. Smoke checks (`#eval`-testable, `decide`-anchored). -/

open FormalRV.PPM.Prog in
example :  -- one layer of two parallel T's + one Clifford layer: T-count 2, depth 2
    countPi8 [[⟨false, .piEighth, [⟨0, .z⟩]⟩, ⟨false, .piEighth, [⟨1, .z⟩]⟩],
              [⟨true, .piQuarter, [⟨0, .z⟩, ⟨1, .x⟩]⟩]] = 2 := by decide

open FormalRV.PPM.Prog in
example :
    rotDepth [[⟨false, .piEighth, [⟨0, .z⟩]⟩, ⟨false, .piEighth, [⟨1, .z⟩]⟩],
           [⟨true, .piQuarter, [⟨0, .z⟩, ⟨1, .x⟩]⟩]] = 2 := by decide

open FormalRV.PPM.Prog in
example :
    countRot [[⟨false, .piEighth, [⟨0, .z⟩]⟩, ⟨false, .piEighth, [⟨1, .z⟩]⟩],
              [⟨true, .piQuarter, [⟨0, .z⟩, ⟨1, .x⟩]⟩]] = 3 := by decide

end FormalRV.Resource
