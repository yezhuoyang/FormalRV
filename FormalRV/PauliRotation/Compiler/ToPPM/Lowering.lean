/-
  FormalRV.PauliRotation.Compiler.ToPPM.Lowering
  ─────────────────────────────────────
  **THE LOWERING `Rot → PPMProg` AND ITS BRANCH SEMANTICS.**

  §1 `stmtDenote`/`progDenote` — the per-outcome-branch MATRIX denotation
     of PPM programs (the denotational side of the operational `run`):
     measurements apply branch projectors, `measureSel` applies the
     parity-SELECTED projector, frames and fired corrections apply their
     Pauli matrices IMMEDIATELY (the decided convention), magic markers
     are semantically inert (resource audit only).

  §2 `lowerRot`/`lowerFlat` — one rotation becomes one teleport block:

       π      ↦  (global phase −1; handled by the proven `dropPi` pre-pass)
       π/2    ↦  frame P                                  (phase −i tracked)
       π/4    ↦  |Y⟩-block:  c = Measure P·Z[a]; c' = Measure X[a];
                              if c ^^ c' == 1 then P      (S-block, proven)
       π/8    ↦  |T⟩-block:  useT[a]; c = Measure P·Z[a];
                              c' = MeasureIf c then Y[a] else X[a];
                              if c' == 1 then P           (T-block, proven)

     Each π/4 and π/8 block consumes ONE fresh ancilla (wire counter `a`)
     and binds TWO outcome slots (counter `c`).  Negative π/4 appends a
     `frame P` (since `e^{+iπ/4P} = iP·e^{−iπ/4P}`); negative π/8 uses the
     `|T†⟩` chirality of the SAME statements (the ancilla-state convention
     of the correctness theorem; the magic audit is identical).

  §3 Count transfer: `countMagicT ∘ lowerFlat` = number of π/8 rotations
     (THE T-count), measurement/slot bookkeeping, and well-formedness.
-/
import FormalRV.PauliRotation.Compiler.ToPPM.SBlock
import FormalRV.PPM.Semantics.ProgramSemantics
import FormalRV.Resource.PPMCount

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource
open Matrix

/-! ## §1. Branch denotation of PPM programs. -/

/-- Per-outcome-branch matrix denotation of ONE statement at width `d`,
given the outcome trace `outs` so far and this statement's `outcome`. -/
noncomputable def stmtDenote (d : Nat) (outs : List Bool) (outcome : Bool) :
    PPMStmt → Matrix (Fin (2 ^ d)) (Fin (2 ^ d)) ℂ
  | .measure _ P => projHalf (axisMat d P) outcome
  | .measureSel sel _ Pt Pe =>
      projHalf (axisMat d (if xorParity outs sel then Pt else Pe)) outcome
  | .measureSel2 sel1 sel2 _ P00 P01 P10 P11 =>
      projHalf (axisMat d
        (if xorParity outs sel1 then
          (if xorParity outs sel2 then P11 else P10)
         else (if xorParity outs sel2 then P01 else P00))) outcome
  | .frame P => axisMat d P
  | .correct par thn els =>
      if xorParity outs par then axisMat d thn else axisMat d els
  | .correctQ mons thn els =>
      if qParity outs mons then axisMat d thn else axisMat d els
  | .useT _ => 1
  | .useCCZ _ _ _ => 1

/-- Per-outcome-branch denotation of a program (later statements act on
the LEFT; the outcome stream `ω` indexes slots like the operational
`run`). -/
noncomputable def progDenote (d : Nat) (ω : Nat → Bool) :
    List Bool → PPMProg → Matrix (Fin (2 ^ d)) (Fin (2 ^ d)) ℂ
  | _, [] => 1
  | outs, st :: p =>
      progDenote d ω (outs ++ List.replicate st.binds (ω outs.length)) p
        * stmtDenote d outs (ω outs.length) st

/-! ## §2. The lowering. -/

/-- Ancillas one rotation consumes. -/
def rotAnc (r : Rot) : Nat :=
  match r.angle with
  | .piQuarter => 1
  | .piEighth  => 1
  | _          => 0

/-- Outcome slots one rotation binds. -/
def rotSlots (r : Rot) : Nat :=
  match r.angle with
  | .piQuarter => 2
  | .piEighth  => 2
  | _          => 0

/-- Lower ONE rotation at fresh ancilla `a`, next outcome slot `c`. -/
def lowerRot (a c : Nat) (r : Rot) : PPMProg :=
  match r.angle with
  | .pi     => []
  | .piHalf => [.frame r.axis]
  | .piQuarter =>
      [.measure c (r.axis ++ [⟨a, .z⟩]),
       .measure (c + 1) [⟨a, .x⟩],
       .correct [c, c + 1] r.axis []]
      ++ (if r.neg then [PPMStmt.frame r.axis] else [])
  | .piEighth =>
      [.useT a,
       .measure c (r.axis ++ [⟨a, .z⟩]),
       .measureSel [c] (c + 1) [⟨a, .y⟩] [⟨a, .x⟩],
       .correct (if r.neg then [c, c + 1] else [c + 1]) r.axis []]

/-- Lower a rotation sequence, threading the ancilla and slot counters. -/
def lowerFlat (a c : Nat) : List Rot → PPMProg
  | []      => []
  | r :: rs => lowerRot a c r ++ lowerFlat (a + rotAnc r) (c + rotSlots r) rs

/-! ## §3. Count transfer. -/

/-- π/8 rotations in a sequence (the sequence-level T-count). -/
def countPi8L (rs : List Rot) : Nat :=
  rs.countP (fun r => r.angle == RAngle.piEighth)

theorem lowerRot_magicT (a c : Nat) (r : Rot) :
    countMagicT (lowerRot a c r)
      = (if r.angle == RAngle.piEighth then 1 else 0) := by
  unfold lowerRot
  cases hr : r.angle <;> simp [countMagicT, countMagicTS]
  · cases r.neg <;> rfl

/-- **THE T-COUNT TRANSFERS EXACTLY**: the lowered program consumes one
T magic state per π/8 rotation — `countMagicT ∘ lower = countPi8`. -/
theorem lowerFlat_magicT (rs : List Rot) :
    ∀ (a c : Nat), countMagicT (lowerFlat a c rs) = countPi8L rs := by
  induction rs with
  | nil => intro a c; rfl
  | cons r t ih =>
      intro a c
      show countMagicT (lowerRot a c r ++ lowerFlat _ _ t) = _
      rw [countMagicT_append, lowerRot_magicT, ih]
      unfold countPi8L
      rw [List.countP_cons]
      omega

theorem lowerRot_cwidth (a c : Nat) (r : Rot) :
    PPMProg.cwidth (lowerRot a c r) = rotSlots r := by
  unfold lowerRot rotSlots
  cases hr : r.angle <;> simp [PPMProg.cwidth, PPMStmt.binds]
  · cases r.neg <;> rfl

/-- Slot bookkeeping: the lowered program binds exactly `2` slots per
π/4 and π/8 rotation. -/
theorem lowerFlat_cwidth (rs : List Rot) :
    ∀ (a c : Nat),
      PPMProg.cwidth (lowerFlat a c rs) = (rs.map rotSlots).sum := by
  induction rs with
  | nil => intro a c; rfl
  | cons r t ih =>
      intro a c
      show PPMProg.cwidth (lowerRot a c r ++ lowerFlat _ _ t) = _
      rw [PPMProg.cwidth_append, lowerRot_cwidth, ih]
      rfl

/-- No CCZ states are consumed by the rotation-by-rotation route (the
recognizer-driven `useCCZ` lane is the SECOND lowering mode). -/
theorem lowerFlat_magicCCZ (rs : List Rot) :
    ∀ (a c : Nat), countMagicCCZ (lowerFlat a c rs) = 0 := by
  induction rs with
  | nil => intro a c; rfl
  | cons r t ih =>
      intro a c
      show countMagicCCZ (lowerRot a c r ++ lowerFlat _ _ t) = _
      rw [countMagicCCZ_append, ih]
      unfold lowerRot
      cases hr : r.angle <;> simp [countMagicCCZ, countMagicCCZS]
      cases r.neg <;> rfl

end FormalRV.PauliRotation
