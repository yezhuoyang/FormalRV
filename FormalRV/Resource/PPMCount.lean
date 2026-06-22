/-
  FormalRV.Resource.PPMCount
  ──────────────────────────
  The canonical, INDEPENDENT resource counters for the PPM program IR
  (`PPM/Syntax/Program.lean` — John's `c2 = Measure X[0]Z[1]X[3]` /
  `if c2 == 1 then …` syntax).

  Same discipline as the rest of `Resource/`: this file imports ONLY the leaf
  IR (which itself imports nothing), never a semantics, compiler, or gadget
  builder — so a count theorem `countMeas (compilePPM g) = n` cannot fudge the
  count; the number is forced by the program's syntax tree, and a skeptic can
  `#eval` the counters on any constructed program without reading a proof.

  TIME counters: measurements, corrections (statements and worst-case fired
  frame ops), magic-state consumption (T / CCZ).  SPACE: the IR's own
  `PPMProg.width` (qubits) and `PPMProg.cwidth` (classical outcome slots) are
  re-exposed through the same interface.
-/
import FormalRV.PPM.Syntax.Program

namespace FormalRV.Resource

open FormalRV.PPM.Prog

/-! ## §1. Per-statement counters (honest pattern matches on the IR). -/

/-- Pauli-product measurements (the dominant PPM cost unit). -/
def countMeasS : PPMStmt → Nat
  | .measure ..     => 1
  | .measureSel ..  => 1
  | .measureSel2 .. => 1
  | _               => 0

/-- Conditional-correction statements. -/
def countCorrectS : PPMStmt → Nat
  | .correct ..  => 1
  | .correctQ .. => 1
  | _            => 0

/-- T magic states consumed. -/
def countMagicTS : PPMStmt → Nat
  | .useT _ => 1
  | _       => 0

/-- CCZ magic states consumed. -/
def countMagicCCZS : PPMStmt → Nat
  | .useCCZ .. => 1
  | _          => 0

/-! ## §2. Program counters (structural walks). -/

/-- **Measurement count** of a PPM program. -/
def countMeas : PPMProg → Nat
  | []     => 0
  | s :: p => countMeasS s + countMeas p

/-- **Correction-statement count** of a PPM program. -/
def countCorrect : PPMProg → Nat
  | []     => 0
  | s :: p => countCorrectS s + countCorrect p

/-- **T-magic count** of a PPM program. -/
def countMagicT : PPMProg → Nat
  | []     => 0
  | s :: p => countMagicTS s + countMagicT p

/-- **CCZ-magic count** of a PPM program. -/
def countMagicCCZ : PPMProg → Nat
  | []     => 0
  | s :: p => countMagicCCZS s + countMagicCCZ p

/-- **Total magic count** (T + CCZ). -/
def countMagic (p : PPMProg) : Nat := countMagicT p + countMagicCCZ p

/-! ## §3. Compositional laws. -/

theorem countMeas_append (p q : PPMProg) :
    countMeas (p ++ q) = countMeas p + countMeas q := by
  induction p with
  | nil => simp [countMeas]
  | cons s t ih =>
      show countMeasS s + countMeas (t ++ q) = countMeasS s + countMeas t + countMeas q
      rw [ih]; omega

theorem countCorrect_append (p q : PPMProg) :
    countCorrect (p ++ q) = countCorrect p + countCorrect q := by
  induction p with
  | nil => simp [countCorrect]
  | cons s t ih =>
      show countCorrectS s + countCorrect (t ++ q)
          = countCorrectS s + countCorrect t + countCorrect q
      rw [ih]; omega

theorem countMagicT_append (p q : PPMProg) :
    countMagicT (p ++ q) = countMagicT p + countMagicT q := by
  induction p with
  | nil => simp [countMagicT]
  | cons s t ih =>
      show countMagicTS s + countMagicT (t ++ q)
          = countMagicTS s + countMagicT t + countMagicT q
      rw [ih]; omega

theorem countMagicCCZ_append (p q : PPMProg) :
    countMagicCCZ (p ++ q) = countMagicCCZ p + countMagicCCZ q := by
  induction p with
  | nil => simp [countMagicCCZ]
  | cons s t ih =>
      show countMagicCCZS s + countMagicCCZ (t ++ q)
          = countMagicCCZS s + countMagicCCZ t + countMagicCCZ q
      rw [ih]; omega

theorem countMagic_append (p q : PPMProg) :
    countMagic (p ++ q) = countMagic p + countMagic q := by
  unfold countMagic
  rw [countMagicT_append, countMagicCCZ_append]; omega

/-- The classical width IS the measurement count (each measurement binds
exactly one outcome slot) — two independent walks reconciled. -/
theorem cwidth_eq_countMeas (p : PPMProg) :
    PPMProg.cwidth p = countMeas p := by
  induction p with
  | nil => rfl
  | cons s t ih =>
      show s.binds + PPMProg.cwidth t = countMeasS s + countMeas t
      rw [ih]
      cases s <;> rfl

/-! ## §4. Smoke checks (`#eval`-testable, `decide`-anchored). -/

example :
    countMeas [.useT 1, .measure 0 [⟨0, .z⟩, ⟨1, .z⟩],
               .correct [0] [⟨1, .x⟩] []] = 1 := by decide
example :
    countMagicT [.useT 1, .measure 0 [⟨0, .z⟩], .useT 0] = 2 := by decide
example :
    countCorrect [.measure 0 [⟨0, .z⟩], .correct [0] [⟨1, .x⟩] [],
                  .correct [0] [⟨0, .z⟩] [⟨1, .z⟩]] = 2 := by decide

end FormalRV.Resource
