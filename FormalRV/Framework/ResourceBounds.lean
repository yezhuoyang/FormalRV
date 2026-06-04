/-
  FormalRV.Framework.ResourceBounds — a GENERAL, reusable framework for auditing a
  paper's resource estimate by BRACKETING it between a verified LOWER bound
  (irreducible: data block / critical path) and a verified naive-construction UPPER
  bound, and quantifying the optimization GAP the paper claims over the naive build.

  This is the framework-level generalisation of the project's "naive upper bound +
  gap" pattern (System/NaiveUpperBound, Corpus/GidneyEkera2021Reproduction): a single
  `ResourceBounds` carries (lower, upper, reported), with decidable soundness /
  bracketing checks and the gap, applicable to ANY resource (qubits, time) of ANY
  paper.  The honest reading:
    • lower ≤ reported : the paper respects the irreducible floor (else suspicious);
    • reported ≤ upper : the paper is at least as efficient as our naive build;
    • upper − reported : the optimization the paper claims but we did NOT construct
      (the GAP).

  No Mathlib.  No `sorry`, no `axiom`.
-/

namespace FormalRV.Framework.Resource

/-- A resource bound: an irreducible LOWER bound, a naive-construction UPPER bound,
    and the paper's REPORTED figure. -/
structure ResourceBounds where
  lower    : Nat
  upper    : Nat
  reported : Nat
  deriving Repr, DecidableEq, Inhabited

namespace ResourceBounds

/-- The bounds are SOUND: the lower bound does not exceed the naive upper bound. -/
def sound (b : ResourceBounds) : Bool := decide (b.lower ≤ b.upper)

/-- The paper respects the irreducible floor (its claim is ≥ our lower bound). -/
def respectsFloor (b : ResourceBounds) : Bool := decide (b.lower ≤ b.reported)

/-- The paper is within our naive upper bound (at least as efficient). -/
def withinNaive (b : ResourceBounds) : Bool := decide (b.reported ≤ b.upper)

/-- The reported figure is BRACKETED: floor ≤ reported ≤ naive upper. -/
def bracketed (b : ResourceBounds) : Bool := b.respectsFloor && b.withinNaive

/-- The optimization GAP: how much the paper saves vs the naive construction. -/
def optimizationGap (b : ResourceBounds) : Nat := b.upper - b.reported

/-! ## Soundness lemmas -/

/-- A bracketed estimate is sound (lower ≤ upper), since lower ≤ reported ≤ upper. -/
theorem bracketed_sound (b : ResourceBounds) (h : b.bracketed = true) : b.sound = true := by
  unfold bracketed respectsFloor withinNaive at h
  unfold sound
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  omega

/-- Bracketing splits into the two one-sided facts. -/
theorem bracketed_iff (b : ResourceBounds) :
    b.bracketed = true ↔ (b.lower ≤ b.reported ∧ b.reported ≤ b.upper) := by
  unfold bracketed respectsFloor withinNaive
  simp [Bool.and_eq_true, decide_eq_true_eq]

/-- If bracketed, the reported figure plus the optimization gap recovers the naive
    upper bound — the gap is exactly the unconstructed optimization. -/
theorem reported_add_gap (b : ResourceBounds) (h : b.withinNaive = true) :
    b.reported + b.optimizationGap = b.upper := by
  unfold withinNaive at h; unfold optimizationGap
  simp only [decide_eq_true_eq] at h
  omega

end ResourceBounds
end FormalRV.Framework.Resource
