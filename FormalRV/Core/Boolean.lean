/-
  FormalRV.Framework.Boolean — boolean helpers used in arithmetic
  correctness proofs.

  Centralizes the small set of Boolean operations BQ-Algo needs (majority,
  half-add carry, full-add carry-out) so each correctness proof can refer to
  a named function instead of an inlined expression.
-/

namespace FormalRV.Framework.Boolean

/-- Majority of three Boolean values: true iff at least two are true.
    Equivalently: the carry-out of a full adder. -/
def majority (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

/-- Smoke checks: all 8 cases. -/
example : majority false false false = false := by decide
example : majority true  false false = false := by decide
example : majority false true  false = false := by decide
example : majority false false true  = false := by decide
example : majority true  true  false = true  := by decide
example : majority true  false true  = true  := by decide
example : majority false true  true  = true  := by decide
example : majority true  true  true  = true  := by decide

/-- The Cuccaro MAJ gate replaces qubit `c` with the majority of
    its three inputs. Algebraically:
      majority(a,b,c) = c ⊕ ((a ⊕ c) ∧ (b ⊕ c))
    This is what makes MAJ implementable as 2 CX + 1 CCX. -/
theorem majority_eq_cuccaro_form (a b c : Bool) :
    majority a b c = (xor c ((xor a c) && (xor b c))) := by
  cases a <;> cases b <;> cases c <;> decide

end FormalRV.Framework.Boolean
