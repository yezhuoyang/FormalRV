/-
  FormalRV.Basic — shared primitives for the qianxu.pdf gap review.

  Contains the surgery-cycle cost τ_s and a few foundational defs that
  every gap module depends on. Lean 4 core only (no mathlib).

  Per CLAUDE.md "Hard rules": every numerical claim in a gap module must
  be a `lake build`-passing Lean lemma. This file is the foundation those
  lemmas build on.

  Refs: qianxu.pdf App. E §1, p. 21 (Eq. E1 surgery cycle cost).
-/

namespace FormalRV

/-- Surgery-cycle cost in stabilizer-measurement cycles, as a function of
    the processor-code distance `d`. From qianxu p. 21: "τ_s ≈ 2d/3".
    Integer division is fine here; the paper's `≈` already absorbs the
    rounding. -/
def tau_s (d : Nat) : Nat := 2 * d / 3

/-- For d = 12 (a plausible processor-code distance): τ_s = 8 cycles. -/
example : tau_s 12 = 8 := by decide

/-- For d = 18: τ_s = 12 cycles. -/
example : tau_s 18 = 12 := by decide

/-- Sanity: τ_s is monotone in d (for the values we care about). -/
example : tau_s 12 ≤ tau_s 18 := by decide

end FormalRV
