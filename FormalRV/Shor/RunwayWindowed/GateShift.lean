/-
  FormalRV.Shor.RunwayWindowed.GateShift — generic gate index-shift transport.
  ════════════════════════════════════════════════════════════════════════════

  `Gate.shiftBy s g` adds `s` to every qubit index of `g`.  The transport theorem
  `applyNat_shiftBy` expresses the Boolean action of the shifted gate in terms of
  the unshifted one on the down-shifted state:

      applyNat (shiftBy s g) f p  =  if p < s then f p
                                     else applyNat g (fun q => f (q+s)) (p - s).

  This is the reusable infrastructure (none existed) that lets a base-0-proven
  reversible circuit (here: the oblivious-carry-runway adder) be re-based above a
  fixed low zone (here: the windowed lookup zone `[0,2w]`) and have its
  correctness TRANSPORTED rather than re-derived.  The runway/cuccaro
  translation-equivariance and the runway-correctness transport build on this.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Correctness

namespace FormalRV.Shor.RunwayWindowed.GateShift

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-- Shift every qubit index of a gate up by `s`. -/
def shiftBy (s : Nat) : Gate → Gate
  | Gate.I => Gate.I
  | Gate.X q => Gate.X (q + s)
  | Gate.CX c t => Gate.CX (c + s) (t + s)
  | Gate.CCX a b c => Gate.CCX (a + s) (b + s) (c + s)
  | Gate.seq g₁ g₂ => Gate.seq (shiftBy s g₁) (shiftBy s g₂)

/-- **The index-shift transport.**  The shifted gate acts on `[s, ∞)` exactly as
    the original acts on `[0, ∞)` (reading the state at offset `s`), and leaves
    `[0, s)` untouched. -/
theorem applyNat_shiftBy (s : Nat) (g : Gate) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (shiftBy s g) f
        = fun p => if p < s then f p
            else Gate.applyNat g (fun q => f (q + s)) (p - s) := by
  induction g with
  | I =>
    intro f; funext p
    show Gate.applyNat Gate.I f p = _
    by_cases hp : p < s
    · simp [hp]
    · simp only [Gate.applyNat, if_neg hp]
      rw [Nat.sub_add_cancel (Nat.le_of_not_lt hp)]
  | X q =>
    intro f; funext p
    show Gate.applyNat (Gate.X (q + s)) f p = _
    by_cases hp : p < s
    · simp only [Gate.applyNat, update, if_pos hp]
      rw [if_neg (by omega : ¬ p = q + s)]
    · simp only [Gate.applyNat, update, if_neg hp]
      by_cases hpq : p = q + s
      · subst hpq; simp
      · rw [if_neg hpq, if_neg (by omega : ¬ p - s = q),
            Nat.sub_add_cancel (Nat.le_of_not_lt hp)]
  | CX c t =>
    intro f; funext p
    show Gate.applyNat (Gate.CX (c + s) (t + s)) f p = _
    by_cases hp : p < s
    · simp only [Gate.applyNat, update, if_pos hp]
      rw [if_neg (by omega : ¬ p = t + s)]
    · simp only [Gate.applyNat, update, if_neg hp]
      by_cases hpt : p = t + s
      · subst hpt; simp
      · rw [if_neg hpt, if_neg (by omega : ¬ p - s = t),
            Nat.sub_add_cancel (Nat.le_of_not_lt hp)]
  | CCX a b c =>
    intro f; funext p
    show Gate.applyNat (Gate.CCX (a + s) (b + s) (c + s)) f p = _
    by_cases hp : p < s
    · simp only [Gate.applyNat, update, if_pos hp]
      rw [if_neg (by omega : ¬ p = c + s)]
    · simp only [Gate.applyNat, update, if_neg hp]
      by_cases hpc : p = c + s
      · subst hpc; simp
      · rw [if_neg hpc, if_neg (by omega : ¬ p - s = c),
            Nat.sub_add_cancel (Nat.le_of_not_lt hp)]
  | seq g₁ g₂ ih₁ ih₂ =>
    intro f; funext p
    show Gate.applyNat (shiftBy s g₂) (Gate.applyNat (shiftBy s g₁) f) p = _
    rw [ih₁ f]
    set f₁ : Nat → Bool := fun p => if p < s then f p
      else Gate.applyNat g₁ (fun q => f (q + s)) (p - s) with hf₁
    rw [ih₂ f₁]
    -- the down-shift of `f₁` is `applyNat g₁ (down-shift of f)`
    have hsh : (fun q => f₁ (q + s)) = Gate.applyNat g₁ (fun q => f (q + s)) := by
      funext q
      show f₁ (q + s) = _
      rw [hf₁]
      simp only [if_neg (by omega : ¬ q + s < s), Nat.add_sub_cancel]
    by_cases hp : p < s
    · simp only [if_pos hp]; rw [hf₁]; simp [hp]
    · simp only [if_neg hp, hsh]
      show Gate.applyNat g₂ (Gate.applyNat g₁ (fun q => f (q + s))) (p - s) = _
      rfl

end FormalRV.Shor.RunwayWindowed.GateShift
