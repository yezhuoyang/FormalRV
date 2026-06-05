import FormalRV.Shor.MainAlgorithm.ContinuedFractionBridge.ConvergentBoundsAndOrder


namespace FormalRV.SQIRPort

/-- **Mathlib-side OF_post_step** (Phase 3 r_found_1 bridge target, added
2026-05-23): integer-valued analog of our `OF_post_step` (which uses
`cf_aux`-based `ContinuedFraction`), defined via mathlib's `GenContFract.of`
with `dens_int_valued`. Bridges to our `OF_post_step` will be the
remaining work. -/
noncomputable def mathlib_OF_post_step (step o m : Nat) : ℤ :=
  Classical.choose (dens_int_valued ((o : ℝ) / (2 ^ m : ℝ)) step)

/-- Spec for `mathlib_OF_post_step`: equals the mathlib `dens` value. -/
theorem mathlib_OF_post_step_spec (step o m : Nat) :
    (GenContFract.of ((o : ℝ) / (2 ^ m : ℝ))).dens step =
      ((mathlib_OF_post_step step o m : ℤ) : ℝ) :=
  Classical.choose_spec (dens_int_valued ((o : ℝ) / (2 ^ m : ℝ)) step)

/-- `mathlib_OF_post_step` is non-negative: convergent denominators are
non-negative (`zero_le_of_den`), so the integer extraction is ≥ 0. -/
theorem mathlib_OF_post_step_nonneg (step o m : Nat) :
    0 ≤ mathlib_OF_post_step step o m := by
  have h_nn := GenContFract.zero_le_of_den (v := (o : ℝ) / (2^m : ℝ)) (n := step)
  rw [mathlib_OF_post_step_spec step o m] at h_nn
  exact_mod_cast h_nn

/-- The Nat-valued version of `mathlib_OF_post_step`, via `Int.toNat`. -/
noncomputable def mathlib_OF_post_step_nat (step o m : Nat) : Nat :=
  (mathlib_OF_post_step step o m).toNat

/-- Spec connecting the Nat version to the Int version: equal when
non-negative, which is always true (`mathlib_OF_post_step_nonneg`). -/
theorem mathlib_OF_post_step_nat_int (step o m : Nat) :
    ((mathlib_OF_post_step_nat step o m : Nat) : ℤ) = mathlib_OF_post_step step o m := by
  unfold mathlib_OF_post_step_nat
  exact Int.toNat_of_nonneg (mathlib_OF_post_step_nonneg step o m)

/-- **Monotonicity of integer-valued `mathlib_OF_post_step`** (Phase 3
r_found_1, added 2026-05-24): direct from mathlib's `of_den_mono`. -/
theorem mathlib_OF_post_step_mono (step o m : Nat) :
    mathlib_OF_post_step step o m ≤ mathlib_OF_post_step (step+1) o m := by
  have h_mono := GenContFract.of_den_mono
    (v := ((o : ℝ) / (2^m : ℝ))) (n := step)
  rw [mathlib_OF_post_step_spec step o m,
      mathlib_OF_post_step_spec (step+1) o m] at h_mono
  exact_mod_cast h_mono

/-- **Monotonicity of `mathlib_OF_post_step_nat`** — Nat-level. -/
theorem mathlib_OF_post_step_nat_mono (step o m : Nat) :
    mathlib_OF_post_step_nat step o m ≤ mathlib_OF_post_step_nat (step+1) o m := by
  have h := mathlib_OF_post_step_mono step o m
  have h_nn1 := mathlib_OF_post_step_nonneg step o m
  have h_nn2 := mathlib_OF_post_step_nonneg (step+1) o m
  have h_int1 := mathlib_OF_post_step_nat_int step o m
  have h_int2 := mathlib_OF_post_step_nat_int (step+1) o m
  have : ((mathlib_OF_post_step_nat step o m : Nat) : ℤ) ≤
         ((mathlib_OF_post_step_nat (step+1) o m : Nat) : ℤ) := by
    rw [h_int1, h_int2]; exact h
  exact_mod_cast this

/-- **Generalized step-by-step monotonicity for `mathlib_OF_post_step_nat`**
(transitive closure of the one-step version): `i ≤ j → dens_nat i ≤ dens_nat j`. -/
theorem mathlib_OF_post_step_nat_mono_le (o m i j : Nat) (h : i ≤ j) :
    mathlib_OF_post_step_nat i o m ≤ mathlib_OF_post_step_nat j o m := by
  induction j with
  | zero =>
    interval_cases i
    exact Nat.le_refl _
  | succ k ih =>
    by_cases h_eq : i = k + 1
    · subst h_eq; exact Nat.le_refl _
    · have h_le_k : i ≤ k := by omega
      exact Nat.le_trans (ih h_le_k) (mathlib_OF_post_step_nat_mono k o m)

/-- **Fibonacci lower bound on `mathlib_OF_post_step`** (Phase 3 r_found_1
infrastructure, added 2026-05-24): direct restatement of mathlib's
`succ_nth_fib_le_of_nth_den` in terms of our integer-valued
`mathlib_OF_post_step`. When the continued fraction has not terminated
before step `n`, the n-th convergent denominator is at least `fib(n+1)`. -/
theorem mathlib_OF_post_step_fib_ge (o m n : Nat)
    (h_not_term : n = 0 ∨ ¬ (GenContFract.of ((o : ℝ) / (2^m : ℝ))).TerminatedAt (n - 1)) :
    (Nat.fib (n + 1) : ℤ) ≤ mathlib_OF_post_step n o m := by
  have h := GenContFract.succ_nth_fib_le_of_nth_den
    (v := ((o : ℝ) / (2^m : ℝ))) (n := n) h_not_term
  rw [mathlib_OF_post_step_spec n o m] at h
  exact_mod_cast h

/-- **Fibonacci lower bound on `mathlib_OF_post_step_nat`** — Nat-level. -/
theorem mathlib_OF_post_step_nat_fib_ge (o m n : Nat)
    (h_not_term : n = 0 ∨ ¬ (GenContFract.of ((o : ℝ) / (2^m : ℝ))).TerminatedAt (n - 1)) :
    Nat.fib (n + 1) ≤ mathlib_OF_post_step_nat n o m := by
  have h := mathlib_OF_post_step_fib_ge o m n h_not_term
  have h_int := mathlib_OF_post_step_nat_int n o m
  have : ((Nat.fib (n + 1) : Nat) : ℤ) ≤ ((mathlib_OF_post_step_nat n o m : Nat) : ℤ) := by
    rw [h_int]; exact h
  exact_mod_cast this

/-- **Positivity of `mathlib_OF_post_step_nat`** (when not terminated):
denominators are at least 1, since `fib(n+1) ≥ 1` for all `n`. -/
theorem mathlib_OF_post_step_nat_pos (o m n : Nat)
    (h_not_term : n = 0 ∨ ¬ (GenContFract.of ((o : ℝ) / (2^m : ℝ))).TerminatedAt (n - 1)) :
    0 < mathlib_OF_post_step_nat n o m := by
  have h_fib_pos : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
  have h_fib_le := mathlib_OF_post_step_nat_fib_ge o m n h_not_term
  omega

end FormalRV.SQIRPort
