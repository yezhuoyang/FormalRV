import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.Determinant
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Data.Int.GCD
import FormalRV.Core.QuantumGate
import FormalRV.Core.QuantumLib
import FormalRV.Shor.QPE
import FormalRV.Shor.QPEAmplitude
import FormalRV.Shor.Eigenstate
import FormalRV.Shor.TotientLowerBound
import FormalRV.Shor.MainAlgorithm.ContinuedFractionBridge



namespace FormalRV.SQIRPort

/-- **Strict-at-`n` bridge variant** (added 2026-05-24): like
`mathlib_OF_post_step_nat_eq_OF_post_step_nonboundary` but requires only
`¬ TerminatedAt n` (NOT `n+1`). The `+1` in the nonboundary version was
an artifact of unifying the n=0 case through `terminated_stable`; here we
inline the `n=0` case explicitly. For uses where the smallest convergent
index satisfies `¬ TerminatedAt n` but may have `TerminatedAt (n+1)`
(generic rational case where `k/r` is the final non-terminal convergent),
this variant is what bridges. -/
theorem mathlib_OF_post_step_nat_eq_OF_post_step_at_n
    (n o m : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).TerminatedAt n) :
    mathlib_OF_post_step_nat n o m = OF_post_step n o m := by
  cases n with
  | zero =>
    -- n = 0: h_not_term IS ¬ TerminatedAt 0.
    have h_mod : o % (2^m) ≠ 0 := nondiv_of_not_terminated_zero o (2^m) h_not_term
    have h_spec := mathlib_OF_post_step_spec 0 o m
    rw [GenContFract.zeroth_den_eq_one] at h_spec
    have h_int : mathlib_OF_post_step 0 o m = 1 := by exact_mod_cast h_spec.symm
    unfold mathlib_OF_post_step_nat
    rw [h_int, OF_post_step_zero]; rfl
  | succ k =>
    -- n = k+1. h_not_term IS ¬ TerminatedAt (k+1). Apply strong at n' = k.
    have h_2pm : 0 < (2^m : Nat) := Nat.two_pow_pos m
    have h_strong := cf_aux_full_matches_mathlib_strong o (2^m) h_2pm k h_not_term
    have h_rhs : OF_post_step (k+1) o m = (cf_aux_full (k+2) o (2^m) 0 1 1 0).2.2.2 := by
      unfold OF_post_step ContinuedFraction
      rw [cf_aux_eq_cf_aux_full_proj]
    have h_lhs_R : ((mathlib_OF_post_step_nat (k+1) o m : Nat) : ℝ)
        = (((cf_aux_full (k+2) o (2^m) 0 1 1 0).2.2.2 : Nat) : ℝ) := by
      have h_spec := mathlib_OF_post_step_spec (k+1) o m
      have h_strong_4 := h_strong.2.2.2
      rw [h_strong_4]
      rw [show ((GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).contsAux (k+2)).b
            = (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).dens (k+1) from rfl]
      rw [show (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) from by
        push_cast; rfl]
      rw [h_spec]
      have h_nat_int := mathlib_OF_post_step_nat_int (k+1) o m
      have : ((mathlib_OF_post_step_nat (k+1) o m : Nat) : ℝ)
           = ((mathlib_OF_post_step (k+1) o m : ℤ) : ℝ) := by
        rw [← h_nat_int]; push_cast; rfl
      rw [this]
    have h_eq_Nat : mathlib_OF_post_step_nat (k+1) o m
        = (cf_aux_full (k+2) o (2^m) 0 1 1 0).2.2.2 := by
      exact_mod_cast h_lhs_R
    rw [h_eq_Nat, h_rhs]

-- (The OBSOLETE "general" theorem with boundary sorry has been DELETED 2026-05-24
--  per John's design recommendation. The non-boundary version above covers all
--  cases needed for r_found_1. The block-commented scaffolding that followed
--  has also been removed 2026-05-24 to eliminate the dead `sorry` text from
--  the source file. Git history preserves the prior scaffolding if needed.)

/-- **Step-1 bridge between cf_aux-based and mathlib-based denominators**
(Phase 3 r_found_1, added 2026-05-24): combines the four step-1 closed
forms to show `mathlib_OF_post_step_nat 1 o m = OF_post_step 1 o m`. -/
theorem mathlib_OF_post_step_nat_eq_OF_post_step_one (o m : Nat) :
    mathlib_OF_post_step_nat 1 o m = OF_post_step 1 o m := by
  unfold mathlib_OF_post_step_nat
  have h_spec := mathlib_OF_post_step_spec 1 o m
  have h_cast : (((o : ℝ)) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) := by push_cast; rfl
  by_cases h_mod : o % (2^m) = 0
  · -- divisible case
    have h_dens := mathlib_dens_one_div o m h_mod
    rw [h_cast] at h_dens
    rw [h_dens] at h_spec
    have h_int : mathlib_OF_post_step 1 o m = 1 := by exact_mod_cast h_spec.symm
    rw [h_int, OF_post_step_one_div o m h_mod]
    rfl
  · -- non-divisible case
    have h_dens := mathlib_dens_one_nondiv o m h_mod
    rw [h_cast] at h_dens
    rw [h_dens] at h_spec
    have h_int : ((2^m / (o % 2^m) : Nat) : ℤ) = mathlib_OF_post_step 1 o m := by
      have h_cast2 : (((2^m / (o % 2^m) : Nat) : ℤ) : ℝ) = (((2^m / (o % 2^m) : Nat) : ℝ)) := by
        push_cast; rfl
      have h_lhs : (((2^m / (o % 2^m) : Nat) : ℤ) : ℝ) =
                   ((mathlib_OF_post_step 1 o m : ℤ) : ℝ) := by
        rw [h_cast2]; exact h_spec
      exact_mod_cast h_lhs
    rw [OF_post_step_one_nondiv o m h_mod, ← h_int]
    rfl

/-- **`mathlib_OF_post_step` at step 0 is 1** (Phase 3 r_found_1 bridge,
added 2026-05-23): mathlib's `zeroth_den_eq_one` gives
`(GenContFract.of v).dens 0 = 1`, so the integer-valued analog is `1`. -/
theorem mathlib_OF_post_step_zero (o m : Nat) :
    mathlib_OF_post_step 0 o m = 1 := by
  have h_spec := mathlib_OF_post_step_spec 0 o m
  rw [GenContFract.zeroth_den_eq_one] at h_spec
  exact_mod_cast h_spec.symm

/-- **`mathlib_OF_post_step_nat` at step 0 is 1** — corollary of
`mathlib_OF_post_step_zero`. -/
theorem mathlib_OF_post_step_nat_zero (o m : Nat) :
    mathlib_OF_post_step_nat 0 o m = 1 := by
  unfold mathlib_OF_post_step_nat
  rw [mathlib_OF_post_step_zero]
  rfl

/-- **Bridge at step 0**: `mathlib_OF_post_step 0 = (OF_post_step 0 : ℤ)`.
This is the first specific-point bridge in the cf_aux ↔ mathlib chain;
future ticks would extend it inductively. -/
theorem mathlib_OF_post_step_eq_OF_post_step_zero (o m : Nat) :
    mathlib_OF_post_step 0 o m = ((OF_post_step 0 o m : Nat) : ℤ) := by
  rw [mathlib_OF_post_step_zero, OF_post_step_zero]
  rfl

/-- **Nat-level bridge at step 0**: `mathlib_OF_post_step_nat 0 = OF_post_step 0`. -/
theorem mathlib_OF_post_step_nat_eq_OF_post_step_zero (o m : Nat) :
    mathlib_OF_post_step_nat 0 o m = OF_post_step 0 o m := by
  rw [mathlib_OF_post_step_nat_zero, OF_post_step_zero]

/-- **Arithmetic Lemma A** (added 2026-05-24, exact-rational foundation):
from `s_closest m k r * r = k * 2^m` and `gcd k r = 1`, deduce `r ∣ 2^m`.
Used in the r > 1 subcase of `TODO_r_found_1_core_exact_rational`. -/
lemma r_dvd_two_pow_of_exact
    (m k r : Nat) (h_coprime : Nat.gcd k r = 1)
    (h_eq : s_closest m k r * r = k * 2^m) :
    r ∣ 2^m := by
  -- r ∣ s_closest * r = k * 2^m. With r coprime to k, r ∣ 2^m.
  have h_cop : r.Coprime k := Nat.coprime_comm.mp h_coprime
  have h_r_dvd_km : r ∣ k * 2^m := by
    rw [← h_eq]; exact dvd_mul_left r (s_closest m k r)
  exact (Nat.Coprime.dvd_mul_left h_cop).mp h_r_dvd_km

/-- **Arithmetic Lemma B** (added 2026-05-24, exact-rational foundation):
the reduced denominator. Under the exact-rational hypothesis,
`gcd (s_closest m k r) (2^m) = 2^m / r`. -/
lemma gcd_s_closest_two_pow_eq
    (m k r : Nat) (h_r_pos : 0 < r) (h_coprime : Nat.gcd k r = 1)
    (h_eq : s_closest m k r * r = k * 2^m) :
    Nat.gcd (s_closest m k r) (2^m) = 2^m / r := by
  have h_r_dvd : r ∣ 2^m := r_dvd_two_pow_of_exact m k r h_coprime h_eq
  set g := 2^m / r with h_g_def
  -- 2^m = g * r (since r ∣ 2^m).
  have h_2m_eq : 2^m = g * r := (Nat.div_mul_cancel h_r_dvd).symm
  -- s_closest = k * g (cancel r from h_eq).
  have h_s_eq : s_closest m k r = k * g := by
    have h_s_r : s_closest m k r * r = (k * g) * r := by rw [h_eq, h_2m_eq]; ring
    exact Nat.eq_of_mul_eq_mul_right h_r_pos h_s_r
  -- gcd (k*g) (g*r) = g * gcd k r = g * 1 = g.
  rw [h_s_eq, h_2m_eq]
  rw [show g * r = r * g from Nat.mul_comm g r]
  rw [Nat.gcd_mul_right, h_coprime, Nat.one_mul]

end FormalRV.SQIRPort
