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
import FormalRV.Shor.Shor.Part2

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

/-- **cf_aux_full denominator invariant** (added 2026-05-24, exact-rational
foundation): the quantity `q_curr · o + q_prev · m` is invariant across
cf_aux_full's iterations. After N steps starting from
`(o₀, m₀, p_prev, p_curr, q_prev, q_curr)`, the state's
`(q_curr_N, q_prev_N)` and Euclidean state `(o_N, m_N) = euclidean_iter N o₀ m₀`
satisfy:
  `q_curr_N · o_N + q_prev_N · m_N = q_curr · o₀ + q_prev · m₀`.

Proof by induction on N. The recurrence `q_curr ← (o/m)·q_curr + q_prev`
together with the Euclidean step `(o, m) → (m, o%m)` preserves the
combination via `(o/m)·m + (o%m) = o` (`Nat.div_add_mod`).

At termination (m_N = 0) with initial state `(0, 1, 1, 0)`: the invariant
becomes `q_curr_N · gcd(o₀, m₀) = m₀`, giving the reduced denominator
`q_curr_N = m₀ / gcd(o₀, m₀)`. -/
theorem cf_aux_full_q_inv :
    ∀ (N o m p_prev p_curr q_prev q_curr : Nat),
      (cf_aux_full N o m p_prev p_curr q_prev q_curr).2.2.2
        * (euclidean_iter N o m).1
      + (cf_aux_full N o m p_prev p_curr q_prev q_curr).2.2.1
        * (euclidean_iter N o m).2
      = q_curr * o + q_prev * m := by
  intro N
  induction N with
  | zero =>
    intros o m p_prev p_curr q_prev q_curr
    -- cf_aux_full 0 returns input state; euclidean_iter 0 = (o, m).
    show q_curr * o + q_prev * m = q_curr * o + q_prev * m
    rfl
  | succ k ih =>
    intros o m p_prev p_curr q_prev q_curr
    by_cases h_m : m = 0
    · subst h_m
      -- m=0: cf_aux_full returns input state, euclidean_iter = (o, 0).
      show (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr)
            else cf_aux_full k 0 (o % 0) p_curr ((o/0)*p_curr+p_prev)
                                          q_curr ((o/0)*q_curr+q_prev)).2.2.2 *
            (if (0 : Nat) = 0 then (o, 0) else euclidean_iter k 0 (o % 0)).1 +
            (if (0 : Nat) = 0 then (p_prev, p_curr, q_prev, q_curr)
            else cf_aux_full k 0 (o % 0) p_curr ((o/0)*p_curr+p_prev)
                                          q_curr ((o/0)*q_curr+q_prev)).2.2.1 *
            (if (0 : Nat) = 0 then (o, 0) else euclidean_iter k 0 (o % 0)).2
          = q_curr * o + q_prev * 0
      simp
    · have h_m_pos : 0 < m := Nat.pos_of_ne_zero h_m
      have h_cf_unfold :
          cf_aux_full (k+1) o m p_prev p_curr q_prev q_curr
          = cf_aux_full k m (o % m) p_curr ((o/m)*p_curr + p_prev)
                                    q_curr ((o/m)*q_curr + q_prev) := by
        show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
              else cf_aux_full k m (o%m) p_curr ((o/m)*p_curr + p_prev)
                                          q_curr ((o/m)*q_curr + q_prev)) = _
        rw [if_neg h_m]
      have h_eucl_unfold :
          euclidean_iter (k+1) o m = euclidean_iter k m (o % m) := by
        show (if m = 0 then (o, m) else euclidean_iter k m (o % m)) = _
        rw [if_neg h_m]
      rw [h_cf_unfold, h_eucl_unfold]
      rw [ih m (o % m) p_curr ((o/m)*p_curr + p_prev) q_curr ((o/m)*q_curr + q_prev)]
      -- Goal: ((o/m)*q_curr + q_prev) * m + q_curr * (o%m) = q_curr * o + q_prev * m.
      have h_div_mod : (o/m)*m + o%m = o := by
        have h := Nat.div_add_mod o m
        linarith [Nat.mul_comm m (o/m)]
      -- RHS = q_curr * ((o/m)*m + o%m) + q_prev*m  [by h_div_mod]
      rw [show q_curr * o = q_curr * ((o/m)*m + o%m) from by rw [h_div_mod]]
      ring

/-- **Lamé's theorem for cf_aux's Euclidean iteration** (added 2026-05-24,
exact-rational foundation): if the Euclidean iteration `euclidean_iter`
on `(o, m)` (with `m > 0`) terminates at the smallest index `j`, then the
Fibonacci bound `Nat.fib (j + 1) ≤ m` holds.

Proof by strong induction on `m`. The Euclidean step `(o, m) → (m, o%m)`
gives the IH at `m' = o%m < m`. To reach `Fib(j+1)` from `Fib(j) ≤ o%m`,
apply IH a second time at `m'' = m%(o%m) < m` (when `j ≥ 2`), then use
`m = q·(o%m) + m%(o%m) ≥ o%m + m%(o%m) ≥ Fib(j) + Fib(j-1) = Fib(j+1)`.

For `j = 1`: trivial (`Fib(2) = 1 ≤ m`). For `j = 2`: handled by `m ≥ 2`. -/
theorem eucl_iter_fib_bound :
    ∀ (m : Nat), 0 < m → ∀ (o j : Nat),
      (euclidean_iter j o m).2 = 0 →
      (∀ j' < j, (euclidean_iter j' o m).2 ≠ 0) →
      Nat.fib (j + 1) ≤ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro h_m_pos o j h_term h_min
    -- j > 0 since (eucl_iter 0).2 = m > 0.
    cases j with
    | zero =>
      exfalso
      have h0 : (euclidean_iter 0 o m).2 = m := rfl
      rw [h0] at h_term
      omega
    | succ j' =>
      -- Unfold eucl_iter (j'+1) using m > 0.
      have h_unfold : euclidean_iter (j' + 1) o m = euclidean_iter j' m (o % m) := by
        show (if m = 0 then (o, m) else euclidean_iter j' m (o % m)) = _
        rw [if_neg h_m_pos.ne']
      rw [h_unfold] at h_term
      by_cases h_om_zero : o % m = 0
      · -- o%m = 0: only consistent with j' = 0 by minimality.
        cases j' with
        | zero =>
          -- j = 1. Fib(2) = 1 ≤ m. ✓
          show Nat.fib 2 ≤ m
          rw [show Nat.fib 2 = 1 from rfl]; omega
        | succ _ =>
          exfalso
          have h_min_1 := h_min 1 (by omega)
          have h_eucl_1 : euclidean_iter 1 o m = (m, 0) := by
            show (if m = 0 then (o, m) else euclidean_iter 0 m (o % m)) = _
            rw [if_neg h_m_pos.ne', h_om_zero]; rfl
          rw [h_eucl_1] at h_min_1
          exact h_min_1 rfl
      · -- o%m > 0.
        have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om_zero
        have h_om_lt_m : o % m < m := Nat.mod_lt _ h_m_pos
        -- Shifted minimality (level 1).
        have h_min_shift : ∀ j'' < j', (euclidean_iter j'' m (o % m)).2 ≠ 0 := by
          intro j'' h_j''
          have h_shift : euclidean_iter j'' m (o % m) = euclidean_iter (j'' + 1) o m := by
            symm
            show (if m = 0 then (o, m) else euclidean_iter j'' m (o % m)) = _
            rw [if_neg h_m_pos.ne']
          rw [h_shift]
          exact h_min (j'' + 1) (by omega)
        -- IH at o%m: Fib(j' + 1) ≤ o%m.
        have h_fib_om : Nat.fib (j' + 1) ≤ o % m :=
          ih (o % m) h_om_lt_m h_om_pos m j' h_term h_min_shift
        cases j' with
        | zero =>
          -- j = 1. Fib(2) ≤ m. m ≥ 1.
          show Nat.fib 2 ≤ m
          rw [show Nat.fib 2 = 1 from rfl]; omega
        | succ j'' =>
          -- j = j''+2. Unfold next step: (eucl_iter (j''+1) m (o%m)) = (eucl_iter j'' (o%m) (m%(o%m))).
          have h_unfold_2 : euclidean_iter (j'' + 1) m (o % m)
              = euclidean_iter j'' (o % m) (m % (o % m)) := by
            show (if (o % m) = 0 then (m, o%m) else
                  euclidean_iter j'' (o % m) (m % (o % m))) = _
            rw [if_neg h_om_zero]
          rw [h_unfold_2] at h_term
          by_cases h_mm_zero : m % (o % m) = 0
          · -- m%(o%m) = 0: only consistent with j'' = 0 by minimality at level 2.
            cases j'' with
            | zero =>
              -- j = 2. Fib(3) = 2 ≤ m. m ≥ o%m + 1 ≥ 2.
              show Nat.fib 3 ≤ m
              rw [show Nat.fib 3 = 2 from rfl]; omega
            | succ _ =>
              exfalso
              have h_min_1 := h_min_shift 1 (by omega)
              have h_eucl_1 : euclidean_iter 1 m (o % m) = (o % m, m % (o % m)) := by
                show (if (o%m) = 0 then (m, o%m)
                      else euclidean_iter 0 (o % m) (m % (o % m))) = _
                rw [if_neg h_om_zero]; rfl
              rw [h_eucl_1] at h_min_1
              exact h_min_1 h_mm_zero
          · -- m%(o%m) > 0. Apply IH at m%(o%m) < m.
            have h_mm_pos : 0 < m % (o % m) := Nat.pos_of_ne_zero h_mm_zero
            have h_mm_lt_om : m % (o % m) < o % m := Nat.mod_lt _ h_om_pos
            have h_mm_lt_m : m % (o % m) < m := Nat.lt_trans h_mm_lt_om h_om_lt_m
            -- Shifted-shifted minimality.
            have h_min_shift_2 : ∀ j''' < j'',
                (euclidean_iter j''' (o % m) (m % (o % m))).2 ≠ 0 := by
              intro j''' h_j'''
              have h_shift_2 : euclidean_iter j''' (o % m) (m % (o % m))
                  = euclidean_iter (j''' + 1) m (o % m) := by
                symm
                show (if (o % m) = 0 then (m, o%m)
                      else euclidean_iter j''' (o % m) (m % (o % m))) = _
                rw [if_neg h_om_zero]
              rw [h_shift_2]
              exact h_min_shift (j''' + 1) (by omega)
            -- IH at m%(o%m): Fib(j''+1) ≤ m%(o%m).
            have h_fib_mm : Nat.fib (j'' + 1) ≤ m % (o % m) :=
              ih (m % (o % m)) h_mm_lt_m h_mm_pos (o % m) j'' h_term h_min_shift_2
            -- Bound: m ≥ o%m + m%(o%m).
            have h_q_pos : 1 ≤ m / (o % m) :=
              Nat.div_pos (Nat.le_of_lt h_om_lt_m) h_om_pos
            have h_div_mod_eq : m / (o % m) * (o % m) + m % (o % m) = m := by
              have h := Nat.div_add_mod m (o % m)
              linarith [Nat.mul_comm (m / (o % m)) (o % m)]
            have h_m_ge : o % m + m % (o % m) ≤ m := by
              have h_mul_ge : 1 * (o % m) ≤ m / (o % m) * (o % m) :=
                Nat.mul_le_mul_right _ h_q_pos
              linarith
            -- Goal: Fib(j''+1+2) ≤ m. Rewrite using Fib_add_two.
            show Nat.fib (j'' + 1 + 1 + 1) ≤ m
            have h_fib_eq : Nat.fib (j'' + 1 + 1 + 1)
                          = Nat.fib (j'' + 1 + 1) + Nat.fib (j'' + 1) := by
              rw [show j'' + 1 + 1 + 1 = (j'' + 1) + 2 from by ring]
              rw [Nat.fib_add_two]; ring
            rw [h_fib_eq]
            -- h_fib_om : Fib(j''+1+1) ≤ o%m. h_fib_mm : Fib(j''+1) ≤ m%(o%m).
            calc Nat.fib (j'' + 1 + 1) + Nat.fib (j'' + 1)
                ≤ o % m + m % (o % m) := by omega
              _ ≤ m := h_m_ge

/-- **Euclidean depth bound `j ≤ 2 * m_exp + 1`** (added 2026-05-24):
combines `eucl_iter_fib_bound` with `pow_two_le_fib` and `Nat.fib`
strict monotonicity to bound the Euclidean termination index of
`(o, 2^m_exp)` by `2 * m_exp + 1`. -/
theorem eucl_iter_le_two_m_plus_one
    (o m_exp j : Nat)
    (h_term : (euclidean_iter j o (2^m_exp)).2 = 0)
    (h_min  : ∀ j' < j, (euclidean_iter j' o (2^m_exp)).2 ≠ 0) :
    j ≤ 2 * m_exp + 1 := by
  have h_pow_pos : 0 < 2^m_exp := Nat.two_pow_pos m_exp
  have h_fib_le : Nat.fib (j + 1) ≤ 2^m_exp :=
    eucl_iter_fib_bound (2^m_exp) h_pow_pos o j h_term h_min
  by_contra h_not
  push_neg at h_not
  have h_j_ge : 2 * m_exp + 2 ≤ j := by omega
  -- Fib monotone at (2*m_exp + 3) ≤ (j + 1)
  have h_fib_mono : Nat.fib (2 * m_exp + 3) ≤ Nat.fib (j + 1) :=
    Nat.fib_mono (by omega)
  -- Fib(2m+2) < Fib(2m+3) since 2m+2 ≥ 2
  have h_fib_strict : Nat.fib (2 * m_exp + 2) < Nat.fib (2 * m_exp + 3) :=
    Nat.fib_lt_fib_succ (by omega)
  -- pow_two_le_fib : 2^m_exp ≤ Fib(2m_exp+2)
  have h_pow_le := pow_two_le_fib m_exp
  omega

/-- **gcd preservation by `euclidean_iter`** (added 2026-05-24): the gcd
of the state pair is invariant under the Euclidean step. By induction
on the iteration depth `d`, peeling one step at a time. -/
theorem eucl_iter_gcd_preserved :
    ∀ (d o m : Nat),
      Nat.gcd (euclidean_iter d o m).1 (euclidean_iter d o m).2 = Nat.gcd o m := by
  intro d
  induction d with
  | zero => intro o m; rfl
  | succ d ih =>
    intro o m
    by_cases h_m : m = 0
    · subst h_m
      have h_eq : euclidean_iter (d + 1) o 0 = (o, 0) := by
        show (if (0:Nat) = 0 then (o, 0) else euclidean_iter d 0 (o % 0)) = (o, 0)
        rfl
      rw [h_eq]
    · have h_eq : euclidean_iter (d + 1) o m = euclidean_iter d m (o % m) := by
        show (if m = 0 then (o, m) else euclidean_iter d m (o % m)) = _
        rw [if_neg h_m]
      rw [h_eq, ih m (o % m)]
      -- Goal: gcd m (o%m) = gcd o m.
      rw [Nat.gcd_comm m (o % m), Nat.gcd_comm o m]
      exact (Nat.gcd_rec m o).symm

/-- **q_curr bound from cf_aux_full_q_inv** (added 2026-05-24): at any
depth `d` where the Euclidean iteration's first component is positive,
the terminal `q_curr` from `cf_aux_full d o m_arg 0 1 1 0` satisfies
`gcd(o, m_arg) * q_curr ≤ m_arg`. Combines `cf_aux_full_q_inv`
(invariant) with `eucl_iter_gcd_preserved`. Gives `q_curr ≤ m_arg / gcd`
when `gcd > 0`. -/
theorem cf_aux_full_q_bound (d o m_arg : Nat)
    (h_pos : 0 < (euclidean_iter d o m_arg).1) :
    Nat.gcd o m_arg * (cf_aux_full d o m_arg 0 1 1 0).2.2.2 ≤ m_arg := by
  have h_inv := cf_aux_full_q_inv d o m_arg 0 1 1 0
  -- h_inv: q_curr · s.1 + q_prev · s.2 = 0 · o + 1 · m_arg = m_arg.
  simp only [Nat.zero_mul, Nat.one_mul, Nat.zero_add] at h_inv
  set s := euclidean_iter d o m_arg with h_s_def
  set q_f := (cf_aux_full d o m_arg 0 1 1 0).2.2.2 with h_qf_def
  set q_p := (cf_aux_full d o m_arg 0 1 1 0).2.2.1 with h_qp_def
  -- h_inv: q_f * s.1 + q_p * s.2 = m_arg.
  have h_q_s1_le : q_f * s.1 ≤ m_arg := by
    have h_p_s2_ge : 0 ≤ q_p * s.2 := Nat.zero_le _
    omega
  -- gcd preserved: gcd(s.1, s.2) = gcd(o, m_arg).
  have h_gcd_eq : Nat.gcd s.1 s.2 = Nat.gcd o m_arg :=
    eucl_iter_gcd_preserved d o m_arg
  set g := Nat.gcd o m_arg with h_g_def
  -- g ∣ s.1.
  have h_g_dvd : g ∣ s.1 := by
    rw [← h_gcd_eq]; exact Nat.gcd_dvd_left s.1 s.2
  -- s.1 ≥ g (since g ∣ s.1, s.1 > 0).
  have h_s1_ge_g : g ≤ s.1 := Nat.le_of_dvd h_pos h_g_dvd
  -- q_f * g ≤ q_f * s.1 ≤ m_arg.
  calc g * q_f
      = q_f * g := by ring
    _ ≤ q_f * s.1 := Nat.mul_le_mul_left q_f h_s1_ge_g
    _ ≤ m_arg := h_q_s1_le

/-- **Peel-from-right Euclidean step** (added 2026-05-24): if the
Euclidean state at depth `d` has positive second component, then at
depth `d+1` the first component equals that previous second component.
This is the "step from the right" view of `euclidean_iter`. By
induction on `d`, propagating the positivity through the recursion. -/
theorem euclidean_iter_succ_first_eq_prev_second :
    ∀ (d o m : Nat),
      0 < (euclidean_iter d o m).2 →
      (euclidean_iter (d + 1) o m).1 = (euclidean_iter d o m).2 := by
  intro d
  induction d with
  | zero =>
    intro o m h_pos
    -- (eucl_iter 0 o m) = (o, m). .2 = m. m > 0.
    have h_m_pos : 0 < m := h_pos
    -- (eucl_iter 1 o m).1 = m, (eucl_iter 0 o m).2 = m.
    have h_eq : euclidean_iter 1 o m = euclidean_iter 0 m (o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter 0 m (o % m)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_eq]
    rfl
  | succ d ih =>
    intro o m h_pos
    by_cases h_m : m = 0
    · subst h_m
      -- (eucl_iter (d+1) o 0) = (o, 0). .2 = 0. Contradicts h_pos.
      have h_eq : euclidean_iter (d + 1) o 0 = (o, 0) := by
        show (if (0:Nat) = 0 then (o, (0:Nat)) else euclidean_iter d 0 (o % 0)) = (o, 0)
        rfl
      rw [h_eq] at h_pos
      simp at h_pos
    · -- m > 0. Unfold: (eucl_iter (d+1) o m) = (eucl_iter d m (o%m)).
      have h_eq_d1 : euclidean_iter (d + 1) o m = euclidean_iter d m (o % m) := by
        show (if m = 0 then (o, m) else euclidean_iter d m (o % m)) = _
        rw [if_neg h_m]
      have h_eq_d2 : euclidean_iter (d + 1 + 1) o m
                   = euclidean_iter (d + 1) m (o % m) := by
        show (if m = 0 then (o, m) else euclidean_iter (d + 1) m (o % m)) = _
        rw [if_neg h_m]
      rw [h_eq_d2, h_eq_d1]
      rw [h_eq_d1] at h_pos
      exact ih m (o % m) h_pos

/-- **Positivity of `.1` under minimality** (added 2026-05-24): if `o > 0`
and the Euclidean iteration's second component is non-zero at every
depth `d' < d`, then the first component at depth `d` is positive.
Used to invoke `cf_aux_full_q_bound` at intermediate depths inside the
exact-rational `r > 1` walking argument. -/
theorem eucl_iter_first_pos_under_min
    (o m : Nat) (h_o_pos : 0 < o) :
    ∀ d, (∀ d' < d, (euclidean_iter d' o m).2 ≠ 0) →
         0 < (euclidean_iter d o m).1 := by
  intro d
  induction d with
  | zero => intro _; exact h_o_pos
  | succ d _ih =>
    intro h_min
    have h_d_ne : (euclidean_iter d o m).2 ≠ 0 := h_min d (Nat.lt_succ_self d)
    rw [euclidean_iter_succ_first_eq_prev_second d o m (Nat.pos_of_ne_zero h_d_ne)]
    exact Nat.pos_of_ne_zero h_d_ne

/-- **Exact-rational branch of `r_found_1_core`**: case when
`s_closest m k r * r = k * 2^m` (equivalently, `v = k/r` exactly as ℝ,
i.e., `r | 2^m`, i.e., `r` is a power of 2). This is the BOUNDARY case
for mathlib's CF — the CF terminates exactly at k/r, so the smallest
N_step with `convs N_step = k/r` is the termination index. The standard
bridge + `dens_eq_r_at_convs_eq_kr` don't apply directly; needs separate
handling (direct cf_aux computation, or use of mathlib's denominator-at-
termination). Includes the trivial sub-case r=1, a=1, k=0. -/
theorem TODO_r_found_1_core_exact_rational
    (a r N m n k : Nat)
    (h_basic : BasicSetting a r N m n)
    (h_k_lt : k < r)
    (h_coprime : Nat.gcd k r = 1)
    (h_eq : s_closest m k r * r = k * 2^m) :
    OF_post a N (s_closest m k r) m = r := by
  obtain ⟨⟨h_a_pos, h_a_lt⟩, h_ord, _h_pow_m, _h_pow_n⟩ := h_basic
  by_cases h_r : r = 1
  · -- r = 1 sub-case: trivial. k = 0 (from k < r), a = 1 (from Order a 1 N).
    subst h_r
    have h_k_zero : k = 0 := Nat.lt_one_iff.mp h_k_lt
    subst h_k_zero
    obtain ⟨_, h_a_mod, _⟩ := h_ord
    have h_a_mod' : a % N = 1 := by simpa using h_a_mod
    have h_a_eq_1 : a = 1 := by
      rw [Nat.mod_eq_of_lt h_a_lt] at h_a_mod'
      exact h_a_mod'
    subst h_a_eq_1
    -- s_closest m 0 1 = 0 by direct unfold of (0 * 2^m + 1/2) / 1.
    have h_s_zero : s_closest m 0 1 = 0 := by
      show (0 * 2^m + 1 / 2) / 1 = 0
      simp
    rw [h_s_zero]
    -- Need 1 < N (from a = 1, a < N).
    have h_N_ge_2 : 1 < N := h_a_lt
    -- OF_post' 1 1 N 0 m = 1.
    have h_walk_1 : OF_post' 1 1 N 0 m = 1 := by
      show (let pre := OF_post' 0 1 N 0 m
            if pre = 0 then
              (if modexp 1 (OF_post_step 0 0 m) N = 1
               then OF_post_step 0 0 m else 0)
            else pre) = 1
      have h_pre : OF_post' 0 1 N 0 m = 0 := rfl
      simp only [h_pre, if_true]
      rw [OF_post_step_zero]
      have h_modexp : modexp 1 1 N = 1 := by
        unfold modexp; simp [Nat.mod_eq_of_lt h_N_ge_2]
      rw [if_pos h_modexp]
    -- Extend OF_post' 1 = 1 to OF_post' (2m+2) = 1 via OF_post'_nonzero_equal.
    unfold OF_post
    have h_2m2_decomp : 2 * m + 2 = (2 * m + 2 - 1) + 1 := by omega
    rw [h_2m2_decomp]
    rw [OF_post'_nonzero_equal (2 * m + 2 - 1) 1 1 N 0 m
        (by rw [h_walk_1]; exact Nat.one_ne_zero)]
    exact h_walk_1
  · -- r > 1 sub-case: r ≥ 2 and r ∣ 2^m (so r is a power of 2 > 1).
    -- Strategy: at j_e = min Euclidean termination index, cf_aux's q_curr = r
    -- (terminal value via cf_aux_full_q_inv + gcd). At intermediate depths, q_curr
    -- is bounded by r (via cf_aux_full_q_bound). Walking gives OF_post = r.
    have h_r_pos : 0 < r := h_ord.1
    have h_r_ge_2 : 2 ≤ r := by omega
    have h_N_pos : 0 < N := by omega
    -- Foundation: r ∣ 2^m, gcd(s_closest, 2^m) = 2^m/r.
    have h_r_dvd : r ∣ 2^m := r_dvd_two_pow_of_exact m k r h_coprime h_eq
    have h_gcd_eq : Nat.gcd (s_closest m k r) (2^m) = 2^m / r :=
      gcd_s_closest_two_pow_eq m k r h_r_pos h_coprime h_eq
    set s := s_closest m k r with h_s_def
    set g := 2^m / r with h_g_def
    have h_2m_eq : 2^m = g * r := (Nat.div_mul_cancel h_r_dvd).symm
    have h_2m_pos : 0 < 2^m := Nat.two_pow_pos m
    have h_g_pos : 0 < g := by
      by_contra h_g_neg
      push_neg at h_g_neg
      interval_cases g
      rw [Nat.zero_mul] at h_2m_eq
      omega
    -- s_closest > 0 in r > 1 case (else gcd = 2^m = 2^m/r forces r = 1).
    have h_s_pos : 0 < s := by
      by_contra h_s_neg
      push_neg at h_s_neg
      interval_cases s
      -- gcd(0, 2^m) = 2^m. So 2^m = g, hence r = 1.
      rw [Nat.gcd_zero_left] at h_gcd_eq
      -- h_gcd_eq: 2^m = 2^m/r = g.
      have h_g_eq : g = 2^m := h_gcd_eq.symm
      rw [h_g_eq] at h_2m_eq
      -- 2^m = 2^m * r
      have h_one_eq_r : 1 = r := by
        have h_mul1 : 2^m * 1 = 2^m * r := by linarith
        exact Nat.eq_of_mul_eq_mul_left h_2m_pos h_mul1
      omega
    -- Find j_e := smallest d with .2 = 0.
    have h_term_exists : ∃ d, (euclidean_iter d s (2^m)).2 = 0 := by
      obtain ⟨d, _, h_term⟩ := eucl_iter_terminates s (2^m)
      exact ⟨d, h_term⟩
    set je := Nat.find h_term_exists with h_je_def
    have h_je_term : (euclidean_iter je s (2^m)).2 = 0 := Nat.find_spec h_term_exists
    have h_je_min : ∀ d < je, (euclidean_iter d s (2^m)).2 ≠ 0 := fun d hd =>
      Nat.find_min h_term_exists hd
    have h_je_le : je ≤ 2 * m + 1 :=
      eucl_iter_le_two_m_plus_one s m je h_je_term h_je_min
    have h_je_pos : 0 < je := by
      by_contra h_jzero
      push_neg at h_jzero
      interval_cases je
      have h_eq0 : euclidean_iter 0 s (2^m) = (s, 2^m) := rfl
      rw [h_eq0] at h_je_term
      simp at h_je_term
    -- (eucl_iter je s 2^m).1 = g (gcd preservation + .2 = 0 at termination).
    have h_je_one : (euclidean_iter je s (2^m)).1 = g := by
      have h_p := eucl_iter_gcd_preserved je s (2^m)
      rw [h_je_term, Nat.gcd_zero_right] at h_p
      rw [h_p, h_gcd_eq]
    -- q_curr at depth je = r (from q_inv: q_je · g = 2^m = g · r, and g > 0).
    have h_inv_je := cf_aux_full_q_inv je s (2^m) 0 1 1 0
    simp only [Nat.zero_mul, Nat.one_mul, Nat.zero_add] at h_inv_je
    rw [h_je_term, Nat.mul_zero, Nat.add_zero] at h_inv_je
    rw [h_je_one] at h_inv_je
    -- h_inv_je: (cf_aux_full je s (2^m) 0 1 1 0).2.2.2 * g = 2^m
    have h_q_je_eq_r : (cf_aux_full je s (2^m) 0 1 1 0).2.2.2 = r := by
      have h_qg_eq_gr : (cf_aux_full je s (2^m) 0 1 1 0).2.2.2 * g = r * g := by
        rw [h_inv_je, h_2m_eq]; ring
      exact Nat.eq_of_mul_eq_mul_right h_g_pos h_qg_eq_gr
    -- OF_post_step (je - 1) s m = r (cf_aux at depth je = terminal q_curr = r).
    have h_step_je_minus_1 : OF_post_step (je - 1) s m = r := by
      have h_je_decomp : je - 1 + 1 = je := Nat.sub_add_cancel h_je_pos
      show (cf_aux ((je - 1) + 1) s (2^m) 0 1 1 0).2 = r
      rw [h_je_decomp, cf_aux_eq_cf_aux_full_proj]
      exact h_q_je_eq_r
    -- Walking helper: OF_post_step x s m ≤ r for x + 1 ≤ je.
    -- (This is the analog of "monotonicity" but via cf_aux_full_q_bound.)
    have h_intermediate_le_r : ∀ x, x + 1 ≤ je → OF_post_step x s m ≤ r := by
      intro x h_xp1_le
      -- OF_post_step x s m = (cf_aux (x+1) s (2^m) 0 1 1 0).2 = q_curr at depth x+1.
      have h_step_eq :
          OF_post_step x s m = (cf_aux_full (x + 1) s (2^m) 0 1 1 0).2.2.2 := by
        show (cf_aux (x + 1) s (2^m) 0 1 1 0).2 = _
        rw [cf_aux_eq_cf_aux_full_proj]
      rw [h_step_eq]
      -- For x+1 ≤ je: by minimality of je, .2 ≠ 0 at all d' < x+1 ≤ je.
      have h_min_for_xp1 :
          ∀ d' < x + 1, (euclidean_iter d' s (2^m)).2 ≠ 0 := by
        intro d' h_d'
        exact h_je_min d' (by omega)
      have h_first_pos :
          0 < (euclidean_iter (x + 1) s (2^m)).1 :=
        eucl_iter_first_pos_under_min s (2^m) h_s_pos (x + 1) h_min_for_xp1
      have h_bound := cf_aux_full_q_bound (x + 1) s (2^m) h_first_pos
      -- h_bound: gcd(s, 2^m) · q_curr ≤ 2^m. Substitute gcd via h_gcd_eq.
      rw [h_gcd_eq] at h_bound
      -- h_bound: g · q ≤ 2^m. Convert RHS to g * r without touching q's arg.
      have h_bound2 : g * (cf_aux_full (x + 1) s (2^m) 0 1 1 0).2.2.2 ≤ g * r := by
        rw [← h_2m_eq]; exact h_bound
      exact Nat.le_of_mul_le_mul_left h_bound2 h_g_pos
    -- Walking: OF_post' je a N s m = r.
    have h_modexp_at_r : modexp a r N = 1 := h_ord.2.1
    have h_walk_je : OF_post' je a N s m = r := by
      have h_je_decomp : je - 1 + 1 = je := Nat.sub_add_cancel h_je_pos
      conv_lhs => rw [← h_je_decomp]
      show (let pre := OF_post' (je - 1) a N s m
            if pre = 0 then
              (if modexp a (OF_post_step (je - 1) s m) N = 1
               then OF_post_step (je - 1) s m else 0)
            else pre) = r
      by_cases h_pre : OF_post' (je - 1) a N s m = 0
      · -- Case A: pre = 0. Result = OF_post_step (je-1) = r (modexp passes).
        simp only [h_pre, if_true]
        rw [h_step_je_minus_1, if_pos h_modexp_at_r]
      · -- Case B: pre ≠ 0. Result = pre = r.
        simp only [h_pre, if_false]
        have h_dvd : r ∣ OF_post' (je - 1) a N s m := by
          rcases OF_post'_dvd_r (je - 1) a N s m h_a_pos h_a_lt r h_ord with
            h0 | hd
          · exact absurd h0 h_pre
          · exact hd
        obtain ⟨x, h_x_lt, h_x_eq⟩ :=
          OF_post'_nonzero_pre (je - 1) a N s m h_pre
        -- x < je - 1, so x + 1 ≤ je - 1 ≤ je. Apply intermediate bound.
        have h_xp1_le : x + 1 ≤ je := by omega
        have h_x_step_le : OF_post_step x s m ≤ r :=
          h_intermediate_le_r x h_xp1_le
        rw [← h_x_eq] at h_dvd ⊢
        have h_step_pos : 0 < OF_post_step x s m := by
          rw [h_x_eq]; exact Nat.pos_of_ne_zero h_pre
        obtain ⟨c, hc⟩ := h_dvd
        have h_c_pos : 0 < c := by
          rcases Nat.eq_zero_or_pos c with rfl | h
          · rw [Nat.mul_zero] at hc; omega
          · exact h
        have h_c_eq_1 : c = 1 := by
          by_contra h_c_ne
          have h_c_ge_2 : c ≥ 2 := by omega
          have h_step_ge : 2 * r ≤ OF_post_step x s m := by
            rw [hc]; linarith [Nat.mul_le_mul_left r h_c_ge_2]
          linarith
        rw [hc, h_c_eq_1, Nat.mul_one]
    -- Extend OF_post' je = r to OF_post a N s m = OF_post' (2m+2) a N s m = r.
    have h_walk_ne : OF_post' je a N s m ≠ 0 := by
      rw [h_walk_je]; exact h_r_pos.ne'
    unfold OF_post
    have h_2m2_decomp : 2 * m + 2 = (2 * m + 2 - je) + je := by omega
    rw [h_2m2_decomp]
    rw [OF_post'_nonzero_equal (2 * m + 2 - je) je a N s m h_walk_ne]
    exact h_walk_je

/-- **Generic branch of `r_found_1_core`**: case when
`s_closest m k r * r ≠ k * 2^m` (i.e., `v ≠ k/r` as ℝ). Khinchin returns
a SMALLEST N_step < T_v (CF termination index) with `convs N_step = k/r`.
At this N_step, `¬ TerminatedAt N_step` and (usually) `¬ TerminatedAt
(N_step + 1)`. The spine proof goes through. The two non-termination
TODOs are now scoped to this branch and tractable via smallest-N_step
arguments using `h_ne`. -/
theorem TODO_r_found_1_core_generic
    (a r N m n k : Nat)
    (h_basic : BasicSetting a r N m n)
    (h_k_lt : k < r)
    (h_coprime : Nat.gcd k r = 1)
    (h_ne : s_closest m k r * r ≠ k * 2^m) :
    OF_post a N (s_closest m k r) m = r := by
  -- Extract BasicSetting components (duplicated from core; could refactor further).
  obtain ⟨⟨h_a_pos, h_a_lt⟩, h_ord, h_pow_m, h_pow_n⟩ := h_basic
  have h_N_pos : 0 < N := by omega
  have h_r_pos : 0 < r := h_ord.1
  have h_r_lt_N : r < N := Order_r_lt_N a r N h_N_pos h_ord
  have h_r_lt_2m : r < 2^m := by
    have h_r_le : r ≤ r * r := by nlinarith
    have h_r_sq_lt : r * r < N * N := by nlinarith
    have h_pow_m_lt : N^2 < 2^m := h_pow_m.1
    have h_N_sq : N^2 = N * N := by ring
    omega
  have h_2pm : 0 < (2^m : Nat) := Nat.two_pow_pos m
  -- Normalize the v form (cast manipulation done once).
  set v : ℝ := ((s_closest m k r : Nat) : ℝ) / ((2^m : Nat) : ℝ) with h_v_def
  have h_v_cast : ((s_closest m k r : ℝ) / (2^m : ℝ)) = v := by
    show ((s_closest m k r : Nat) : ℝ) / ((2 : ℝ) ^ m) = v
    rw [h_v_def]; push_cast; ring
  -- Step 1: Khinchin gives existence of N_step with convs N_step = k/r.
  -- Rewrite to use v directly.
  have h_exists_v : ∃ N_step, (GenContFract.of v).convs N_step
                              = (((k : ℚ) / r : ℚ) : ℝ) := by
    obtain ⟨N_step, h_convs⟩ :=
      k_over_r_is_convergent a r N m n k
        ⟨⟨h_a_pos, h_a_lt⟩, h_ord, h_pow_m, h_pow_n⟩ h_k_lt h_coprime
    rw [h_v_cast] at h_convs
    exact ⟨N_step, h_convs⟩
  -- Step 2: Pick smallest N_step via Nat.find.
  set N_step := Nat.find h_exists_v with h_N_step_def
  have h_convs : (GenContFract.of v).convs N_step = (((k : ℚ) / r : ℚ) : ℝ) :=
    Nat.find_spec h_exists_v
  have h_min_N_step : ∀ j < N_step,
      (GenContFract.of v).convs j ≠ (((k : ℚ) / r : ℚ) : ℝ) :=
    fun j hj hbad => Nat.find_min h_exists_v hj hbad
  -- Step 3: Derive v ≠ k/r in ℝ from h_ne (s_closest * r ≠ k * 2^m as Nat).
  have h_v_ne_kr : v ≠ (((k : ℚ) / r : ℚ) : ℝ) := by
    intro h_eq
    have h_pow_pos_R : (0 : ℝ) < ((2^m : Nat) : ℝ) := by exact_mod_cast h_2pm
    have h_r_pos_R : (0 : ℝ) < ((r : Nat) : ℝ) := by exact_mod_cast h_r_pos
    rw [h_v_def] at h_eq
    have h_rhs : (((k : ℚ) / r : ℚ) : ℝ) = (k : ℝ) / (r : ℝ) := by push_cast; ring
    rw [h_rhs] at h_eq
    have h_cross : (s_closest m k r : ℝ) * (r : ℝ)
                 = (k : ℝ) * ((2^m : Nat) : ℝ) := by
      field_simp at h_eq
      linarith
    have h_2pm_R : ((2^m : Nat) : ℝ) = ((2 : ℝ) ^ m) := by push_cast; rfl
    rw [h_2pm_R] at h_cross
    have h_nat_eq : (s_closest m k r) * r = k * (2^m) := by exact_mod_cast h_cross
    exact h_ne h_nat_eq
  -- Step 4: Derive ¬ TerminatedAt N_step from v ≠ k/r + h_convs N_step = k/r.
  -- Mathlib's of_correctness_of_terminatedAt: if Terminated, convs = v exactly.
  have h_not_term_N_step : ¬ (GenContFract.of v).TerminatedAt N_step := by
    intro h_term
    have h_convs_eq_v := GenContFract.of_correctness_of_terminatedAt h_term
    -- h_convs_eq_v : v = (GenContFract.of v).convs N_step.
    rw [h_convs] at h_convs_eq_v
    exact h_v_ne_kr h_convs_eq_v
  -- Step 3: dens N_step = r (via dens_eq_r_at_convs_eq_kr).
  have h_dens : (GenContFract.of v).dens N_step = (r : ℝ) :=
    dens_eq_r_at_convs_eq_kr v N_step k r h_not_term_N_step h_r_pos h_coprime h_convs
  -- Step 4: N_step ≤ 2m + 1.
  have h_not_term_alt : N_step = 0 ∨ ¬ (GenContFract.of v).TerminatedAt (N_step - 1) := by
    by_cases h : N_step = 0
    · left; exact h
    · right
      intro h_term
      have h_le : N_step - 1 ≤ N_step := by omega
      exact h_not_term_N_step (GenContFract.terminated_stable h_le h_term)
  have h_N_step_bound : N_step ≤ 2 * m + 1 :=
    N_step_le_2m_plus_1 v N_step r m h_dens h_not_term_alt h_r_lt_2m
  -- Step 5: Bridge OF_post_step N_step (s_closest m k r) m = r via the at_n
  -- variant (only needs ¬ TerminatedAt N_step, NOT N_step + 1). This avoids
  -- the boundary case where mathlib's CF may terminate exactly at N_step + 1.
  have h_bridge := mathlib_OF_post_step_nat_eq_OF_post_step_at_n N_step (s_closest m k r) m
    h_not_term_N_step
  -- mathlib_OF_post_step_nat N_step (s_closest m k r) m = OF_post_step N_step (s_closest m k r) m.
  -- We want: OF_post_step N_step (s_closest m k r) m = r.
  -- From h_dens + spec: mathlib_OF_post_step_nat N_step (s_closest m k r) m = r.
  have h_mathlib_eq_r : mathlib_OF_post_step_nat N_step (s_closest m k r) m = r := by
    have h_spec := mathlib_OF_post_step_spec N_step (s_closest m k r) m
    have h_cast_v : ((s_closest m k r : ℝ) / (2^m : ℝ)) = v := h_v_cast
    rw [h_cast_v] at h_spec
    rw [h_dens] at h_spec
    -- h_spec: (r : ℝ) = (mathlib_OF_post_step N_step (s_closest m k r) m : ℤ : ℝ).
    have h_int_eq : (r : ℤ) = mathlib_OF_post_step N_step (s_closest m k r) m := by
      exact_mod_cast h_spec
    have h_nat_int := mathlib_OF_post_step_nat_int N_step (s_closest m k r) m
    -- h_nat_int : ((mathlib_OF_post_step_nat N_step ... : Nat) : ℤ) = mathlib_OF_post_step N_step ...
    rw [← h_int_eq] at h_nat_int
    -- h_nat_int : ((mathlib_OF_post_step_nat N_step ... : Nat) : ℤ) = (r : ℤ).
    exact_mod_cast h_nat_int
  have h_of_step_eq_r : OF_post_step N_step (s_closest m k r) m = r := by
    rw [← h_bridge]; exact h_mathlib_eq_r
  -- Step 6: Walking — OF_post' (N_step + 1) a N (s_closest m k r) m = r.
  have h_modexp_at_r : modexp a r N = 1 := h_ord.2.1
  have h_walk_succ : OF_post' (N_step + 1) a N (s_closest m k r) m = r := by
    show (let pre := OF_post' N_step a N (s_closest m k r) m
          if pre = 0 then
            (if modexp a (OF_post_step N_step (s_closest m k r) m) N = 1
             then OF_post_step N_step (s_closest m k r) m else 0)
          else pre) = r
    by_cases h_pre : OF_post' N_step a N (s_closest m k r) m = 0
    · -- Case A: pre = 0. Result is OF_post_step N_step = r (since modexp a r N = 1).
      simp only [h_pre, if_true]
      rw [h_of_step_eq_r]
      rw [if_pos h_modexp_at_r]
    · -- Case B: pre ≠ 0. Result = pre. Show pre = r via dvd + bound.
      simp only [h_pre, if_false]
      -- r ∣ pre.
      have h_dvd : r ∣ OF_post' N_step a N (s_closest m k r) m := by
        rcases OF_post'_dvd_r N_step a N (s_closest m k r) m h_a_pos h_a_lt r h_ord with
          h0 | hd
        · exact absurd h0 h_pre
        · exact hd
      -- pre = OF_post_step x for some x < N_step.
      obtain ⟨x, h_x_lt, h_x_eq⟩ :=
        OF_post'_nonzero_pre N_step a N (s_closest m k r) m h_pre
      -- Bound OF_post_step x ≤ r via bridge + monotonicity.
      have h_x_succ_le : x + 1 ≤ N_step := by omega
      have h_not_term_x_succ :
          ¬ (GenContFract.of v).TerminatedAt (x + 1) := fun h =>
        h_not_term_N_step (GenContFract.terminated_stable h_x_succ_le h)
      have h_bridge_x := mathlib_OF_post_step_nat_eq_OF_post_step_nonboundary x
        (s_closest m k r) m h_not_term_x_succ
      have h_mono :
          mathlib_OF_post_step_nat x (s_closest m k r) m
          ≤ mathlib_OF_post_step_nat N_step (s_closest m k r) m :=
        mathlib_OF_post_step_nat_mono_le (s_closest m k r) m x N_step (by omega)
      rw [h_mathlib_eq_r, h_bridge_x, h_x_eq] at h_mono
      -- h_mono : OF_post' N_step ... ≤ r.
      have h_pre_pos : 0 < OF_post' N_step a N (s_closest m k r) m :=
        Nat.pos_of_ne_zero h_pre
      obtain ⟨c, hc⟩ := h_dvd
      have h_c_pos : 0 < c := by
        rcases Nat.eq_zero_or_pos c with rfl | h
        · rw [Nat.mul_zero] at hc; omega
        · exact h
      have h_c_eq_1 : c = 1 := by
        by_contra h_c_ne
        have h_c_ge_2 : c ≥ 2 := by omega
        have h_r_mul_ge : r * 2 ≤ r * c := Nat.mul_le_mul_left r h_c_ge_2
        have h_pre_ge : 2 * r ≤ OF_post' N_step a N (s_closest m k r) m := by
          rw [hc]; linarith
        linarith
      rw [hc, h_c_eq_1, Nat.mul_one]
  -- Step 7: Extend OF_post' (N_step + 1) = r to OF_post' (2m+2) = r via OF_post'_nonzero_equal.
  have h_2m2_decomp : 2 * m + 2 = (2 * m + 2 - (N_step + 1)) + (N_step + 1) := by omega
  have h_walk_ne : OF_post' (N_step + 1) a N (s_closest m k r) m ≠ 0 := by
    rw [h_walk_succ]; exact h_r_pos.ne'
  unfold OF_post
  rw [h_2m2_decomp]
  rw [OF_post'_nonzero_equal (2 * m + 2 - (N_step + 1)) (N_step + 1) a N
      (s_closest m k r) m h_walk_ne]
  exact h_walk_succ

/-- **r_found_1_core**: the operational claim — `OF_post` equals `r` on
the `s_closest` input. The `r_found_1` axiom follows by unfolding `r_found`
as an indicator.

Refactored 2026-05-24 per John's recommendation into a case split on
`s_closest m k r * r = k * 2^m`, dispatching to the exact-rational or
generic helper. -/
theorem TODO_r_found_1_core
    (a r N m n k : Nat)
    (h_basic : BasicSetting a r N m n)
    (h_k_lt : k < r)
    (h_coprime : Nat.gcd k r = 1) :
    OF_post a N (s_closest m k r) m = r := by
  by_cases h_eq : s_closest m k r * r = k * 2^m
  · exact TODO_r_found_1_core_exact_rational a r N m n k h_basic h_k_lt h_coprime h_eq
  · exact TODO_r_found_1_core_generic a r N m n k h_basic h_k_lt h_coprime h_eq

/-- **`r_found_1`** (closed 2026-05-24): The post-processor `r_found`
returns 1 (i.e., recovers the order `r`) when the measurement outcome
is `s_closest m k r` — the integer nearest `k · 2^m / r`.

This is the headline operational claim: classical post-processing on a
"good" QPE outcome reliably extracts the order. Built from
`TODO_r_found_1_core` (which proves `OF_post = r`) by unfolding the
indicator `r_found`. Axiom-clean (propext, Classical.choice, Quot.sound). -/
theorem r_found_1
    (a r N m n k : Nat)
    (h_basic : BasicSetting a r N m n)
    (h_k_lt : k < r)
    (h_coprime : Nat.gcd k r = 1) :
    r_found (s_closest m k r) m r a N = 1 := by
  have h_core := TODO_r_found_1_core a r N m n k h_basic h_k_lt h_coprime
  unfold r_found
  rw [if_pos h_core]

/-- **`phi_n_over_n_lowerbound`** (Coq: `EulerTotient.v`; Lean closure
2026-05-24). Euler's totient lower bound: `ϕ(r) / r ≥ exp(−2) / (log₂ N)^4`
whenever `r ≤ N` and `r > 0`.

**CLOSED** by an elementary distinct-prime-factor argument (no
Mertens-third-theorem needed). The full proof lives in
`SQIRPort/TotientLowerBound.lean` as `phi_n_over_n_lowerbound_proved`;
this is the thin re-export keeping the original name so existing
references resolve. -/
theorem phi_n_over_n_lowerbound (r N : Nat) (h_r_pos : 0 < r) (h_le : r ≤ N) :
    ((Nat.totient r : ℝ) / (r : ℝ))
      ≥ Real.exp (-2) / (Nat.log2 N : ℝ)^4 :=
  phi_n_over_n_lowerbound_proved r N h_r_pos h_le

/-- Probabilities are non-negative.

**Closed 2026-05-24 as a theorem.** Direct consequence of the
operational definition: a sum of `Complex.normSq` values, each of which
is non-negative; the `else 0` branch is also non-negative. -/
theorem prob_partial_meas_nonneg {m_dim full_dim : Nat}
    (ψ : QState m_dim) (φ : QState full_dim) : 0 ≤ prob_partial_meas ψ φ := by
  unfold prob_partial_meas
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  · rfl

/-! ## Partial-measurement API (basis-vector first register)

API lemmas for `prob_partial_meas` when the first register is a
computational basis state `|s⟩`. These reduce the inner-product sum to
a single non-zero contribution (at `x.val = s`), giving a clean closed
form: the partial-measurement probability is the sum of squared
amplitudes over the "selected slice" of the joint state. -/

/-- **Selected-slice index** for partial measurement: maps a "first
register" outcome `s : Fin m_dim` and "second register" basis index
`y : Fin (full_dim / m_dim)` to the joint-register basis index
`s · (full_dim / m_dim) + y` in `Fin full_dim`. The cast through
`Fin (m_dim * (full_dim / m_dim))` uses the divisibility hypothesis. -/
noncomputable def partial_meas_index {m_dim full_dim : Nat}
    (h_dvd : m_dim ∣ full_dim) (s : Fin m_dim)
    (y : Fin (full_dim / m_dim)) : Fin full_dim :=
  Fin.cast (Nat.mul_div_cancel' h_dvd) ⟨s.val * (full_dim / m_dim) + y.val, by
    have hx : s.val < m_dim := s.isLt
    have hy : y.val < full_dim / m_dim := y.isLt
    calc s.val * (full_dim / m_dim) + y.val
        < s.val * (full_dim / m_dim) + (full_dim / m_dim) := by omega
      _ = (s.val + 1) * (full_dim / m_dim) := by ring
      _ ≤ m_dim * (full_dim / m_dim) := Nat.mul_le_mul_right _ hx⟩

/-- **Partial-measurement formula for a basis-vector outcome**: when
the first-register outcome is `basis_vector m_dim s` with `s < m_dim`,
the inner-product sum collapses to a single term (the contribution
at `x.val = s`), and the partial-measurement probability becomes a
sum of squared amplitudes along the selected slice of the joint state.

      prob_partial_meas (basis_vector m_dim s) φ
        = ∑ y : Fin (full_dim / m_dim),
            ‖φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y)‖²
-/
theorem prob_partial_meas_basis_vector
    {m_dim full_dim : Nat} (s : Nat) (h_s_lt : s < m_dim)
    (h_dvd : m_dim ∣ full_dim) (φ : QState full_dim) :
    prob_partial_meas (basis_vector m_dim s) φ
      = ∑ y : Fin (full_dim / m_dim),
          Complex.normSq (φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0) := by
  unfold prob_partial_meas
  rw [dif_pos h_dvd]
  refine Finset.sum_congr rfl ?_
  intro y _
  congr 1
  -- ∑ x : Fin m_dim, conj(basis x 0) · φ(...) = φ(...) at x = s.
  rw [Finset.sum_eq_single (⟨s, h_s_lt⟩ : Fin m_dim)]
  · -- main case: x = ⟨s, h_s_lt⟩, basis_vector at s is 1.
    show starRingEnd ℂ ((basis_vector m_dim s) ⟨s, h_s_lt⟩ 0) *
          φ (Fin.cast (Nat.mul_div_cancel' h_dvd) _) 0
        = φ (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0
    show starRingEnd ℂ (if (⟨s, h_s_lt⟩ : Fin m_dim).val = s then (1 : ℂ) else 0)
          * φ _ 0 = _
    simp [partial_meas_index]
  · -- other cases: x ≠ ⟨s, h_s_lt⟩, so x.val ≠ s, basis is 0.
    intro x _ h_ne
    show starRingEnd ℂ ((basis_vector m_dim s) x 0) * φ _ 0 = 0
    show starRingEnd ℂ (if x.val = s then (1 : ℂ) else 0) * φ _ 0 = 0
    have h_x_ne : x.val ≠ s := fun heq => h_ne (Fin.ext heq)
    simp [h_x_ne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Partial-measurement of basis-vector on a tensor-product state**:
when the joint state factors as `kron_vec a b`, the partial-measurement
probability at a first-register basis-vector outcome reduces to the
single squared amplitude of `a` at that outcome, multiplied by the
total `‖b‖²` of the second-register state:

      prob_partial_meas (basis_vector (2^p) s) (kron_vec a b)
        = ‖a_s‖² · ∑ y : Fin (2^q), ‖b_y‖²

For a normalized second-register state (`Pure_State_Vector b`), the
sum is `1` and the partial-meas reduces to just `‖a_s‖²` — exactly the
"distribution on the first register, ignoring the second" reading of
partial measurement. Proof: combines `prob_partial_meas_basis_vector`
with the index identity `partial_meas_index = kron_vec_combine` and
`Equiv.sum_comp` for the dimensional reindex. -/
theorem prob_partial_meas_basis_kron_vec
    {p q : Nat} (s : Nat) (h_s_lt : s < 2^p)
    (a : QState (2^p)) (b : QState (2^q)) :
    prob_partial_meas (basis_vector (2^p) s)
        (FormalRV.Framework.kron_vec a b)
      = Complex.normSq (a ⟨s, h_s_lt⟩ 0) *
        ∑ y : Fin (2^q), Complex.normSq (b y 0) := by
  have h_dvd : (2^p : ℕ) ∣ (2^(p+q) : ℕ) := pow_dvd_pow 2 (Nat.le_add_right p q)
  have h_div : (2^(p+q)) / (2^p) = 2^q := by
    rw [pow_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos p)]
  rw [prob_partial_meas_basis_vector s h_s_lt h_dvd]
  -- Step 1: identify partial_meas_index with kron_vec_combine.
  have h_idx_eq : ∀ y : Fin ((2^(p+q))/(2^p)),
      partial_meas_index h_dvd ⟨s, h_s_lt⟩ y
        = FormalRV.Framework.kron_vec_combine ⟨s, h_s_lt⟩ (Fin.cast h_div y) := by
    intro y
    apply Fin.ext
    show s * ((2^(p+q))/(2^p)) + y.val = s * 2^q + y.val
    have : s * ((2^(p+q))/(2^p)) = s * 2^q := by rw [h_div]
    omega
  -- Step 2: apply kron_vec_normSq_apply_combine pointwise.
  rw [show (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq ((FormalRV.Framework.kron_vec a b)
                              (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0))
        = (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq (a ⟨s, h_s_lt⟩ 0) *
            Complex.normSq (b (Fin.cast h_div y) 0)) by
      refine Finset.sum_congr rfl ?_
      intro y _
      rw [h_idx_eq y]
      exact FormalRV.Framework.kron_vec_normSq_apply_combine a b ⟨s, h_s_lt⟩ _]
  -- Step 3: factor out normSq(a_s) and reindex via Fin.castOrderIso h_div.
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Fin.castOrderIso h_div).toEquiv
    (fun y => Complex.normSq (b y 0))

/-- **Partial-measurement of `qpe_phase_state ⊗ eigen` gives the ideal
analytic probability**: when the QPE-output state is the tensor product
of the ideal QPE phase register `qpe_phase_state m θ` and any
data-register state `ψ_eigen`, the partial-measurement probability at
the phase-register outcome `y` is exactly the ideal `qpe_prob m y θ`,
scaled by the total squared amplitude of `ψ_eigen` (which is `1` when
`ψ_eigen` is `Pure_State_Vector`).

      prob_partial_meas (basis_vector (2^m) y)
          (kron_vec (qpe_phase_state m θ) ψ_eigen)
        = qpe_prob m y θ · ∑ z, ‖ψ_eigen_z‖²

This is the kernel-clean connection between the actual
partial-measurement probability (left side, lives in the Shor port) and
the abstract analytic QPE probability (right side, lives in
`Framework.QPEAmplitude`). For normalized `ψ_eigen`, this reduces to
`qpe_prob m y θ`. -/
theorem prob_partial_meas_qpe_phase_state_kron
    {m anc : Nat} (y : Nat) (h_y_lt : y < 2^m) (θ : ℝ)
    (ψ_eigen : QState (2^anc)) :
    prob_partial_meas (basis_vector (2^m) y)
        (FormalRV.Framework.kron_vec
          (FormalRV.Framework.qpe_phase_state m θ) ψ_eigen)
      = FormalRV.Framework.qpe_prob m y θ *
        ∑ z : Fin (2^anc), Complex.normSq (ψ_eigen z 0) := by
  rw [prob_partial_meas_basis_kron_vec y h_y_lt
        (FormalRV.Framework.qpe_phase_state m θ) ψ_eigen]
  rw [FormalRV.Framework.normSq_qpe_phase_state_apply]

/-- **Corollary: normalized eigenstate case**. When `ψ_eigen` is a
`Pure_State_Vector` (`∑ ‖ψ_eigen_z‖² = 1`), the partial-measurement
probability is exactly the ideal analytic `qpe_prob m y θ`. -/
theorem prob_partial_meas_qpe_phase_state_kron_pure
    {m anc : Nat} (y : Nat) (h_y_lt : y < 2^m) (θ : ℝ)
    (ψ_eigen : QState (2^anc))
    (h_pure : FormalRV.Framework.Pure_State_Vector ψ_eigen) :
    prob_partial_meas (basis_vector (2^m) y)
        (FormalRV.Framework.kron_vec
          (FormalRV.Framework.qpe_phase_state m θ) ψ_eigen)
      = FormalRV.Framework.qpe_prob m y θ := by
  rw [prob_partial_meas_qpe_phase_state_kron y h_y_lt θ ψ_eigen]
  unfold FormalRV.Framework.Pure_State_Vector at h_pure
  rw [h_pure, mul_one]

/-- **Orthogonal-superposition partial-measurement formula**: for an
orthonormal family `β : Fin r → QState (2^q)` (the eigenstates of the
unmeasured register) and any family `α : Fin r → QState (2^p)` of
"phase register" outputs, the partial-measurement probability of a
basis outcome on the linear combination

      Ψ = ∑ j : Fin r, kron_vec (α j) (β j)

equals the orthogonality-collapsed sum

      ∑ j : Fin r, ‖α_j ⟨s, _⟩ 0‖².

The cross-terms `α_j · α_j'` (for `j ≠ j'`) vanish by orthonormality
of `β`. Proof: combines `prob_partial_meas_basis_vector` with
`Framework.normSq_sum_apply_orth` (Parseval) and the identification
`partial_meas_index = kron_vec_combine`. -/
theorem prob_partial_meas_basis_sum_kron_orth
    {p q r : Nat} (s : Nat) (h_s_lt : s < 2^p)
    (α : Fin r → QState (2^p)) (β : Fin r → QState (2^q))
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0) :
    prob_partial_meas (basis_vector (2^p) s)
        ((∑ j : Fin r, FormalRV.Framework.kron_vec (α j) (β j) :
           Matrix (Fin (2^(p+q))) (Fin 1) ℂ))
      = ∑ j : Fin r, Complex.normSq ((α j) ⟨s, h_s_lt⟩ 0) := by
  have h_dvd : (2^p : ℕ) ∣ (2^(p+q) : ℕ) := pow_dvd_pow 2 (Nat.le_add_right p q)
  have h_div : (2^(p+q)) / (2^p) = 2^q := by
    rw [pow_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos p)]
  rw [prob_partial_meas_basis_vector s h_s_lt h_dvd]
  -- Step 1: identify partial_meas_index with kron_vec_combine (same as kron_vec lemma).
  have h_idx_eq : ∀ y : Fin ((2^(p+q))/(2^p)),
      partial_meas_index h_dvd ⟨s, h_s_lt⟩ y
        = FormalRV.Framework.kron_vec_combine ⟨s, h_s_lt⟩ (Fin.cast h_div y) := by
    intro y
    apply Fin.ext
    show s * ((2^(p+q))/(2^p)) + y.val = s * 2^q + y.val
    have : s * ((2^(p+q))/(2^p)) = s * 2^q := by rw [h_div]
    omega
  -- Step 2: distribute sum into kron_vec_apply_combine.
  rw [show (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq ((∑ j : Fin r,
              FormalRV.Framework.kron_vec (α j) (β j) :
              Matrix (Fin (2^(p+q))) (Fin 1) ℂ)
              (partial_meas_index h_dvd ⟨s, h_s_lt⟩ y) 0))
        = (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq (∑ j : Fin r,
              (α j) ⟨s, h_s_lt⟩ 0 * (β j) (Fin.cast h_div y) 0)) by
      refine Finset.sum_congr rfl ?_
      intro y _
      congr 1
      simp only [Matrix.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_idx_eq y]
      exact FormalRV.Framework.kron_vec_apply_combine (α j) (β j) ⟨s, h_s_lt⟩ _]
  -- Step 3: reindex sum from Fin ((2^(p+q))/(2^p)) to Fin (2^q).
  rw [show (∑ y : Fin ((2^(p+q))/(2^p)),
            Complex.normSq (∑ j : Fin r,
              (α j) ⟨s, h_s_lt⟩ 0 * (β j) (Fin.cast h_div y) 0))
        = (∑ y : Fin (2^q),
            Complex.normSq (∑ j : Fin r,
              (α j) ⟨s, h_s_lt⟩ 0 * (β j) y 0)) from by
      exact Equiv.sum_comp (Fin.castOrderIso h_div).toEquiv
        (fun y => Complex.normSq (∑ j : Fin r,
          (α j) ⟨s, h_s_lt⟩ 0 * (β j) y 0))]
  -- Step 4: apply Parseval.
  exact FormalRV.Framework.normSq_sum_apply_orth β h_orth
    (fun j => (α j) ⟨s, h_s_lt⟩ 0)

/-- **Scalar scaling for partial measurement** (Born-rule homogeneity):
scaling the joint state by `c ∈ ℂ` (applied pointwise as `fun i j =>
c * φ i j`) scales the partial-measurement probability by `‖c‖²`.

      prob_partial_meas ψ (c · φ)  =  ‖c‖² · prob_partial_meas ψ φ

The scaled state is written as `fun i j => c * φ i j` rather than
`c • φ` to avoid the `SMul ℂ (QState dim)` typeclass-synthesis issue
(`QState` is a `def` alias for `Matrix (Fin dim) (Fin 1) ℂ`, so the
Matrix SMul instance doesn't automatically lift). For callers using
`c • φ`, applying `Matrix.smul_apply` recovers the equivalence.

Proof: in the divisibility branch, push the scalar through the inner
sum (via `Finset.mul_sum` + `ring`), then use `Complex.normSq_mul`
to factor `‖c‖²` out of each `normSq` term, then `Finset.mul_sum` to
pull it out of the outer sum. The else-0 branch is trivial (`ring`). -/
theorem prob_partial_meas_smul_right
    {m_dim full_dim : Nat}
    (ψ : QState m_dim) (φ : QState full_dim) (c : ℂ) :
    prob_partial_meas ψ (fun i j => c * φ i j)
      = Complex.normSq c * prob_partial_meas ψ φ := by
  unfold prob_partial_meas
  by_cases h_dvd : m_dim ∣ full_dim
  · rw [dif_pos h_dvd, dif_pos h_dvd]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [show (∑ x : Fin m_dim, starRingEnd ℂ (ψ x 0) *
              (c * φ (Fin.cast (Nat.mul_div_cancel' h_dvd) _) 0))
          = c * ∑ x : Fin m_dim, starRingEnd ℂ (ψ x 0) *
              φ (Fin.cast (Nat.mul_div_cancel' h_dvd) _) 0 from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intros; ring]
    rw [Complex.normSq_mul]
  · rw [dif_neg h_dvd, dif_neg h_dvd]
    ring

/-- **`normSq` of `1/√r`** as a real cast: `‖1/√r‖² = 1/r`. Used to
turn the `(1/√r)`-scaling factor (from the standard orbit-state
normalization `|1⟩_n = (1/√r) · Σ_k |ψ_k⟩`) into the `(1/r)` weight
in the QPE peak-bound chain. -/
theorem normSq_one_div_sqrt (r : Nat) (h_r_pos : 0 < r) :
    Complex.normSq ((1 / (Real.sqrt r : ℂ))) = 1 / (r : ℝ) := by
  have h_r_R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h_r_pos
  rw [show (1 / (Real.sqrt r : ℂ)) = ((1 / Real.sqrt r : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.normSq_ofReal]
  field_simp
  rw [Real.sq_sqrt h_r_R.le]

/-- **QPE orthogonal-sum bridge with `1/r` factor**: the headline
combination of the scalar lemma + orthogonal-superposition formula +
QPE phase-state evaluation. Given:
* a family `k : Fin r → ℝ` of "true phases" (one per eigenstate),
* an orthonormal family `β : Fin r → QState (2^q)` of unmeasured-
  register eigenstates,

the partial-measurement probability of basis outcome `s` on the
normalized orbit-state-style superposition
`(1/√r) · ∑_j (qpe_phase_state p (k_j)) ⊗ |β_j⟩` equals the
average ideal QPE probability:

      (1/r) · ∑_j, qpe_prob p s (k_j).

Combined with `qpe_prob_peak_bound`, this gives the standard
`(1/r) · 4/π²` per-correctly-aligned-eigenstate lower bound — exactly
the per-outcome contribution at the heart of `QPE_MMI_correct`. -/
theorem prob_partial_meas_qpe_orth_sum
    {p q r : Nat} (s : Nat) (h_s_lt : s < 2^p) (h_r_pos : 0 < r)
    (k : Fin r → ℝ)
    (β : Fin r → QState (2^q))
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0) :
    prob_partial_meas (basis_vector (2^p) s)
        (fun i j => (1 / (Real.sqrt r : ℂ)) *
          ((∑ j_idx : Fin r,
             FormalRV.Framework.kron_vec
               (FormalRV.Framework.qpe_phase_state p (k j_idx)) (β j_idx) :
             Matrix (Fin (2^(p+q))) (Fin 1) ℂ) i j))
      = (1 / (r : ℝ)) * ∑ j_idx : Fin r,
          FormalRV.Framework.qpe_prob p s (k j_idx) := by
  -- Step 1: factor out the (1/√r) scalar via prob_partial_meas_smul_right.
  rw [prob_partial_meas_smul_right]
  -- Step 2: apply the orthogonal-superposition partial-meas formula.
  rw [prob_partial_meas_basis_sum_kron_orth s h_s_lt
        (fun j => FormalRV.Framework.qpe_phase_state p (k j)) β h_orth]
  -- Step 3: ‖qpe_phase_state at index‖² = qpe_prob.
  simp_rw [FormalRV.Framework.normSq_qpe_phase_state_apply]
  -- Step 4: ‖1/√r‖² = 1/r.
  rw [normSq_one_div_sqrt r h_r_pos]

/-- **`QPE_MMI_correct_from_orbit`** (added 2026-05-24): state-
factorization conditional form of `QPE_MMI_correct`. Given an
orthonormal eigenstate family `β j` (for the unmeasured register) and
the orbit-state superposition shape

  `(1/√r) · ∑ j_idx : Fin r,
     (qpe_phase_state m (j_idx/r)) ⊗ (β j_idx)`

for the joint output state, the QPE peak bound `≥ 4/(π²·r)` at outcome
`s_closest m k r` follows. Closes the analytic half of the
`QPE_MMI_correct` axiom; the remaining (semantic / circuit) half is
showing that `Shor_final_state m n anc f` actually has this form,
which requires the circuit semantics of `QPE_var` plus the modular
multiplier's eigenstate spectrum (deferred to Phase 4).

Kernel-clean: depends on `prob_partial_meas_qpe_orth_sum` (the
`(1/r)`-factored partial-meas bridge), `qpe_prob_at_s_closest_ge`
(the analytic `4/π²` peak bound at the matching `k/r` term), and
basic real arithmetic. -/
theorem QPE_MMI_correct_from_orbit
    {m q r : Nat} (k : Nat) (h_k_lt : k < r) (h_r_pos : 0 < r)
    (h_s_lt : s_closest m k r < 2^m)
    (β : Fin r → Matrix (Fin (2^q)) (Fin 1) ℂ)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (fun i j => (1 / (Real.sqrt r : ℂ)) *
          ((∑ j_idx : Fin r,
             FormalRV.Framework.kron_vec
               (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
               (β j_idx) :
             Matrix (Fin (2^(m + q))) (Fin 1) ℂ) i j))
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  rw [prob_partial_meas_qpe_orth_sum (s_closest m k r) h_s_lt h_r_pos
        (fun j_idx => ((j_idx.val : ℝ) / r)) β h_orth]
  have h_r_pos_R : (0 : ℝ) < r := by exact_mod_cast h_r_pos
  have h_simp : (1 / (r : ℝ)) * (4 / Real.pi^2) = 4 / (Real.pi^2 * r) := by
    field_simp
  -- Sum is bounded below by the j_idx = ⟨k, h_k_lt⟩ term, which is ≥ 4/π².
  have h_sum_ge : (4 / Real.pi^2 : ℝ)
      ≤ ∑ j_idx : Fin r,
          FormalRV.Framework.qpe_prob m (s_closest m k r)
                                        ((j_idx.val : ℝ) / r) := by
    have h_term : (4 / Real.pi^2 : ℝ)
        ≤ FormalRV.Framework.qpe_prob m (s_closest m k r) ((k : ℝ) / r) :=
      qpe_prob_at_s_closest_ge m k r h_r_pos
    set g : Fin r → ℝ := fun j_idx =>
        FormalRV.Framework.qpe_prob m (s_closest m k r) ((j_idx.val : ℝ) / r) with hg
    have h_g_nonneg : ∀ j_idx ∈ Finset.univ, 0 ≤ g j_idx :=
      fun _ _ => FormalRV.Framework.qpe_prob_nonneg _ _ _
    have h_single : g ⟨k, h_k_lt⟩ ≤ ∑ j_idx, g j_idx :=
      Finset.single_le_sum h_g_nonneg (Finset.mem_univ _)
    have h_g_k : g ⟨k, h_k_lt⟩ = FormalRV.Framework.qpe_prob m (s_closest m k r) ((k : ℝ) / r) := rfl
    rw [h_g_k] at h_single
    linarith
  have h_lhs_ge : (1 / (r : ℝ)) * (4 / Real.pi^2)
                ≤ (1 / (r : ℝ)) * ∑ j_idx : Fin r,
                    FormalRV.Framework.qpe_prob m (s_closest m k r)
                                                  ((j_idx.val : ℝ) / r) :=
    mul_le_mul_of_nonneg_left h_sum_ge (by positivity)
  linarith

/-- **`QPE_MMI_correct_from_orbit_state_eq`** (added 2026-05-24):
the state-equality form of `QPE_MMI_correct_from_orbit`. Given an
`actual_state` at the natural `Matrix (Fin (2^(m+q))) (Fin 1) ℂ`
type and an equality hypothesis showing that this state is exactly
the orbit-superposition form, the QPE peak bound follows.

This is the cleanest "factor the QPE_MMI_correct axiom through a
state-equality hypothesis" theorem. To recover the public
`QPE_MMI_correct` shape, the remaining work is a separate equality
theorem:

  `Shor_final_state m n anc f = (orbit-superposition state)`

(possibly with a `QState.cast` for the dimension `2^m · 2^n · 2^anc`
vs `2^(m + (n + anc))` mismatch). That equality is the genuine
SQIR/`QPEGeneral.v` semantic obligation; this conditional theorem
closes everything downstream of it. -/
theorem QPE_MMI_correct_from_orbit_state_eq
    {m q r : Nat} (k : Nat) (h_k_lt : k < r) (h_r_pos : 0 < r)
    (h_s_lt : s_closest m k r < 2^m)
    (β : Fin r → Matrix (Fin (2^q)) (Fin 1) ℂ)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0)
    (actual_state : Matrix (Fin (2^(m + q))) (Fin 1) ℂ)
    (h_state : actual_state =
      fun i j => (1 / (Real.sqrt r : ℂ)) *
        ((∑ j_idx : Fin r,
           FormalRV.Framework.kron_vec
             (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
             (β j_idx) :
           Matrix (Fin (2^(m + q))) (Fin 1) ℂ) i j)) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r)) actual_state
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  rw [h_state]
  exact QPE_MMI_correct_from_orbit k h_k_lt h_r_pos h_s_lt β h_orth

/-- **`QPE_MMI_correct_from_Shor_orbit_state`** (added 2026-05-24):
the Shor-shaped wrapper around `QPE_MMI_correct_from_orbit_state_eq`.
Takes the Shor-specific parameters and `BasicSetting`/`ModMulImpl`/
well-typed hypotheses (mirroring `QPE_MMI_correct`'s signature), plus
an explicit state-equality hypothesis showing the joint output state
is the orbit superposition. Derives `0 < r` from `BasicSetting`'s
`Order` field and `s_closest m k r < 2^m` from the existing
`s_closest_ub` helper, then dispatches to
`QPE_MMI_correct_from_orbit_state_eq`.

The conclusion is stated on `actual_state` (not directly on
`Shor_final_state`) to avoid the `QState (2^m * 2^n * 2^anc)` vs
`Matrix (Fin (2^(m + (n + anc))))` dimensional cast — a future tick
can bridge `actual_state` and `Shor_final_state` via `QState.cast` in
a separate equality theorem. The current theorem isolates the QPE-
bound content from that cast bookkeeping.

The `_h_mmi` / `_h_wt` arguments are unused in the proof but kept in
the signature to mirror the public `QPE_MMI_correct`'s shape exactly,
making the final substitution into the full Shor chain mechanical
once the state-factorization equality lands. -/
theorem QPE_MMI_correct_from_Shor_orbit_state
    (a r N m n anc k : Nat)
    (f : Nat → BaseUCom (n + anc))
    (β : Fin r → Matrix (Fin (2^(n + anc))) (Fin 1) ℂ)
    (h_basic : BasicSetting a r N m n)
    (_h_mmi : ModMulImpl a N n anc f)
    (_h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^(n + anc)), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0)
    (actual_state : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ)
    (h_state : actual_state =
      fun i j => (1 / (Real.sqrt r : ℂ)) *
        ((∑ j_idx : Fin r,
           FormalRV.Framework.kron_vec
             (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
             (β j_idx) :
           Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ) i j)) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r)) actual_state
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  have h_r_pos : 0 < r := h_basic.2.1.1
  have h_s_lt : s_closest m k r < 2^m :=
    s_closest_ub a r N m n k h_basic h_k_lt
  exact QPE_MMI_correct_from_orbit_state_eq k h_k_lt h_r_pos h_s_lt
    β h_orth actual_state h_state

/-- **`QPE_MMI_correct_assuming_orbit_factorization`** (added
2026-05-24): the maximal closure of the QPE_MMI_correct axiom that
this codebase currently supports.

Replaces the entire QPE semantic chain with a SINGLE existential
hypothesis `h_orbit_exists`: "there exist orthonormal eigenstates β
and an orbit-form state whose partial-measurement probability matches
`Shor_final_state`'s." Given this hypothesis, the QPE peak bound
follows from the kernel-clean conditional chain
(`QPE_MMI_correct_from_Shor_orbit_state` ∘
`QPE_MMI_correct_from_orbit_state_eq` ∘
`QPE_MMI_correct_from_orbit` ∘ `prob_partial_meas_qpe_orth_sum` ∘
`qpe_prob_peak_bound`) — no axiom is needed downstream of the
existential.

**This theorem cannot replace the `QPE_MMI_correct` axiom directly**
because the existential `h_orbit_exists` is genuinely deep: it
unfolds into the modular-multiplier eigenstate construction +
`QPE_var` circuit semantics, both Phase-4 obligations needing
multi-file infrastructure that does not yet exist in
`Framework.QuantumLib` (linearity of `uc_eval` over arbitrary state
sums, partial-trace machinery, the spectral theorem for unitary
matrices applied to the modular multiplier, etc.).

What this theorem DOES accomplish:
- It witnesses that the analytic / counting / averaging content of
  `QPE_MMI_correct` is fully Lean-proved.
- It pinpoints the EXACT remaining semantic obligation in a single
  named existential hypothesis.
- Replacing this single existential with a theorem-form derivation
  (the Phase-4 work) is sufficient to close the entire QPE chain.

Kernel-clean: `[propext, Classical.choice, Quot.sound]` only. -/
theorem QPE_MMI_correct_assuming_orbit_factorization
    (a r N m n anc k : Nat) (f : Nat → BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_mmi : ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_orbit_exists :
        ∃ (β : Fin r → Matrix (Fin (2^(n + anc))) (Fin 1) ℂ)
          (actual_state : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ),
          ((∀ j j' : Fin r,
             ∑ y : Fin (2^(n + anc)),
                  starRingEnd ℂ ((β j') y 0) * (β j) y 0
             = if j = j' then (1 : ℂ) else 0)
          ∧ (actual_state = fun i j => (1 / (Real.sqrt r : ℂ)) *
              ((∑ j_idx : Fin r,
                 FormalRV.Framework.kron_vec
                   (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
                   (β j_idx) :
                 Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ) i j))
          ∧ (prob_partial_meas (basis_vector (2^m) (s_closest m k r))
                (Shor_final_state m n anc f)
              = prob_partial_meas (basis_vector (2^m) (s_closest m k r))
                                  actual_state))) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  obtain ⟨β, actual_state, h_orth, h_state, h_prob_eq⟩ := h_orbit_exists
  rw [h_prob_eq]
  exact QPE_MMI_correct_from_Shor_orbit_state a r N m n anc k f β
    h_basic h_mmi h_wt h_k_lt h_orth actual_state h_state

end FormalRV.SQIRPort
