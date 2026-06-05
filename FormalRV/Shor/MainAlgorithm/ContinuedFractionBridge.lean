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
import FormalRV.Shor.MainAlgorithm.QuantumAndContinuedFractions

namespace FormalRV.SQIRPort

/-- **Denominator equals `r` at the Khinchin-recovered step** (Phase 3
r_found_1 slice 4b sub-step 3, added 2026-05-23): if `convs n = (k/r : ℚ)`
(in ℝ) at a non-terminated step with `gcd(k, r) = 1` and `r > 0`, then
`dens n = (r : ℝ)`. Proof: extract integer-valued `a = nums n`,
`b = dens n`; show `b > 0` via Fibonacci lower bound; coprimality from
`of_v_nums_dens_coprime`; cross-multiply `a/b = k/r` to get the integer
identity `a·r = b·k`; from coprimality of `(a,b)` and `(k,r)` plus
positivity, conclude `b = r` by mutual divisibility. -/
theorem dens_eq_r_at_convs_eq_kr (v : ℝ) (n : Nat) (k r : Nat)
    (h_not_term : ¬ (GenContFract.of v).TerminatedAt n)
    (h_r_pos : 0 < r) (h_coprime : Nat.gcd k r = 1)
    (h_convs : (GenContFract.of v).convs n = (((k:ℚ)/r : ℚ) : ℝ)) :
    (GenContFract.of v).dens n = (r : ℝ) := by
  obtain ⟨a, ha⟩ := nums_int_valued v n
  obtain ⟨b, hb⟩ := dens_int_valued v n
  have h_not_term' : n = 0 ∨ ¬ (GenContFract.of v).TerminatedAt (n - 1) := by
    by_cases h : n = 0
    · left; exact h
    · right
      intro h_term
      have h_le : n - 1 ≤ n := by omega
      exact h_not_term (GenContFract.terminated_stable h_le h_term)
  have h_fib_le := GenContFract.succ_nth_fib_le_of_nth_den (v := v) (n := n) h_not_term'
  rw [hb] at h_fib_le
  have h_fib_pos : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
  have h_b_pos : 0 < b := by
    have h_pos_R : (0 : ℝ) < (b : ℝ) := by
      calc (0 : ℝ) < (Nat.fib (n + 1) : ℝ) := by exact_mod_cast h_fib_pos
        _ ≤ (b : ℝ) := h_fib_le
    exact_mod_cast h_pos_R
  have h_cop_ab : Int.gcd a b = 1 := of_v_nums_dens_coprime v n h_not_term a b ha hb
  have h_conv : (GenContFract.of v).convs n = (a : ℝ) / (b : ℝ) := by
    rw [GenContFract.conv_eq_num_div_den, ha, hb]
  rw [h_conv] at h_convs
  have h_rhs : ((((k : ℚ) / r : ℚ) : ℝ)) = (k : ℝ) / (r : ℝ) := by push_cast; ring
  rw [h_rhs] at h_convs
  have h_b_ne : (b : ℝ) ≠ 0 := by exact_mod_cast h_b_pos.ne'
  have h_r_ne : (r : ℝ) ≠ 0 := by exact_mod_cast h_r_pos.ne'
  have h_eq : (a : ℝ) * r = (b : ℝ) * k := by
    field_simp at h_convs
    linarith
  have h_int : a * r = b * k := by exact_mod_cast h_eq
  have h_iscop_ab : IsCoprime a b := (Int.isCoprime_iff_gcd_eq_one).mpr h_cop_ab
  have h_b_dvd : b ∣ (r : ℤ) := by
    have h_dvd : b ∣ a * r := ⟨k, by linarith⟩
    exact h_iscop_ab.symm.dvd_of_dvd_mul_left h_dvd
  have h_iscop_kr : IsCoprime (k : ℤ) (r : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    show Int.gcd (k : ℤ) (r : ℤ) = 1
    simp [Int.gcd]; exact h_coprime
  have h_r_dvd : (r : ℤ) ∣ b := by
    have h_dvd : (r : ℤ) ∣ k * b := ⟨a, by linarith⟩
    exact h_iscop_kr.symm.dvd_of_dvd_mul_left h_dvd
  have h_r_pos_Z : (0 : ℤ) < (r : ℤ) := by exact_mod_cast h_r_pos
  have h_b_eq_r : b = (r : ℤ) :=
    Int.dvd_antisymm (Int.le_of_lt h_b_pos) (Int.le_of_lt h_r_pos_Z) h_b_dvd h_r_dvd
  rw [hb, h_b_eq_r]
  push_cast; rfl

/-- **Fibonacci step bound** (Phase 3, r_found_1 prep, added 2026-05-23):
direct restatement of mathlib's `GenContFract.succ_nth_fib_le_of_nth_den` —
if the `N_step`-th denominator of `GenContFract.of v` equals `r`, then
`fib (N_step + 1) ≤ r`. Used downstream to bound `N_step ≤ 2m+1` once we
know `r ≤ N < 2^m`. -/
theorem dens_eq_fib_bound (v : ℝ) (r N_step : Nat)
    (h_dens : (GenContFract.of v).dens N_step = (r : ℝ))
    (h_not_term : N_step = 0 ∨ ¬ (GenContFract.of v).TerminatedAt (N_step - 1)) :
    (Nat.fib (N_step + 1) : ℝ) ≤ (r : ℝ) := by
  have h := GenContFract.succ_nth_fib_le_of_nth_den (v := v) (n := N_step) h_not_term
  rw [h_dens] at h
  exact h

/-- **Fibonacci grows at least as fast as `2^m`** (Phase 3 r_found_1 slice
4c, added 2026-05-23): `2^m ≤ Nat.fib (2m + 2)`. Proven by induction;
inductive step uses `fib_add_two` + monotonicity `fib_lt_fib_succ`. -/
theorem pow_two_le_fib (m : Nat) : 2 ^ m ≤ Nat.fib (2 * m + 2) := by
  induction m with
  | zero => simp [Nat.fib]
  | succ k ih =>
    have h_succ : 2 * (k + 1) + 2 = (2 * k + 2) + 2 := by ring
    rw [h_succ]
    rw [Nat.fib_add_two]
    have h_ge_fib : Nat.fib (2*k+2) ≤ Nat.fib (2*k+2+1) := by
      have h2 : (2 : Nat) ≤ 2 * k + 2 := by omega
      exact (Nat.fib_lt_fib_succ h2).le
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≤ 2 * Nat.fib (2 * k + 2) := by omega
      _ ≤ Nat.fib (2 * k + 2) + Nat.fib (2 * k + 2 + 1) := by omega

/-- **Step bound from Fibonacci** (Phase 3 r_found_1 slice 4c, added
2026-05-23): if `fib(N_step + 1) ≤ r < 2^m`, then `N_step ≤ 2m + 1`.
Proof: contradiction; if N_step ≥ 2m + 2, monotonicity gives
`fib(N_step + 1) ≥ fib(2m + 2) ≥ 2^m > r`, contradicting `fib ≤ r`. -/
theorem fib_step_bound (N_step r m : Nat)
    (h_fib : Nat.fib (N_step + 1) ≤ r) (h_r_lt : r < 2^m) :
    N_step ≤ 2 * m + 1 := by
  by_contra h_not
  push_neg at h_not
  have h_mono : Nat.fib (2 * m + 2) ≤ Nat.fib (N_step + 1) :=
    Nat.fib_mono (by omega)
  have h_pow : 2 ^ m ≤ Nat.fib (2 * m + 2) := pow_two_le_fib m
  omega

/-- **Assembled step bound** (Phase 3 r_found_1 slice 4c, added 2026-05-23):
if `(GenContFract.of v).dens N_step = (r : ℝ)` (with non-termination), and
`r < 2^m`, then `N_step ≤ 2m + 1`. Combines `dens_eq_fib_bound` with the
elementary Fib growth `pow_two_le_fib`. -/
theorem N_step_le_2m_plus_1 (v : ℝ) (N_step r m : Nat)
    (h_dens : (GenContFract.of v).dens N_step = (r : ℝ))
    (h_not_term : N_step = 0 ∨ ¬ (GenContFract.of v).TerminatedAt (N_step - 1))
    (h_r_lt : r < 2^m) :
    N_step ≤ 2 * m + 1 := by
  have h_fib_R := dens_eq_fib_bound v r N_step h_dens h_not_term
  have h_fib : Nat.fib (N_step + 1) ≤ r := by exact_mod_cast h_fib_R
  exact fib_step_bound N_step r m h_fib h_r_lt

/-- **Order-divides-exponent iff `modexp = 1`** (Phase 3 r_found_1 prep,
added 2026-05-23): standard number-theory fact, `a^d ≡ 1 (mod N) ↔ r ∣ d`,
where `r` is the multiplicative order of `a` mod `N`. Proven elementarily
using division-with-remainder (`d = r * q + s`, `0 ≤ s < r`); the (⇒)
direction uses minimality of `r` to force `s = 0`. Needed downstream for
the OF_post' walking argument: it says the FIRST positive denominator
satisfying `modexp` is a multiple of `r`, and combined with our
denominator monotonicity argument, that first valid denominator IS `r`
itself. -/
theorem modexp_eq_one_iff_dvd (a N d : Nat) (h_pos : 0 < a) (h_lt : a < N)
    (r : Nat) (h_ord : Order a r N) :
    modexp a d N = 1 ↔ r ∣ d := by
  obtain ⟨h_r_pos, h_r_one, h_r_min⟩ := h_ord
  have h_N : 1 < N := by omega
  unfold modexp
  constructor
  · intro h_eq
    have h_dec : r * (d / r) + d % r = d := Nat.div_add_mod d r
    have h_s_lt : d % r < r := Nat.mod_lt _ h_r_pos
    have h_split : a^d = (a^r)^(d/r) * a^(d % r) := by
      conv_lhs => rw [← h_dec]
      rw [pow_add, pow_mul]
    have h_pow_q : (a^r)^(d/r) % N = 1 := by
      rw [Nat.pow_mod, h_r_one, one_pow]
      exact Nat.one_mod_eq_one.mpr (by omega)
    have h_s_mod : a^(d % r) % N = 1 := by
      have h1 : a^d % N = ((a^r)^(d/r) % N * (a^(d%r) % N)) % N := by
        rw [h_split, Nat.mul_mod]
      rw [h_pow_q, one_mul, Nat.mod_mod] at h1
      rw [← h1]; exact h_eq
    by_contra h_not_dvd
    rw [Nat.dvd_iff_mod_eq_zero] at h_not_dvd
    have h_s_pos : 0 < d % r := by omega
    exact h_r_min (d % r) h_s_pos h_s_lt h_s_mod
  · intro ⟨q, hq⟩
    rw [hq, pow_mul]
    rw [Nat.pow_mod, h_r_one, one_pow]
    exact Nat.one_mod_eq_one.mpr (by omega)

/-- **`OF_post'` returns 0 or a valid denominator** (Phase 3 r_found_1
prep, added 2026-05-23): structural induction on `OF_post'`'s walk. Says:
either `OF_post' step a N o m = 0`, or its value `d` satisfies
`modexp a d N = 1`. By design of the walk: any nonzero return path goes
through an `if modexp a ... = 1` check. This is independent of the
cf_aux ↔ mathlib bridge — pure structural property of the walk. -/
theorem OF_post'_zero_or_modexp (step a N o m : Nat) :
    OF_post' step a N o m = 0 ∨ modexp a (OF_post' step a N o m) N = 1 := by
  induction step with
  | zero => left; rfl
  | succ k ih =>
    unfold OF_post'
    by_cases h_pre : OF_post' k a N o m = 0
    · rw [h_pre]
      simp only [if_true]
      by_cases h_modexp : modexp a (OF_post_step k o m) N = 1
      · right; rw [if_pos h_modexp]; exact h_modexp
      · left; rw [if_neg h_modexp]
    · simp only [h_pre, if_false]
      rcases ih with hpre0 | hmod
      · exact absurd hpre0 h_pre
      · right; exact hmod

/-- **`OF_post'` returns 0 or a multiple of `r`** (Phase 3 r_found_1
prep, added 2026-05-23): one-line corollary combining
`OF_post'_zero_or_modexp` with `modexp_eq_one_iff_dvd`. Any nonzero
return value of `OF_post'` must be a multiple of the order `r`. Combined
with the denominator bound `≤ r` (from monotonicity at the right step),
the only valid nonzero return is `r` itself. -/
theorem OF_post'_dvd_r (step a N o m : Nat)
    (h_pos : 0 < a) (h_lt : a < N) (r : Nat) (h_ord : Order a r N) :
    OF_post' step a N o m = 0 ∨ r ∣ OF_post' step a N o m := by
  rcases OF_post'_zero_or_modexp step a N o m with hzero | hmod
  · left; exact hzero
  · right; exact (modexp_eq_one_iff_dvd a N _ h_pos h_lt r h_ord).mp hmod

/-- **`OF_post'_nonzero_pre`** (added 2026-05-24, port of SQIR `Shor.v:989`):
if `OF_post' step` is nonzero, then it equals `OF_post_step x o m` for some
`x < step` (the walk found a step where modexp passed). By induction on step. -/
theorem OF_post'_nonzero_pre (step a N o m : Nat)
    (h_ne : OF_post' step a N o m ≠ 0) :
    ∃ x, x < step ∧ OF_post_step x o m = OF_post' step a N o m := by
  induction step with
  | zero => exact absurd rfl h_ne
  | succ k ih =>
    show ∃ x, x < k + 1 ∧ OF_post_step x o m = OF_post' (k+1) a N o m
    by_cases h_pre : OF_post' k a N o m = 0
    · -- At step k+1, pre = 0. Result is OF_post_step k (if modexp passes) or 0.
      have h_unfold : OF_post' (k+1) a N o m
          = (if modexp a (OF_post_step k o m) N = 1
             then OF_post_step k o m else 0) := by
        show (let pre := OF_post' k a N o m
              if pre = 0 then
                (if modexp a (OF_post_step k o m) N = 1
                 then OF_post_step k o m else 0)
              else pre) = _
        simp [h_pre]
      rw [h_unfold] at h_ne ⊢
      by_cases h_mod : modexp a (OF_post_step k o m) N = 1
      · refine ⟨k, by omega, ?_⟩
        rw [if_pos h_mod]
      · exact absurd (by rw [if_neg h_mod]) h_ne
    · -- At step k+1, pre ≠ 0. Result = pre. Apply IH.
      have h_unfold : OF_post' (k+1) a N o m = OF_post' k a N o m := by
        show (let pre := OF_post' k a N o m
              if pre = 0 then _ else pre) = _
        simp [h_pre]
      rw [h_unfold] at h_ne ⊢
      obtain ⟨x, h_x_lt, h_x_eq⟩ := ih h_ne
      exact ⟨x, by omega, h_x_eq⟩

/-- **`OF_post'` stable once nonzero** (added 2026-05-24, port of SQIR
`Shor.v:979`): once `OF_post'` is nonzero at some depth `step`, it stays
equal for all higher depths `x + step`. By induction on x: the def's
"if pre = 0 then check else pre" guard preserves the nonzero value. -/
theorem OF_post'_nonzero_equal (x step a N o m : Nat)
    (h_ne : OF_post' step a N o m ≠ 0) :
    OF_post' (x + step) a N o m = OF_post' step a N o m := by
  induction x with
  | zero =>
    show OF_post' (0 + step) a N o m = OF_post' step a N o m
    rw [Nat.zero_add]
  | succ x' ih =>
    have h_eq : x' + 1 + step = (x' + step) + 1 := by ring
    rw [h_eq]
    show (let pre := OF_post' (x' + step) a N o m
          if pre = 0 then
            (if modexp a (OF_post_step (x' + step) o m) N = 1
             then OF_post_step (x' + step) o m else 0)
          else pre) = OF_post' step a N o m
    have h_ih_ne : OF_post' (x' + step) a N o m ≠ 0 := by rw [ih]; exact h_ne
    simp only [if_neg h_ih_ne]
    exact ih

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

/-- **`OF_post_step` at step 0 is 1** (Phase 3 r_found_1 bridge, added
2026-05-23): direct unfold of `cf_aux 1 o (2^m) 0 1 1 0`. Since `2^m ≠ 0`,
one cf_aux step yields `(a, 1)` and the depth-0 base case returns
`(p_curr, q_curr) = (a, 1)`, giving denominator 1. -/
theorem OF_post_step_zero (o m : Nat) : OF_post_step 0 o m = 1 := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux 1 o (2^m) 0 1 1 0).2 = 1
  unfold cf_aux
  simp
  rfl

/-- **`OF_post_step` at step 1 when divisible**: if `o % 2^m = 0` then
`OF_post_step 1 o m = 1`. cf_aux unfolding: first step gives `(a, 1)`
then depth-0 with `m = 0` returns `(p_curr, q_curr) = (a, 1)`. -/
theorem OF_post_step_one_div (o m : Nat) (h_mod : o % (2^m) = 0) :
    OF_post_step 1 o m = 1 := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux 2 o (2^m) 0 1 1 0).2 = 1
  unfold cf_aux
  simp
  unfold cf_aux
  simp [h_mod]

/-- **`OF_post_step` at step 1 when not divisible**: if `o % 2^m ≠ 0`
then `OF_post_step 1 o m = (2^m) / (o % 2^m)`. -/
theorem OF_post_step_one_nondiv (o m : Nat) (h_mod : o % (2^m) ≠ 0) :
    OF_post_step 1 o m = (2^m) / (o % 2^m) := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux 2 o (2^m) 0 1 1 0).2 = (2^m) / (o % 2^m)
  unfold cf_aux
  simp
  unfold cf_aux
  simp [h_mod]
  rfl

/-- **`OF_post_step` at step 2 when divisible**: if `o % 2^m = 0` then
`OF_post_step 2 o m = 1`. cf_aux unfolds 3 times; the m=0 case in the
inner Euclidean step returns `q_curr = 1`. -/
theorem OF_post_step_two_div (o m : Nat) (h_mod : o % (2^m) = 0) :
    OF_post_step 2 o m = 1 := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux 3 o (2^m) 0 1 1 0).2 = 1
  unfold cf_aux
  simp
  unfold cf_aux
  simp [h_mod]

/-- **`OF_post_step` for general n when divisible** (Phase 3 r_found_1,
added 2026-05-24): if `o % 2^m = 0` then `OF_post_step n o m = 1` for
ALL n. cf_aux unfolds once, then the inner state has `m = 0` which
terminates with `q_curr = 1` at any depth ≥ 1. The depth-0 case
specializes to `(cf_aux 0 ...).2 = q_curr = 1`. -/
theorem OF_post_step_div_general (n o m : Nat) (h_mod : o % (2^m) = 0) :
    OF_post_step n o m = 1 := by
  unfold OF_post_step ContinuedFraction
  show (cf_aux (n + 1) o (2^m) 0 1 1 0).2 = 1
  unfold cf_aux
  simp
  cases n with
  | zero => rfl
  | succ k =>
    rw [h_mod]
    unfold cf_aux
    simp

/-- **`OF_post_step` step 1 specialized to `o < 2^m`** (Shor use case,
added 2026-05-24 tick 62): when `o < 2^m` and `o > 0`, the cf_aux step-1
output simplifies via `o % 2^m = o` to `OF_post_step 1 o m = 2^m / o`.
This is the typical case for s_closest (which is < 2^m). -/
theorem OF_post_step_one_shor (o m : Nat) (h_o_pos : 0 < o)
    (h_o_lt : o < 2^m) :
    OF_post_step 1 o m = (2^m) / o := by
  have h_mod_eq : o % (2^m) = o := Nat.mod_eq_of_lt h_o_lt
  unfold OF_post_step ContinuedFraction
  show (cf_aux 2 o (2^m) 0 1 1 0).2 = (2^m) / o
  unfold cf_aux
  simp
  unfold cf_aux
  rw [h_mod_eq]
  simp [h_o_pos.ne']
  rfl

/-- **Shor-case bridge analysis observation** (Phase 3 r_found_1, tick 63):
For `o < 2^m` (the Shor use case for s_closest), cf_aux's first step is
"trivial" (a = o/(2^m) = 0): from initial `(0, 1, 1, 0)` it transitions to
`(1, 0, 0, 1)` and then runs `cf_aux n (2^m) o 1 0 0 1`. This is cf_aux on
the SWAPPED rational `2^m/o` but with a SWAPPED initial state — NOT the
standard ContinuedFraction call. The swap maps cf_aux dens output to
mathlib's nums output for the inverted ratio. Captured as design intent;
formalization is multi-tick. -/
def shor_case_cf_aux_swap_intent : Prop := True  -- placeholder doc

/-- **Mathlib's `dens 1` for `o/2^m`, divisible case**: when `o % 2^m = 0`,
the input is an integer, the stream terminates immediately, and
`dens 1 = dens 0 = 1`. -/
theorem mathlib_dens_one_div (o m : Nat) (h_mod : o % (2^m) = 0) :
    (GenContFract.of (((o : ℝ)) / ((2^m : Nat) : ℝ))).dens 1 = 1 := by
  have h_pow_pos : 0 < 2^m := Nat.two_pow_pos m
  have h_dvd : (2^m : Nat) ∣ o := Nat.dvd_of_mod_eq_zero h_mod
  have h_pow_ne : ((2^m : Nat) : ℝ) ≠ 0 := by exact_mod_cast h_pow_pos.ne'
  have h_int_eq : (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) = (((o / 2^m : Nat) : ℤ) : ℝ) := by
    have h1 : ((o / 2^m : Nat) : ℝ) = ((o : Nat) : ℝ) / ((2^m : Nat) : ℝ) :=
      Nat.cast_div h_dvd h_pow_ne
    rw [show (((o / 2^m : Nat) : ℤ) : ℝ) = ((o / 2^m : Nat) : ℝ) from by push_cast; rfl]
    exact h1.symm
  rw [h_int_eq]
  have h_s_nil := GenContFract.of_s_of_int ℝ ((o / 2^m : Nat) : ℤ)
  have h_term : (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).TerminatedAt 0 := by
    rw [GenContFract.terminatedAt_iff_s_terminatedAt]
    show (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).s.get? 0 = none
    rw [h_s_nil]
    rfl
  rw [GenContFract.dens_stable_of_terminated (n := 0) (m := 1) (by omega) h_term]
  exact GenContFract.zeroth_den_eq_one

/-- **Mathlib's `dens 1` for `o/2^m`, non-divisible case**: when
`o % 2^m ≠ 0`, applying `of_s_head` + `first_den_eq` +
`Int.fract_div_natCast_eq_div_natCast_mod` + `Rat.floor_natCast_div_natCast`
gives `dens 1 = ⌊2^m / (o % 2^m)⌋ = (2^m) / (o % 2^m)`. -/
theorem mathlib_dens_one_nondiv (o m : Nat) (h_mod : o % (2^m) ≠ 0) :
    (GenContFract.of (((o : ℝ)) / ((2^m : Nat) : ℝ))).dens 1
      = (((2^m) / (o % 2^m) : Nat) : ℝ) := by
  have h_pow_pos : 0 < 2^m := Nat.two_pow_pos m
  have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) ≠ 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_mod_pos : 0 < o % (2^m) := Nat.pos_of_ne_zero h_mod
    have h_num_pos : (0 : ℝ) < ((o % (2^m) : Nat) : ℝ) := by exact_mod_cast h_mod_pos
    have h_pow_pos_R : (0 : ℝ) < ((2^m : Nat) : ℝ) := by exact_mod_cast h_pow_pos
    positivity
  have h_head := GenContFract.of_s_head (K := ℝ)
    (v := (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ))) h_fract_ne
  have h_first := GenContFract.first_den_eq
    (g := GenContFract.of (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ)))
    (gp := { a := 1, b := ↑⌊(Int.fract (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ)))⁻¹⌋ })
    (zeroth_s_eq := by
      show (GenContFract.of (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ))).s.get? 0 = some _
      rw [show (GenContFract.of (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ))).s.get? 0
           = (GenContFract.of (((o : ℕ) : ℝ) / ((2^m : Nat) : ℝ))).s.head from rfl]
      exact h_head)
  rw [h_first]
  show (↑⌊(Int.fract ((↑o : ℝ) / ((2 ^ m : Nat) : ℝ)))⁻¹⌋ : ℝ)
       = ((2 ^ m / (o % 2 ^ m) : Nat) : ℝ)
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
  have h_eq : (((2^m : Nat) : ℝ) / ((o % 2^m : Nat) : ℝ))
            = ((((2^m : Nat) : ℚ) / ((o % 2^m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  rw [h_eq, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  push_cast
  rfl

/-- **Cast normalization for the GenContFract.of argument**: the two forms
`(o : ℝ) / (2^m : ℝ)` and `(o : ℝ) / ((2^m : Nat) : ℝ)` are equal. Used
to convert between the form needed by mathlib_OF_post_step_spec and the
form produced by GenContFract.of unfolding. -/
theorem of_arg_cast_norm (o m : Nat) :
    (((o : ℝ)) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) := by push_cast; rfl

/-- **Mathlib's `dens 2` for `o/2^m`, divisible case**: when `o % 2^m = 0`,
the input is an integer, the stream terminates immediately, and
`dens 2 = dens 0 = 1`. Same proof as step-1 divisible case but with
`dens_stable_of_terminated` extended to step 2. -/
theorem mathlib_dens_two_div (o m : Nat) (h_mod : o % (2^m) = 0) :
    (GenContFract.of (((o : ℝ)) / ((2^m : Nat) : ℝ))).dens 2 = 1 := by
  have h_pow_pos : 0 < 2^m := Nat.two_pow_pos m
  have h_dvd : (2^m : Nat) ∣ o := Nat.dvd_of_mod_eq_zero h_mod
  have h_pow_ne : ((2^m : Nat) : ℝ) ≠ 0 := by exact_mod_cast h_pow_pos.ne'
  have h_int_eq : (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) = (((o / 2^m : Nat) : ℤ) : ℝ) := by
    have h1 : ((o / 2^m : Nat) : ℝ) = ((o : Nat) : ℝ) / ((2^m : Nat) : ℝ) :=
      Nat.cast_div h_dvd h_pow_ne
    rw [show (((o / 2^m : Nat) : ℤ) : ℝ) = ((o / 2^m : Nat) : ℝ) from by push_cast; rfl]
    exact h1.symm
  rw [h_int_eq]
  have h_s_nil := GenContFract.of_s_of_int ℝ ((o / 2^m : Nat) : ℤ)
  have h_term : (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).TerminatedAt 0 := by
    rw [GenContFract.terminatedAt_iff_s_terminatedAt]
    show (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).s.get? 0 = none
    rw [h_s_nil]
    rfl
  rw [GenContFract.dens_stable_of_terminated (n := 0) (m := 2) (by omega) h_term]
  exact GenContFract.zeroth_den_eq_one

/-- **Mathlib's `dens n` for `o/2^m`, divisible case (general n)**: when
`o % 2^m = 0`, the input is an integer, the stream terminates immediately,
and `dens n = 1` for all n. Generalization of mathlib_dens_two_div. -/
theorem mathlib_dens_div_general (o m : Nat) (n : Nat) (h_mod : o % (2^m) = 0) :
    (GenContFract.of (((o : ℝ)) / ((2^m : Nat) : ℝ))).dens n = 1 := by
  have h_pow_pos : 0 < 2^m := Nat.two_pow_pos m
  have h_dvd : (2^m : Nat) ∣ o := Nat.dvd_of_mod_eq_zero h_mod
  have h_pow_ne : ((2^m : Nat) : ℝ) ≠ 0 := by exact_mod_cast h_pow_pos.ne'
  have h_int_eq : (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ)) = (((o / 2^m : Nat) : ℤ) : ℝ) := by
    have h1 : ((o / 2^m : Nat) : ℝ) = ((o : Nat) : ℝ) / ((2^m : Nat) : ℝ) :=
      Nat.cast_div h_dvd h_pow_ne
    rw [show (((o / 2^m : Nat) : ℤ) : ℝ) = ((o / 2^m : Nat) : ℝ) from by push_cast; rfl]
    exact h1.symm
  rw [h_int_eq]
  have h_s_nil := GenContFract.of_s_of_int ℝ ((o / 2^m : Nat) : ℤ)
  have h_term : (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).TerminatedAt 0 := by
    rw [GenContFract.terminatedAt_iff_s_terminatedAt]
    show (GenContFract.of (((o / 2^m : Nat) : ℤ) : ℝ)).s.get? 0 = none
    rw [h_s_nil]
    rfl
  by_cases h_n : n = 0
  · rw [h_n]; exact GenContFract.zeroth_den_eq_one
  · rw [GenContFract.dens_stable_of_terminated (n := 0) (m := n) (by omega) h_term]
    exact GenContFract.zeroth_den_eq_one

/-- **KEY RECURRENCE: mathlib's stream Euclidean shift = cf_aux's Euclidean
step** (Phase 3 r_found_1, added 2026-05-24): for `o, m : Nat` with `m > 0`
and `o % m ≠ 0`, mathlib's `IntFractPair.stream` at step `n+1` for `o/m`
equals the stream at step `n` for `m/(o%m)`. This is the structural bridge
between mathlib's `(Int.fract v)⁻¹` recursion and our cf_aux's Euclidean
state update `(o, m) ↦ (m, o%m)`. With this recurrence, the cf_aux ↔
mathlib bridge becomes provable by induction. -/
theorem stream_succ_euclidean (o m : Nat) (h_m_pos : 0 < m)
    (h_mod : o % m ≠ 0) (n : Nat) :
    GenContFract.IntFractPair.stream (((o : ℝ)) / ((m : Nat) : ℝ)) (n+1)
      = GenContFract.IntFractPair.stream (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ)) n := by
  have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) ≠ 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_mod_pos : 0 < o % m := Nat.pos_of_ne_zero h_mod
    have h_num_pos : (0 : ℝ) < ((o % m : Nat) : ℝ) := by exact_mod_cast h_mod_pos
    have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
    positivity
  rw [GenContFract.IntFractPair.stream_succ h_fract_ne n]
  congr 1
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]

/-- **Generalized mathlib int-valued dens for arbitrary `(o, m)`**: extracts
the integer-valued denominator of `(GenContFract.of (o/m))` at step `n` for
arbitrary m (not just powers of 2). Needed for the non-divisible-case bridge
which recurses through arbitrary Euclidean states. -/
noncomputable def mathlib_dens_int_gen (n o m : Nat) : ℤ :=
  Classical.choose (dens_int_valued (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) n)

/-- Spec for `mathlib_dens_int_gen`. -/
theorem mathlib_dens_int_gen_spec (n o m : Nat) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).dens n =
      ((mathlib_dens_int_gen n o m : ℤ) : ℝ) :=
  Classical.choose_spec (dens_int_valued (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) n)

/-- **`mathlib_dens_int_gen 0 o m = 1`**: base case for the generalized
mathlib int-valued dens at step 0 (independent of `o, m`). Follows
directly from mathlib's `zeroth_den_eq_one`. -/
theorem mathlib_dens_int_gen_zero (o m : Nat) :
    mathlib_dens_int_gen 0 o m = 1 := by
  have h_spec := mathlib_dens_int_gen_spec 0 o m
  rw [GenContFract.zeroth_den_eq_one] at h_spec
  exact_mod_cast h_spec.symm

/-- **`mathlib_dens_int_gen n o m ≥ 0`**: non-negativity of the generalized
int-valued dens. From `GenContFract.zero_le_of_den`. -/
theorem mathlib_dens_int_gen_nonneg (n o m : Nat) :
    0 ≤ mathlib_dens_int_gen n o m := by
  have h_nn := GenContFract.zero_le_of_den
    (v := (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) (n := n)
  rw [mathlib_dens_int_gen_spec n o m] at h_nn
  exact_mod_cast h_nn

/-- **`mathlib_dens_int_gen` Fibonacci lower bound** (general version of
`mathlib_OF_post_step_fib_ge`): when not terminated before step `n`,
`fib (n+1) ≤ mathlib_dens_int_gen n o m`. -/
theorem mathlib_dens_int_gen_fib_ge (o m n : Nat)
    (h_not_term : n = 0 ∨
      ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt (n - 1)) :
    (Nat.fib (n + 1) : ℤ) ≤ mathlib_dens_int_gen n o m := by
  have h := GenContFract.succ_nth_fib_le_of_nth_den
    (v := (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) (n := n) h_not_term
  rw [mathlib_dens_int_gen_spec n o m] at h
  exact_mod_cast h

/-- **Mathlib's `nums 0` for `o/m`** (ℝ-version): direct from
`zeroth_num_eq_h` + `of_h_eq_floor` + `Rat.floor_natCast_div_natCast` +
`Rat.floor_cast`. The 0-th convergent numerator equals `o / m` as Nat. -/
theorem mathlib_nums_zero_eq (o m : Nat) (_h_m_pos : 0 < m) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).nums 0
      = ((o / m : Nat) : ℝ) := by
  rw [GenContFract.zeroth_num_eq_h, GenContFract.of_h_eq_floor]
  rw [show ((((o : Nat) : ℝ) / ((m : Nat) : ℝ)) : ℝ)
      = ((((o : Nat) : ℚ) / ((m : Nat) : ℚ) : ℚ) : ℝ) from by push_cast; ring]
  rw [Rat.floor_cast, Rat.floor_natCast_div_natCast]
  push_cast; rfl

/-- **Mathlib's `dens 0` for `o/m`** (ℝ-version): direct from
`zeroth_den_eq_one`. The 0-th convergent denominator is always 1. -/
theorem mathlib_dens_zero_eq (o m : Nat) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).dens 0 = 1 :=
  GenContFract.zeroth_den_eq_one

/-- **Mathlib's `dens 1` for `o/m`, non-terminated** (ℝ-version): when
`o % m ≠ 0`, `dens 1 = m/(o%m)`. Via `of_s_head` + `first_den_eq` +
`Int.fract_div_natCast_eq_div_natCast_mod` + `Rat.floor_natCast_div_natCast`. -/
theorem mathlib_dens_one_eq_nondiv (o m : Nat) (h_m_pos : 0 < m)
    (h_mod : o % m ≠ 0) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).dens 1
      = ((m / (o % m) : Nat) : ℝ) := by
  have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
  have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) ≠ 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_mod_pos : 0 < o % m := Nat.pos_of_ne_zero h_mod
    have h_num_pos : (0 : ℝ) < ((o % m : Nat) : ℝ) := by exact_mod_cast h_mod_pos
    positivity
  have h_head := GenContFract.of_s_head (K := ℝ)
    (v := (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))) h_fract_ne
  have h_first := GenContFract.first_den_eq
    (g := GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ)))
    (gp := { a := 1, b := ↑⌊(Int.fract (((o : ℕ) : ℝ) / ((m : Nat) : ℝ)))⁻¹⌋ })
    (zeroth_s_eq := by
      show (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.get? 0 = some _
      rw [show (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.get? 0
           = (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.head from rfl]
      exact h_head)
  rw [h_first]
  show (↑⌊(Int.fract ((↑o : ℝ) / ((m : Nat) : ℝ)))⁻¹⌋ : ℝ)
       = ((m / (o % m) : Nat) : ℝ)
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
  have h_eq : (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))
            = ((((m : Nat) : ℚ) / ((o % m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  rw [h_eq, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  push_cast
  rfl

/-- **Mathlib's `nums 1` for `o/m`, non-terminated** (ℝ-version): when
`o % m ≠ 0`, `nums 1 = (m/(o%m)) * (o/m) + 1` (Nat-cast). Uses
`first_num_eq` (which gives `nums 1 = b·h + 1` where `a=1` from
SimpContFract) + floor computations + `norm_cast` to clean up Int/Nat
division mismatches. -/
theorem mathlib_nums_one_eq_nondiv (o m : Nat) (h_m_pos : 0 < m)
    (h_mod : o % m ≠ 0) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).nums 1
      = ((m / (o % m) * (o / m) + 1 : Nat) : ℝ) := by
  have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) ≠ 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have h_mod_pos : 0 < o % m := Nat.pos_of_ne_zero h_mod
    have h_num_pos : (0 : ℝ) < ((o % m : Nat) : ℝ) := by exact_mod_cast h_mod_pos
    have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
    positivity
  have h_head := GenContFract.of_s_head (K := ℝ)
    (v := (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))) h_fract_ne
  have h_first := GenContFract.first_num_eq
    (g := GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ)))
    (gp := { a := 1, b := ↑⌊(Int.fract (((o : ℕ) : ℝ) / ((m : Nat) : ℝ)))⁻¹⌋ })
    (zeroth_s_eq := by
      show (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.get? 0 = some _
      rw [show (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.get? 0
           = (GenContFract.of (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))).s.head from rfl]
      exact h_head)
  rw [h_first]
  rw [GenContFract.of_h_eq_floor]
  show (↑⌊(Int.fract ((↑o : ℝ) / ((m : Nat) : ℝ)))⁻¹⌋ : ℝ) *
       ⌊((↑o : ℝ) / ((m : Nat) : ℝ))⌋ + 1
       = ((m / (o % m) * (o / m) + 1 : Nat) : ℝ)
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
  have h_eq1 : (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))
            = ((((m : Nat) : ℚ) / ((o % m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  have h_eq2 : (((o : Nat) : ℝ) / ((m : Nat) : ℝ))
            = ((((o : Nat) : ℚ) / ((m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  rw [h_eq1, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  rw [h_eq2, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  norm_cast

/-- **n=0 base case of the joint state-tracking invariant** (Phase 3
r_found_1, added 2026-05-24 tick 73): when `m > 0` and the CF isn't
terminated at step 0, cf_aux_full's depth-2 state matches mathlib's
(nums 0, nums 1, dens 0, dens 1). Combines `cf_aux_full_2_nondiv` (LHS
explicit value) with the four mathlib step-0/step-1 helpers. -/
theorem cf_aux_full_matches_mathlib_zero (o m : Nat) (h_m_pos : 0 < m)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0) :
    (GenContFract.of ((o : ℝ) / m)).nums 0 = (((cf_aux_full 2 o m 0 1 1 0).1 : Nat) : ℝ) ∧
    (GenContFract.of ((o : ℝ) / m)).nums 1 = (((cf_aux_full 2 o m 0 1 1 0).2.1 : Nat) : ℝ) ∧
    (GenContFract.of ((o : ℝ) / m)).dens 0 = (((cf_aux_full 2 o m 0 1 1 0).2.2.1 : Nat) : ℝ) ∧
    (GenContFract.of ((o : ℝ) / m)).dens 1 = (((cf_aux_full 2 o m 0 1 1 0).2.2.2 : Nat) : ℝ) := by
  have h_mod : o % m ≠ 0 := nondiv_of_not_terminated_zero o m h_not_term
  have h_cast : ((o : ℝ) / m) = (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) := by push_cast; rfl
  rw [cf_aux_full_2_nondiv o m h_m_pos h_mod]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_cast]; exact mathlib_nums_zero_eq o m h_m_pos
  · rw [h_cast]; exact mathlib_nums_one_eq_nondiv o m h_m_pos h_mod
  · rw [h_cast, mathlib_dens_zero_eq]; simp
  · rw [h_cast]; exact mathlib_dens_one_eq_nondiv o m h_m_pos h_mod

/-- **Parametric general bridge invariant** (Phase 3 r_found_1, added
2026-05-24 by direction "focus on Legendre_ContinuedFraction sorries"):
The CRUX of the cf_aux ↔ mathlib bridge.

For any `n`, any current cf_aux Euclidean state `(o, m)` (with `m > 0`),
and any initial cf_aux_full state `(p_prev, p_curr, q_prev, q_curr)`
matching mathlib's `contsAux` at indices `(K, K+1)` for some `v0`, and
provided the Euclidean iteration of `(o, m)` produces the right partial
denominators `b_K, b_{K+1}, ...` of `v0`'s continued fraction, then after
`n` cf_aux steps the state matches mathlib's `contsAux` at `(K+n, K+n+1)`.

This is the GENERAL form that subsumes the specific-initial-state versions.
The succ case proof uses `contsAux_recurrence` (mathlib) and `cf_aux_succ_pos`
(local) — they have STRUCTURALLY identical recurrences modulo a Nat ↔ ℝ cast.

Succ case is the SINGLE remaining cf_aux ↔ mathlib structural sorry. -/
theorem cf_aux_full_general_match
    (n : Nat) (o m : Nat) (h_m_pos : 0 < m)
    (v0 : ℝ) (K : Nat)
    (p_prev p_curr q_prev q_curr : Nat)
    (h_state :
      ((p_prev : ℝ) = ((GenContFract.of v0).contsAux K).a) ∧
      ((p_curr : ℝ) = ((GenContFract.of v0).contsAux (K+1)).a) ∧
      ((q_prev : ℝ) = ((GenContFract.of v0).contsAux K).b) ∧
      ((q_curr : ℝ) = ((GenContFract.of v0).contsAux (K+1)).b))
    (_h_eucl : ∀ i : ℕ, ¬ (GenContFract.of v0).TerminatedAt (K + i) →
      (GenContFract.of v0).s.get? (K + i) =
        some ⟨1, (((euclidean_iter i o m).1 / (euclidean_iter i o m).2 : Nat) : ℝ)⟩)
    (_h_not_term : ¬ (GenContFract.of v0).TerminatedAt (K + n)) :
    (((cf_aux_full n o m p_prev p_curr q_prev q_curr).1 : Nat) : ℝ)
        = ((GenContFract.of v0).contsAux (K + n)).a ∧
    (((cf_aux_full n o m p_prev p_curr q_prev q_curr).2.1 : Nat) : ℝ)
        = ((GenContFract.of v0).contsAux (K + n + 1)).a ∧
    (((cf_aux_full n o m p_prev p_curr q_prev q_curr).2.2.1 : Nat) : ℝ)
        = ((GenContFract.of v0).contsAux (K + n)).b ∧
    (((cf_aux_full n o m p_prev p_curr q_prev q_curr).2.2.2 : Nat) : ℝ)
        = ((GenContFract.of v0).contsAux (K + n + 1)).b := by
  induction n generalizing o m p_prev p_curr q_prev q_curr K with
  | zero =>
    -- n=0: cf_aux_full 0 returns the initial state directly; h_state matches.
    simp only [cf_aux_full, Nat.add_zero]
    exact ⟨h_state.1, h_state.2.1, h_state.2.2.1, h_state.2.2.2⟩
  | succ k ih =>
    -- Step 1: Unfold cf_aux_full (k+1) o m (...) using m > 0.
    rw [show cf_aux_full (k+1) o m p_prev p_curr q_prev q_curr
          = cf_aux_full k m (o%m) p_curr ((o/m)*p_curr + p_prev)
                                  q_curr ((o/m)*q_curr + q_prev) from by
      show (if m = 0 then (p_prev, p_curr, q_prev, q_curr)
            else cf_aux_full k m (o%m) p_curr ((o/m)*p_curr + p_prev)
                                       q_curr ((o/m)*q_curr + q_prev)) = _
      rw [if_neg h_m_pos.ne']]
    -- Step 2: Case split on o%m. If 0, mathlib terminates at K+1 contradicting
    -- h_not_term at K+k+1 ≥ K+1 (assuming k can be anything; but we still need
    -- to prove this rigorously, hence the sub-sorry). If > 0, apply IH at k
    -- with shifted parameters.
    by_cases h_om : o % m = 0
    · -- o%m = 0: derive contradiction.
      -- Strategy: case split on Terminated at (K+1).
      -- - If Terminated: by terminated_stable + K+1 ≤ K+(k+1), contradicts h_not_term.
      -- - If ¬ Terminated: h_eucl @ 1 forces s.get? (K+1) = some ⟨1, m/0 = 0⟩.
      --   But mathlib's IntFractPair.one_le_succ_nth_stream_b says b ≥ 1. Contradiction.
      exfalso
      by_cases h_term_K1 : (GenContFract.of v0).TerminatedAt (K + 1)
      · -- Case 1: Terminated at K+1 → Terminated at K+(k+1) by stable → contradicts h_not_term.
        apply _h_not_term
        exact GenContFract.terminated_stable (by omega : K + 1 ≤ K + (k + 1)) h_term_K1
      · -- Case 2: ¬ Terminated at K+1 → derive impossible stream value.
        have h_eucl_1 := _h_eucl 1 (by
          show ¬ (GenContFract.of v0).TerminatedAt (K + 1)
          have : K + 1 = K + 1 := rfl
          exact h_term_K1)
        -- h_eucl_1 : s.get? (K+1) = some ⟨1, ((euclidean_iter 1 o m).1 / .2 : Nat) : ℝ⟩.
        -- With o%m = 0 and m > 0: euclidean_iter 1 o m = (m, 0), quotient = m/0 = 0.
        have h_iter_1 : euclidean_iter 1 o m = (m, 0) := by
          show (if m = 0 then (o, m) else euclidean_iter 0 m (o%m)) = _
          rw [if_neg h_m_pos.ne', h_om]
          rfl
        rw [h_iter_1] at h_eucl_1
        simp at h_eucl_1
        -- h_eucl_1 : s.get? (K+1) = some ⟨1, 0⟩.
        -- Extract: ∃ ifp, stream v0 (K+2) = some ifp ∧ ↑ifp.b = 0.
        obtain ⟨ifp, h_stream, h_b_eq⟩ :=
          GenContFract.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some h_eucl_1
        -- h_b_eq : (↑ifp.b : ℝ) = (⟨1, 0⟩ : GenContFract.Pair ℝ).b
        simp only [show ((⟨1, 0⟩ : GenContFract.Pair ℝ).b) = (0 : ℝ) from rfl] at h_b_eq
        have h_ifp_b_zero : ifp.b = 0 := by exact_mod_cast h_b_eq
        -- Mathlib: stream v (n+1) = some ifp → 1 ≤ ifp.b. Contradiction.
        have h_one_le := GenContFract.IntFractPair.one_le_succ_nth_stream_b h_stream
        omega
    · -- o%m > 0: apply IH with new (o', m') := (m, o%m), K' := K+1.
      have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
      -- Step (a): get s.get? K from h_eucl at i=0.
      have h_K_lt : K ≤ K + (k+1) := by omega
      have h_not_term_K : ¬ (GenContFract.of v0).TerminatedAt K := fun h =>
        _h_not_term (GenContFract.terminated_stable h_K_lt h)
      have h_eucl_0 := _h_eucl 0 h_not_term_K
      -- Simplify euclidean_iter 0 o m = (o, m).
      have h_iter_0 : euclidean_iter 0 o m = (o, m) := rfl
      rw [Nat.add_zero, h_iter_0] at h_eucl_0
      -- h_eucl_0 : s.get? K = some ⟨1, ((o/m : Nat) : ℝ)⟩
      -- Step (b): compute contsAux (K+2) via contsAux_recurrence with gp := ⟨1, o/m⟩.
      have h_contsAux_K : (GenContFract.of v0).contsAux K = ⟨(p_prev : ℝ), (q_prev : ℝ)⟩ :=
        GenContFract.Pair.mk.injEq .. |>.mpr ⟨h_state.1.symm, h_state.2.2.1.symm⟩
      have h_contsAux_K1 : (GenContFract.of v0).contsAux (K + 1) =
          ⟨(p_curr : ℝ), (q_curr : ℝ)⟩ :=
        GenContFract.Pair.mk.injEq .. |>.mpr ⟨h_state.2.1.symm, h_state.2.2.2.symm⟩
      have h_contsAux_K2 := GenContFract.contsAux_recurrence
        (g := GenContFract.of v0) (n := K) h_eucl_0 h_contsAux_K h_contsAux_K1
      -- h_contsAux_K2 : contsAux (K+2) = ⟨(o/m)·p_curr + 1·p_prev, (o/m)·q_curr + 1·q_prev⟩
      -- Step (c): build h_eucl' for new (m, o%m) at K+1, via h_eucl@(i+1).
      have h_eucl' : ∀ i : ℕ, ¬ (GenContFract.of v0).TerminatedAt (K + 1 + i) →
          (GenContFract.of v0).s.get? (K + 1 + i) =
            some ⟨1, (((euclidean_iter i m (o%m)).1 / (euclidean_iter i m (o%m)).2 : Nat) : ℝ)⟩ := by
        intros i h_nt
        have h_shift : K + 1 + i = K + (i + 1) := by ring
        rw [h_shift] at h_nt ⊢
        have h := _h_eucl (i+1) h_nt
        -- euclidean_iter (i+1) o m = euclidean_iter i m (o%m) (since m > 0).
        have h_iter_shift : euclidean_iter (i+1) o m = euclidean_iter i m (o%m) := by
          show (if m = 0 then (o, m) else euclidean_iter i m (o%m)) = euclidean_iter i m (o%m)
          rw [if_neg h_m_pos.ne']
        rw [h_iter_shift] at h
        exact h
      -- Step (d): build h_not_term' at K+1+k = K+(k+1).
      have h_not_term' : ¬ (GenContFract.of v0).TerminatedAt (K + 1 + k) := by
        have : K + 1 + k = K + (k + 1) := by ring
        rw [this]; exact _h_not_term
      -- Step (e): build h_state' for new state.
      have h_state' :
          (((p_curr : Nat) : ℝ) = ((GenContFract.of v0).contsAux (K+1)).a) ∧
          ((((o/m)*p_curr + p_prev : Nat) : ℝ) = ((GenContFract.of v0).contsAux (K+1+1)).a) ∧
          (((q_curr : Nat) : ℝ) = ((GenContFract.of v0).contsAux (K+1)).b) ∧
          ((((o/m)*q_curr + q_prev : Nat) : ℝ) = ((GenContFract.of v0).contsAux (K+1+1)).b) := by
        refine ⟨h_state.2.1, ?_, h_state.2.2.2, ?_⟩
        · -- ((o/m)*p_curr + p_prev : Nat) : ℝ = contsAux (K+2) .a
          have : K + 1 + 1 = K + 2 := by ring
          rw [this, h_contsAux_K2]
          push_cast; ring
        · -- ((o/m)*q_curr + q_prev : Nat) : ℝ = contsAux (K+2) .b
          have : K + 1 + 1 = K + 2 := by ring
          rw [this, h_contsAux_K2]
          push_cast; ring
      -- Apply IH.
      have h_apply :=
        ih m (o%m) h_om_pos (K+1) p_curr ((o/m)*p_curr + p_prev) q_curr ((o/m)*q_curr + q_prev)
            h_state' h_eucl' h_not_term'
      -- Goal: cf_aux_full k m (o%m) ... matches contsAux at (K+(k+1), K+(k+1)+1).
      -- IH gives matching at (K+1+k, K+1+k+1). Just rewrite K+(k+1) → K+1+k.
      have h_idx : K + (k + 1) = K + 1 + k := by ring
      rw [h_idx]
      exact h_apply

/-- **ℝ-version of `cf_of_div_succ_step`** (added 2026-05-24): the (n+1)-th
stream entry of `GenContFract.of (o/m : ℝ)` equals the n-th of
`GenContFract.of (m/(o%m) : ℝ)`. Same proof as the ℚ version. -/
theorem cf_of_div_succ_step_R (o m n : Nat) (_h_mod_pos : 0 < o % m) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.get? (n+1) =
      (GenContFract.of (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))).s.get? n := by
  rw [GenContFract.of_s_succ]
  congr 2
  rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]

/-- **Terminated at 0 when `o % m = 0`** (added 2026-05-24): when the
remainder is 0 (including the m = 0 case, where o % 0 = o ≠ 0 doesn't
hold but v = 0/0 = 0 ℝ still gives terminated), mathlib's CF for v = o/m
terminates at step 0. Extracted from the inline proof in
`eucl_iter_match_stream`. -/
theorem terminated_at_0_when_mod_zero (o m : Nat) (h_om : o % m = 0) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0 := by
  rw [GenContFract.terminatedAt_iff_s_none]
  have h_fract_eq : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) = 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod, h_om]
    simp
  have h_stream_none : GenContFract.IntFractPair.stream
      (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 1 = none :=
    GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero (n := 0) rfl h_fract_eq
  rw [GenContFract.of_s_head_aux, h_stream_none]
  rfl

/-- **Converse base case** (added 2026-05-24): when mathlib's CF terminates
at step 0 for v=o/m with m > 0, then o%m = 0.

This is the j=0 base case of the eventual `eucl_terminated_of_mathlib_terminated`
helper. Direct from `nondiv_of_not_terminated_zero`'s contrapositive. -/
theorem mod_zero_of_terminated_at_0 (o m : Nat) (_h_m_pos : 0 < m)
    (h_term : (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0) :
    o % m = 0 := by
  by_contra h_om_ne
  -- nondiv_of_not_terminated_zero: ¬ Terminated at 0 → o%m ≠ 0.
  -- We have Terminated at 0 and want o%m = 0.
  -- The lemma's contrapositive (o%m = 0 → Terminated at 0) goes the wrong way.
  -- Need direct proof: Terminated at 0 → fract v = 0 → o%m = 0.
  apply h_om_ne
  -- Goal: o % m = 0.
  -- From Terminated at 0: s.get? 0 = none → stream 1 = none → fract v = 0 → o%m = 0.
  rw [GenContFract.terminatedAt_iff_s_none] at h_term
  rw [GenContFract.of_s_head_aux] at h_term
  -- h_term : Option.bind (stream v 1) ... = none
  -- So stream v 1 = none.
  have h_stream_1 : GenContFract.IntFractPair.stream
      (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 1 = none := by
    rcases h_eq : GenContFract.IntFractPair.stream
        (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 1 with _ | ifp
    · rfl
    · rw [h_eq] at h_term; exact absurd h_term (by simp)
  -- stream 1 = none → fract v = 0.
  rw [GenContFract.IntFractPair.succ_nth_stream_eq_none_iff] at h_stream_1
  -- h_stream_1 : stream 0 = none ∨ ∃ ifp, stream 0 = some ifp ∧ ifp.fr = 0
  rcases h_stream_1 with h_s0_none | ⟨ifp, h_s0, h_fr⟩
  · -- stream 0 = none: impossible (stream 0 is always some).
    have : GenContFract.IntFractPair.stream
        (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 0 =
        some (GenContFract.IntFractPair.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) := rfl
    rw [this] at h_s0_none
    exact absurd h_s0_none (by simp)
  · -- stream 0 = some ifp, ifp.fr = 0.
    -- stream 0 = some {b=⌊v⌋, fr=fract v}, so ifp.fr = fract v = 0.
    have h_s0_val : GenContFract.IntFractPair.stream
        (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 0 =
        some (GenContFract.IntFractPair.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))) := rfl
    rw [h_s0_val] at h_s0
    have h_ifp_eq : ifp = GenContFract.IntFractPair.of
        (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) := by
      exact (Option.some_inj.mp h_s0).symm
    rw [h_ifp_eq] at h_fr
    -- h_fr : (intFractPair.of v).fr = 0 = fract v = 0.
    have h_fr_eq : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) = 0 := h_fr
    rw [Int.fract_div_natCast_eq_div_natCast_mod] at h_fr_eq
    -- h_fr_eq : (o % m : ℝ) / (m : ℝ) = 0
    have h_m_ne : ((m : Nat) : ℝ) ≠ 0 := by
      exact_mod_cast _h_m_pos.ne'
    have : ((o % m : Nat) : ℝ) = 0 := by
      field_simp at h_fr_eq
      linarith
    exact_mod_cast this

/-- **Converse direction: mathlib-terminated → Euclidean-terminated** (added
2026-05-24): when mathlib's CF terminates at step j for v=o/m (m > 0),
cf_aux's Euclidean iteration has hit `.2 = 0` by step j+1.

Proof: induction on j. Base via `mod_zero_of_terminated_at_0`. Succ uses
`cf_of_div_succ_step_R` to shift mathlib's view + IH at (m, o%m). -/
theorem eucl_terminated_of_mathlib_terminated (o m : Nat) (h_m_pos : 0 < m)
    (j : Nat) (h_term : (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt j) :
    (euclidean_iter (j+1) o m).2 = 0 := by
  induction j generalizing o m with
  | zero =>
    have h_om : o % m = 0 := mod_zero_of_terminated_at_0 o m h_m_pos h_term
    show (if m = 0 then (o, m) else euclidean_iter 0 m (o % m)).2 = 0
    rw [if_neg h_m_pos.ne']
    exact h_om
  | succ j' ih =>
    by_cases h_om : o % m = 0
    · -- o%m = 0: mathlib already terminated at 0, so euclidean_iter 1 hits 0.
      -- Use stability to extend.
      have h_eucl_1 : (euclidean_iter 1 o m).2 = 0 := by
        show (if m = 0 then (o, m) else euclidean_iter 0 m (o % m)).2 = 0
        rw [if_neg h_m_pos.ne']
        exact h_om
      have h_assoc : j' + 2 = 1 + (j' + 1) := by ring
      rw [h_assoc]
      exact eucl_iter_stable 1 o m (j' + 1) h_eucl_1
    · -- o%m > 0: shift via cf_of_div_succ_step_R + apply IH at (m, o%m).
      have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
      have h_term' : (GenContFract.of (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))).TerminatedAt j' := by
        rw [GenContFract.terminatedAt_iff_s_none] at h_term ⊢
        rw [← cf_of_div_succ_step_R o m j' h_om_pos]
        exact h_term
      have h_ih := ih m (o % m) h_om_pos h_term'
      -- h_ih : (euclidean_iter (j'+1) m (o%m)).2 = 0
      -- Need: (euclidean_iter (j'+2) o m).2 = 0
      have h_assoc : j' + 2 = (j' + 1) + 1 := by ring
      rw [h_assoc]
      show (if m = 0 then (o, m) else euclidean_iter (j' + 1) m (o % m)).2 = 0
      rw [if_neg h_m_pos.ne']
      exact h_ih

/-- **Mathlib-terminated ↔ Euclidean-terminated bridge** (added 2026-05-24):
when cf_aux's Euclidean iteration hits `.2 = 0` at step `j+1`, mathlib's
CF stream for `v = o/m` terminates at step `j`. This is the last piece
needed to close the terminated-case bridge in `TODO_non_div_terminated_stable`.

Proof: induction on `j`. The base case uses `terminated_at_0_when_mod_zero`.
The succ case shifts via `cf_of_div_succ_step_R` and applies IH at the
shifted Euclidean state. -/
theorem mathlib_terminated_of_eucl_terminated (o m : Nat) (h_m_pos : 0 < m)
    (j : Nat) (h_eucl : (euclidean_iter (j+1) o m).2 = 0) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt j := by
  induction j generalizing o m with
  | zero =>
    -- h_eucl : (euclidean_iter 1 o m).2 = (m, o%m).2 = o%m = 0 (since m > 0)
    have h_eucl_unfold : euclidean_iter 1 o m = (m, o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter 0 m (o%m)) = _
      rw [if_neg h_m_pos.ne']; rfl
    rw [h_eucl_unfold] at h_eucl
    -- h_eucl : o % m = 0
    exact terminated_at_0_when_mod_zero o m h_eucl
  | succ j' ih =>
    -- h_eucl : (euclidean_iter (j'+2) o m).2 = 0
    have h_assoc : j' + 2 = (j' + 1) + 1 := by ring
    rw [h_assoc] at h_eucl
    have h_unfold : euclidean_iter ((j' + 1) + 1) o m = euclidean_iter (j' + 1) m (o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter (j' + 1) m (o % m)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_unfold] at h_eucl
    -- h_eucl : (euclidean_iter (j'+1) m (o%m)).2 = 0
    by_cases h_om : o % m = 0
    · -- o%m = 0: TerminatedAt 0 + terminated_stable.
      have h_term_0 : (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0 :=
        terminated_at_0_when_mod_zero o m h_om
      exact GenContFract.terminated_stable (by omega : 0 ≤ j' + 1) h_term_0
    · -- o%m > 0: shift via cf_of_div_succ_step_R + apply IH.
      have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
      have h_ih := ih m (o % m) h_om_pos h_eucl
      -- h_ih : TerminatedAt j' for v' = m/(o%m).
      -- Want: TerminatedAt (j'+1) for v = o/m. Bridge via cf_of_div_succ_step_R.
      rw [GenContFract.terminatedAt_iff_s_none] at h_ih ⊢
      rw [cf_of_div_succ_step_R o m j' h_om_pos]
      exact h_ih

/-- **Eucl iter ↔ mathlib stream correspondence** (added 2026-05-24):
For `v = o/m` with `m > 0`, mathlib's `s.get? i = some ⟨1, x⟩` where
`x = quotient of the (i+1)-th Euclidean iterate of (o, m)`. By induction
on i using `cf_of_div_succ_step_R` and the i=0 case from `of_s_head` +
floor computations.

This is the `h_eucl` hypothesis the general lemma needs, computed for the
specific case where v0 = o/m and the cf_aux call uses (m, o%m) as initial
Euclidean state. -/
theorem eucl_iter_match_stream (o m : Nat) (h_m_pos : 0 < m) (i : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt i) :
    (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.get? i =
      some ⟨1, (((euclidean_iter (i+1) o m).1 / (euclidean_iter (i+1) o m).2 : Nat) : ℝ)⟩ := by
  induction i generalizing o m with
  | zero =>
    -- Base case: s.get? 0 = some ⟨1, ⌊1/Int.fract v⌋⟩ via of_s_head.
    -- ¬ Terminated at 0 → o%m ≠ 0 → fract v ≠ 0 → use of_s_head.
    have h_om : o % m ≠ 0 := nondiv_of_not_terminated_zero o m h_not_term
    have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
    have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
    have h_fract_ne : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) ≠ 0 := by
      rw [Int.fract_div_natCast_eq_div_natCast_mod]
      have h_num_pos : (0 : ℝ) < ((o % m : Nat) : ℝ) := by exact_mod_cast h_om_pos
      positivity
    have h_head := GenContFract.of_s_head (K := ℝ)
      (v := (((o : ℕ) : ℝ) / ((m : Nat) : ℝ))) h_fract_ne
    -- h_head : s.head = some ⟨1, ⌊(Int.fract v)⁻¹⌋⟩
    rw [show (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.get? 0
         = (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.head from rfl,
        h_head]
    congr 2
    -- Goal: ⌊(Int.fract (o/m))⁻¹⌋ = ((euclidean_iter 1 o m).1 / .2 : Nat) : ℝ
    have h_iter_1 : (euclidean_iter 1 o m) = (m, o % m) := by
      show (if m = 0 then (o, m) else euclidean_iter 0 m (o%m)) = _
      rw [if_neg h_m_pos.ne']; rfl
    rw [h_iter_1]
    -- Goal: ↑⌊(Int.fract (o/m))⁻¹⌋ = ((m / (o%m) : Nat) : ℝ)
    rw [Int.fract_div_natCast_eq_div_natCast_mod, inv_div]
    -- Goal: ↑⌊(m : ℝ) / (o%m : ℝ)⌋ = ((m / (o%m) : Nat) : ℝ)
    have h_eq : (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))
              = ((((m : Nat) : ℚ) / ((o % m : Nat) : ℚ) : ℚ) : ℝ) := by push_cast; ring
    rw [h_eq, Rat.floor_cast, Rat.floor_natCast_div_natCast]
    push_cast; rfl
  | succ j ih =>
    -- Inductive case: use cf_of_div_succ_step_R to shift to (m, o%m), apply IH.
    -- Need ¬ Terminated at j+1 for v=o/m. By stream_succ_eq_none_iff, if Terminated at 0
    -- (o%m = 0), then Terminated at j+1 too. So ¬ Terminated at j+1 → o%m ≠ 0.
    have h_om : o % m ≠ 0 := by
      intro h
      apply h_not_term
      apply GenContFract.terminated_stable (by omega : 0 ≤ j + 1)
      -- Show TerminatedAt 0 for v=o/m when o%m = 0.
      rw [GenContFract.terminatedAt_iff_s_none]
      -- s.get? 0 = none. Use of_s_head_aux + stream_eq_none_of_fr_eq_zero.
      have h_fract_eq : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) = 0 := by
        rw [Int.fract_div_natCast_eq_div_natCast_mod, h]
        simp
      have h_stream_none : GenContFract.IntFractPair.stream
          (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 1 = none :=
        GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero (n := 0) rfl h_fract_eq
      rw [GenContFract.of_s_head_aux, h_stream_none]
      rfl
    have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
    -- Shift: s.get? (j+1) for o/m = s.get? j for m/(o%m).
    rw [cf_of_div_succ_step_R o m j h_om_pos]
    -- Apply IH at (m, o%m) at index j.
    have h_not_term_shifted :
        ¬ (GenContFract.of (((m : Nat) : ℝ) / ((o % m : Nat) : ℝ))).TerminatedAt j := by
      intro h_term
      apply h_not_term
      -- TerminatedAt at j+1 for o/m ↔ s.get? (j+1) for o/m = none.
      rw [GenContFract.terminatedAt_iff_s_none] at h_term ⊢
      rw [cf_of_div_succ_step_R o m j h_om_pos]
      exact h_term
    have h_ih := ih m (o%m) h_om_pos h_not_term_shifted
    rw [h_ih]
    congr 2
    -- Goal: euclidean_iter (j+1) m (o%m) = euclidean_iter (j+2) o m.
    have h_shift : euclidean_iter (j+2) o m = euclidean_iter (j+1) m (o%m) := by
      show (if m = 0 then (o, m) else euclidean_iter (j+1) m (o%m)) = _
      rw [if_neg h_m_pos.ne']
    rw [h_shift]

/-- **`cf_aux_full_matches_mathlib_strong`** (Phase 3 r_found_1, added
2026-05-24 via bridge-consolidation tick): cf_aux_full's depth-(n+2) output
on `(o, m, 0, 1, 1, 0)` matches mathlib's `(nums n, nums (n+1), dens n,
dens (n+1))` for `v = o/m`.

Hypothesis: `¬ Terminated at (n+1)` (stronger than the weaker variant — this
makes the proof go through cleanly via the general lemma without needing
case analysis on whether matlibs's CF terminates exactly at n+1).

Proof: peel off Stage A's first cf_aux step (uses m > 0); state matches
`contsAux 0/1` for v = o/m; apply `cf_aux_full_general_match` at K=0, depth
n+1, with `eucl_iter_match_stream` providing h_eucl. -/
theorem cf_aux_full_matches_mathlib_strong (o m : Nat) (h_m_pos : 0 < m)
    (n : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt (n+1)) :
    (((cf_aux_full (n+2) o m 0 1 1 0).1 : Nat) : ℝ) =
        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (n+1)).a ∧
    (((cf_aux_full (n+2) o m 0 1 1 0).2.1 : Nat) : ℝ) =
        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (n+2)).a ∧
    (((cf_aux_full (n+2) o m 0 1 1 0).2.2.1 : Nat) : ℝ) =
        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (n+1)).b ∧
    (((cf_aux_full (n+2) o m 0 1 1 0).2.2.2 : Nat) : ℝ) =
        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (n+2)).b := by
  -- Stage A peel: cf_aux_full (n+2) o m 0 1 1 0 = cf_aux_full (n+1) m (o%m) 1 (o/m) 0 1.
  have h_peel : cf_aux_full (n+2) o m 0 1 1 0
      = cf_aux_full (n+1) m (o%m) 1 (o/m) 0 1 := by
    show (if m = 0 then _ else cf_aux_full (n+1) m (o%m) 1 ((o/m)*1+0) 0 ((o/m)*0+1)) = _
    rw [if_neg h_m_pos.ne']
    simp [Nat.mul_zero, Nat.mul_one]
  rw [h_peel]
  -- Apply general lemma. v0 := o/m, K := 0, (o', m') := (m, o%m), n' := n+1.
  -- Need: m' = o%m > 0. Derive from ¬ Terminated at (n+1) → ¬ Terminated at 0 → o%m > 0.
  have h_not_term_0 : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt 0 :=
    fun h => h_not_term (GenContFract.terminated_stable (by omega : 0 ≤ n+1) h)
  have h_om : o % m ≠ 0 := nondiv_of_not_terminated_zero o m h_not_term_0
  have h_om_pos : 0 < o % m := Nat.pos_of_ne_zero h_om
  -- Build h_state: initial state (1, o/m, 0, 1) matches contsAux 0/1 for v=o/m.
  have h_zero_contsAux : ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 0).a = 1 ∧
                        ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 0).b = 0 := by
    rw [GenContFract.zeroth_contAux_eq_one_zero]; exact ⟨rfl, rfl⟩
  -- contsAux 1 = ⟨h, 1⟩ where h = ⌊v⌋ = o/m (Nat-div).
  have h_one_contsAux_a : ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).a
                          = ((o / m : Nat) : ℝ) := by
    -- Use nth_cont_eq_succ_nth_contAux + zeroth_num_eq_h equivalent reasoning.
    -- Actually mathlib_nums_zero_eq gives nums 0 = o/m as ℝ.
    have := mathlib_nums_zero_eq o m h_m_pos
    -- nums 0 = (g.contsAux 1).a (by definitions). So we can rewrite.
    show ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).a
       = ((o / m : Nat) : ℝ)
    rw [show ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).a
         = (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).nums 0 from rfl]
    exact this
  have h_one_contsAux_b : ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).b
                          = 1 := by
    show ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).b = 1
    rw [show ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 1).b
         = (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).dens 0 from rfl]
    exact GenContFract.zeroth_den_eq_one
  have h_state :
      (((1 : Nat) : ℝ) = ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 0).a) ∧
      ((((o/m : Nat) : ℝ)) = ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (0+1)).a) ∧
      (((0 : Nat) : ℝ) = ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux 0).b) ∧
      (((1 : Nat) : ℝ) = ((GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).contsAux (0+1)).b) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_zero_contsAux.1]; push_cast; rfl
    · rw [h_one_contsAux_a]
    · rw [h_zero_contsAux.2]; push_cast; rfl
    · rw [h_one_contsAux_b]; push_cast; rfl
  -- Build h_eucl: at iter i ¬ Terminated at i → s.get? i = some ⟨1, eucl_iter i m (o%m)⟩.
  have h_eucl : ∀ i : ℕ,
      ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt (0 + i) →
      (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).s.get? (0 + i) =
        some ⟨1, (((euclidean_iter i m (o%m)).1 / (euclidean_iter i m (o%m)).2 : Nat) : ℝ)⟩ := by
    intros i h_nt
    rw [Nat.zero_add] at h_nt ⊢
    rw [eucl_iter_match_stream o m h_m_pos i h_nt]
    -- Goal: some ⟨1, ↑((euclidean_iter (i+1) o m).1/.2)⟩ = some ⟨1, ↑((euclidean_iter i m (o%m)).1/.2)⟩
    have h_shift : euclidean_iter (i+1) o m = euclidean_iter i m (o%m) := by
      show (if m = 0 then (o, m) else euclidean_iter i m (o%m))
          = euclidean_iter i m (o%m)
      rw [if_neg h_m_pos.ne']
    rw [h_shift]
  -- Apply general lemma.
  have h_not_term' : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((m : Nat) : ℝ))).TerminatedAt (0 + (n+1)) := by
    rw [Nat.zero_add]; exact h_not_term
  have h_general := cf_aux_full_general_match (n+1) m (o%m) h_om_pos
    (((o : Nat) : ℝ) / ((m : Nat) : ℝ)) 0 1 (o/m) 0 1 h_state h_eucl h_not_term'
  -- h_general's RHS uses index `0 + (n+1)` and `0 + (n+1) + 1`. Simplify.
  rw [Nat.zero_add] at h_general
  exact h_general

/-- **Convergent recurrence for `GenContFract.of`** (Phase 3 r_found_1
infrastructure, added 2026-05-24 tick 59): the n+1-th convergent of v
equals `⌊v⌋ + 1/(n-th convergent of (Int.fract v)⁻¹)`. Direct from
mathlib's `Real.convergent_succ` + `Real.convs_eq_convergent` (which
bridges `Real.convergent` Rat-valued and `GenContFract.convs` Real-valued).
This is the building block for the dens/nums recurrence relations
needed by the cf_aux ↔ mathlib bridge. -/
theorem of_convs_succ_via_fract (v : ℝ) (n : Nat) :
    (GenContFract.of v).convs (n + 1) =
      (⌊v⌋ : ℝ) + ((GenContFract.of (Int.fract v)⁻¹).convs n)⁻¹ := by
  rw [Real.convs_eq_convergent v, Real.convs_eq_convergent (Int.fract v)⁻¹]
  rw [Real.convergent_succ]
  push_cast
  ring

/-- **Specialized convs swap when `0 < o < m`** (Phase 3 r_found_1,
added 2026-05-24 tick 60): when `o < m`, `⌊o/m⌋ = 0`, so the convergent
recurrence simplifies to a pure SWAP — the (n+1)th convergent of `o/m`
is the inverse of the n-th convergent of `m/o`. Crucial structural
property for the bridge when starting in the "fractional" regime. -/
theorem of_convs_succ_lt (o m : Nat) (h_lt : o < m) (h_o_pos : 0 < o)
    (n : Nat) :
    (GenContFract.of (((o : ℝ)) / ((m : Nat) : ℝ))).convs (n + 1) =
      ((GenContFract.of (((m : Nat) : ℝ) / ((o : Nat) : ℝ))).convs n)⁻¹ := by
  have h_m_pos : 0 < m := by omega
  have h_pow_pos_R : (0 : ℝ) < ((m : Nat) : ℝ) := by exact_mod_cast h_m_pos
  have h_o_pos_R : (0 : ℝ) < ((o : Nat) : ℝ) := by exact_mod_cast h_o_pos
  rw [Real.convs_eq_convergent, Real.convs_eq_convergent, Real.convergent_succ]
  have h_floor : ⌊((o : ℕ) : ℝ) / ((m : ℕ) : ℝ)⌋ = 0 := by
    apply Int.floor_eq_zero_iff.mpr
    constructor
    · positivity
    · rw [show (1 : ℝ) = (m : ℝ) / m by field_simp]
      apply div_lt_div_of_pos_right (by exact_mod_cast h_lt) h_pow_pos_R
  have h_fract : Int.fract (((o : Nat) : ℝ) / ((m : Nat) : ℝ))
                = ((o : Nat) : ℝ) / ((m : Nat) : ℝ) := by
    unfold Int.fract
    rw [h_floor]
    simp
  rw [h_floor, h_fract, inv_div]
  push_cast
  ring

/-- **`of_correctness_of_terminatedAt` accessor**: when `GenContFract.of v`
terminates at step `n`, the n-th convergent equals `v` exactly. Used
for rational-input correctness — once the CF terminates, we recover the
input rational. -/
theorem mathlib_convs_at_term (v : ℝ) (n : Nat)
    (h_term : (GenContFract.of v).TerminatedAt n) :
    (GenContFract.of v).convs n = v :=
  (GenContFract.of_correctness_of_terminatedAt h_term).symm

/-- Connect `mathlib_dens_int_gen` (general) to `mathlib_OF_post_step`
(specialized to `m = 2^bit`): they agree by spec uniqueness when both
extract the same dens value. -/
theorem mathlib_dens_int_gen_eq_OF_post_step (n o m : Nat) :
    mathlib_dens_int_gen n o (2^m) = mathlib_OF_post_step n o m := by
  have h1 := mathlib_dens_int_gen_spec n o (2^m)
  have h2 := mathlib_OF_post_step_spec n o m
  have h_cast : (((o : ℝ)) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) := by push_cast; rfl
  rw [h_cast] at h1
  have h_eq : ((mathlib_dens_int_gen n o (2^m) : ℤ) : ℝ) =
              ((mathlib_OF_post_step n o m : ℤ) : ℝ) := by
    rw [← h1, ← h2]
  exact_mod_cast h_eq

/-- **Strategy for the cf_aux ↔ mathlib bridge** (Phase 3 r_found_1,
documentation):

The bridge `mathlib_dens_int_gen n o m = cf_aux's q_curr after evolving from
initial state via n Euclidean steps` cannot be proved by simple induction on `n`
because cf_aux's recursive call uses NEW inputs `(m, o % m)` while
mathlib's `dens (n+1)` for `o/m` involves the SAME `o/m`. The connection
is via mathlib's `of_s_succ`: `(GenContFract.of (o/m)).s.get? (n+1) =
(GenContFract.of (m/(o%m))).s.get? n`, plus our `stream_succ_euclidean`.

The right joint invariant tracks cf_aux's running state `(p_prev, p_curr,
q_prev, q_curr)` against mathlib's (nums offset, nums (offset+1), dens
offset, dens (offset+1)) for an evolving offset. Each Euclidean step of
cf_aux advances offset by 1 in mathlib's framework. The succ case of the
joint induction then uses `nums_recurrence`/`dens_recurrence` to extend
both sides by one more step.

This invariant is mechanically constructable but proof-wise complex
(multi-tick effort). For now, captured here as design intent. -/
def cf_aux_bridge_invariant : Prop := True  -- placeholder docs

/-- **Empirical bridge validation by case enumeration**: hand-traced
proof that step-2 cf_aux output and mathlib dens(2) match for both
sub-cases (verified informally in tick 55 PROGRESS.md notes).

Case A (`o%2^m ≠ 0` AND `(2^m)%(o%2^m) = 0`): both sides give `(2^m)/(o%2^m)`.
  - cf_aux: a' = (2^m)/(o%2^m), stream terminates at step 1, dens(2) = dens(1) = a'.
Case B (`o%2^m ≠ 0` AND `(2^m)%(o%2^m) ≠ 0`): both sides give `a''·a' + 1`.
  - cf_aux: returns (a''·(a'·a+1)+a, a''·a'+1).
  - mathlib: b_0 = a', b_1 = a'', dens(2) = b_1·dens(1) + dens(0) = a''·a' + 1.

This case-enumeration validates the proof pattern. The general n-step proof
follows the SAME mechanism but inducted: cf_aux's "current after Euclidean
shift" matches mathlib's "dens at corresponding shifted offset". The
inductive step uses `dens_recurrence` + the Euclidean shift via
`stream_succ_euclidean`. Mechanical but ~50-100 lines. -/
def cf_aux_step_2_validated : Prop := True  -- empirical validation marker

-- (General bridge scaffold moved later — needs `mathlib_OF_post_step_nat_eq_OF_post_step_div_general`.)

/-- **Bridge for general n in the divisible case** (Phase 3 r_found_1
breakthrough, added 2026-05-24): when `o % 2^m = 0`, both sides equal 1
for all n. Combines `OF_post_step_div_general` and `mathlib_dens_div_general`. -/
theorem mathlib_OF_post_step_nat_eq_OF_post_step_div_general
    (n o m : Nat) (h_mod : o % (2^m) = 0) :
    mathlib_OF_post_step_nat n o m = OF_post_step n o m := by
  unfold mathlib_OF_post_step_nat
  have h_spec := mathlib_OF_post_step_spec n o m
  have h_cast : (((o : ℝ)) / ((2^m : Nat) : ℝ)) = ((o : ℝ) / (2^m : ℝ)) := by push_cast; rfl
  have h_dens := mathlib_dens_div_general o m n h_mod
  rw [h_cast] at h_dens
  rw [h_dens] at h_spec
  have h_int : mathlib_OF_post_step n o m = 1 := by exact_mod_cast h_spec.symm
  rw [h_int, OF_post_step_div_general n o m h_mod]
  rfl

/-- **Non-boundary bridge** (added 2026-05-24, REPLACES general version per
John's design recommendation): `mathlib_OF_post_step_nat n o m = OF_post_step
n o m` whenever mathlib's CF has NOT terminated by step `(n+1)`. The boundary
case (terminated exactly at `n+1` but not at `n`) is excluded.

The boundary case was proof-engineering debt without conceptual content. For
`r_found_1`'s use, the non-boundary hypothesis is always satisfied (via
N_step + dens_eq_r_at_convs_eq_kr arguments).

Hypothesis `¬ TerminatedAt (n+1)` IMPLIES:
- `¬ TerminatedAt 0` (by terminated_stable contrapositive),
- hence `o % (2^m) ≠ 0` (non-divisibility, via nondiv_of_not_terminated_zero),
- and `¬ TerminatedAt n` (also by contrapositive), letting us apply strong. -/
theorem mathlib_OF_post_step_nat_eq_OF_post_step_nonboundary
    (n o m : Nat)
    (h_not_term : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).TerminatedAt (n+1)) :
    mathlib_OF_post_step_nat n o m = OF_post_step n o m := by
  -- Derive ¬ Terminated at 0 from h_not_term (terminated_stable contrapositive).
  have h_not_term_0 : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).TerminatedAt 0 := by
    intro h
    exact h_not_term (GenContFract.terminated_stable (by omega : 0 ≤ n+1) h)
  -- Derive o % (2^m) ≠ 0 (non-divisibility).
  have h_mod : o % (2^m) ≠ 0 := nondiv_of_not_terminated_zero o (2^m) h_not_term_0
  cases n with
  | zero =>
    -- n = 0: both sides equal 1.
    have h_spec := mathlib_OF_post_step_spec 0 o m
    rw [GenContFract.zeroth_den_eq_one] at h_spec
    have h_int : mathlib_OF_post_step 0 o m = 1 := by exact_mod_cast h_spec.symm
    unfold mathlib_OF_post_step_nat
    rw [h_int]
    rw [OF_post_step_zero]
    rfl
  | succ k =>
    -- n = k+1. Apply strong at n' = k. Need ¬ Terminated at (k+1) = n.
    -- From h_not_term (¬ Terminated at n+1) by stable contrapositive.
    have h_term_n : ¬ (GenContFract.of (((o : Nat) : ℝ) / ((2^m : Nat) : ℝ))).TerminatedAt (k+1) := by
      intro h
      exact h_not_term (GenContFract.terminated_stable (by omega : k+1 ≤ k+2) h)
    have h_2pm : 0 < (2^m : Nat) := Nat.two_pow_pos m
    have h_strong := cf_aux_full_matches_mathlib_strong o (2^m) h_2pm k h_term_n
    -- Bridge gives cf_aux's .2.2.2 = dens (k+1) in ℝ. Combine with spec → Nat equality.
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

end FormalRV.SQIRPort
