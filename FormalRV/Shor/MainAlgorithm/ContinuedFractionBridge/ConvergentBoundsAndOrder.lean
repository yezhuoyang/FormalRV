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
import FormalRV.QPE.QPE
import FormalRV.QPE.QPEAmplitude
import FormalRV.Shor.OrderFinding.Eigenstate
import FormalRV.Shor.OrderFinding.TotientLowerBound
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

end FormalRV.SQIRPort
