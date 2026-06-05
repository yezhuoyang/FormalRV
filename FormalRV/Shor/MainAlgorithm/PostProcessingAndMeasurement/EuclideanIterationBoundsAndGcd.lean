import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement.EuclideanIterationFibBounds

namespace FormalRV.SQIRPort

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

end FormalRV.SQIRPort
