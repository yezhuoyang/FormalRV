import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement.OFPostStepNatEqualities

namespace FormalRV.SQIRPort

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

end FormalRV.SQIRPort
