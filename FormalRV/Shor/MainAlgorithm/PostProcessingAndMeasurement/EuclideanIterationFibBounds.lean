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

end FormalRV.SQIRPort
