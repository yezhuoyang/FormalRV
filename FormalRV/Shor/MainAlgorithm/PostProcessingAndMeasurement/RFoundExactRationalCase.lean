import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement.EuclideanIterationBoundsAndGcd


namespace FormalRV.SQIRPort

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

end FormalRV.SQIRPort
