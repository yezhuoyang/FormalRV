import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement.RFoundExactRationalCase

namespace FormalRV.SQIRPort

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

end FormalRV.SQIRPort
