import FormalRV.Shor.MainAlgorithm.QuantumAndContinuedFractions.QPEPeakBound

namespace FormalRV.SQIRPort

/-! ### Phase-3 building blocks for `r_found_1` (added 2026-05-23)

These two private lemmas establish that `s_closest m k r / 2^m` is a
sufficiently-close rational approximation of `k / r` to satisfy
Khinchin's hypothesis (`Real.exists_convs_eq_rat`), which would then
let us conclude `k/r` is a convergent of `s_closest / 2^m`. The
remaining work (slices 2, 3 per `notes/sqir-shor-axiom-closure.md`)
is bridging our `def ContinuedFraction` to mathlib's
`Real.convergent` / `GenContFract.of`. -/

/-- `s_closest m k r / 2^m` is within `1/(2·2^m)` of `k/r`.

**Proof**: With `q := s_closest m k r = (k·2^m + r/2)/r` and
`m_r := (k·2^m + r/2) % r`, we have `r·q + m_r = k·2^m + r/2` and
`m_r < r`. Casting to ℝ: `q·r - k·2^m = (r/2 : ℕ) - m_r`. The Nat
floor `(r/2 : ℕ)` satisfies `r/2 - 1 ≤ (r/2 : ℕ) ≤ r/2` (Real). With
`0 ≤ m_r ≤ r - 1`, we get `|q·r - k·2^m| ≤ r/2`. Divide through by
`2^m · r > 0` to get the stated bound. -/
theorem s_closest_close_to_k_over_r (m k r : Nat) (h_r_pos : 0 < r) :
    |(s_closest m k r : ℝ) / (2^m : ℝ) - (k : ℝ) / (r : ℝ)|
      ≤ 1 / (2 * (2^m : ℝ)) := by
  have h_r_R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h_r_pos
  have h_2m_pos : (0 : ℝ) < (2^m : ℝ) := by positivity
  unfold s_closest
  set q := (k * 2^m + r / 2) / r
  set m_r := (k * 2^m + r / 2) % r
  have h_div_nat : r * q + m_r = k * 2^m + r / 2 := Nat.div_add_mod _ _
  have h_mod_lt : m_r < r := Nat.mod_lt _ h_r_pos
  have h_half_le : ((r / 2 : Nat) : ℝ) ≤ (r : ℝ) / 2 := by
    have h_nat : (r / 2 : Nat) * 2 ≤ r := Nat.div_mul_le_self r 2
    have h_R : ((r / 2 : Nat) : ℝ) * 2 ≤ (r : ℝ) := by exact_mod_cast h_nat
    linarith
  have h_half_ge : ((r / 2 : Nat) : ℝ) ≥ (r : ℝ) / 2 - 1 := by
    have h_nat : r ≤ 2 * (r / 2) + 1 := by omega
    have h_R : (r : ℝ) ≤ 2 * ((r / 2 : Nat) : ℝ) + 1 := by exact_mod_cast h_nat
    linarith
  have h_abs_bound : |(q : ℝ) * r - (k : ℝ) * 2^m| ≤ (r : ℝ) / 2 := by
    have h_step : (r : ℝ) * q + (m_r : ℝ) = (k : ℝ) * 2^m + ((r / 2 : Nat) : ℝ) := by
      exact_mod_cast h_div_nat
    have h_diff : (q : ℝ) * r - (k : ℝ) * 2^m = ((r / 2 : Nat) : ℝ) - (m_r : ℝ) := by
      have : (r : ℝ) * q = (q : ℝ) * r := by ring
      linarith
    rw [h_diff, abs_sub_le_iff]
    have h_m_r_nonneg : (0 : ℝ) ≤ (m_r : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_m_r_lt : (m_r : ℝ) ≤ (r : ℝ) - 1 := by
      have h1 : m_r + 1 ≤ r := h_mod_lt
      have h2 : ((m_r + 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast h1
      push_cast at h2
      linarith
    exact ⟨by linarith, by linarith⟩
  have h_denom : (q : ℝ) / (2^m : ℝ) - (k : ℝ) / (r : ℝ) =
                  ((q : ℝ) * r - (k : ℝ) * 2^m) / ((2^m : ℝ) * r) := by
    field_simp
  rw [h_denom, abs_div]
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2^m : ℝ) * r)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h_abs_bound, h_2m_pos, h_r_R]

/-- The Khinchin-precondition: under `BasicSetting`, `1/(2·2^m) ≤ 1/(2·r²)`.
Together with `s_closest_close_to_k_over_r`, this gives
`|s_closest/2^m - k/r| < 1/(2r²)`, which is `Real.exists_convs_eq_rat`'s
hypothesis — establishing `k/r` is a convergent of `s_closest/2^m`. -/
theorem khinchin_precond (r N m : Nat) (h_r_pos : 0 < r)
    (h_r_lt_N : r < N) (h_Nsq_lt : N^2 < 2^m) :
    1 / (2 * (2^m : ℝ)) ≤ 1 / (2 * (r : ℝ)^2) := by
  have h_r_R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h_r_pos
  have h_Nsq_R : (N : ℝ)^2 < (2^m : ℝ) := by exact_mod_cast h_Nsq_lt
  have h_r_le_N : (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt h_r_lt_N
  have h_r_sq_lt : (r : ℝ)^2 < (2^m : ℝ) := by
    have : (r : ℝ)^2 ≤ (N : ℝ)^2 := by nlinarith
    linarith
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  linarith

/-- **Khinchin precondition fully assembled** (Phase 3, r_found_1 prep,
added 2026-05-23): under `BasicSetting`, the rational `s_closest m k r / 2^m`
approximates `k/r` strictly better than `1/(2r²)`. This is exactly the
hypothesis of mathlib's `Real.exists_convs_eq_rat` (Khinchin). Combining
`s_closest_close_to_k_over_r` (`≤ 1/(2·2^m)`) with the strict
`2^m > r²` from BasicSetting+Order_r_lt_N. -/
theorem khinchin_applies_to_s_closest
    (a r N m n k : Nat) (h_basic : BasicSetting a r N m n) (h_k_lt : k < r) :
    |(s_closest m k r : ℝ) / (2^m : ℝ) - (k : ℝ) / (r : ℝ)| < 1 / (2 * (r : ℝ)^2) := by
  obtain ⟨⟨h_a_pos, h_a_lt_N⟩, h_ord, ⟨h_Nsq_lt, _⟩, _⟩ := h_basic
  have h_r_pos : 0 < r := h_ord.1
  have h_N_pos : 0 < N := by omega
  have h_r_lt_N : r < N := Order_r_lt_N a r N h_N_pos h_ord
  have h_r_R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h_r_pos
  have h_2m_pos : (0 : ℝ) < (2^m : ℝ) := by positivity
  have h_Nsq_R : (N : ℝ)^2 < (2^m : ℝ) := by exact_mod_cast h_Nsq_lt
  have h_r_le_N : (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt h_r_lt_N
  have h_r_sq_lt : (r : ℝ)^2 < (2^m : ℝ) := by
    have : (r : ℝ)^2 ≤ (N : ℝ)^2 := by nlinarith
    linarith
  have h_bound := s_closest_close_to_k_over_r m k r h_r_pos
  have h_strict : 1 / (2 * (2^m : ℝ)) < 1 / (2 * (r : ℝ)^2) := by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    linarith
  linarith

/-- **Khinchin recovery: `k/r` is a convergent of `s_closest/2^m`** (Phase
3, r_found_1 prep, added 2026-05-23): direct application of
`Real.exists_convs_eq_rat` using `khinchin_applies_to_s_closest` as the
hypothesis. The denominator handling: `((k:ℚ)/r).den = r` when `gcd(k,r)=1`
(via `Rat.den_div_eq_of_coprime`). Now we know some convergent of mathlib's
`GenContFract.of` equals `k/r` — the cf_bridge work would translate this
to our `OF_post_step`. -/
theorem k_over_r_is_convergent
    (a r N m n k : Nat) (h_basic : BasicSetting a r N m n) (h_k_lt : k < r)
    (h_coprime : Nat.gcd k r = 1) :
    ∃ N_step, (GenContFract.of ((s_closest m k r : ℝ) / (2^m : ℝ))).convs N_step
                = (((k : ℚ) / r : ℚ) : ℝ) := by
  set q : ℚ := (k : ℚ) / r with hq_def
  have h_r_pos : 0 < r := h_basic.2.1.1
  have h_q_den : q.den = r := by
    rw [hq_def]
    have h_r_pos_Z : (0 : ℤ) < (r : ℤ) := by exact_mod_cast h_r_pos
    have h_cop : (Int.natAbs (k : ℤ)).Coprime (Int.natAbs (r : ℤ)) := by
      simp; exact h_coprime
    have h_den := Rat.den_div_eq_of_coprime h_r_pos_Z h_cop
    push_cast at h_den
    exact_mod_cast h_den
  show ∃ N_step, (GenContFract.of ((s_closest m k r : ℝ) / (2^m : ℝ))).convs N_step = (q : ℝ)
  apply Real.exists_convs_eq_rat
  rw [h_q_den]
  show |(s_closest m k r : ℝ) / (2^m : ℝ) - (q : ℝ)| < 1 / (2 * (r : ℝ)^2)
  rw [show (q : ℝ) = (k : ℝ) / r from by rw [hq_def]; push_cast; ring]
  exact khinchin_applies_to_s_closest a r N m n k h_basic h_k_lt

end FormalRV.SQIRPort
