import FormalRV.Shor.MainAlgorithm.QuantumAndContinuedFractions.ShorStatesAndHeadlineStatements

namespace FormalRV.SQIRPort

/-! ## Bridge from `s_closest` to the analytic QPE peak bound

The Shor-specific connector between the integer-valued `s_closest`
post-processor and the abstract analytic `qpe_prob_peak_bound` from
`Framework.QPEAmplitude`. At phase `θ = k/r`, the chosen measurement
outcome `s_closest m k r` is the integer closest to `k · 2^m / r`, so
the phase discrepancy `2^m · θ - s_closest` is bounded by `1/2`. This
makes `qpe_prob_peak_bound` directly applicable, yielding `qpe_prob ≥ 4/π²`. -/

/-- **Closest-integer property of `s_closest`** (added 2026-05-24):
the QPE phase discrepancy at `θ = k/r` and outcome `s_closest m k r` is
bounded by `1/2`. Combinatorial Nat fact: `s_closest m k r = (k·2^m + r/2)/r`
(Nat div), so `r · s_closest = k·2^m + (r/2:ℕ) - R` with `R = (k·2^m + r/2)
% r ∈ [0, r)`. Hence `k·2^m / r - s_closest = (R - (r/2:ℕ)) / r`, and
since `(r/2:ℕ) ∈ {(r-1)/2, r/2}` and `R ≤ r - 1`, the numerator's
absolute value is bounded by `r/2`. -/
theorem qpe_phase_discrepancy_s_closest_le_half
    (m k r : Nat) (h_r_pos : 0 < r) :
    |FormalRV.Framework.qpe_phase_discrepancy m (s_closest m k r)
        ((k : ℝ) / (r : ℝ))| ≤ 1 / 2 := by
  unfold FormalRV.Framework.qpe_phase_discrepancy s_closest
  set K : ℕ := k * 2^m with h_K_def
  set S : ℕ := (K + r/2) / r with h_S_def
  set R : ℕ := (K + r/2) % r with h_R_def
  -- Nat side: the round-to-nearest divmod facts.
  have h_R_lt : R < r := Nat.mod_lt _ h_r_pos
  have h_R_le : R + 1 ≤ r := h_R_lt
  have h_div_mod : r * S + R = K + r/2 := Nat.div_add_mod _ _
  have h_r_div_2_le : 2 * (r/2) ≤ r := by omega
  have h_r_div_2_ge : r ≤ 2 * (r/2) + 1 := by omega
  -- Real-cast versions.
  have h_r_pos_R : (0 : ℝ) < r := by exact_mod_cast h_r_pos
  have h_div_mod_R : (r : ℝ) * S + R = K + (r/2 : ℕ) := by exact_mod_cast h_div_mod
  have h_R_le_R : (R : ℝ) + 1 ≤ r := by exact_mod_cast h_R_le
  have h_R_nn : (0 : ℝ) ≤ R := by exact_mod_cast (Nat.zero_le _)
  have h_2div2_le_R : 2 * ((r/2 : ℕ) : ℝ) ≤ r := by exact_mod_cast h_r_div_2_le
  have h_2div2_ge_R : (r : ℝ) ≤ 2 * ((r/2 : ℕ) : ℝ) + 1 := by exact_mod_cast h_r_div_2_ge
  -- Express 2^m · (k/r) - S as (R - (r/2:ℕ)) / r using the divmod identity.
  have h_eq : (2 : ℝ)^m * ((k : ℝ) / r) - (S : ℝ)
            = ((R : ℝ) - ((r/2 : ℕ) : ℝ)) / r := by
    have h_K_real : (K : ℝ) = (k : ℝ) * (2 : ℝ)^m := by
      show ((k * 2^m : ℕ) : ℝ) = (k : ℝ) * (2 : ℝ)^m
      push_cast; ring
    field_simp
    linarith
  rw [h_eq, abs_div, abs_of_pos h_r_pos_R, div_le_iff₀ h_r_pos_R, abs_le]
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-- **Shor-specific QPE peak bound**: the ideal-amplitude probability at
outcome `s_closest m k r` for true phase `k/r` satisfies `qpe_prob ≥
4/π²`. Combines `qpe_phase_discrepancy_s_closest_le_half` (closest-
integer property) with the analytic `qpe_prob_peak_bound` from
`Framework.QPEAmplitude`. -/
theorem qpe_prob_at_s_closest_ge
    (m k r : Nat) (h_r_pos : 0 < r) :
    FormalRV.Framework.qpe_prob m (s_closest m k r) ((k : ℝ) / (r : ℝ))
      ≥ 4 / Real.pi ^ 2 :=
  FormalRV.Framework.qpe_prob_peak_bound m _ _
    (qpe_phase_discrepancy_s_closest_le_half m k r h_r_pos)

-- The `QPE_MMI_correct` axiom was DELETED on 2026-05-27 and replaced
-- by a theorem of the same name in `PostQFT.lean`. The replacement
-- chains through `QPE_MMI_correct_modulo_qpe_semantics` (proved here in
-- Shor.lean) + the LSB-pipeline state equality
-- `Shor_final_state_lsb_eq_shor_orbit_state` (proved in PostQFT.lean).
-- The proof is enabled by the design change to `Shor_final_state`,
-- which now uses `QPE_var_lsb` (the LSB-compatible QPE wrapper).
-- `Shor_correct_var` and `Shor_correct` are now also defined in
-- PostQFT.lean for the same reason.

/-- **`QPE_MMI_correct_conditional`** (added 2026-05-24): the
kernel-clean form of the QPE+modular-multiplication peak bound,
parameterized by a hypothesis-form QPE-MMI peak statement. Mirrors
the `Shor_correct_var_conditional` pattern: the deep external
obligation enters as an explicit universally-quantified argument,
so this theorem's own axiom dependence is the standard kernel only.

**Mathematical content hidden in the axiom.** The full proof in SQIR
(`QPEGeneral.v` + `Shor.v:861`) decomposes into three layers:

1. **QPE circuit semantics** (`Framework.QPE.QPE_semantics_full` shape):
   For any unitary `U` with eigenstate `|ψ⟩` at eigenvalue `exp(2πi·θ)`,
   the QPE circuit on `|0⟩_m ⊗ |ψ⟩` produces a state of the form
   `(∑_y α_y(θ) |y⟩) ⊗ |ψ⟩`, with the amplitudes `α_y(θ)` given
   explicitly by the inverse-QFT Dirichlet kernel.

2. **Modular-multiplication eigenstate decomposition** (orbit-state
   construction): the data-register input `|1⟩_n` decomposes as
   `(1/√r) · ∑_{k<r} |ψ_k⟩`, where each `|ψ_k⟩` is a joint eigenstate
   of all the powers `f i = U_a^{2^i}` with eigenvalue
   `exp(2πi · k · 2^i / r)` (the standard orbit-state construction
   from the cyclic action of multiplication-by-`a` mod `N`).

3. **Analytic QPE peak bound** (Dirichlet-kernel arithmetic):
   for `θ` within `1/2^(m+1)` of `k/r`, the amplitude
   `α_{s_closest m k r}(θ)` has squared magnitude `≥ 4/π²`.

Combining (1) × (2) × (3): linearity of `uc_eval` over the sum in
(2), per-component QPE semantics from (1), Born's-rule partial
measurement (`prob_partial_meas` def), orthogonality of distinct
`|ψ_k⟩` to drop cross-terms, then the peak bound (3) on the
diagonal component. The combined factor `(1/r) · (4/π²) = 4/(π²·r)`
matches the conclusion.

The combination proof requires Hilbert-space linear-algebra
infrastructure not yet in `Framework.QuantumLib` (vector-space
linearity of `uc_eval` over arbitrary sums, partial-measurement on
sums of states, joint-eigenstate sum projection); each is multi-tick
on its own. Once that infrastructure exists, this conditional can
be restated with the three layer-hypotheses separately and proved
by combining them. -/
theorem QPE_MMI_correct_conditional
    (a r N m n anc k : Nat) (f : Nat → BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_mmi : ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_QPE_MMI_peak :
      ∀ (a' r' N' m' n' anc' k' : Nat) (f' : Nat → BaseUCom (n' + anc')),
        BasicSetting a' r' N' m' n' →
        ModMulImpl a' N' n' anc' f' →
        (∀ i, i < m' → uc_well_typed (f' i)) →
        k' < r' →
        prob_partial_meas (basis_vector (2^m') (s_closest m' k' r'))
            (Shor_final_state m' n' anc' f')
          ≥ 4 / (Real.pi^2 * (r' : ℝ))) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) :=
  h_QPE_MMI_peak a r N m n anc k f h_basic h_mmi h_wt h_k_lt

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

/-- **Denominators of `GenContFract.of v` are integer-valued** (paired
form, Phase 3 r_found_1 slice 4b sub-step 1, added 2026-05-23): joint
induction giving `∃ d : ℤ, dens n = d ∧ ∃ d', dens (n+1) = d'` for all
`n`. The base cases use `zeroth_den_eq_one` and either
`first_den_eq` (if not terminated at 0) or `dens_stable_of_terminated`
(if terminated at 0). The inductive step uses `dens_recurrence` for the
non-terminated case (since `GenContFract.of` has partial-numerator 1 by
`of_partNum_eq_one_and_exists_int_partDen_eq`, the recurrence specializes
to `dens(n+2) = b·dens(n+1) + dens(n)` with `b` integer-valued). -/
theorem dens_int_valued_pair (v : ℝ) :
    ∀ n, (∃ d : ℤ, (GenContFract.of v).dens n = (d : ℝ)) ∧
         (∃ d : ℤ, (GenContFract.of v).dens (n+1) = (d : ℝ)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨⟨1, ?_⟩, ?_⟩
    · simp [GenContFract.zeroth_den_eq_one]
    · by_cases h : (GenContFract.of v).s.get? 0 = none
      · refine ⟨1, ?_⟩
        have h_term : (GenContFract.of v).TerminatedAt 0 := h
        rw [GenContFract.dens_stable_of_terminated (n := 0) (m := 1) (by omega) h_term]
        simp [GenContFract.zeroth_den_eq_one]
      · have h' : ∃ gp, (GenContFract.of v).s.get? 0 = some gp := by
          rcases hopt : (GenContFract.of v).s.get? 0 with _ | gp
          · exact absurd hopt h
          · exact ⟨gp, rfl⟩
        obtain ⟨gp, hgp⟩ := h'
        rw [GenContFract.first_den_eq hgp]
        obtain ⟨_, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp
        exact ⟨z, hz⟩
  | succ k ih =>
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    refine ⟨⟨b, hb⟩, ?_⟩
    by_cases h : (GenContFract.of v).s.get? (k+1) = none
    · refine ⟨b, ?_⟩
      have h_term : (GenContFract.of v).TerminatedAt (k+1) := h
      rw [GenContFract.dens_stable_of_terminated (n := k+1) (m := k+2) (by omega) h_term]
      exact hb
    · have h' : ∃ gp, (GenContFract.of v).s.get? (k+1) = some gp := by
        rcases hopt : (GenContFract.of v).s.get? (k+1) with _ | gp
        · exact absurd hopt h
        · exact ⟨gp, rfl⟩
      obtain ⟨gp, hgp⟩ := h'
      have h_rec := GenContFract.dens_recurrence (g := GenContFract.of v) (n := k)
        hgp ha hb
      obtain ⟨ha_eq, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp
      refine ⟨z * b + a, ?_⟩
      show (GenContFract.of v).dens (k + 1 + 1) = _
      rw [show k + 1 + 1 = k + 2 from rfl]
      rw [h_rec, ha_eq, hz]
      push_cast
      ring

/-- Single-`n` corollary: `dens n` of `GenContFract.of v` is integer-valued. -/
theorem dens_int_valued (v : ℝ) (n : Nat) :
    ∃ d : ℤ, (GenContFract.of v).dens n = (d : ℝ) :=
  (dens_int_valued_pair v n).1

/-- **Numerators of `GenContFract.of v` are integer-valued** (paired
form, Phase 3 r_found_1 slice 4b sub-step 2, added 2026-05-23): analogous
to `dens_int_valued_pair`. The base case n=0 uses
`zeroth_num_eq_h` + `of_h_eq_floor` (so `nums 0 = ⌊v⌋`); the n=1
non-terminated case uses `first_num_eq` (giving `nums 1 = b·h + 1`); the
inductive step uses `nums_recurrence` with `a = 1` from
`of_partNum_eq_one_and_exists_int_partDen_eq`. -/
theorem nums_int_valued_pair (v : ℝ) :
    ∀ n, (∃ d : ℤ, (GenContFract.of v).nums n = (d : ℝ)) ∧
         (∃ d : ℤ, (GenContFract.of v).nums (n+1) = (d : ℝ)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨⟨⌊v⌋, ?_⟩, ?_⟩
    · rw [GenContFract.zeroth_num_eq_h, GenContFract.of_h_eq_floor]
    · by_cases h : (GenContFract.of v).s.get? 0 = none
      · refine ⟨⌊v⌋, ?_⟩
        have h_term : (GenContFract.of v).TerminatedAt 0 := h
        rw [GenContFract.nums_stable_of_terminated (n := 0) (m := 1) (by omega) h_term]
        rw [GenContFract.zeroth_num_eq_h, GenContFract.of_h_eq_floor]
      · have h' : ∃ gp, (GenContFract.of v).s.get? 0 = some gp := by
          rcases hopt : (GenContFract.of v).s.get? 0 with _ | gp
          · exact absurd hopt h
          · exact ⟨gp, rfl⟩
        obtain ⟨gp, hgp⟩ := h'
        rw [GenContFract.first_num_eq hgp]
        obtain ⟨ha_eq, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp
        refine ⟨z * ⌊v⌋ + 1, ?_⟩
        rw [ha_eq, hz, GenContFract.of_h_eq_floor]
        push_cast; ring
  | succ k ih =>
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    refine ⟨⟨b, hb⟩, ?_⟩
    by_cases h : (GenContFract.of v).s.get? (k+1) = none
    · refine ⟨b, ?_⟩
      have h_term : (GenContFract.of v).TerminatedAt (k+1) := h
      rw [GenContFract.nums_stable_of_terminated (n := k+1) (m := k+2) (by omega) h_term]
      exact hb
    · have h' : ∃ gp, (GenContFract.of v).s.get? (k+1) = some gp := by
        rcases hopt : (GenContFract.of v).s.get? (k+1) with _ | gp
        · exact absurd hopt h
        · exact ⟨gp, rfl⟩
      obtain ⟨gp, hgp⟩ := h'
      have h_rec := GenContFract.nums_recurrence (g := GenContFract.of v) (n := k)
        hgp ha hb
      obtain ⟨ha_eq, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp
      refine ⟨z * b + a, ?_⟩
      show (GenContFract.of v).nums (k + 1 + 1) = _
      rw [show k + 1 + 1 = k + 2 from rfl]
      rw [h_rec, ha_eq, hz]
      push_cast; ring

/-- Single-`n` corollary: `nums n` of `GenContFract.of v` is integer-valued. -/
theorem nums_int_valued (v : ℝ) (n : Nat) :
    ∃ d : ℤ, (GenContFract.of v).nums n = (d : ℝ) :=
  (nums_int_valued_pair v n).1

/-- **Determinant identity for `GenContFract.of v`** (Phase 3, r_found_1
slice 4b prep, added 2026-05-23): the standard Bezout-like determinant
identity `p_n q_{n+1} - q_n p_{n+1} = (-1)^(n+1)` for the convergents of
`GenContFract.of v`. Re-stated from mathlib's `SimpContFract.determinant`
via the `SimpContFract.of` packaging — `(SimpContFract.of v : GenContFract)
= GenContFract.of v` definitionally. This is what gives gcd(p_n, q_n) = 1
as integers (modulo upgrading int-valuedness; future tick). -/
theorem of_v_determinant (v : ℝ) (n : Nat)
    (h_not_term : ¬ (GenContFract.of v).TerminatedAt n) :
    (GenContFract.of v).nums n * (GenContFract.of v).dens (n+1)
      - (GenContFract.of v).dens n * (GenContFract.of v).nums (n+1)
        = (-1) ^ (n+1) := by
  let s : SimpContFract ℝ := SimpContFract.of v
  have h_eq : (s : GenContFract ℝ) = GenContFract.of v := rfl
  have h_det := SimpContFract.determinant (s := s) (n := n)
    (by rw [h_eq]; exact h_not_term)
  rw [h_eq] at h_det
  exact h_det

/-- **Coprimality of integer-valued numerators and denominators** (Phase 3
r_found_1 slice 4b sub-step 2b, added 2026-05-23): for `GenContFract.of v`
at any non-terminated step `n`, if `nums n = (a : ℝ)` and `dens n = (b : ℝ)`
with `a b : ℤ`, then `Int.gcd a b = 1`. Proof: extract integer-valued
`a' = nums (n+1)`, `b' = dens (n+1)` (via `nums_int_valued` /
`dens_int_valued`), apply `of_v_determinant` (Bezout-like identity
`a·b' - b·a' = (-1)^(n+1)`), cast to ℤ, then case-split on parity of `n+1`:
either way yields a Bezout combination summing to 1, so `Int.gcd a b ∣ 1`
by `Int.gcd_dvd_iff`. -/
theorem of_v_nums_dens_coprime (v : ℝ) (n : Nat)
    (h_not_term : ¬ (GenContFract.of v).TerminatedAt n)
    (a b : ℤ) (ha : (GenContFract.of v).nums n = (a : ℝ))
    (hb : (GenContFract.of v).dens n = (b : ℝ)) :
    Int.gcd a b = 1 := by
  obtain ⟨a', ha'⟩ := nums_int_valued v (n+1)
  obtain ⟨b', hb'⟩ := dens_int_valued v (n+1)
  have h_det := of_v_determinant v n h_not_term
  rw [ha, hb, ha', hb'] at h_det
  have h_int : a * b' - b * a' = (-1) ^ (n + 1) := by
    have h_cast : ((a * b' - b * a' : ℤ) : ℝ) = (((-1 : ℤ) ^ (n + 1) : ℤ) : ℝ) := by
      push_cast
      convert h_det using 1
    exact_mod_cast h_cast
  rcases (Nat.even_or_odd (n+1)) with hev | hod
  · have h_pow : ((-1 : ℤ) ^ (n + 1)) = 1 := Even.neg_one_pow hev
    rw [h_pow] at h_int
    have h2 : a * b' + b * (-a') = 1 := by linarith
    have hdiv : Int.gcd a b ∣ 1 :=
      Int.gcd_dvd_iff.mpr ⟨b', -a', by exact_mod_cast h2.symm⟩
    exact Nat.eq_one_of_dvd_one hdiv
  · have h_pow : ((-1 : ℤ) ^ (n + 1)) = -1 := Odd.neg_one_pow hod
    rw [h_pow] at h_int
    have h2 : a * (-b') + b * a' = 1 := by linarith
    have hdiv : Int.gcd a b ∣ 1 :=
      Int.gcd_dvd_iff.mpr ⟨-b', a', by exact_mod_cast h2.symm⟩
    exact Nat.eq_one_of_dvd_one hdiv

end FormalRV.SQIRPort
