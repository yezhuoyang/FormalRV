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

end FormalRV.SQIRPort
