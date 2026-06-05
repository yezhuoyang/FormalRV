import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement.PartialMeasurementOrthogonalSum

namespace FormalRV.SQIRPort

/-- **`QPE_MMI_correct_from_orbit`** (added 2026-05-24): state-
factorization conditional form of `QPE_MMI_correct`. Given an
orthonormal eigenstate family `β j` (for the unmeasured register) and
the orbit-state superposition shape

  `(1/√r) · ∑ j_idx : Fin r,
     (qpe_phase_state m (j_idx/r)) ⊗ (β j_idx)`

for the joint output state, the QPE peak bound `≥ 4/(π²·r)` at outcome
`s_closest m k r` follows. Closes the analytic half of the
`QPE_MMI_correct` axiom; the remaining (semantic / circuit) half is
showing that `Shor_final_state m n anc f` actually has this form,
which requires the circuit semantics of `QPE_var` plus the modular
multiplier's eigenstate spectrum (deferred to Phase 4).

Kernel-clean: depends on `prob_partial_meas_qpe_orth_sum` (the
`(1/r)`-factored partial-meas bridge), `qpe_prob_at_s_closest_ge`
(the analytic `4/π²` peak bound at the matching `k/r` term), and
basic real arithmetic. -/
theorem QPE_MMI_correct_from_orbit
    {m q r : Nat} (k : Nat) (h_k_lt : k < r) (h_r_pos : 0 < r)
    (h_s_lt : s_closest m k r < 2^m)
    (β : Fin r → Matrix (Fin (2^q)) (Fin 1) ℂ)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (fun i j => (1 / (Real.sqrt r : ℂ)) *
          ((∑ j_idx : Fin r,
             FormalRV.Framework.kron_vec
               (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
               (β j_idx) :
             Matrix (Fin (2^(m + q))) (Fin 1) ℂ) i j))
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  rw [prob_partial_meas_qpe_orth_sum (s_closest m k r) h_s_lt h_r_pos
        (fun j_idx => ((j_idx.val : ℝ) / r)) β h_orth]
  have h_r_pos_R : (0 : ℝ) < r := by exact_mod_cast h_r_pos
  have h_simp : (1 / (r : ℝ)) * (4 / Real.pi^2) = 4 / (Real.pi^2 * r) := by
    field_simp
  -- Sum is bounded below by the j_idx = ⟨k, h_k_lt⟩ term, which is ≥ 4/π².
  have h_sum_ge : (4 / Real.pi^2 : ℝ)
      ≤ ∑ j_idx : Fin r,
          FormalRV.Framework.qpe_prob m (s_closest m k r)
                                        ((j_idx.val : ℝ) / r) := by
    have h_term : (4 / Real.pi^2 : ℝ)
        ≤ FormalRV.Framework.qpe_prob m (s_closest m k r) ((k : ℝ) / r) :=
      qpe_prob_at_s_closest_ge m k r h_r_pos
    set g : Fin r → ℝ := fun j_idx =>
        FormalRV.Framework.qpe_prob m (s_closest m k r) ((j_idx.val : ℝ) / r) with hg
    have h_g_nonneg : ∀ j_idx ∈ Finset.univ, 0 ≤ g j_idx :=
      fun _ _ => FormalRV.Framework.qpe_prob_nonneg _ _ _
    have h_single : g ⟨k, h_k_lt⟩ ≤ ∑ j_idx, g j_idx :=
      Finset.single_le_sum h_g_nonneg (Finset.mem_univ _)
    have h_g_k : g ⟨k, h_k_lt⟩ = FormalRV.Framework.qpe_prob m (s_closest m k r) ((k : ℝ) / r) := rfl
    rw [h_g_k] at h_single
    linarith
  have h_lhs_ge : (1 / (r : ℝ)) * (4 / Real.pi^2)
                ≤ (1 / (r : ℝ)) * ∑ j_idx : Fin r,
                    FormalRV.Framework.qpe_prob m (s_closest m k r)
                                                  ((j_idx.val : ℝ) / r) :=
    mul_le_mul_of_nonneg_left h_sum_ge (by positivity)
  linarith

/-- **`QPE_MMI_correct_from_orbit_state_eq`** (added 2026-05-24):
the state-equality form of `QPE_MMI_correct_from_orbit`. Given an
`actual_state` at the natural `Matrix (Fin (2^(m+q))) (Fin 1) ℂ`
type and an equality hypothesis showing that this state is exactly
the orbit-superposition form, the QPE peak bound follows.

This is the cleanest "factor the QPE_MMI_correct axiom through a
state-equality hypothesis" theorem. To recover the public
`QPE_MMI_correct` shape, the remaining work is a separate equality
theorem:

  `Shor_final_state m n anc f = (orbit-superposition state)`

(possibly with a `QState.cast` for the dimension `2^m · 2^n · 2^anc`
vs `2^(m + (n + anc))` mismatch). That equality is the genuine
SQIR/`QPEGeneral.v` semantic obligation; this conditional theorem
closes everything downstream of it. -/
theorem QPE_MMI_correct_from_orbit_state_eq
    {m q r : Nat} (k : Nat) (h_k_lt : k < r) (h_r_pos : 0 < r)
    (h_s_lt : s_closest m k r < 2^m)
    (β : Fin r → Matrix (Fin (2^q)) (Fin 1) ℂ)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^q), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0)
    (actual_state : Matrix (Fin (2^(m + q))) (Fin 1) ℂ)
    (h_state : actual_state =
      fun i j => (1 / (Real.sqrt r : ℂ)) *
        ((∑ j_idx : Fin r,
           FormalRV.Framework.kron_vec
             (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
             (β j_idx) :
           Matrix (Fin (2^(m + q))) (Fin 1) ℂ) i j)) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r)) actual_state
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  rw [h_state]
  exact QPE_MMI_correct_from_orbit k h_k_lt h_r_pos h_s_lt β h_orth

/-- **`QPE_MMI_correct_from_Shor_orbit_state`** (added 2026-05-24):
the Shor-shaped wrapper around `QPE_MMI_correct_from_orbit_state_eq`.
Takes the Shor-specific parameters and `BasicSetting`/`ModMulImpl`/
well-typed hypotheses (mirroring `QPE_MMI_correct`'s signature), plus
an explicit state-equality hypothesis showing the joint output state
is the orbit superposition. Derives `0 < r` from `BasicSetting`'s
`Order` field and `s_closest m k r < 2^m` from the existing
`s_closest_ub` helper, then dispatches to
`QPE_MMI_correct_from_orbit_state_eq`.

The conclusion is stated on `actual_state` (not directly on
`Shor_final_state`) to avoid the `QState (2^m * 2^n * 2^anc)` vs
`Matrix (Fin (2^(m + (n + anc))))` dimensional cast — a future tick
can bridge `actual_state` and `Shor_final_state` via `QState.cast` in
a separate equality theorem. The current theorem isolates the QPE-
bound content from that cast bookkeeping.

The `_h_mmi` / `_h_wt` arguments are unused in the proof but kept in
the signature to mirror the public `QPE_MMI_correct`'s shape exactly,
making the final substitution into the full Shor chain mechanical
once the state-factorization equality lands. -/
theorem QPE_MMI_correct_from_Shor_orbit_state
    (a r N m n anc k : Nat)
    (f : Nat → BaseUCom (n + anc))
    (β : Fin r → Matrix (Fin (2^(n + anc))) (Fin 1) ℂ)
    (h_basic : BasicSetting a r N m n)
    (_h_mmi : ModMulImpl a N n anc f)
    (_h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^(n + anc)), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0)
    (actual_state : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ)
    (h_state : actual_state =
      fun i j => (1 / (Real.sqrt r : ℂ)) *
        ((∑ j_idx : Fin r,
           FormalRV.Framework.kron_vec
             (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
             (β j_idx) :
           Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ) i j)) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r)) actual_state
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  have h_r_pos : 0 < r := h_basic.2.1.1
  have h_s_lt : s_closest m k r < 2^m :=
    s_closest_ub a r N m n k h_basic h_k_lt
  exact QPE_MMI_correct_from_orbit_state_eq k h_k_lt h_r_pos h_s_lt
    β h_orth actual_state h_state

/-- **`QPE_MMI_correct_assuming_orbit_factorization`** (added
2026-05-24): the maximal closure of the QPE_MMI_correct axiom that
this codebase currently supports.

Replaces the entire QPE semantic chain with a SINGLE existential
hypothesis `h_orbit_exists`: "there exist orthonormal eigenstates β
and an orbit-form state whose partial-measurement probability matches
`Shor_final_state`'s." Given this hypothesis, the QPE peak bound
follows from the kernel-clean conditional chain
(`QPE_MMI_correct_from_Shor_orbit_state` ∘
`QPE_MMI_correct_from_orbit_state_eq` ∘
`QPE_MMI_correct_from_orbit` ∘ `prob_partial_meas_qpe_orth_sum` ∘
`qpe_prob_peak_bound`) — no axiom is needed downstream of the
existential.

**This theorem cannot replace the `QPE_MMI_correct` axiom directly**
because the existential `h_orbit_exists` is genuinely deep: it
unfolds into the modular-multiplier eigenstate construction +
`QPE_var` circuit semantics, both Phase-4 obligations needing
multi-file infrastructure that does not yet exist in
`Framework.QuantumLib` (linearity of `uc_eval` over arbitrary state
sums, partial-trace machinery, the spectral theorem for unitary
matrices applied to the modular multiplier, etc.).

What this theorem DOES accomplish:
- It witnesses that the analytic / counting / averaging content of
  `QPE_MMI_correct` is fully Lean-proved.
- It pinpoints the EXACT remaining semantic obligation in a single
  named existential hypothesis.
- Replacing this single existential with a theorem-form derivation
  (the Phase-4 work) is sufficient to close the entire QPE chain.

Kernel-clean: `[propext, Classical.choice, Quot.sound]` only. -/
theorem QPE_MMI_correct_assuming_orbit_factorization
    (a r N m n anc k : Nat) (f : Nat → BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_mmi : ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_orbit_exists :
        ∃ (β : Fin r → Matrix (Fin (2^(n + anc))) (Fin 1) ℂ)
          (actual_state : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ),
          ((∀ j j' : Fin r,
             ∑ y : Fin (2^(n + anc)),
                  starRingEnd ℂ ((β j') y 0) * (β j) y 0
             = if j = j' then (1 : ℂ) else 0)
          ∧ (actual_state = fun i j => (1 / (Real.sqrt r : ℂ)) *
              ((∑ j_idx : Fin r,
                 FormalRV.Framework.kron_vec
                   (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
                   (β j_idx) :
                 Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ) i j))
          ∧ (prob_partial_meas (basis_vector (2^m) (s_closest m k r))
                (Shor_final_state m n anc f)
              = prob_partial_meas (basis_vector (2^m) (s_closest m k r))
                                  actual_state))) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  obtain ⟨β, actual_state, h_orth, h_state, h_prob_eq⟩ := h_orbit_exists
  rw [h_prob_eq]
  exact QPE_MMI_correct_from_Shor_orbit_state a r N m n anc k f β
    h_basic h_mmi h_wt h_k_lt h_orth actual_state h_state

end FormalRV.SQIRPort
