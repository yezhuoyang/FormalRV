import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.RelaxedBasicSetting
import FormalRV.Shor.VerifiedShor.RelaxedSetting

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
/-! ## Tick 83 — Relaxed QPE_MMI chain. -/

/-! ### Task 2 — Lower-sizing extraction lemmas from BasicSettingRelaxed. -/

theorem BasicSettingRelaxed_a_pos
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : 0 < a := h.1.1

theorem BasicSettingRelaxed_a_lt
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : a < N := h.1.2

theorem BasicSettingRelaxed_order
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) :
    FormalRV.SQIRPort.Order a r N := h.2.1

theorem BasicSettingRelaxed_Nsq_lt
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : N^2 < 2^m := h.2.2.1.1

theorem BasicSettingRelaxed_pow_le_2Nsq
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : 2^m ≤ 2 * N^2 := h.2.2.1.2

theorem BasicSettingRelaxed_N_lt_pow_n
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : N < 2^n := h.2.2.2

theorem BasicSettingRelaxed_N_le_pow_n
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : N ≤ 2^n :=
  (BasicSettingRelaxed_N_lt_pow_n h).le

theorem BasicSettingRelaxed_N_pos
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : 0 < N :=
  Nat.lt_of_lt_of_le (BasicSettingRelaxed_a_pos h) (Nat.le_of_lt (BasicSettingRelaxed_a_lt h))

/-! ### Task 3 — Relaxed qpe_semantics_measurement_eq_from_lsb. -/

theorem qpe_semantics_measurement_eq_from_lsb_relaxed
    (a r N m n anc k : Nat)
    (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_modmul : FormalRV.SQIRPort.ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (f i)) :
    FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.Framework.basis_vector (2^m)
          (FormalRV.SQIRPort.s_closest m k r))
        (FormalRV.SQIRPort.Shor_final_state m n anc f)
    = FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.Framework.basis_vector (2^m)
          (FormalRV.SQIRPort.s_closest m k r))
        (FormalRV.SQIRPort.shor_orbit_state a r N m n anc) := by
  obtain ⟨h_r_pos, h_arN, h_min⟩ := BasicSettingRelaxed_order h_basic_r
  have h_N_pos : 0 < N := BasicSettingRelaxed_N_pos h_basic_r
  have h_N_gt_one : 1 < N := by
    have := BasicSettingRelaxed_a_lt h_basic_r
    have := BasicSettingRelaxed_a_pos h_basic_r
    omega
  have h_N_lt_pow : N ≤ 2^n := BasicSettingRelaxed_N_le_pow_n h_basic_r
  have hm : 0 < m := by
    have h_Nsq_lt : N^2 < 2^m := BasicSettingRelaxed_Nsq_lt h_basic_r
    have h_Nsq_pos : 0 < N^2 := by positivity
    by_contra h
    push_neg at h
    interval_cases m
    simp at h_Nsq_lt
    omega
  have hmanc : 0 < m + (n + anc) := by omega
  have h_state_eq : FormalRV.SQIRPort.Shor_final_state m n anc f
      = FormalRV.SQIRPort.QState.cast (by rw [pow_add, pow_add, mul_assoc])
          (FormalRV.SQIRPort.shor_orbit_state a r N m n anc) := by
    show FormalRV.SQIRPort.Shor_final_state_lsb m n anc f = _
    exact FormalRV.SQIRPort.Shor_final_state_lsb_eq_shor_orbit_state
      a r N m n anc hmanc hm h_r_pos h_arN h_min h_N_gt_one h_N_lt_pow h_N_pos
      f h_modmul (fun i hi => h_wt i hi)
  rw [h_state_eq, FormalRV.SQIRPort.prob_partial_meas_cast]

/-! ### Task 5 — Relaxed QPE_MMI_correct_from_Shor_orbit_state. -/

theorem QPE_MMI_correct_from_Shor_orbit_state_relaxed
    (a r N m n anc k : Nat)
    (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (β : Fin r → Matrix (Fin (2^(n + anc))) (Fin 1) ℂ)
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (_h_mmi : FormalRV.SQIRPort.ModMulImpl a N n anc f)
    (_h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (f i))
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
    FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.Framework.basis_vector (2^m)
          (FormalRV.SQIRPort.s_closest m k r)) actual_state
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  have h_r_pos : 0 < r := (BasicSettingRelaxed_order h_basic_r).1
  have h_s_lt : FormalRV.SQIRPort.s_closest m k r < 2^m :=
    s_closest_ub_relaxed a r N m n k h_basic_r h_k_lt
  exact FormalRV.SQIRPort.QPE_MMI_correct_from_orbit_state_eq k h_k_lt h_r_pos h_s_lt
    β h_orth actual_state h_state

/-! ### Task 5 (cont.) — Relaxed QPE_MMI_correct_assuming_orbit_factorization. -/

theorem QPE_MMI_correct_assuming_orbit_factorization_relaxed
    (a r N m n anc k : Nat)
    (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_mmi : FormalRV.SQIRPort.ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (f i))
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
          ∧ (FormalRV.SQIRPort.prob_partial_meas
                (FormalRV.Framework.basis_vector (2^m)
                  (FormalRV.SQIRPort.s_closest m k r))
                (FormalRV.SQIRPort.Shor_final_state m n anc f)
              = FormalRV.SQIRPort.prob_partial_meas
                  (FormalRV.Framework.basis_vector (2^m)
                    (FormalRV.SQIRPort.s_closest m k r))
                  actual_state))) :
    FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.Framework.basis_vector (2^m)
          (FormalRV.SQIRPort.s_closest m k r))
        (FormalRV.SQIRPort.Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  obtain ⟨β, actual_state, h_orth, h_state, h_prob_eq⟩ := h_orbit_exists
  rw [h_prob_eq]
  exact QPE_MMI_correct_from_Shor_orbit_state_relaxed a r N m n anc k f β
    h_basic_r h_mmi h_wt h_k_lt h_orth actual_state h_state

/-! ### Task 4 — Relaxed QPE_MMI_correct_modulo_qpe_semantics. -/

theorem QPE_MMI_correct_modulo_qpe_semantics_relaxed
    (a r N m n anc k : Nat)
    (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_mmi : FormalRV.SQIRPort.ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_qpe_semantics :
      FormalRV.SQIRPort.prob_partial_meas
          (FormalRV.Framework.basis_vector (2^m)
            (FormalRV.SQIRPort.s_closest m k r))
          (FormalRV.SQIRPort.Shor_final_state m n anc f)
        = FormalRV.SQIRPort.prob_partial_meas
            (FormalRV.Framework.basis_vector (2^m)
              (FormalRV.SQIRPort.s_closest m k r))
            (FormalRV.SQIRPort.shor_orbit_state a r N m n anc)) :
    FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.Framework.basis_vector (2^m)
          (FormalRV.SQIRPort.s_closest m k r))
        (FormalRV.SQIRPort.Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  apply QPE_MMI_correct_assuming_orbit_factorization_relaxed a r N m n anc k f
    h_basic_r h_mmi h_wt h_k_lt
  obtain ⟨h_r_pos, h_arN, h_min⟩ := BasicSettingRelaxed_order h_basic_r
  have h_N_pos : 0 < N := BasicSettingRelaxed_N_pos h_basic_r
  have h_N_gt_one : 1 < N := by
    have := BasicSettingRelaxed_a_lt h_basic_r
    have := BasicSettingRelaxed_a_pos h_basic_r
    omega
  have h_N_lt_pow : N ≤ 2^n := BasicSettingRelaxed_N_le_pow_n h_basic_r
  refine ⟨FormalRV.SQIRPort.modmult_eigenstate_combined a r N n anc,
          FormalRV.SQIRPort.shor_orbit_state a r N m n anc, ?_, rfl, h_qpe_semantics⟩
  intros j j'
  exact FormalRV.SQIRPort.modmult_eigenstate_combined_orthonormal a r N n anc
    h_r_pos h_arN h_min h_N_gt_one h_N_lt_pow j j'

/-! ### Task 6 — Relaxed QPE_MMI_correct. -/

theorem QPE_MMI_correct_relaxed
    (a r N m n anc k : Nat)
    (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_mmi : FormalRV.SQIRPort.ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (f i))
    (h_k_lt : k < r) :
    FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.Framework.basis_vector (2^m)
          (FormalRV.SQIRPort.s_closest m k r))
        (FormalRV.SQIRPort.Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  apply QPE_MMI_correct_modulo_qpe_semantics_relaxed a r N m n anc k f
    h_basic_r h_mmi h_wt h_k_lt
  exact qpe_semantics_measurement_eq_from_lsb_relaxed a r N m n anc k f h_basic_r h_mmi h_wt

/-! ### Task 7 — Fully relaxed parametric Shor theorem.

Re-proves the body of `Shor_correct_var_conditional` with sub-lemma
calls replaced by their `_relaxed` variants. -/

theorem Shor_correct_var_relaxed
    (a r N m n anc : Nat) (u : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_modmul : FormalRV.SQIRPort.ModMulImpl a N n anc u)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (u i)) :
    FormalRV.SQIRPort.probability_of_success a r N m n anc u
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have h_a_pos : 0 < a := BasicSettingRelaxed_a_pos h_basic_r
  have h_a_lt : a < N := BasicSettingRelaxed_a_lt h_basic_r
  obtain ⟨h_r_pos, h_arN, h_min⟩ := BasicSettingRelaxed_order h_basic_r
  have h_N_pos : 0 < N := BasicSettingRelaxed_N_pos h_basic_r
  have h_r_lt_N : r < N := FormalRV.SQIRPort.Order_r_lt_N a r N h_N_pos
    ⟨h_r_pos, h_arN, h_min⟩
  have h_r_le_N : r ≤ N := Nat.le_of_lt h_r_lt_N
  have h_r_pos_R : (0 : ℝ) < r := by exact_mod_cast h_r_pos
  have h_r_ne_R : (r : ℝ) ≠ 0 := ne_of_gt h_r_pos_R
  -- The integrand
  set f : Nat → ℝ := fun x =>
      FormalRV.SQIRPort.r_found x m r a N *
        FormalRV.SQIRPort.prob_partial_meas
          (FormalRV.Framework.basis_vector (2^m) x)
          (FormalRV.SQIRPort.Shor_final_state m n anc u)
    with hf_def
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    refine mul_nonneg ?_ (FormalRV.SQIRPort.prob_partial_meas_nonneg _ _)
    unfold FormalRV.SQIRPort.r_found
    split_ifs <;> norm_num
  -- Step 1: subset+injectivity using _relaxed versions.
  have h_step1 :
      ∑ i ∈ Finset.range r, f (FormalRV.SQIRPort.s_closest m i r)
        ≤ ∑ x ∈ Finset.range (2^m), f x := by
    rw [show (∑ i ∈ Finset.range r, f (FormalRV.SQIRPort.s_closest m i r))
          = ∑ x ∈ (Finset.range r).image (fun i => FormalRV.SQIRPort.s_closest m i r), f x
            from ?_]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        rw [Finset.mem_range] at hi ⊢
        exact s_closest_ub_relaxed a r N m n i h_basic_r hi
      · intro x _ _; exact hf_nonneg x
    · rw [Finset.sum_image]
      intros i hi j hj heq
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      exact s_closest_injective_relaxed a r N m n h_basic_r i j hi hj heq
  -- Step 2: per-term bound using QPE_MMI_correct_relaxed.
  set g : Nat → ℝ := fun i =>
    (if Nat.gcd i r = 1 then (1 : ℝ) else 0) * (4 / (Real.pi^2 * (r : ℝ)))
    with hg_def
  have h_step2 :
      ∀ i ∈ Finset.range r, g i ≤ f (FormalRV.SQIRPort.s_closest m i r) := by
    intro i hi
    rw [Finset.mem_range] at hi
    show g i ≤ f (FormalRV.SQIRPort.s_closest m i r)
    by_cases hcop : Nat.gcd i r = 1
    · show (if Nat.gcd i r = 1 then (1:ℝ) else 0) * (4 / (Real.pi^2 * (r:ℝ)))
            ≤ FormalRV.SQIRPort.r_found
                (FormalRV.SQIRPort.s_closest m i r) m r a N *
                FormalRV.SQIRPort.prob_partial_meas
                  (FormalRV.Framework.basis_vector (2^m)
                    (FormalRV.SQIRPort.s_closest m i r))
                  (FormalRV.SQIRPort.Shor_final_state m n anc u)
      rw [if_pos hcop, one_mul]
      have h_rf : FormalRV.SQIRPort.r_found
          (FormalRV.SQIRPort.s_closest m i r) m r a N = 1 :=
        r_found_1_relaxed a r N m n i h_basic_r hi hcop
      rw [h_rf, one_mul]
      exact QPE_MMI_correct_relaxed a r N m n anc i u h_basic_r h_modmul h_wt hi
    · show (if Nat.gcd i r = 1 then (1:ℝ) else 0) * (4 / (Real.pi^2 * (r:ℝ)))
            ≤ f (FormalRV.SQIRPort.s_closest m i r)
      rw [if_neg hcop, zero_mul]
      exact hf_nonneg _
  -- Step 3: Σ g over [0, r) = (4/(π²·r)) · ϕ(r)
  have h_step3 :
      ∑ i ∈ Finset.range r, g i
        = (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ) := by
    show (∑ i ∈ Finset.range r,
           (if Nat.gcd i r = 1 then (1:ℝ) else 0) * (4 / (Real.pi^2 * (r:ℝ))))
          = (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ)
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    rw [Nat.totient]
    push_cast
    rw [show ((Finset.range r).filter (Nat.Coprime r)).card
          = ((Finset.range r).filter (fun i => Nat.gcd i r = 1)).card from ?_]
    · rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
          Nat.smul_one_eq_cast, Finset.filter_congr_decidable]
    · congr 1; ext i; simp [Nat.Coprime, Nat.coprime_comm]
  -- Step 4: bound by Euler totient
  have h_step4 :
      (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ)
        ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
    have h_phi : ((Nat.totient r : ℝ) / (r : ℝ))
                  ≥ Real.exp (-2) / (Nat.log2 N : ℝ)^4 :=
      FormalRV.SQIRPort.phi_n_over_n_lowerbound r N h_r_pos h_r_le_N
    have h_pi_sq : (0 : ℝ) < Real.pi^2 := pow_pos Real.pi_pos 2
    have h_rewrite :
        (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ)
          = (4 / Real.pi^2) * ((Nat.totient r : ℝ) / (r : ℝ)) := by
      field_simp
    rw [h_rewrite]
    have h_κ : FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4
              = (4 / Real.pi^2) * (Real.exp (-2) / (Nat.log2 N : ℝ)^4) := by
      unfold FormalRV.SQIRPort.κ; field_simp
    rw [h_κ]
    apply mul_le_mul_of_nonneg_left h_phi
    positivity
  unfold FormalRV.SQIRPort.probability_of_success
  calc FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4
      ≤ (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ) := h_step4
    _ = ∑ i ∈ Finset.range r, g i := h_step3.symm
    _ ≤ ∑ i ∈ Finset.range r, f (FormalRV.SQIRPort.s_closest m i r) :=
          Finset.sum_le_sum h_step2
    _ ≤ ∑ x ∈ Finset.range (2^m), f x := h_step1

end FormalRV.BQAlgo
