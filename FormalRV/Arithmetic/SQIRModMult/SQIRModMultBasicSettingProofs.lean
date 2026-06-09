import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultEncoding
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSpec
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultQStart
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultFamily
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSizing
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultAccumulatorRange

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-- `BasicSetting → BasicSettingRelaxed` (drops the upper-bound conjunct). -/
theorem BasicSettingRelaxed_of_BasicSetting
    {a r N m n : Nat} (h : FormalRV.SQIRPort.BasicSetting a r N m n) :
    BasicSettingRelaxed a r N m n := by
  obtain ⟨ha, hord, hm, hn, _⟩ := h
  exact ⟨ha, hord, hm, hn⟩

/-- **Canonical sizing**: `bits = Nat.log2 N + 1` gives `2*N ≤ 2^bits`
when `N` is a power of 2 minus 1 or smaller; we use `Nat.log2 (2*N) + 1`
as a generic choice. -/
theorem VerifiedCircuitSizing_canonical_pow2_succ
    (N : Nat) (hN : 0 < N) :
    VerifiedCircuitSizing N (Nat.log2 (2 * N) + 1) := by
  set bits := Nat.log2 (2 * N) + 1 with h_bits_def
  have h_2N_pos : 0 < 2 * N := by omega
  have h_log2_le : 2 ^ (Nat.log2 (2 * N)) ≤ 2 * N := Nat.log2_self_le (by omega)
  have h_pow_bits_ge : 2 ^ bits = 2 * 2 ^ (Nat.log2 (2 * N)) := by
    rw [h_bits_def, pow_succ]; ring
  refine ⟨?_, ?_, ?_⟩
  · omega
  · have : N ≤ 2 * N := by omega
    have h_2N_le : 2 * N ≤ 2 ^ bits := by
      rw [h_pow_bits_ge]
      have h_strict : 2 * N < 2 ^ (Nat.log2 (2 * N) + 1) := Nat.lt_log2_self
      omega
    omega
  · rw [h_pow_bits_ge]
    have h_strict : 2 * N < 2 ^ (Nat.log2 (2 * N) + 1) := Nat.lt_log2_self
    omega

/-! ## Tick 81 — Relaxed sub-lemmas (copies of original proofs with
relaxed hypothesis). -/

/-- **Relaxed s_closest_ub.** -/
theorem s_closest_ub_relaxed (a r N m n k : Nat)
    (h_basic : BasicSettingRelaxed a r N m n) (h_k_lt : k < r) :
    FormalRV.SQIRPort.s_closest m k r < 2^m := by
  obtain ⟨⟨h_a_pos, h_a_lt_N⟩, h_ord, ⟨h_Nsq_lt, _⟩, _⟩ := h_basic
  have h_r_pos : 0 < r := h_ord.1
  have h_N_pos : 0 < N := by omega
  have h_r_lt_N : r < N := FormalRV.SQIRPort.Order_r_lt_N a r N h_N_pos h_ord
  have h_N_le_Nsq : N ≤ N^2 := by nlinarith
  have h_r_lt_2m : r < 2^m := by omega
  unfold FormalRV.SQIRPort.s_closest
  rw [Nat.div_lt_iff_lt_mul h_r_pos]
  have h_k_succ : k + 1 ≤ r := h_k_lt
  have h_k_mul : (k + 1) * 2^m ≤ r * 2^m := Nat.mul_le_mul_right _ h_k_succ
  have h_r_half : r / 2 < 2^m := by omega
  have h_expand : (k + 1) * 2^m = k * 2^m + 2^m := by ring
  have h_comm : r * 2^m = 2^m * r := Nat.mul_comm _ _
  omega

/-- **Relaxed s_closest_injective** — same proof as the original, just
adjusted for the relaxed hypothesis. -/
theorem s_closest_injective_relaxed
    (a r N m n : Nat) (h_basic : BasicSettingRelaxed a r N m n) :
    ∀ i j : Nat, i < r → j < r →
      FormalRV.SQIRPort.s_closest m i r = FormalRV.SQIRPort.s_closest m j r → i = j := by
  intros i j h_i h_j h_eq
  obtain ⟨⟨h_a_pos, h_a_lt_N⟩, h_ord, ⟨h_Nsq_lt, _⟩, _⟩ := h_basic
  have h_r_pos : 0 < r := h_ord.1
  have h_N_pos : 0 < N := by omega
  have h_r_lt_N : r < N := FormalRV.SQIRPort.Order_r_lt_N a r N h_N_pos h_ord
  have h_N_le_Nsq : N ≤ N^2 := by nlinarith
  have h_r_lt_2m : r < 2^m := by omega
  unfold FormalRV.SQIRPort.s_closest at h_eq
  have h_i_div : r * ((i * 2^m + r/2) / r) + (i * 2^m + r/2) % r = i * 2^m + r/2 :=
    Nat.div_add_mod (i * 2^m + r/2) r
  have h_j_div : r * ((j * 2^m + r/2) / r) + (j * 2^m + r/2) % r = j * 2^m + r/2 :=
    Nat.div_add_mod (j * 2^m + r/2) r
  have h_i_mod_lt : (i * 2^m + r/2) % r < r := Nat.mod_lt _ h_r_pos
  have h_j_mod_lt : (j * 2^m + r/2) % r < r := Nat.mod_lt _ h_r_pos
  rw [h_eq] at h_i_div
  rcases Nat.lt_trichotomy i j with h_lt | h_eq_ij | h_gt
  · exfalso
    have h_ij_step : i * 2^m + 2^m ≤ j * 2^m := by
      have h1 : i + 1 ≤ j := h_lt
      nlinarith
    have h_rearrange : i * 2^m + (j * 2^m + r/2) % r
                       = j * 2^m + (i * 2^m + r/2) % r := by omega
    omega
  · exact h_eq_ij
  · exfalso
    have h_ij_step : j * 2^m + 2^m ≤ i * 2^m := by
      have h1 : j + 1 ≤ i := h_gt
      nlinarith
    have h_rearrange : i * 2^m + (j * 2^m + r/2) % r
                       = j * 2^m + (i * 2^m + r/2) % r := by omega
    omega

/-- **Relaxed r_found_1**: Since the existing `r_found_1` proof chain
discards the n-bound throughout, it lifts to the relaxed setting via a
constructed-BasicSetting argument with a placeholder upper bound.

Pragmatic implementation: the existing `r_found_1` works at `BasicSetting`,
which requires `2^n ≤ 2*N`.  We don't have this, but the proof
doesn't use it.  Rather than re-proving the entire chain, we use the
relaxed-from-BasicSetting bridge in reverse: state the relaxed theorem
with an extra `(h_fake : 2^n ≤ 2*N)` parameter that we discard at call
sites by NOT using this lemma when the bound is unavailable.

For the SQIR `Shor_correct_var` chain, the bound IS available (since
BasicSetting holds), so the relaxed lemma can fall through to the
existing one.  For our verified family with `bits = n + 1`, the bound
is NOT available — but we sidestep this by USING THE EXISTING
`Shor_correct_var` AT `n = bits` where BasicSetting also holds, which
is the route we've taken in Tick 80. -/
theorem r_found_1_relaxed_with_bound
    (a r N m n k : Nat) (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_2n_bound : 2 ^ n ≤ 2 * N) (h_k_lt : k < r) (h_coprime : Nat.gcd k r = 1) :
    FormalRV.SQIRPort.r_found (FormalRV.SQIRPort.s_closest m k r) m r a N = 1 := by
  obtain ⟨ha, hord, hm, hn⟩ := h_basic_r
  exact FormalRV.SQIRPort.r_found_1 a r N m n k
    ⟨ha, hord, hm, hn, h_2n_bound⟩ h_k_lt h_coprime

/-! ## Tick 81 — Relaxed Shor_correct_var_relaxed_with_bound.

The relaxed variant still threads the `2^n ≤ 2*N` upper bound through
because `r_found_1` cannot yet be fully relaxed without re-proving the
continued-fraction chain.  However, the SIGNATURE makes the upper-bound
visible as a SEPARATE hypothesis, which clarifies the obstruction. -/

/-- **Relaxed Shor_correct_var (with bound)**: takes the upper bound
explicitly so that the proof obligations are visible. -/
theorem Shor_correct_var_relaxed_with_bound
    (a r N m n anc : Nat) (u : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_2n_bound : 2 ^ n ≤ 2 * N)
    (h_modmul : FormalRV.SQIRPort.ModMulImpl a N n anc u)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (u i)) :
    FormalRV.SQIRPort.probability_of_success a r N m n anc u
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  obtain ⟨ha, hord, hm, hn⟩ := h_basic_r
  exact FormalRV.SQIRPort.Shor_correct_var a r N m n anc u
    ⟨ha, hord, hm, hn, h_2n_bound⟩ h_modmul h_wt

/-! ## Tick 81 — Final verified Shor theorem with relaxed setup.

The final theorem cleanly SEPARATES:
- `BasicSettingRelaxed a r N m bits`: the Shor mathematical setup at
  data-register size `bits`.
- `VerifiedCircuitSizing N bits`: the verified-circuit sizing
  requirements.
- A residual `2 ^ bits ≤ 2 * N` hypothesis surfaced from the
  un-relaxed-yet `r_found_1` chain.

The residual hypothesis is the EXACT obstruction documented in the
Tick 80 caveat — it forces `2^bits = 2*N` (knife-edge case) when
combined with `VerifiedCircuitSizing`.  Future ticks would relax
`r_found_1` (via continued-fraction proof restructuring) to remove
this last constraint. -/
theorem Shor_correct_with_sqir_verified_modmult_relaxed
    (a r N m bits ainv : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m bits)
    (h_bits : VerifiedCircuitSizing N bits)
    (h_2n_bound : 2 ^ bits ≤ 2 * N)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
      (sqir_modmult_rev_anc bits)
      (f_modmult_circuit_verified_bits a ainv N bits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have hbits : 1 ≤ bits := h_bits.1
  have hN : N ≤ 2^bits := h_bits.2.1
  have hN2 : 2 * N ≤ 2^bits := h_bits.2.2
  have h_a_pos : 0 < a := h_basic_r.1.1
  have h_a_lt : a < N := h_basic_r.1.2
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have h_N_ge_2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h_lt | h_ge
    · exfalso
      have hN_eq : N = 1 := by omega
      rw [hN_eq, Nat.mod_one] at h_inv
      exact absurd h_inv (by decide)
    · exact h_ge
  exact Shor_correct_var_relaxed_with_bound a r N m bits
    (sqir_modmult_rev_anc bits) (f_modmult_circuit_verified_bits a ainv N bits)
    h_basic_r h_2n_bound
    (f_modmult_circuit_verified_bits_MMI a ainv N bits hbits h_N_ge_2 hN hN2 h_inv)
    (fun i _ => f_modmult_circuit_verified_bits_uc_well_typed a ainv N bits
                  hbits hN_pos hN hN2 i)

/-! ## Tick 82 — Canonical-n bridge + relaxed continued-fraction chain.

### Key insight
Lemma conclusions that do NOT mention `n` (e.g., `r_found_1`,
`s_closest_ub`) can be invoked at ANY `n` where `BasicSetting` holds.
From `BasicSettingRelaxed a r N m bits`, we construct
`BasicSetting a r N m (Nat.log2 (2*N))` (the canonical n where the
tight upper bound holds automatically), then invoke the original
theorems. -/

/-- **Canonical-n bridge**: From `BasicSettingRelaxed` at any `bits`, we
can construct `BasicSetting` at `n_canonical = Nat.log2 (2*N)`. -/
theorem BasicSetting_at_canonical_n_of_BasicSettingRelaxed
    (a r N m bits : Nat) (h_basic_r : BasicSettingRelaxed a r N m bits) :
    FormalRV.SQIRPort.BasicSetting a r N m (Nat.log2 (2 * N)) := by
  obtain ⟨⟨h_a_pos, h_a_lt⟩, h_ord, hm, _⟩ := h_basic_r
  have hN_pos : 0 < N := by omega
  refine ⟨⟨h_a_pos, h_a_lt⟩, h_ord, hm, ?_, ?_⟩
  · -- N < 2^log2(2N): from 2*N < 2^(log2(2N)+1) = 2 * 2^log2(2N).
    have h_lt : 2 * N < 2 ^ (Nat.log2 (2 * N) + 1) := Nat.lt_log2_self
    have h_eq : 2 ^ (Nat.log2 (2 * N) + 1) = 2 * 2 ^ Nat.log2 (2 * N) := by
      rw [pow_succ]; ring
    omega
  · exact Nat.log2_self_le (by omega : 2 * N ≠ 0)

/-- **Relaxed `r_found_1`**: same conclusion as the original, but
hypothesis weakened to `BasicSettingRelaxed`.  Uses the canonical-n
bridge since the conclusion `r_found (...) = 1` does not mention `n`. -/
theorem r_found_1_relaxed (a r N m bits k : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m bits)
    (h_k_lt : k < r) (h_coprime : Nat.gcd k r = 1) :
    FormalRV.SQIRPort.r_found (FormalRV.SQIRPort.s_closest m k r) m r a N = 1 :=
  FormalRV.SQIRPort.r_found_1 a r N m (Nat.log2 (2 * N)) k
    (BasicSetting_at_canonical_n_of_BasicSettingRelaxed a r N m bits h_basic_r)
    h_k_lt h_coprime

/-! ### Blocker for full relaxation: QPE_MMI_correct's deep machinery.

The review shows that `qpe_semantics_measurement_eq_from_lsb` (PostQFT.lean:3330),
`QPE_MMI_correct_modulo_qpe_semantics` (Shor.lean:4980), and
`QPE_MMI_correct_assuming_orbit_factorization` all use only
`h_n_bounds.1.le` (= `N ≤ 2^n`) from BasicSetting — never the upper
bound `2^n ≤ 2*N`.  However, relaxing them requires re-stating each
with `BasicSettingRelaxed` and updating callers; this is a 4-6 lemma
copy-modify chain that requires modifying Shor.lean/PostQFT.lean.

The Tick 82 review confirms the mathematical relaxability of the
entire chain.  Implementing it requires either:
- modifying Shor.lean / PostQFT.lean to weaken the BasicSetting
  hypothesis everywhere (invasive);
- or duplicating ~200-300 lines of proof scaffolding in this file.

For Tick 82, we land the canonical-n bridge + `r_found_1_relaxed`
(which removes one of the residual obstructions) but the QPE_MMI
chain remains a future-tick blocker.  Status B per task spec. -/

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

/-! ### Task 8 — Final usable verified SQIR Shor theorem. -/

/-- **Fully usable verified SQIR Shor theorem** — no residual upper
bound on `2^bits` from BasicSetting. -/
theorem Shor_correct_with_sqir_verified_modmult_usable
    (a r N m bits ainv : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m bits)
    (h_sizing : VerifiedCircuitSizing N bits)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
      (sqir_modmult_rev_anc bits)
      (f_modmult_circuit_verified_bits a ainv N bits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have hbits : 1 ≤ bits := h_sizing.1
  have hN : N ≤ 2^bits := h_sizing.2.1
  have hN2 : 2 * N ≤ 2^bits := h_sizing.2.2
  have hN_pos : 0 < N := BasicSettingRelaxed_N_pos h_basic_r
  have h_N_ge_2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h_lt | h_ge
    · exfalso
      have hN_eq : N = 1 := by omega
      rw [hN_eq, Nat.mod_one] at h_inv
      exact absurd h_inv (by decide)
    · exact h_ge
  exact Shor_correct_var_relaxed a r N m bits
    (sqir_modmult_rev_anc bits) (f_modmult_circuit_verified_bits a ainv N bits)
    h_basic_r
    (f_modmult_circuit_verified_bits_MMI a ainv N bits hbits h_N_ge_2 hN hN2 h_inv)
    (fun i _ => f_modmult_circuit_verified_bits_uc_well_typed a ainv N bits
                  hbits hN_pos hN hN2 i)

/-! ### Task 9 — Canonical bits corollary. -/

/-- **Canonical-bits corollary**: bits = `Nat.log2 (2*N) + 1`. -/
theorem Shor_correct_with_sqir_verified_modmult_canonical_bits
    (a r N m ainv : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m (Nat.log2 (2*N) + 1))
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m (Nat.log2 (2*N) + 1)
      (sqir_modmult_rev_anc (Nat.log2 (2*N) + 1))
      (f_modmult_circuit_verified_bits a ainv N (Nat.log2 (2*N) + 1))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have hN_pos : 0 < N := BasicSettingRelaxed_N_pos h_basic_r
  exact Shor_correct_with_sqir_verified_modmult_usable a r N m
    (Nat.log2 (2*N) + 1) ainv h_basic_r
    (VerifiedCircuitSizing_canonical_pow2_succ N hN_pos) h_inv

/-! ## Tick 84 — Final review, alias, and Phase summary.

### Documentation: which Shor theorem to cite

The original SQIR `Shor_correct` and `Shor_correct_var` theorems
(`PostQFT.lean`) depend on the placeholder axioms
`f_modmult_circuit`, `f_modmult_circuit_MMI`, and
`f_modmult_circuit_uc_well_typed` (declared in `Shor.lean:4570-4711`).
Confirmed by `lean_verify Shor_correct` listing these axioms.

The **verified** Shor theorem to cite for the kernel-clean,
axiom-free result is one of:

- `Shor_correct_with_sqir_verified_modmult_usable`: takes
  `BasicSettingRelaxed`, `VerifiedCircuitSizing`, and the modular
  inverse hypothesis.
- `Shor_correct_with_sqir_verified_modmult_canonical_bits`: same but
  the sizing is auto-discharged at `bits = Nat.log2 (2*N) + 1`.

These theorems use the verified SQIR modular multiplier
(`f_modmult_circuit_verified_bits` → `sqir_modmult_MCP_gate`) and
NOT the placeholder `f_modmult_circuit`.  Their axiom dependency is
exactly `[propext, Classical.choice, Quot.sound]` (the standard kernel).

**Do not cite `Shor_correct` or `Shor_correct_var` as the verified
result** — they remain in the codebase for historical compatibility
but rely on placeholder axioms. -/

/-- **Verified Shor's algorithm correctness theorem (no placeholder
axioms).**  Alias for `Shor_correct_with_sqir_verified_modmult_canonical_bits`
under a name that signals its axiom-free status. -/
theorem Shor_correct_verified_no_modmult_axioms
    (a r N m ainv : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m (Nat.log2 (2*N) + 1))
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m (Nat.log2 (2*N) + 1)
      (sqir_modmult_rev_anc (Nat.log2 (2*N) + 1))
      (f_modmult_circuit_verified_bits a ainv N (Nat.log2 (2*N) + 1))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 :=
  Shor_correct_with_sqir_verified_modmult_canonical_bits a r N m ainv h_basic_r h_inv

end FormalRV.BQAlgo
