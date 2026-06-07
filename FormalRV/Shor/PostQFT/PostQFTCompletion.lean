import FormalRV.QPE.PhaseKickback
import FormalRV.QPE.QPEAmplitude
import FormalRV.QFT.IQFTDefinitions
import FormalRV.QFT.IQFTRecursiveArbitrary

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-- **QPE_var_lsb action on the kron(|0⟩_m, (1/√r)·∑_k β_k) input.**
The linearity-and-eigenstate step: applying `uc_eval (QPE_var_lsb)` to
the kron of `|0⟩_m` with a `(1/√r)`-weighted sum of modmult eigenstates
yields the corresponding `(1/√r)`-weighted sum of
`qpe_phase_state m (k/r) ⊗ ψ_k`. Combines `kron_vec_smul_right` +
`kron_vec_sum_right` + `Matrix.mul_smul` + `Matrix.mul_sum` +
`QPE_var_lsb_on_modmult_eigenstate`. -/
theorem QPE_var_lsb_on_orbit_sum
    (a r N : Nat) {m n anc : Nat}
    (hmanc : 0 < m + (n + anc)) (hm : 0 < m)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1) (h_N_pos : 0 < N)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped (n + anc) (f i)) :
    FormalRV.Framework.uc_eval (QPE_var_lsb m (n + anc) f)
      * kron_vec (FormalRV.Framework.kron_zeros m)
          ((1 / (Real.sqrt r : ℂ)) •
            ∑ k : Fin r, modmult_eigenstate_combined a r N n anc k)
    = (1 / (Real.sqrt r : ℂ)) •
        ∑ k : Fin r,
          kron_vec (qpe_phase_state m ((k.val : ℝ) / (r : ℝ)))
                   (modmult_eigenstate_combined a r N n anc k) := by
  rw [kron_vec_smul_right, kron_vec_sum_right]
  rw [Matrix.mul_smul, Matrix.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact QPE_var_lsb_on_modmult_eigenstate a r N k hmanc hm h_r_pos h_arN h_N_pos
    f h_modmul h_wt_all

/-- **HEADLINE: pre-cast Shor state equality (LSB pipeline).** The
right-associated `kron_vec (kron_zeros m) (kron_vec |1⟩_n |0⟩_anc)`
input — which equals `Shor_initial_state` modulo the `Nat.add_assoc`
cast — produces `shor_orbit_state` after `uc_eval (QPE_var_lsb)`.

Proof chain (all kernel-clean atoms from prior ticks):
  `orbit_decomposition_combined_matrix` to express the data+ancilla
  part as the orbit sum →
  `QPE_var_lsb_on_orbit_sum` to apply QPE per orbit term →
  `shor_orbit_state` unfolding + pointwise match.

The follow-up theorem `Shor_final_state_lsb_eq_shor_orbit_state` adds
the `QState.cast` bookkeeping to connect with `Shor_final_state_lsb`'s
signature. -/
theorem QPE_var_lsb_on_Shor_initial_raw
    (a r N : Nat) {m n anc : Nat}
    (hmanc : 0 < m + (n + anc)) (hm : 0 < m)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1)
    (h_min : ∀ s, 0 < s → s < r → a^s % N ≠ 1)
    (h_N : 1 < N) (h_N_lt : N ≤ 2^n) (h_N_pos : 0 < N)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped (n + anc) (f i)) :
    FormalRV.Framework.uc_eval (QPE_var_lsb m (n + anc) f)
      * (kron_vec (FormalRV.Framework.kron_zeros m)
           (kron_vec (FormalRV.Framework.basis_vector (2^n) 1)
                     (FormalRV.Framework.kron_zeros anc))
          : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ)
    = shor_orbit_state a r N m n anc := by
  rw [orbit_decomposition_combined_matrix a r N n anc h_r_pos h_arN h_min h_N h_N_lt]
  rw [QPE_var_lsb_on_orbit_sum a r N hmanc hm h_r_pos h_arN h_N_pos f h_modmul h_wt_all]
  unfold shor_orbit_state
  ext i col
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]

/-- **`kron_vec` associativity** modulo the `Nat.add_assoc` cast.
`QState.cast (Nat.add_assoc) (kron(kron x y, z)) = kron x (kron y z)`
(at dim `2^(a+(b+c))`). Pointwise proof via division/mod arithmetic on
the index decomposition (`kron_vec_high` / `kron_vec_low` chains). -/
theorem kron_vec_assoc {a b c : Nat}
    (x : Matrix (Fin (2^a)) (Fin 1) ℂ)
    (y : Matrix (Fin (2^b)) (Fin 1) ℂ)
    (z : Matrix (Fin (2^c)) (Fin 1) ℂ) :
    QState.cast (by rw [Nat.add_assoc])
        (kron_vec (kron_vec x y) z : Matrix (Fin (2^((a+b)+c))) (Fin 1) ℂ)
    = (kron_vec x (kron_vec y z) : Matrix (Fin (2^(a+(b+c)))) (Fin 1) ℂ) := by
  funext i col
  show (kron_vec (kron_vec x y) z) (Fin.cast _ i) 0
      = kron_vec x (kron_vec y z) i col
  fin_cases col
  rw [kron_vec_apply, kron_vec_apply, kron_vec_apply, kron_vec_apply, mul_assoc]
  have h_cast : (Fin.cast (by rw [Nat.add_assoc] : 2^(a+(b+c)) = 2^((a+b)+c)) i).val
                  = i.val := rfl
  have h_pow_eq : (2^(b+c) : Nat) = 2^b * 2^c := by rw [pow_add]
  have h_x_idx : kron_vec_high (kron_vec_high (Fin.cast (by rw [Nat.add_assoc]
                  : 2^(a+(b+c)) = 2^((a+b)+c)) i)) = (kron_vec_high i : Fin (2^a)) := by
    apply Fin.ext
    show (Fin.cast _ i).val / 2^c / 2^b = i.val / 2^(b+c)
    rw [h_cast, Nat.div_div_eq_div_mul, mul_comm, ← pow_add]
  have h_y_idx : kron_vec_low (kron_vec_high (Fin.cast (by rw [Nat.add_assoc]
                  : 2^(a+(b+c)) = 2^((a+b)+c)) i))
                = (kron_vec_high (kron_vec_low i) : Fin (2^b)) := by
    apply Fin.ext
    show (Fin.cast _ i).val / 2^c % 2^b = i.val % 2^(b+c) / 2^c
    rw [h_cast, h_pow_eq, Nat.mod_mul_left_div_self]
  have h_z_idx : kron_vec_low (Fin.cast (by rw [Nat.add_assoc]
                  : 2^(a+(b+c)) = 2^((a+b)+c)) i)
                = (kron_vec_low (kron_vec_low i) : Fin (2^c)) := by
    apply Fin.ext
    show (Fin.cast _ i).val % 2^c = i.val % 2^(b+c) % 2^c
    rw [h_cast, h_pow_eq, Nat.mod_mul_left_mod]
  rw [h_x_idx, h_y_idx, h_z_idx]

/-- **HEADLINE: Fully-typed Shor LSB state equality.**
`Shor_final_state_lsb m n anc f = QState.cast _ (shor_orbit_state a r N m n anc)`.

Combines:
- Unfold `Shor_final_state_lsb` and `Shor_initial_state`.
- `kron_vec_assoc` to bridge the left-associated kron_vec inside
  `Shor_initial_state` with the right-associated form.
- `QPE_var_lsb_on_Shor_initial_raw` to apply QPE_var_lsb and produce
  `shor_orbit_state`.

This is the MATHEMATICAL CLOSURE of the LSB-pipeline state equality.
Bridging to the published `Shor_final_state` (using `QPE_var`, not
`QPE_var_lsb`) requires a separate DESIGN DECISION (per autoresearch
protocol stop conditions). -/
theorem Shor_final_state_lsb_eq_shor_orbit_state
    (a r N m n anc : Nat)
    (hmanc : 0 < m + (n + anc)) (hm : 0 < m)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1)
    (h_min : ∀ s, 0 < s → s < r → a^s % N ≠ 1)
    (h_N : 1 < N) (h_N_lt : N ≤ 2^n) (h_N_pos : 0 < N)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped (n + anc) (f i)) :
    Shor_final_state_lsb m n anc f
    = QState.cast (by rw [pow_add, pow_add, mul_assoc])
        (shor_orbit_state a r N m n anc) := by
  unfold Shor_final_state_lsb Shor_initial_state FormalRV.SQIRPort.uc_eval
  congr 1
  rw [kron_vec_assoc (FormalRV.Framework.kron_zeros m)
        (FormalRV.Framework.basis_vector (2^n) 1)
        (FormalRV.Framework.kron_zeros anc)]
  exact QPE_var_lsb_on_Shor_initial_raw a r N hmanc hm h_r_pos h_arN h_min h_N h_N_lt h_N_pos
    f h_modmul h_wt_all

/-! ### Final closure: replacing the `QPE_MMI_correct` axiom

The LSB-pipeline state equality `Shor_final_state_lsb_eq_shor_orbit_state`
combined with the design change to `Shor_final_state` (which now uses
`QPE_var_lsb` — see Shor.lean) unlocks the closure of `QPE_MMI_correct`.

The new theorem chain:
1. `qpe_semantics_measurement_eq_from_lsb`: discharges the
   `h_qpe_semantics` hypothesis of `QPE_MMI_correct_modulo_qpe_semantics`.
2. `theorem QPE_MMI_correct`: replaces the deleted axiom of the same name.
3. `theorem Shor_correct_var`: re-declares the (now axiom-free) Shor
   correctness theorem in this file (moved from Shor.lean since it
   depends on the new theorem).
4. `theorem Shor_correct`: re-declares the specialised version. -/

/-- **`h_qpe_semantics` discharge.** With `Shor_final_state` now defined
via `QPE_var_lsb`, the LSB-pipeline state equality
`Shor_final_state_lsb_eq_shor_orbit_state` reduces it to a `QState.cast`
of `shor_orbit_state`, and `prob_partial_meas_cast` strips the cast. -/
theorem qpe_semantics_measurement_eq_from_lsb
    (a r N m n anc k : Nat) (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_modmul : ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → uc_well_typed (f i)) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (Shor_final_state m n anc f)
    = prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (shor_orbit_state a r N m n anc) := by
  obtain ⟨⟨h_a_pos, h_a_lt⟩, h_ord, h_m_bounds, h_n_bounds⟩ := h_basic
  obtain ⟨h_r_pos, h_arN, h_min⟩ := h_ord
  have h_N_pos : 0 < N := by omega
  have h_N_gt_one : 1 < N := by omega
  have h_N_lt_pow : N ≤ 2^n := h_n_bounds.1.le
  have hm : 0 < m := by
    have h_2m_pos : 0 < 2^m := Nat.two_pow_pos m
    have h_Nsq_pos : 0 < N^2 := by positivity
    have h_Nsq_lt : N^2 < 2^m := h_m_bounds.1
    by_contra h
    push_neg at h
    interval_cases m
    simp at h_Nsq_lt
    omega
  have hmanc : 0 < m + (n + anc) := by omega
  -- Shor_final_state and Shor_final_state_lsb are rfl-equal after the design change.
  have h_state_eq : Shor_final_state m n anc f
      = QState.cast (by rw [pow_add, pow_add, mul_assoc])
          (shor_orbit_state a r N m n anc) := by
    show Shor_final_state_lsb m n anc f
        = QState.cast _ (shor_orbit_state a r N m n anc)
    exact Shor_final_state_lsb_eq_shor_orbit_state a r N m n anc hmanc hm
      h_r_pos h_arN h_min h_N_gt_one h_N_lt_pow h_N_pos f h_modmul
      (fun i hi => h_wt i hi)
  rw [h_state_eq, prob_partial_meas_cast]

/-- **HEADLINE: `QPE_MMI_correct` (theorem replacing the axiom).** Same
statement as the deleted axiom; proof chains through
`QPE_MMI_correct_modulo_qpe_semantics` (in Shor.lean) +
`qpe_semantics_measurement_eq_from_lsb` (above). -/
theorem QPE_MMI_correct
    (a r N m n anc k : Nat) (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_mmi : ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  apply QPE_MMI_correct_modulo_qpe_semantics a r N m n anc k f h_basic h_mmi h_wt h_k_lt
  exact qpe_semantics_measurement_eq_from_lsb a r N m n anc k f h_basic h_mmi h_wt

/-- **`Shor_correct_var`** (Coq: `Shor.v:1193`). Re-declared in PostQFT
since `Shor.lean`'s version was deleted along with the axiom. Now
uses the proved `QPE_MMI_correct` theorem instead of the axiom. -/
theorem Shor_correct_var
    (a r N m n anc : Nat) (u : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_modmul : ModMulImpl a N n anc u)
    (h_wt : ∀ i, i < m → uc_well_typed (u i)) :
    probability_of_success a r N m n anc u ≥ κ / (Nat.log2 N : ℝ)^4 :=
  Shor_correct_var_conditional a r N m n anc u h_basic h_modmul h_wt
    (fun a' r' N' m' n' anc' k' f' h_b h_m h_w h_k =>
      QPE_MMI_correct a' r' N' m' n' anc' k' f' h_b h_m h_w h_k)
    (fun r' N' h_pos h_le => phi_n_over_n_lowerbound r' N' h_pos h_le)

/-- **`Shor_correct`** (Coq: `Shor.v:1295`). The specialised version
at `f_modmult_circuit`. Re-declared in PostQFT since `Shor.lean`'s
version was deleted along with the axiom. Uses the proved
`Shor_correct_var`.

**DEPRECATED (2026-05-29, Tick 84):** This theorem depends on the
deprecated placeholder axioms `f_modmult_circuit`,
`f_modmult_circuit_MMI`, and `f_modmult_circuit_uc_well_typed`.
Cite `FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms`
instead — that is the verified, axiom-free Shor theorem using the
SQIR-faithful modular multiplier. -/
@[deprecated "Use FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms instead — that theorem does not depend on the placeholder f_modmult_circuit* axioms" (since := "2026-05-29")]
theorem Shor_correct
    (a N : Nat) (h_aN : 0 < a ∧ a < N) (h_coprime : Nat.gcd a N = 1) :
    let m := Nat.log2 (2 * N^2)
    let n := Nat.log2 (2 * N)
    probability_of_success a (ord a N) N m n (modmult_rev_anc n)
        (f_modmult_circuit a (modinv a N) N n)
      ≥ κ / (Nat.log2 N : ℝ)^4 := by
  obtain ⟨h_a_pos, h_a_lt⟩ := h_aN
  have h_N_gt_one : 1 < N := by omega
  have h_Nsq_ne : N^2 ≠ 0 := by positivity
  have h_2N_ne : (2 * N) ≠ 0 := by omega
  have h_2Nsq_ne : (2 * N^2) ≠ 0 := by
    have : 0 < 2 * N^2 := by positivity
    omega
  have h_N_ne : N ≠ 0 := by omega
  have h_ord : Order a (ord a N) N := ord_Order a N h_a_pos h_a_lt h_coprime
  have h_log2_m : Nat.log2 (2 * N^2) = Nat.log2 (N^2) + 1 :=
    Nat.log2_two_mul h_Nsq_ne
  have h_log2_n : Nat.log2 (2 * N) = Nat.log2 N + 1 :=
    Nat.log2_two_mul h_N_ne
  have h_m_lower : 2 ^ (Nat.log2 (2 * N^2)) ≤ 2 * N^2 :=
    Nat.log2_self_le h_2Nsq_ne
  have h_m_upper : N^2 < 2 ^ (Nat.log2 (2 * N^2)) := by
    rw [h_log2_m, pow_succ]
    have h1 : 2 ^ Nat.log2 (N^2) ≤ N^2 := Nat.log2_self_le h_Nsq_ne
    have h2 : N^2 < 2 ^ (Nat.log2 (N^2) + 1) := by
      rw [← Nat.log2_lt h_Nsq_ne]; omega
    rw [pow_succ] at h2
    omega
  have h_n_lower : 2 ^ (Nat.log2 (2 * N)) ≤ 2 * N :=
    Nat.log2_self_le h_2N_ne
  have h_n_upper : N < 2 ^ (Nat.log2 (2 * N)) := by
    rw [h_log2_n, pow_succ]
    have h1 : 2 ^ Nat.log2 N ≤ N := Nat.log2_self_le h_N_ne
    have h2 : N < 2 ^ (Nat.log2 N + 1) := by
      rw [← Nat.log2_lt h_N_ne]; omega
    rw [pow_succ] at h2
    omega
  have h_basic : BasicSetting a (ord a N) N
      (Nat.log2 (2 * N^2)) (Nat.log2 (2 * N)) :=
    ⟨⟨h_a_pos, h_a_lt⟩, h_ord, ⟨h_m_upper, h_m_lower⟩, ⟨h_n_upper, h_n_lower⟩⟩
  have h_minv_lt : modinv a N < N := modinv_upper_bound a N h_N_gt_one
  have h_minv_inv : a * modinv a N % N = 1 :=
    Order_modinv_correct a N (ord a N) h_ord h_a_lt
  exact Shor_correct_var a (ord a N) N
    (Nat.log2 (2 * N^2)) (Nat.log2 (2 * N))
    (modmult_rev_anc (Nat.log2 (2 * N)))
    (f_modmult_circuit a (modinv a N) N (Nat.log2 (2 * N)))
    h_basic
    (f_modmult_circuit_MMI a (modinv a N) N (Nat.log2 (2 * N))
      h_a_lt h_minv_lt h_minv_inv)
    (fun i _ => f_modmult_circuit_uc_well_typed a (modinv a N) N
      (Nat.log2 (2 * N)) h_N_gt_one h_a_lt h_minv_lt i)

end FormalRV.SQIRPort
