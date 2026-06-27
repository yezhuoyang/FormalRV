/- PhaseKickback — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.QPE.PhaseKickback.Part3

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-! ## H-on-zeros uniform superposition

The H-preparation theorem that establishes the uniform superposition
state at the entry of QPE. Built from the basic identities
`H_zero_eq_plus`, `uc_eval_npar_H_kron_vec`, and the structural
arithmetic helpers below. -/

/-- **Arbitrary-control + arbitrary-data data-side factorization.**
The full generality of `pad_u_shifted_kron_basis_control_vec` — by
linearity over the basis decomposition of χ. -/
theorem pad_u_shifted_kron_vec_factors {m anc n : Nat} (hn : n < anc)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    pad_u (m + anc) (m + n) M * kron_vec χ ψ
      = kron_vec χ (pad_u anc n M * ψ) := by
  conv_lhs => rw [vec_eq_sum_basis (2^m) χ]
  conv_rhs => rw [vec_eq_sum_basis (2^m) χ]
  rw [kron_vec_sum_left, Matrix.mul_sum, kron_vec_sum_left]
  apply Finset.sum_congr rfl
  intro x _
  rw [kron_vec_smul_left (χ x 0) _ _]
  rw [Matrix.mul_smul]
  rw [pad_u_shifted_kron_basis_control_vec hn M x ψ]
  rw [kron_vec_smul_left]

/-- **`kron_zeros (m+1) = kron_vec (kron_zeros m) (kron_zeros 1)`.**
Both sides reduce to `basis_vector (2^(m+1)) 0`. -/
theorem kron_zeros_succ (m : Nat) :
    FormalRV.Framework.kron_zeros (m + 1)
      = kron_vec (FormalRV.Framework.kron_zeros m)
                 (FormalRV.Framework.kron_zeros 1) := by
  unfold FormalRV.Framework.kron_zeros
  rw [kron_vec_basis_eq_basis_combine m 1
        (⟨0, Nat.two_pow_pos m⟩) (⟨0, Nat.two_pow_pos 1⟩)]
  congr 1

/-- **Scalar recurrence:** `(1/√2^m) · (√2/2) = 1/√2^(m+1)`. -/
theorem inv_sqrt_pow_two_succ (m : Nat) :
    ((1 : ℂ) / Real.sqrt (2^m : ℝ)) * ((Real.sqrt 2 / 2 : ℂ))
      = (1 : ℂ) / Real.sqrt (2^(m+1) : ℝ) := by
  have h_pos : (0 : ℝ) < (2^m : ℝ) := by positivity
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h_sqrt_mul : Real.sqrt (2^(m+1) : ℝ) = Real.sqrt (2^m : ℝ) * Real.sqrt 2 := by
    rw [pow_succ, Real.sqrt_mul h_pos.le]
  rw [h_sqrt_mul]
  push_cast
  have h_sqrt_2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr h2_pos
  have h_sqrt_m_pos : (0 : ℝ) < Real.sqrt (2^m : ℝ) := Real.sqrt_pos.mpr h_pos
  have h_sqrt_2_ne_C : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast h_sqrt_2_pos.ne'
  have h_sqrt_m_ne_C : (Real.sqrt (2^m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h_sqrt_m_pos.ne'
  field_simp
  exact_mod_cast Real.sq_sqrt (le_of_lt h2_pos)

/-- **Sum split over the last bit:** the uniform basis sum on `m+1`
qubits splits into pairs along the highest-bit / lowest-bit alternative. -/
theorem uniform_sum_succ_split (m : Nat) :
    ∑ z : Fin (2^(m+1)), FormalRV.Framework.basis_vector (2^(m+1)) z.val
      = ∑ x : Fin (2^m),
          (kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                    (FormalRV.Framework.basis_vector (2^1) 0)
            + kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                       (FormalRV.Framework.basis_vector (2^1) 1)) := by
  rw [← Fintype.sum_equiv (kronEquiv m 1)
      (fun p : Fin (2^m) × Fin (2^1) =>
        FormalRV.Framework.basis_vector (2^(m+1)) (kronEquiv m 1 p).val)
      (fun z => FormalRV.Framework.basis_vector (2^(m+1)) z.val)
      (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  have h0 : (kronEquiv m 1 (x, (⟨0, Nat.two_pow_pos 1⟩ : Fin (2^1)))).val
            = (kron_vec_combine x (⟨0, Nat.two_pow_pos 1⟩ : Fin (2^1))).val := rfl
  have h1 : (kronEquiv m 1 (x, (⟨1, by simp⟩ : Fin (2^1)))).val
            = (kron_vec_combine x (⟨1, by simp⟩ : Fin (2^1))).val := rfl
  show ∑ y : Fin 2,
        FormalRV.Framework.basis_vector (2^(m+1)) (kronEquiv m 1 (x, y)).val = _
  rw [Fin.sum_univ_two]
  rw [show ((0 : Fin 2) : Fin (2^1)) = ⟨0, Nat.two_pow_pos 1⟩ from rfl]
  rw [show ((1 : Fin 2) : Fin (2^1)) = ⟨1, by simp⟩ from rfl]
  rw [h0, h1]
  rw [← kron_vec_basis_eq_basis_combine m 1 x ⟨0, Nat.two_pow_pos 1⟩]
  rw [← kron_vec_basis_eq_basis_combine m 1 x ⟨1, by simp⟩]

/-- Single-qubit `m=1` scalar special case. -/
private theorem inv_sqrt_two_pow_one :
    ((1 : ℂ) / Real.sqrt ((2:ℝ)^1)) = (Real.sqrt 2 / 2 : ℂ) := by
  have h_pos : (0 : ℝ) < 2 := by norm_num
  have h_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h_pos.le
  have hs : Real.sqrt ((2:ℝ)^1) = Real.sqrt 2 := by norm_num
  rw [hs]
  have h_sqrt_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr h_pos).ne'
  field_simp
  exact_mod_cast h_sq.symm

/-- **PURE H-ON-ZEROS UNIFORM SUPERPOSITION.** The Hadamard column
on `m` qubits applied to the all-zeros state produces the uniform
superposition `(1/√2^m) · ∑_x |x⟩`. Requires `0 < m` because at
`m = 0` the framework's `pad_u 0 0` returns zero. Inducts on `m`:
- m=1 base: `H_zero_eq_plus` + scalar special case.
- m+1 step: split via `kron_zeros_succ`, IH for prefix m H-gates via
  `uc_eval_npar_H_kron_vec`, then the final H gate at position m via
  `pad_u_shifted_kron_vec_factors` + `pad_u_one_zero_eq` +
  `hMatrix_mul_basis_zero`; reassemble with kron-vec linearity and
  `uniform_sum_succ_split`. -/
theorem npar_H_kron_zeros_pure_eq_uniform_sum :
    ∀ (m : Nat), 0 < m →
      FormalRV.Framework.uc_eval
          (npar_H m : FormalRV.Framework.BaseUCom m) *
          FormalRV.Framework.kron_zeros m
        = ((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
          ∑ x : Fin (2^m), FormalRV.Framework.basis_vector (2^m) x.val := by
  intro m hm
  induction m with
  | zero => omega
  | succ k ih =>
      by_cases hk : k = 0
      · subst hk
        rw [show (npar_H 1 : FormalRV.Framework.BaseUCom 1) =
              UCom.seq (npar_H 0) (FormalRV.Framework.BaseUCom.H 0) from rfl]
        show FormalRV.Framework.uc_eval _ * FormalRV.Framework.uc_eval _ *
              FormalRV.Framework.kron_zeros 1 = _
        rw [uc_eval_npar_H_zero_eq_one (by omega : 0 < 1)]
        rw [Matrix.mul_one]
        rw [H_zero_eq_plus]
        rw [inv_sqrt_two_pow_one]
        congr 1
        show FormalRV.Framework.basis_vector 2 0 +
              FormalRV.Framework.basis_vector 2 1
            = ∑ x : Fin 2, FormalRV.Framework.basis_vector 2 x.val
        rw [Fin.sum_univ_two]
        rfl
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
        have ih_app := ih hk_pos
        rw [uc_eval_npar_H_succ]
        rw [kron_zeros_succ]
        rw [Matrix.mul_assoc]
        rw [uc_eval_npar_H_kron_vec k 1 hk_pos (FormalRV.Framework.kron_zeros k)
            (FormalRV.Framework.kron_zeros 1)]
        rw [ih_app]
        rw [show pad_u (k + 1) k hMatrix = pad_u (k + 1) (k + 0) hMatrix from by rfl]
        rw [pad_u_shifted_kron_vec_factors (by omega : 0 < 1) hMatrix _ _]
        rw [pad_u_one_zero_eq]
        rw [show (FormalRV.Framework.kron_zeros 1 : Matrix (Fin 2) (Fin 1) ℂ)
              = FormalRV.Framework.basis_vector 2 0 from rfl]
        rw [hMatrix_mul_basis_zero]
        rw [kron_vec_smul_left, kron_vec_smul_right]
        rw [smul_smul]
        rw [inv_sqrt_pow_two_succ k]
        congr 1
        rw [uniform_sum_succ_split k]
        rw [kron_vec_add_right]
        rw [kron_vec_sum_left, kron_vec_sum_left]
        rw [← Finset.sum_add_distrib]
        rfl

/-- **TENSORED H-ON-ZEROS UNIFORM SUPERPOSITION.** The H column on
`m` control qubits applied to `kron_vec (kron_zeros m) ψ` produces
the uniform-superposition state on the control register tensored with
the unchanged data state `ψ`. Combines the pure theorem with
`uc_eval_npar_H_kron_vec` (the m-qubit H factorization across kron). -/
theorem npar_H_kron_zeros_eq_uniform_sum {m anc : Nat} (hm : 0 < m)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval (npar_H m : FormalRV.Framework.BaseUCom (m + anc))
        * kron_vec (FormalRV.Framework.kron_zeros m) ψ
      = ((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
          ∑ x : Fin (2^m),
            kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  rw [uc_eval_npar_H_kron_vec m anc hm (FormalRV.Framework.kron_zeros m) ψ]
  rw [npar_H_kron_zeros_pure_eq_uniform_sum m hm]
  rw [kron_vec_smul_left]
  rw [kron_vec_sum_left]

/-! ## Unconditional pre-QFT QPE eigenstate theorem

The cap of the pre-QFT half of QPE. With the H-preparation and
shifted-cascade infrastructure now in place, the conditional pre-QFT
theorem from earlier sessions becomes fully unconditional. -/

/-- **Shifted oracle eigen on the H-prepared uniform-superposition
state.** For each oracle `f` with data-register eigenstate `ψ` of
eigenvalue `ζ`, the lifted (shifted) oracle has the H-prepared
uniform sum `(1/√2^m) · ∑_x |x⟩ ⊗ ψ` as an eigenstate with the
same eigenvalue. Proved by distributing the matrix-vector
product over the scalar and the sum, applying
`lifted_oracle_eigen_on_kron_basis_control_vec` pointwise, then
reassembling via `smul_comm`. -/
theorem shifted_oracle_eigen_on_uniform_control_sum
    {m anc : Nat}
    (f : FormalRV.Framework.BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ)
    (ζ : ℂ)
    (h_wt : UCom.WellTyped anc f)
    (h_eig_data : FormalRV.Framework.uc_eval f * ψ = ζ • ψ) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => m + q) f : FormalRV.Framework.BaseUCom (m + anc))
      *
    (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
      ∑ x : Fin (2^m),
        kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
    =
    ζ •
    (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
      ∑ x : Fin (2^m),
        kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ) := by
  rw [Matrix.mul_smul]
  rw [Matrix.mul_sum]
  rw [show ∑ x : Fin (2^m),
        FormalRV.Framework.uc_eval
            (map_qubits (fun q => m + q) f :
              FormalRV.Framework.BaseUCom (m + anc))
          * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
        = ∑ x : Fin (2^m),
            ζ • kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ from by
    apply Finset.sum_congr rfl
    intro x _
    exact lifted_oracle_eigen_on_kron_basis_control_vec f x ψ ζ h_wt h_eig_data]
  rw [← Finset.smul_sum]
  rw [smul_comm]

/-- **UNCONDITIONAL PRE-QFT QPE EIGENSTATE THEOREM.**

The full pre-QFT QPE composition on a data-register eigenstate `ψ`:
applying `npar_H m` then `controlled_powers` to `|0^m⟩ ⊗ ψ` produces
the phase-projector-product form acting on the uniform-superposition
state `(1/√2^m) · ∑_x |x⟩ ⊗ ψ`.

Composition of:
1. `npar_H_kron_zeros_eq_uniform_sum` — H prepares the uniform sum.
2. `shifted_oracle_eigen_on_uniform_control_sum` — establishes the
   common-eigenstate hypothesis for each lifted oracle on the
   uniform sum.
3. `uc_eval_controlled_powers_shifted_on_common_eigenstate` —
   the QPE-shifted cascade theorem, which now applies because (2)
   discharges its eigen hypothesis.

This is the cap of the pre-QFT half of QPE. The conditional
theorem `QPE_pre_QFT_on_eigenstate_conditional` from earlier
sessions is now subsumed by this unconditional version. -/
theorem QPE_pre_QFT_on_eigenstate
    {m anc : Nat} (hmanc : 0 < m + anc) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) (ζ : Nat → ℂ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (h_eig_data : ∀ i, i < m → FormalRV.Framework.uc_eval (f i) * ψ = ζ i • ψ) :
    FormalRV.Framework.uc_eval (controlled_powers
        (fun i => (map_qubits (fun q => m + q) (f i) :
          FormalRV.Framework.BaseUCom (m + anc))) m)
      * (FormalRV.Framework.uc_eval
            (npar_H m : FormalRV.Framework.BaseUCom (m + anc))
          * kron_vec (FormalRV.Framework.kron_zeros m) ψ)
    = @phase_projector_product (m + anc) ζ m
        * (((1 : ℂ) / Real.sqrt (2^m : ℝ)) •
            ∑ x : Fin (2^m),
              kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ) := by
  rw [npar_H_kron_zeros_eq_uniform_sum hm ψ]
  apply uc_eval_controlled_powers_shifted_on_common_eigenstate hmanc f h_wt_all _ ζ
  intro i hi
  exact shifted_oracle_eigen_on_uniform_control_sum (f i) ψ (ζ i)
        (h_wt_all i hi) (h_eig_data i hi)


end FormalRV.SQIRPort
