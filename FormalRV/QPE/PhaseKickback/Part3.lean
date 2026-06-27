/- PhaseKickback — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.QPE.PhaseKickback.Part2

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-! ## Control-side bridge for `pad_u`

For control-register `pad_u` (qubit `n < m`), the `padEquiv (m+anc) n`
decomposition factors through `kron_vec_combine`:

    (padEquiv (m+anc) n ((xH, xM), Fin.cast (combine_kron xL y))).val
      = (kron_vec_combine (padEquiv m n ((xH, xM), xL)) y).val

This is the mirror of `padEquiv_combined_eq_kron_combine` (data-side
bridge) and the central arithmetic identity for any future
control-side basis-state theorem. Proof: unfold padEquiv +
kron_vec_combine, reduce to `2^(m+anc-n-1) = 2^(m-n-1) * 2^anc`, ring. -/
theorem padEquiv_control_eq_kron_combine (m anc n : Nat) (hn : n < m)
    (h_combined : n < m + anc)
    (h_size : m + anc - n - 1 = (m - n - 1) + anc)
    (xH : Fin (2^n)) (xM : Fin 2) (xL : Fin (2^(m-n-1)))
    (y : Fin (2^anc)) :
    (padEquiv (m + anc) n h_combined
        ((xH, xM), Fin.cast (by rw [h_size]) (kron_vec_combine xL y))).val
      = (kron_vec_combine (padEquiv m n hn ((xH, xM), xL)) y).val := by
  unfold padEquiv kron_vec_combine
  show (xL.val * 2^anc + y.val + 2^(m+anc-n-1) * (xM.val + 2 * xH.val))
        = (xL.val + 2^(m-n-1) * (xM.val + 2 * xH.val)) * 2^anc + y.val
  have h_pow : (2 : Nat)^(m+anc-n-1) = 2^(m-n-1) * 2^anc := by
    have hsum : (m-n-1) + anc = m+anc-n-1 := by omega
    rw [← pow_add, hsum]
  rw [h_pow]; ring

/-- **Control-side `pad_u` / `kron_vec` factorization (basis form).**

Mirror of `pad_u_shifted_kron_basis_factors` for control-register
gates. For `pad_u (m + anc) n M` with `n < m` (i.e., the qubit lies in
the control register), the action on a tensor of two basis vectors
factors through the local control-side `pad_u m n M`:

    pad_u (m + anc) n M * kron_vec (basis_x) (basis_y)
      = kron_vec (pad_u m n M * basis_x) (basis_y)

Proof: structurally identical to the data-side theorem, but uses
`padEquiv_control_eq_kron_combine` as the alignment bridge instead
of the data-side bridge, and decomposes `x` and `kron_vec_high r` via
`padEquiv m n` instead of `y` and `kron_vec_low r` via `padEquiv anc n`. -/
theorem pad_u_control_kron_basis_factors
    {m anc n : Nat} (hn : n < m)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (x : Fin (2^m)) (y : Fin (2^anc)) :
    pad_u (m + anc) n M
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                   (FormalRV.Framework.basis_vector (2^anc) y.val)
      = kron_vec (pad_u m n M * FormalRV.Framework.basis_vector (2^m) x.val)
                 (FormalRV.Framework.basis_vector (2^anc) y.val) := by
  have h_combined : n < m + anc := by omega
  have h_size : m + anc - n - 1 = (m - n - 1) + anc := by omega
  rw [kron_vec_basis_eq_basis_combine]
  ext r col
  have hcol : col = (0 : Fin 1) := Subsingleton.elim _ _
  subst hcol
  rw [mul_basis_vector_apply _ _ (kron_vec_combine x y).isLt]
  rw [kron_vec_apply]
  rw [mul_basis_vector_apply _ _ x.isLt]
  obtain ⟨⟨⟨xH, xM⟩, xL⟩, hx⟩ : ∃ p, padEquiv m n hn p = x :=
    ⟨(padEquiv m n hn).symm x, (padEquiv m n hn).apply_symm_apply x⟩
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hrh⟩ : ∃ p, padEquiv m n hn p = kron_vec_high r :=
    ⟨(padEquiv m n hn).symm (kron_vec_high r),
     (padEquiv m n hn).apply_symm_apply (kron_vec_high r)⟩
  have hxy_eq :
      (⟨(kron_vec_combine x y).val, (kron_vec_combine x y).isLt⟩ : Fin (2^(m+anc)))
        = padEquiv (m+anc) n h_combined
            ((xH, xM), Fin.cast (by rw [h_size]) (kron_vec_combine xL y)) := by
    apply Fin.ext
    rw [padEquiv_control_eq_kron_combine m anc n hn h_combined h_size
        xH xM xL y, hx]
  rw [hxy_eq]
  have hx_full :
      (⟨x.val, x.isLt⟩ : Fin (2^m)) = padEquiv m n hn ((xH, xM), xL) := by
    apply Fin.ext; rw [hx]
  rw [hx_full]
  have h_low_y : FormalRV.Framework.basis_vector (2^anc) (y.val) (kron_vec_low r) 0
      = if (kron_vec_low r).val = y.val then (1 : ℂ) else 0 := by
    rw [FormalRV.Framework.basis_vector_apply]
  rw [h_low_y]
  have hr_eq : r = padEquiv (m+anc) n h_combined
      ((rH, rM), Fin.cast (by rw [h_size]) (kron_vec_combine rL (kron_vec_low r))) := by
    apply Fin.ext
    rw [padEquiv_control_eq_kron_combine m anc n hn h_combined h_size
        rH rM rL (kron_vec_low r), hrh, kron_vec_combine_high_low]
  conv_rhs => rw [← hrh]
  conv_lhs => rw [hr_eq]
  rw [pad_u_apply_reindex h_combined M rH xH rM xM _ _]
  rw [pad_u_apply_reindex hn M rH xH rM xM rL xL]
  by_cases h_rH : rH = xH
  all_goals by_cases h_rL : rL = xL
  all_goals by_cases h_low : (kron_vec_low r).val = y.val
  -- Case 1 (TTT)
  · have h_combine_eq : kron_vec_combine rL (kron_vec_low r) =
                          kron_vec_combine xL y := by
      apply Fin.ext
      unfold kron_vec_combine
      simp [Fin.val_inj.mpr h_rL, h_low]
    have h_cast_eq : (Fin.cast (by rw [h_size]) (kron_vec_combine rL (kron_vec_low r)) :
                       Fin (2^(m+anc-n-1)))
                    = Fin.cast (by rw [h_size]) (kron_vec_combine xL y) := by
      apply Fin.ext; simp [h_combine_eq]
    rw [if_pos h_rH, if_pos h_cast_eq, if_pos h_rL, if_pos h_low]
    ring
  -- Case 2 (TTF)
  · have h_combine_ne : kron_vec_combine rL (kron_vec_low r) ≠
                          kron_vec_combine xL y := by
      intro h
      apply h_low
      have : kron_vec_low (kron_vec_combine rL (kron_vec_low r))
              = kron_vec_low (kron_vec_combine xL y) := by rw [h]
      rw [kron_vec_low_combine, kron_vec_low_combine] at this
      exact Fin.val_inj.mpr this
    have h_cast_ne : (Fin.cast (by rw [h_size]) (kron_vec_combine rL (kron_vec_low r)) :
                       Fin (2^(m+anc-n-1)))
                    ≠ Fin.cast (by rw [h_size]) (kron_vec_combine xL y) := by
      intro h; exact h_combine_ne ((Fin.cast_inj _).mp h)
    rw [if_pos h_rH, if_neg h_cast_ne, if_pos h_rL, if_neg h_low]
    ring
  -- Case 3 (TFT)
  · have h_combine_ne : kron_vec_combine rL (kron_vec_low r) ≠
                          kron_vec_combine xL y := by
      intro h
      apply h_rL
      have : kron_vec_high (kron_vec_combine rL (kron_vec_low r))
              = kron_vec_high (kron_vec_combine xL y) := by rw [h]
      rw [kron_vec_high_combine, kron_vec_high_combine] at this
      exact this
    have h_cast_ne : (Fin.cast (by rw [h_size]) (kron_vec_combine rL (kron_vec_low r)) :
                       Fin (2^(m+anc-n-1)))
                    ≠ Fin.cast (by rw [h_size]) (kron_vec_combine xL y) := by
      intro h; exact h_combine_ne ((Fin.cast_inj _).mp h)
    rw [if_pos h_rH, if_neg h_cast_ne, if_neg h_rL]
    ring
  -- Case 4 (TFF)
  · have h_combine_ne : kron_vec_combine rL (kron_vec_low r) ≠
                          kron_vec_combine xL y := by
      intro h
      apply h_rL
      have : kron_vec_high (kron_vec_combine rL (kron_vec_low r))
              = kron_vec_high (kron_vec_combine xL y) := by rw [h]
      rw [kron_vec_high_combine, kron_vec_high_combine] at this
      exact this
    have h_cast_ne : (Fin.cast (by rw [h_size]) (kron_vec_combine rL (kron_vec_low r)) :
                       Fin (2^(m+anc-n-1)))
                    ≠ Fin.cast (by rw [h_size]) (kron_vec_combine xL y) := by
      intro h; exact h_combine_ne ((Fin.cast_inj _).mp h)
    rw [if_pos h_rH, if_neg h_cast_ne, if_neg h_rL]
    ring
  -- Cases 5-8: rH ≠ xH, first factor is 0; simp closes
  all_goals (simp [h_rH])

/-- **Linearity extension: control-side `pad_u` on basis-control,
arbitrary-data `kron_vec`.** Same linearity-over-basis-decomposition
strategy as `pad_u_shifted_kron_basis_control_vec`. -/
theorem pad_u_control_kron_basis_control_vec {m anc n : Nat} (hn : n < m)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (x : Fin (2^m)) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    pad_u (m + anc) n M
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = kron_vec (pad_u m n M * FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  conv_lhs => rw [vec_eq_sum_basis (2^anc) ψ]
  conv_rhs => rw [vec_eq_sum_basis (2^anc) ψ]
  rw [kron_vec_sum_right, Matrix.mul_sum, kron_vec_sum_right]
  apply Finset.sum_congr rfl
  intro y _
  rw [kron_vec_smul_right (ψ y 0) _ _]
  rw [Matrix.mul_smul]
  rw [pad_u_control_kron_basis_factors hn M x y]
  rw [kron_vec_smul_right]

/-! ## Linearity on the control side + npar_H factorization -/

/-- Linearity of `kron_vec` on the LEFT over finite sums.
Companion to `kron_vec_sum_right`. -/
theorem kron_vec_sum_left {a b : Nat}
    {ι : Type*} [Fintype ι] (s : ι → Matrix (Fin (2^a)) (Fin 1) ℂ)
    (φ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec (∑ y, s y) φ = ∑ y, kron_vec (s y) φ := by
  ext i j
  rw [Matrix.sum_apply, kron_vec_apply, Matrix.sum_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [kron_vec_apply]

/-- **Arbitrary control-vector `pad_u` factorization.** Extends
`pad_u_control_kron_basis_control_vec` (basis-control) to arbitrary
`χ` via linearity over the basis decomposition. -/
theorem pad_u_control_kron_vec_factors {m anc n : Nat} (hn : n < m)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    pad_u (m + anc) n M * kron_vec χ ψ
      = kron_vec (pad_u m n M * χ) ψ := by
  conv_lhs => rw [vec_eq_sum_basis (2^m) χ]
  conv_rhs => rw [vec_eq_sum_basis (2^m) χ]
  rw [kron_vec_sum_left, Matrix.mul_sum, Matrix.mul_sum, kron_vec_sum_left]
  apply Finset.sum_congr rfl
  intro x _
  rw [kron_vec_smul_left (χ x 0) _ _]
  rw [Matrix.mul_smul]
  rw [pad_u_control_kron_basis_control_vec hn M x ψ]
  rw [Matrix.mul_smul]
  rw [kron_vec_smul_left]

/-- **App1 control-register wrapper.** Since `BaseUnitary 1` has only
the `R` constructor, this reduces to `pad_u_control_kron_vec_factors`. -/
theorem uc_eval_app1_control_kron_vec {m anc n : Nat} (hn : n < m)
    (u : FormalRV.Framework.BaseUnitary 1)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (UCom.app1 u n : FormalRV.Framework.BaseUCom (m + anc)) * kron_vec χ ψ
      = kron_vec
          (FormalRV.Framework.uc_eval (UCom.app1 u n : FormalRV.Framework.BaseUCom m) * χ) ψ := by
  cases u with
  | R θ φ lam =>
      show pad_u (m + anc) n (rotation θ φ lam) * kron_vec χ ψ = _
      exact pad_u_control_kron_vec_factors hn (rotation θ φ lam) χ ψ

/-- **Auxiliary: `npar_H k` factorization for any `k ≤ m`.** Induction
on `k` with `m` fixed. The H at qubit `k < m` lifts to
`pad_u (m+anc) k hMatrix`, which factors through `kron_vec` via
`pad_u_control_kron_vec_factors`. -/
theorem uc_eval_npar_H_kron_vec_aux (m anc : Nat) (hm : 0 < m)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    ∀ k, k ≤ m →
      FormalRV.Framework.uc_eval
          (npar_H k : FormalRV.Framework.BaseUCom (m + anc)) * kron_vec χ ψ
        = kron_vec
            (FormalRV.Framework.uc_eval (npar_H k : FormalRV.Framework.BaseUCom m) * χ) ψ := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [uc_eval_npar_H_zero_eq_one (by omega : 0 < m + anc)]
      rw [uc_eval_npar_H_zero_eq_one hm]
      rw [Matrix.one_mul, Matrix.one_mul]
  | succ k ih =>
      intro hk
      have hk_lt_m : k < m := by omega
      have hk_le_m : k ≤ m := Nat.le_of_lt hk_lt_m
      rw [uc_eval_npar_H_succ]
      rw [uc_eval_npar_H_succ]
      rw [Matrix.mul_assoc]
      rw [ih hk_le_m]
      rw [pad_u_control_kron_vec_factors hk_lt_m hMatrix _ ψ]
      rw [Matrix.mul_assoc]

/-- **`npar_H m` factors through `kron_vec`.** The full Hadamard column
on `m` control qubits acts on a `kron_vec χ ψ` by applying `npar_H m`
to the control component `χ` and leaving the data component `ψ`
unchanged. Specialization of the auxiliary lemma at `k = m`. -/
theorem uc_eval_npar_H_kron_vec (m anc : Nat) (hm : 0 < m)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (npar_H m : FormalRV.Framework.BaseUCom (m + anc)) * kron_vec χ ψ
      = kron_vec
          (FormalRV.Framework.uc_eval (npar_H m : FormalRV.Framework.BaseUCom m) * χ) ψ :=
  uc_eval_npar_H_kron_vec_aux m anc hm χ ψ m (le_refl m)

/-! ## H-on-zero base case + lower-level helpers -/

/-- For `dim = 1`, `pad_u 1 0 M = M`. The reindex layer collapses
because the high and low padding factors are `Iₙ(1)`. -/
theorem pad_u_one_zero_eq (M : Matrix (Fin 2) (Fin 2) ℂ) : pad_u 1 0 M = M := by
  ext i j
  obtain ⟨⟨⟨iH, iM⟩, iL⟩, hi⟩ : ∃ p, padEquiv 1 0 (by omega) p = i :=
    ⟨(padEquiv 1 0 (by omega)).symm i, (padEquiv 1 0 (by omega)).apply_symm_apply i⟩
  obtain ⟨⟨⟨jH, jM⟩, jL⟩, hj⟩ : ∃ p, padEquiv 1 0 (by omega) p = j :=
    ⟨(padEquiv 1 0 (by omega)).symm j, (padEquiv 1 0 (by omega)).apply_symm_apply j⟩
  rw [← hi, ← hj]
  rw [pad_u_apply_reindex (by omega : 0 < 1) M iH jH iM jM iL jL]
  have h_iH_zero : iH.val = 0 := by have := iH.isLt; omega
  have h_iL_zero : iL.val = 0 := by have := iL.isLt; omega
  have h_jH_zero : jH.val = 0 := by have := jH.isLt; omega
  have h_jL_zero : jL.val = 0 := by have := jL.isLt; omega
  have hiH : iH = jH := by apply Fin.ext; omega
  have hiL : iL = jL := by apply Fin.ext; omega
  rw [if_pos hiH, if_pos hiL, one_mul, mul_one]
  have h_padEq_i : (padEquiv 1 0 (by omega) ((iH, iM), iL)).val = iM.val := by
    unfold padEquiv finProdFinEquiv; simp
  have h_padEq_j : (padEquiv 1 0 (by omega) ((jH, jM), jL)).val = jM.val := by
    unfold padEquiv finProdFinEquiv; simp
  have h_eq_iM : (padEquiv 1 0 (by omega) ((iH, iM), iL) : Fin 2) = iM := by
    apply Fin.ext; rw [h_padEq_i]
  have h_eq_jM : (padEquiv 1 0 (by omega) ((jH, jM), jL) : Fin 2) = jM := by
    apply Fin.ext; rw [h_padEq_j]
  rw [h_eq_iM, h_eq_jM]

/-- `hMatrix * |0⟩ = (√2/2) · (|0⟩ + |1⟩)`. The fundamental Hadamard
identity on the standard zero state. Proved by 2-entry extensionality. -/
theorem hMatrix_mul_basis_zero :
    hMatrix * FormalRV.Framework.basis_vector 2 0
      = ((Real.sqrt 2 / 2 : ℂ)) •
        (FormalRV.Framework.basis_vector 2 0 +
          FormalRV.Framework.basis_vector 2 1) := by
  ext i j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst hj
  fin_cases i
  · simp [hMatrix, FormalRV.Framework.basis_vector_apply,
          Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply]
  · simp [hMatrix, FormalRV.Framework.basis_vector_apply,
          Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply]

/-- **Single-qubit H-on-zero**: `uc_eval (H 0 : BaseUCom 1) * kron_zeros 1
= (√2/2) · (basis_vector 2 0 + basis_vector 2 1)`. The base case of
the m-qubit `npar_H` induction. -/
theorem H_zero_eq_plus :
    FormalRV.Framework.uc_eval
        (FormalRV.Framework.BaseUCom.H 0 : FormalRV.Framework.BaseUCom 1) *
        FormalRV.Framework.kron_zeros 1
      = ((Real.sqrt 2 / 2 : ℂ)) •
        (FormalRV.Framework.basis_vector 2 0 +
          FormalRV.Framework.basis_vector 2 1) := by
  show pad_u 1 0 (FormalRV.Framework.rotation (Real.pi / 2) 0 Real.pi) *
        FormalRV.Framework.kron_zeros 1 = _
  rw [FormalRV.Framework.rotation_H]
  rw [pad_u_one_zero_eq]
  show hMatrix * FormalRV.Framework.basis_vector 2 0 = _
  exact hMatrix_mul_basis_zero


end FormalRV.SQIRPort
