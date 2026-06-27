/- PhaseKickback — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.QPE.PhaseKickback.ShiftedCascade

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-! ## Bridge: padEquiv on combined-kron index

The arithmetic identity at the core of `pad_u_shifted_kron_basis_factors`:
the `padEquiv (m+anc) (m+n)` decomposition of `kron_vec_combine x y`
factors through a `combine_kron(x, y_H)` outer index whenever `y` has
been pre-decomposed via `padEquiv anc n`.

This is the central .val identity. Used to align the `pad_u`-side
3-way splitting with the `kron_vec`-side 2-way splitting.

Proof: unfold padEquiv (chain of `finProdFinEquiv` + `Fin.castOrderIso`)
to expose the Nat-value formulas; reduce to `2^anc = 2^(anc-n-1) * 2 * 2^n`
via `pow_add` arithmetic; close with `ring`. -/
theorem padEquiv_combined_eq_kron_combine
    (m anc n : Nat) (hn : n < anc)
    (h_combined : m + n < m + anc)
    (h_size : m + anc - (m + n) - 1 = anc - n - 1)
    (x : Fin (2^m)) (yH : Fin (2^n)) (yM : Fin 2)
    (yL : Fin (2^(anc-n-1))) :
    (padEquiv (m + anc) (m + n) h_combined
        ((kron_vec_combine x yH, yM), Fin.cast (by rw [h_size]) yL)).val
      = (kron_vec_combine x (padEquiv anc n hn ((yH, yM), yL))).val := by
  unfold padEquiv kron_vec_combine
  show (yL.val + 2^(m+anc-(m+n)-1) * (yM.val + 2 * (x.val * 2^n + yH.val)))
        = x.val * 2^anc + (yL.val + 2^(anc-n-1) * (yM.val + 2 * yH.val))
  have h_size_pow : (2 : Nat) ^ (m+anc-(m+n)-1) = 2^(anc-n-1) := by
    have : m + anc - (m + n) - 1 = anc - n - 1 := by omega
    rw [this]
  rw [h_size_pow]
  have h_pow_anc : (2 : Nat) ^ anc = 2^(anc-n-1) * 2 * 2^n := by
    have h_sum : (anc - n - 1) + 1 + n = anc := by omega
    rw [show (2 : Nat) ^ (anc-n-1) * 2 * 2^n = 2 ^ ((anc-n-1) + 1 + n) from by
          rw [pow_add, pow_add]; ring]
    rw [h_sum]
  rw [h_pow_anc]
  ring

/-- **`pad_u` on `kron_vec` of basis vectors: factorization theorem.**

For the QPE shift convention (control register at qubits `[0, m)`,
data register at `[m, m + anc)`), `pad_u (m + anc) (m + n) M` applied
to a tensor of two basis vectors factors as `kron_vec` of the
control-side basis with the local `pad_u anc n M` action on the
data-side basis.

Proof outline:
1. Rewrite `kron_vec (basis_vector x) (basis_vector y)` as
   `basis_vector (kron_vec_combine x y)` via
   `kron_vec_basis_eq_basis_combine`.
2. After `ext r`, extract column entries using `mul_basis_vector_apply`.
3. Decompose `y` and `kron_vec_low r` via `padEquiv anc n`.
4. Apply the bridge `padEquiv_combined_eq_kron_combine` to express
   both `r` and the combined index in `padEquiv (m+anc) (m+n)` form.
5. Apply `pad_u_apply_reindex` to both LHS entry and RHS pad_u entry.
6. Case split (2x2x2 = 8 cases) on `kron_vec_high r = x`, `lrH = yH`,
   `lrL = yL`. Each case reduces to `combine_kron`-injectivity
   arithmetic + `simp`. -/
theorem pad_u_shifted_kron_basis_factors
    {m anc n : Nat} (hn : n < anc)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (x : Fin (2^m)) (y : Fin (2^anc)) :
    pad_u (m + anc) (m + n) M
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                   (FormalRV.Framework.basis_vector (2^anc) y.val)
      = kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                 (pad_u anc n M *
                   FormalRV.Framework.basis_vector (2^anc) y.val) := by
  have h_combined : m + n < m + anc := by omega
  have h_size : m + anc - (m + n) - 1 = anc - n - 1 := by omega
  rw [kron_vec_basis_eq_basis_combine]
  ext r col
  have hcol : col = (0 : Fin 1) := Subsingleton.elim _ _
  subst hcol
  rw [mul_basis_vector_apply _ _ (kron_vec_combine x y).isLt]
  rw [kron_vec_apply]
  rw [mul_basis_vector_apply _ _ y.isLt]
  obtain ⟨⟨⟨yH, yM⟩, yL⟩, hy⟩ :
      ∃ p, padEquiv anc n hn p = y :=
    ⟨(padEquiv anc n hn).symm y, (padEquiv anc n hn).apply_symm_apply y⟩
  obtain ⟨⟨⟨lrH, lrM⟩, lrL⟩, hlr⟩ :
      ∃ p, padEquiv anc n hn p = kron_vec_low r :=
    ⟨(padEquiv anc n hn).symm (kron_vec_low r),
     (padEquiv anc n hn).apply_symm_apply (kron_vec_low r)⟩
  have hxy_eq :
      (⟨(kron_vec_combine x y).val, (kron_vec_combine x y).isLt⟩ : Fin (2^(m+anc)))
        = padEquiv (m+anc) (m+n) h_combined
            ((kron_vec_combine x yH, yM), Fin.cast (by rw [h_size]) yL) := by
    apply Fin.ext
    rw [padEquiv_combined_eq_kron_combine m anc n hn h_combined h_size
        x yH yM yL, hy]
  rw [hxy_eq]
  have hy_full :
      (⟨y.val, y.isLt⟩ : Fin (2^anc)) = padEquiv anc n hn ((yH, yM), yL) := by
    apply Fin.ext; rw [hy]
  rw [hy_full]
  have h_high_r : FormalRV.Framework.basis_vector (2^m) (x.val) (kron_vec_high r) 0
      = if (kron_vec_high r).val = x.val then (1 : ℂ) else 0 := by
    rw [FormalRV.Framework.basis_vector_apply]
  rw [h_high_r]
  have hr_eq : r = padEquiv (m+anc) (m+n) h_combined
      ((kron_vec_combine (kron_vec_high r) lrH, lrM),
        Fin.cast (by rw [h_size]) lrL) := by
    apply Fin.ext
    rw [padEquiv_combined_eq_kron_combine m anc n hn h_combined h_size
        (kron_vec_high r) lrH lrM lrL, hlr, kron_vec_combine_high_low]
  conv_rhs => rw [← hlr]
  conv_lhs => rw [hr_eq]
  rw [pad_u_apply_reindex h_combined M _ _ lrM yM _ _]
  rw [pad_u_apply_reindex hn M lrH yH lrM yM lrL yL]
  -- Helper: combine_kron is injective on values; combine_kron_ne when high
  -- or low components differ.
  -- 8-way case split.
  by_cases h_hr : (kron_vec_high r).val = x.val
  all_goals by_cases h_lrH : lrH = yH
  all_goals by_cases h_lrL : lrL = yL
  -- Case 1 (TTT): all equal
  · have h_combine : kron_vec_combine (kron_vec_high r) lrH = kron_vec_combine x yH := by
      apply Fin.ext
      unfold kron_vec_combine
      simp [h_hr, Fin.val_inj.mpr h_lrH]
    have h_castL : (Fin.cast (by rw [h_size]) lrL : Fin (2^(m+anc-(m+n)-1)))
                  = Fin.cast (by rw [h_size]) yL := by
      apply Fin.ext; simp [h_lrL]
    rw [if_pos h_combine, if_pos h_castL, if_pos h_hr]
    simp [h_lrH, h_lrL]
  -- Case 2 (TTF): lrL ≠ yL
  · have h_combine : kron_vec_combine (kron_vec_high r) lrH = kron_vec_combine x yH := by
      apply Fin.ext
      unfold kron_vec_combine
      simp [h_hr, Fin.val_inj.mpr h_lrH]
    have h_castL_ne : (Fin.cast (by rw [h_size]) lrL : Fin (2^(m+anc-(m+n)-1)))
                  ≠ Fin.cast (by rw [h_size]) yL := by
      intro h; apply h_lrL
      exact (Fin.cast_inj _).mp h
    rw [if_pos h_combine, if_neg h_castL_ne, if_neg h_lrL]
    ring
  -- Case 3 (TFT): lrH ≠ yH
  · have h_combine_ne : kron_vec_combine (kron_vec_high r) lrH
                          ≠ kron_vec_combine x yH := by
      intro h
      apply h_lrH
      have h_val : ((kron_vec_combine (kron_vec_high r) lrH) : Nat) =
              ((kron_vec_combine x yH) : Nat) := Fin.val_inj.mpr h
      unfold kron_vec_combine at h_val
      simp at h_val
      have h_lrH_lt : lrH.val < 2^n := lrH.isLt
      have h_yH_lt : yH.val < 2^n := yH.isLt
      rw [h_hr] at h_val
      apply Fin.ext; omega
    simp [h_combine_ne, h_lrH]
  -- Case 4 (TFF): lrH ≠ yH (lrL also ≠ yL, but combine_ne suffices)
  · have h_combine_ne : kron_vec_combine (kron_vec_high r) lrH
                          ≠ kron_vec_combine x yH := by
      intro h
      apply h_lrH
      have h_val : ((kron_vec_combine (kron_vec_high r) lrH) : Nat) =
              ((kron_vec_combine x yH) : Nat) := Fin.val_inj.mpr h
      unfold kron_vec_combine at h_val
      simp at h_val
      have h_lrH_lt : lrH.val < 2^n := lrH.isLt
      have h_yH_lt : yH.val < 2^n := yH.isLt
      rw [h_hr] at h_val
      apply Fin.ext; omega
    simp [h_combine_ne, h_lrH]
  -- Case 5 (FTT): high r ≠ x
  · have h_combine_ne : kron_vec_combine (kron_vec_high r) lrH
                          ≠ kron_vec_combine x yH := by
      intro h
      apply h_hr
      have h_val : ((kron_vec_combine (kron_vec_high r) lrH) : Nat) =
              ((kron_vec_combine x yH) : Nat) := Fin.val_inj.mpr h
      unfold kron_vec_combine at h_val
      simp [Fin.val_inj.mpr h_lrH] at h_val
      have h_lrH_lt : lrH.val < 2^n := lrH.isLt
      omega
    simp [h_combine_ne, h_hr]
  -- Case 6 (FTF): high r ≠ x
  · have h_combine_ne : kron_vec_combine (kron_vec_high r) lrH
                          ≠ kron_vec_combine x yH := by
      intro h
      apply h_hr
      have h_val : ((kron_vec_combine (kron_vec_high r) lrH) : Nat) =
              ((kron_vec_combine x yH) : Nat) := Fin.val_inj.mpr h
      unfold kron_vec_combine at h_val
      simp [Fin.val_inj.mpr h_lrH] at h_val
      have h_lrH_lt : lrH.val < 2^n := lrH.isLt
      omega
    simp [h_combine_ne, h_hr]
  -- Case 7 (FFT): high r ≠ x — use kron_vec_high_combine
  · have h_combine_ne : kron_vec_combine (kron_vec_high r) lrH
                          ≠ kron_vec_combine x yH := by
      intro h
      apply h_hr
      have : kron_vec_high (kron_vec_combine (kron_vec_high r) lrH)
              = kron_vec_high (kron_vec_combine x yH) := by rw [h]
      rw [kron_vec_high_combine, kron_vec_high_combine] at this
      exact Fin.val_inj.mpr this
    simp [h_combine_ne, h_hr]
  -- Case 8 (FFF): high r ≠ x — use kron_vec_high_combine
  · have h_combine_ne : kron_vec_combine (kron_vec_high r) lrH
                          ≠ kron_vec_combine x yH := by
      intro h
      apply h_hr
      have : kron_vec_high (kron_vec_combine (kron_vec_high r) lrH)
              = kron_vec_high (kron_vec_combine x yH) := by rw [h]
      rw [kron_vec_high_combine, kron_vec_high_combine] at this
      exact Fin.val_inj.mpr this
    simp [h_combine_ne, h_hr]

/-! ## Vector decomposition + linearity extensions

To extend the basis-state factorization theorem to arbitrary data
vectors `ψ`, we decompose `ψ` as a sum of basis vectors and lift
factorization pointwise. -/

/-- **Vector decomposition into basis.** Any matrix column vector
equals the sum over basis vectors weighted by its entries. The
elementary linear algebra fact `ψ = ∑ y, ψ y 0 • basis_vector y`. -/
theorem vec_eq_sum_basis (n : Nat) (ψ : Matrix (Fin n) (Fin 1) ℂ) :
    ψ = ∑ y : Fin n, ψ y 0 • FormalRV.Framework.basis_vector n y.val := by
  ext i j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst hj
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [FormalRV.Framework.basis_vector_apply_eq _ _ _ _ rfl]; ring
  · intro j _ hj
    have hjv : i.val ≠ j.val := fun h => hj (Fin.ext h.symm)
    rw [FormalRV.Framework.basis_vector_apply, if_neg hjv]; ring
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- Linearity of `kron_vec` on the right over finite sums. -/
theorem kron_vec_sum_right {a b : Nat} (χ : Matrix (Fin (2^a)) (Fin 1) ℂ)
    {ι : Type*} [Fintype ι] (s : ι → Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec χ (∑ y, s y) = ∑ y, kron_vec χ (s y) := by
  ext i j
  rw [Matrix.sum_apply, kron_vec_apply, Matrix.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [kron_vec_apply]

/-- **Single-qubit `pad_u` on basis-control, arbitrary-data kron.**

The basis-state theorem `pad_u_shifted_kron_basis_factors` extends
by linearity over the basis decomposition of `ψ`:

    pad_u (m + anc) (m + n) M * kron_vec (basis_vector x) ψ
      = kron_vec (basis_vector x) (pad_u anc n M * ψ).

Proof: decompose `ψ` as `∑_y ψ(y, 0) • basis_y`, distribute via
`kron_vec_sum_right` and `Matrix.mul_sum`, then apply the basis
theorem pointwise. -/
theorem pad_u_shifted_kron_basis_control_vec {m anc n : Nat} (hn : n < anc)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (x : Fin (2^m)) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    pad_u (m + anc) (m + n) M
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                 (pad_u anc n M * ψ) := by
  conv_lhs => rw [vec_eq_sum_basis (2^anc) ψ]
  conv_rhs => rw [vec_eq_sum_basis (2^anc) ψ]
  rw [kron_vec_sum_right, Matrix.mul_sum, Matrix.mul_sum, kron_vec_sum_right]
  apply Finset.sum_congr rfl
  intro y _
  rw [kron_vec_smul_right (ψ y 0) _ _]
  rw [Matrix.mul_smul]
  rw [pad_u_shifted_kron_basis_factors hn M x y]
  rw [Matrix.mul_smul]
  rw [kron_vec_smul_right]

/-- **`pad_ctrl` (CNOT) on basis-control, arbitrary-data kron.**

The shifted CNOT factors through `kron_vec` for any data state.
Derivable from `pad_u_shifted_kron_basis_control_vec` via
`pad_ctrl`'s projector decomposition. -/
theorem pad_ctrl_shifted_kron_basis_control_vec {m anc a b : Nat}
    (ha : a < anc) (hb : b < anc)
    (x : Fin (2^m)) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    pad_ctrl (m + anc) (m + a) (m + b) σx
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
                 (pad_ctrl anc a b σx * ψ) := by
  unfold pad_ctrl
  rw [Matrix.add_mul]
  rw [pad_u_shifted_kron_basis_control_vec ha proj0 x ψ]
  rw [Matrix.mul_assoc]
  rw [pad_u_shifted_kron_basis_control_vec hb σx x ψ]
  rw [pad_u_shifted_kron_basis_control_vec ha proj1 x _]
  rw [← kron_vec_add_right]
  rw [Matrix.add_mul, Matrix.mul_assoc]

/-- **CIRCUIT-LEVEL shifted factorization.** For any well-typed
`BaseUCom anc` circuit `c`, the shifted lift `map_qubits (· + m) c`
acts on `kron_vec (basis_vector x) ψ` by leaving the control-side
basis state intact and applying the local `uc_eval c` to the data
side.

Proof: structural induction on `c`. Each gate case uses the
corresponding shifted basis-control-vec lemma; `seq` chains via IH
and matrix associativity; `app3` is vacuous. -/
theorem uc_eval_map_qubits_shift_kron_basis_control_vec {m anc : Nat}
    (c : FormalRV.Framework.BaseUCom anc)
    (h_wt : UCom.WellTyped anc c)
    (x : Fin (2^m)) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => m + q) c : FormalRV.Framework.BaseUCom (m + anc))
      * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
    = kron_vec (FormalRV.Framework.basis_vector (2^m) x.val)
               (FormalRV.Framework.uc_eval c * ψ) := by
  induction c generalizing ψ with
  | seq c₁ c₂ ih₁ ih₂ =>
      cases h_wt with
      | seq h_wt1 h_wt2 =>
        show FormalRV.Framework.uc_eval
              (map_qubits (fun q => m + q) c₂ : FormalRV.Framework.BaseUCom (m + anc))
              * FormalRV.Framework.uc_eval
                  (map_qubits (fun q => m + q) c₁ : FormalRV.Framework.BaseUCom (m + anc))
              * kron_vec
                  (FormalRV.Framework.basis_vector (2^m) x.val) ψ
              = _
        rw [Matrix.mul_assoc]
        rw [ih₁ h_wt1 ψ]
        rw [ih₂ h_wt2 _]
        show kron_vec _ (FormalRV.Framework.uc_eval c₂ *
                          (FormalRV.Framework.uc_eval c₁ * ψ))
              = kron_vec _ (FormalRV.Framework.uc_eval c₂ *
                              FormalRV.Framework.uc_eval c₁ * ψ)
        rw [Matrix.mul_assoc]
  | app1 u n =>
      cases h_wt with
      | app1 hn =>
        cases u with
        | R θ φ lam =>
          exact pad_u_shifted_kron_basis_control_vec hn (rotation θ φ lam) x ψ
  | app2 u a b =>
      cases h_wt with
      | app2 ha hb hab =>
        cases u
        exact pad_ctrl_shifted_kron_basis_control_vec ha hb x ψ
  | app3 u _ _ _ => cases u

/-- **Unconditional lifted-oracle eigen on basis-control kron.**

Given a data-register eigenstate `ψ` of `f` with eigenvalue `ζ`,
the shifted oracle `map_qubits (· + m) f` has `kron_vec (basis_x) ψ`
as eigenstate with the same eigenvalue.

This is the unconditional version of
`lifted_oracle_eigen_on_kron_control_conditional` for basis-control
states. The proof is a 2-line composition of the circuit-level
shifted factorization theorem above with the scalar pull-out via
`kron_vec_smul_right`. -/
theorem lifted_oracle_eigen_on_kron_basis_control_vec {m anc : Nat}
    (f : FormalRV.Framework.BaseUCom anc)
    (x : Fin (2^m)) (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) (ζ : ℂ)
    (h_wt : UCom.WellTyped anc f)
    (h_eig : FormalRV.Framework.uc_eval f * ψ = ζ • ψ) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => m + q) f : FormalRV.Framework.BaseUCom (m + anc))
        * kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ
      = ζ • kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ := by
  rw [uc_eval_map_qubits_shift_kron_basis_control_vec f h_wt x ψ]
  rw [h_eig, kron_vec_smul_right]


end FormalRV.SQIRPort
