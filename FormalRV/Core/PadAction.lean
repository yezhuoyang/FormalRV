/-
  FormalRV.Framework.PadAction — entry-formula and basis-vector-action
  lemmas for `pad_u` / `pad_ctrl`.

  Foundation for proving the SQIR `f_to_vec_*` family (`f_to_vec_CNOT`,
  `f_to_vec_H`, `f_to_vec_T`, etc.) which describe how each gate acts on
  computational-basis states.

  Status: under construction. The first foundation theorem is
  `pad_u_apply_reindex` — it gives the (r, c) entry of `pad_u dim n M` when
  the indices are written via the reindex equiv used in `pad_u`'s definition.
-/
import FormalRV.Core.UnitarySem
import FormalRV.Core.QuantumLib

namespace FormalRV.Framework

open Matrix Complex
open scoped Kronecker

/-! ## The reindex equiv used by `pad_u` -/

/-- The reindex equiv embedded inside `pad_u dim n` (when `n < dim`).
    Decomposes a `Fin (2^dim)` index into a triple `(high, middle, low)` with
    `high : Fin (2^n)`, `middle : Fin 2`, `low : Fin (2^(dim-n-1))`. -/
noncomputable def padEquiv (dim n : Nat) (h : n < dim) :
    (Fin (2^n) × Fin 2) × Fin (2^(dim-n-1)) ≃ Fin (2^dim) :=
  let e₀ : (Fin (2^n) × Fin 2) × Fin (2^(dim-n-1)) ≃ Fin (2^n * 2 * 2^(dim-n-1)) :=
    (finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv
  e₀.trans (Fin.castOrderIso (two_pow_split dim n h)).toEquiv

/-! ## Entry formula for `pad_u`

    The (r, c) entry of `pad_u dim n M` factorizes as
      δ_high(r,c) · M[middle(r), middle(c)] · δ_low(r,c)
    where the δ's enforce equality on the high and low parts of the index. -/

/-- Entry formula for `pad_u dim n M` with indices written via `padEquiv`.
    This is the workhorse for proving how `pad_u` acts on basis vectors. -/
theorem pad_u_apply_reindex {dim n : Nat} (h : n < dim)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (rH cH : Fin (2^n)) (rM cM : Fin 2) (rL cL : Fin (2^(dim-n-1))) :
    pad_u dim n M (padEquiv dim n h ((rH, rM), rL)) (padEquiv dim n h ((cH, cM), cL))
      = (if rH = cH then (1:ℂ) else 0)
        * M rM cM
        * (if rL = cL then (1:ℂ) else 0) := by
  unfold pad_u padEquiv
  rw [dif_pos h]
  -- Goal: Matrix.reindex e e ((Iₙ(2^n) ⊗ₖ M) ⊗ₖ Iₙ(2^(dim-n-1))) (e ...) (e ...) = ...
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
             Equiv.symm_apply_apply]
  -- Goal: ((Iₙ(2^n) ⊗ₖ M) ⊗ₖ Iₙ(2^(dim-n-1))) ((rH, rM), rL) ((cH, cM), cL) = ...
  rw [Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply]
  -- Goal: Iₙ(2^n) rH cH * M rM cM * Iₙ(2^(dim-n-1)) rL cL = ...
  unfold Iₙ
  by_cases h1 : rH = cH <;> by_cases h2 : rL = cL
  all_goals first
    | (subst h1; subst h2; simp [Matrix.one_apply_eq])
    | (subst h1; rw [Matrix.one_apply_eq, Matrix.one_apply_ne h2]; simp [h2])
    | (subst h2; rw [Matrix.one_apply_ne h1, Matrix.one_apply_eq]; simp [h1])
    | (rw [Matrix.one_apply_ne h1, Matrix.one_apply_ne h2]; simp [h1, h2])

/-! ## Action of a matrix on a basis vector

    For any matrix `A : Matrix (Fin n) (Fin n) ℂ` and basis state
    `basis_vector n k`, the product `A * basis_vector n k` is the k-th
    column of `A`. -/

/-- `A * basis_vector n k` extracts column `k` of `A`. -/
theorem mul_basis_vector_apply {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ)
    (k : Nat) (h : k < n) (i : Fin n) :
    (A * basis_vector n k) i 0 = A i ⟨k, h⟩ := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single ⟨k, h⟩]
  · simp [basis_vector]
  · intro j _ hj
    have hjk : j.val ≠ k := fun heq => hj (Fin.ext heq)
    simp [basis_vector, hjk]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-! ## `pad_u` acting on a basis state, via the `padEquiv` decomposition -/

/-- The (r, 0) entry of `pad_u dim n M * basis_vector(2^dim, K)` when both
    `r` and `K` are written via `padEquiv`. -/
theorem pad_u_basis_vector_entry {dim n : Nat} (h : n < dim)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (kH : Fin (2^n)) (kM : Fin 2) (kL : Fin (2^(dim-n-1)))
    (rH : Fin (2^n)) (rM : Fin 2) (rL : Fin (2^(dim-n-1))) :
    (pad_u dim n M * basis_vector (2^dim)
        (padEquiv dim n h ((kH, kM), kL)).val)
      (padEquiv dim n h ((rH, rM), rL)) 0
      = (if rH = kH then (1:ℂ) else 0)
        * M rM kM
        * (if rL = kL then (1:ℂ) else 0) := by
  rw [mul_basis_vector_apply _ _ (padEquiv dim n h ((kH, kM), kL)).isLt]
  -- Goal: pad_u dim n M (padEquiv ...) ⟨(padEquiv ...).val, _⟩ = ...
  -- Need ⟨(padEquiv ...).val, _⟩ = padEquiv ...
  have h_eq : (⟨(padEquiv dim n h ((kH, kM), kL)).val,
               (padEquiv dim n h ((kH, kM), kL)).isLt⟩ : Fin (2^dim))
              = padEquiv dim n h ((kH, kM), kL) := Fin.ext rfl
  rw [h_eq]
  exact pad_u_apply_reindex h M rH kH rM kM rL kL

/-! ## Bit-flip on `Fin 2` -/

/-- Flip a `Fin 2` value: 0 ↔ 1. -/
def flipBit : Fin 2 → Fin 2
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨_+2, h⟩ => absurd h (by omega)

@[simp] theorem flipBit_zero : flipBit 0 = 1 := rfl
@[simp] theorem flipBit_one : flipBit 1 = 0 := rfl

theorem flipBit_ne (x : Fin 2) : flipBit x ≠ x := by
  fin_cases x <;> decide

theorem ne_iff_eq_flipBit (x y : Fin 2) : x ≠ y ↔ x = flipBit y := by
  fin_cases x <;> fin_cases y <;> decide

/-- σx as a function on `Fin 2` indices: 1 iff `i ≠ j`, expressible as
    `i = flipBit j`. Used to compute σx applied to basis indices. -/
theorem σx_apply (i j : Fin 2) :
    σx i j = (if i = flipBit j then (1:ℂ) else 0) := by
  fin_cases i <;> fin_cases j <;> simp [σx]

/-! ## `pad_u σx` flips the middle bit of a basis state

    Special case of `pad_u_basis_vector_entry` for `M = σx`. The σx Pauli
    has the property `σx[a][b] = 1 ↔ a ≠ b`, so the only surviving entry
    of `pad_u σx * basis_vector(K)` is at the middle-bit-flipped index. -/

/-- Bridge lemma: equality of `padEquiv` values iff triple equality. -/
theorem padEquiv_val_eq_iff {dim n : Nat} (h : n < dim)
    (a b : (Fin (2^n) × Fin 2) × Fin (2^(dim-n-1))) :
    (padEquiv dim n h a).val = (padEquiv dim n h b).val ↔ a = b := by
  constructor
  · intro h_eq
    exact (padEquiv dim n h).injective (Fin.ext h_eq)
  · intro h_eq; rw [h_eq]

theorem pad_u_σx_on_basis_vector_padEquiv {dim n : Nat} (h : n < dim)
    (kH : Fin (2^n)) (kM : Fin 2) (kL : Fin (2^(dim-n-1))) :
    pad_u dim n σx * basis_vector (2^dim)
        (padEquiv dim n h ((kH, kM), kL)).val
      = basis_vector (2^dim)
          (padEquiv dim n h ((kH, flipBit kM), kL)).val := by
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hr⟩ : ∃ x, padEquiv dim n h x = r :=
    ⟨(padEquiv dim n h).symm r, (padEquiv dim n h).apply_symm_apply r⟩
  rw [← hr]
  rw [pad_u_basis_vector_entry h σx kH kM kL rH rM rL]
  rw [σx_apply]
  simp only [basis_vector_apply]
  -- Convert val-equality to triple-equality via padEquiv_val_eq_iff
  have h_iff : (padEquiv dim n h ((rH, rM), rL)).val =
               (padEquiv dim n h ((kH, flipBit kM), kL)).val
             ↔ (rH = kH ∧ rM = flipBit kM ∧ rL = kL) := by
    rw [padEquiv_val_eq_iff]
    simp [Prod.mk.injEq, and_assoc]
  simp only [h_iff]
  by_cases h1 : rH = kH <;> by_cases h2 : rM = flipBit kM <;> by_cases h3 : rL = kL <;>
    simp [h1, h2, h3]

/-! ## `pad_u proj0` / `pad_u proj1` on basis states

    Projectors are diagonal: `proj0[a][b] = 1 ↔ a = b = 0`. So
    `pad_u proj0 * b(K)` keeps the state when the target qubit is 0,
    zeros it otherwise. -/

theorem proj0_apply (i j : Fin 2) :
    proj0 i j = (if i = 0 ∧ j = 0 then (1:ℂ) else 0) := by
  fin_cases i <;> fin_cases j <;> simp [proj0]

theorem proj1_apply (i j : Fin 2) :
    proj1 i j = (if i = 1 ∧ j = 1 then (1:ℂ) else 0) := by
  fin_cases i <;> fin_cases j <;> simp [proj1]

/-- `pad_u dim n proj0` acting on a basis state with middle bit 0
    leaves it unchanged. -/
theorem pad_u_proj0_on_basis_vector_zero {dim n : Nat} (h : n < dim)
    (kH : Fin (2^n)) (kL : Fin (2^(dim-n-1))) :
    pad_u dim n proj0 * basis_vector (2^dim)
        (padEquiv dim n h ((kH, (0 : Fin 2)), kL)).val
      = basis_vector (2^dim)
          (padEquiv dim n h ((kH, (0 : Fin 2)), kL)).val := by
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hr⟩ : ∃ x, padEquiv dim n h x = r :=
    ⟨(padEquiv dim n h).symm r, (padEquiv dim n h).apply_symm_apply r⟩
  rw [← hr]
  rw [pad_u_basis_vector_entry h proj0 kH 0 kL rH rM rL]
  rw [proj0_apply]
  simp only [basis_vector_apply]
  have h_iff : (padEquiv dim n h ((rH, rM), rL)).val =
               (padEquiv dim n h ((kH, (0 : Fin 2)), kL)).val
             ↔ (rH = kH ∧ rM = 0 ∧ rL = kL) := by
    rw [padEquiv_val_eq_iff]
    simp [Prod.mk.injEq, and_assoc]
  simp only [h_iff]
  by_cases h1 : rH = kH <;> by_cases h2 : rM = (0:Fin 2) <;> by_cases h3 : rL = kL <;>
    simp [h1, h2, h3]

/-- `pad_u dim n proj0` acting on a basis state with middle bit 1
    annihilates it. -/
theorem pad_u_proj0_on_basis_vector_one {dim n : Nat} (h : n < dim)
    (kH : Fin (2^n)) (kL : Fin (2^(dim-n-1))) :
    pad_u dim n proj0 * basis_vector (2^dim)
        (padEquiv dim n h ((kH, (1 : Fin 2)), kL)).val = 0 := by
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hr⟩ : ∃ x, padEquiv dim n h x = r :=
    ⟨(padEquiv dim n h).symm r, (padEquiv dim n h).apply_symm_apply r⟩
  rw [← hr]
  rw [pad_u_basis_vector_entry h proj0 kH 1 kL rH rM rL]
  rw [proj0_apply]
  simp

/-- `pad_u dim n proj1` acting on a basis state with middle bit 1
    leaves it unchanged. -/
theorem pad_u_proj1_on_basis_vector_one {dim n : Nat} (h : n < dim)
    (kH : Fin (2^n)) (kL : Fin (2^(dim-n-1))) :
    pad_u dim n proj1 * basis_vector (2^dim)
        (padEquiv dim n h ((kH, (1 : Fin 2)), kL)).val
      = basis_vector (2^dim)
          (padEquiv dim n h ((kH, (1 : Fin 2)), kL)).val := by
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hr⟩ : ∃ x, padEquiv dim n h x = r :=
    ⟨(padEquiv dim n h).symm r, (padEquiv dim n h).apply_symm_apply r⟩
  rw [← hr]
  rw [pad_u_basis_vector_entry h proj1 kH 1 kL rH rM rL]
  rw [proj1_apply]
  simp only [basis_vector_apply]
  have h_iff : (padEquiv dim n h ((rH, rM), rL)).val =
               (padEquiv dim n h ((kH, (1 : Fin 2)), kL)).val
             ↔ (rH = kH ∧ rM = 1 ∧ rL = kL) := by
    rw [padEquiv_val_eq_iff]
    simp [Prod.mk.injEq, and_assoc]
  simp only [h_iff]
  by_cases h1 : rH = kH <;> by_cases h2 : rM = (1:Fin 2) <;> by_cases h3 : rL = kL <;>
    simp [h1, h2, h3]

/-- `pad_u dim n proj1` acting on a basis state with middle bit 0
    annihilates it. -/
theorem pad_u_proj1_on_basis_vector_zero {dim n : Nat} (h : n < dim)
    (kH : Fin (2^n)) (kL : Fin (2^(dim-n-1))) :
    pad_u dim n proj1 * basis_vector (2^dim)
        (padEquiv dim n h ((kH, (0 : Fin 2)), kL)).val = 0 := by
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hr⟩ : ∃ x, padEquiv dim n h x = r :=
    ⟨(padEquiv dim n h).symm r, (padEquiv dim n h).apply_symm_apply r⟩
  rw [← hr]
  rw [pad_u_basis_vector_entry h proj1 kH 0 kL rH rM rL]
  rw [proj1_apply]
  simp

/-! ## `funbool_to_nat` split lemma

    Decomposes `funbool_to_nat dim f` into the (top, middle, bottom) parts
    that align with `pad_u`'s qubit-`n` decomposition. This is the Nat-level
    bridge that lets us write `f_to_vec dim f = basis_vector(2^dim, padEquiv ...)`
    and then apply the pad_u-on-basis-vector lemmas. -/

theorem funbool_to_nat_split_aux (n k : Nat) (f : Nat → Bool) :
    funbool_to_nat (n + 1 + k) f
      = funbool_to_nat n f * 2^(k+1)
        + (if f n then 1 else 0) * 2^k
        + funbool_to_nat k (fun p => f (p + n + 1)) := by
  induction k with
  | zero =>
      simp [funbool_to_nat_succ]
      ring
  | succ k ih =>
      have h_lhs : funbool_to_nat (n + 1 + (k+1)) f
                  = 2 * funbool_to_nat (n + 1 + k) f
                    + (if f (n + 1 + k) then 1 else 0) := by
        rw [show n + 1 + (k + 1) = (n + 1 + k) + 1 from by omega]
        exact funbool_to_nat_succ (n + 1 + k) f
      rw [h_lhs, ih]
      have h_rhs_succ : funbool_to_nat (k+1) (fun p => f (p + n + 1))
                      = 2 * funbool_to_nat k (fun p => f (p + n + 1))
                        + (if f (k + n + 1) then 1 else 0) := by
        rw [funbool_to_nat_succ]
      rw [h_rhs_succ]
      have h_index : k + n + 1 = n + 1 + k := by omega
      rw [h_index]
      ring

theorem funbool_to_nat_split (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    funbool_to_nat dim f
      = funbool_to_nat n f * 2^(dim - n)
        + (if f n then 1 else 0) * 2^(dim - n - 1)
        + funbool_to_nat (dim - n - 1) (fun p => f (p + n + 1)) := by
  have h_eq : dim = n + 1 + (dim - n - 1) := by omega
  conv_lhs => rw [h_eq]
  rw [funbool_to_nat_split_aux n (dim - n - 1) f]
  have h_pow : (dim - n - 1) + 1 = dim - n := by omega
  rw [h_pow]

/-! ## Compute `padEquiv` value as a natural number -/

/-- The natural-number value of `padEquiv((kH, kM), kL)` is the standard
    base-2 packing: `kH * 2^(dim-n) + kM * 2^(dim-n-1) + kL`. -/
theorem padEquiv_val_formula {dim n : Nat} (h : n < dim)
    (kH : Fin (2^n)) (kM : Fin 2) (kL : Fin (2^(dim-n-1))) :
    (padEquiv dim n h ((kH, kM), kL)).val
      = kH.val * 2^(dim-n) + kM.val * 2^(dim-n-1) + kL.val := by
  unfold padEquiv
  simp [finProdFinEquiv, Fin.castOrderIso]
  have h_pow : 2^(dim - n - 1) * 2 = 2^(dim - n) := by
    have hsucc : dim - n = (dim - n - 1) + 1 := by omega
    conv_rhs => rw [hsucc]
    rw [pow_succ]
  -- After simp, goal is essentially:
  -- kL + 2^(dim-n-1) * (kM + 2 * kH) = kH * 2^(dim-n) + kM * 2^(dim-n-1) + kL
  -- Rewrite 2^(dim-n) using h_pow and expand
  rw [show kH.val * 2^(dim-n) = kH.val * (2^(dim-n-1) * 2) from by rw [h_pow]]
  ring

/-! ## `f_to_vec` rewritten as a `padEquiv` basis state at qubit `n` -/

/-- `f_to_vec dim f` is the basis state at the `padEquiv` packing of
    (top-bits-of-f, f-at-n, bottom-bits-of-f). -/
theorem f_to_vec_eq_basis_padEquiv (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    f_to_vec dim f
      = basis_vector (2^dim)
          (padEquiv dim n h
            ((⟨funbool_to_nat n f, funbool_to_nat_lt n f⟩,
              ⟨if f n then 1 else 0, by split_ifs <;> omega⟩),
             ⟨funbool_to_nat (dim - n - 1) (fun p => f (p + n + 1)),
              funbool_to_nat_lt _ _⟩)).val := by
  unfold f_to_vec
  congr 1
  rw [padEquiv_val_formula]
  exact funbool_to_nat_split dim n h f

/-! ## `funbool_to_nat` under function update -/

/-- After `update f n v`, the `funbool_to_nat` decomposition only changes
    in the middle bit. -/
theorem funbool_to_nat_update_eq (dim n : Nat) (h : n < dim)
    (f : Nat → Bool) (v : Bool) :
    funbool_to_nat dim (update f n v)
      = funbool_to_nat n f * 2^(dim - n)
        + (if v then 1 else 0) * 2^(dim - n - 1)
        + funbool_to_nat (dim - n - 1) (fun p => f (p + n + 1)) := by
  have h_top : funbool_to_nat n (update f n v) = funbool_to_nat n f := by
    apply funbool_to_nat_congr
    intro i hi
    simp [update]
    intro h_eq; omega
  have h_mid : (update f n v) n = v := by simp [update]
  have h_bot : funbool_to_nat (dim - n - 1) (fun p => update f n v (p + n + 1))
             = funbool_to_nat (dim - n - 1) (fun p => f (p + n + 1)) := by
    apply funbool_to_nat_congr
    intro i _
    simp [update]
    intro h_eq; omega
  rw [funbool_to_nat_split dim n h (update f n v), h_top, h_mid, h_bot]

/-! ## `flipBit` value formula -/

/-- `flipBit (⟨if b then 1 else 0⟩).val = if !b then 1 else 0`. -/
theorem flipBit_val_of_b (b : Bool) :
    (flipBit ⟨if b then 1 else 0, by split_ifs <;> omega⟩).val
      = (if !b then 1 else 0) := by
  cases b <;> simp [flipBit]

/-! ## f-coordinate version: `pad_u σx` flips bit `n` of `f` -/

/-- `pad_u dim n σx` acting on `f_to_vec dim f` flips the bit at index `n`. -/
theorem pad_u_σx_on_f_to_vec (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    pad_u dim n σx * f_to_vec dim f = f_to_vec dim (update f n (!f n)) := by
  rw [f_to_vec_eq_basis_padEquiv dim n h f]
  rw [pad_u_σx_on_basis_vector_padEquiv h]
  unfold f_to_vec
  congr 1
  rw [padEquiv_val_formula h]
  rw [funbool_to_nat_update_eq dim n h f (!f n)]
  rw [flipBit_val_of_b]

/-! ## f-coordinate versions: proj0 / proj1 on `f_to_vec` -/

/-- `pad_u dim n proj0` acting on `f_to_vec dim f`: keeps the state if
    `f n = false`, annihilates if `f n = true`. -/
theorem pad_u_proj0_on_f_to_vec (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    pad_u dim n proj0 * f_to_vec dim f
      = if f n then 0 else f_to_vec dim f := by
  by_cases hfn : f n
  · -- f n = true: kM = 1, proj0 annihilates
    rw [if_pos hfn]
    rw [f_to_vec_eq_basis_padEquiv dim n h f]
    have hkM : (⟨if f n then 1 else 0, by split_ifs <;> omega⟩ : Fin 2) = (1 : Fin 2) := by
      apply Fin.ext; simp [hfn]
    rw [hkM]
    exact pad_u_proj0_on_basis_vector_one h _ _
  · -- f n = false: kM = 0, proj0 keeps the state
    rw [if_neg hfn]
    conv_lhs => rw [f_to_vec_eq_basis_padEquiv dim n h f]
    have hkM : (⟨if f n then 1 else 0, by split_ifs <;> omega⟩ : Fin 2) = (0 : Fin 2) := by
      apply Fin.ext; simp [hfn]
    rw [hkM]
    rw [pad_u_proj0_on_basis_vector_zero h _ _]
    rw [← hkM]
    exact (f_to_vec_eq_basis_padEquiv dim n h f).symm

/-- `pad_u dim n proj1` acting on `f_to_vec dim f`: keeps the state if
    `f n = true`, annihilates if `f n = false`. -/
theorem pad_u_proj1_on_f_to_vec (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    pad_u dim n proj1 * f_to_vec dim f
      = if f n then f_to_vec dim f else 0 := by
  by_cases hfn : f n
  · -- f n = true: kM = 1, proj1 keeps the state
    rw [if_pos hfn]
    conv_lhs => rw [f_to_vec_eq_basis_padEquiv dim n h f]
    have hkM : (⟨if f n then 1 else 0, by split_ifs <;> omega⟩ : Fin 2) = (1 : Fin 2) := by
      apply Fin.ext; simp [hfn]
    rw [hkM]
    rw [pad_u_proj1_on_basis_vector_one h _ _]
    rw [← hkM]
    exact (f_to_vec_eq_basis_padEquiv dim n h f).symm
  · -- f n = false: kM = 0, proj1 annihilates
    rw [if_neg hfn]
    rw [f_to_vec_eq_basis_padEquiv dim n h f]
    have hkM : (⟨if f n then 1 else 0, by split_ifs <;> omega⟩ : Fin 2) = (0 : Fin 2) := by
      apply Fin.ext; simp [hfn]
    rw [hkM]
    exact pad_u_proj1_on_basis_vector_zero h _ _

/-! ## `f_to_vec_CNOT` — proven via the projector decomposition

    `pad_ctrl n i j σx = pad_u i proj0 + pad_u i proj1 * pad_u j σx`. Apply to
    `f_to_vec n f`, distribute, use the f-coordinate per-gate lemmas, and
    case-split on `f i`. -/

theorem f_to_vec_CNOT_proved (n i j : Nat) (f : Nat → Bool)
    (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    uc_eval (BaseUCom.CNOT i j : BaseUCom n) * f_to_vec n f
      = f_to_vec n (update f j (xor (f j) (f i))) := by
  -- uc_eval (CNOT i j) = ueval_cnot n i j = pad_ctrl n i j σx
  show pad_ctrl n i j σx * f_to_vec n f = _
  unfold pad_ctrl
  -- (A + B * C) * v = A * v + B * (C * v)
  rw [Matrix.add_mul, Matrix.mul_assoc]
  rw [pad_u_σx_on_f_to_vec n j hj f]
  rw [pad_u_proj0_on_f_to_vec n i hi f]
  rw [pad_u_proj1_on_f_to_vec n i hi (update f j (!f j))]
  -- (update f j (!f j)) i = f i since i ≠ j
  rw [show update f j (!f j) i = f i from update_neq f j i (!f j) hij]
  -- LHS now: (if f i then 0 else f_to_vec n f) + (if f i then f_to_vec n (update f j (!f j)) else 0)
  by_cases hfi : f i
  · -- f i = true: LHS = 0 + f_to_vec n (update f j (!f j)) = f_to_vec n (update f j (!f j))
    rw [if_pos hfi, if_pos hfi]
    rw [zero_add]
    -- xor (f j) (f i) = xor (f j) true = !(f j)
    have hxor : xor (f j) (f i) = !f j := by simp [hfi]
    rw [hxor]
  · -- f i = false: LHS = f_to_vec n f + 0 = f_to_vec n f
    rw [if_neg hfi, if_neg hfi]
    rw [add_zero]
    -- xor (f j) (f i) = xor (f j) false = f j
    have hxor : xor (f j) (f i) = f j := by simp [hfi]
    rw [hxor]
    -- update f j (f j) = f
    have h_id : update f j (f j) = f := by
      funext k
      simp [update]
      intro hkj; rw [hkj]
    rw [h_id]

/-! ## T gate: diagonal phase, no superposition

    `tMatrix = !![1, 0; 0, exp(i·π/4)]`. Acting on a basis state, T leaves
    it unchanged with a phase factor of `exp(i·π/4)` if the qubit is `|1⟩`,
    or `1` (no phase) if `|0⟩`. -/

theorem tMatrix_apply (i j : Fin 2) :
    tMatrix i j
      = (if i = j then (if i = 1 then Complex.exp (Complex.I * (Real.pi / 4)) else 1) else 0) := by
  fin_cases i <;> fin_cases j <;> simp [tMatrix]

/-- `pad_u dim n tMatrix` acting on a `padEquiv`-coordinated basis state:
    leaves the state unchanged, multiplied by the T-phase factor at qubit `n`. -/
theorem pad_u_T_on_basis_vector_padEquiv {dim n : Nat} (h : n < dim)
    (kH : Fin (2^n)) (kM : Fin 2) (kL : Fin (2^(dim-n-1))) :
    pad_u dim n tMatrix * basis_vector (2^dim)
        (padEquiv dim n h ((kH, kM), kL)).val
      = (if kM = 1 then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
        • basis_vector (2^dim) (padEquiv dim n h ((kH, kM), kL)).val := by
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hr⟩ : ∃ x, padEquiv dim n h x = r :=
    ⟨(padEquiv dim n h).symm r, (padEquiv dim n h).apply_symm_apply r⟩
  rw [← hr]
  rw [pad_u_basis_vector_entry h tMatrix kH kM kL rH rM rL]
  rw [tMatrix_apply]
  simp only [basis_vector_apply, Matrix.smul_apply, smul_eq_mul]
  have h_iff : (padEquiv dim n h ((rH, rM), rL)).val =
               (padEquiv dim n h ((kH, kM), kL)).val
             ↔ (rH = kH ∧ rM = kM ∧ rL = kL) := by
    rw [padEquiv_val_eq_iff]
    simp [Prod.mk.injEq, and_assoc]
  simp only [h_iff]
  by_cases h1 : rH = kH <;> by_cases h2 : rM = kM <;> by_cases h3 : rL = kL <;>
    simp [h1, h2, h3]

/-- `pad_u dim n tMatrix` on `f_to_vec dim f`: phase-multiplies by `e^(iπ/4)`
    if `f n` is true, else leaves unchanged.

    Faithful translation of SQIR `f_to_vec_T` from `UnitaryOps.v`. -/
theorem f_to_vec_T_proved (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    pad_u dim n tMatrix * f_to_vec dim f
      = (if f n then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
        • f_to_vec dim f := by
  rw [f_to_vec_eq_basis_padEquiv dim n h f]
  rw [pad_u_T_on_basis_vector_padEquiv h]
  -- Both sides have the same basis vector; only the scalar differs.
  -- kM = ⟨if f n then 1 else 0, _⟩, so kM = 1 ↔ f n.
  have h_kM_eq_one : ((⟨if f n then 1 else 0, by split_ifs <;> omega⟩ : Fin 2) = 1)
                       ↔ (f n = true) := by
    cases h_fn : f n
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
  simp only [h_kM_eq_one]

/-! ## Generic Rz(θ) entry formula -/

/-- Entry formula for `rotation 0 0 θ` (the Rz(θ) gate). Diagonal with
    entries 1 (at |0⟩) and exp(θ·i) (at |1⟩). Generalizes T, S, Z, T†, S†
    entry formulas. -/
theorem rotation_Rz_apply (θ : ℝ) (i j : Fin 2) :
    rotation 0 0 θ i j
      = (if i = j then (if i = 1 then Complex.exp ((θ : ℂ) * Complex.I) else 1) else 0) := by
  unfold rotation
  fin_cases i <;> fin_cases j <;> simp

/-! ## Generic Rz(θ) action on basis state -/

/-- `pad_u dim n (rotation 0 0 θ)` acting on a `padEquiv`-coordinated basis state:
    diagonal phase `exp(θ·i)` if middle bit is 1, else 1.
    Generalizes pad_u_T/Z/S_on_basis_vector_padEquiv. -/
theorem pad_u_Rz_on_basis_vector_padEquiv {dim n : Nat} (h : n < dim) (θ : ℝ)
    (kH : Fin (2^n)) (kM : Fin 2) (kL : Fin (2^(dim-n-1))) :
    pad_u dim n (rotation 0 0 θ) * basis_vector (2^dim)
        (padEquiv dim n h ((kH, kM), kL)).val
      = (if kM = 1 then Complex.exp ((θ : ℂ) * Complex.I) else 1)
        • basis_vector (2^dim) (padEquiv dim n h ((kH, kM), kL)).val := by
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hr⟩ : ∃ x, padEquiv dim n h x = r :=
    ⟨(padEquiv dim n h).symm r, (padEquiv dim n h).apply_symm_apply r⟩
  rw [← hr]
  rw [pad_u_basis_vector_entry h (rotation 0 0 θ) kH kM kL rH rM rL]
  rw [rotation_Rz_apply]
  simp only [basis_vector_apply, Matrix.smul_apply, smul_eq_mul]
  have h_iff : (padEquiv dim n h ((rH, rM), rL)).val =
               (padEquiv dim n h ((kH, kM), kL)).val
             ↔ (rH = kH ∧ rM = kM ∧ rL = kL) := by
    rw [padEquiv_val_eq_iff]
    simp [Prod.mk.injEq, and_assoc]
  simp only [h_iff]
  by_cases h1 : rH = kH <;> by_cases h2 : rM = kM <;> by_cases h3 : rL = kL <;>
    simp [h1, h2, h3]

/-- `pad_u dim n (rotation 0 0 θ)` on `f_to_vec dim f`: phase-multiplies by
    `exp(θ·i)` if `f n` is true, else leaves unchanged.
    Unifies f_to_vec_T/Z/S/TDAG/SDAG_proved at arbitrary θ. -/
theorem f_to_vec_Rz_proved (dim n : Nat) (h : n < dim) (θ : ℝ) (f : Nat → Bool) :
    pad_u dim n (rotation 0 0 θ) * f_to_vec dim f
      = (if f n then Complex.exp ((θ : ℂ) * Complex.I) else 1) • f_to_vec dim f := by
  rw [f_to_vec_eq_basis_padEquiv dim n h f]
  rw [pad_u_Rz_on_basis_vector_padEquiv h]
  have h_kM_eq_one : ((⟨if f n then 1 else 0, by split_ifs <;> omega⟩ : Fin 2) = 1)
                       ↔ (f n = true) := by
    cases h_fn : f n
    · simp
    · simp
  simp only [h_kM_eq_one]

/-- SQIR-faithful uc_eval form of `f_to_vec_Rz`. Generalizes
    f_to_vec_T/Z/S/TDAG/SDAG_uc_eval. -/
theorem f_to_vec_Rz_uc_eval (dim n : Nat) (h : n < dim) (θ : ℝ) (f : Nat → Bool) :
    uc_eval (BaseUCom.Rz θ n : BaseUCom dim) * f_to_vec dim f
      = (if f n then Complex.exp ((θ : ℂ) * Complex.I) else 1) • f_to_vec dim f := by
  show pad_u dim n (rotation 0 0 θ) * f_to_vec dim f = _
  exact f_to_vec_Rz_proved dim n h θ f

/-! ## SKIP / ID: no-op identity -/

/-- SKIP applied to any state is the identity. -/
theorem f_to_vec_SKIP_uc_eval {dim : Nat} (h : 0 < dim) (f : Nat → Bool) :
    uc_eval (BaseUCom.SKIP : BaseUCom dim) * f_to_vec dim f = f_to_vec dim f := by
  show pad_u dim 0 (rotation 0 0 0) * f_to_vec dim f = f_to_vec dim f
  rw [rotation_I, pad_u_id h, Matrix.one_mul]

/-- The matrix semantics of `ID n` is the identity matrix when `n < dim`. -/
theorem ID_uc_eval_eq_one {dim n : Nat} (h : n < dim) :
    uc_eval (BaseUCom.ID n : BaseUCom dim) = (1 : Square dim) := by
  show pad_u dim n (rotation 0 0 0) = 1
  rw [rotation_I, pad_u_id h]

/-- `ID n` applied to any state is identity. -/
theorem f_to_vec_ID {dim n : Nat} (h : n < dim) (f : Nat → Bool) :
    uc_eval (BaseUCom.ID n : BaseUCom dim) * f_to_vec dim f = f_to_vec dim f := by
  rw [ID_uc_eval_eq_one h, Matrix.one_mul]

/-! ## Pauli Z gate: diagonal sign flip on |1⟩ -/

/-- Entry formula for `σz`. -/
theorem σz_apply (i j : Fin 2) :
    σz i j = (if i = j then (if i = 1 then (-1 : ℂ) else 1) else 0) := by
  fin_cases i <;> fin_cases j <;> simp [σz]

theorem pad_u_Z_on_basis_vector_padEquiv {dim n : Nat} (h : n < dim)
    (kH : Fin (2^n)) (kM : Fin 2) (kL : Fin (2^(dim-n-1))) :
    pad_u dim n σz * basis_vector (2^dim)
        (padEquiv dim n h ((kH, kM), kL)).val
      = (if kM = 1 then (-1 : ℂ) else 1)
        • basis_vector (2^dim) (padEquiv dim n h ((kH, kM), kL)).val := by
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hr⟩ : ∃ x, padEquiv dim n h x = r :=
    ⟨(padEquiv dim n h).symm r, (padEquiv dim n h).apply_symm_apply r⟩
  rw [← hr]
  rw [pad_u_basis_vector_entry h σz kH kM kL rH rM rL]
  rw [σz_apply]
  simp only [basis_vector_apply, Matrix.smul_apply, smul_eq_mul]
  have h_iff : (padEquiv dim n h ((rH, rM), rL)).val =
               (padEquiv dim n h ((kH, kM), kL)).val
             ↔ (rH = kH ∧ rM = kM ∧ rL = kL) := by
    rw [padEquiv_val_eq_iff]
    simp [Prod.mk.injEq, and_assoc]
  simp only [h_iff]
  by_cases h1 : rH = kH <;> by_cases h2 : rM = kM <;> by_cases h3 : rL = kL <;>
    simp [h1, h2, h3]

/-- `pad_u dim n σz` on `f_to_vec dim f`: sign flip if `f n` is true.

    Faithful translation of SQIR `f_to_vec_Z` from `UnitaryOps.v`. -/
theorem f_to_vec_Z_proved (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    pad_u dim n σz * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [f_to_vec_eq_basis_padEquiv dim n h f]
  rw [pad_u_Z_on_basis_vector_padEquiv h]
  have h_kM_eq_one : ((⟨if f n then 1 else 0, by split_ifs <;> omega⟩ : Fin 2) = 1)
                       ↔ (f n = true) := by
    cases h_fn : f n
    · simp
    · simp
  simp only [h_kM_eq_one]

/-- SQIR-faithful form of `f_to_vec_Z`. -/
theorem f_to_vec_Z_uc_eval (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (BaseUCom.Z n : BaseUCom dim) * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  show pad_u dim n (rotation 0 0 Real.pi) * f_to_vec dim f = _
  rw [rotation_Z]
  exact f_to_vec_Z_proved dim n h f

/-! ## S gate: diagonal phase i on |1⟩ -/

theorem sMatrix_apply (i j : Fin 2) :
    sMatrix i j = (if i = j then (if i = 1 then Complex.I else 1) else 0) := by
  fin_cases i <;> fin_cases j <;> simp [sMatrix]

theorem pad_u_S_on_basis_vector_padEquiv {dim n : Nat} (h : n < dim)
    (kH : Fin (2^n)) (kM : Fin 2) (kL : Fin (2^(dim-n-1))) :
    pad_u dim n sMatrix * basis_vector (2^dim)
        (padEquiv dim n h ((kH, kM), kL)).val
      = (if kM = 1 then Complex.I else 1)
        • basis_vector (2^dim) (padEquiv dim n h ((kH, kM), kL)).val := by
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hr⟩ : ∃ x, padEquiv dim n h x = r :=
    ⟨(padEquiv dim n h).symm r, (padEquiv dim n h).apply_symm_apply r⟩
  rw [← hr]
  rw [pad_u_basis_vector_entry h sMatrix kH kM kL rH rM rL]
  rw [sMatrix_apply]
  simp only [basis_vector_apply, Matrix.smul_apply, smul_eq_mul]
  have h_iff : (padEquiv dim n h ((rH, rM), rL)).val =
               (padEquiv dim n h ((kH, kM), kL)).val
             ↔ (rH = kH ∧ rM = kM ∧ rL = kL) := by
    rw [padEquiv_val_eq_iff]
    simp [Prod.mk.injEq, and_assoc]
  simp only [h_iff]
  by_cases h1 : rH = kH <;> by_cases h2 : rM = kM <;> by_cases h3 : rL = kL <;>
    simp [h1, h2, h3]

/-- `pad_u dim n sMatrix` on `f_to_vec dim f`: phase factor `i` if `f n` is true.
    Faithful translation of SQIR `f_to_vec_S`. -/
theorem f_to_vec_S_proved (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    pad_u dim n sMatrix * f_to_vec dim f
      = (if f n then Complex.I else 1) • f_to_vec dim f := by
  rw [f_to_vec_eq_basis_padEquiv dim n h f]
  rw [pad_u_S_on_basis_vector_padEquiv h]
  have h_kM_eq_one : ((⟨if f n then 1 else 0, by split_ifs <;> omega⟩ : Fin 2) = 1)
                       ↔ (f n = true) := by
    cases h_fn : f n
    · simp
    · simp
  simp only [h_kM_eq_one]

/-- SQIR-faithful form of `f_to_vec_S`. -/
theorem f_to_vec_S_uc_eval (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (BaseUCom.S n : BaseUCom dim) * f_to_vec dim f
      = (if f n then Complex.I else 1) • f_to_vec dim f := by
  show pad_u dim n (rotation 0 0 (Real.pi / 2)) * f_to_vec dim f = _
  rw [rotation_S]
  exact f_to_vec_S_proved dim n h f

/-! ## S† gate: diagonal phase -i on |1⟩ -/

/-- The S†-gate matrix: `!![1, 0; 0, -I]`. -/
noncomputable def sdagMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -Complex.I]

/-- `rotation 0 0 (-π/2) = sdagMatrix`. -/
theorem rotation_SDAG : rotation 0 0 (-(Real.pi / 2)) = sdagMatrix := by
  unfold rotation sdagMatrix
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  -- residue: cexp (-(↑Real.pi / 2 * I)) = -I
  rw [show -((Real.pi : ℂ) / 2 * I) = -((Real.pi : ℂ) / 2 * I) from rfl]
  rw [Complex.exp_neg]
  rw [show ((Real.pi : ℂ) / 2 * I) = ((Real.pi : ℂ) / 2) * I from rfl]
  rw [Complex.exp_pi_div_two_mul_I]
  exact Complex.inv_I

theorem sdagMatrix_apply (i j : Fin 2) :
    sdagMatrix i j = (if i = j then (if i = 1 then -Complex.I else 1) else 0) := by
  fin_cases i <;> fin_cases j <;> simp [sdagMatrix]

theorem pad_u_SDAG_on_basis_vector_padEquiv {dim n : Nat} (h : n < dim)
    (kH : Fin (2^n)) (kM : Fin 2) (kL : Fin (2^(dim-n-1))) :
    pad_u dim n sdagMatrix * basis_vector (2^dim)
        (padEquiv dim n h ((kH, kM), kL)).val
      = (if kM = 1 then -Complex.I else 1)
        • basis_vector (2^dim) (padEquiv dim n h ((kH, kM), kL)).val := by
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hr⟩ : ∃ x, padEquiv dim n h x = r :=
    ⟨(padEquiv dim n h).symm r, (padEquiv dim n h).apply_symm_apply r⟩
  rw [← hr]
  rw [pad_u_basis_vector_entry h sdagMatrix kH kM kL rH rM rL]
  rw [sdagMatrix_apply]
  simp only [basis_vector_apply, Matrix.smul_apply, smul_eq_mul]
  have h_iff : (padEquiv dim n h ((rH, rM), rL)).val =
               (padEquiv dim n h ((kH, kM), kL)).val
             ↔ (rH = kH ∧ rM = kM ∧ rL = kL) := by
    rw [padEquiv_val_eq_iff]
    simp [Prod.mk.injEq, and_assoc]
  simp only [h_iff]
  by_cases h1 : rH = kH <;> by_cases h2 : rM = kM <;> by_cases h3 : rL = kL <;>
    simp [h1, h2, h3]

theorem f_to_vec_SDAG_proved (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    pad_u dim n sdagMatrix * f_to_vec dim f
      = (if f n then -Complex.I else 1) • f_to_vec dim f := by
  rw [f_to_vec_eq_basis_padEquiv dim n h f]
  rw [pad_u_SDAG_on_basis_vector_padEquiv h]
  have h_kM_eq_one : ((⟨if f n then 1 else 0, by split_ifs <;> omega⟩ : Fin 2) = 1)
                       ↔ (f n = true) := by
    cases h_fn : f n
    · simp
    · simp
  simp only [h_kM_eq_one]

theorem f_to_vec_SDAG_uc_eval (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (BaseUCom.SDAG n : BaseUCom dim) * f_to_vec dim f
      = (if f n then -Complex.I else 1) • f_to_vec dim f := by
  show pad_u dim n (rotation 0 0 (-(Real.pi / 2))) * f_to_vec dim f = _
  rw [rotation_SDAG]
  exact f_to_vec_SDAG_proved dim n h f

/-! ## T† gate: diagonal phase exp(-i·π/4), no superposition

    Mirrors T but with negative phase. Faithful translation of SQIR's
    `UnitaryOps.v f_to_vec_TDAG`. -/

/-- The T†-gate matrix: `!![1, 0; 0, exp(-i·π/4)]`. -/
noncomputable def tdagMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (-(Complex.I * (Real.pi / 4)))]

theorem tdagMatrix_apply (i j : Fin 2) :
    tdagMatrix i j
      = (if i = j then (if i = 1 then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1) else 0) := by
  fin_cases i <;> fin_cases j <;> simp [tdagMatrix]

theorem pad_u_TDAG_on_basis_vector_padEquiv {dim n : Nat} (h : n < dim)
    (kH : Fin (2^n)) (kM : Fin 2) (kL : Fin (2^(dim-n-1))) :
    pad_u dim n tdagMatrix * basis_vector (2^dim)
        (padEquiv dim n h ((kH, kM), kL)).val
      = (if kM = 1 then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
        • basis_vector (2^dim) (padEquiv dim n h ((kH, kM), kL)).val := by
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hr⟩ : ∃ x, padEquiv dim n h x = r :=
    ⟨(padEquiv dim n h).symm r, (padEquiv dim n h).apply_symm_apply r⟩
  rw [← hr]
  rw [pad_u_basis_vector_entry h tdagMatrix kH kM kL rH rM rL]
  rw [tdagMatrix_apply]
  simp only [basis_vector_apply, Matrix.smul_apply, smul_eq_mul]
  have h_iff : (padEquiv dim n h ((rH, rM), rL)).val =
               (padEquiv dim n h ((kH, kM), kL)).val
             ↔ (rH = kH ∧ rM = kM ∧ rL = kL) := by
    rw [padEquiv_val_eq_iff]
    simp [Prod.mk.injEq, and_assoc]
  simp only [h_iff]
  by_cases h1 : rH = kH <;> by_cases h2 : rM = kM <;> by_cases h3 : rL = kL <;>
    simp [h1, h2, h3]

/-- `pad_u dim n tdagMatrix` on `f_to_vec dim f`: phase-multiplies by
    `e^(-i·π/4)` if `f n` is true, else leaves unchanged.

    Faithful translation of SQIR `f_to_vec_TDAG` from `UnitaryOps.v`. -/
theorem f_to_vec_TDAG_proved (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    pad_u dim n tdagMatrix * f_to_vec dim f
      = (if f n then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
        • f_to_vec dim f := by
  rw [f_to_vec_eq_basis_padEquiv dim n h f]
  rw [pad_u_TDAG_on_basis_vector_padEquiv h]
  have h_kM_eq_one : ((⟨if f n then 1 else 0, by split_ifs <;> omega⟩ : Fin 2) = 1)
                       ↔ (f n = true) := by
    cases h_fn : f n
    · simp
    · simp
  simp only [h_kM_eq_one]

/-! ## H gate: produces a superposition of two basis states

    Hadamard `H = (1/√2) !![1, 1; 1, -1]` has the property:
    `H |0⟩ = (1/√2)(|0⟩ + |1⟩)`, `H |1⟩ = (1/√2)(|0⟩ - |1⟩)`.

    Acting on `f_to_vec dim f`, the result is a sum of two basis states:
    one with `f n` flipped to `false`, one with `f n` flipped to `true`,
    with phases dictated by `(-1)^(f n)` on the second term.

    Faithful translation of SQIR `UnitaryOps.v f_to_vec_H`. -/

theorem hMatrix_apply (i j : Fin 2) :
    hMatrix i j
      = (if i = 1 ∧ j = 1 then -(Real.sqrt 2 / 2 : ℂ) else (Real.sqrt 2 / 2 : ℂ)) := by
  fin_cases i <;> fin_cases j <;> simp [hMatrix]

/-- `pad_u dim n hMatrix` acting on a `padEquiv`-coordinated basis state:
    produces a sum of two basis states (`mid = 0` and `mid = 1`) with
    Hadamard coefficients. -/
theorem pad_u_H_on_basis_vector_padEquiv {dim n : Nat} (h : n < dim)
    (kH : Fin (2^n)) (kM : Fin 2) (kL : Fin (2^(dim-n-1))) :
    pad_u dim n hMatrix * basis_vector (2^dim)
        (padEquiv dim n h ((kH, kM), kL)).val
      = ((Real.sqrt 2 / 2 : ℂ))
          • basis_vector (2^dim) (padEquiv dim n h ((kH, (0 : Fin 2)), kL)).val
        + ((if kM = 1 then (-1 : ℂ) else 1) * (Real.sqrt 2 / 2 : ℂ))
          • basis_vector (2^dim) (padEquiv dim n h ((kH, (1 : Fin 2)), kL)).val := by
  ext r jj
  have hj : jj = 0 := Subsingleton.elim _ _
  subst hj
  obtain ⟨⟨⟨rH, rM⟩, rL⟩, hr⟩ : ∃ x, padEquiv dim n h x = r :=
    ⟨(padEquiv dim n h).symm r, (padEquiv dim n h).apply_symm_apply r⟩
  rw [← hr]
  rw [pad_u_basis_vector_entry h hMatrix kH kM kL rH rM rL]
  rw [hMatrix_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, basis_vector_apply, smul_eq_mul]
  have h_iff_0 : (padEquiv dim n h ((rH, rM), rL)).val =
                 (padEquiv dim n h ((kH, (0 : Fin 2)), kL)).val
               ↔ (rH = kH ∧ rM = (0 : Fin 2) ∧ rL = kL) := by
    rw [padEquiv_val_eq_iff]; simp [Prod.mk.injEq, and_assoc]
  have h_iff_1 : (padEquiv dim n h ((rH, rM), rL)).val =
                 (padEquiv dim n h ((kH, (1 : Fin 2)), kL)).val
               ↔ (rH = kH ∧ rM = (1 : Fin 2) ∧ rL = kL) := by
    rw [padEquiv_val_eq_iff]; simp [Prod.mk.injEq, and_assoc]
  simp only [h_iff_0, h_iff_1]
  by_cases h1 : rH = kH
  · by_cases h3 : rL = kL
    · -- rH=kH, rL=kL: only the middle bit case-analysis remains
      subst h1; subst h3
      fin_cases rM <;> fin_cases kM <;> simp <;> ring
    · simp [h1, h3]
  · simp [h1]

/-! ## f-coordinate `f_to_vec_H` -/

/-- `f_to_vec dim (update f n false)` in `padEquiv` form (middle bit = 0). -/
theorem f_to_vec_update_false_eq_padEquiv (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    f_to_vec dim (update f n false) = basis_vector (2^dim)
        (padEquiv dim n h ((⟨funbool_to_nat n f, funbool_to_nat_lt n f⟩,
                            (0 : Fin 2)),
                           ⟨funbool_to_nat (dim-n-1) (fun p => f (p+n+1)),
                            funbool_to_nat_lt _ _⟩)).val := by
  unfold f_to_vec
  congr 1
  rw [padEquiv_val_formula]
  rw [funbool_to_nat_update_eq dim n h f false]
  simp

/-- `f_to_vec dim (update f n true)` in `padEquiv` form (middle bit = 1). -/
theorem f_to_vec_update_true_eq_padEquiv (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    f_to_vec dim (update f n true) = basis_vector (2^dim)
        (padEquiv dim n h ((⟨funbool_to_nat n f, funbool_to_nat_lt n f⟩,
                            (1 : Fin 2)),
                           ⟨funbool_to_nat (dim-n-1) (fun p => f (p+n+1)),
                            funbool_to_nat_lt _ _⟩)).val := by
  unfold f_to_vec
  congr 1
  rw [padEquiv_val_formula]
  rw [funbool_to_nat_update_eq dim n h f true]
  simp

/-- `pad_u dim n hMatrix` on `f_to_vec dim f`: produces a sum of two basis
    states (n flipped to false, n flipped to true) with Hadamard weights.

    Faithful translation of SQIR `f_to_vec_H` from `UnitaryOps.v`. -/
theorem f_to_vec_H_proved (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    pad_u dim n hMatrix * f_to_vec dim f
      = (Real.sqrt 2 / 2 : ℂ) • f_to_vec dim (update f n false)
        + ((if f n then (-1 : ℂ) else 1) * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f n true) := by
  rw [f_to_vec_eq_basis_padEquiv dim n h f]
  rw [pad_u_H_on_basis_vector_padEquiv h]
  rw [← f_to_vec_update_false_eq_padEquiv dim n h f]
  rw [← f_to_vec_update_true_eq_padEquiv dim n h f]
  -- Convert (kM = 1) condition to (f n = true)
  have h_kM_eq_one : ((⟨if f n then 1 else 0, by split_ifs <;> omega⟩ : Fin 2) = 1)
                       ↔ (f n = true) := by
    cases h_fn : f n
    · simp
    · simp
  simp only [h_kM_eq_one]

/-! ## `uc_eval`-bridge: align per-gate `f_to_vec_*` with SQIR's
    `uc_eval (BaseUCom.X n) * f_to_vec dim f` form.

    Lifts `pad_u dim n {tMatrix, tdagMatrix, hMatrix}` to
    `uc_eval (BaseUCom.{T, TDAG, H} n)`. -/

/-- `rotation 0 0 (-π/4) = tdagMatrix`. Mirrors `rotation_T`. -/
theorem rotation_TDAG : rotation 0 0 (-(Real.pi / 4)) = tdagMatrix := by
  unfold rotation tdagMatrix
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    rw [show ((Real.pi : ℂ) / 4) * I = I * ((Real.pi : ℂ) / 4) from mul_comm _ _]

/-! ## Phase-gate σz commutation corollaries.
    All Z-rotations commute with σz; the four phase gates T, T†, S, S†
    are special cases of `rotation_Rz_commutes_σz`. -/

/-- `T · σz = σz · T`. Phase commutes with Pauli Z. -/
theorem tMatrix_commutes_σz : tMatrix * σz = σz * tMatrix := by
  rw [← rotation_T]; exact rotation_Rz_commutes_σz _

/-- `S · σz = σz · S`. -/
theorem sMatrix_commutes_σz : sMatrix * σz = σz * sMatrix := by
  rw [← rotation_S]; exact rotation_Rz_commutes_σz _

/-- `T† · σz = σz · T†`. -/
theorem tdagMatrix_commutes_σz : tdagMatrix * σz = σz * tdagMatrix := by
  rw [← rotation_TDAG]; exact rotation_Rz_commutes_σz _

/-- `S† · σz = σz · S†`. -/
theorem sdagMatrix_commutes_σz : sdagMatrix * σz = σz * sdagMatrix := by
  rw [← rotation_SDAG]; exact rotation_Rz_commutes_σz _

/-- `T · S = S · T`. Phase gates commute with each other. Two-line corollary
    of `rotation_Rz_commutes`. -/
theorem tMatrix_commutes_sMatrix : tMatrix * sMatrix = sMatrix * tMatrix := by
  rw [← rotation_T, ← rotation_S]; exact rotation_Rz_commutes _ _

/-- `T · S† = S† · T`. -/
theorem tMatrix_commutes_sdagMatrix : tMatrix * sdagMatrix = sdagMatrix * tMatrix := by
  rw [← rotation_T, ← rotation_SDAG]; exact rotation_Rz_commutes _ _

/-- `T† · S = S · T†`. -/
theorem tdagMatrix_commutes_sMatrix : tdagMatrix * sMatrix = sMatrix * tdagMatrix := by
  rw [← rotation_TDAG, ← rotation_S]; exact rotation_Rz_commutes _ _

/-- `T† · S† = S† · T†`. -/
theorem tdagMatrix_commutes_sdagMatrix :
    tdagMatrix * sdagMatrix = sdagMatrix * tdagMatrix := by
  rw [← rotation_TDAG, ← rotation_SDAG]; exact rotation_Rz_commutes _ _

/-- Circuit equivalence: `T q ; S q ≡ S q ; T q`. Phase gates commute. -/
theorem T_S_eq_S_T {dim n : Nat} :
    uc_eval (UCom.seq (BaseUCom.T n : BaseUCom dim) (BaseUCom.S n))
      = uc_eval (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.T n)) := by
  show pad_u dim n (rotation 0 0 (Real.pi / 2))
        * pad_u dim n (rotation 0 0 (Real.pi / 4))
       = pad_u dim n (rotation 0 0 (Real.pi / 4))
         * pad_u dim n (rotation 0 0 (Real.pi / 2))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_T, rotation_S,
      tMatrix_commutes_sMatrix]

/-- Circuit equivalence: `T q ; S† q ≡ S† q ; T q`. -/
theorem T_SDAG_eq_SDAG_T {dim n : Nat} :
    uc_eval (UCom.seq (BaseUCom.T n : BaseUCom dim) (BaseUCom.SDAG n))
      = uc_eval (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.T n)) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
        * pad_u dim n (rotation 0 0 (Real.pi / 4))
       = pad_u dim n (rotation 0 0 (Real.pi / 4))
         * pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_T, rotation_SDAG,
      tMatrix_commutes_sdagMatrix]

/-- Circuit equivalence: `T† q ; S q ≡ S q ; T† q`. -/
theorem TDAG_S_eq_S_TDAG {dim n : Nat} :
    uc_eval (UCom.seq (BaseUCom.TDAG n : BaseUCom dim) (BaseUCom.S n))
      = uc_eval (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.TDAG n)) := by
  show pad_u dim n (rotation 0 0 (Real.pi / 2))
        * pad_u dim n (rotation 0 0 (-(Real.pi / 4)))
       = pad_u dim n (rotation 0 0 (-(Real.pi / 4)))
         * pad_u dim n (rotation 0 0 (Real.pi / 2))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_TDAG, rotation_S,
      tdagMatrix_commutes_sMatrix]

/-- Circuit equivalence: `T† q ; S† q ≡ S† q ; T† q`. -/
theorem TDAG_SDAG_eq_SDAG_TDAG {dim n : Nat} :
    uc_eval (UCom.seq (BaseUCom.TDAG n : BaseUCom dim) (BaseUCom.SDAG n))
      = uc_eval (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.TDAG n)) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
        * pad_u dim n (rotation 0 0 (-(Real.pi / 4)))
       = pad_u dim n (rotation 0 0 (-(Real.pi / 4)))
         * pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_TDAG, rotation_SDAG,
      tdagMatrix_commutes_sdagMatrix]

/-- Circuit equivalence: `Z q ; S q ≡ S q ; Z q`. Z and S are both Z-axis
    rotations and commute. -/
theorem Z_S_eq_S_Z {dim n : Nat} :
    uc_eval (UCom.seq (BaseUCom.Z n : BaseUCom dim) (BaseUCom.S n))
      = uc_eval (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.Z n)) := by
  show pad_u dim n (rotation 0 0 (Real.pi / 2)) * pad_u dim n (rotation 0 0 Real.pi)
       = pad_u dim n (rotation 0 0 Real.pi) * pad_u dim n (rotation 0 0 (Real.pi / 2))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_S, rotation_Z,
      sMatrix_commutes_σz]

/-- Circuit equivalence: `Z q ; T q ≡ T q ; Z q`. Z and T commute. -/
theorem Z_T_eq_T_Z {dim n : Nat} :
    uc_eval (UCom.seq (BaseUCom.Z n : BaseUCom dim) (BaseUCom.T n))
      = uc_eval (UCom.seq (BaseUCom.T n : BaseUCom dim) (BaseUCom.Z n)) := by
  show pad_u dim n (rotation 0 0 (Real.pi / 4)) * pad_u dim n (rotation 0 0 Real.pi)
       = pad_u dim n (rotation 0 0 Real.pi) * pad_u dim n (rotation 0 0 (Real.pi / 4))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_T, rotation_Z,
      tMatrix_commutes_σz]

/-- Circuit equivalence: `Z q ; S† q ≡ S† q ; Z q`. -/
theorem Z_SDAG_eq_SDAG_Z {dim n : Nat} :
    uc_eval (UCom.seq (BaseUCom.Z n : BaseUCom dim) (BaseUCom.SDAG n))
      = uc_eval (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.Z n)) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi / 2))) * pad_u dim n (rotation 0 0 Real.pi)
       = pad_u dim n (rotation 0 0 Real.pi) * pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_SDAG, rotation_Z,
      sdagMatrix_commutes_σz]

/-- Circuit equivalence: `Z q ; T† q ≡ T† q ; Z q`. -/
theorem Z_TDAG_eq_TDAG_Z {dim n : Nat} :
    uc_eval (UCom.seq (BaseUCom.Z n : BaseUCom dim) (BaseUCom.TDAG n))
      = uc_eval (UCom.seq (BaseUCom.TDAG n : BaseUCom dim) (BaseUCom.Z n)) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi / 4))) * pad_u dim n (rotation 0 0 Real.pi)
       = pad_u dim n (rotation 0 0 Real.pi) * pad_u dim n (rotation 0 0 (-(Real.pi / 4)))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_TDAG, rotation_Z,
      tdagMatrix_commutes_σz]


/-- SQIR-faithful form of `f_to_vec_X` (Pauli X = bit flip).
    Translates SQIR `UnitaryOps.v f_to_vec_X`. -/
theorem f_to_vec_X_uc_eval (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (BaseUCom.X n : BaseUCom dim) * f_to_vec dim f
      = f_to_vec dim (update f n (!f n)) := by
  show pad_u dim n (rotation Real.pi 0 Real.pi) * f_to_vec dim f = _
  rw [rotation_X]
  exact pad_u_σx_on_f_to_vec dim n h f

/-- SQIR-faithful form of `f_to_vec_T`. -/
theorem f_to_vec_T_uc_eval (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (BaseUCom.T n : BaseUCom dim) * f_to_vec dim f
      = (if f n then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
        • f_to_vec dim f := by
  show pad_u dim n (rotation 0 0 (Real.pi / 4)) * f_to_vec dim f = _
  rw [rotation_T]
  exact f_to_vec_T_proved dim n h f

/-- SQIR-faithful form of `f_to_vec_TDAG`. -/
theorem f_to_vec_TDAG_uc_eval (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (BaseUCom.TDAG n : BaseUCom dim) * f_to_vec dim f
      = (if f n then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
        • f_to_vec dim f := by
  show pad_u dim n (rotation 0 0 (-(Real.pi / 4))) * f_to_vec dim f = _
  rw [rotation_TDAG]
  exact f_to_vec_TDAG_proved dim n h f

/-- SQIR-faithful form of `f_to_vec_H`. -/
theorem f_to_vec_H_uc_eval (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (BaseUCom.H n : BaseUCom dim) * f_to_vec dim f
      = (Real.sqrt 2 / 2 : ℂ) • f_to_vec dim (update f n false)
        + ((if f n then (-1 : ℂ) else 1) * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f n true) := by
  show pad_u dim n (rotation (Real.pi / 2) 0 Real.pi) * f_to_vec dim f = _
  rw [rotation_H]
  exact f_to_vec_H_proved dim n h f

/-! ## Sequence composition helpers

    For chaining `f_to_vec_*` through a multi-gate circuit
    (e.g., the 15-gate `CCX` decomposition). -/

/-- `uc_eval (UCom.seq c₁ c₂) = uc_eval c₂ * uc_eval c₁`. By definition,
    exposed as a `@[simp]` lemma so `simp [uc_eval_seq]` walks down a
    seq-tree. -/
@[simp] theorem uc_eval_seq {dim : Nat} (c₁ c₂ : BaseUCom dim) :
    uc_eval (UCom.seq c₁ c₂) = uc_eval c₂ * uc_eval c₁ := rfl

/-- Apply a `seq` to a state vector: c₁ first, then c₂.
    Useful for unrolling `(uc_eval (seq c₁ c₂)) * v` to
    `uc_eval c₂ * (uc_eval c₁ * v)` in proofs that step gate-by-gate. -/
theorem uc_eval_seq_mul {dim : Nat} (c₁ c₂ : BaseUCom dim)
    (v : Matrix (Fin (2^dim)) (Fin 1) ℂ) :
    uc_eval (UCom.seq c₁ c₂) * v = uc_eval c₂ * (uc_eval c₁ * v) := by
  rw [uc_eval_seq, Matrix.mul_assoc]

/-- Distribute a matrix product over a sum-of-state-vectors: `A * (v + w) = A*v + A*w`.
    The Hadamard introduces a sum, so chaining through later gates needs this. -/
theorem mul_add_state {dim : Nat} (A : Square dim)
    (v w : Matrix (Fin (2^dim)) (Fin 1) ℂ) :
    A * (v + w) = A * v + A * w :=
  Matrix.mul_add A v w

/-- Distribute a matrix product over a scalar-multiplied state vector:
    `A * (c • v) = c • (A * v)`. -/
theorem mul_smul_state {dim : Nat} (A : Square dim) (c : ℂ)
    (v : Matrix (Fin (2^dim)) (Fin 1) ℂ) :
    A * (c • v) = c • (A * v) :=
  Matrix.mul_smul A c v

/-! ## SWAP gate (3-CNOT chain swaps two qubits) -/

/-- `SWAP a b = CNOT a b; CNOT b a; CNOT a b` swaps the values at qubits a and b
    in any basis state. -/
theorem f_to_vec_SWAP (dim a b : Nat) (ha : a < dim) (hb : b < dim) (hab : a ≠ b)
    (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.CNOT a b : BaseUCom dim)
              (UCom.seq (BaseUCom.CNOT b a) (BaseUCom.CNOT a b)))
      * f_to_vec dim f
      = f_to_vec dim (update (update f a (f b)) b (f a)) := by
  rw [uc_eval_seq_mul, uc_eval_seq_mul]
  rw [f_to_vec_CNOT_proved dim a b f ha hb hab]
  rw [f_to_vec_CNOT_proved dim b a _ hb ha (Ne.symm hab)]
  rw [f_to_vec_CNOT_proved dim a b _ ha hb hab]
  congr 1
  funext k
  by_cases hka : k = a
  · by_cases hkb : k = b
    · exact absurd (hka.symm.trans hkb) hab
    · rw [hka]
      simp [update, hab, Ne.symm hab, hkb]
      cases f a <;> cases f b <;> rfl
  · by_cases hkb : k = b
    · rw [hkb]
      simp [update, hab, Ne.symm hab, hka]
    · simp [update, hka, hkb]

/-! ## Compositional identities at the f_to_vec level -/

/-- `Rz θ ; Rz θ'` on `f_to_vec dim f` adds the angles in the phase factor.
    f-coord version of SQIR's `Rz_Rz_add`. -/
theorem f_to_vec_Rz_Rz (dim n : Nat) (h : n < dim) (θ θ' : ℝ) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.Rz θ n : BaseUCom dim) (BaseUCom.Rz θ' n))
      * f_to_vec dim f
      = (if f n then Complex.exp (((θ + θ') : ℂ) * Complex.I) else 1) • f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_Rz_uc_eval dim n h θ f]
  rw [mul_smul_state]
  rw [f_to_vec_Rz_uc_eval dim n h θ' f]
  rw [smul_smul]
  congr 1
  by_cases hfn : f n
  · simp [hfn]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp [hfn]


/-- `X q ; X q` is identity on `f_to_vec dim f`.
    Mirrors SQIR's `X_X_id` at the f-coordinate level. -/
theorem f_to_vec_X_X (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.X n : BaseUCom dim) (BaseUCom.X n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_X_uc_eval dim n h f]
  rw [f_to_vec_X_uc_eval dim n h (update f n (!f n))]
  rw [show (update f n (!f n)) n = !f n from update_eq f n (!f n)]
  rw [show (!(!f n)) = f n from Bool.not_not (f n)]
  rw [update_idem]
  exact congrArg (f_to_vec dim) (update_self f n)

/-- `X q ; X q ; X q` acts as a single X on `f_to_vec dim f` (X³ = X). -/
theorem f_to_vec_X_X_X (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.X n : BaseUCom dim) (BaseUCom.X n))
                       (BaseUCom.X n))
      * f_to_vec dim f
      = f_to_vec dim (update f n (!f n)) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_X_X dim n h f]
  exact f_to_vec_X_uc_eval dim n h f

/-- `X q ; X q ; X q ; X q` is identity on `f_to_vec dim f` (X⁴ = ID). -/
theorem f_to_vec_X_X_X_X (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.X n : BaseUCom dim) (BaseUCom.X n))
                       (BaseUCom.X n)) (BaseUCom.X n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_X_X_X dim n h f]
  rw [f_to_vec_X_uc_eval dim n h _]
  rw [show (update f n (!f n)) n = !f n from update_eq f n (!f n)]
  rw [show (!(!f n)) = f n from Bool.not_not (f n)]
  rw [update_idem]
  exact congrArg (f_to_vec dim) (update_self f n)


/-- `Z q ; Z q` is identity on `f_to_vec dim f`.
    Z's two phase factors `(if f n then -1 else 1)` multiply to 1. -/
theorem f_to_vec_Z_Z (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.Z n : BaseUCom dim) (BaseUCom.Z n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_Z_uc_eval dim n h f]
  rw [mul_smul_state]
  rw [f_to_vec_Z_uc_eval dim n h f]
  rw [smul_smul]
  by_cases hfn : f n
  · simp [hfn]
  · simp [hfn]

/-- `S q ; S q` acts as Z on `f_to_vec dim f` (since S² = Z). Combines
    `S_S_eq_Z` (UnitarySem.lean) with `f_to_vec_Z_uc_eval`. -/
theorem f_to_vec_S_S (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
      * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [show uc_eval (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
        = uc_eval (BaseUCom.Z n : BaseUCom dim) from S_S_eq_Z n]
  exact f_to_vec_Z_uc_eval dim n h f

/-- `Z q ; Z q ; Z q` acts as Z on `f_to_vec dim f` (Z³ = Z). -/
theorem f_to_vec_Z_Z_Z (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.Z n : BaseUCom dim) (BaseUCom.Z n))
                       (BaseUCom.Z n))
      * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_Z_Z dim n h f]
  exact f_to_vec_Z_uc_eval dim n h f

/-- `Z q ; Z q ; Z q ; Z q` is identity on `f_to_vec dim f` (Z⁴ = ID). -/
theorem f_to_vec_Z_Z_Z_Z (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.Z n : BaseUCom dim) (BaseUCom.Z n))
                       (BaseUCom.Z n)) (BaseUCom.Z n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_Z_Z_Z dim n h f]
  rw [mul_smul_state]
  rw [f_to_vec_Z_uc_eval dim n h f]
  rw [smul_smul]
  by_cases hfn : f n
  · simp [hfn]
  · simp [hfn]


/-- `CNOT i j ; CNOT i j` is identity on `f_to_vec dim f` (CNOT is involutive).
    -- SQIR/SQIR/Equivalences.v line 109: CNOT_CNOT_id. -/
theorem f_to_vec_CNOT_CNOT (dim i j : Nat) (hi : i < dim) (hj : j < dim) (hij : i ≠ j)
    (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.CNOT i j : BaseUCom dim) (BaseUCom.CNOT i j))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CNOT_proved dim i j f hi hj hij]
  rw [f_to_vec_CNOT_proved dim i j _ hi hj hij]
  rw [show (update f j (xor (f j) (f i))) j = xor (f j) (f i)
        from update_eq f j (xor (f j) (f i))]
  rw [show (update f j (xor (f j) (f i))) i = f i from update_neq f j i _ hij]
  rw [update_idem]
  rw [show xor (xor (f j) (f i)) (f i) = f j from by
        rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]]
  exact congrArg (f_to_vec dim) (update_self f j)

/-- `CNOT i j ; CNOT i j ; CNOT i j` acts as a single CNOT on
    `f_to_vec dim f` (CNOT³ = CNOT, since CNOT² = ID).
    -- SQIR/SQIR/Equivalences.v line ~120: 3-chain CNOT identity. -/
theorem f_to_vec_CNOT_CNOT_CNOT (dim i j : Nat) (hi : i < dim) (hj : j < dim)
    (hij : i ≠ j) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.CNOT i j : BaseUCom dim) (BaseUCom.CNOT i j))
                       (BaseUCom.CNOT i j))
      * f_to_vec dim f
      = f_to_vec dim (update f j (xor (f j) (f i))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CNOT_CNOT dim i j hi hj hij f]
  exact f_to_vec_CNOT_proved dim i j f hi hj hij

/-- `S q ; S† q` is identity on `f_to_vec dim f`.
    Phase factors `i * -i = 1` on |1⟩. -/
theorem f_to_vec_S_SDAG (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.SDAG n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_S_uc_eval dim n h f]
  rw [mul_smul_state]
  rw [f_to_vec_SDAG_uc_eval dim n h f]
  rw [smul_smul]
  by_cases hfn : f n
  · simp [hfn, Complex.I_mul_I]
  · simp [hfn]

/-- `S† q ; S q` is identity (symmetric companion). -/
theorem f_to_vec_SDAG_S (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.S n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_SDAG_uc_eval dim n h f]
  rw [mul_smul_state]
  rw [f_to_vec_S_uc_eval dim n h f]
  rw [smul_smul]
  by_cases hfn : f n
  · simp [hfn, Complex.I_mul_I]
  · simp [hfn]

/-- `exp(iπ/4) * exp(-iπ/4) = 1` (inline version, used before exp_pi4_mul_exp_neg_pi4
    is declared). -/
private theorem exp_pi4_mul_exp_neg_pi4_aux :
    Complex.exp (Complex.I * (Real.pi / 4))
      * Complex.exp (-(Complex.I * (Real.pi / 4))) = 1 := by
  rw [← Complex.exp_add]
  rw [show Complex.I * (Real.pi / 4) + -(Complex.I * (Real.pi / 4)) = 0 from by ring]
  exact Complex.exp_zero

/-- `tMatrix * tdagMatrix = σi` (T and T† are inverses at the matrix level). -/
theorem tMatrix_mul_tdagMatrix : tMatrix * tdagMatrix = σi := by
  unfold tMatrix tdagMatrix σi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, exp_pi4_mul_exp_neg_pi4_aux]

/-- `tdagMatrix * tMatrix = σi`. -/
theorem tdagMatrix_mul_tMatrix : tdagMatrix * tMatrix = σi := by
  unfold tMatrix tdagMatrix σi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm, exp_pi4_mul_exp_neg_pi4_aux]

/-- `sMatrix * sdagMatrix = σi` (S and S† are inverses at the matrix level). -/
theorem sMatrix_mul_sdagMatrix : sMatrix * sdagMatrix = σi := by
  unfold sMatrix sdagMatrix σi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- `sdagMatrix * sMatrix = σi`. -/
theorem sdagMatrix_mul_sMatrix : sdagMatrix * sMatrix = σi := by
  unfold sMatrix sdagMatrix σi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- `sMatrix * sMatrix = σz` (S² = Z, since I² = -1). -/
theorem sMatrix_mul_sMatrix : sMatrix * sMatrix = σz := by
  unfold sMatrix σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-! ## Padded T/TDAG/S/SDAG mutual-inverse identities -/

/-- T followed by TDAG is the identity at the padded level. -/
theorem pad_u_tMatrix_tdagMatrix {dim n : Nat} (h : n < dim) :
    pad_u dim n tMatrix * pad_u dim n tdagMatrix = (1 : Square dim) :=
  pad_u_mul_inv h tdagMatrix tMatrix tMatrix_mul_tdagMatrix

/-- TDAG followed by T is the identity at the padded level. -/
theorem pad_u_tdagMatrix_tMatrix {dim n : Nat} (h : n < dim) :
    pad_u dim n tdagMatrix * pad_u dim n tMatrix = (1 : Square dim) :=
  pad_u_mul_inv h tMatrix tdagMatrix tdagMatrix_mul_tMatrix

/-- S followed by SDAG is the identity at the padded level. -/
theorem pad_u_sMatrix_sdagMatrix {dim n : Nat} (h : n < dim) :
    pad_u dim n sMatrix * pad_u dim n sdagMatrix = (1 : Square dim) :=
  pad_u_mul_inv h sdagMatrix sMatrix sMatrix_mul_sdagMatrix

/-- SDAG followed by S is the identity at the padded level. -/
theorem pad_u_sdagMatrix_sMatrix {dim n : Nat} (h : n < dim) :
    pad_u dim n sdagMatrix * pad_u dim n sMatrix = (1 : Square dim) :=
  pad_u_mul_inv h sMatrix sdagMatrix sdagMatrix_mul_sMatrix

/-- `sdagMatrix * sdagMatrix = σz` (S†² = Z, since (-I)² = -1). -/
theorem sdagMatrix_mul_sdagMatrix : sdagMatrix * sdagMatrix = σz := by
  unfold sdagMatrix σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- `S³ = S†`. The S gate has order 4: S² = Z, S³ = S† (its inverse). -/
theorem sMatrix_pow_three : sMatrix * sMatrix * sMatrix = sdagMatrix := by
  rw [sMatrix_mul_sMatrix]
  unfold sMatrix sdagMatrix σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `S†³ = S`. -/
theorem sdagMatrix_pow_three : sdagMatrix * sdagMatrix * sdagMatrix = sMatrix := by
  rw [sdagMatrix_mul_sdagMatrix]
  unfold sdagMatrix sMatrix σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Circuit equivalence: `S† q ; S† q ≡ Z q`. Lift of `sdagMatrix_mul_sdagMatrix`. -/
theorem SDAG_SDAG_eq_Z {dim n : Nat} :
    uc_eval (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.SDAG n))
      = uc_eval (BaseUCom.Z n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
        * pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
      = pad_u dim n (rotation 0 0 Real.pi)
  rw [pad_u_mul_pad_u, rotation_SDAG, sdagMatrix_mul_sdagMatrix, ← rotation_Z]

/-- `σz · S = S†` at the matrix level (since Z·diag(1,i) = diag(1,-i)). -/
theorem σz_mul_sMatrix : σz * sMatrix = sdagMatrix := by
  unfold σz sMatrix sdagMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `σz · S† = S` at the matrix level. -/
theorem σz_mul_sdagMatrix : σz * sdagMatrix = sMatrix := by
  unfold σz sMatrix sdagMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Padded version: `pad_u Z · pad_u S = pad_u S†`. -/
theorem pad_u_σz_mul_pad_u_sMatrix (dim n : Nat) :
    pad_u dim n σz * pad_u dim n sMatrix = pad_u dim n sdagMatrix := by
  rw [pad_u_mul_pad_u, σz_mul_sMatrix]

/-- Padded version: `pad_u Z · pad_u S† = pad_u S`. -/
theorem pad_u_σz_mul_pad_u_sdagMatrix (dim n : Nat) :
    pad_u dim n σz * pad_u dim n sdagMatrix = pad_u dim n sMatrix := by
  rw [pad_u_mul_pad_u, σz_mul_sdagMatrix]

/-- Circuit equivalence: `S q ; Z q ≡ S† q` — Z·S = S† via σz_mul_sMatrix. -/
theorem S_Z_eq_SDAG {dim n : Nat} :
    uc_eval (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.Z n))
      = uc_eval (BaseUCom.SDAG n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 Real.pi) * pad_u dim n (rotation 0 0 (Real.pi/2))
        = pad_u dim n (rotation 0 0 (-(Real.pi/2)))
  rw [rotation_S, rotation_Z, rotation_SDAG, pad_u_σz_mul_pad_u_sMatrix]

/-- Circuit equivalence: `S† q ; Z q ≡ S q` — Z·S† = S via σz_mul_sdagMatrix. -/
theorem SDAG_Z_eq_S {dim n : Nat} :
    uc_eval (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.Z n))
      = uc_eval (BaseUCom.S n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 Real.pi) * pad_u dim n (rotation 0 0 (-(Real.pi/2)))
        = pad_u dim n (rotation 0 0 (Real.pi/2))
  rw [rotation_S, rotation_Z, rotation_SDAG, pad_u_σz_mul_pad_u_sdagMatrix]

/-- Circuit equivalence: `S q ; S q ; S q ≡ S† q`. Lift of `sMatrix_pow_three`
    (S has order 4, so S³ = S^(-1) = S†). -/
theorem S_S_S_eq_SDAG {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
                       (BaseUCom.S n))
      = uc_eval (BaseUCom.SDAG n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (Real.pi / 2))
        * (pad_u dim n (rotation 0 0 (Real.pi / 2))
            * pad_u dim n (rotation 0 0 (Real.pi / 2)))
      = pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_S, rotation_SDAG, sMatrix_pow_three]

/-- Circuit equivalence: `S† q ; S† q ; S† q ≡ S q`. Dual of `S_S_S_eq_SDAG`. -/
theorem SDAG_SDAG_SDAG_eq_S {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.SDAG n))
                       (BaseUCom.SDAG n))
      = uc_eval (BaseUCom.S n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
        * (pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
            * pad_u dim n (rotation 0 0 (-(Real.pi / 2))))
      = pad_u dim n (rotation 0 0 (Real.pi / 2))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_SDAG, rotation_S, sdagMatrix_pow_three]

/-- `S q ; S q ; S q` acts as S† phase on `f_to_vec dim f` (S³ ≡ S†). -/
theorem f_to_vec_S_S_S (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
                       (BaseUCom.S n))
      * f_to_vec dim f
      = (if f n then -Complex.I else 1) • f_to_vec dim f := by
  rw [S_S_S_eq_SDAG]
  exact f_to_vec_SDAG_uc_eval dim n h f

/-- `S† q ; S† q ; S† q` acts as S phase on `f_to_vec dim f` (S†³ ≡ S). -/
theorem f_to_vec_SDAG_SDAG_SDAG (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.SDAG n))
                       (BaseUCom.SDAG n))
      * f_to_vec dim f
      = (if f n then Complex.I else 1) • f_to_vec dim f := by
  rw [SDAG_SDAG_SDAG_eq_S]
  exact f_to_vec_S_uc_eval dim n h f

/-- Circuit equivalence: `H q ; H q ; H q ≡ H q`. Lift of `hMatrix_pow_three`. -/
theorem H_H_H_eq_H {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
                       (BaseUCom.H n))
      = uc_eval (BaseUCom.H n : BaseUCom dim) := by
  show pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
        * (pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
            * pad_u dim n (rotation (Real.pi/2) 0 Real.pi))
      = pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_H, hMatrix_pow_three]

/-- `H q ; H q ; H q` acts as a single H on `f_to_vec dim f`. -/
theorem f_to_vec_H_H_H (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
                       (BaseUCom.H n))
      * f_to_vec dim f
      = uc_eval (BaseUCom.H n : BaseUCom dim) * f_to_vec dim f := by
  rw [H_H_H_eq_H]

/-- Circuit equivalence: `X q ; X q ; X q ≡ X q`. Lift of `σx_pow_three`. -/
theorem X_X_X_eq_X {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.X n : BaseUCom dim) (BaseUCom.X n))
                       (BaseUCom.X n))
      = uc_eval (BaseUCom.X n : BaseUCom dim) := by
  show pad_u dim n (rotation Real.pi 0 Real.pi)
        * (pad_u dim n (rotation Real.pi 0 Real.pi)
            * pad_u dim n (rotation Real.pi 0 Real.pi))
      = pad_u dim n (rotation Real.pi 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_X, σx_pow_three]

/-- Circuit equivalence: `Y q ; Y q ; Y q ≡ Y q`. Lift of `σy_pow_three`. -/
theorem Y_Y_Y_eq_Y {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))
                       (BaseUCom.Y n))
      = uc_eval (BaseUCom.Y n : BaseUCom dim) := by
  show pad_u dim n (rotation Real.pi (Real.pi/2) (Real.pi/2))
        * (pad_u dim n (rotation Real.pi (Real.pi/2) (Real.pi/2))
            * pad_u dim n (rotation Real.pi (Real.pi/2) (Real.pi/2)))
      = pad_u dim n (rotation Real.pi (Real.pi/2) (Real.pi/2))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_Y, σy_pow_three]

/-- Circuit equivalence: `Z q ; Z q ; Z q ≡ Z q`. Lift of `σz_pow_three`. -/
theorem Z_Z_Z_eq_Z {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.Z n : BaseUCom dim) (BaseUCom.Z n))
                       (BaseUCom.Z n))
      = uc_eval (BaseUCom.Z n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 Real.pi)
        * (pad_u dim n (rotation 0 0 Real.pi)
            * pad_u dim n (rotation 0 0 Real.pi))
      = pad_u dim n (rotation 0 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_Z, σz_pow_three]

/-- `S† q ; S† q` acts as Z on `f_to_vec dim f` (since (S†)² = Z). -/
theorem f_to_vec_SDAG_SDAG (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.SDAG n))
      * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [show uc_eval (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.SDAG n))
        = uc_eval (BaseUCom.Z n : BaseUCom dim) from SDAG_SDAG_eq_Z]
  exact f_to_vec_Z_uc_eval dim n h f


/-- `(exp(iπ/4))² = I` (used for T² = S). -/
private theorem exp_pi4_sq_eq_I :
    (Complex.exp (Complex.I * (Real.pi / 4)))^2 = Complex.I := by
  rw [show (Complex.exp (Complex.I * (Real.pi / 4)))^2
        = Complex.exp (Complex.I * (Real.pi / 4) * 2) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show Complex.I * (Real.pi / 4) * 2 = (Real.pi : ℂ) / 2 * Complex.I from by ring]
  exact Complex.exp_pi_div_two_mul_I

/-- `tMatrix * tMatrix = sMatrix` (T² = S, since (exp(iπ/4))² = exp(iπ/2) = I). -/
theorem tMatrix_mul_tMatrix : tMatrix * tMatrix = sMatrix := by
  unfold tMatrix sMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  -- Residue at (1,1): exp(iπ/4) * exp(iπ/4) = I
  rw [show Complex.exp (Complex.I * (Real.pi / 4)) * Complex.exp (Complex.I * (Real.pi / 4))
        = (Complex.exp (Complex.I * (Real.pi / 4)))^2 from by ring]
  exact exp_pi4_sq_eq_I

/-- `T⁴ = Z` at the matrix level — chain of `T² = S` and `S² = Z`. -/
theorem tMatrix_pow_four : tMatrix * tMatrix * tMatrix * tMatrix = σz := by
  rw [Matrix.mul_assoc (tMatrix * tMatrix) tMatrix tMatrix,
      tMatrix_mul_tMatrix, sMatrix_mul_sMatrix]

/-- `S⁴ = I` at the matrix level — chain of `S² = Z` and `Z² = I`. -/
theorem sMatrix_pow_four : sMatrix * sMatrix * sMatrix * sMatrix = σi := by
  rw [Matrix.mul_assoc (sMatrix * sMatrix) sMatrix sMatrix,
      sMatrix_mul_sMatrix, σz_mul_σz]

/-- Circuit equivalence: `T q ; T q ; T q ; T q ≡ Z q`. Lifts `tMatrix_pow_four`
    via three `pad_u_mul_pad_u` collapses. -/
theorem T_T_T_T_eq_Z {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.T n : BaseUCom dim) (BaseUCom.T n))
                       (BaseUCom.T n)) (BaseUCom.T n))
      = uc_eval (BaseUCom.Z n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (Real.pi/4))
        * (pad_u dim n (rotation 0 0 (Real.pi/4))
            * (pad_u dim n (rotation 0 0 (Real.pi/4))
                * pad_u dim n (rotation 0 0 (Real.pi/4))))
      = pad_u dim n (rotation 0 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u]
  rw [rotation_T, rotation_Z, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      tMatrix_pow_four]

/-- Circuit equivalence: `H q ; H q ; H q ; H q ≡ ID q`. Lifts
    `hMatrix_pow_four`. Note: H² ≡ ID is stronger; this is included for
    symmetry with the T⁴/S⁴/T†⁴/S†⁴ family. -/
theorem H_H_H_H_eq_ID {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
                       (BaseUCom.H n)) (BaseUCom.H n))
      = uc_eval (BaseUCom.ID n : BaseUCom dim) := by
  show pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
        * (pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
            * (pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
                * pad_u dim n (rotation (Real.pi/2) 0 Real.pi)))
      = pad_u dim n (rotation 0 0 0)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u]
  rw [rotation_H, rotation_I, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hMatrix_pow_four]

/-- Circuit equivalence: `S q ; S q ; S q ; S q ≡ ID q`. Lifts `sMatrix_pow_four`. -/
theorem S_S_S_S_eq_ID {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
                       (BaseUCom.S n)) (BaseUCom.S n))
      = uc_eval (BaseUCom.ID n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (Real.pi/2))
        * (pad_u dim n (rotation 0 0 (Real.pi/2))
            * (pad_u dim n (rotation 0 0 (Real.pi/2))
                * pad_u dim n (rotation 0 0 (Real.pi/2))))
      = pad_u dim n (rotation 0 0 0)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u]
  rw [rotation_S, rotation_I, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      sMatrix_pow_four]

/-- `T q ; T q ; T q ; T q` acts as Z phase on `f_to_vec dim f`. -/
theorem f_to_vec_T_T_T_T (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.T n : BaseUCom dim) (BaseUCom.T n))
                       (BaseUCom.T n)) (BaseUCom.T n))
      * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [T_T_T_T_eq_Z]
  exact f_to_vec_Z_uc_eval dim n h f

/-- `H q ; H q ; H q ; H q` acts as identity on `f_to_vec dim f`. -/
theorem f_to_vec_H_H_H_H (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
                       (BaseUCom.H n)) (BaseUCom.H n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [H_H_H_H_eq_ID]
  exact f_to_vec_ID h f

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: H⁵ = H at basis level
/-- `H q ; H q ; H q ; H q ; H q` acts as a single `H q` on `f_to_vec dim f`
    (H⁵ = H, since H⁴ = ID). **Relational form**: H|b⟩ = (|0⟩ ± |1⟩)/√2 is not
    a basis state, so the cleanest statement is `uc_eval(H⁵) · v = uc_eval(H) · v`.
    Mirrors `f_to_vec_Y_Y_Y_Y_Y` (Iter 133) — same proof structure as Y⁵ since both
    have order-4 = ID without a closed-form basis-state expression. -/
theorem f_to_vec_H_H_H_H_H (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
              (BaseUCom.H n)) (BaseUCom.H n)) (BaseUCom.H n))
      * f_to_vec dim f
      = uc_eval (BaseUCom.H n : BaseUCom dim) * f_to_vec dim f := by
  -- uc_eval(seq^4 H) * f_to_vec f = H * (uc_eval(seq^3 H) * f_to_vec f) by uc_eval_seq_mul.
  -- Inner uc_eval(seq^3 H) * f_to_vec f = f_to_vec f by f_to_vec_H_H_H_H (H⁴ = ID).
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_H_H_H dim n h f]

/-- `S q ; S q ; S q ; S q` acts as identity on `f_to_vec dim f`. -/
theorem f_to_vec_S_S_S_S (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
                       (BaseUCom.S n)) (BaseUCom.S n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [S_S_S_S_eq_ID]
  exact f_to_vec_ID h f

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: S⁵ = S at basis level
/-- `S q ; S q ; S q ; S q ; S q` acts as a single `S q` on `f_to_vec dim f`
    (S⁵ = S, since S⁴ = ID). **Closed-form** result via `f_to_vec_S_uc_eval`:
    `(if f n then Complex.I else 1) • f_to_vec dim f`. Diagonal-phase variant
    of Z⁵; S maps |b⟩ to i^b |b⟩, so the basis-state action is just a phase
    factor. Completes the diagonal-phase order-5 family alongside `f_to_vec_Z_Z_Z_Z_Z`
    (Iter 132 SQIR-tick). -/
theorem f_to_vec_S_S_S_S_S (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
              (BaseUCom.S n)) (BaseUCom.S n)) (BaseUCom.S n))
      * f_to_vec dim f
      = (if f n then Complex.I else 1) • f_to_vec dim f := by
  -- uc_eval(seq^4 S) * f_to_vec f = S * (uc_eval(seq^3 S) * f_to_vec f) by uc_eval_seq_mul.
  -- Inner uc_eval(seq^3 S) * f_to_vec f = f_to_vec f by f_to_vec_S_S_S_S (S⁴ = ID).
  -- Then S * f_to_vec f = (i^[f n]) • f_to_vec f by f_to_vec_S_uc_eval.
  rw [uc_eval_seq_mul]
  rw [f_to_vec_S_S_S_S dim n h f]
  exact f_to_vec_S_uc_eval dim n h f

/-- `(exp(-iπ/4))² = -I`. -/
private theorem exp_neg_pi4_sq_eq_neg_I :
    (Complex.exp (-(Complex.I * (Real.pi / 4))))^2 = -Complex.I := by
  rw [show (Complex.exp (-(Complex.I * (Real.pi / 4))))^2
        = Complex.exp (-(Complex.I * (Real.pi / 4)) * 2) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show -(Complex.I * (Real.pi / 4)) * 2 = -((Real.pi : ℂ) / 2 * Complex.I) from by ring]
  rw [Complex.exp_neg]
  rw [Complex.exp_pi_div_two_mul_I]
  exact Complex.inv_I

/-- `tdagMatrix * tdagMatrix = sdagMatrix` (T†² = S†). -/
theorem tdagMatrix_mul_tdagMatrix : tdagMatrix * tdagMatrix = sdagMatrix := by
  unfold tdagMatrix sdagMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  -- Residue at (1,1): exp(-iπ/4) * exp(-iπ/4) = -I
  rw [show Complex.exp (-(Complex.I * (Real.pi / 4)))
        * Complex.exp (-(Complex.I * (Real.pi / 4)))
        = (Complex.exp (-(Complex.I * (Real.pi / 4))))^2 from by ring]
  exact exp_neg_pi4_sq_eq_neg_I

/-- Circuit equivalence: `T† q ; T† q ≡ S† q`. -/
theorem TDAG_TDAG_eq_SDAG {dim : Nat} (n : Nat) :
    uc_eval (UCom.seq (BaseUCom.TDAG n : BaseUCom dim) (BaseUCom.TDAG n))
      = uc_eval (BaseUCom.SDAG n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi / 4)))
        * pad_u dim n (rotation 0 0 (-(Real.pi / 4)))
      = pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
  rw [rotation_TDAG, rotation_SDAG, pad_u_mul_pad_u, tdagMatrix_mul_tdagMatrix]

/-- `T† q ; T† q` acts as S† phase on `f_to_vec dim f` (since (T†)² = S†). -/
theorem f_to_vec_TDAG_TDAG (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.TDAG n : BaseUCom dim) (BaseUCom.TDAG n))
      * f_to_vec dim f
      = (if f n then -Complex.I else 1) • f_to_vec dim f := by
  rw [show uc_eval (UCom.seq (BaseUCom.TDAG n : BaseUCom dim) (BaseUCom.TDAG n))
        = uc_eval (BaseUCom.SDAG n : BaseUCom dim) from TDAG_TDAG_eq_SDAG n]
  exact f_to_vec_SDAG_uc_eval dim n h f

/-- `T†⁴ = Z` at the matrix level — chain of `T†² = S†` and `S†² = Z`. -/
theorem tdagMatrix_pow_four :
    tdagMatrix * tdagMatrix * tdagMatrix * tdagMatrix = σz := by
  rw [Matrix.mul_assoc (tdagMatrix * tdagMatrix) tdagMatrix tdagMatrix,
      tdagMatrix_mul_tdagMatrix, sdagMatrix_mul_sdagMatrix]

/-- `T⁵ = Z · T` — direct corollary of T⁴ = Z. -/
theorem tMatrix_pow_five :
    tMatrix * tMatrix * tMatrix * tMatrix * tMatrix = σz * tMatrix := by
  rw [tMatrix_pow_four]

/-- `T†⁵ = Z · T†` — direct corollary of T†⁴ = Z. -/
theorem tdagMatrix_pow_five :
    tdagMatrix * tdagMatrix * tdagMatrix * tdagMatrix * tdagMatrix = σz * tdagMatrix := by
  rw [tdagMatrix_pow_four]

/-- S has order 4 at the padded level: S · S · S · S = 1 (chain form). -/
theorem pad_u_sMatrix_pow_four {dim n : Nat} (h : n < dim) :
    pad_u dim n sMatrix * pad_u dim n sMatrix * pad_u dim n sMatrix * pad_u dim n sMatrix
      = (1 : Square dim) :=
  pad_u_pow_four_eq_one h sMatrix sMatrix_pow_four

/-- `S†⁴ = I` at the matrix level — chain of `S†² = Z` and `Z² = I`. -/
theorem sdagMatrix_pow_four :
    sdagMatrix * sdagMatrix * sdagMatrix * sdagMatrix = σi := by
  rw [Matrix.mul_assoc (sdagMatrix * sdagMatrix) sdagMatrix sdagMatrix,
      sdagMatrix_mul_sdagMatrix, σz_mul_σz]

/-- S† has order 4 at the padded level: S† · S† · S† · S† = 1 (chain form). -/
theorem pad_u_sdagMatrix_pow_four {dim n : Nat} (h : n < dim) :
    pad_u dim n sdagMatrix * pad_u dim n sdagMatrix * pad_u dim n sdagMatrix * pad_u dim n sdagMatrix
      = (1 : Square dim) :=
  pad_u_pow_four_eq_one h sdagMatrix sdagMatrix_pow_four

/-- T's 4-chain at the padded level equals pad_u σz (the padded Z gate).
    Reflects T⁴ = Z; no `n < dim` hypothesis needed. -/
theorem pad_u_tMatrix_pow_four (dim n : Nat) :
    pad_u dim n tMatrix * pad_u dim n tMatrix * pad_u dim n tMatrix * pad_u dim n tMatrix
      = pad_u dim n σz :=
  pad_u_pow_four_eq dim n tMatrix σz tMatrix_pow_four

/-- T†'s 4-chain at the padded level equals pad_u σz. Reflects T†⁴ = Z. -/
theorem pad_u_tdagMatrix_pow_four (dim n : Nat) :
    pad_u dim n tdagMatrix * pad_u dim n tdagMatrix * pad_u dim n tdagMatrix * pad_u dim n tdagMatrix
      = pad_u dim n σz :=
  pad_u_pow_four_eq dim n tdagMatrix σz tdagMatrix_pow_four

/-- T's 2-chain at the padded level equals pad_u sMatrix. Reflects T² = S. -/
theorem pad_u_tMatrix_mul_tMatrix (dim n : Nat) :
    pad_u dim n tMatrix * pad_u dim n tMatrix = pad_u dim n sMatrix :=
  pad_u_pow_two_eq dim n tMatrix sMatrix tMatrix_mul_tMatrix

/-- S's 2-chain at the padded level equals pad_u σz. Reflects S² = Z. -/
theorem pad_u_sMatrix_mul_sMatrix (dim n : Nat) :
    pad_u dim n sMatrix * pad_u dim n sMatrix = pad_u dim n σz :=
  pad_u_pow_two_eq dim n sMatrix σz sMatrix_mul_sMatrix

/-- T†'s 2-chain at the padded level equals pad_u sdagMatrix. Reflects T†² = S†. -/
theorem pad_u_tdagMatrix_mul_tdagMatrix (dim n : Nat) :
    pad_u dim n tdagMatrix * pad_u dim n tdagMatrix = pad_u dim n sdagMatrix :=
  pad_u_pow_two_eq dim n tdagMatrix sdagMatrix tdagMatrix_mul_tdagMatrix

/-- S†'s 2-chain at the padded level equals pad_u σz. Reflects S†² = Z. -/
theorem pad_u_sdagMatrix_mul_sdagMatrix (dim n : Nat) :
    pad_u dim n sdagMatrix * pad_u dim n sdagMatrix = pad_u dim n σz :=
  pad_u_pow_two_eq dim n sdagMatrix σz sdagMatrix_mul_sdagMatrix

/-- S's 3-chain at the padded level equals pad_u sdagMatrix. Reflects S³ = S†. -/
theorem pad_u_sMatrix_pow_three (dim n : Nat) :
    pad_u dim n sMatrix * pad_u dim n sMatrix * pad_u dim n sMatrix
      = pad_u dim n sdagMatrix :=
  pad_u_pow_three_eq dim n sMatrix sdagMatrix sMatrix_pow_three

/-- S†'s 3-chain at the padded level equals pad_u sMatrix. Reflects S†³ = S. -/
theorem pad_u_sdagMatrix_pow_three (dim n : Nat) :
    pad_u dim n sdagMatrix * pad_u dim n sdagMatrix * pad_u dim n sdagMatrix
      = pad_u dim n sMatrix :=
  pad_u_pow_three_eq dim n sdagMatrix sMatrix sdagMatrix_pow_three

/-- `S⁵ = S`. Follows from S⁴ = I + Matrix.one_mul. -/
theorem sMatrix_pow_five :
    sMatrix * sMatrix * sMatrix * sMatrix * sMatrix = sMatrix := by
  rw [sMatrix_pow_four, σi_eq_one, Matrix.one_mul]

/-- `S†⁵ = S†`. -/
theorem sdagMatrix_pow_five :
    sdagMatrix * sdagMatrix * sdagMatrix * sdagMatrix * sdagMatrix = sdagMatrix := by
  rw [sdagMatrix_pow_four, σi_eq_one, Matrix.one_mul]

/-- S's 5-chain at the padded level equals pad_u sMatrix. Reflects S⁵ = S. -/
theorem pad_u_sMatrix_pow_five (dim n : Nat) :
    pad_u dim n sMatrix * pad_u dim n sMatrix * pad_u dim n sMatrix * pad_u dim n sMatrix * pad_u dim n sMatrix
      = pad_u dim n sMatrix :=
  pad_u_pow_five_eq dim n sMatrix sMatrix sMatrix_pow_five

/-- S†'s 5-chain at the padded level equals pad_u sdagMatrix. Reflects S†⁵ = S†. -/
theorem pad_u_sdagMatrix_pow_five (dim n : Nat) :
    pad_u dim n sdagMatrix * pad_u dim n sdagMatrix * pad_u dim n sdagMatrix * pad_u dim n sdagMatrix * pad_u dim n sdagMatrix
      = pad_u dim n sdagMatrix :=
  pad_u_pow_five_eq dim n sdagMatrix sdagMatrix sdagMatrix_pow_five

/-- T's 5-chain at the padded level equals pad_u (σz·T). Reflects T⁵ = Z·T. -/
theorem pad_u_tMatrix_pow_five (dim n : Nat) :
    pad_u dim n tMatrix * pad_u dim n tMatrix * pad_u dim n tMatrix * pad_u dim n tMatrix * pad_u dim n tMatrix
      = pad_u dim n (σz * tMatrix) :=
  pad_u_pow_five_eq dim n tMatrix (σz * tMatrix) tMatrix_pow_five

/-- T†'s 5-chain at the padded level equals pad_u (σz·T†). Reflects T†⁵ = Z·T†. -/
theorem pad_u_tdagMatrix_pow_five (dim n : Nat) :
    pad_u dim n tdagMatrix * pad_u dim n tdagMatrix * pad_u dim n tdagMatrix * pad_u dim n tdagMatrix * pad_u dim n tdagMatrix
      = pad_u dim n (σz * tdagMatrix) :=
  pad_u_pow_five_eq dim n tdagMatrix (σz * tdagMatrix) tdagMatrix_pow_five

/-- Circuit equivalence: `T† q ; T† q ; T† q ; T† q ≡ Z q`.
    Lifts `tdagMatrix_pow_four`. -/
theorem TDAG_TDAG_TDAG_TDAG_eq_Z {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.TDAG n : BaseUCom dim)
                       (BaseUCom.TDAG n)) (BaseUCom.TDAG n)) (BaseUCom.TDAG n))
      = uc_eval (BaseUCom.Z n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi/4)))
        * (pad_u dim n (rotation 0 0 (-(Real.pi/4)))
            * (pad_u dim n (rotation 0 0 (-(Real.pi/4)))
                * pad_u dim n (rotation 0 0 (-(Real.pi/4)))))
      = pad_u dim n (rotation 0 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u]
  rw [rotation_TDAG, rotation_Z, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      tdagMatrix_pow_four]

/-- Circuit equivalence: `S† q ; S† q ; S† q ; S† q ≡ ID q`.
    Lifts `sdagMatrix_pow_four`. -/
theorem SDAG_SDAG_SDAG_SDAG_eq_ID {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.SDAG n : BaseUCom dim)
                       (BaseUCom.SDAG n)) (BaseUCom.SDAG n)) (BaseUCom.SDAG n))
      = uc_eval (BaseUCom.ID n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi/2)))
        * (pad_u dim n (rotation 0 0 (-(Real.pi/2)))
            * (pad_u dim n (rotation 0 0 (-(Real.pi/2)))
                * pad_u dim n (rotation 0 0 (-(Real.pi/2)))))
      = pad_u dim n (rotation 0 0 0)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u]
  rw [rotation_SDAG, rotation_I, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      sdagMatrix_pow_four]

/-- `T† q ; T† q ; T† q ; T† q` acts as Z phase on `f_to_vec dim f`. -/
theorem f_to_vec_TDAG_TDAG_TDAG_TDAG (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.TDAG n : BaseUCom dim)
                       (BaseUCom.TDAG n)) (BaseUCom.TDAG n)) (BaseUCom.TDAG n))
      * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [TDAG_TDAG_TDAG_TDAG_eq_Z]
  exact f_to_vec_Z_uc_eval dim n h f

/-- `S† q ; S† q ; S† q ; S† q` acts as identity on `f_to_vec dim f`. -/
theorem f_to_vec_SDAG_SDAG_SDAG_SDAG (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.SDAG n : BaseUCom dim)
                       (BaseUCom.SDAG n)) (BaseUCom.SDAG n)) (BaseUCom.SDAG n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [SDAG_SDAG_SDAG_SDAG_eq_ID]
  exact f_to_vec_ID h f

-- Note: `S_S_eq_Z` (the circuit equivalence S;S ≡ Z) already exists in
-- UnitarySem.lean line 578, proven via rotation_Rz_compose. Our
-- sMatrix_mul_sMatrix above gives an alternative matrix-level proof
-- (useful for f_to_vec-level rewriting).

/-- Circuit equivalence: `S q ; S† q ≡ ID` (uc_eval = identity matrix). -/
theorem S_SDAG_eq_id {dim n : Nat} (h : n < dim) :
    uc_eval (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.SDAG n))
      = (1 : Square dim) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
        * pad_u dim n (rotation 0 0 (Real.pi / 2))
      = 1
  rw [rotation_S, rotation_SDAG, pad_u_mul_pad_u, sdagMatrix_mul_sMatrix, pad_u_id h]

/-- Circuit equivalence: `S† q ; S q ≡ ID`. -/
theorem SDAG_S_eq_id {dim n : Nat} (h : n < dim) :
    uc_eval (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.S n))
      = (1 : Square dim) := by
  show pad_u dim n (rotation 0 0 (Real.pi / 2))
        * pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
      = 1
  rw [rotation_S, rotation_SDAG, pad_u_mul_pad_u, sMatrix_mul_sdagMatrix, pad_u_id h]

/-- `T† q ; T q` is identity (matrix-level proof). -/
theorem f_to_vec_TDAG_then_T (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.TDAG n : BaseUCom dim) (BaseUCom.T n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  show (pad_u dim n (rotation 0 0 (Real.pi / 4))
        * pad_u dim n (rotation 0 0 (-(Real.pi / 4)))) * f_to_vec dim f = _
  rw [rotation_T, rotation_TDAG, pad_u_mul_pad_u, tMatrix_mul_tdagMatrix, pad_u_id h, Matrix.one_mul]

/-- `Y q ; Y q` is identity (matrix-level proof).
    σy is its own inverse (σy²=I), so the matrix-level shortcut applies. -/
theorem f_to_vec_Y_Y (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  show (pad_u dim n (rotation Real.pi (Real.pi/2) (Real.pi/2))
        * pad_u dim n (rotation Real.pi (Real.pi/2) (Real.pi/2))) * f_to_vec dim f = _
  rw [rotation_Y, pad_u_mul_pad_u, σy_mul_σy, pad_u_id h, Matrix.one_mul]

/-- `H q ; H q` is identity. Cleanest proof via the matrix-level identity
    `hMatrix_mul_hMatrix` (already proven in UnitarySem) — avoids the
    superposition-cancellation route. -/
theorem f_to_vec_H_H (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  show (pad_u dim n (rotation (Real.pi / 2) 0 Real.pi)
        * pad_u dim n (rotation (Real.pi / 2) 0 Real.pi)) * f_to_vec dim f = _
  rw [rotation_H, pad_u_mul_pad_u, hMatrix_mul_hMatrix, pad_u_id h, Matrix.one_mul]

/-! ## Validation: chaining works for T;T (T² phase) -/

/-- Chaining check: applying T twice on `f_to_vec dim f` gives a `T²` phase factor.
    Validates the `uc_eval_seq_mul` + `mul_smul_state` + `f_to_vec_T_uc_eval`
    chain works as expected. This is the simplest non-trivial multi-gate
    composition through `f_to_vec`. -/
theorem f_to_vec_T_T (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.T n : BaseUCom dim) (BaseUCom.T n))
      * f_to_vec dim f
      = (if f n then Complex.exp (Complex.I * (Real.pi / 4))
                    * Complex.exp (Complex.I * (Real.pi / 4))
              else 1)
        • f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_T_uc_eval dim n h f]
  rw [mul_smul_state]
  rw [f_to_vec_T_uc_eval dim n h f]
  rw [smul_smul]
  congr 1
  by_cases hfn : f n <;> simp [hfn]

/-- Chaining check: applying T then T† gives no phase change (T†T = id). -/
theorem f_to_vec_TDAG_T (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.T n : BaseUCom dim) (BaseUCom.TDAG n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_T_uc_eval dim n h f]
  rw [mul_smul_state]
  rw [f_to_vec_TDAG_uc_eval dim n h f]
  rw [smul_smul]
  -- Need: (if f n then exp(-iπ/4) else 1) * (if f n then exp(iπ/4) else 1) = 1
  rw [show ((if f n then Complex.exp (Complex.I * (Real.pi / 4)) else (1 : ℂ))
            * (if f n then Complex.exp (-(Complex.I * (Real.pi / 4))) else (1 : ℂ)))
          = 1 from by
    by_cases hfn : f n
    · simp [hfn, ← Complex.exp_add]
    · simp [hfn]]
  rw [one_smul]

/-! ## CCX prefix: H c; CNOT b c

    First non-trivial 2-gate composition involving Hadamard. After H c:
    superposition of two basis states. CNOT b c on each branch flips the
    c-bit conditional on b-bit, so the final updated functions become
    `update f c (f b)` and `update f c (!f b)`. -/

theorem f_to_vec_H_CNOT (dim b c : Nat) (hb : b < dim) (hc : c < dim)
    (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c))
      * f_to_vec dim f
      = (Real.sqrt 2 / 2 : ℂ) • f_to_vec dim (update f c (f b))
        + ((if f c then (-1 : ℂ) else 1) * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (!f b)) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_uc_eval dim c hc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim b c (update f c false) hb hc hbc]
  rw [f_to_vec_CNOT_proved dim b c (update f c true) hb hc hbc]
  -- Simplify the nested update expressions to the desired form.
  -- Simplify the inner xor expression: bit c of (update f c v) = v;
  -- bit b of (update f c v) = f b (since b ≠ c).
  rw [show (update f c false) c = false from update_eq f c false]
  rw [show (update f c true) c = true from update_eq f c true]
  rw [show (update f c false) b = f b from update_neq f c b false hbc]
  rw [show (update f c true) b = f b from update_neq f c b true hbc]
  -- xor false (f b) = f b; xor true (f b) = !f b
  simp only [Bool.false_xor, Bool.true_xor]
  -- Then update_idem collapses the nested updates.
  rw [update_idem, update_idem]

/-! ## CCX prefix: H c; CNOT b c; T† c

    3-gate prefix. After H+CNOT we have 2 branches with c-bit = f b vs !f b.
    Applying T† c picks up a phase `exp(-i·π/4)` if the branch's c-bit is 1,
    `1` if 0. The phases differ between the branches. -/

theorem f_to_vec_H_CNOT_TDAG (dim b c : Nat) (hb : b < dim) (hc : c < dim)
    (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c))
                      (BaseUCom.TDAG c))
      * f_to_vec dim f
      = ((if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (f b))
        + ((if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (!f b)) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_CNOT dim b c hb hc hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_TDAG_uc_eval dim c hc (update f c (f b))]
  rw [f_to_vec_TDAG_uc_eval dim c hc (update f c (!f b))]
  rw [show (update f c (f b)) c = f b from update_eq f c (f b)]
  rw [show (update f c (!f b)) c = !f b from update_eq f c (!f b)]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: H c; CNOT b c; T† c; CNOT a c

    4-gate prefix. The CNOT a c flips the c-bit XOR with a-bit. Phases
    from T† c carry through unchanged (CNOT is unitary, doesn't add phase). -/

theorem f_to_vec_H_CNOT_TDAG_CNOT (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
      * f_to_vec dim f
      = ((if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (xor (f b) (f a)))
        + ((if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (xor (!f b) (f a))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_CNOT_TDAG dim b c hb hc hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim a c (update f c (f b)) ha hc hac]
  rw [f_to_vec_CNOT_proved dim a c (update f c (!f b)) ha hc hac]
  -- Simplify each branch's update.
  -- branch 0: update (update f c (f b)) c (xor ((update f c (f b)) c) ((update f c (f b)) a))
  --         = update (update f c (f b)) c (xor (f b) (f a))    [by update_eq, update_neq with a ≠ c]
  --         = update f c (xor (f b) (f a))                       [by update_idem]
  rw [show (update f c (f b)) c = f b from update_eq f c (f b)]
  rw [show (update f c (!f b)) c = !f b from update_eq f c (!f b)]
  rw [show (update f c (f b)) a = f a from update_neq f c a (f b) hac]
  rw [show (update f c (!f b)) a = f a from update_neq f c a (!f b) hac]
  rw [update_idem, update_idem]

/-! ## CCX prefix: H c; CNOT b c; T† c; CNOT a c; T c (5 gates, ends s1+T)

    First gate of `s2`. T c picks up phase exp(iπ/4) on each branch when
    its c-bit is 1. Branch 0 c-bit = xor(f b)(f a); branch 1 c-bit =
    xor(!f b)(f a). These bits are complementary (always differ). -/

theorem f_to_vec_CCX_prefix_5 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
      * f_to_vec dim f
      = ((if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (xor (f b) (f a)))
        + ((if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (xor (!f b) (f a))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_CNOT_TDAG_CNOT dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_T_uc_eval dim c hc (update f c (xor (f b) (f a)))]
  rw [f_to_vec_T_uc_eval dim c hc (update f c (xor (!f b) (f a)))]
  rw [show (update f c (xor (f b) (f a))) c = xor (f b) (f a)
      from update_eq f c (xor (f b) (f a))]
  rw [show (update f c (xor (!f b) (f a))) c = xor (!f b) (f a)
      from update_eq f c (xor (!f b) (f a))]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + CNOT b c (6 gates)

    Gate 6: CNOT b c. Each branch's c-bit XORs with f b (since b is unchanged).
    Branch 0 c-bit was xor(f b)(f a), now becomes f a (self-cancellation).
    Branch 1 c-bit was xor(!f b)(f a), now becomes !f a. -/

theorem f_to_vec_CCX_prefix_6 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
      * f_to_vec dim f
      = ((if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (f a))
        + ((if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (!f a)) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_5 dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim b c (update f c (xor (f b) (f a))) hb hc hbc]
  rw [f_to_vec_CNOT_proved dim b c (update f c (xor (!f b) (f a))) hb hc hbc]
  rw [show (update f c (xor (f b) (f a))) c = xor (f b) (f a)
      from update_eq f c (xor (f b) (f a))]
  rw [show (update f c (xor (!f b) (f a))) c = xor (!f b) (f a)
      from update_eq f c (xor (!f b) (f a))]
  rw [show (update f c (xor (f b) (f a))) b = f b
      from update_neq f c b (xor (f b) (f a)) hbc]
  rw [show (update f c (xor (!f b) (f a))) b = f b
      from update_neq f c b (xor (!f b) (f a)) hbc]
  rw [show xor (xor (f b) (f a)) (f b) = f a from by
      cases f b <;> cases f a <;> decide]
  rw [show xor (xor (!f b) (f a)) (f b) = !f a from by
      cases f b <;> cases f a <;> decide]
  rw [update_idem, update_idem]

/-! ## CCX prefix: ... + T† c (7 gates)

    Gate 7: T† c (third gate of s2). Adds phase exp(-iπ/4) per branch
    when branch's c-bit is 1. Branch 0 c-bit = f a, branch 1 = !f a. -/

theorem f_to_vec_CCX_prefix_7 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
      * f_to_vec dim f
      = ((if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (f a))
        + ((if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (!f a)) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_6 dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_TDAG_uc_eval dim c hc (update f c (f a))]
  rw [f_to_vec_TDAG_uc_eval dim c hc (update f c (!f a))]
  rw [show (update f c (f a)) c = f a from update_eq f c (f a)]
  rw [show (update f c (!f a)) c = !f a from update_eq f c (!f a)]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + CNOT a c (8 gates, ends s2)

    Gate 8 = last gate of s2. CNOT a c flips c-bit XOR with a-bit.
    Branch 0: xor(f a)(f a) = false. Branch 1: xor(!f a)(f a) = true.
    After this gate, the two branches have FIXED c-bits — the f-dependence
    in the c-bit has been fully absorbed into the phase factors. -/

theorem f_to_vec_CCX_prefix_8 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
      * f_to_vec dim f
      = ((if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + ((if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_7 dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim a c (update f c (f a)) ha hc hac]
  rw [f_to_vec_CNOT_proved dim a c (update f c (!f a)) ha hc hac]
  rw [show (update f c (f a)) c = f a from update_eq f c (f a)]
  rw [show (update f c (!f a)) c = !f a from update_eq f c (!f a)]
  rw [show (update f c (f a)) a = f a from update_neq f c a (f a) hac]
  rw [show (update f c (!f a)) a = f a from update_neq f c a (!f a) hac]
  rw [show xor (f a) (f a) = false from by cases f a <;> decide]
  rw [show xor (!f a) (f a) = true from by cases f a <;> decide]
  rw [update_idem, update_idem]

/-! ## CCX prefix: ... + CNOT a b (9 gates, start of s3)

    Gate 9 = first gate of s3. CNOT a b — control a, target b. This is
    the FIRST gate that doesn't touch c. b-bit XORs with a-bit. Each
    branch gains a NESTED update (at c, then at b). Phases unchanged. -/

theorem f_to_vec_CCX_prefix_9 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
      * f_to_vec dim f
      = ((if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update (update f c false) b (xor (f b) (f a)))
        + ((if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update (update f c true) b (xor (f b) (f a))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_8 dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim a b (update f c false) ha hb hab]
  rw [f_to_vec_CNOT_proved dim a b (update f c true) ha hb hab]
  -- (update f c v) b = f b (b ≠ c), (update f c v) a = f a (a ≠ c)
  rw [show (update f c false) b = f b from update_neq f c b false hbc]
  rw [show (update f c false) a = f a from update_neq f c a false hac]
  rw [show (update f c true) b = f b from update_neq f c b true hbc]
  rw [show (update f c true) a = f a from update_neq f c a true hac]

/-! ## CCX prefix: ... + T† b (10 gates)

    Gate 10: T† b. b-bit phase factor. After CNOT a b, both branches
    have b-bit = xor(f b)(f a) — SAME for both branches. So both branches
    pick up the same phase factor (no new asymmetry). -/

theorem f_to_vec_CCX_prefix_10 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
      * f_to_vec dim f
      = ((if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update (update f c false) b (xor (f b) (f a)))
        + ((if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update (update f c true) b (xor (f b) (f a))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_9 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_TDAG_uc_eval dim b hb (update (update f c false) b (xor (f b) (f a)))]
  rw [f_to_vec_TDAG_uc_eval dim b hb (update (update f c true) b (xor (f b) (f a)))]
  -- (update _ b w) b = w
  rw [show (update (update f c false) b (xor (f b) (f a))) b = xor (f b) (f a)
      from update_eq _ b (xor (f b) (f a))]
  rw [show (update (update f c true) b (xor (f b) (f a))) b = xor (f b) (f a)
      from update_eq _ b (xor (f b) (f a))]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + CNOT a b (11 gates, ends s3)

    Gate 11 = last gate of s3. CNOT a b again — un-does gate 9's b-bit XOR.
    State b-bit returns to f b. After update_idem (collapse double-b update)
    and update_self (resetting b to f b is no-op), the state simplifies
    back to `update f c {false,true}`. -/

theorem f_to_vec_CCX_prefix_11 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
        (BaseUCom.CNOT a b))
      * f_to_vec dim f
      = ((if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + ((if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_10 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim a b
      (update (update f c false) b (xor (f b) (f a))) ha hb hab]
  rw [f_to_vec_CNOT_proved dim a b
      (update (update f c true) b (xor (f b) (f a))) ha hb hab]
  -- (update _ b w) b = w; (update (update f c v) b w) a = f a (a ≠ b, a ≠ c)
  rw [show (update (update f c false) b (xor (f b) (f a))) b = xor (f b) (f a)
      from update_eq _ b (xor (f b) (f a))]
  rw [show (update (update f c true) b (xor (f b) (f a))) b = xor (f b) (f a)
      from update_eq _ b (xor (f b) (f a))]
  rw [show (update (update f c false) b (xor (f b) (f a))) a = f a from by
      rw [update_neq _ b a (xor (f b) (f a)) hab,
          update_neq _ c a false hac]]
  rw [show (update (update f c true) b (xor (f b) (f a))) a = f a from by
      rw [update_neq _ b a (xor (f b) (f a)) hab,
          update_neq _ c a true hac]]
  -- xor (xor (f b) (f a)) (f a) = f b
  rw [show xor (xor (f b) (f a)) (f a) = f b from by
      cases f b <;> cases f a <;> decide]
  -- update_idem collapses the double-b update; update_self collapses (update _ b (f b))
  rw [update_idem, update_idem]
  -- Now: update (update f c false) b (f b) needs (update f c false) b = f b first
  rw [show update (update f c false) b (f b)
        = update (update f c false) b ((update f c false) b) from by
      rw [update_neq _ c b false hbc]]
  rw [show update (update f c true) b (f b)
        = update (update f c true) b ((update f c true) b) from by
      rw [update_neq _ c b true hbc]]
  rw [update_self, update_self]

/-! ## CCX prefix: ... + T a (12 gates)

    Gate 12 = T a (start of s4). a-bit phase factor.
    Both branches' a-bit is f a (a is unchanged through all previous gates,
    and (update f c v) a = f a for a ≠ c). Same phase on both branches. -/

theorem f_to_vec_CCX_prefix_12 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
        (BaseUCom.CNOT a b))
        (BaseUCom.T a))
      * f_to_vec dim f
      = ((if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + ((if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_11 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_T_uc_eval dim a ha (update f c false)]
  rw [f_to_vec_T_uc_eval dim a ha (update f c true)]
  rw [show (update f c false) a = f a from update_neq f c a false hac]
  rw [show (update f c true) a = f a from update_neq f c a true hac]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + T b (13 gates)

    Gate 13 = T b. b-bit phase factor. Both branches' b-bit is f b
    (b is unchanged after gate 11's un-do). Same phase on both. -/

theorem f_to_vec_CCX_prefix_13 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
        (BaseUCom.CNOT a b))
        (BaseUCom.T a))
        (BaseUCom.T b))
      * f_to_vec dim f
      = ((if f b then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + ((if f b then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_12 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_T_uc_eval dim b hb (update f c false)]
  rw [f_to_vec_T_uc_eval dim b hb (update f c true)]
  rw [show (update f c false) b = f b from update_neq f c b false hbc]
  rw [show (update f c true) b = f b from update_neq f c b true hbc]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + T c (14 gates)

    Gate 14 = T c. c-bit phase factor. Branch 0 c-bit = false (no phase),
    branch 1 c-bit = true (phase exp(iπ/4)). Last asymmetry-introducing
    gate before the final H bifurcation. -/

theorem f_to_vec_CCX_prefix_14 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
        (BaseUCom.CNOT a b))
        (BaseUCom.T a))
        (BaseUCom.T b))
        (BaseUCom.T c))
      * f_to_vec dim f
      = ((1 : ℂ)
          * (if f b then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + (Complex.exp (Complex.I * (Real.pi / 4))
           * (if f b then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_13 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_T_uc_eval dim c hc (update f c false)]
  rw [f_to_vec_T_uc_eval dim c hc (update f c true)]
  rw [show (update f c false) c = false from update_eq f c false]
  rw [show (update f c true) c = true from update_eq f c true]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; simp
  · congr 1
    simp only [if_true]
    ring

/-! ## Algebraic infrastructure for the 7-T phase cancellation

    Identities involving `Complex.exp (i·π/4)` that the CCX_PHASE_CANCEL
    step will need. Each is independent of the circuit machinery. -/

/-- exp(iπ/4) · exp(-iπ/4) = 1. -/
theorem exp_pi4_mul_exp_neg_pi4 :
    Complex.exp (Complex.I * (Real.pi / 4))
      * Complex.exp (-(Complex.I * (Real.pi / 4))) = 1 := by
  rw [← Complex.exp_add]
  rw [show Complex.I * (Real.pi / 4) + -(Complex.I * (Real.pi / 4)) = 0 from by ring]
  exact Complex.exp_zero

/-- exp(-iπ/4) · exp(iπ/4) = 1. -/
theorem exp_neg_pi4_mul_exp_pi4 :
    Complex.exp (-(Complex.I * (Real.pi / 4)))
      * Complex.exp (Complex.I * (Real.pi / 4)) = 1 := by
  rw [mul_comm]; exact exp_pi4_mul_exp_neg_pi4

/-- exp(iπ/4)^2 · exp(-iπ/4)^2 = 1. -/
theorem exp_pi4_sq_mul_exp_neg_pi4_sq :
    (Complex.exp (Complex.I * (Real.pi / 4)))^2
      * (Complex.exp (-(Complex.I * (Real.pi / 4))))^2 = 1 := by
  rw [show (Complex.exp (Complex.I * (Real.pi / 4)))^2
        * (Complex.exp (-(Complex.I * (Real.pi / 4))))^2
        = (Complex.exp (Complex.I * (Real.pi / 4))
           * Complex.exp (-(Complex.I * (Real.pi / 4))))^2 from by ring]
  rw [exp_pi4_mul_exp_neg_pi4]
  ring

/-- exp(iπ/4)^4 = exp(iπ) = -1. -/
theorem exp_pi4_pow_four :
    (Complex.exp (Complex.I * (Real.pi / 4)))^4 = -1 := by
  rw [show (Complex.exp (Complex.I * (Real.pi / 4)))^4
        = Complex.exp (Complex.I * (Real.pi / 4) * 4) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show Complex.I * (Real.pi / 4) * 4 = (Real.pi : ℂ) * Complex.I from by ring]
  exact Complex.exp_pi_mul_I

/-- exp(-iπ/4)^4 = exp(-iπ) = -1. Dagger version of `exp_pi4_pow_four`. -/
theorem exp_neg_pi4_pow_four :
    (Complex.exp (-(Complex.I * (Real.pi / 4))))^4 = -1 := by
  rw [show (Complex.exp (-(Complex.I * (Real.pi / 4))))^4
        = Complex.exp (-(Complex.I * (Real.pi / 4)) * 4) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show -(Complex.I * (Real.pi / 4)) * 4 = -((Real.pi : ℂ) * Complex.I) from by ring]
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]
  ring

/-- exp(iπ/4)^2 = exp(iπ/2) = i. The basic π/4 → π/2 squaring identity.
    Useful for further reducing 2-factor exp products inside the CCX
    phase-cancellation cases. -/
theorem exp_pi4_pow_two_eq_I :
    (Complex.exp (Complex.I * (Real.pi / 4)))^2 = Complex.I := by
  rw [show (Complex.exp (Complex.I * (Real.pi / 4)))^2
        = Complex.exp (Complex.I * (Real.pi / 4) * 2) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show Complex.I * (Real.pi / 4) * 2 = (Real.pi / 2 : ℂ) * Complex.I from by ring]
  exact Complex.exp_pi_div_two_mul_I

/-- exp(-iπ/4)^2 = exp(-iπ/2) = -i. Dagger version. -/
theorem exp_neg_pi4_pow_two_eq_neg_I :
    (Complex.exp (-(Complex.I * (Real.pi / 4))))^2 = -Complex.I := by
  rw [show (Complex.exp (-(Complex.I * (Real.pi / 4))))^2
        = Complex.exp (-(Complex.I * (Real.pi / 4)) * 2) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show -(Complex.I * (Real.pi / 4)) * 2 = -((Real.pi / 2 : ℂ) * Complex.I) from by ring]
  rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I]
  simp [Complex.inv_I]

/-- 4-factor alternating pattern: `e * e⁻¹ * e * e⁻¹ = 1` where
    `e = exp(iπ/4)`. This product appears in CCX_PHASE_CANCEL α₁
    expressions for cases where (f a, f b) = (F, F). 1-line proof
    via repeated `exp_pi4_mul_exp_neg_pi4` after associativity. -/
theorem exp_pi4_alt_four :
    Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (-(Complex.I * (Real.pi / 4)))
    * Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (-(Complex.I * (Real.pi / 4))) = 1 := by
  rw [show Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
     = (Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4))))
       * (Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))) from by ring]
  rw [exp_pi4_mul_exp_neg_pi4]
  ring

/-- 4-factor consecutive-grouping pattern: `e * e * e⁻¹ * e⁻¹ = 1` where
    `e = exp(iπ/4)`. Appears in CCX_PHASE_CANCEL α₁ for (F,T,*) and
    (T,F,*) cases (2 positive π/4 factors then 2 negative). -/
theorem exp_pi4_consec_four :
    Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (-(Complex.I * (Real.pi / 4)))
    * Complex.exp (-(Complex.I * (Real.pi / 4))) = 1 := by
  rw [show Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
     = (Complex.exp (Complex.I * (Real.pi / 4)))^2
       * (Complex.exp (-(Complex.I * (Real.pi / 4))))^2 from by ring]
  exact exp_pi4_sq_mul_exp_neg_pi4_sq

/-- 4-factor palindrome pattern: `e * e⁻¹ * e⁻¹ * e = 1` where
    `e = exp(iπ/4)`. Appears in CCX_PHASE_CANCEL α₀ for (T,F,*) cases. -/
theorem exp_pi4_palindrome_four :
    Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (-(Complex.I * (Real.pi / 4)))
    * Complex.exp (-(Complex.I * (Real.pi / 4)))
    * Complex.exp (Complex.I * (Real.pi / 4)) = 1 := by
  rw [show Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (Complex.I * (Real.pi / 4))
     = (Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4))))
       * (Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (Complex.I * (Real.pi / 4))) from by ring]
  rw [exp_pi4_mul_exp_neg_pi4, exp_neg_pi4_mul_exp_pi4]
  ring

/-- 4-factor uniform-product pattern: `e * e * e * e = -1` where
    `e = exp(iπ/4)`. Appears in CCX_PHASE_CANCEL α₁ for (T,T,*) cases.
    Equivalent to `exp_pi4_pow_four` but in mul-of-mul form. -/
theorem exp_pi4_mul_four_eq_neg_one :
    Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (Complex.I * (Real.pi / 4)) = -1 := by
  rw [show Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (Complex.I * (Real.pi / 4))
     = (Complex.exp (Complex.I * (Real.pi / 4)))^4 from by ring]
  exact exp_pi4_pow_four

/-- (√2/2)² = 1/2 in ℂ. -/
theorem sqrt2_div2_sq : ((Real.sqrt 2 : ℂ) / 2) * ((Real.sqrt 2 : ℂ) / 2) = 1/2 := by
  have h : ((Real.sqrt 2 : ℂ))^2 = 2 := by
    have hreal : ((Real.sqrt 2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    exact_mod_cast hreal
  field_simp
  linear_combination h

/-- Hadamard sandwich: `H X H = Z`. -/
theorem hMatrix_σx_hMatrix : hMatrix * σx * hMatrix = σz := by
  unfold hMatrix σx σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try linear_combination 2 * sqrt2_div2_sq) <;>
    (try linear_combination -2 * sqrt2_div2_sq)

/-- Hadamard sandwich: `H Z H = X`. Dual of `hMatrix_σx_hMatrix`. -/
theorem hMatrix_σz_hMatrix : hMatrix * σz * hMatrix = σx := by
  unfold hMatrix σz σx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try linear_combination 2 * sqrt2_div2_sq) <;>
    (try linear_combination -2 * sqrt2_div2_sq)

/-- Hadamard sandwich: `H Y H = -Y`. The Y axis flips under Hadamard
    conjugation (Y is anti-symmetric under the X↔Z basis swap). -/
theorem hMatrix_σy_hMatrix : hMatrix * σy * hMatrix = -σy := by
  unfold hMatrix σy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply] <;>
    (try linear_combination 2 * Complex.I * sqrt2_div2_sq) <;>
    (try linear_combination -(2 * Complex.I) * sqrt2_div2_sq)

/-- S sandwich: `S X S† = Y`. The S gate maps X to Y under conjugation
    (a 90° rotation in the X-Y plane). -/
theorem sMatrix_σx_sdagMatrix : sMatrix * σx * sdagMatrix = σy := by
  unfold sMatrix σx sdagMatrix σy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- S sandwich: `S Y S† = -X`. -/
theorem sMatrix_σy_sdagMatrix : sMatrix * σy * sdagMatrix = -σx := by
  unfold sMatrix σy sdagMatrix σx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- S sandwich: `S Z S† = Z`. The Z axis is fixed by S (since both are
    Z-axis rotations and commute). -/
theorem sMatrix_σz_sdagMatrix : sMatrix * σz * sdagMatrix = σz := by
  unfold sMatrix σz sdagMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Dual S†-sandwich: `S† X S = -Y`. Inverse rotation of `S X S† = Y`. -/
theorem sdagMatrix_σx_sMatrix : sdagMatrix * σx * sMatrix = -σy := by
  unfold sdagMatrix σx sMatrix σy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Dual S†-sandwich: `S† Y S = X`. -/
theorem sdagMatrix_σy_sMatrix : sdagMatrix * σy * sMatrix = σx := by
  unfold sdagMatrix σy sMatrix σx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Dual S†-sandwich: `S† Z S = Z`. -/
theorem sdagMatrix_σz_sMatrix : sdagMatrix * σz * sMatrix = σz := by
  unfold sdagMatrix σz sMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- T-sandwich: `T Z T† = Z`. T is a Z-axis rotation (by π/4) so it
    commutes with σz; the sandwich therefore acts trivially. -/
theorem tMatrix_σz_tdagMatrix : tMatrix * σz * tdagMatrix = σz := by
  unfold tMatrix σz tdagMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
          ← Complex.exp_add, Complex.exp_zero]

/-- T†-sandwich: `T† Z T = Z`. Dual of `tMatrix_σz_tdagMatrix`. -/
theorem tdagMatrix_σz_tMatrix : tdagMatrix * σz * tMatrix = σz := by
  unfold tdagMatrix σz tMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
          ← Complex.exp_add, Complex.exp_zero]

/-- Circuit equivalence: `H q ; X q ; H q ≡ Z q`. This is the
    canonical Hadamard sandwich identity at the circuit level — lifts
    the matrix identity `hMatrix * σx * hMatrix = σz` (theorem
    `hMatrix_σx_hMatrix`) through `pad_u_mul_pad_u`. -/
theorem H_X_H_eq_Z {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.X n))
                       (BaseUCom.H n))
      = uc_eval (BaseUCom.Z n : BaseUCom dim) := by
  show pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
        * (pad_u dim n (rotation Real.pi 0 Real.pi)
            * pad_u dim n (rotation (Real.pi/2) 0 Real.pi))
      = pad_u dim n (rotation 0 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_H, rotation_X, rotation_Z, hMatrix_σx_hMatrix]

/-- Circuit equivalence: `H q ; Z q ; H q ≡ X q`. Dual sandwich. -/
theorem H_Z_H_eq_X {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.Z n))
                       (BaseUCom.H n))
      = uc_eval (BaseUCom.X n : BaseUCom dim) := by
  show pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
        * (pad_u dim n (rotation 0 0 Real.pi)
            * pad_u dim n (rotation (Real.pi/2) 0 Real.pi))
      = pad_u dim n (rotation Real.pi 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_H, rotation_Z, rotation_X, hMatrix_σz_hMatrix]

/-- `H q ; X q ; H q` acts as Z on `f_to_vec dim f` (Hadamard sandwich). -/
theorem f_to_vec_H_X_H (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.X n))
                       (BaseUCom.H n))
      * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [H_X_H_eq_Z]
  exact f_to_vec_Z_uc_eval dim n h f

/-- `H q ; Z q ; H q` acts as X (bit flip) on `f_to_vec dim f`. -/
theorem f_to_vec_H_Z_H (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.Z n))
                       (BaseUCom.H n))
      * f_to_vec dim f
      = f_to_vec dim (update f n (!f n)) := by
  rw [H_Z_H_eq_X]
  exact f_to_vec_X_uc_eval dim n h f

/-- `H q ; Z q` and `X q ; H q` agree on `f_to_vec dim f`. Hadamard
    interchange at the f-coord level (lift of `H_comm_Z`). -/
theorem f_to_vec_H_comm_Z (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.Z n)) * f_to_vec dim f
      = uc_eval (UCom.seq (BaseUCom.X n) (BaseUCom.H n)) * f_to_vec dim f := by
  rw [H_comm_Z]

/-- `H q ; X q` and `Z q ; H q` agree on `f_to_vec dim f`. Dual interchange. -/
theorem f_to_vec_H_comm_X (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.X n)) * f_to_vec dim f
      = uc_eval (UCom.seq (BaseUCom.Z n) (BaseUCom.H n)) * f_to_vec dim f := by
  rw [H_comm_X]

/-! ## CCX final: gate 15 (H c) + phase cancellation

    Apply H c to the 14-gate prefix. Each branch bifurcates, giving 4
    sub-branches. The phase factors must arrange so that sub-branches
    cancel/combine to yield exactly `f_to_vec dim (update f c v)` where
    `v = xor (f c) (f a && f b)` — the Toffoli output.

    Structure of the proof:
    1. Apply prefix_14 to get the 2-branch state.
    2. Apply uc_eval_seq_mul + f_to_vec_H_uc_eval per branch.
    3. update_idem collapses (update (update f c v) c v') = update f c v'.
    4. The result is a 4-branch sum that the phase-cancellation step
       must collapse to the Toffoli output.

    The cancellation is intrinsically case-bound: 8 cases for
    (f a, f b, f c) ∈ {true, false}³. Each requires simplifying
    Complex.exp products to ±1 or ±exp(iπ/4) etc. This is the
    algebraic heart of the 7-T Toffoli identity.

    Below: the statement is the LEFT-ASSOCIATED 15-gate chain (matching
    our prefix_X chain). Bridging to SQIR's right-associated `CCX`
    follows from `useq_assoc` and is a separate theorem
    (`uc_eval_CCX_eq_left_assoc`, future tick). -/

theorem f_to_vec_CCX_left_proved (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
        (BaseUCom.CNOT a b))
        (BaseUCom.T a))
        (BaseUCom.T b))
        (BaseUCom.T c))
        (BaseUCom.H c))
      * f_to_vec dim f
      = f_to_vec dim (update f c (xor (f c) (f a && f b))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_14 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_H_uc_eval dim c hc (update f c false)]
  rw [f_to_vec_H_uc_eval dim c hc (update f c true)]
  rw [show (update f c false) c = false from update_eq f c false]
  rw [show (update f c true) c = true from update_eq f c true]
  -- update_idem to simplify nested updates at c
  rw [update_idem, update_idem]
  -- 8-case analysis on (f a, f b, f c) — each case has specific
  -- complex products that simplify to ±√2/2 etc.
  -- Split explicitly into named sub-cases so each can be closed
  -- independently in future ticks.
  cases hfa : f a
  · cases hfb : f b
    · cases hfc : f c
      · -- Case (F, F, F): α₀ = √2/2, α₁ = √2/2 (4-factor alternating)
        -- Expected: f_to_vec dim (update f c F)
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_alt_four]
        -- Collapse smul nesting via smul_smul + (√2/2)² = 1/2.
        simp only [one_mul, smul_smul, sqrt2_div2_sq]
        -- LHS has 4 terms with (1/2) coefficient; F1 terms cancel,
        -- F0 terms combine to 1•F0.
        module
      · -- Case (F, F, T): α₀ = √2/2, α₁ = -√2/2
        -- Expected: f_to_vec dim (update f c T)
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_alt_four]
        simp only [one_mul, smul_smul, sqrt2_div2_sq]
        module
    · cases hfc : f c
      · -- Case (F, T, F): α₀ uses alt-4, α₁ uses consec-4
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_alt_four]
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_consec_four]
        simp only [one_mul, smul_smul, sqrt2_div2_sq]
        module
      · -- Case (F, T, T): same as (F,T,F) but fc=T
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_alt_four]
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_consec_four]
        simp only [one_mul, smul_smul, sqrt2_div2_sq]
        module
  · cases hfb : f b
    · cases hfc : f c
      · -- Case (T, F, F): α₀ has e*e⁻¹*e⁻¹*e pattern (palindrome),
        -- α₁ has e*e*e⁻¹*e⁻¹ (consec-4)
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (Complex.I * (Real.pi / 4)) = (1 : ℂ)
            from exp_pi4_palindrome_four]
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_consec_four]
        simp only [one_mul, smul_smul, sqrt2_div2_sq]
        module
      · -- Case (T, F, T): same as (T,F,F) but fc=T
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (Complex.I * (Real.pi / 4)) = (1 : ℂ)
            from exp_pi4_palindrome_four]
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_consec_four]
        simp only [one_mul, smul_smul, sqrt2_div2_sq]
        module
    · cases hfc : f c
      · -- Case (T, T, F): α₀ uses consec-4, α₁ uses mul-4 (= -1)
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_consec_four]
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4)) = (-1 : ℂ)
            from exp_pi4_mul_four_eq_neg_one]
        simp only [one_mul, smul_smul, sqrt2_div2_sq, neg_one_mul, mul_neg_one,
                   mul_neg, neg_mul, neg_neg]
        module
      · -- Case (T, T, T): same as (T,T,F) but fc=T; α₁'s -1 from
        -- exp_pi4_pow_four cancels the -1 from (if fc then -1 else 1)
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_consec_four]
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4)) = (-1 : ℂ)
            from exp_pi4_mul_four_eq_neg_one]
        simp only [one_mul, smul_smul, sqrt2_div2_sq, neg_one_mul, mul_neg_one,
                   mul_neg, neg_mul, neg_neg]
        module
  -- 8 named sub-cases, each requires explicit case analysis on r
  -- (r = false-update-index, true-update-index, or other) plus
  -- specific Complex.exp arithmetic. To discharge, would need
  -- ~50 LOC per case (8 × 50 = 400 LOC total).
  -- CCX_PHASE_CANCEL: 8 named sub-goals, each requiring complex
  -- arithmetic with exp(iπ/4) products. The exp_pi4_* helpers above
  -- give the canonical reductions but each case still needs:
  --   (1) explicit smul_add + smul_smul + add_smul to collect F0/F1 coeffs
  --   (2) ring_nf or linear_combination with exp_pi4_pow_four
  --   (3) potentially Matrix.ext to split into entry equations

/-! ## Bridge: SQIR's right-associated `BaseUCom.CCX` = left-associated chain

    `BaseUCom.CCX a b c` is built right-associated:
        seq s1 (seq s2 (seq s3 s4))
    where each sₖ is itself right-associated. Our `f_to_vec_CCX_left_proved`
    operates on the left-associated 15-gate chain. Since `useq_assoc` gives
    matrix-level equivalence, the two `uc_eval`s are equal — we just need
    to re-associate.

    Proof strategy: unfold both sides, `simp only [uc_eval_seq]` to expand
    `uc_eval (seq c1 c2) = uc_eval c2 * uc_eval c1`, then apply
    `Matrix.mul_assoc` enough times to canonicalize. -/

theorem uc_eval_CCX_eq_left_chain (dim a b c : Nat) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim)
      = uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
          (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
          (BaseUCom.CNOT a c))
          (BaseUCom.T c))
          (BaseUCom.CNOT b c))
          (BaseUCom.TDAG c))
          (BaseUCom.CNOT a c))
          (BaseUCom.CNOT a b))
          (BaseUCom.TDAG b))
          (BaseUCom.CNOT a b))
          (BaseUCom.T a))
          (BaseUCom.T b))
          (BaseUCom.T c))
          (BaseUCom.H c)) := by
  show uc_eval _ = uc_eval _
  unfold BaseUCom.CCX
  simp only [uc_eval_seq, Matrix.mul_assoc]

/-- SQIR-faithful form of `f_to_vec_CCX`, derived from the left-chain
    proof + right-association bridge. Matches the axiom statement in
    `Framework.GateDecompositions`. -/
theorem f_to_vec_CCX_proved (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim) * f_to_vec dim f
      = f_to_vec dim (update f c (xor (f c) (f a && f b))) := by
  rw [uc_eval_CCX_eq_left_chain]
  exact f_to_vec_CCX_left_proved dim a b c ha hb hc hab hac hbc f

/-- Corollary: when at least one control bit is 0, CCX leaves the state
    unchanged. -/
theorem f_to_vec_CCX_no_op (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool)
    (h : (f a && f b) = false) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim) * f_to_vec dim f
      = f_to_vec dim f := by
  rw [f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc f, h,
      Bool.xor_false, update_self]

/-- Corollary: when both control bits are 1, CCX flips the target bit. -/
theorem f_to_vec_CCX_flip (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool)
    (hfa : f a = true) (hfb : f b = true) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim) * f_to_vec dim f
      = f_to_vec dim (update f c (!f c)) := by
  rw [f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc f, hfa, hfb,
      Bool.and_self, Bool.xor_true]

/-- CCX is its own inverse on basis vectors: applying it twice returns the
    original state. Follows from `f_to_vec_CCX_proved` plus the fact that
    `update_neq` keeps the controls a, b unchanged across the inner update,
    so the second xor flips back what the first xor flipped.
    -- SQIR/SQIR/UnitaryOps.v analog: CCX is the Toffoli gate, an involution. -/
theorem f_to_vec_CCX_involutive (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim) *
      (uc_eval (BaseUCom.CCX a b c : BaseUCom dim) * f_to_vec dim f)
      = f_to_vec dim f := by
  rw [f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc f]
  rw [f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc _]
  -- Inner state: update f c (xor (f c) (f a && f b))
  -- Reading a, b through this update returns f a, f b since a ≠ c, b ≠ c.
  rw [update_neq f c a (xor (f c) (f a && f b)) hac,
      update_neq f c b (xor (f c) (f a && f b)) hbc,
      update_eq f c (xor (f c) (f a && f b))]
  -- Goal: f_to_vec dim (update (update f c (xor ...)) c
  --         (xor (xor (f c) (f a && f b)) (f a && f b))) = f_to_vec dim f
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false, update_idem, update_self]

/-! ## CCX_eq_toffoliMatrix: matrix equality from f_to_vec_CCX

    Two 8×8 matrices are equal iff their actions on all 8 basis vectors agree.
    `uc_eval (BaseUCom.CCX 0 1 2)` and `toffoliMatrix` should agree because
    both implement the Toffoli permutation: identity on indices 0-5, and
    swap 6 ↔ 7. -/

/-- The natural-number inverse of `funbool_to_nat`: extracts bit at position
    `n-1-i` of `j`. For `j < 2^n`, `funbool_to_nat n (nat_to_funbool n j) = j`. -/
def nat_to_funbool (n : Nat) (j : Nat) : Nat → Bool :=
  fun i => (j / 2^(n - 1 - i)) % 2 = 1

/-- Two square matrices are equal iff their actions on all basis vectors agree. -/
theorem matrix_eq_of_basis_action {n : Nat} (M N : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ k : Fin n, M * basis_vector n k.val = N * basis_vector n k.val) :
    M = N := by
  ext i j
  have hj : M * basis_vector n j.val = N * basis_vector n j.val := h j
  have key : (M * basis_vector n j.val) i 0 = (N * basis_vector n j.val) i 0 := by rw [hj]
  rw [mul_basis_vector_apply M j.val j.isLt i] at key
  rw [mul_basis_vector_apply N j.val j.isLt i] at key
  exact key

/-- Inverse property: `funbool_to_nat n (nat_to_funbool n j) = j` for `j < 2^n`. -/
theorem funbool_to_nat_nat_to_funbool (n j : Nat) (h : j < 2^n) :
    funbool_to_nat n (nat_to_funbool n j) = j := by
  induction n generalizing j with
  | zero =>
      have : j = 0 := by simp at h; omega
      rw [this]; rfl
  | succ k ih =>
      rw [funbool_to_nat_succ]
      -- Top bit: nat_to_funbool (k+1) j k corresponds to bit position 0 of j.
      have h_top : nat_to_funbool (k+1) j k = decide (j % 2 = 1) := by
        unfold nat_to_funbool
        have h_zero : k + 1 - 1 - k = 0 := by omega
        simp [h_zero]
      rw [h_top]
      -- Lower bits: nat_to_funbool (k+1) j i = nat_to_funbool k (j/2) i for i < k.
      have h_lower : ∀ i, i < k →
          nat_to_funbool (k+1) j i = nat_to_funbool k (j/2) i := by
        intro i hi
        unfold nat_to_funbool
        have h_eq : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
        rw [h_eq, pow_succ]
        rw [show j / (2^(k-1-i) * 2) = j / 2 / 2^(k-1-i) from by
              rw [Nat.div_div_eq_div_mul]; ring_nf]
      rw [funbool_to_nat_congr k _ _ h_lower]
      have h_ih : j / 2 < 2^k := by
        rw [show 2^(k+1) = 2 * 2^k from by ring] at h
        omega
      rw [ih (j/2) h_ih]
      -- Goal: 2 * (j/2) + (if decide (j%2=1) then 1 else 0) = j
      by_cases h_mod : j % 2 = 1
      · rw [show (decide (j % 2 = 1) = true) from decide_eq_true h_mod]
        simp; omega
      · have h_mod_zero : j % 2 = 0 := by omega
        rw [show (decide (j % 2 = 1) = false) from decide_eq_false h_mod]
        simp; omega

/-- Bridge: every basis vector at index `j < 2^n` can be written as
    `f_to_vec` of the inverse-funbool-to-nat function. Nat-indexed form,
    avoids `Fin (2^n)` vs `Fin 8` unification friction. -/
theorem basis_vector_eq_f_to_vec_nat (n j : Nat) (h : j < 2^n) :
    basis_vector (2^n) j = f_to_vec n (nat_to_funbool n j) := by
  unfold f_to_vec
  congr 1
  exact (funbool_to_nat_nat_to_funbool n j h).symm

/-- Fin-indexed version (legacy). -/
theorem basis_vector_eq_f_to_vec_nat_to_funbool (n : Nat) (j : Fin (2^n)) :
    basis_vector (2^n) j.val = f_to_vec n (nat_to_funbool n j.val) :=
  basis_vector_eq_f_to_vec_nat n j.val j.isLt

/-- For k.val = 0: nat_to_funbool 3 0 i = false for all i. -/
theorem nat_to_funbool_3_0_eq_false (i : Nat) :
    nat_to_funbool 3 0 i = false := by
  unfold nat_to_funbool
  simp

/-- For k.val = 1 = 001₂: bit pattern is (false, false, true) at indices (0, 1, 2). -/
theorem nat_to_funbool_3_1_zero : nat_to_funbool 3 1 0 = false := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_1_one : nat_to_funbool 3 1 1 = false := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_1_two : nat_to_funbool 3 1 2 = true := by
  unfold nat_to_funbool; simp

/-- For k.val = 2 = 010₂: bit pattern (false, true, false). -/
theorem nat_to_funbool_3_2_zero : nat_to_funbool 3 2 0 = false := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_2_one : nat_to_funbool 3 2 1 = true := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_2_two : nat_to_funbool 3 2 2 = false := by
  unfold nat_to_funbool; simp

/-- For k.val = 3 = 011₂: bit pattern (false, true, true). -/
theorem nat_to_funbool_3_3_zero : nat_to_funbool 3 3 0 = false := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_3_one : nat_to_funbool 3 3 1 = true := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_3_two : nat_to_funbool 3 3 2 = true := by
  unfold nat_to_funbool; simp

/-- For k.val = 4 = 100₂: bit pattern (true, false, false). -/
theorem nat_to_funbool_3_4_zero : nat_to_funbool 3 4 0 = true := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_4_one : nat_to_funbool 3 4 1 = false := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_4_two : nat_to_funbool 3 4 2 = false := by
  unfold nat_to_funbool; simp

/-- For k.val = 5 = 101₂: bit pattern (true, false, true). -/
theorem nat_to_funbool_3_5_zero : nat_to_funbool 3 5 0 = true := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_5_one : nat_to_funbool 3 5 1 = false := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_5_two : nat_to_funbool 3 5 2 = true := by
  unfold nat_to_funbool; simp

/-- For k.val = 6 = 110₂: bit pattern (true, true, false). -/
theorem nat_to_funbool_3_6_zero : nat_to_funbool 3 6 0 = true := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_6_one : nat_to_funbool 3 6 1 = true := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_6_two : nat_to_funbool 3 6 2 = false := by
  unfold nat_to_funbool; simp

/-- For k.val = 7 = 111₂: bit pattern (true, true, true). -/
theorem nat_to_funbool_3_7_zero : nat_to_funbool 3 7 0 = true := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_7_one : nat_to_funbool 3 7 1 = true := by
  unfold nat_to_funbool; simp
theorem nat_to_funbool_3_7_two : nat_to_funbool 3 7 2 = true := by
  unfold nat_to_funbool; simp

-- NOTE: `CCX_eq_toffoliMatrix_proved` lives in `GateDecompositions.lean`
-- because it references `toffoliMatrix` which is defined there. Helpers used
-- there (matrix_eq_of_basis_action, basis_vector_eq_f_to_vec_nat,
-- nat_to_funbool, nat_to_funbool_3_0_eq_false) are all in this file.

/-- Matrix-level Toffoli involution: applying CCX twice is the identity matrix.
    Lifted from `f_to_vec_CCX_involutive` via `matrix_eq_of_basis_action`.
    -- SQIR/SQIR/UnitaryOps.v analog: CCX is self-inverse (involution). -/
theorem CCX_CCX_eq_one (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim) *
      uc_eval (BaseUCom.CCX a b c : BaseUCom dim)
    = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool, Matrix.mul_assoc,
      f_to_vec_CCX_involutive dim a b c ha hb hc hab hac hbc, Matrix.one_mul]

/-- UCom.equiv form of `CCX_CCX_eq_one`: at the circuit level,
    `CCX a b c ; CCX a b c ≅ ID 0` whenever `dim ≥ 1`. Useful for
    Toffoli-pair cancellation in circuit-level rewriting.
    -- SQIR/SQIR/Equivalences.v analog: SKIP-style identity (X_X_id pattern). -/
theorem CCX_CCX_id {dim : Nat} (a b c : Nat) (h0 : 0 < dim)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    UCom.equiv
      (UCom.seq (BaseUCom.CCX a b c : BaseUCom dim) (BaseUCom.CCX a b c))
      (BaseUCom.ID 0) := by
  show uc_eval (BaseUCom.CCX a b c : BaseUCom dim) *
         uc_eval (BaseUCom.CCX a b c : BaseUCom dim)
       = uc_eval (BaseUCom.ID 0 : BaseUCom dim)
  rw [uc_eval_ID_eq_one h0]
  exact CCX_CCX_eq_one dim a b c ha hb hc hab hac hbc

/-- `CCX a b c ; CCX a b c ; CCX a b c` acts as a single CCX on
    `f_to_vec dim f` (CCX³ = CCX, since CCX² = ID). Direct corollary
    of `CCX_CCX_eq_one` (matrix-level) + `f_to_vec_CCX_proved`.
    Completes the 3-chain family on basis states: X³, Z³, CNOT³, CCX³.
    -- SQIR/SQIR/UnitaryOps.v analog: Toffoli 3-chain identity. -/
theorem f_to_vec_CCX_CCX_CCX (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.CCX a b c : BaseUCom dim)
                                (BaseUCom.CCX a b c))
                       (BaseUCom.CCX a b c))
      * f_to_vec dim f
      = f_to_vec dim (update f c (xor (f c) (f a && f b))) := by
  -- Unfold outer seq, then inner seq, to get CCX * (CCX * (CCX * f_to_vec f)).
  rw [uc_eval_seq_mul, uc_eval_seq_mul]
  -- Innermost CCX * f_to_vec f reduces to f_to_vec (update ...) by f_to_vec_CCX_proved.
  rw [f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc f]
  -- Remaining outer two CCXs act on the updated f_to_vec; by involution, return as-is.
  exact f_to_vec_CCX_involutive dim a b c ha hb hc hab hac hbc _

/-- `X q ; X q ; X q ; X q ; X q` acts as a single X on `f_to_vec dim f`
    (X⁵ = X, since X⁴ = ID). Iter 101 extension of the basis-state
    Pauli-chain family. Useful for circuit-rewriting passes that
    encounter X-gate odd-length chains. -/
theorem f_to_vec_X_X_X_X_X (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.X n : BaseUCom dim) (BaseUCom.X n))
              (BaseUCom.X n)) (BaseUCom.X n)) (BaseUCom.X n))
      * f_to_vec dim f
      = f_to_vec dim (update f n (!f n)) := by
  -- uc_eval(seq^4 X) * f_to_vec f = X * (uc_eval(seq^3 X) * f_to_vec f) by uc_eval_seq_mul.
  -- Inner uc_eval(seq^3 X) * f_to_vec f = f_to_vec f by f_to_vec_X_X_X_X (X⁴ = ID).
  -- Then X * f_to_vec f = f_to_vec (update f n (!f n)) by f_to_vec_X_uc_eval.
  rw [uc_eval_seq_mul]
  rw [f_to_vec_X_X_X_X dim n h f]
  exact f_to_vec_X_uc_eval dim n h f

-- SQIR/SQIR/Equivalences.v (Pauli order-cycle analog of Z⁵ = Z): f_to_vec lift
/-- `Z q ; Z q ; Z q ; Z q ; Z q` acts as a single Z on `f_to_vec dim f`
    (Z⁵ = Z, since Z⁴ = ID). Mirrors `f_to_vec_X_X_X_X_X` (Iter 101)
    for the Pauli Z gate's cyclic phase action. Useful for circuit-
    rewriting passes that encounter Z-gate odd-length chains. -/
theorem f_to_vec_Z_Z_Z_Z_Z (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.Z n : BaseUCom dim) (BaseUCom.Z n))
              (BaseUCom.Z n)) (BaseUCom.Z n)) (BaseUCom.Z n))
      * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  -- uc_eval(seq^4 Z) * f_to_vec f = Z * (uc_eval(seq^3 Z) * f_to_vec f) by uc_eval_seq_mul.
  -- Inner uc_eval(seq^3 Z) * f_to_vec f = f_to_vec f by f_to_vec_Z_Z_Z_Z (Z⁴ = ID).
  -- Then Z * f_to_vec f = (±1) • f_to_vec f by f_to_vec_Z_uc_eval.
  rw [uc_eval_seq_mul]
  rw [f_to_vec_Z_Z_Z_Z dim n h f]
  exact f_to_vec_Z_uc_eval dim n h f

-- SQIR/SQIR/Equivalences.v line 109: CNOT_CNOT_id
/-- Matrix-level CNOT involution: applying CNOT twice is the identity matrix.
    Lifted from `f_to_vec_CNOT_CNOT` via `matrix_eq_of_basis_action`. -/
theorem CNOT_CNOT_eq_one (dim i j : Nat)
    (hi : i < dim) (hj : j < dim) (hij : i ≠ j) :
    uc_eval (UCom.seq (BaseUCom.CNOT i j : BaseUCom dim) (BaseUCom.CNOT i j))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_CNOT_CNOT dim i j hi hj hij, Matrix.one_mul]

/-- UCom.equiv form of `CNOT_CNOT_eq_one`: at the circuit level,
    `CNOT i j ; CNOT i j ≅ ID 0` whenever `dim ≥ 1`. -/
theorem CNOT_CNOT_id {dim : Nat} (i j : Nat) (h0 : 0 < dim)
    (hi : i < dim) (hj : j < dim) (hij : i ≠ j) :
    UCom.equiv
      (UCom.seq (UCom.seq (BaseUCom.CNOT i j : BaseUCom dim) (BaseUCom.CNOT i j))
                (BaseUCom.ID 0))
      (BaseUCom.ID 0) := by
  show uc_eval (BaseUCom.ID 0 : BaseUCom dim) *
         uc_eval (UCom.seq (BaseUCom.CNOT i j : BaseUCom dim) (BaseUCom.CNOT i j))
       = uc_eval (BaseUCom.ID 0 : BaseUCom dim)
  rw [uc_eval_ID_eq_one h0, CNOT_CNOT_eq_one dim i j hi hj hij, Matrix.one_mul]

/-- **Seq-form basis-state lift** of `CCX_CCX_eq_one`. Cleaner
    statement than `f_to_vec_CCX_involutive` (product form): uses
    `UCom.seq` directly. Useful for chained rewrites at the seq
    level. -- SQIR/SQIR/Equivalences.v: CCX_CCX_id at basis state. -/
theorem f_to_vec_seq_CCX_CCX_eq_self (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.CCX a b c : BaseUCom dim) (BaseUCom.CCX a b c))
      * f_to_vec dim f
      = f_to_vec dim f := by
  show (uc_eval (BaseUCom.CCX a b c : BaseUCom dim)
        * uc_eval (BaseUCom.CCX a b c : BaseUCom dim))
       * f_to_vec dim f = f_to_vec dim f
  rw [CCX_CCX_eq_one dim a b c ha hb hc hab hac hbc, Matrix.one_mul]

/-- **Seq-form basis-state lift** of `CNOT_CNOT_eq_one`. The matrix-
    level theorem is ALREADY in seq form, so the `rw` applies
    directly without a `show`. -/
theorem f_to_vec_seq_CNOT_CNOT_eq_self (dim i j : Nat)
    (hi : i < dim) (hj : j < dim) (hij : i ≠ j) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.CNOT i j : BaseUCom dim) (BaseUCom.CNOT i j))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [CNOT_CNOT_eq_one dim i j hi hj hij, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v line 68: X_X_id
/-- Matrix-level X involution: applying X twice is the identity matrix.
    Lifted from `f_to_vec_X_X` via `matrix_eq_of_basis_action`.
    **Completes the X/CNOT/CCX matrix-level involution family** —
    each is a single-line application of the basis-action lift, using
    the existing per-gate basis-state involutions. -/
theorem X_X_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (BaseUCom.X n : BaseUCom dim) (BaseUCom.X n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_X_X dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v line ~71: Y_Y_id
/-- Matrix-level Y involution: applying Y twice is the identity matrix.
    Lifted from `f_to_vec_Y_Y` via `matrix_eq_of_basis_action`. -/
theorem Y_Y_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_Y_Y dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v line ~74: Z_Z_id
/-- Matrix-level Z involution: applying Z twice is the identity matrix.
    Lifted from `f_to_vec_Z_Z` via `matrix_eq_of_basis_action`. -/
theorem Z_Z_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (BaseUCom.Z n : BaseUCom dim) (BaseUCom.Z n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_Z_Z dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v line ~77: H_H_id
/-- Matrix-level H involution: applying H twice is the identity matrix.
    Lifted from `f_to_vec_H_H` via `matrix_eq_of_basis_action`.
    **Extends the Pauli involution family** (X/Y/Z/H) to matrix-level. -/
theorem H_H_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_H_H dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v: X⁴ = ID (order-4 identity for Pauli X)
/-- Matrix-level X order-4 identity: `X⁴ = 1`. Lifted from
    `f_to_vec_X_X_X_X` via `matrix_eq_of_basis_action`. Mirrors the
    pattern of `X_X_eq_one` but for the 4-chain. Useful for cyclic
    cancellation in circuits where X gates may appear an even number
    of times on the same qubit. -/
theorem X_X_X_X_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.X n : BaseUCom dim)
                                          (BaseUCom.X n))
                                (BaseUCom.X n))
                      (BaseUCom.X n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_X_X_X_X dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v: Z⁴ = ID (order-4 identity for Pauli Z)
/-- Matrix-level Z order-4 identity: `Z⁴ = 1`. Lifted from
    `f_to_vec_Z_Z_Z_Z` via `matrix_eq_of_basis_action`. -/
theorem Z_Z_Z_Z_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.Z n : BaseUCom dim)
                                          (BaseUCom.Z n))
                                (BaseUCom.Z n))
                      (BaseUCom.Z n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_Z_Z_Z_Z dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v: S⁴ = ID (order-4 identity for S phase gate)
/-- Matrix-level S order-4 identity: `S⁴ = 1`. Derived from
    existing `S_S_S_S_eq_ID` (RHS `uc_eval (BaseUCom.ID n)`) +
    `uc_eval_ID_eq_one` (converts to matrix `1` when `n < dim`). -/
theorem S_S_S_S_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
                       (BaseUCom.S n)) (BaseUCom.S n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  rw [S_S_S_S_eq_ID, uc_eval_ID_eq_one h]

-- SQIR/SQIR/Equivalences.v: H⁴ = ID
/-- Matrix-level H order-4 identity: `H⁴ = 1`. Direct lift of
    `H_H_H_H_eq_ID` via `uc_eval_ID_eq_one`. -/
theorem H_H_H_H_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
                       (BaseUCom.H n)) (BaseUCom.H n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  rw [H_H_H_H_eq_ID, uc_eval_ID_eq_one h]

-- SQIR/SQIR/Equivalences.v: Y⁴ = ID (order-4 identity for Pauli Y)
/-- Matrix-level Y order-4 identity: `Y⁴ = 1`. **Derived via
    composition** rather than f_to_vec lift (no
    `f_to_vec_Y_Y_Y_Y` exists). Strategy: reassociate
    `Y * (Y * (Y * Y))` to `(Y * Y) * (Y * Y)` via `Matrix.mul_assoc`,
    then collapse each pair via `Y_Y_eq_one`. -/
theorem Y_Y_Y_Y_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.Y n : BaseUCom dim)
                                          (BaseUCom.Y n))
                                (BaseUCom.Y n))
                      (BaseUCom.Y n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  -- uc_eval (UCom.seq ... Y) = Y * (Y * (Y * Y)) (left-associated bracket).
  show uc_eval (BaseUCom.Y n : BaseUCom dim)
        * (uc_eval (BaseUCom.Y n)
          * (uc_eval (BaseUCom.Y n) * uc_eval (BaseUCom.Y n))) = 1
  rw [← Matrix.mul_assoc
        (uc_eval (BaseUCom.Y n : BaseUCom dim))
        (uc_eval (BaseUCom.Y n))
        (uc_eval (BaseUCom.Y n) * uc_eval (BaseUCom.Y n))]
  -- Now: (Y * Y) * (Y * Y) = 1
  show (uc_eval (UCom.seq (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n)))
        * (uc_eval (UCom.seq (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))) = 1
  rw [Y_Y_eq_one dim n h, Matrix.one_mul]

/-- Basis-state lift of `Y_Y_Y_Y_eq_one` (matrix-level Y⁴ = 1).
    Useful for chaining at the f_to_vec layer (per-bit cascade
    correctness proofs needing Y-gate involution in 4-chain form). -/
theorem f_to_vec_Y_Y_Y_Y (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.Y n : BaseUCom dim)
                                          (BaseUCom.Y n))
                                (BaseUCom.Y n))
                      (BaseUCom.Y n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [Y_Y_Y_Y_eq_one dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: Y⁵ = Y at basis level
/-- `Y q ; Y q ; Y q ; Y q ; Y q` acts as a single `Y q` on `f_to_vec dim f`
    (Y⁵ = Y, since Y⁴ = ID). **Relational form**: unlike X⁵ and Z⁵ which
    have closed-form basis-state results (`update` for X, `±1 •` for Z),
    Y introduces an `i·(-1)^b` phase that has no closed form on
    `f_to_vec dim f` alone. So the cleanest statement is
    `uc_eval(Y⁵) · v = uc_eval(Y) · v`. Completes the Pauli order-5
    basis-state family (X⁵/Y⁵/Z⁵) mirroring Iter 101 and the Iter 132
    SQIR-tick. -/
theorem f_to_vec_Y_Y_Y_Y_Y (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))
              (BaseUCom.Y n)) (BaseUCom.Y n)) (BaseUCom.Y n))
      * f_to_vec dim f
      = uc_eval (BaseUCom.Y n : BaseUCom dim) * f_to_vec dim f := by
  -- uc_eval(seq^4 Y) * f_to_vec f = Y * (uc_eval(seq^3 Y) * f_to_vec f) by uc_eval_seq_mul.
  -- Inner uc_eval(seq^3 Y) * f_to_vec f = f_to_vec f by f_to_vec_Y_Y_Y_Y (Y⁴ = ID).
  rw [uc_eval_seq_mul]
  rw [f_to_vec_Y_Y_Y_Y dim n h f]

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: Y⁵ = Y at matrix level
/-- **Matrix-level Y order-5 cyclic identity**: `Y⁵ = Y`. Direct
    consequence of `Y_Y_Y_Y_eq_one` (Y⁴ = 1) plus `Matrix.mul_one`.
    More useful than the f_to_vec form (Iter 133) when the input is
    NOT a basis state — e.g., during circuit-equivalence rewriting
    on arbitrary state vectors. Per Iter 132 reflection. -/
theorem Y_Y_Y_Y_Y_eq_Y (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))
              (BaseUCom.Y n)) (BaseUCom.Y n)) (BaseUCom.Y n))
      = uc_eval (BaseUCom.Y n : BaseUCom dim) := by
  -- uc_eval (seq^4 Y) unfolds (defeq) to Y * uc_eval(seq^3 Y).
  show uc_eval (BaseUCom.Y n : BaseUCom dim)
        * uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))
                                       (BaseUCom.Y n)) (BaseUCom.Y n))
       = uc_eval (BaseUCom.Y n : BaseUCom dim)
  rw [Y_Y_Y_Y_eq_one dim n h, Matrix.mul_one]

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: Z⁵ = Z at matrix level
/-- **Matrix-level Z order-5 cyclic identity**: `Z⁵ = Z`. Direct
    consequence of `Z_Z_Z_Z_eq_one` (Z⁴ = 1) plus `Matrix.mul_one`.
    Mirrors `Y_Y_Y_Y_Y_eq_Y` (Iter 137) — same proof structure.
    Matrix-level form for circuit-equivalence proofs on arbitrary
    state vectors. -/
theorem Z_Z_Z_Z_Z_eq_Z (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.Z n : BaseUCom dim) (BaseUCom.Z n))
              (BaseUCom.Z n)) (BaseUCom.Z n)) (BaseUCom.Z n))
      = uc_eval (BaseUCom.Z n : BaseUCom dim) := by
  -- uc_eval (seq^4 Z) unfolds (defeq) to Z * uc_eval(seq^3 Z).
  show uc_eval (BaseUCom.Z n : BaseUCom dim)
        * uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.Z n : BaseUCom dim) (BaseUCom.Z n))
                                       (BaseUCom.Z n)) (BaseUCom.Z n))
       = uc_eval (BaseUCom.Z n : BaseUCom dim)
  rw [Z_Z_Z_Z_eq_one dim n h, Matrix.mul_one]

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: X⁵ = X at matrix level
/-- **Matrix-level X order-5 cyclic identity**: `X⁵ = X`. Direct
    consequence of `X_X_X_X_eq_one` (X⁴ = 1) plus `Matrix.mul_one`.
    Completes the Pauli matrix-level order-5 family (X/Y/Z all done
    after this — Y from Iter 137, Z from the Iter 144 SQIR-tick). -/
theorem X_X_X_X_X_eq_X (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.X n : BaseUCom dim) (BaseUCom.X n))
              (BaseUCom.X n)) (BaseUCom.X n)) (BaseUCom.X n))
      = uc_eval (BaseUCom.X n : BaseUCom dim) := by
  -- uc_eval (seq^4 X) unfolds (defeq) to X * uc_eval(seq^3 X).
  show uc_eval (BaseUCom.X n : BaseUCom dim)
        * uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.X n : BaseUCom dim) (BaseUCom.X n))
                                       (BaseUCom.X n)) (BaseUCom.X n))
       = uc_eval (BaseUCom.X n : BaseUCom dim)
  rw [X_X_X_X_eq_one dim n h, Matrix.mul_one]

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: H⁵ = H at matrix level
/-- **Matrix-level H order-5 cyclic identity**: `H⁵ = H`. Direct
    consequence of `H_H_H_H_eq_one` (H⁴ = 1) plus `Matrix.mul_one`.
    Mirrors `X_X_X_X_X_eq_X`/`Y_Y_Y_Y_Y_eq_Y`/`Z_Z_Z_Z_Z_eq_Z`,
    same proof shape. Matrix-level form for circuit-equivalence
    proofs on arbitrary state vectors (not just basis states). -/
theorem H_H_H_H_H_eq_H (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
              (BaseUCom.H n)) (BaseUCom.H n)) (BaseUCom.H n))
      = uc_eval (BaseUCom.H n : BaseUCom dim) := by
  -- uc_eval (seq^4 H) unfolds (defeq) to H * uc_eval(seq^3 H).
  show uc_eval (BaseUCom.H n : BaseUCom dim)
        * uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
                                       (BaseUCom.H n)) (BaseUCom.H n))
       = uc_eval (BaseUCom.H n : BaseUCom dim)
  rw [H_H_H_H_eq_one dim n h, Matrix.mul_one]

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: S⁵ = S at matrix level
/-- **Matrix-level S order-5 cyclic identity**: `S⁵ = S`. Direct
    consequence of `S_S_S_S_eq_one` (S⁴ = 1) plus `Matrix.mul_one`.
    Same proof pattern as X/Y/Z/H matrix-level lifts. Completes
    the Clifford matrix-level order-5 family (X, Y, Z, H, S all
    done now). -/
theorem S_S_S_S_S_eq_S (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
              (BaseUCom.S n)) (BaseUCom.S n)) (BaseUCom.S n))
      = uc_eval (BaseUCom.S n : BaseUCom dim) := by
  -- uc_eval (seq^4 S) unfolds (defeq) to S * uc_eval(seq^3 S).
  show uc_eval (BaseUCom.S n : BaseUCom dim)
        * uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
                                       (BaseUCom.S n)) (BaseUCom.S n))
       = uc_eval (BaseUCom.S n : BaseUCom dim)
  rw [S_S_S_S_eq_one dim n h, Matrix.mul_one]

/-- Toffoli control symmetry: swapping the two control qubits leaves
    the gate's matrix unchanged. Follows from `f_to_vec_CCX_proved`,
    which uses `f a && f b` — symmetric in `a, b` via `Bool.and_comm`.
    -- SQIR/SQIR/UnitaryOps.v analog: CCX a b c ≡ CCX b a c. -/
theorem CCX_control_symm {dim : Nat} (a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim)
      = uc_eval (BaseUCom.CCX b a c : BaseUCom dim) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc,
      f_to_vec_CCX_proved dim b a c hb ha hc (Ne.symm hab) hbc hac,
      Bool.and_comm]

/-- UCom.equiv form of `CCX_control_symm`: at the circuit level,
    `CCX a b c ≅ CCX b a c`. Direct corollary since `UCom.equiv` is
    just `uc_eval` equality.
    -- SQIR/SQIR/Equivalences.v style. -/
theorem CCX_control_symm_equiv {dim : Nat} (a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    UCom.equiv (BaseUCom.CCX a b c : BaseUCom dim) (BaseUCom.CCX b a c) :=
  CCX_control_symm a b c ha hb hc hab hac hbc

/-- Basis-state lift of `CCX_control_symm`: applying CCX with controls
    `(a, b)` to `f_to_vec dim f` gives the same result as CCX with
    controls swapped `(b, a)`. Direct corollary, useful when the
    available rewriting form is on `f_to_vec`-applied form.
    -- SQIR/SQIR/UnitaryOps.v: CCX-control-symmetry at the basis level. -/
theorem f_to_vec_CCX_control_symm (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim) * f_to_vec dim f
      = uc_eval (BaseUCom.CCX b a c : BaseUCom dim) * f_to_vec dim f := by
  rw [CCX_control_symm a b c ha hb hc hab hac hbc]

/-! ## Status / next steps

    What's proven above is sufficient to express how `pad_u dim n M` acts
    on a single basis state `f_to_vec dim f`. Specifically the chain
    `f_to_vec_eq_basis_padEquiv` + `pad_u_σx_on_basis_vector_padEquiv`
    + `padEquiv_val_formula` + `funbool_to_nat_split` shows
    `pad_u dim n σx * f_to_vec dim f` is the basis state at the integer
    obtained by flipping bit at qubit-`n` position.

    The next milestones (not closed in this iteration):

    1. `funbool_to_nat_update_negate`: relate `funbool_to_nat dim (update f n (!f n))`
       back to `funbool_to_nat dim f` with the middle bit flipped. Requires
       a lemma `funbool_to_nat_congr : (∀ i < n, f i = g i) → funbool_to_nat n f = funbool_to_nat n g`
       (induction on n).
    2. Lift to `f`-coordinates: `pad_u_σx_on_f_to_vec`,
       `pad_u_proj0_on_f_to_vec`, `pad_u_proj1_on_f_to_vec`.
    3. Compose for `pad_ctrl`: case-split on `f i` and combine.
    4. Conclude `f_to_vec_CNOT`.

    Each is < 50 LOC of Lean. Total remaining: ~200 LOC for `f_to_vec_CNOT`.
    Then per-gate work for `f_to_vec_H/T/TDAG` (similar size) + chaining
    for `f_to_vec_CCX`. -/

end FormalRV.Framework
