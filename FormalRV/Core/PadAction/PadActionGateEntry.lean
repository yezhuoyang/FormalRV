import FormalRV.Core.UnitarySem
import FormalRV.Core.QuantumLib
import FormalRV.Core.PadAction.PadActionDefinitions

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker

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
theorem exp_pi4_mul_exp_neg_pi4_aux :
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

end FormalRV.Framework
