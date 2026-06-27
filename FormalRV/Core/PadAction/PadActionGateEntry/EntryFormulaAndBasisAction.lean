/- PadActionGateEntry — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
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


end FormalRV.Framework
