/- UnitarySem — Part5 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Core.UnitarySem.Part4

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker  -- enables `A ⊗ₖ B` notation for Matrix.kronecker

/-! ## SKIP and ID equivalences -/

/-- σi (the explicit `!![1,0;0,1]` matrix) equals `Iₙ 2` (mathlib's identity). -/
theorem σi_eq_Iₙ_two : σi = Iₙ 2 := by
  unfold σi Iₙ
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- pad_u of the identity matrix at any qubit gives the global identity.
    Proof sketch: substitute σi = Iₙ 2, apply Iₙ_kron_Iₙ twice
    (Iₙ a ⊗ₖ Iₙ b = 1 as a Matrix on (Fin a × Fin b)), then reindex
    of identity is identity. -/
theorem pad_u_id {dim n : Nat} (h : n < dim) :
    pad_u dim n σi = (1 : Square dim) := by
  unfold pad_u
  rw [dif_pos h]
  rw [σi_eq_Iₙ_two]
  -- Goal: reindex e e ((Iₙ (2^n) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ (2^(dim-n-1))) = 1
  -- First, Iₙ(2^n) ⊗ₖ Iₙ 2 = 1 : Matrix (Fin (2^n) × Fin 2) ...
  rw [show (Iₙ (2^n) ⊗ₖ Iₙ 2 : Matrix (Fin (2^n) × Fin 2) (Fin (2^n) × Fin 2) ℂ) = 1 from
        Iₙ_kron_Iₙ (2^n) 2]
  -- Now goal: reindex e e (1 ⊗ₖ Iₙ (2^(dim-n-1))) = 1
  rw [show ((1 : Matrix (Fin (2^n) × Fin 2) (Fin (2^n) × Fin 2) ℂ) ⊗ₖ Iₙ (2^(dim-n-1)))
        = 1 from by
          unfold Iₙ
          exact Matrix.one_kronecker_one]
  -- Now goal: reindex e e (1 : Matrix _ _ ℂ) = 1
  exact Matrix.submatrix_one_equiv _

/-- `pad_u` of the identity 2×2 matrix (the canonical `1`) gives the
    global identity. Trivial corollary of `σi_eq_one` and `pad_u_id`. -/
theorem pad_u_one {dim n : Nat} (h : n < dim) :
    pad_u dim n (1 : Matrix (Fin 2) (Fin 2) ℂ) = (1 : Square dim) := by
  rw [← σi_eq_one]
  exact pad_u_id h

-- SQIR/SQIR/UnitarySem.v: base case of pad's single-qubit induction.
/-- `pad_u 1 0 M = M`: padding a 2×2 unitary at qubit 0 of a 1-qubit system
    is the identity operation. Since `2^1 = 2` definitionally, both sides
    inhabit `Matrix (Fin 2) (Fin 2) ℂ` without any explicit cast.

    Both inner kron multipliers `Iₙ (2^0) = Iₙ 1` and `Iₙ (2^(1-0-1)) = Iₙ 1`
    are the 1×1 identity, so the kron entry at `((0, b), 0) ((0, b'), 0)`
    equals `1 · M b b' · 1 = M b b'`. The reindex `e` from
    `(Fin 1 × Fin 2) × Fin 1 ≃ Fin 2` then identifies `i ↔ ((0, i), 0)`.

    Proof currently sorried: requires unwinding the explicit `Fin`
    arithmetic of `finProdFinEquiv` and `Fin.castOrderIso` at the
    concrete `dim=1, n=0` instance. Sorry name: `TODO_pad_u_dim_eq_one`. -/
theorem pad_u_dim_eq_one (M : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u 1 0 M = M := by
  unfold pad_u
  simp only [dif_pos (Nat.zero_lt_one)]
  ext i j
  show (Matrix.reindex _ _ ((Iₙ (2^0) ⊗ₖ M) ⊗ₖ Iₙ (2^(1-0-1)))) i j = M i j
  simp [Iₙ, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> rfl

open BaseUCom in
/-- Well-typed counterpart of `ID_ill_typed`: `uc_eval (ID q) = 1`
    when `q < dim`. The semantics of `ID q` is the identity matrix on
    `dim` qubits — `rotation 0 0 0` is the 2×2 identity, and padding it
    via `pad_u_id` preserves identity. -/
theorem uc_eval_ID_eq_one {dim q : Nat} (h : q < dim) :
    uc_eval (ID q : BaseUCom dim) = 1 := by
  show pad_u dim q (rotation 0 0 0) = 1
  rw [rotation_I, pad_u_id h]

open BaseUCom in
/-- `useq (ID q) c ≡ c` — `ID q` is a left-identity of useq at the UCom
    level (when `q < dim`). 2-line proof via `uc_eval_ID_eq_one`. -/
theorem useq_ID_l {dim q : Nat} (hq : q < dim) (c : BaseUCom dim) :
    UCom.equiv (UCom.seq (ID q) c) c := by
  show uc_eval c * uc_eval (ID q : BaseUCom dim) = uc_eval c
  rw [uc_eval_ID_eq_one hq, Matrix.mul_one]

open BaseUCom in
/-- `useq c (ID q) ≡ c` — `ID q` is a right-identity of useq. -/
theorem useq_ID_r {dim q : Nat} (hq : q < dim) (c : BaseUCom dim) :
    UCom.equiv (UCom.seq c (ID q)) c := by
  show uc_eval (ID q : BaseUCom dim) * uc_eval c = uc_eval c
  rw [uc_eval_ID_eq_one hq, Matrix.one_mul]

open BaseUCom in
/-- `uc_eval (SKIP) = 1` when `0 < dim`. SKIP is `ID 0` definitionally,
    so this is `uc_eval_ID_eq_one` with q = 0. -/
theorem uc_eval_SKIP_eq_one {dim : Nat} (h : 0 < dim) :
    uc_eval (SKIP : BaseUCom dim) = (1 : Square dim) :=
  uc_eval_ID_eq_one h

open BaseUCom in
/-- `useq SKIP c ≡ c` — SKIP is a left-identity of useq (when `0 < dim`).
    Direct corollary of `useq_ID_l` with q = 0. -/
theorem useq_SKIP_l {dim : Nat} (hd : 0 < dim) (c : BaseUCom dim) :
    UCom.equiv (UCom.seq SKIP c) c :=
  useq_ID_l hd c

open BaseUCom in
/-- `useq c SKIP ≡ c` — SKIP is a right-identity of useq. -/
theorem useq_SKIP_r {dim : Nat} (hd : 0 < dim) (c : BaseUCom dim) :
    UCom.equiv (UCom.seq c SKIP) c :=
  useq_ID_r hd c

/-- `pad_u` distributes over matrix powers (when `n < dim`). Iterates
    `pad_u_mul_pad_u` and bases out at `pad_u_one`. -/
theorem pad_u_pow {dim n : Nat} (h : n < dim) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ k, pad_u dim n (A ^ k) = (pad_u dim n A) ^ k
  | 0 => by rw [pow_zero, pow_zero]; exact pad_u_one h
  | k + 1 => by rw [pow_succ, pow_succ, ← pad_u_pow h A k, pad_u_mul_pad_u]

/-- Padded version: `(pad_u (Rz θ))^k = pad_u (Rz (k·θ))` (when n < dim).
    Direct corollary of `pad_u_pow` + `rotation_Rz_pow`. -/
theorem pad_u_rotation_Rz_pow {dim n : Nat} (h : n < dim) (θ : ℝ) (k : Nat) :
    (pad_u dim n (rotation 0 0 θ))^k = pad_u dim n (rotation 0 0 (k * θ)) := by
  rw [← pad_u_pow h, rotation_Rz_pow]

/-- Padded zero-rotation collapses to the global identity (when n < dim).
    Direct corollary of `rotation_I` + `pad_u_id`. -/
theorem pad_u_rotation_I {dim n : Nat} (h : n < dim) :
    pad_u dim n (rotation 0 0 0) = (1 : Square dim) := by
  rw [rotation_I]
  exact pad_u_id h

/-- Padded version: `pad_u (Rz θ) * pad_u (Rz θ') = pad_u (Rz (θ+θ'))`.
    No `n < dim` hypothesis needed; both sides vanish to 0 when n ≥ dim. -/
theorem pad_u_rotation_Rz_compose (dim n : Nat) (θ θ' : ℝ) :
    pad_u dim n (rotation 0 0 θ) * pad_u dim n (rotation 0 0 θ')
      = pad_u dim n (rotation 0 0 (θ + θ')) := by
  rw [pad_u_mul_pad_u, rotation_Rz_compose]

/-- Padded version: `pad_u (Rz θ) * pad_u (Rz (-θ)) = 1` (when n < dim).
    Direct corollary of `pad_u_mul_pad_u` + `rotation_Rz_neg_inv` + `pad_u_id`. -/
theorem pad_u_rotation_Rz_neg_inv {dim n : Nat} (h : n < dim) (θ : ℝ) :
    pad_u dim n (rotation 0 0 θ) * pad_u dim n (rotation 0 0 (-θ))
      = (1 : Square dim) := by
  rw [pad_u_mul_pad_u, rotation_Rz_neg_inv, pad_u_id h]

/-- Symmetric direction: `pad_u (Rz (-θ)) * pad_u (Rz θ) = 1` (when n < dim).
    Companion to `pad_u_rotation_Rz_neg_inv`. -/
theorem pad_u_rotation_Rz_neg_inv_l {dim n : Nat} (h : n < dim) (θ : ℝ) :
    pad_u dim n (rotation 0 0 (-θ)) * pad_u dim n (rotation 0 0 θ)
      = (1 : Square dim) := by
  rw [pad_u_mul_pad_u, rotation_Rz_neg_inv_l, pad_u_id h]

/-- Generic self-inverse lift: any 2×2 matrix that squares to σi (the
    identity) gives a self-inverse pad_u at the matrix level. Recipe:
    pad_u_mul_pad_u to fold the product, hA to collapse A*A to σi,
    pad_u_id to land on the global identity. -/
theorem pad_u_self_inv {dim n : Nat} (h : n < dim) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A * A = σi) :
    pad_u dim n A * pad_u dim n A = (1 : Square dim) := by
  rw [pad_u_mul_pad_u, hA]
  exact pad_u_id h

/-- σx is self-inverse at the padded level. -/
theorem pad_u_σx_sq {dim n : Nat} (h : n < dim) :
    pad_u dim n σx * pad_u dim n σx = (1 : Square dim) :=
  pad_u_self_inv h σx σx_mul_σx

/-- σy is self-inverse at the padded level. -/
theorem pad_u_σy_sq {dim n : Nat} (h : n < dim) :
    pad_u dim n σy * pad_u dim n σy = (1 : Square dim) :=
  pad_u_self_inv h σy σy_mul_σy

/-- σz is self-inverse at the padded level. -/
theorem pad_u_σz_sq {dim n : Nat} (h : n < dim) :
    pad_u dim n σz * pad_u dim n σz = (1 : Square dim) :=
  pad_u_self_inv h σz σz_mul_σz

/-- The Hadamard is self-inverse at the padded level. -/
theorem pad_u_hMatrix_sq {dim n : Nat} (h : n < dim) :
    pad_u dim n hMatrix * pad_u dim n hMatrix = (1 : Square dim) :=
  pad_u_self_inv h hMatrix hMatrix_mul_hMatrix

/-- Generic mutual-inverse lift: if B * A = σi (i.e., A is a left-inverse
    of B in the 2×2 ring), then their padded versions are mutual inverses
    at the matrix level. Generalizes `pad_u_self_inv`. Use cases include
    T*TDAG, S*SDAG, and any other unitary-with-its-adjoint pair. -/
theorem pad_u_mul_inv {dim n : Nat} (h : n < dim) (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hBA : B * A = σi) :
    pad_u dim n B * pad_u dim n A = (1 : Square dim) := by
  rw [pad_u_mul_pad_u, hBA]
  exact pad_u_id h

/-- Generic order-2 chain lift: A*A = B → pad_u A * pad_u A = pad_u B.
    No `n < dim` hypothesis. The `B = σi` case lets `pad_u_id` finish
    to the global identity (see `pad_u_self_inv`). -/
theorem pad_u_pow_two_eq (dim n : Nat)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A * A = B) :
    pad_u dim n A * pad_u dim n A = pad_u dim n B := by
  rw [pad_u_mul_pad_u, hA]

/-- Generic order-3 chain lift: A*A*A = B → 3× chain product of pad_u A
    = pad_u B. No `n < dim` hypothesis. Use cases include S³=S†, S†³=S,
    σx/σy/σz³=themselves, hMatrix³=hMatrix. -/
theorem pad_u_pow_three_eq (dim n : Nat)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A * A * A = B) :
    pad_u dim n A * pad_u dim n A * pad_u dim n A = pad_u dim n B := by
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, hA]

/-- Generic order-4 chain lift: A*A*A*A = B → the chain product of
    four pad_u A's equals pad_u B. No `n < dim` hypothesis required;
    both sides are 0 when n ≥ dim (since pad_u dim n returns 0 there
    and a 4-chain of 0's is 0). The `B = σi` case lets `pad_u_id`
    finish to the global identity (see `pad_u_pow_four_eq_one`). -/
theorem pad_u_pow_four_eq (dim n : Nat)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A * A * A * A = B) :
    pad_u dim n A * pad_u dim n A * pad_u dim n A * pad_u dim n A
      = pad_u dim n B := by
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, hA]

/-- Generic order-5 chain lift: A*A*A*A*A = B → 5× chain product of
    pad_u A = pad_u B. No `n < dim` hypothesis. Use cases include
    σx/σy/σz⁵=themselves (Pauli order-5 by σ²=I × σ), hMatrix⁵=hMatrix,
    sMatrix⁵=sMatrix, sdagMatrix⁵=sdagMatrix. -/
theorem pad_u_pow_five_eq (dim n : Nat)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A * A * A * A * A = B) :
    pad_u dim n A * pad_u dim n A * pad_u dim n A * pad_u dim n A * pad_u dim n A
      = pad_u dim n B := by
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, hA]

-- SQIR/SQIR/UnitaryOps.v analog: higher-order Pauli powers (σ_i^k for k ≥ 4).
/-- Generic order-6 chain lift: A^6 = B → 6× chain product of pad_u A
    equals pad_u B. No `n < dim` hypothesis. Use cases include the
    Pauli order-6 case (σx⁶ = (σx²)³ = σi³ = σi), used in T-gate
    distillation cycle analysis. -/
theorem pad_u_pow_six_eq (dim n : Nat)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A * A * A * A * A * A = B) :
    pad_u dim n A * pad_u dim n A * pad_u dim n A * pad_u dim n A
      * pad_u dim n A * pad_u dim n A
      = pad_u dim n B := by
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u,
      pad_u_mul_pad_u, pad_u_mul_pad_u, hA]

/-- Generic order-4 lift (chain form): if A * A * A * A = σi, then the
    chain product of four pad_u A's is the identity. Use cases include
    hMatrix (H⁴=I), sMatrix (S⁴=I), sdagMatrix, and the Paulis (their
    chain product happens to be σi by σ²=σi twice). -/
theorem pad_u_pow_four_eq_one {dim n : Nat} (h : n < dim)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A * A * A * A = σi) :
    pad_u dim n A * pad_u dim n A * pad_u dim n A * pad_u dim n A
      = (1 : Square dim) := by
  rw [pad_u_pow_four_eq dim n A σi hA]
  exact pad_u_id h

/-- Hadamard has order 4 at the padded level: H · H · H · H = 1. -/
theorem pad_u_hMatrix_pow_four {dim n : Nat} (h : n < dim) :
    pad_u dim n hMatrix * pad_u dim n hMatrix * pad_u dim n hMatrix * pad_u dim n hMatrix
      = (1 : Square dim) :=
  pad_u_pow_four_eq_one h hMatrix hMatrix_pow_four

/-- σx has order 4 at the padded level (chain form). -/
theorem pad_u_σx_pow_four {dim n : Nat} (h : n < dim) :
    pad_u dim n σx * pad_u dim n σx * pad_u dim n σx * pad_u dim n σx
      = (1 : Square dim) :=
  pad_u_pow_four_eq_one h σx σx_pow_four

/-- σy has order 4 at the padded level (chain form). -/
theorem pad_u_σy_pow_four {dim n : Nat} (h : n < dim) :
    pad_u dim n σy * pad_u dim n σy * pad_u dim n σy * pad_u dim n σy
      = (1 : Square dim) :=
  pad_u_pow_four_eq_one h σy σy_pow_four

/-- σz has order 4 at the padded level (chain form). -/
theorem pad_u_σz_pow_four {dim n : Nat} (h : n < dim) :
    pad_u dim n σz * pad_u dim n σz * pad_u dim n σz * pad_u dim n σz
      = (1 : Square dim) :=
  pad_u_pow_four_eq_one h σz σz_pow_four

/-- σx's 5-chain at the padded level equals pad_u σx (cycle wraps to self). -/
theorem pad_u_σx_pow_five (dim n : Nat) :
    pad_u dim n σx * pad_u dim n σx * pad_u dim n σx * pad_u dim n σx * pad_u dim n σx
      = pad_u dim n σx :=
  pad_u_pow_five_eq dim n σx σx σx_pow_five

/-- σy's 5-chain at the padded level equals pad_u σy. -/
theorem pad_u_σy_pow_five (dim n : Nat) :
    pad_u dim n σy * pad_u dim n σy * pad_u dim n σy * pad_u dim n σy * pad_u dim n σy
      = pad_u dim n σy :=
  pad_u_pow_five_eq dim n σy σy σy_pow_five

/-- σz's 5-chain at the padded level equals pad_u σz. -/
theorem pad_u_σz_pow_five (dim n : Nat) :
    pad_u dim n σz * pad_u dim n σz * pad_u dim n σz * pad_u dim n σz * pad_u dim n σz
      = pad_u dim n σz :=
  pad_u_pow_five_eq dim n σz σz σz_pow_five

/-- Hadamard's 5-chain at the padded level equals pad_u hMatrix. -/
theorem pad_u_hMatrix_pow_five (dim n : Nat) :
    pad_u dim n hMatrix * pad_u dim n hMatrix * pad_u dim n hMatrix * pad_u dim n hMatrix * pad_u dim n hMatrix
      = pad_u dim n hMatrix :=
  pad_u_pow_five_eq dim n hMatrix hMatrix hMatrix_pow_five

/-- σx's 6-chain at the padded level equals pad_u σi (= identity if n < dim). -/
theorem pad_u_σx_pow_six (dim n : Nat) :
    pad_u dim n σx * pad_u dim n σx * pad_u dim n σx * pad_u dim n σx
      * pad_u dim n σx * pad_u dim n σx
      = pad_u dim n σi :=
  pad_u_pow_six_eq dim n σx σi σx_pow_six

/-- σy's 6-chain at the padded level equals pad_u σi. -/
theorem pad_u_σy_pow_six (dim n : Nat) :
    pad_u dim n σy * pad_u dim n σy * pad_u dim n σy * pad_u dim n σy
      * pad_u dim n σy * pad_u dim n σy
      = pad_u dim n σi :=
  pad_u_pow_six_eq dim n σy σi σy_pow_six

/-- σz's 6-chain at the padded level equals pad_u σi. -/
theorem pad_u_σz_pow_six (dim n : Nat) :
    pad_u dim n σz * pad_u dim n σz * pad_u dim n σz * pad_u dim n σz
      * pad_u dim n σz * pad_u dim n σz
      = pad_u dim n σi :=
  pad_u_pow_six_eq dim n σz σi σz_pow_six

/-- Generic order-6 lift (chain form): if A^6 = σi, then the chain
    product of six pad_u A's is the global identity (under n < dim).
    Mirrors `pad_u_pow_four_eq_one` for the order-6 case. -/
theorem pad_u_pow_six_eq_one {dim n : Nat} (h : n < dim)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A * A * A * A * A * A = σi) :
    pad_u dim n A * pad_u dim n A * pad_u dim n A * pad_u dim n A
      * pad_u dim n A * pad_u dim n A
      = (1 : Square dim) := by
  rw [pad_u_pow_six_eq dim n A σi hA]
  exact pad_u_id h

/-- σx has order 6 at the padded level: 6-chain = global identity
    (when n < dim). Combines `pad_u_pow_six_eq_one` with `σx_pow_six`. -/
theorem pad_u_σx_pow_six_eq_one {dim n : Nat} (h : n < dim) :
    pad_u dim n σx * pad_u dim n σx * pad_u dim n σx * pad_u dim n σx
      * pad_u dim n σx * pad_u dim n σx
      = (1 : Square dim) :=
  pad_u_pow_six_eq_one h σx σx_pow_six

/-- σy has order 6 at the padded level: 6-chain = global identity. -/
theorem pad_u_σy_pow_six_eq_one {dim n : Nat} (h : n < dim) :
    pad_u dim n σy * pad_u dim n σy * pad_u dim n σy * pad_u dim n σy
      * pad_u dim n σy * pad_u dim n σy
      = (1 : Square dim) :=
  pad_u_pow_six_eq_one h σy σy_pow_six

/-- σz has order 6 at the padded level: 6-chain = global identity. -/
theorem pad_u_σz_pow_six_eq_one {dim n : Nat} (h : n < dim) :
    pad_u dim n σz * pad_u dim n σz * pad_u dim n σz * pad_u dim n σz
      * pad_u dim n σz * pad_u dim n σz
      = (1 : Square dim) :=
  pad_u_pow_six_eq_one h σz σz_pow_six


end FormalRV.Framework
