/-
  FormalRV.Framework.QuantumLib — Lean implementation of the QuantumLib
  helpers SQIR depends on.

  Originally axiomatized; now being converted to real definitions one by one.
  Each axiom that gets discharged here lets a downstream sorry in QPE.lean,
  GateDecompositions.lean, or Shor/Order.lean become attackable.

  Status: PARTIAL. Core state-vector helpers are defined; some
  Shor-specific helpers (modmult, probability_of_success) remain
  axiomatized pending circuit-implementation work.
-/
import FormalRV.Core.UnitarySem
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace FormalRV.Framework

open BigOperators

/-! ## funbool_to_nat — interpret a Boolean function as a Nat (big-endian)

    Faithful translation of SQIR's recursive form
    `funbool_to_nat (S n) f = 2 * funbool_to_nat n f + Nat.b2n (f n)`.
    This is BIG-ENDIAN: `f 0` is the most-significant bit, `f (n-1)` the LSB.
    With this convention, for a `dim`-qubit register, `f i` is the value of
    qubit `i` in `pad_u`'s MSB-first qubit indexing. -/

/-- Encode the first k values of `f` as a natural number, big-endian:
    `funbool_to_nat (k+1) f = 2 * funbool_to_nat k f + (if f k then 1 else 0)`.
    Bit `(k-1-i)` of the result is `f i` (so `f 0` is the MSB). -/
def funbool_to_nat : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k+1, f => 2 * funbool_to_nat k f + (if f k then 1 else 0)

@[simp] theorem funbool_to_nat_zero (f : Nat → Bool) :
    funbool_to_nat 0 f = 0 := rfl

/-- Recurrence by definition (kept as a named lemma for downstream use). -/
@[simp] theorem funbool_to_nat_succ (k : Nat) (f : Nat → Bool) :
    funbool_to_nat (k+1) f
      = 2 * funbool_to_nat k f + (if f k then 1 else 0) := rfl

theorem funbool_to_nat_lt (k : Nat) (f : Nat → Bool) : funbool_to_nat k f < 2^k := by
  induction k with
  | zero => simp [funbool_to_nat]
  | succ n ih =>
      simp [funbool_to_nat_succ, pow_succ]
      cases hf : f n
      · simp; omega
      · simp; omega

/-! ## basis_vector — k-th computational basis state

    SQIR's `basis_vector n k = e_k` (the standard basis vector with 1 at
    index k, 0 elsewhere). -/

/-- The k-th computational basis state in `n`-dim space. -/
def basis_vector (n k : Nat) : Matrix (Fin n) (Fin 1) ℂ :=
  fun i _ => if i.val = k then 1 else 0

@[simp] theorem basis_vector_apply (n k : Nat) (i : Fin n) (j : Fin 1) :
    basis_vector n k i j = if i.val = k then 1 else 0 := rfl

/-- `basis_vector` value at the matching index is 1. -/
theorem basis_vector_apply_eq (n k : Nat) (i : Fin n) (j : Fin 1) (h : i.val = k) :
    basis_vector n k i j = 1 := by rw [basis_vector_apply, if_pos h]

/-- `basis_vector` value at a non-matching index is 0. -/
theorem basis_vector_apply_ne (n k : Nat) (i : Fin n) (j : Fin 1) (h : i.val ≠ k) :
    basis_vector n k i j = 0 := by rw [basis_vector_apply, if_neg h]

/-! ## f_to_vec — basis state from a Boolean function -/

/-- The basis state |f(n-1)...f(0)⟩, encoded little-endian via funbool_to_nat. -/
def f_to_vec (n : Nat) (f : Nat → Bool) : Matrix (Fin (2^n)) (Fin 1) ℂ :=
  basis_vector (2^n) (funbool_to_nat n f)

/-! ## kron_zeros — k-fold Kronecker of |0⟩ = |0...0⟩ = first basis vector -/

/-- The all-zeros basis state on k qubits. Equals `basis_vector (2^k) 0`. -/
def kron_zeros (k : Nat) : Matrix (Fin (2^k)) (Fin 1) ℂ :=
  basis_vector (2^k) 0

/-- `funbool_to_nat n (fun _ => false) = 0`. (Restated here so it's available
    above `kron_zeros_eq_f_to_vec_false`; re-stated as a `@[simp]` lemma below
    for ergonomics.) -/
private theorem funbool_to_nat_const_false_aux (k : Nat) :
    funbool_to_nat k (fun _ => false) = 0 := by
  induction k with
  | zero => rfl
  | succ n ih => simp [funbool_to_nat_succ, ih]

theorem kron_zeros_eq_f_to_vec_false (k : Nat) :
    kron_zeros k = f_to_vec k (fun _ => false) := by
  unfold kron_zeros f_to_vec
  rw [funbool_to_nat_const_false_aux]

/-- Encoding the all-true function gives `2^k - 1`. -/
theorem funbool_to_nat_const_true (k : Nat) :
    funbool_to_nat k (fun _ => true) = 2^k - 1 := by
  induction k with
  | zero => rfl
  | succ n ih =>
      simp [funbool_to_nat_succ, ih, pow_succ]
      have h2pow : 1 ≤ 2^n := Nat.one_le_two_pow
      omega

/-- The all-ones state |1...1⟩ as `f_to_vec` of the constant-true function. -/
theorem f_to_vec_const_true (n : Nat) :
    f_to_vec n (fun _ => true) = basis_vector (2^n) (2^n - 1) := by
  unfold f_to_vec
  rw [funbool_to_nat_const_true]

/-- Entry-wise formula for `f_to_vec`: 1 at index `funbool_to_nat n f`, 0 elsewhere. -/
theorem f_to_vec_apply (n : Nat) (f : Nat → Bool) (i : Fin (2^n)) (j : Fin 1) :
    f_to_vec n f i j = if i.val = funbool_to_nat n f then 1 else 0 := by
  unfold f_to_vec
  rw [basis_vector_apply]

/-- `f_to_vec` value at the matching index is 1. -/
theorem f_to_vec_apply_eq (n : Nat) (f : Nat → Bool) (i : Fin (2^n)) (j : Fin 1)
    (h : i.val = funbool_to_nat n f) : f_to_vec n f i j = 1 := by
  rw [f_to_vec_apply, if_pos h]

/-- `f_to_vec` value at a non-matching index is 0. -/
theorem f_to_vec_apply_ne (n : Nat) (f : Nat → Bool) (i : Fin (2^n)) (j : Fin 1)
    (h : i.val ≠ funbool_to_nat n f) : f_to_vec n f i j = 0 := by
  rw [f_to_vec_apply, if_neg h]

/-- `f_to_vec 0` has only one entry (the trivial 1×1 column), and it's 1. -/
theorem f_to_vec_zero_apply (f : Nat → Bool) (i : Fin (2^0)) (j : Fin 1) :
    f_to_vec 0 f i j = 1 := by
  rw [f_to_vec_apply]
  have hi : i.val = 0 := by omega
  simp [hi, funbool_to_nat]

/-- `f_to_vec n f` is never the zero matrix (it's always a basis vector). -/
theorem f_to_vec_ne_zero (n : Nat) (f : Nat → Bool) :
    f_to_vec n f ≠ 0 := by
  intro h
  have hk : f_to_vec n f ⟨funbool_to_nat n f, funbool_to_nat_lt n f⟩ 0 = 1 := by
    rw [f_to_vec_apply]; simp
  rw [h] at hk
  simp at hk

/-- `basis_vector n k ≠ 0` when `k < n` (the standard basis is nonzero). -/
theorem basis_vector_ne_zero (n k : Nat) (h : k < n) :
    basis_vector n k ≠ 0 := by
  intro hzero
  have h1 : basis_vector n k ⟨k, h⟩ 0 = 1 := by
    rw [basis_vector_apply]; simp
  rw [hzero] at h1
  simp at h1

/-- `kron_zeros k ≠ 0` (the all-zeros basis state is non-zero). -/
theorem kron_zeros_ne_zero (k : Nat) : kron_zeros k ≠ 0 := by
  unfold kron_zeros
  exact basis_vector_ne_zero (2^k) 0 (Nat.two_pow_pos k)

/-! ## State-vector tensor product (kron_vec)

    For state vectors over qubit registers (Fin (2^a) and Fin (2^b)),
    the Kronecker product naturally lives in Fin (2^(a+b)).

    Implementation: combine indices via `i = i_high * 2^b + i_low`,
    matching the standard tensor-product convention. -/

/-- Tensor product of two qubit-register state vectors. -/
noncomputable def kron_vec {a b : Nat}
    (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    Matrix (Fin (2^(a+b))) (Fin 1) ℂ :=
  fun i _ =>
    let h_eq : (2^(a+b) : Nat) = 2^a * 2^b := pow_add 2 a b
    let h_lt : i.val < 2^a * 2^b := h_eq ▸ i.isLt
    let i_high : Fin (2^a) := ⟨i.val / 2^b,
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)).mpr h_lt⟩
    let i_low : Fin (2^b) := ⟨i.val % 2^b, Nat.mod_lt _ (Nat.two_pow_pos b)⟩
    ψ i_high 0 * φ i_low 0

scoped infixl:70 " ⊗ᵥ " => kron_vec

/-- High-bits projection: extract the upper qubits' index from a composite
    `Fin (2^(a+b))` index. `kron_vec_high i = i.val / 2^b`. -/
def kron_vec_high {a b : Nat} (i : Fin (2^(a+b))) : Fin (2^a) :=
  ⟨i.val / 2^b,
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)).mpr
      (pow_add 2 a b ▸ i.isLt)⟩

/-- Low-bits projection: extract the lower qubits' index from a composite
    `Fin (2^(a+b))` index. `kron_vec_low i = i.val % 2^b`. -/
def kron_vec_low {a b : Nat} (i : Fin (2^(a+b))) : Fin (2^b) :=
  ⟨i.val % 2^b, Nat.mod_lt _ (Nat.two_pow_pos b)⟩

/-- Explicit unfolding: `kron_vec ψ φ` at composite index `i` equals the
    product of `ψ` at the high-bits projection and `φ` at the low-bits
    projection. Direct restatement of the definition with the let-bindings
    pulled out as named helpers. -/
theorem kron_vec_apply {a b : Nat}
    (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ : Matrix (Fin (2^b)) (Fin 1) ℂ)
    (i : Fin (2^(a+b))) (j : Fin 1) :
    kron_vec ψ φ i j = ψ (kron_vec_high i) 0 * φ (kron_vec_low i) 0 := rfl

/-- The high/low decomposition recovers the original composite index:
    `i.val = high.val * 2^b + low.val`. Standard division-with-remainder
    identity, the key fact behind the eventual `Fin (2^(a+b)) ≃ Fin 2^a × Fin 2^b`
    reindexing for `Pure_State_Vector_kron`. -/
theorem kron_vec_high_low_unique {a b : Nat} (i : Fin (2^(a+b))) :
    i.val = (kron_vec_high i).val * 2^b + (kron_vec_low i).val := by
  unfold kron_vec_high kron_vec_low
  exact (Nat.div_add_mod' i.val (2^b)).symm

/-- Injectivity of the high/low projection pair: two composite indices
    with equal high and low projections must be equal. Direct corollary
    of `kron_vec_high_low_unique` plus `Fin.ext`. -/
theorem kron_vec_high_low_inj {a b : Nat} (i₁ i₂ : Fin (2^(a+b)))
    (hh : kron_vec_high i₁ = kron_vec_high i₂)
    (hl : kron_vec_low i₁ = kron_vec_low i₂) :
    i₁ = i₂ := by
  apply Fin.ext
  rw [kron_vec_high_low_unique i₁, kron_vec_high_low_unique i₂, hh, hl]

/-- Composite-index assembly: given a high-bits index `j : Fin (2^a)` and
    a low-bits index `k : Fin (2^b)`, build the corresponding composite
    index `Fin (2^(a+b))` via `j * 2^b + k`. The inverse of the
    `(kron_vec_high, kron_vec_low)` projection pair. -/
def kron_vec_combine {a b : Nat} (j : Fin (2^a)) (k : Fin (2^b)) : Fin (2^(a+b)) :=
  ⟨j.val * 2^b + k.val, by
    rw [pow_add]
    calc j.val * 2^b + k.val
        < j.val * 2^b + 2^b := Nat.add_lt_add_left k.isLt _
      _ = (j.val + 1) * 2^b := by ring
      _ ≤ 2^a * 2^b := Nat.mul_le_mul_right _ j.isLt⟩

/-- Round-trip: extracting the high bits from an assembled composite index
    recovers the original high index. `(j * 2^b + k) / 2^b = j` since
    `k < 2^b` makes the `k / 2^b` term vanish. -/
theorem kron_vec_high_combine {a b : Nat} (j : Fin (2^a)) (k : Fin (2^b)) :
    kron_vec_high (kron_vec_combine j k) = j := by
  apply Fin.ext
  show (j.val * 2^b + k.val) / 2^b = j.val
  rw [add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos b),
      Nat.div_eq_of_lt k.isLt, zero_add]

/-- Round-trip: extracting the low bits from an assembled composite index
    recovers the original low index. `(j * 2^b + k) % 2^b = k` since
    `j * 2^b` is a multiple of `2^b` and `k < 2^b`. -/
theorem kron_vec_low_combine {a b : Nat} (j : Fin (2^a)) (k : Fin (2^b)) :
    kron_vec_low (kron_vec_combine j k) = k := by
  apply Fin.ext
  show (j.val * 2^b + k.val) % 2^b = k.val
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt k.isLt]

/-- The other round-trip direction: assembling the high/low projections of
    `i` reconstructs `i`. Closes the bijection
    `Fin (2^a) × Fin (2^b) ≃ Fin (2^(a+b))` via `kron_vec_high_low_inj`. -/
theorem kron_vec_combine_high_low {a b : Nat} (i : Fin (2^(a+b))) :
    kron_vec_combine (kron_vec_high i) (kron_vec_low i) = i := by
  apply kron_vec_high_low_inj
  · exact kron_vec_high_combine _ _
  · exact kron_vec_low_combine _ _

/-- Apply formula via assembly: evaluating `kron_vec ψ φ` at the composite
    index `combine j k` gives the clean tensor-product formula
    `ψ j 0 * φ k 0`. The most useful unfolding lemma for sums over
    `(j, k)` rather than over the composite index. -/
theorem kron_vec_apply_combine {a b : Nat}
    (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ : Matrix (Fin (2^b)) (Fin 1) ℂ)
    (j : Fin (2^a)) (k : Fin (2^b)) :
    kron_vec ψ φ (kron_vec_combine j k) 0 = ψ j 0 * φ k 0 := by
  rw [kron_vec_apply, kron_vec_high_combine, kron_vec_low_combine]

/-- The full bijection `Fin (2^a) × Fin (2^b) ≃ Fin (2^(a+b))` packaged
    as an `Equiv`, using `kron_vec_combine` as the forward map and
    `(kron_vec_high, kron_vec_low)` as the inverse. The round-trip lemmas
    `kron_vec_high_combine`, `kron_vec_low_combine`, and
    `kron_vec_combine_high_low` discharge the `left_inv` / `right_inv`
    obligations. Used downstream with `Finset.sum_equiv` to reindex
    sums over `Fin (2^(a+b))` as iterated sums over `(j, k)`. -/
def kronEquiv (a b : Nat) : Fin (2^a) × Fin (2^b) ≃ Fin (2^(a+b)) where
  toFun p := kron_vec_combine p.1 p.2
  invFun i := (kron_vec_high i, kron_vec_low i)
  left_inv := fun ⟨j, k⟩ => by
    simp [kron_vec_high_combine, kron_vec_low_combine]
  right_inv := kron_vec_combine_high_low

/-- Per-element norm-factorization: at any composite index `combine j k`,
    the squared modulus of `kron_vec ψ φ` factors as the product of
    squared moduli of `ψ` and `φ` at `j` and `k`. Direct chain of
    `kron_vec_apply_combine` and `Complex.normSq_mul`. The pointwise
    fact behind `kron_vec_normSq_sum`. -/
theorem kron_vec_normSq_apply_combine {a b : Nat}
    (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ : Matrix (Fin (2^b)) (Fin 1) ℂ)
    (j : Fin (2^a)) (k : Fin (2^b)) :
    Complex.normSq ((kron_vec ψ φ) (kron_vec_combine j k) 0)
      = Complex.normSq (ψ j 0) * Complex.normSq (φ k 0) := by
  rw [kron_vec_apply_combine, Complex.normSq_mul]

/-- Sum-factorization: the total squared norm of the tensor product factors
    as the product of total squared norms. The standard
    `‖ψ ⊗ φ‖² = ‖ψ‖² · ‖φ‖²` identity, lifted to component sums via the
    `kronEquiv` bijection + `Fintype.sum_prod_type` + `Finset.mul_sum`. -/
theorem kron_vec_normSq_sum {a b : Nat}
    (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    ∑ i : Fin (2^(a+b)), Complex.normSq ((kron_vec ψ φ) i 0)
      = (∑ j : Fin (2^a), Complex.normSq (ψ j 0))
        * (∑ k : Fin (2^b), Complex.normSq (φ k 0)) := by
  have reindex : ∑ i : Fin (2^(a+b)), Complex.normSq ((kron_vec ψ φ) i 0)
      = ∑ p : Fin (2^a) × Fin (2^b),
          Complex.normSq ((kron_vec ψ φ) (kron_vec_combine p.1 p.2) 0) :=
    (Fintype.sum_equiv (kronEquiv a b) _ _ (fun _ => rfl)).symm
  rw [reindex]
  simp_rw [kron_vec_normSq_apply_combine]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- Bilinearity (left zero): `0 ⊗ᵥ φ = 0`. The tensor product
    annihilates when either factor is zero. -/
theorem kron_vec_zero_left {a b : Nat} (φ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec (0 : Matrix (Fin (2^a)) (Fin 1) ℂ) φ = 0 := by
  ext i j
  simp [kron_vec]

/-- Bilinearity (right zero): `ψ ⊗ᵥ 0 = 0`. -/
theorem kron_vec_zero_right {a b : Nat} (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) :
    kron_vec ψ (0 : Matrix (Fin (2^b)) (Fin 1) ℂ) = 0 := by
  ext i j
  simp [kron_vec]

/-- Negation distributes through the left factor: `(-ψ) ⊗ᵥ φ = -(ψ ⊗ᵥ φ)`. -/
theorem kron_vec_neg_left {a b : Nat}
    (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec (-ψ) φ = -(kron_vec ψ φ) := by
  ext i j
  simp [kron_vec, Matrix.neg_apply, neg_mul]

/-- Negation distributes through the right factor: `ψ ⊗ᵥ (-φ) = -(ψ ⊗ᵥ φ)`. -/
theorem kron_vec_neg_right {a b : Nat}
    (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec ψ (-φ) = -(kron_vec ψ φ) := by
  ext i j
  simp [kron_vec, Matrix.neg_apply, mul_neg]

/-- Scalar multiplication on the left factor: `(c • ψ) ⊗ᵥ φ = c • (ψ ⊗ᵥ φ)`. -/
theorem kron_vec_smul_left {a b : Nat} (c : ℂ)
    (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec (c • ψ) φ = c • (kron_vec ψ φ) := by
  ext i j
  simp only [kron_vec, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Scalar multiplication on the right factor: `ψ ⊗ᵥ (c • φ) = c • (ψ ⊗ᵥ φ)`. -/
theorem kron_vec_smul_right {a b : Nat} (c : ℂ)
    (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec ψ (c • φ) = c • (kron_vec ψ φ) := by
  ext i j
  simp only [kron_vec, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Distributivity over addition on the left factor:
    `(ψ₁ + ψ₂) ⊗ᵥ φ = ψ₁ ⊗ᵥ φ + ψ₂ ⊗ᵥ φ`. -/
theorem kron_vec_add_left {a b : Nat}
    (ψ₁ ψ₂ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec (ψ₁ + ψ₂) φ = kron_vec ψ₁ φ + kron_vec ψ₂ φ := by
  ext i j
  simp [kron_vec, Matrix.add_apply, add_mul]

/-- Distributivity over addition on the right factor:
    `ψ ⊗ᵥ (φ₁ + φ₂) = ψ ⊗ᵥ φ₁ + ψ ⊗ᵥ φ₂`. -/
theorem kron_vec_add_right {a b : Nat}
    (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ₁ φ₂ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec ψ (φ₁ + φ₂) = kron_vec ψ φ₁ + kron_vec ψ φ₂ := by
  ext i j
  simp [kron_vec, Matrix.add_apply, mul_add]

/-- Combined two-sided scalar multiplication: scaling each factor multiplies
    the result by the product of scalars. Direct chain of the
    `kron_vec_smul_left` / `_right` pair with `smul_smul`. -/
theorem kron_vec_smul_smul {a b : Nat} (c d : ℂ)
    (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec (c • ψ) (d • φ) = (c * d) • (kron_vec ψ φ) := by
  rw [kron_vec_smul_left, kron_vec_smul_right, smul_smul]

/-- Subtraction distributes through the left factor:
    `(ψ₁ - ψ₂) ⊗ᵥ φ = ψ₁ ⊗ᵥ φ - ψ₂ ⊗ᵥ φ`. Direct chain of
    `kron_vec_add_left` and `kron_vec_neg_left`. -/
theorem kron_vec_sub_left {a b : Nat}
    (ψ₁ ψ₂ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec (ψ₁ - ψ₂) φ = kron_vec ψ₁ φ - kron_vec ψ₂ φ := by
  rw [sub_eq_add_neg, kron_vec_add_left, kron_vec_neg_left, sub_eq_add_neg]

/-- Subtraction distributes through the right factor:
    `ψ ⊗ᵥ (φ₁ - φ₂) = ψ ⊗ᵥ φ₁ - ψ ⊗ᵥ φ₂`. -/
theorem kron_vec_sub_right {a b : Nat}
    (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ₁ φ₂ : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    kron_vec ψ (φ₁ - φ₂) = kron_vec ψ φ₁ - kron_vec ψ φ₂ := by
  rw [sub_eq_add_neg, kron_vec_add_right, kron_vec_neg_right, sub_eq_add_neg]

/-! ## Pure_State_Vector — unit-norm condition -/

/-- A state vector is "pure" iff its squared L2-norm is 1. -/
noncomputable def Pure_State_Vector {n : Nat} (ψ : Matrix (Fin n) (Fin 1) ℂ) : Prop :=
  ∑ i : Fin n, Complex.normSq (ψ i 0) = 1

/-! ## probability_of_outcome — |⟨φ | ψ⟩|² -/

/-- The Born-rule probability of measuring `φ` from state `ψ`:
    `|⟨φ|ψ⟩|² = |φ⃰ · ψ|²`. -/
noncomputable def probability_of_outcome {n : Nat}
    (φ ψ : Matrix (Fin n) (Fin 1) ℂ) : ℝ :=
  Complex.normSq ((φ.conjTranspose * ψ) 0 0)

/-- Zero φ gives zero probability (no overlap). -/
theorem probability_of_outcome_zero_left {n : Nat} (ψ : Matrix (Fin n) (Fin 1) ℂ) :
    probability_of_outcome (0 : Matrix (Fin n) (Fin 1) ℂ) ψ = 0 := by
  unfold probability_of_outcome
  simp [Matrix.conjTranspose_zero, Matrix.zero_mul]

/-- Zero ψ gives zero probability. -/
theorem probability_of_outcome_zero_right {n : Nat} (φ : Matrix (Fin n) (Fin 1) ℂ) :
    probability_of_outcome φ (0 : Matrix (Fin n) (Fin 1) ℂ) = 0 := by
  unfold probability_of_outcome
  simp [Matrix.mul_zero]

/-- Born-rule probabilities are always non-negative (norm-squared of a complex number). -/
theorem probability_of_outcome_nonneg {n : Nat}
    (φ ψ : Matrix (Fin n) (Fin 1) ℂ) :
    0 ≤ probability_of_outcome φ ψ := Complex.normSq_nonneg _

/-- Scaling the outcome state scales the probability by `|c|²`. -/
theorem probability_of_outcome_smul_right {n : Nat}
    (c : ℂ) (φ ψ : Matrix (Fin n) (Fin 1) ℂ) :
    probability_of_outcome φ (c • ψ)
      = Complex.normSq c * probability_of_outcome φ ψ := by
  unfold probability_of_outcome
  rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul]

/-- Scaling the projector φ by `c` also scales the probability by `|c|²`. -/
theorem probability_of_outcome_smul_left {n : Nat}
    (c : ℂ) (φ ψ : Matrix (Fin n) (Fin 1) ℂ) :
    probability_of_outcome (c • φ) ψ
      = Complex.normSq c * probability_of_outcome φ ψ := by
  unfold probability_of_outcome
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
      Complex.normSq_mul]
  congr 1
  exact Complex.normSq_conj c

/-- Negating the outcome state doesn't change the probability — global-sign
    is a unit-modulus phase factor. -/
theorem probability_of_outcome_neg_right {n : Nat}
    (φ ψ : Matrix (Fin n) (Fin 1) ℂ) :
    probability_of_outcome φ (-ψ) = probability_of_outcome φ ψ := by
  unfold probability_of_outcome
  rw [Matrix.mul_neg, Matrix.neg_apply, Complex.normSq_neg]

/-- Negating the projector also doesn't change the probability. -/
theorem probability_of_outcome_neg_left {n : Nat}
    (φ ψ : Matrix (Fin n) (Fin 1) ℂ) :
    probability_of_outcome (-φ) ψ = probability_of_outcome φ ψ := by
  unfold probability_of_outcome
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.neg_apply, Complex.normSq_neg]

/-- Scaling the outcome state ψ by `exp(iθ)` doesn't change the probability —
    the exp(iθ) factor has unit modulus, so |exp(iθ)|² = 1 contributes
    trivially. The canonical global-phase invariance for Born-rule probabilities. -/
theorem probability_of_outcome_smul_exp_I_right {n : Nat}
    (θ : ℝ) (φ ψ : Matrix (Fin n) (Fin 1) ℂ) :
    probability_of_outcome φ (Complex.exp (↑θ * Complex.I) • ψ)
      = probability_of_outcome φ ψ := by
  rw [probability_of_outcome_smul_right, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- Scaling the projection state φ by `exp(iθ)` doesn't change the probability —
    symmetric companion of `probability_of_outcome_smul_exp_I_right`. -/
theorem probability_of_outcome_smul_exp_I_left {n : Nat}
    (θ : ℝ) (φ ψ : Matrix (Fin n) (Fin 1) ℂ) :
    probability_of_outcome (Complex.exp (↑θ * Complex.I) • φ) ψ
      = probability_of_outcome φ ψ := by
  rw [probability_of_outcome_smul_left, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- Born-rule probability is symmetric: `|⟨φ|ψ⟩|² = |⟨ψ|φ⟩|²`. The two inner
    products differ only by complex conjugation, and `normSq` is invariant
    under conjugation. -/
theorem probability_of_outcome_comm {n : Nat}
    (φ ψ : Matrix (Fin n) (Fin 1) ℂ) :
    probability_of_outcome φ ψ = probability_of_outcome ψ φ := by
  unfold probability_of_outcome
  have h : (φ.conjTranspose * ψ) 0 0 = star ((ψ.conjTranspose * φ) 0 0) := by
    rw [← Matrix.conjTranspose_apply, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
  rw [h]
  show Complex.normSq ((starRingEnd ℂ) ((ψ.conjTranspose * φ) 0 0)) = _
  rw [Complex.normSq_conj]

/-- For a pure state ψ, the Born-rule self-overlap is exactly 1:
    `|⟨ψ|ψ⟩|² = 1`. This is the consistency condition that makes
    `probability_of_outcome` interpretable as a probability over the
    standard ψ-basis. -/
theorem probability_of_outcome_self {n : Nat}
    (ψ : Matrix (Fin n) (Fin 1) ℂ) (h : Pure_State_Vector ψ) :
    probability_of_outcome ψ ψ = 1 := by
  unfold probability_of_outcome
  have key : (ψ.conjTranspose * ψ) 0 0
      = ((∑ i : Fin n, Complex.normSq (ψ i 0) : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (star (ψ i 0) : ℂ) = (starRingEnd ℂ) (ψ i 0) from rfl, mul_comm,
        Complex.mul_conj]
  unfold Pure_State_Vector at h
  rw [key, h, Complex.ofReal_one, Complex.normSq_one]

/-! ## Shor-specific helpers (still axiomatized — pending circuit translation) -/

/-- Multiplicative order of `a` mod `N`: smallest positive `r` with
    `a^r ≡ 1 mod N`, or `0` if no such `r` exists (i.e., `a` is not a
    unit mod `N`). Defined as Mathlib's `orderOf` on the multiplicative
    monoid of `ZMod N`. -/
noncomputable def ord (a N : Nat) : Nat :=
  orderOf (a : ZMod N)

/-- Modular inverse of `a` mod `N`. Returns the natural-number
    representative of `(a : ZMod N)⁻¹`; `0` when no inverse exists. -/
noncomputable def modinv (a N : Nat) : Nat :=
  ((a : ZMod N)⁻¹).val

/-- Number of ancilla qubits used by the modular-mult subcircuit. -/
def modmult_rev_anc (n : Nat) : Nat := 2 * n  -- placeholder

-- (removed 2026-06-09) Dead `FormalRV.Framework` axioms `f_modmult_circuit` and
-- `probability_of_success` deleted: they shadowed the live `FormalRV.SQIRPort`
-- symbols of the same name and were never referenced by the verified chain.

/-- Shor's success-probability constant κ = 4 · e⁻² / π² ≈ 0.055. -/
noncomputable def kappa : ℝ := 4 * Real.exp (-2) / Real.pi ^ 2

/-! ## Sanity lemmas about the new defs -/

@[simp] theorem basis_vector_self (n k : Nat) (h : k < n) :
    basis_vector n k ⟨k, h⟩ 0 = 1 := by
  simp [basis_vector]

@[simp] theorem basis_vector_zero_apply_zero (n : Nat) (h : 0 < n) :
    basis_vector n 0 ⟨0, h⟩ 0 = 1 := by
  simp [basis_vector]

theorem kron_zeros_apply_zero (k : Nat) (h : 0 < 2^k := Nat.two_pow_pos k) :
    kron_zeros k ⟨0, h⟩ 0 = 1 := by
  unfold kron_zeros
  simp

/-- `kron_zeros` is 0 at any non-zero index. -/
theorem kron_zeros_apply_ne_zero (k : Nat) (i : Fin (2^k)) (j : Fin 1)
    (h : i.val ≠ 0) : kron_zeros k i j = 0 := by
  unfold kron_zeros
  rw [basis_vector_apply, if_neg h]

@[simp] theorem funbool_to_nat_const_false (k : Nat) :
    funbool_to_nat k (fun _ => false) = 0 := funbool_to_nat_const_false_aux k

/-! ## Function update (helper for `f_to_vec_*` action lemmas) -/

/-- Function update: `update f c v` is `f` except at index `c` where it
    returns `v`. Matches SQIR's `update` from QuantumLib. -/
def update (f : Nat → Bool) (c : Nat) (v : Bool) : Nat → Bool :=
  fun i => if i = c then v else f i

/-- Definitional unfolding of `update`: ite on the index. -/
theorem update_apply (f : Nat → Bool) (c i : Nat) (v : Bool) :
    update f c v i = if i = c then v else f i := rfl

@[simp] theorem update_eq (f : Nat → Bool) (c : Nat) (v : Bool) :
    update f c v c = v := by simp [update]

@[simp] theorem update_neq (f : Nat → Bool) (c i : Nat) (v : Bool) (h : i ≠ c) :
    update f c v i = f i := by simp [update, h]

/-- Two updates at the same index: only the latter one survives. -/
@[simp] theorem update_idem (f : Nat → Bool) (n : Nat) (v₁ v₂ : Bool) :
    update (update f n v₁) n v₂ = update f n v₂ := by
  funext k
  simp [update]
  by_cases hk : k = n
  · simp [hk]
  · simp [hk]

/-- Updating a position to its current value is a no-op. -/
@[simp] theorem update_self (f : Nat → Bool) (n : Nat) :
    update f n (f n) = f := by
  funext k
  by_cases hk : k = n
  · subst hk; simp [update]
  · simp [update, hk]

/-- Updates at distinct indices commute. -/
theorem update_comm (f : Nat → Bool) (i j : Nat) (X Y : Bool) (h : i ≠ j) :
    update (update f i X) j Y = update (update f j Y) i X := by
  funext k
  by_cases hk_i : k = i
  · subst hk_i; simp [update, h]
  · by_cases hk_j : k = j
    · subst hk_j; simp [update, Ne.symm h]
    · simp [update, hk_i, hk_j]

/-- `funbool_to_nat n f` only depends on `f` at indices `[0, n)`. -/
theorem funbool_to_nat_congr (n : Nat) (f g : Nat → Bool)
    (hfg : ∀ i, i < n → f i = g i) :
    funbool_to_nat n f = funbool_to_nat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [funbool_to_nat_succ, funbool_to_nat_succ]
      have hk : f k = g k := hfg k (Nat.lt_succ_self k)
      have h_lt : ∀ i, i < k → f i = g i := fun i hi => hfg i (Nat.lt_succ_of_lt hi)
      rw [ih h_lt, hk]

/-! ## Pure_State_Vector closure lemmas -/

/-- Computational basis states are pure. -/
theorem Pure_State_Vector_basis_vector (n k : Nat) (h : k < n) :
    Pure_State_Vector (basis_vector n k) := by
  show ∑ i : Fin n, Complex.normSq (basis_vector n k i 0) = 1
  have key : (∑ i : Fin n, Complex.normSq (basis_vector n k i 0))
              = Complex.normSq (basis_vector n k ⟨k, h⟩ 0) := by
    apply Finset.sum_eq_single
    · intro i _ hi
      have h_ne : i.val ≠ k := fun heq => hi (Fin.ext heq)
      simp [basis_vector, h_ne]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [key]
  simp [basis_vector]

/-- `f_to_vec n f` is a pure state vector. -/
theorem Pure_State_Vector_f_to_vec (n : Nat) (f : Nat → Bool) :
    Pure_State_Vector (f_to_vec n f) :=
  Pure_State_Vector_basis_vector (2^n) (funbool_to_nat n f)
    (funbool_to_nat_lt n f)

/-- The all-zeros basis state on `k` qubits is pure. -/
theorem Pure_State_Vector_kron_zeros (k : Nat) :
    Pure_State_Vector (kron_zeros k) :=
  Pure_State_Vector_basis_vector (2^k) 0 (Nat.two_pow_pos k)

/-- Specialization of `probability_of_outcome_self` to computational
    basis vectors — `|⟨e_k|e_k⟩|² = 1`. -/
theorem probability_of_outcome_basis_self (n k : Nat) (h : k < n) :
    probability_of_outcome (basis_vector n k) (basis_vector n k) = 1 :=
  probability_of_outcome_self _ (Pure_State_Vector_basis_vector n k h)

/-- Specialization of `probability_of_outcome_self` to `f_to_vec`
    boolean-encoded basis states. -/
theorem probability_of_outcome_f_to_vec_self (n : Nat) (f : Nat → Bool) :
    probability_of_outcome (f_to_vec n f) (f_to_vec n f) = 1 :=
  probability_of_outcome_self _ (Pure_State_Vector_f_to_vec n f)

/-- Distinct computational basis states are orthogonal under the Born rule:
    `j ≠ k → |⟨e_j|e_k⟩|² = 0`. The inner product `(e_j)ᴴ · e_k` vanishes
    termwise — every index `i` makes at most one of the two indicator
    factors nonzero. -/
theorem probability_of_outcome_basis_orth (n j k : Nat) (h : j ≠ k) :
    probability_of_outcome (basis_vector n j) (basis_vector n k) = 0 := by
  unfold probability_of_outcome
  have key : ((basis_vector n j).conjTranspose * (basis_vector n k)) 0 0 = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro i _
    simp only [Matrix.conjTranspose_apply, basis_vector_apply]
    by_cases hij : i.val = j
    · simp [hij]; exact h
    · simp [hij]
  rw [key]
  exact Complex.normSq_zero

/-- Combined Kronecker-delta form: for valid indices `j, k < n`, the
    Born-rule overlap of two basis vectors is 1 if equal, 0 otherwise. -/
theorem probability_of_outcome_basis (n j k : Nat) (hj : j < n) (hk : k < n) :
    probability_of_outcome (basis_vector n j) (basis_vector n k)
      = if j = k then 1 else 0 := by
  by_cases h : j = k
  · subst h
    rw [if_pos rfl]
    exact probability_of_outcome_basis_self n j hj
  · rw [if_neg h]
    exact probability_of_outcome_basis_orth n j k h

/-- General Born-rule expansion: `prob φ ψ = |∑ i, conj(φ_i) · ψ_i|²` —
    the inner-product form, with the matrix multiplication unfolded. -/
theorem probability_of_outcome_apply {n : Nat} (φ ψ : Matrix (Fin n) (Fin 1) ℂ) :
    probability_of_outcome φ ψ
      = Complex.normSq (∑ i : Fin n, star (φ i 0) * ψ i 0) := by
  unfold probability_of_outcome
  rw [Matrix.mul_apply]
  simp [Matrix.conjTranspose_apply]

/-- The Born-rule probability of measuring the `k`-th basis state from a
    state vector `ψ` is exactly `|ψ k 0|²` — the squared amplitude of `ψ`
    at index `k`. This is the canonical "amplitude → probability" rule. -/
theorem probability_of_outcome_basis_apply (n k : Nat) (hk : k < n)
    (ψ : Matrix (Fin n) (Fin 1) ℂ) :
    probability_of_outcome (basis_vector n k) ψ
      = Complex.normSq (ψ ⟨k, hk⟩ 0) := by
  unfold probability_of_outcome
  have key : ((basis_vector n k).conjTranspose * ψ) 0 0 = ψ ⟨k, hk⟩ 0 := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp [Matrix.conjTranspose_apply, basis_vector_apply]
    · intro i _ hi
      have : i.val ≠ k := fun heq => hi (Fin.ext heq)
      simp [Matrix.conjTranspose_apply, basis_vector_apply, this]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [key]

/-- Completeness of computational-basis measurement: summing the Born-rule
    probabilities over all basis outcomes recovers the L2-norm-squared of `ψ`.
    Combined with `Pure_State_Vector ψ`, this yields the standard "total
    probability = 1" guarantee. -/
theorem probability_of_outcome_basis_finset_sum {n : Nat}
    (ψ : Matrix (Fin n) (Fin 1) ℂ) :
    ∑ k : Fin n, probability_of_outcome (basis_vector n k.val) ψ
      = ∑ k : Fin n, Complex.normSq (ψ k 0) := by
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [probability_of_outcome_basis_apply n k.val k.isLt]

/-- Total-probability theorem: for any pure state `ψ`, the sum of Born-rule
    probabilities over all computational-basis outcomes is exactly 1.
    Direct chain of `probability_of_outcome_basis_finset_sum` with the
    `Pure_State_Vector` definition. -/
theorem probability_of_outcome_total {n : Nat}
    (ψ : Matrix (Fin n) (Fin 1) ℂ) (h : Pure_State_Vector ψ) :
    ∑ k : Fin n, probability_of_outcome (basis_vector n k.val) ψ = 1 := by
  rw [probability_of_outcome_basis_finset_sum]
  exact h

/-- For a pure state, the Born-rule probability of any single
    computational-basis outcome is at most 1. Each term `|ψ_k|²` is
    non-negative and bounded by the total sum, which equals 1 by purity. -/
theorem probability_of_outcome_basis_le_one (n k : Nat) (hk : k < n)
    (ψ : Matrix (Fin n) (Fin 1) ℂ) (h : Pure_State_Vector ψ) :
    probability_of_outcome (basis_vector n k) ψ ≤ 1 := by
  rw [probability_of_outcome_basis_apply n k hk ψ]
  have key : Complex.normSq (ψ ⟨k, hk⟩ 0)
      ≤ ∑ i : Fin n, Complex.normSq (ψ i 0) := by
    apply Finset.single_le_sum (f := fun i => Complex.normSq (ψ i 0))
    · intro i _; exact Complex.normSq_nonneg _
    · exact Finset.mem_univ _
  unfold Pure_State_Vector at h
  rw [h] at key
  exact key

/-- Subset bound: for any pure state and any subset of basis outcomes,
    the sum of Born probabilities is at most 1. The standard "successful
    outcomes" bound used in QPE/Shor measurement-success arguments. -/
theorem probability_of_outcome_basis_finset_sum_le_one {n : Nat}
    (S : Finset (Fin n)) (ψ : Matrix (Fin n) (Fin 1) ℂ) (h : Pure_State_Vector ψ) :
    ∑ k ∈ S, probability_of_outcome (basis_vector n k.val) ψ ≤ 1 := by
  have h1 : ∑ k ∈ S, probability_of_outcome (basis_vector n k.val) ψ
            ≤ ∑ k : Fin n, probability_of_outcome (basis_vector n k.val) ψ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_univ S
    · intros i _ _; exact probability_of_outcome_nonneg _ _
  rw [probability_of_outcome_total ψ h] at h1
  exact h1

/-- The Born-rule probability of a basis outcome vanishes iff the
    corresponding amplitude vanishes — a direct consequence of
    `Complex.normSq_eq_zero`. Useful for "this measurement outcome is
    unreachable" arguments. -/
theorem probability_of_outcome_basis_eq_zero_iff (n k : Nat) (hk : k < n)
    (ψ : Matrix (Fin n) (Fin 1) ℂ) :
    probability_of_outcome (basis_vector n k) ψ = 0 ↔ ψ ⟨k, hk⟩ 0 = 0 := by
  rw [probability_of_outcome_basis_apply n k hk ψ]
  exact Complex.normSq_eq_zero

/-- Strict positivity: a nonzero amplitude gives a strictly positive
    measurement probability. Contrapositive of
    `probability_of_outcome_basis_eq_zero_iff`, useful for "this outcome
    is reachable" arguments. -/
theorem probability_of_outcome_basis_pos (n k : Nat) (hk : k < n)
    (ψ : Matrix (Fin n) (Fin 1) ℂ) (h : ψ ⟨k, hk⟩ 0 ≠ 0) :
    0 < probability_of_outcome (basis_vector n k) ψ := by
  rw [probability_of_outcome_basis_apply n k hk ψ]
  exact Complex.normSq_pos.mpr h

/-- Combined iff form: Born-rule probability is strictly positive iff
    the corresponding amplitude is nonzero. Packages
    `probability_of_outcome_basis_pos` with its converse. -/
theorem probability_of_outcome_basis_pos_iff (n k : Nat) (hk : k < n)
    (ψ : Matrix (Fin n) (Fin 1) ℂ) :
    0 < probability_of_outcome (basis_vector n k) ψ ↔ ψ ⟨k, hk⟩ 0 ≠ 0 := by
  rw [probability_of_outcome_basis_apply n k hk ψ]
  exact Complex.normSq_pos

/-- Pure state vectors are nonzero — their squared L2-norm sums to 1, but
    the zero vector has L2-norm 0 ≠ 1. -/
theorem Pure_State_Vector_ne_zero {n : Nat} (ψ : Matrix (Fin n) (Fin 1) ℂ)
    (h : Pure_State_Vector ψ) : ψ ≠ 0 := by
  intro hzero
  rw [hzero] at h
  unfold Pure_State_Vector at h
  simp at h

/-- Pure state vectors stay pure under negation (since |−x|² = |x|²). -/
theorem Pure_State_Vector_neg {n : Nat} (ψ : Matrix (Fin n) (Fin 1) ℂ)
    (h : Pure_State_Vector ψ) : Pure_State_Vector (-ψ) := by
  unfold Pure_State_Vector at h ⊢
  simp [Matrix.neg_apply, Complex.normSq_neg]
  exact h

/-- Pure state vectors stay pure under unit-modulus scalar multiplication
    (since |c·x|² = |c|² · |x|² = 1 · |x|²). Used for global-phase factors. -/
theorem Pure_State_Vector_smul_unit {n : Nat} (c : ℂ)
    (hc : Complex.normSq c = 1) (ψ : Matrix (Fin n) (Fin 1) ℂ)
    (h : Pure_State_Vector ψ) : Pure_State_Vector (c • ψ) := by
  unfold Pure_State_Vector at h ⊢
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul]
  rw [← Finset.mul_sum, h, mul_one]
  exact hc

/-- Specialization of `Pure_State_Vector_smul_unit` to `c = exp(iθ)`
    (always unit modulus for real θ). The most useful instance — captures
    the standard global-phase-factor case used throughout quantum computing. -/
theorem Pure_State_Vector_smul_exp_I {n : Nat} (θ : ℝ)
    (ψ : Matrix (Fin n) (Fin 1) ℂ) (h : Pure_State_Vector ψ) :
    Pure_State_Vector (Complex.exp (↑θ * Complex.I) • ψ) := by
  apply Pure_State_Vector_smul_unit _ ?_ ψ h
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- The tensor product of two pure states is a pure state. Direct
    1-line corollary of `kron_vec_normSq_sum`: ‖ψ ⊗ φ‖² = ‖ψ‖² · ‖φ‖²
    = 1 · 1 = 1. The capstone of the kron_vec layer. -/
theorem Pure_State_Vector_kron {a b : Nat}
    (ψ : Matrix (Fin (2^a)) (Fin 1) ℂ) (φ : Matrix (Fin (2^b)) (Fin 1) ℂ)
    (hψ : Pure_State_Vector ψ) (hφ : Pure_State_Vector φ) :
    Pure_State_Vector (kron_vec ψ φ) := by
  unfold Pure_State_Vector at *
  rw [kron_vec_normSq_sum, hψ, hφ, mul_one]

/-- The tensor product of two computational basis states is a pure state.
    Direct corollary of `Pure_State_Vector_kron` and
    `Pure_State_Vector_basis_vector`. -/
theorem Pure_State_Vector_kron_basis_vector {a b : Nat}
    (j : Fin (2^a)) (k : Fin (2^b)) :
    Pure_State_Vector
      (kron_vec (basis_vector (2^a) j.val) (basis_vector (2^b) k.val)) :=
  Pure_State_Vector_kron _ _
    (Pure_State_Vector_basis_vector _ _ j.isLt)
    (Pure_State_Vector_basis_vector _ _ k.isLt)

/-- The tensor product of two boolean-encoded basis states is a pure state.
    Symmetric companion of `Pure_State_Vector_kron_basis_vector` using
    `f_to_vec`. -/
theorem Pure_State_Vector_kron_f_to_vec {a b : Nat} (f g : Nat → Bool) :
    Pure_State_Vector (kron_vec (f_to_vec a f) (f_to_vec b g)) :=
  Pure_State_Vector_kron _ _
    (Pure_State_Vector_f_to_vec a f)
    (Pure_State_Vector_f_to_vec b g)

end FormalRV.Framework
