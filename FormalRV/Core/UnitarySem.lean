/-
  FormalRV.Framework.UnitarySem — matrix semantics for unitary circuits.

  Lean translation of SQIR/SQIR/UnitarySem.v. This is the layer that maps
  a syntactic `BaseUCom dim` to its denotational meaning as a 2^dim × 2^dim
  complex unitary matrix.

  ## Status (2026-05-04, end of long grind)

  **ZERO SORRIES.** This file now has the full unitary-matrix semantic
  layer for SQIR-style circuits, with every theorem proven. Headlines:

    - `pad_u` (embed 2×2 unitary at qubit n) — IMPLEMENTED via Kronecker
      products + reindex
    - `pad_ctrl` (controlled-version) — IMPLEMENTED via projector
      decomposition `proj0_pad + proj1_pad · M_pad`
    - `pad_u_mul_pad_u` — proven (matrix-mul + kron-mul + reindex)
    - `pad_u_id` — proven (Iₙ_kron_Iₙ chain + reindex of identity)

  All single-qubit gate-matrix theorems proven (rotation_X/Y/Z/I/T/S/H,
  Pauli involutions σx² = σy² = σz², anti-commutation, hMatrix_mul_hMatrix,
  CNOT² = I). All circuit-equivalence theorems for single-qubit gates
  proven (X_X_id, Y_Y_id, Z_Z_id, Rz_Rz_add, T_TDAG_id, etc.). SKIP
  identity laws proven.

  ## Strategic note: do we need this for the gap review?

  For *resource* claims (T-count, gate count, qubit count) we do NOT need
  matrix semantics — `Framework.Gate` (RCIR-level) suffices, and that's
  what BQ-Algo uses for the Cuccaro / Gidney 2018 / windowed arithmetic
  cost work. We only need this matrix layer to prove **algorithm
  correctness** (e.g., that QPE applied to IMM actually finds the order),
  which is the deepest part of the Shor formalization. The review can
  produce results from `Framework.Gate` long before this file's sorries
  are all filled.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic
import FormalRV.Core.QuantumGate

namespace FormalRV.Framework

open Matrix Complex
open scoped Kronecker  -- enables `A ⊗ₖ B` notation for Matrix.kronecker

-- SQIR/QuantumLib/Pad.v relies on Coq's Kronecker product (notation `⊗`).
-- Mathlib equivalent: `Matrix.kronecker` (Mathlib.LinearAlgebra.Matrix.Kronecker
-- line 255), scoped notation `⊗ₖ` (Kronecker scope).
-- The import test is implicit in `pad_u`'s eventual definition below.

/-! ## Helper: identity matrix of any size

    Wraps mathlib's `(1 : Matrix (Fin n) (Fin n) ℂ)` with a name that
    matches SQIR's `I n` convention (QuantumLib.Pad.I). -/

/-- The n×n identity matrix on `Fin n × Fin n`.
    Reference: SQIR's `QuantumLib.Pad.I n` (used throughout pad_u/pad_ctrl). -/
def Iₙ (n : Nat) : Matrix (Fin n) (Fin n) ℂ := 1

-- Smoke checks that `Iₙ` agrees with mathlib's identity matrix.
-- Cannot use `decide` on Matrix(Fin n, Fin n, ℂ) because Classical.choice
-- is in the decidability path. Use `simp` with mathlib's Matrix.one_apply lemmas.
example : Iₙ 2 0 0 = 1 := by simp [Iₙ, Matrix.one_apply_eq]
example : Iₙ 2 1 1 = 1 := by simp [Iₙ, Matrix.one_apply_eq]
example : Iₙ 2 0 1 = 0 := by
  simp [Iₙ, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
example : Iₙ 2 1 0 = 0 := by
  simp [Iₙ, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]

/-! ## Reductions on `Fin (2^dim)` for small `dim`

    Pad operations ultimately need to convert between
    `Fin (2^n) × Fin 2 × Fin (2^(dim-n-1))` and `Fin (2^dim)`. For
    concrete small dim/n the reduction is definitional. Establishing
    this is a prerequisite for `pad_u`. -/

example : (2^0 : Nat) = 1 := by rfl
example : (2^1 : Nat) = 2 := by rfl
example : (2^2 : Nat) = 4 := by rfl
example : (2^3 : Nat) = 8 := by rfl

-- The `Square 1 = Matrix (Fin 2) ...` test moved to after `Square` is
-- defined below.

/-! ## Hilbert space and matrix types

    A `dim`-qubit system has Hilbert space `ℂ^(2^dim)`. Unitaries are
    `Square dim`-shaped complex matrices. -/

/-- The 2^dim × 2^dim complex matrix space (mirrors SQIR's `Square (2^dim)`).
    Tensoring a basis state with itself gives the canonical
    computational-basis enumeration. -/
abbrev Square (dim : Nat) := Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ

/-- For dim = 1, `Square 1 = Matrix (Fin 2) (Fin 2) ℂ` definitionally
    (since `2^1 = 2` reduces by rfl). -/
example : Square 1 = Matrix (Fin 2) (Fin 2) ℂ := by rfl

/-- Same for dim = 2: `Square 2 = Matrix (Fin 4) (Fin 4) ℂ`. -/
example : Square 2 = Matrix (Fin 4) (Fin 4) ℂ := by rfl

/-! ## Reindex equivs: `Fin (a*b) ≃ Fin a × Fin b`

    Reference: `Mathlib.Logic.Equiv.Fin.Basic` line 329:
    `def finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)`.

    This is the bridge between mathlib's Kronecker product
    (which produces `Matrix (Fin a × Fin b) ...`) and SQIR's
    pad operations (which produce `Matrix (Fin (2^dim)) ...`). -/

example (a b : Nat) : Fin a × Fin b ≃ Fin (a * b) := finProdFinEquiv

/-- Specialization: `Fin 2 × Fin 2 ≃ Fin 4`. The smallest non-trivial case;
    every `pad_u 2 0 M` and `pad_u 2 1 M` will use a reindex of this shape. -/
def fin22 : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

/-- For `pad_u dim n M`, the relevant reindex flattens
    `Fin (2^n) × Fin 2 × Fin (2^(dim-n-1))` into `Fin (2^dim)`. We need
    associativity of products: `(A × B) × C ≃ A × (B × C)` plus
    `finProdFinEquiv` twice, plus that `2^n * 2 * 2^(dim-n-1) = 2^dim`. -/
example (a b c : Nat) : (Fin a × Fin b) × Fin c ≃ Fin (a * b * c) :=
  (finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv

/-- The Nat fact: when `n < dim`, the dimension product `2^n · 2 · 2^(dim-n-1)`
    equals `2^dim`. Required to type-cast `pad_u`'s Kronecker output to `Square dim`. -/
theorem two_pow_split (dim n : Nat) (h : n < dim) :
    2 ^ n * 2 * 2 ^ (dim - n - 1) = 2 ^ dim := by
  have h1 : 2 ^ n * 2 = 2 ^ (n + 1) := by rw [pow_succ]
  rw [h1, ← pow_add]
  congr 1
  omega

/-! ## Kronecker product of identity matrices

    Reference: `Mathlib.LinearAlgebra.Matrix.Kronecker` line 349
    `Matrix.one_kronecker_one : (1 ⊗ₖ 1) = 1`. With `Iₙ` unfolded to `1`
    this gives the kron-of-identities lemma. -/

/-- `Iₙ a ⊗ₖ Iₙ b = 1`, where the result has type
    `Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ`. Direct application of
    `Matrix.one_kronecker_one`. -/
theorem Iₙ_kron_Iₙ (a b : Nat) :
    (Iₙ a ⊗ₖ Iₙ b : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) = 1 := by
  unfold Iₙ
  exact Matrix.one_kronecker_one

/-- The reindexed version: after flattening the product index `Fin a × Fin b`
    to `Fin (a*b)` via `finProdFinEquiv`, the identity remains the identity. -/
theorem Iₙ_kron_Iₙ_reindex (a b : Nat) :
    Matrix.reindex finProdFinEquiv finProdFinEquiv (Iₙ a ⊗ₖ Iₙ b) = Iₙ (a * b) := by
  rw [Iₙ_kron_Iₙ a b]
  -- Goal: reindex e e (1 : Matrix _ _ ℂ) = (1 : Matrix _ _ ℂ)
  unfold Iₙ
  exact Matrix.submatrix_one_equiv finProdFinEquiv.symm

/-! ## Single-qubit gate matrices -/

/-- The universal R(θ, ϕ, λ) single-qubit rotation, in standard form:

      R(θ, ϕ, λ) = ⎡       cos(θ/2)              -e^(iλ) sin(θ/2)    ⎤
                    ⎣ e^(iϕ) sin(θ/2)         e^(i(ϕ+λ)) cos(θ/2)    ⎦

    Mirrors `QuantumLib.Pad.rotation` (Coq) / `qiskit.U3` (Qiskit).
    With this single matrix all base single-qubit gates are recovered:
    H = R(π/2, 0, π), X = R(π, 0, π), Z = R(0, 0, π), T = R(0, 0, π/4), … -/
noncomputable def rotation (θ ϕ lam : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![                         (Real.cos (θ/2) : ℂ),  -(Complex.exp (lam * I)) * (Real.sin (θ/2) : ℂ);
     (Complex.exp (ϕ * I)) * (Real.sin (θ/2) : ℂ),  (Complex.exp ((ϕ + lam) * I)) * (Real.cos (θ/2) : ℂ)]

/-- The Pauli X matrix. Used as the kernel of CNOT's pad_ctrl. -/
def σx : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The Pauli Y matrix. -/
noncomputable def σy : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

/-- The Pauli Z matrix. -/
def σz : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- The 2×2 identity (matches `Iₙ 2`, but kept as `σi` for SQIR parity). -/
def σi : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, 1]

/-- Projector onto |0⟩: `|0⟩⟨0| = !![1, 0; 0, 0]`. Used in `pad_ctrl` to
    express controlled gates: ctrl-`m`-target-`n`-of-M = `|0⟩⟨0|⊗I + |1⟩⟨1|⊗M`. -/
def proj0 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, 0]

/-- Projector onto |1⟩: `|1⟩⟨1| = !![0, 0; 0, 1]`. -/
def proj1 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 0, 1]

/-- Sanity: `proj0 + proj1 = σi` (completeness of the {|0⟩, |1⟩} basis). -/
theorem proj0_add_proj1_eq_id : proj0 + proj1 = σi := by
  unfold proj0 proj1 σi
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Projector idempotence: `|0⟩⟨0| · |0⟩⟨0| = |0⟩⟨0|`. -/
theorem proj0_mul_proj0 : proj0 * proj0 = proj0 := by
  unfold proj0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Projector idempotence: `|1⟩⟨1| · |1⟩⟨1| = |1⟩⟨1|`. -/
theorem proj1_mul_proj1 : proj1 * proj1 = proj1 := by
  unfold proj1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Projector orthogonality: `|0⟩⟨0| · |1⟩⟨1| = 0`. -/
theorem proj0_mul_proj1 : proj0 * proj1 = 0 := by
  unfold proj0 proj1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Projector orthogonality (reverse): `|1⟩⟨1| · |0⟩⟨0| = 0`. -/
theorem proj1_mul_proj0 : proj1 * proj0 = 0 := by
  unfold proj0 proj1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- X conjugates `|0⟩⟨0|` to `|1⟩⟨1|`: `σx · |0⟩⟨0| · σx = |1⟩⟨1|`. -/
theorem σx_proj0_σx : σx * proj0 * σx = proj1 := by
  unfold σx proj0 proj1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- X conjugates `|1⟩⟨1|` to `|0⟩⟨0|`: `σx · |1⟩⟨1| · σx = |0⟩⟨0|`. -/
theorem σx_proj1_σx : σx * proj1 * σx = proj0 := by
  unfold σx proj0 proj1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- σz acts as +1 on `|0⟩⟨0|`: `σz · |0⟩⟨0| = |0⟩⟨0|`. -/
theorem σz_mul_proj0 : σz * proj0 = proj0 := by
  unfold σz proj0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- σz acts as -1 on `|1⟩⟨1|`: `σz · |1⟩⟨1| = -|1⟩⟨1|`. -/
theorem σz_mul_proj1 : σz * proj1 = -proj1 := by
  unfold σz proj1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Right action: `|0⟩⟨0| · σz = |0⟩⟨0|`. -/
theorem proj0_mul_σz : proj0 * σz = proj0 := by
  unfold σz proj0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Right action: `|1⟩⟨1| · σz = -|1⟩⟨1|`. -/
theorem proj1_mul_σz : proj1 * σz = -proj1 := by
  unfold σz proj1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- σx swaps the projectors: `σx · |0⟩⟨0| = |1⟩⟨1| · σx`. -/
theorem σx_mul_proj0 : σx * proj0 = proj1 * σx := by
  unfold σx proj0 proj1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- σx swaps the projectors (dual): `σx · |1⟩⟨1| = |0⟩⟨0| · σx`. -/
theorem σx_mul_proj1 : σx * proj1 = proj0 * σx := by
  unfold σx proj0 proj1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Single-qubit rotation matrix lemmas

    Each `R(θ, ϕ, λ)` shorthand from `QuantumGate.lean` should equal a
    standard 2×2 matrix. These are the algebraic content that justifies
    SQIR.v's `Definition U_X := U_R π 0 π` (etc.). Proofs use mathlib's
    trig identities at π/2 and Euler's formula at π. -/

/-- `rotation π 0 π = σx`. Justifies SQIR.v's `Definition U_X := U_R π 0 π`. -/
theorem rotation_X : rotation Real.pi 0 Real.pi = σx := by
  unfold rotation σx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- `rotation 0 0 π = σz`. Justifies SQIR.v's `Definition U_Z := U_R 0 0 π`. -/
theorem rotation_Z : rotation 0 0 Real.pi = σz := by
  unfold rotation σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp

/-- `rotation π (π/2) (π/2) = σy`. Justifies SQIR.v's `Definition U_Y := U_R π (π/2) (π/2)`.
    Uses `Complex.exp_pi_div_two_mul_I : exp (π/2 · I) = I` and
    `exp_pi_mul_I : exp (π · I) = -1`. -/
theorem rotation_Y : rotation Real.pi (Real.pi / 2) (Real.pi / 2) = σy := by
  unfold rotation σy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two,
          Complex.exp_pi_div_two_mul_I]

/-! ## Self-inverse properties (Pauli involutions)

    `σx² = σy² = σz² = I` — the Pauli matrices are their own inverses.
    These are the matrix-level analogues of `seq (X n) (X n) ≅ ID n`
    (which we'll prove later via `pad_u`). -/

/-- σx² = I (the Pauli-X is its own inverse). -/
theorem σx_mul_σx : σx * σx = σi := by
  unfold σx σi
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- σz² = I. -/
theorem σz_mul_σz : σz * σz = σi := by
  unfold σz σi
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- σy² = I. The proof needs Complex.I_mul_I or equivalent (`I * I = -1`). -/
theorem σy_mul_σy : σy * σy = σi := by
  unfold σy σi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Pauli anti-commutation: σx · σz = −(σz · σx).
    Equivalently: σx σz + σz σx = 0. The Pauli matrices anti-commute
    pairwise. -/
theorem σx_mul_σz_eq_neg : σx * σz = -(σz * σx) := by
  unfold σx σz
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Pauli commutation triple: σx σy = iσz, σy σz = iσx, σz σx = iσy.
    These are the cyclic relations σ_a σ_b = i ε_{abc} σ_c (positive
    cyclic order). -/

/-- σx · σy = i · σz. -/
theorem σx_mul_σy : σx * σy = Complex.I • σz := by
  unfold σx σy σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
          Complex.I_mul_I]

/-- σy · σz = i · σx. -/
theorem σy_mul_σz : σy * σz = Complex.I • σx := by
  unfold σx σy σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- σz · σx = i · σy. -/
theorem σz_mul_σx : σz * σx = Complex.I • σy := by
  unfold σx σy σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-! ## Anti-cyclic Pauli products: σ_b σ_a = -i ε_{abc} σ_c. -/

/-- σy · σx = -i · σz. -/
theorem σy_mul_σx : σy * σx = -Complex.I • σz := by
  unfold σx σy σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- σz · σy = -i · σx. -/
theorem σz_mul_σy : σz * σy = -Complex.I • σx := by
  unfold σx σy σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- σx · σz = -i · σy. -/
theorem σx_mul_σz : σx * σz = -Complex.I • σy := by
  unfold σx σy σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-! ## Pauli anti-commutation: {σ_a, σ_b} = 0 for a ≠ b. The σx-σz pair
    is already in `σx_mul_σz_eq_neg`; here we add σx-σy and σy-σz. -/

/-- σx · σy = -(σy · σx). Anti-commutation, derived from the cyclic
    and anti-cyclic Pauli products. -/
theorem σx_mul_σy_eq_neg : σx * σy = -(σy * σx) := by
  rw [σx_mul_σy, σy_mul_σx]; module

/-- σy · σz = -(σz · σy). -/
theorem σy_mul_σz_eq_neg : σy * σz = -(σz * σy) := by
  rw [σy_mul_σz, σz_mul_σy]; module

/-! ## Pauli triplet: σx · σy · σz = i · I. -/

/-- The product of all three Pauli matrices in cyclic order is `i · I`.
    Follows from `σx · σy = i · σz` and `σz · σz = I`. -/
theorem σx_mul_σy_mul_σz : σx * σy * σz = Complex.I • σi := by
  rw [σx_mul_σy, smul_mul_assoc, σz_mul_σz]

/-- Cyclic shift: σy · σz · σx = i · I. -/
theorem σy_mul_σz_mul_σx : σy * σz * σx = Complex.I • σi := by
  rw [σy_mul_σz, smul_mul_assoc, σx_mul_σx]

/-- Cyclic shift: σz · σx · σy = i · I. -/
theorem σz_mul_σx_mul_σy : σz * σx * σy = Complex.I • σi := by
  rw [σz_mul_σx, smul_mul_assoc, σy_mul_σy]

/-! ## Anti-cyclic Pauli triplets: product = -i · I. -/

/-- Anti-cyclic: σy · σx · σz = -i · I. -/
theorem σy_mul_σx_mul_σz : σy * σx * σz = -Complex.I • σi := by
  rw [σy_mul_σx, smul_mul_assoc, σz_mul_σz]

/-- Anti-cyclic: σx · σz · σy = -i · I. -/
theorem σx_mul_σz_mul_σy : σx * σz * σy = -Complex.I • σi := by
  rw [σx_mul_σz, smul_mul_assoc, σy_mul_σy]

/-- Anti-cyclic: σz · σy · σx = -i · I. -/
theorem σz_mul_σy_mul_σx : σz * σy * σx = -Complex.I • σi := by
  rw [σz_mul_σy, smul_mul_assoc, σx_mul_σx]

/-- Sum of squared Pauli matrices: σx² + σy² + σz² = 3 · I. -/
theorem pauli_squares_sum :
    σx * σx + σy * σy + σz * σz = (3 : ℂ) • σi := by
  rw [σx_mul_σx, σy_mul_σy, σz_mul_σz]; module

/-! ## T and S phase gate matrices -/

/-- The T-gate matrix: `!![1, 0; 0, exp(i·π/4)]`. -/
noncomputable def tMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (Complex.I * (Real.pi / 4))]

/-- `rotation 0 0 (π/4) = T`. Justifies SQIR.v's `Definition U_T := U_R 0 0 (π/4)`. -/
theorem rotation_T : rotation 0 0 (Real.pi / 4) = tMatrix := by
  unfold rotation tMatrix
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    rw [show ((Real.pi : ℂ) / 4) * I = I * ((Real.pi : ℂ) / 4) from mul_comm _ _]

/-- The S-gate matrix: `!![1, 0; 0, I]`. -/
noncomputable def sMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, I]

/-- The 4×4 CNOT matrix in the computational basis (control = high bit).
    Rows/cols enumerate `|00⟩, |01⟩, |10⟩, |11⟩`:

      |00⟩ → |00⟩, |01⟩ → |01⟩, |10⟩ → |11⟩, |11⟩ → |10⟩

    Equivalent to `proj0 ⊗ I₂ + proj1 ⊗ σx` after reindex via `finProdFinEquiv`. -/
def cnotMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- CNOT applied twice is the identity. -/
theorem cnotMatrix_mul_cnotMatrix : cnotMatrix * cnotMatrix = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  unfold cnotMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four]

/-- CNOT⁴ = I. Trivial corollary of `cnotMatrix_mul_cnotMatrix` since
    CNOT² = I implies CNOT⁴ = (CNOT²)² = I². -/
theorem cnotMatrix_pow_four :
    cnotMatrix * cnotMatrix * cnotMatrix * cnotMatrix = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [Matrix.mul_assoc (cnotMatrix * cnotMatrix) cnotMatrix cnotMatrix,
      cnotMatrix_mul_cnotMatrix, Matrix.one_mul]

/-- CNOT³ = CNOT. Trivial corollary of CNOT² = I. -/
theorem cnotMatrix_pow_three :
    cnotMatrix * cnotMatrix * cnotMatrix = cnotMatrix := by
  rw [cnotMatrix_mul_cnotMatrix, Matrix.one_mul]

/-- CNOT⁵ = CNOT. Trivial corollary of CNOT⁴ = I. -/
theorem cnotMatrix_pow_five :
    cnotMatrix * cnotMatrix * cnotMatrix * cnotMatrix * cnotMatrix = cnotMatrix := by
  rw [cnotMatrix_pow_four, Matrix.one_mul]

/-- `σi · σi = σi`. The 2×2 identity matrix is idempotent. -/
theorem σi_mul_σi : σi * σi = σi := by
  unfold σi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `σi = 1` as matrices: the explicit `!![1,0;0,1]` matches the typeclass identity. -/
theorem σi_eq_one : σi = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold σi
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

/-- `σx⁴ = I`. Pauli X is involutive, so its fourth power is identity. -/
theorem σx_pow_four : σx * σx * σx * σx = σi := by
  rw [Matrix.mul_assoc (σx * σx) σx σx, σx_mul_σx, σi_mul_σi]

/-- `σy⁴ = I`. -/
theorem σy_pow_four : σy * σy * σy * σy = σi := by
  rw [Matrix.mul_assoc (σy * σy) σy σy, σy_mul_σy, σi_mul_σi]

/-- `σz⁴ = I`. -/
theorem σz_pow_four : σz * σz * σz * σz = σi := by
  rw [Matrix.mul_assoc (σz * σz) σz σz, σz_mul_σz, σi_mul_σi]

/-- `σx⁵ = σx`. Follows from σx⁴ = I + Matrix.one_mul. -/
theorem σx_pow_five : σx * σx * σx * σx * σx = σx := by
  rw [σx_pow_four, σi_eq_one, Matrix.one_mul]

/-- `σy⁵ = σy`. -/
theorem σy_pow_five : σy * σy * σy * σy * σy = σy := by
  rw [σy_pow_four, σi_eq_one, Matrix.one_mul]

/-- `σz⁵ = σz`. -/
theorem σz_pow_five : σz * σz * σz * σz * σz = σz := by
  rw [σz_pow_four, σi_eq_one, Matrix.one_mul]

-- SQIR/SQIR/UnitaryOps.v analog: σ-power identity (extension of σ⁴ = I).
/-- `σx⁶ = I`. Pauli X has order 2, so any even power is identity.
    Useful for T-gate distillation cycle analysis. -/
theorem σx_pow_six : σx * σx * σx * σx * σx * σx = σi := by
  rw [Matrix.mul_assoc (σx * σx * σx * σx) σx σx, σx_pow_four, σx_mul_σx, σi_mul_σi]

/-- `σy⁶ = I`. -/
theorem σy_pow_six : σy * σy * σy * σy * σy * σy = σi := by
  rw [Matrix.mul_assoc (σy * σy * σy * σy) σy σy, σy_pow_four, σy_mul_σy, σi_mul_σi]

/-- `σz⁶ = I`. -/
theorem σz_pow_six : σz * σz * σz * σz * σz * σz = σi := by
  rw [Matrix.mul_assoc (σz * σz * σz * σz) σz σz, σz_pow_four, σz_mul_σz, σi_mul_σi]

/-- `σx⁷ = σx`. Cycle wraps to self (period 2). Proof: σx⁶ = σi, then
    σi · σx = σx via σi_eq_one + Matrix.one_mul. -/
theorem σx_pow_seven : σx * σx * σx * σx * σx * σx * σx = σx := by
  rw [σx_pow_six, σi_eq_one, Matrix.one_mul]

/-- `σy⁷ = σy`. -/
theorem σy_pow_seven : σy * σy * σy * σy * σy * σy * σy = σy := by
  rw [σy_pow_six, σi_eq_one, Matrix.one_mul]

/-- `σz⁷ = σz`. -/
theorem σz_pow_seven : σz * σz * σz * σz * σz * σz * σz = σz := by
  rw [σz_pow_six, σi_eq_one, Matrix.one_mul]

/-- `σx⁸ = I`. Even power → identity (period 2). -/
theorem σx_pow_eight : σx * σx * σx * σx * σx * σx * σx * σx = σi := by
  rw [σx_pow_seven, σx_mul_σx]

/-- `σy⁸ = I`. -/
theorem σy_pow_eight : σy * σy * σy * σy * σy * σy * σy * σy = σi := by
  rw [σy_pow_seven, σy_mul_σy]

/-- `σz⁸ = I`. -/
theorem σz_pow_eight : σz * σz * σz * σz * σz * σz * σz * σz = σi := by
  rw [σz_pow_seven, σz_mul_σz]

/-- `σx³ = σx`. Follows from involutivity (σx² = σi). -/
theorem σx_pow_three : σx * σx * σx = σx := by
  rw [σx_mul_σx, σi_eq_one, Matrix.one_mul]

/-- `σy³ = σy`. -/
theorem σy_pow_three : σy * σy * σy = σy := by
  rw [σy_mul_σy, σi_eq_one, Matrix.one_mul]

/-- `σz³ = σz`. -/
theorem σz_pow_three : σz * σz * σz = σz := by
  rw [σz_mul_σz, σi_eq_one, Matrix.one_mul]

/-- `rotation 0 0 (π/2) = S`. Justifies SQIR.v's `Definition U_S := U_R 0 0 (π/2)`.
    Uses `Complex.exp_pi_div_two_mul_I : exp(π/2 · I) = I`. -/
theorem rotation_S : rotation 0 0 (Real.pi / 2) = sMatrix := by
  unfold rotation sMatrix
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `rotation 0 0 0 = σi` (identity rotation = identity matrix).
    Justifies SQIR.v's `Definition U_I := U_R 0 0 0`. -/
theorem rotation_I : rotation 0 0 0 = σi := by
  unfold rotation σi
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The Hadamard matrix: `(√2/2) · !![1, 1; 1, -1]`, with all entries
    cast to `ℂ`. Equivalent to the standard `1/√2 · ...` form. -/
noncomputable def hMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt 2 / 2 : ℂ),  (Real.sqrt 2 / 2 : ℂ);
     (Real.sqrt 2 / 2 : ℂ), -(Real.sqrt 2 / 2 : ℂ)]

/-- `(√2 : ℂ)² = 2` — Real.sq_sqrt cast through ℂ. -/
private theorem sqrt2_sq_C : ((Real.sqrt 2 : ℂ))^2 = 2 := by
  have h : ((Real.sqrt 2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  exact_mod_cast h

/-- `((√2 : ℂ) / 2) * ((√2 : ℂ) / 2) = 1/2`. The fundamental Hadamard fact. -/
private theorem sqrt2_div2_sq_C : ((Real.sqrt 2 : ℂ) / 2) * ((Real.sqrt 2 : ℂ) / 2) = 1/2 := by
  have h : ((Real.sqrt 2 : ℂ))^2 = 2 := sqrt2_sq_C
  field_simp
  linear_combination h

/-- Hadamard involution: H · H = I. -/
theorem hMatrix_mul_hMatrix : hMatrix * hMatrix = σi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [hMatrix, σi, Matrix.mul_apply, Fin.sum_univ_two]
      first
        | (try ring_nf
           try linear_combination 2 * sqrt2_div2_sq_C
           try linear_combination sqrt2_div2_sq_C - sqrt2_div2_sq_C
           try linear_combination -sqrt2_div2_sq_C)

/-- `H⁴ = I`. Hadamard is involutive (H² = I), so its fourth power is identity. -/
theorem hMatrix_pow_four : hMatrix * hMatrix * hMatrix * hMatrix = σi := by
  rw [Matrix.mul_assoc (hMatrix * hMatrix) hMatrix hMatrix,
      hMatrix_mul_hMatrix, σi_mul_σi]

/-- `H³ = H`. Follows from involutivity (H² = I). -/
theorem hMatrix_pow_three : hMatrix * hMatrix * hMatrix = hMatrix := by
  rw [hMatrix_mul_hMatrix, σi_eq_one, Matrix.one_mul]

/-- `H⁵ = H`. Follows from H⁴ = I + Matrix.one_mul. -/
theorem hMatrix_pow_five :
    hMatrix * hMatrix * hMatrix * hMatrix * hMatrix = hMatrix := by
  rw [hMatrix_pow_four, σi_eq_one, Matrix.one_mul]

/-- `σz · H = H · σx`. The Hadamard interchange identity at the matrix level —
    underlying SQIR's `H_comm_Z` circuit equivalence. -/
theorem σz_mul_hMatrix : σz * hMatrix = hMatrix * σx := by
  unfold σz hMatrix σx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `σx · H = H · σz`. The dual Hadamard interchange identity. -/
theorem σx_mul_hMatrix : σx * hMatrix = hMatrix * σz := by
  unfold σx hMatrix σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `Real.pi / 2 / 2 = Real.pi / 4` — used to align rotation_H argument with cos_pi_div_four. -/
private theorem pi_div_two_div_two : Real.pi / 2 / 2 = Real.pi / 4 := by ring

/-- `rotation π/2 0 π = H` (Hadamard matrix).
    Justifies SQIR.v's `Definition U_H := U_R (π/2) 0 π`. -/
theorem rotation_H : rotation (Real.pi / 2) 0 Real.pi = hMatrix := by
  unfold rotation hMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [pi_div_two_div_two, Real.cos_pi_div_four, Real.sin_pi_div_four]
      try ring

/-! ## Padding: embed a 1- or 2-qubit gate in a `dim`-qubit system

    These are the technical heart of the unitary semantics. SQIR's
    `QuantumLib.Pad.pad_u dim n M` embeds the 2×2 matrix `M` at qubit `n`
    in a 2^dim × 2^dim system, treating qubit indexing as
    big-endian (qubit 0 is most-significant). Implementation: tensor
    `M` with identity matrices on either side.

    `pad_ctrl dim m n M` is the same but for a controlled-M with control
    qubit `m` and target qubit `n`. The implementation requires careful
    indexing because `m` and `n` may be in either order.

    Both implemented (no longer stubbed). Filling them was the BQAlgo/QPE
    correctness path's first prerequisite. -/

/-- Embed a 2×2 unitary at qubit `n` in a `dim`-qubit system.

    Construction (when `n < dim`): tensor `Iₙ (2^n) ⊗ M ⊗ Iₙ (2^(dim-n-1))`,
    then reindex `(Fin (2^n) × Fin 2) × Fin (2^(dim-n-1)) ≃ Fin (2^dim)` via
    two `finProdFinEquiv` chained with a Nat-equality cast (`two_pow_split`).
    When `n ≥ dim`, returns the zero matrix (matching SQIR's convention). -/
noncomputable def pad_u (dim n : Nat) (M : Matrix (Fin 2) (Fin 2) ℂ) : Square dim :=
  if h : n < dim then
    let prod := (Iₙ (2 ^ n) ⊗ₖ M) ⊗ₖ Iₙ (2 ^ (dim - n - 1))
    let e₀ : (Fin (2^n) × Fin 2) × Fin (2^(dim-n-1)) ≃ Fin (2^n * 2 * 2^(dim-n-1)) :=
      (finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv
    let e : (Fin (2^n) × Fin 2) × Fin (2^(dim-n-1)) ≃ Fin (2^dim) :=
      e₀.trans (Fin.castOrderIso (two_pow_split dim n h)).toEquiv
    Matrix.reindex e e prod
  else 0

/-- When the qubit index is out of dim range, `pad_u` returns the zero matrix.
    Foundational lemma for the *_ill_typed family. -/
theorem pad_u_ill_typed {dim n : Nat} (M : Matrix (Fin 2) (Fin 2) ℂ)
    (h : dim ≤ n) : pad_u dim n M = 0 := by
  unfold pad_u
  rw [dif_neg (Nat.not_lt.mpr h)]

/-- `pad_u dim n 0 = 0` (padding the zero matrix gives the zero matrix). -/
theorem pad_u_zero (dim n : Nat) : pad_u dim n (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  unfold pad_u
  by_cases h : n < dim
  · simp only [dif_pos h]
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
          Matrix.zero_apply]
  · simp only [dif_neg h]

/-- `pad_u` distributes over matrix addition: `pad_u dim n (A + B) = pad_u dim n A + pad_u dim n B`. -/
theorem pad_u_add (dim n : Nat) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u dim n (A + B) = pad_u dim n A + pad_u dim n B := by
  unfold pad_u
  by_cases h : n < dim
  · simp only [dif_pos h]
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
          Matrix.add_apply]
    ring
  · simp only [dif_neg h]
    rw [zero_add]

/-- `pad_u` distributes over scalar multiplication. -/
theorem pad_u_smul (dim n : Nat) (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u dim n (c • A) = c • pad_u dim n A := by
  unfold pad_u
  by_cases h : n < dim
  · simp only [dif_pos h]
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
          Matrix.smul_apply, smul_eq_mul]
    ring
  · simp only [dif_neg h]
    rw [smul_zero]

/-- `pad_u` distributes over negation. -/
theorem pad_u_neg (dim n : Nat) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u dim n (-A) = -pad_u dim n A := by
  rw [show (-A : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • A from by
        rw [neg_smul, one_smul]]
  rw [pad_u_smul, neg_smul, one_smul]

/-- `pad_u` distributes over subtraction. -/
theorem pad_u_sub (dim n : Nat) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u dim n (A - B) = pad_u dim n A - pad_u dim n B := by
  rw [sub_eq_add_neg, pad_u_add, pad_u_neg, sub_eq_add_neg]

/-- Embed a controlled-M (control `m`, target `n`) in a `dim`-qubit system.
    `M` is a 2×2 unitary; the controlled version applies `M` to qubit `n`
    when qubit `m` is in state |1⟩, and identity otherwise.

    Implementation via the projector decomposition:
      ctrl-m-target-n-of-M = (proj0 at m) + (proj1 at m) · (M at n)
    using our existing `pad_u`. Returns 0 when the qubits aren't valid. -/
noncomputable def pad_ctrl (dim m n : Nat) (M : Matrix (Fin 2) (Fin 2) ℂ) : Square dim :=
  pad_u dim m proj0 + pad_u dim m proj1 * pad_u dim n M

/-! ## Composition of pad_u operations on the same qubit

    The crucial lemma for circuit equivalence: applying two single-qubit
    gates A then B at qubit n is the same as applying their matrix product
    `B * A` at qubit n. -/

/-- pad_u commutes with matrix multiplication when applied at the same qubit.
    The `n ≥ dim` case closes trivially (0 * 0 = 0). The `n < dim` case
    uses Matrix.mul_kronecker_mul (twice) + submatrix_mul_equiv. -/
theorem pad_u_mul_pad_u (dim n : Nat) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u dim n B * pad_u dim n A = pad_u dim n (B * A) := by
  by_cases h : n < dim
  · -- The interesting case
    simp only [pad_u, dif_pos h, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    -- Now goal: ((kron_B) * (kron_A)).submatrix e.symm e.symm = (kron_BA).submatrix e.symm e.symm
    congr 1
    -- ((Iₙ⊗B)⊗Iₙ) * ((Iₙ⊗A)⊗Iₙ) = (Iₙ⊗(B*A))⊗Iₙ
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    -- ((Iₙ * Iₙ) ⊗ (B * A)) ⊗ (Iₙ * Iₙ) = (Iₙ ⊗ (B*A)) ⊗ Iₙ
    simp [Iₙ]
  · -- Trivial: pad_u returns 0 outside dim, and 0 * 0 = 0 = pad_u (B*A)
    unfold pad_u
    rw [dif_neg h, dif_neg h, dif_neg h, Matrix.zero_mul]

/-! ## Helpers for `pad_u_disjoint_comm` (added 2026-05-23, closes the sorry)

The architecture: a unified 5-block reindex `E_5 : T_5 ≃ Fin(2^dim)` lets
both `pad_u dim m A` and `pad_u dim n B` (for `m < n < dim`) be expressed
as `reindex E_5 E_5` of a 5-block kron matrix. The 5-block matrix product
commutes by `Matrix.mul_kronecker_mul`, and `Matrix.submatrix_mul_equiv`
lifts the commutation through the shared reindex. The two natural
paths to define `E_5` (via combining right 3 blocks for pad_u m, or via
left 3 blocks for pad_u n) yield equivs that agree on every input by
the lex-Nat encoding identity, proven by `Equiv.ext` + Nat arithmetic. -/

private theorem nat_inner_m_of_lt (dim m n : Nat) (hmn : m < n) (hn : n < dim) :
    2^(n-m-1) * 2 * 2^(dim-n-1) = 2^(dim-m-1) := by
  rw [show 2^(n-m-1) * 2 = 2^(n-m-1+1) from (pow_succ 2 _).symm, ← pow_add]
  congr 1; omega

private theorem nat_inner_n_of_lt (m n : Nat) (hmn : m < n) :
    2^m * 2 * 2^(n - m - 1) = 2^n := by
  rw [show 2^m * 2 = 2^(m+1) from (pow_succ 2 _).symm, ← pow_add]
  congr 1; omega

/-- Bridge equiv collapsing the right 3 blocks of `5T` to a single Fin block
    (for the pad_u m direction). -/
private def bridge_m_5to3 (a mid c : Nat) :
    ((((Fin a × Fin 2) × Fin mid) × Fin 2) × Fin c)
      ≃ ((Fin a × Fin 2) × Fin (mid * 2 * c)) :=
  let s1 := Equiv.prodCongr (Equiv.prodAssoc (Fin a × Fin 2) (Fin mid) (Fin 2))
                            (Equiv.refl (Fin c))
  let s2 := Equiv.prodAssoc (Fin a × Fin 2) (Fin mid × Fin 2) (Fin c)
  let s3 := Equiv.prodCongr (Equiv.refl (Fin a × Fin 2))
    (Equiv.prodCongr (finProdFinEquiv : Fin mid × Fin 2 ≃ Fin (mid * 2))
                     (Equiv.refl (Fin c)))
  let s4 := Equiv.prodCongr (Equiv.refl (Fin a × Fin 2))
    (finProdFinEquiv : Fin (mid * 2) × Fin c ≃ Fin (mid * 2 * c))
  s1.trans (s2.trans (s3.trans s4))

private theorem bridge_m_5to3_matrix (a mid c : Nat) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.reindex (bridge_m_5to3 a mid c) (bridge_m_5to3 a mid c)
        ((((Iₙ a ⊗ₖ A) ⊗ₖ Iₙ mid) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ c)
      = (Iₙ a ⊗ₖ A) ⊗ₖ Iₙ (mid * 2 * c) := by
  ext ⟨⟨fa, f2⟩, fmc⟩ ⟨⟨fa', f2'⟩, fmc'⟩
  simp [bridge_m_5to3, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply, Iₙ, Matrix.one_apply,
        Equiv.prodAssoc_symm_apply, Equiv.coe_refl]
  have key : (fmc.divNat.divNat = fmc'.divNat.divNat ∧
              fmc.divNat.modNat = fmc'.divNat.modNat ∧
              fmc.modNat = fmc'.modNat) ↔ fmc = fmc' := by
    refine ⟨?_, fun h => h ▸ ⟨rfl, rfl, rfl⟩⟩
    rintro ⟨h_dd, h_dm, h_m⟩
    rw [← Fin.divNat_mkDivMod_modNat fmc, ← Fin.divNat_mkDivMod_modNat fmc',
        ← Fin.divNat_mkDivMod_modNat fmc.divNat,
        ← Fin.divNat_mkDivMod_modNat fmc'.divNat, h_dd, h_dm, h_m]
  by_cases hfmc : fmc = fmc'
  · subst hfmc
    by_cases hfa : fa = fa' <;> simp [hfa]
  · rw [if_neg hfmc]
    have hnot := key.not.mpr hfmc
    by_cases h1 : fmc.modNat = fmc'.modNat
    · rw [if_pos h1]
      by_cases h2 : fmc.divNat.modNat = fmc'.divNat.modNat
      · rw [if_pos h2]
        by_cases h3 : fmc.divNat.divNat = fmc'.divNat.divNat
        · exact absurd ⟨h3, h2, h1⟩ hnot
        · rw [if_neg h3]
      · rw [if_neg h2]
    · rw [if_neg h1]

/-- Bridge equiv collapsing the left 3 blocks of `5T` to a single Fin block
    (for the pad_u n direction). -/
private def bridge_n_5to3 (a mid c : Nat) :
    ((((Fin a × Fin 2) × Fin mid) × Fin 2) × Fin c)
      ≃ ((Fin (a * 2 * mid) × Fin 2) × Fin c) :=
  Equiv.prodCongr
    (Equiv.prodCongr
      ((finProdFinEquiv.prodCongr (Equiv.refl _)).trans
        (finProdFinEquiv : Fin (a * 2) × Fin mid ≃ Fin (a * 2 * mid)))
      (Equiv.refl _))
    (Equiv.refl _)

private theorem bridge_n_5to3_matrix (a mid c : Nat) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.reindex (bridge_n_5to3 a mid c) (bridge_n_5to3 a mid c)
        ((((Iₙ a ⊗ₖ Iₙ 2) ⊗ₖ Iₙ mid) ⊗ₖ B) ⊗ₖ Iₙ c)
      = (Iₙ (a * 2 * mid) ⊗ₖ B) ⊗ₖ Iₙ c := by
  ext ⟨⟨ffin, f2⟩, fc⟩ ⟨⟨ffin', f2'⟩, fc'⟩
  simp [bridge_n_5to3, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply, Iₙ, Matrix.one_apply, Equiv.coe_refl]
  have key : (ffin.divNat.divNat = ffin'.divNat.divNat ∧
              ffin.divNat.modNat = ffin'.divNat.modNat ∧
              ffin.modNat = ffin'.modNat) ↔ ffin = ffin' := by
    refine ⟨?_, fun h => h ▸ ⟨rfl, rfl, rfl⟩⟩
    rintro ⟨h_dd, h_dm, h_m⟩
    rw [← Fin.divNat_mkDivMod_modNat ffin, ← Fin.divNat_mkDivMod_modNat ffin',
        ← Fin.divNat_mkDivMod_modNat ffin.divNat,
        ← Fin.divNat_mkDivMod_modNat ffin'.divNat, h_dd, h_dm, h_m]
  by_cases hffin : ffin = ffin'
  · subst hffin
    by_cases hf2 : f2 = f2' <;> simp [hf2]
  · have hand : ¬((ffin.divNat.divNat = ffin'.divNat.divNat ∧
                    ffin.divNat.modNat = ffin'.divNat.modNat) ∧
                    ffin.modNat = ffin'.modNat) := by
      rw [and_assoc]; exact key.not.mpr hffin
    simp [hffin, hand]

/-- Core abstract 5-block commutation: A in slot 2 and B in slot 4
    of a 5-factor kron tensor structure commute. Both products reduce
    to `(((Iₙ a ⊗ A) ⊗ Iₙ mid) ⊗ B) ⊗ Iₙ c` via `mul_kronecker_mul` ×8. -/
private theorem kron_5block_disjoint_comm_aux (a mid c : Nat)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    ((((Iₙ a ⊗ₖ A) ⊗ₖ Iₙ mid) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ c)
       * ((((Iₙ a ⊗ₖ Iₙ 2) ⊗ₖ Iₙ mid) ⊗ₖ B) ⊗ₖ Iₙ c)
    = ((((Iₙ a ⊗ₖ Iₙ 2) ⊗ₖ Iₙ mid) ⊗ₖ B) ⊗ₖ Iₙ c)
       * ((((Iₙ a ⊗ₖ A) ⊗ₖ Iₙ mid) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ c) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  unfold Iₙ; simp

private theorem reindex_kron_prodCongr_aux {α α' β β' : Type*} [Fintype α] [Fintype β]
    (e₁ : α ≃ α') (e₂ : β ≃ β')
    (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    Matrix.reindex (Equiv.prodCongr e₁ e₂) (Equiv.prodCongr e₁ e₂) (A ⊗ₖ B)
      = Matrix.reindex e₁ e₁ A ⊗ₖ Matrix.reindex e₂ e₂ B := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]

private theorem cast_inner_Iₙ_aux {α : Type*} [Fintype α]
    (X : Matrix α α ℂ) (K M : Nat) (h : K = M) :
    Matrix.reindex (Equiv.prodCongr (Equiv.refl α) (Fin.castOrderIso h).toEquiv)
                    (Equiv.prodCongr (Equiv.refl α) (Fin.castOrderIso h).toEquiv)
                    (X ⊗ₖ Iₙ K)
      = X ⊗ₖ Iₙ M := by
  subst h; rw [reindex_kron_prodCongr_aux]; simp [Matrix.reindex_apply, Iₙ]

private theorem cast_outer_Iₙ_aux {β : Type*} [Fintype β]
    (X : Matrix β β ℂ) (K M : Nat) (h : K = M) :
    Matrix.reindex (Equiv.prodCongr (Fin.castOrderIso h).toEquiv (Equiv.refl β))
                    (Equiv.prodCongr (Fin.castOrderIso h).toEquiv (Equiv.refl β))
                    (Iₙ K ⊗ₖ X)
      = Iₙ M ⊗ₖ X := by
  subst h; rw [reindex_kron_prodCongr_aux]; simp [Matrix.reindex_apply, Iₙ]

private theorem reindex_trans_eq_aux {α β γ : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β ≃ γ) (M : Matrix α α ℂ) :
    Matrix.reindex (e.trans f) (e.trans f) M
      = Matrix.reindex f f (Matrix.reindex e e M) := by
  ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Combined bridge: collapsing the right 3 blocks of 5block_A (with Iₙ cast)
    yields the 3-block form `(Iₙ(2^m) ⊗ A) ⊗ Iₙ(2^(dim-m-1))`. -/
private theorem combined_bridge_m_aux (dim m n : Nat) (hmn : m < n) (hn : n < dim)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.reindex
        ((bridge_m_5to3 (2^m) (2^(n-m-1)) (2^(dim-n-1))).trans
          (Equiv.prodCongr (Equiv.refl _)
            (Fin.castOrderIso (nat_inner_m_of_lt dim m n hmn hn)).toEquiv))
        ((bridge_m_5to3 (2^m) (2^(n-m-1)) (2^(dim-n-1))).trans
          (Equiv.prodCongr (Equiv.refl _)
            (Fin.castOrderIso (nat_inner_m_of_lt dim m n hmn hn)).toEquiv))
        ((((Iₙ (2^m) ⊗ₖ A) ⊗ₖ Iₙ (2^(n-m-1))) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ (2^(dim-n-1)))
      = (Iₙ (2^m) ⊗ₖ A) ⊗ₖ Iₙ (2^(dim-m-1)) := by
  rw [reindex_trans_eq_aux, bridge_m_5to3_matrix]
  exact cast_inner_Iₙ_aux _ _ _ _

/-- Combined bridge: collapsing the left 3 blocks of 5block_B (with Iₙ cast)
    yields the 3-block form `(Iₙ(2^n) ⊗ B) ⊗ Iₙ(2^(dim-n-1))`. -/
private theorem combined_bridge_n_aux (dim m n : Nat) (hmn : m < n) (hn : n < dim)
    (B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.reindex
        ((bridge_n_5to3 (2^m) (2^(n-m-1)) (2^(dim-n-1))).trans
          (Equiv.prodCongr (Equiv.prodCongr
            (Fin.castOrderIso (nat_inner_n_of_lt m n hmn)).toEquiv (Equiv.refl _))
            (Equiv.refl _)))
        ((bridge_n_5to3 (2^m) (2^(n-m-1)) (2^(dim-n-1))).trans
          (Equiv.prodCongr (Equiv.prodCongr
            (Fin.castOrderIso (nat_inner_n_of_lt m n hmn)).toEquiv (Equiv.refl _))
            (Equiv.refl _)))
        ((((Iₙ (2^m) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ (2^(n-m-1))) ⊗ₖ B) ⊗ₖ Iₙ (2^(dim-n-1)))
      = (Iₙ (2^n) ⊗ₖ B) ⊗ₖ Iₙ (2^(dim-n-1)) := by
  rw [reindex_trans_eq_aux, bridge_n_5to3_matrix, reindex_kron_prodCongr_aux,
      cast_outer_Iₙ_aux]
  simp [Matrix.reindex_apply]

/-- The unified reindex via the pad_u m direction (combining right 3 blocks). -/
private noncomputable def E_m_unified (dim m n : Nat) (hmn : m < n) (hn : n < dim) :
    ((((Fin (2^m) × Fin 2) × Fin (2^(n-m-1))) × Fin 2) × Fin (2^(dim-n-1)))
      ≃ Fin (2^dim) :=
  ((bridge_m_5to3 (2^m) (2^(n-m-1)) (2^(dim-n-1))).trans
      (Equiv.prodCongr (Equiv.refl _)
        (Fin.castOrderIso (nat_inner_m_of_lt dim m n hmn hn)).toEquiv)).trans
    (((finProdFinEquiv.prodCongr (Equiv.refl _)).trans
        (finProdFinEquiv : Fin (2^m * 2) × Fin (2^(dim-m-1)) ≃ Fin (2^m * 2 * 2^(dim-m-1)))).trans
      (Fin.castOrderIso (two_pow_split dim m (lt_trans hmn hn))).toEquiv)

/-- The unified reindex via the pad_u n direction (combining left 3 blocks). -/
private noncomputable def E_n_unified (dim m n : Nat) (hmn : m < n) (hn : n < dim) :
    ((((Fin (2^m) × Fin 2) × Fin (2^(n-m-1))) × Fin 2) × Fin (2^(dim-n-1)))
      ≃ Fin (2^dim) :=
  ((bridge_n_5to3 (2^m) (2^(n-m-1)) (2^(dim-n-1))).trans
      (Equiv.prodCongr (Equiv.prodCongr
        (Fin.castOrderIso (nat_inner_n_of_lt m n hmn)).toEquiv (Equiv.refl _))
        (Equiv.refl _))).trans
    (((finProdFinEquiv.prodCongr (Equiv.refl _)).trans
        (finProdFinEquiv : Fin (2^n * 2) × Fin (2^(dim-n-1)) ≃ Fin (2^n * 2 * 2^(dim-n-1)))).trans
      (Fin.castOrderIso (two_pow_split dim n hn)).toEquiv)

/-- The two unified reindexes are equal as Equivs (proven by Equiv.ext +
    Fin.ext + Nat exponent identity `2^(dim-m-1) = 2^(dim-n-1) · 2^(n-m-1) · 2`). -/
private theorem E_m_eq_E_n_unified (dim m n : Nat) (hmn : m < n) (hn : n < dim) :
    E_m_unified dim m n hmn hn = E_n_unified dim m n hmn hn := by
  ext ⟨⟨⟨⟨xa, x2m⟩, xc⟩, x2n⟩, xe⟩
  simp [E_m_unified, E_n_unified, bridge_m_5to3, bridge_n_5to3, finProdFinEquiv,
        Fin.castOrderIso, Equiv.prodAssoc]
  have key : (2 ^ (dim - m - 1) : Nat) = 2 ^ (dim - n - 1) * 2 ^ (n - m - 1) * 2 := by
    rw [show (2 ^ (dim - n - 1) * 2 ^ (n - m - 1) * 2 : Nat)
          = 2 ^ ((dim - n - 1) + (n - m - 1) + 1) from by
          rw [show ((dim - n - 1) + (n - m - 1) + 1 : Nat)
              = ((dim - n - 1) + ((n - m - 1) + 1)) from by ring,
              pow_add, pow_succ]; ring]
    congr 1; omega
  rw [key]; ring

private theorem pad_u_m_via_E_unified (dim m n : Nat) (hmn : m < n) (hn : n < dim)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u dim m A = Matrix.reindex (E_m_unified dim m n hmn hn) (E_m_unified dim m n hmn hn)
        ((((Iₙ (2^m) ⊗ₖ A) ⊗ₖ Iₙ (2^(n-m-1))) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ (2^(dim-n-1))) := by
  have hm : m < dim := lt_trans hmn hn
  unfold pad_u E_m_unified
  rw [dif_pos hm]
  dsimp only  -- reduce `let` bindings to flat form
  conv_rhs => rw [reindex_trans_eq_aux]
  congr 1
  exact (combined_bridge_m_aux dim m n hmn hn A).symm

private theorem pad_u_n_via_E_unified (dim m n : Nat) (hmn : m < n) (hn : n < dim)
    (B : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u dim n B = Matrix.reindex (E_n_unified dim m n hmn hn) (E_n_unified dim m n hmn hn)
        ((((Iₙ (2^m) ⊗ₖ Iₙ 2) ⊗ₖ Iₙ (2^(n-m-1))) ⊗ₖ B) ⊗ₖ Iₙ (2^(dim-n-1))) := by
  unfold pad_u E_n_unified
  rw [dif_pos hn]
  dsimp only  -- reduce `let` bindings to flat form
  conv_rhs => rw [reindex_trans_eq_aux]
  congr 1
  exact (combined_bridge_n_aux dim m n hmn hn B).symm

/-- The `m < n < dim` case of `pad_u_disjoint_comm`. -/
private theorem pad_u_disjoint_comm_lt (dim m n : Nat)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hmn : m < n) (hn : n < dim) :
    pad_u dim m A * pad_u dim n B = pad_u dim n B * pad_u dim m A := by
  rw [pad_u_m_via_E_unified dim m n hmn hn A,
      pad_u_n_via_E_unified dim m n hmn hn B,
      E_m_eq_E_n_unified dim m n hmn hn]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv _ _ _ (E_n_unified dim m n hmn hn).symm _,
      Matrix.submatrix_mul_equiv _ _ _ (E_n_unified dim m n hmn hn).symm _,
      kron_5block_disjoint_comm_aux]

-- SQIR/QuantumLib/Pad.v analog: `pad_A_B_commutes`.
/-- Disjoint single-qubit `pad_u`'s commute under matrix multiplication
    (closed 2026-05-23 via the 5-block reindex strategy). For `m ≠ n`,
    WLOG `m < n`; both pad_u's factor through the same unified 5-block
    reindex `E_5 : T_5 ≃ Fin(2^dim)`, where the 5-block matrices commute
    via `Matrix.mul_kronecker_mul` ×4 + identity collapses, and the
    commutation lifts through `Matrix.submatrix_mul_equiv`. The unified
    `E_5` is reached via two different bridge paths (combining right 3
    blocks for pad_u m, left 3 blocks for pad_u n) that yield equal Equivs
    by `Equiv.ext` + the Nat identity `2^(dim-m-1) = 2^(dim-n-1)·2^(n-m-1)·2`. -/
theorem pad_u_disjoint_comm (dim m n : Nat) (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hm : m < dim) (hn : n < dim) (hmn : m ≠ n) :
    pad_u dim m A * pad_u dim n B = pad_u dim n B * pad_u dim m A := by
  rcases Nat.lt_or_gt_of_ne hmn with hlt | hgt
  · exact pad_u_disjoint_comm_lt dim m n A B hlt hn
  · exact (pad_u_disjoint_comm_lt dim n m B A hgt hm).symm

/-- Disjoint `pad_u`'s commute (totally unconstrained version: handles
    out-of-range qubits via the `pad_u_ill_typed` zero collapse). -/
theorem pad_u_disjoint_comm' (dim m n : Nat) (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hmn : m ≠ n) :
    pad_u dim m A * pad_u dim n B = pad_u dim n B * pad_u dim m A := by
  by_cases hm : m < dim
  · by_cases hn : n < dim
    · exact pad_u_disjoint_comm dim m n A B hm hn hmn
    · rw [pad_u_ill_typed _ (Nat.le_of_not_lt hn),
          Matrix.zero_mul, Matrix.mul_zero]
  · rw [pad_u_ill_typed _ (Nat.le_of_not_lt hm),
        Matrix.zero_mul, Matrix.mul_zero]

/-- A `pad_u` and a `pad_ctrl` on pairwise-disjoint qubits commute.
    Derived from `pad_u_disjoint_comm'` by unfolding `pad_ctrl`
    (`= pad_u m proj0 + pad_u m proj1 * pad_u n M`) and propagating
    the commutation through the projector decomposition. -/
theorem pad_u_pad_ctrl_disjoint_comm (dim q m n : Nat)
    (U M : Matrix (Fin 2) (Fin 2) ℂ)
    (hq_m : q ≠ m) (hq_n : q ≠ n) :
    pad_u dim q U * pad_ctrl dim m n M
      = pad_ctrl dim m n M * pad_u dim q U := by
  unfold pad_ctrl
  -- pad_u q U * (P0_m + P1_m * M_n) = pad_u q U * P0_m + pad_u q U * P1_m * M_n
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  · -- pad_u q U * pad_u m proj0 = pad_u m proj0 * pad_u q U
    exact pad_u_disjoint_comm' dim q m U proj0 hq_m
  · -- pad_u q U * (pad_u m proj1 * pad_u n M)
    --   = (pad_u m proj1 * pad_u n M) * pad_u q U
    rw [← Matrix.mul_assoc, pad_u_disjoint_comm' dim q m U proj1 hq_m,
        Matrix.mul_assoc, pad_u_disjoint_comm' dim q n U M hq_n,
        ← Matrix.mul_assoc]

/-- Two `pad_ctrl`'s on four pairwise-disjoint qubits commute.
    Same derivation chain as `pad_u_pad_ctrl_disjoint_comm`. -/
theorem pad_ctrl_disjoint_comm (dim m n m' n' : Nat)
    (M M' : Matrix (Fin 2) (Fin 2) ℂ)
    (hmm : m ≠ m') (hmn : m ≠ n') (hnm : n ≠ m') (hnn : n ≠ n') :
    pad_ctrl dim m n M * pad_ctrl dim m' n' M'
      = pad_ctrl dim m' n' M' * pad_ctrl dim m n M := by
  unfold pad_ctrl
  -- Expand both products fully via distributive laws.
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  -- Each of the four expanded LHS terms commutes with the matching RHS
  -- term via pad_u_disjoint_comm'; addition is commutative so `abel`
  -- handles the reordering.
  have h1 : pad_u dim m proj0 * pad_u dim m' proj0
              = pad_u dim m' proj0 * pad_u dim m proj0 :=
    pad_u_disjoint_comm' dim m m' proj0 proj0 hmm
  have h2 : pad_u dim m proj1 * pad_u dim n M * pad_u dim m' proj0
              = pad_u dim m' proj0 * (pad_u dim m proj1 * pad_u dim n M) := by
    rw [Matrix.mul_assoc, pad_u_disjoint_comm' dim n m' M proj0 hnm,
        ← Matrix.mul_assoc, pad_u_disjoint_comm' dim m m' proj1 proj0 hmm,
        Matrix.mul_assoc]
  have h3 : pad_u dim m proj0 * (pad_u dim m' proj1 * pad_u dim n' M')
              = pad_u dim m' proj1 * pad_u dim n' M' * pad_u dim m proj0 := by
    rw [← Matrix.mul_assoc, pad_u_disjoint_comm' dim m m' proj0 proj1 hmm,
        Matrix.mul_assoc, pad_u_disjoint_comm' dim m n' proj0 M' hmn,
        ← Matrix.mul_assoc]
  have h4 : pad_u dim m proj1 * pad_u dim n M
              * (pad_u dim m' proj1 * pad_u dim n' M')
              = pad_u dim m' proj1 * pad_u dim n' M'
                  * (pad_u dim m proj1 * pad_u dim n M) := by
    -- 4-term reordering via 4 pairwise pad_u commutations (P1m↔P1m',
    -- P1m↔Mn', Mn↔P1m', Mn↔Mn').  Calc chain over fully-left-assoc
    -- form `A · B · C · D` lets each commute be a single rewrite.
    calc pad_u dim m proj1 * pad_u dim n M
              * (pad_u dim m' proj1 * pad_u dim n' M')
        = pad_u dim m proj1 * pad_u dim n M
            * pad_u dim m' proj1 * pad_u dim n' M' := by
          rw [Matrix.mul_assoc (pad_u dim m proj1 * pad_u dim n M)]
      _ = pad_u dim m proj1 * (pad_u dim n M * pad_u dim m' proj1)
            * pad_u dim n' M' := by
          rw [Matrix.mul_assoc (pad_u dim m proj1)]
      _ = pad_u dim m proj1 * (pad_u dim m' proj1 * pad_u dim n M)
            * pad_u dim n' M' := by
          rw [pad_u_disjoint_comm' dim n m' M proj1 hnm]
      _ = pad_u dim m proj1 * pad_u dim m' proj1 * pad_u dim n M
            * pad_u dim n' M' := by
          rw [← Matrix.mul_assoc (pad_u dim m proj1)]
      _ = pad_u dim m' proj1 * pad_u dim m proj1 * pad_u dim n M
            * pad_u dim n' M' := by
          rw [pad_u_disjoint_comm' dim m m' proj1 proj1 hmm]
      _ = pad_u dim m' proj1 * pad_u dim m proj1
            * (pad_u dim n M * pad_u dim n' M') := by
          rw [Matrix.mul_assoc (pad_u dim m' proj1 * pad_u dim m proj1)]
      _ = pad_u dim m' proj1 * pad_u dim m proj1
            * (pad_u dim n' M' * pad_u dim n M) := by
          rw [pad_u_disjoint_comm' dim n n' M M' hnn]
      _ = pad_u dim m' proj1 * pad_u dim m proj1
            * pad_u dim n' M' * pad_u dim n M := by
          rw [← Matrix.mul_assoc (pad_u dim m' proj1 * pad_u dim m proj1)]
      _ = pad_u dim m' proj1 * (pad_u dim m proj1 * pad_u dim n' M')
            * pad_u dim n M := by
          rw [Matrix.mul_assoc (pad_u dim m' proj1)]
      _ = pad_u dim m' proj1 * (pad_u dim n' M' * pad_u dim m proj1)
            * pad_u dim n M := by
          rw [pad_u_disjoint_comm' dim m n' proj1 M' hmn]
      _ = pad_u dim m' proj1 * pad_u dim n' M' * pad_u dim m proj1
            * pad_u dim n M := by
          rw [← Matrix.mul_assoc (pad_u dim m' proj1)]
      _ = pad_u dim m' proj1 * pad_u dim n' M'
            * (pad_u dim m proj1 * pad_u dim n M) := by
          rw [Matrix.mul_assoc (pad_u dim m' proj1 * pad_u dim n' M')]
  rw [h1, h2, h3, h4]
  abel

/-! ## Per-base-gate semantic -/

/-- The matrix corresponding to a base 1-qubit unitary applied to qubit `n`. -/
noncomputable def ueval_r (dim n : Nat) (U : BaseUnitary 1) : Square dim :=
  match U with
  | BaseUnitary.R θ ϕ lam => pad_u dim n (rotation θ ϕ lam)

/-- The matrix corresponding to CNOT with control `m`, target `n`. -/
noncomputable def ueval_cnot (dim m n : Nat) : Square dim :=
  pad_ctrl dim m n σx

/-! ## Unitary semantics — the headline function -/

/-- Denote a `BaseUCom dim` as its 2^dim × 2^dim complex matrix.
    Mirrors SQIR's `uc_eval` (UnitarySem.v line 24). -/
noncomputable def uc_eval {dim : Nat} : BaseUCom dim → Square dim
  | UCom.seq c₁ c₂      => uc_eval c₂ * uc_eval c₁
  | UCom.app1 U n       => ueval_r dim n U
  | UCom.app2 _ m n     => ueval_cnot dim m n
  | UCom.app3 _ _ _ _   => 0    -- no 3-qubit primitives in BaseUnitary

/-! ## Equivalence -/

/-- Two unitary circuits are equivalent iff their matrix semantics agree.
    We avoid `≡` because it collides with `Nat.ModEq` notation; use the
    function name `UCom.equiv` directly, or the local `≅` alias below. -/
def UCom.equiv {dim : Nat} (c₁ c₂ : BaseUCom dim) : Prop :=
  uc_eval c₁ = uc_eval c₂

scoped infix:50 " ≅ " => UCom.equiv

/-- Equivalence is reflexive. -/
theorem UCom.equiv_refl {dim : Nat} (c : BaseUCom dim) : UCom.equiv c c := rfl

/-- Equivalence is symmetric. -/
theorem UCom.equiv_symm {dim : Nat} {c₁ c₂ : BaseUCom dim} :
    UCom.equiv c₁ c₂ → UCom.equiv c₂ c₁ := fun h => h.symm

/-- Equivalence is transitive. -/
theorem UCom.equiv_trans {dim : Nat} {c₁ c₂ c₃ : BaseUCom dim} :
    UCom.equiv c₁ c₂ → UCom.equiv c₂ c₃ → UCom.equiv c₁ c₃ :=
  fun h₁₂ h₂₃ => h₁₂.trans h₂₃

/-- Sequential composition is associative.
    The `uc_eval` of `seq c₁ c₂` is `uc_eval c₂ * uc_eval c₁` (right-to-left
    matrix order), so this reduces to associativity of matrix multiplication. -/
theorem useq_assoc {dim : Nat} (c₁ c₂ c₃ : BaseUCom dim) :
    UCom.equiv (UCom.seq (UCom.seq c₁ c₂) c₃) (UCom.seq c₁ (UCom.seq c₂ c₃)) := by
  show uc_eval c₃ * (uc_eval c₂ * uc_eval c₁)
        = (uc_eval c₃ * uc_eval c₂) * uc_eval c₁
  exact (Matrix.mul_assoc _ _ _).symm

/-- `useq` left-associativity (reverse direction): `c₁;(c₂;c₃) ≡ (c₁;c₂);c₃`.
    Direct corollary of `useq_assoc` via `UCom.equiv_symm`. -/
theorem useq_assoc_l {dim : Nat} (c₁ c₂ c₃ : BaseUCom dim) :
    UCom.equiv (UCom.seq c₁ (UCom.seq c₂ c₃)) (UCom.seq (UCom.seq c₁ c₂) c₃) :=
  UCom.equiv_symm (useq_assoc c₁ c₂ c₃)

/-! ## Circuit-equivalence theorems (translation of SQIR Equivalences.v)

    All proofs depend on `pad_u_mul_pad_u` (currently sorried). Once that
    helper is filled, these become unconditionally true. -/

open BaseUCom in
/-- `uc_eval (X q) = 0` when q is out of dim range. SQIR `X_ill_typed`. -/
theorem X_ill_typed {dim q : Nat} (h : dim ≤ q) :
    uc_eval (X q : BaseUCom dim) = 0 :=
  pad_u_ill_typed (rotation Real.pi 0 Real.pi) h

open BaseUCom in
/-- `uc_eval (Y q) = 0` when q is out of dim range. SQIR `Y_ill_typed`. -/
theorem Y_ill_typed {dim q : Nat} (h : dim ≤ q) :
    uc_eval (Y q : BaseUCom dim) = 0 :=
  pad_u_ill_typed (rotation Real.pi (Real.pi/2) (Real.pi/2)) h

open BaseUCom in
/-- `uc_eval (Z q) = 0` when q is out of dim range. SQIR `Z_ill_typed`. -/
theorem Z_ill_typed {dim q : Nat} (h : dim ≤ q) :
    uc_eval (Z q : BaseUCom dim) = 0 :=
  pad_u_ill_typed (rotation 0 0 Real.pi) h

open BaseUCom in
/-- `uc_eval (H q) = 0` when q is out of dim range. SQIR `H_ill_typed`. -/
theorem H_ill_typed {dim q : Nat} (h : dim ≤ q) :
    uc_eval (H q : BaseUCom dim) = 0 :=
  pad_u_ill_typed (rotation (Real.pi/2) 0 Real.pi) h

open BaseUCom in
/-- `uc_eval (T q) = 0` when q is out of dim range. -/
theorem T_ill_typed {dim q : Nat} (h : dim ≤ q) :
    uc_eval (T q : BaseUCom dim) = 0 :=
  pad_u_ill_typed (rotation 0 0 (Real.pi/4)) h

open BaseUCom in
/-- `uc_eval (TDAG q) = 0` when q is out of dim range. -/
theorem TDAG_ill_typed {dim q : Nat} (h : dim ≤ q) :
    uc_eval (TDAG q : BaseUCom dim) = 0 :=
  pad_u_ill_typed (rotation 0 0 (-(Real.pi/4))) h

open BaseUCom in
/-- `uc_eval (S q) = 0` when q is out of dim range. -/
theorem S_ill_typed {dim q : Nat} (h : dim ≤ q) :
    uc_eval (S q : BaseUCom dim) = 0 :=
  pad_u_ill_typed (rotation 0 0 (Real.pi/2)) h

open BaseUCom in
/-- `uc_eval (SDAG q) = 0` when q is out of dim range. -/
theorem SDAG_ill_typed {dim q : Nat} (h : dim ≤ q) :
    uc_eval (SDAG q : BaseUCom dim) = 0 :=
  pad_u_ill_typed (rotation 0 0 (-(Real.pi/2))) h

open BaseUCom in
/-- `uc_eval (ID q) = 0` when q is out of dim range. SQIR `ID_ill_typed`. -/
theorem ID_ill_typed {dim q : Nat} (h : dim ≤ q) :
    uc_eval (ID q : BaseUCom dim) = 0 :=
  pad_u_ill_typed (rotation 0 0 0) h

open BaseUCom in
/-- `uc_eval (Rz θ q) = 0` when q is out of dim range (parametric).
    SQIR/SQIR/UnitaryOps.v: `Rz_ill_typed`. -/
theorem Rz_ill_typed {dim q : Nat} (θ : ℝ) (h : dim ≤ q) :
    uc_eval (Rz θ q : BaseUCom dim) = 0 :=
  pad_u_ill_typed (rotation 0 0 θ) h

open BaseUCom in
/-- `uc_eval (CNOT m n) = 0` when control qubit m is out of dim range.
    SQIR/SQIR/UnitaryOps.v: `CNOT_ill_typed` (control branch only — the
    target-oob and same-qubit branches behave differently in our model
    and need separate lemmas). -/
theorem CNOT_ill_typed_control {dim m n : Nat} (h : dim ≤ m) :
    uc_eval (CNOT m n : BaseUCom dim) = 0 := by
  show ueval_cnot dim m n = 0
  unfold ueval_cnot pad_ctrl
  rw [pad_u_ill_typed proj0 h, pad_u_ill_typed proj1 h,
      Matrix.zero_mul, add_zero]

open BaseUCom in
/-- `uc_eval (SWAP m n) = 0` when m is out of dim range. SWAP unfolds to
    a 3-CNOT chain, all of which have m as control somewhere. -/
theorem SWAP_ill_typed_left {dim m n : Nat} (h : dim ≤ m) :
    uc_eval (SWAP m n : BaseUCom dim) = 0 := by
  unfold SWAP
  show (uc_eval (CNOT m n : BaseUCom dim) * uc_eval (CNOT n m : BaseUCom dim))
        * uc_eval (CNOT m n : BaseUCom dim) = 0
  rw [CNOT_ill_typed_control h, Matrix.zero_mul, Matrix.zero_mul]

open BaseUCom in
/-- `uc_eval (SWAP m n) = 0` when n is out of dim range. The middle CNOT
    (CNOT n m) has n as control and vanishes by CNOT_ill_typed_control. -/
theorem SWAP_ill_typed_right {dim m n : Nat} (h : dim ≤ n) :
    uc_eval (SWAP m n : BaseUCom dim) = 0 := by
  unfold SWAP
  show (uc_eval (CNOT m n : BaseUCom dim) * uc_eval (CNOT n m : BaseUCom dim))
        * uc_eval (CNOT m n : BaseUCom dim) = 0
  rw [CNOT_ill_typed_control h, Matrix.mul_zero, Matrix.zero_mul]

open BaseUCom in
/-- `X q ; X q ≡ ID q` — the X gate is its own inverse.
    SQIR/Equivalences.v line 68. -/
theorem X_X_id {dim : Nat} (q : Nat) :
    UCom.equiv (UCom.seq (X q : BaseUCom dim) (X q)) (ID q) := by
  show uc_eval (X q : BaseUCom dim) * uc_eval (X q) = uc_eval (ID q : BaseUCom dim)
  show pad_u dim q (rotation Real.pi 0 Real.pi) * pad_u dim q (rotation Real.pi 0 Real.pi)
        = pad_u dim q (rotation 0 0 0)
  rw [pad_u_mul_pad_u, rotation_X, rotation_I, σx_mul_σx]

open BaseUCom in
/-- `Z q ; Z q ≡ ID q` — the Z gate is its own inverse.
    Analogous to SQIR's `X_X_id`. -/
theorem Z_Z_id {dim : Nat} (q : Nat) :
    UCom.equiv (UCom.seq (Z q : BaseUCom dim) (Z q)) (ID q) := by
  show pad_u dim q (rotation 0 0 Real.pi) * pad_u dim q (rotation 0 0 Real.pi)
        = pad_u dim q (rotation 0 0 0)
  rw [pad_u_mul_pad_u, rotation_Z, rotation_I, σz_mul_σz]

open BaseUCom in
/-- `Y q ; Y q ≡ ID q`. -/
theorem Y_Y_id {dim : Nat} (q : Nat) :
    UCom.equiv (UCom.seq (Y q : BaseUCom dim) (Y q)) (ID q) := by
  show pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))
        * pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))
        = pad_u dim q (rotation 0 0 0)
  rw [pad_u_mul_pad_u, rotation_Y, rotation_I, σy_mul_σy]

open BaseUCom in
/-- `H q ; H q ≡ ID q` — the Hadamard gate is its own inverse.
    -- SQIR/SQIR/Equivalences.v line 78: H_H_id. -/
theorem H_H_id {dim : Nat} (q : Nat) :
    UCom.equiv (UCom.seq (H q : BaseUCom dim) (H q)) (ID q) := by
  show pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
        * pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
        = pad_u dim q (rotation 0 0 0)
  rw [pad_u_mul_pad_u, rotation_H, rotation_I, hMatrix_mul_hMatrix]

open BaseUCom in
/-- `H q ; Z q ≡ X q ; H q` — the Hadamard interchange identity.
    -- SQIR/SQIR/Equivalences.v line 164: H_comm_Z. -/
theorem H_comm_Z {dim : Nat} (q : Nat) :
    UCom.equiv (UCom.seq (H q : BaseUCom dim) (Z q))
               (UCom.seq (X q) (H q)) := by
  show pad_u dim q (rotation 0 0 Real.pi)
        * pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
       = pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
         * pad_u dim q (rotation Real.pi 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_H, rotation_Z, rotation_X,
      σz_mul_hMatrix]

open BaseUCom in
/-- `H q ; X q ≡ Z q ; H q` — the dual Hadamard interchange identity. -/
theorem H_comm_X {dim : Nat} (q : Nat) :
    UCom.equiv (UCom.seq (H q : BaseUCom dim) (X q))
               (UCom.seq (Z q) (H q)) := by
  show pad_u dim q (rotation Real.pi 0 Real.pi)
        * pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
       = pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
         * pad_u dim q (rotation 0 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_H, rotation_X, rotation_Z,
      σx_mul_hMatrix]

/-- Helper: composition of `rotation 0 0 θ` and `rotation 0 0 θ'`.
    Uses `Complex.exp_add`: `exp(iθ) · exp(iθ') = exp(i(θ+θ'))`. -/
theorem rotation_Rz_compose (θ θ' : ℝ) :
    rotation 0 0 θ * rotation 0 0 θ' = rotation 0 0 (θ + θ') := by
  unfold rotation
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add] <;>
    ring_nf

/-- Z-rotation by θ followed by Z-rotation by -θ is the identity matrix.
    Direct corollary of `rotation_Rz_compose` + `rotation_I`. -/
theorem rotation_Rz_neg_inv (θ : ℝ) :
    rotation 0 0 θ * rotation 0 0 (-θ) = σi := by
  rw [rotation_Rz_compose, add_neg_cancel, rotation_I]

/-- Z-rotation by -θ followed by Z-rotation by θ is the identity matrix.
    Symmetric companion to `rotation_Rz_neg_inv`. -/
theorem rotation_Rz_neg_inv_l (θ : ℝ) :
    rotation 0 0 (-θ) * rotation 0 0 θ = σi := by
  rw [rotation_Rz_compose, neg_add_cancel, rotation_I]

/-- The X-axis rotation by 0 is the identity matrix.
    `Rx 0 = R 0 (-π/2) (π/2)`; with cos(0) = 1, sin(0) = 0, the off-diagonal
    terms vanish and the diagonal is (1, exp(0)) = (1, 1). Same shape as
    `rotation_I` but with the Rx angle convention. -/
theorem rotation_Rx_zero : rotation 0 (-(Real.pi/2)) (Real.pi/2) = σi := by
  unfold rotation σi
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Z-rotation raised to the k-th power equals a Z-rotation by k·θ.
    Generalizes `rotation_Rz_compose` to arbitrary powers via induction. -/
theorem rotation_Rz_pow (θ : ℝ) (k : Nat) :
    (rotation 0 0 θ)^k = rotation 0 0 (k * θ) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, ← σi_eq_one, ← rotation_I]
  | succ k ih =>
    rw [pow_succ, ih, rotation_Rz_compose]
    congr 1
    push_cast
    ring


/-- Any Z-rotation commutes with σz: `Rz(θ) · σz = σz · Rz(θ)`. Both
    matrices are diagonal so this is the trivial commutation of two
    diagonal 2×2 matrices. Subsumes T, T†, S, S† commutation with σz. -/
theorem rotation_Rz_commutes_σz (θ : ℝ) :
    rotation 0 0 θ * σz = σz * rotation 0 0 θ := by
  unfold rotation σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Z-rotations commute with each other. Subsumes T·S = S·T, T·T† = T†·T,
    S·S† = S†·S, etc. as instances. Follows from `rotation_Rz_compose` and
    `add_comm`. -/
theorem rotation_Rz_commutes (θ θ' : ℝ) :
    rotation 0 0 θ * rotation 0 0 θ' = rotation 0 0 θ' * rotation 0 0 θ := by
  rw [rotation_Rz_compose, rotation_Rz_compose, add_comm]

open BaseUCom in
/-- `Rz θ q ; Rz θ' q ≡ Rz (θ + θ') q` — Z-rotations add their angles.
    SQIR/Equivalences.v line 88. -/
theorem Rz_Rz_add {dim : Nat} (q : Nat) (θ θ' : ℝ) :
    UCom.equiv (UCom.seq (Rz θ q : BaseUCom dim) (Rz θ' q)) (Rz (θ + θ') q) := by
  show pad_u dim q (rotation 0 0 θ') * pad_u dim q (rotation 0 0 θ)
        = pad_u dim q (rotation 0 0 (θ + θ'))
  rw [pad_u_mul_pad_u, rotation_Rz_compose, add_comm]

open BaseUCom in
/-- `Rz 0 q ≡ ID q` — zero rotation is identity. -/
theorem Rz_0_id {dim : Nat} (q : Nat) :
    UCom.equiv (Rz 0 q : BaseUCom dim) (ID q) := by
  show pad_u dim q (rotation 0 0 0) = pad_u dim q (rotation 0 0 0)
  rfl

open BaseUCom in
/-- `T q ; TDAG q ≡ ID q` — T is inverted by T†.
    T = Rz(π/4), TDAG = Rz(-π/4), product = Rz(0) = ID. -/
theorem T_TDAG_id {dim : Nat} (q : Nat) :
    UCom.equiv (UCom.seq (T q : BaseUCom dim) (TDAG q)) (ID q) := by
  show pad_u dim q (rotation 0 0 (-(Real.pi / 4))) * pad_u dim q (rotation 0 0 (Real.pi / 4))
        = pad_u dim q (rotation 0 0 0)
  rw [pad_u_mul_pad_u, rotation_Rz_compose]
  congr 2
  ring

open BaseUCom in
/-- `TDAG q ; T q ≡ ID q` — symmetric companion. -/
theorem TDAG_T_id {dim : Nat} (q : Nat) :
    UCom.equiv (UCom.seq (TDAG q : BaseUCom dim) (T q)) (ID q) := by
  show pad_u dim q (rotation 0 0 (Real.pi / 4)) * pad_u dim q (rotation 0 0 (-(Real.pi / 4)))
        = pad_u dim q (rotation 0 0 0)
  rw [pad_u_mul_pad_u, rotation_Rz_compose]
  congr 2
  ring

open BaseUCom in
/-- `S q ; SDAG q ≡ ID q`. -/
theorem S_SDAG_id {dim : Nat} (q : Nat) :
    UCom.equiv (UCom.seq (S q : BaseUCom dim) (SDAG q)) (ID q) := by
  show pad_u dim q (rotation 0 0 (-(Real.pi / 2))) * pad_u dim q (rotation 0 0 (Real.pi / 2))
        = pad_u dim q (rotation 0 0 0)
  rw [pad_u_mul_pad_u, rotation_Rz_compose]
  congr 2
  ring

open BaseUCom in
/-- `SDAG q ; S q ≡ ID q` — symmetric companion of `S_SDAG_id`. -/
theorem SDAG_S_id {dim : Nat} (q : Nat) :
    UCom.equiv (UCom.seq (SDAG q : BaseUCom dim) (S q)) (ID q) := by
  show pad_u dim q (rotation 0 0 (Real.pi / 2)) * pad_u dim q (rotation 0 0 (-(Real.pi / 2)))
        = pad_u dim q (rotation 0 0 0)
  rw [pad_u_mul_pad_u, rotation_Rz_compose]
  congr 2
  ring

open BaseUCom in
/-- `Rz θ q ; Rz (-θ) q ≡ ID q` — every Z-rotation is invertible by its negation.
    Generalizes `T_TDAG_id` (θ = π/4) and `S_SDAG_id` (θ = π/2). -/
theorem Rz_neg_id {dim : Nat} (q : Nat) (θ : ℝ) :
    UCom.equiv (UCom.seq (Rz θ q : BaseUCom dim) (Rz (-θ) q)) (ID q) := by
  show pad_u dim q (rotation 0 0 (-θ)) * pad_u dim q (rotation 0 0 θ)
        = pad_u dim q (rotation 0 0 0)
  rw [pad_u_mul_pad_u, rotation_Rz_compose]
  congr 2
  ring

open BaseUCom in
/-- `Rz (-θ) q ; Rz θ q ≡ ID q` — reverse direction of `Rz_neg_id`. Direct
    corollary obtained by substituting θ ↦ -θ and folding the double-negation. -/
theorem Rz_neg_id_l {dim : Nat} (q : Nat) (θ : ℝ) :
    UCom.equiv (UCom.seq (Rz (-θ) q : BaseUCom dim) (Rz θ q)) (ID q) := by
  have h := Rz_neg_id (dim := dim) q (-θ)
  rw [neg_neg] at h
  exact h

/-- `rotation 0 0 (2π) = σi`. The 2π Z-rotation is identity (exp(2πi) = 1). -/
theorem rotation_2pi : rotation 0 0 (2 * Real.pi) = σi := by
  unfold rotation σi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [show (2 * (Real.pi : ℂ)) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I from rfl,
          show (Complex.I * (2 * (Real.pi : ℂ))) = 2 * (Real.pi : ℂ) * Complex.I
            from by ring,
          Complex.exp_two_pi_mul_I]

/-- 2π-periodicity of Z-rotations: `rotation 0 0 (θ + 2π) = rotation 0 0 θ`. -/
theorem rotation_Rz_periodic (θ : ℝ) :
    rotation 0 0 (θ + 2 * Real.pi) = rotation 0 0 θ := by
  rw [← rotation_Rz_compose, rotation_2pi, σi_eq_one, Matrix.mul_one]

open BaseUCom in
/-- `Rz (2π) q ≡ ID q` — full 2π rotation is the identity. -/
theorem Rz_2pi_id {dim : Nat} (q : Nat) :
    UCom.equiv (Rz (2 * Real.pi) q : BaseUCom dim) (ID q) := by
  show pad_u dim q (rotation 0 0 (2 * Real.pi)) = pad_u dim q (rotation 0 0 0)
  rw [rotation_2pi, rotation_I]

open BaseUCom in
/-- `Rz (-2π) q ≡ ID q` — full -2π rotation is also the identity (Z-rotations
    are 2π-periodic, so -2π and 0 give equivalent matrices). -/
theorem Rz_neg_2pi_id {dim : Nat} (q : Nat) :
    UCom.equiv (Rz (-(2 * Real.pi)) q : BaseUCom dim) (ID q) := by
  show pad_u dim q (rotation 0 0 (-(2 * Real.pi))) = pad_u dim q (rotation 0 0 0)
  have h := rotation_Rz_periodic (-(2 * Real.pi))
  rw [show -(2 * Real.pi) + 2 * Real.pi = 0 from by ring] at h
  exact congr_arg (pad_u dim q) h.symm


open BaseUCom in
/-- `Rz π q ≡ Z q` — π Z-rotation is the Pauli Z gate. -/
theorem Rz_pi_eq_Z {dim : Nat} (q : Nat) :
    UCom.equiv (Rz Real.pi q : BaseUCom dim) (Z q) := rfl

open BaseUCom in
/-- `Rz (π/2) q ≡ S q` — π/2 Z-rotation is the S gate. -/
theorem Rz_pi_div_two_eq_S {dim : Nat} (q : Nat) :
    UCom.equiv (Rz (Real.pi / 2) q : BaseUCom dim) (S q) := rfl

open BaseUCom in
/-- `Rz (π/4) q ≡ T q` — π/4 Z-rotation is the T gate. -/
theorem Rz_pi_div_four_eq_T {dim : Nat} (q : Nat) :
    UCom.equiv (Rz (Real.pi / 4) q : BaseUCom dim) (T q) := rfl

open BaseUCom in
/-- `Rz (-π/2) q ≡ S† q`. -/
theorem Rz_neg_pi_div_two_eq_SDAG {dim : Nat} (q : Nat) :
    UCom.equiv (Rz (-(Real.pi / 2)) q : BaseUCom dim) (SDAG q) := rfl

open BaseUCom in
/-- `Rz (-π/4) q ≡ T† q`. -/
theorem Rz_neg_pi_div_four_eq_TDAG {dim : Nat} (q : Nat) :
    UCom.equiv (Rz (-(Real.pi / 4)) q : BaseUCom dim) (TDAG q) := rfl

open BaseUCom in
/-- `Rz (θ + 2π) q ≡ Rz θ q` — Z-rotation is 2π-periodic at the circuit level. -/
theorem Rz_periodic {dim : Nat} (q : Nat) (θ : ℝ) :
    UCom.equiv (Rz (θ + 2 * Real.pi) q : BaseUCom dim) (Rz θ q) := by
  show pad_u dim q (rotation 0 0 (θ + 2 * Real.pi)) = pad_u dim q (rotation 0 0 θ)
  rw [rotation_Rz_periodic]

open BaseUCom in
/-- `Rz (4π) q ≡ ID q` — 4π rotation is the identity (since 4π = 2π + 2π).
    Direct corollary of Rz_periodic + Rz_2pi_id. -/
theorem Rz_4pi_id {dim : Nat} (q : Nat) :
    UCom.equiv (Rz (4 * Real.pi) q : BaseUCom dim) (ID q) := by
  have h1 := Rz_periodic (dim := dim) q (2 * Real.pi)
  rw [show (2 * Real.pi + 2 * Real.pi : ℝ) = 4 * Real.pi from by ring] at h1
  exact h1.trans (Rz_2pi_id q)

open BaseUCom in
/-- `Rz (-4π) q ≡ ID q` — symmetric companion to Rz_4pi_id for negative angle. -/
theorem Rz_neg_4pi_id {dim : Nat} (q : Nat) :
    UCom.equiv (Rz (-(4 * Real.pi)) q : BaseUCom dim) (ID q) := by
  have h1 := Rz_periodic (dim := dim) q (-(4 * Real.pi))
  rw [show -(4 * Real.pi) + 2 * Real.pi = -(2 * Real.pi) from by ring] at h1
  exact h1.symm.trans (Rz_neg_2pi_id q)

open BaseUCom in
/-- `Rz (k·2π) q ≡ ID q` for any k : ℕ — parametric generalization of
    Rz_2pi_id (k=1) and Rz_4pi_id (k=2). Proof by induction on k. -/
theorem Rz_2pi_smul_id {dim : Nat} (q : Nat) (k : Nat) :
    UCom.equiv (Rz ((k : ℝ) * (2 * Real.pi)) q : BaseUCom dim) (ID q) := by
  induction k with
  | zero =>
    rw [show ((0 : ℕ) : ℝ) * (2 * Real.pi) = 0 from by push_cast; ring]
    exact Rz_0_id q
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : ℝ) * (2 * Real.pi)
          = ((k : ℕ) : ℝ) * (2 * Real.pi) + 2 * Real.pi from by push_cast; ring]
    exact (Rz_periodic q ((k : ℕ) * (2 * Real.pi))).trans ih

open BaseUCom in
/-- `Rz (-(k·2π)) q ≡ ID q` for any k : ℕ — symmetric companion to
    Rz_2pi_smul_id for negative multiples of 2π. -/
theorem Rz_neg_2pi_smul_id {dim : Nat} (q : Nat) (k : Nat) :
    UCom.equiv (Rz (-((k : ℝ) * (2 * Real.pi))) q : BaseUCom dim) (ID q) := by
  induction k with
  | zero =>
    rw [show -(((0 : ℕ) : ℝ) * (2 * Real.pi)) = 0 from by push_cast; ring]
    exact Rz_0_id q
  | succ k ih =>
    have h := Rz_periodic (dim := dim) q (-(((k + 1 : ℕ) : ℝ) * (2 * Real.pi)))
    rw [show -(((k + 1 : ℕ) : ℝ) * (2 * Real.pi)) + 2 * Real.pi
          = -(((k : ℕ) : ℝ) * (2 * Real.pi)) from by push_cast; ring] at h
    exact h.symm.trans ih

open BaseUCom in
/-- `T q ; T q ≡ S q` — two T gates equal S (since Rz(π/4) twice = Rz(π/2) = S). -/
theorem T_T_eq_S {dim : Nat} (q : Nat) :
    UCom.equiv (UCom.seq (T q : BaseUCom dim) (T q)) (S q) := by
  show pad_u dim q (rotation 0 0 (Real.pi / 4)) * pad_u dim q (rotation 0 0 (Real.pi / 4))
        = pad_u dim q (rotation 0 0 (Real.pi / 2))
  rw [pad_u_mul_pad_u, rotation_Rz_compose]
  congr 2
  ring

open BaseUCom in
/-- `S q ; S q ≡ Z q` — two S gates equal Z (since Rz(π/2) twice = Rz(π) = Z). -/
theorem S_S_eq_Z {dim : Nat} (q : Nat) :
    UCom.equiv (UCom.seq (S q : BaseUCom dim) (S q)) (Z q) := by
  show pad_u dim q (rotation 0 0 (Real.pi / 2)) * pad_u dim q (rotation 0 0 (Real.pi / 2))
        = pad_u dim q (rotation 0 0 Real.pi)
  rw [pad_u_mul_pad_u, rotation_Rz_compose]
  congr 2
  ring

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

/-! ## Pad_ctrl basic identities -/

/-- A controlled-identity gate is the global identity (both qubits valid).
    Whether the control fires or not, applying I has no effect, so the
    sum (proj0 + proj1·I) collapses to (proj0 + proj1) = σi → identity. -/
theorem pad_ctrl_id {dim m n : Nat} (hm : m < dim) (hn : n < dim) :
    pad_ctrl dim m n σi = (1 : Square dim) := by
  unfold pad_ctrl
  rw [pad_u_id hn, Matrix.mul_one, ← pad_u_add,
      proj0_add_proj1_eq_id, pad_u_id hm]

/-- A controlled-zero "gate" is just the projection on the control qubit at
    state |0⟩: when the control fires there's nothing to apply (target term
    vanishes). Mathematically `pad_ctrl _ _ _ 0 = pad_u _ _ proj0`. Useful
    as infrastructure for splitting pad_ctrl proofs additively. -/
theorem pad_ctrl_zero (dim m n : Nat) :
    pad_ctrl dim m n (0 : Matrix (Fin 2) (Fin 2) ℂ) = pad_u dim m proj0 := by
  unfold pad_ctrl
  rw [pad_u_zero, Matrix.mul_zero, add_zero]

/-- Scalar multiplication in the target argument: only the |1⟩ branch
    sees the scaling, since the |0⟩ branch (proj0) doesn't depend on the
    target operator. -/
theorem pad_ctrl_smul (dim m n : Nat) (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_ctrl dim m n (c • A)
      = pad_u dim m proj0 + c • (pad_u dim m proj1 * pad_u dim n A) := by
  unfold pad_ctrl
  rw [pad_u_smul, Matrix.mul_smul]

/-- Negation in the target argument: only the |1⟩ branch flips sign. -/
theorem pad_ctrl_neg (dim m n : Nat) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_ctrl dim m n (-A)
      = pad_u dim m proj0 - pad_u dim m proj1 * pad_u dim n A := by
  unfold pad_ctrl
  rw [pad_u_neg, Matrix.mul_neg, ← sub_eq_add_neg]

/-- Asymmetric additivity in the target: adding a second operator to the
    target produces the original pad_ctrl plus an extra |1⟩-branch term —
    the proj0 contribution doesn't double, since proj0 is target-independent. -/
theorem pad_ctrl_add (dim m n : Nat) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_ctrl dim m n (A + B)
      = pad_ctrl dim m n A + pad_u dim m proj1 * pad_u dim n B := by
  unfold pad_ctrl
  rw [pad_u_add, Matrix.mul_add, ← add_assoc]

/-- Asymmetric subtractivity in the target: subtracting a second operator
    from the target subtracts only an extra |1⟩-branch term. Corollary
    of `pad_ctrl_add` + `pad_u_neg` via `sub_eq_add_neg`. -/
theorem pad_ctrl_sub (dim m n : Nat) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_ctrl dim m n (A - B)
      = pad_ctrl dim m n A - pad_u dim m proj1 * pad_u dim n B := by
  simp only [sub_eq_add_neg]
  rw [pad_ctrl_add, pad_u_neg, Matrix.mul_neg]

/-- Boundary case: when the target qubit is out of dim range, the |1⟩-branch
    term vanishes and pad_ctrl reduces to just the proj0 padding. -/
theorem pad_ctrl_target_oob (dim m n : Nat) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hn : ¬n < dim) :
    pad_ctrl dim m n A = pad_u dim m proj0 := by
  unfold pad_ctrl
  have h : pad_u dim n A = 0 := by unfold pad_u; rw [dif_neg hn]
  rw [h, Matrix.mul_zero, add_zero]

/-- Boundary case: when the control qubit is out of dim range, both
    projector paddings vanish and pad_ctrl is just zero. -/
theorem pad_ctrl_control_oob (dim m n : Nat) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hm : ¬m < dim) :
    pad_ctrl dim m n A = 0 := by
  unfold pad_ctrl
  have h0 : pad_u dim m proj0 = 0 := by unfold pad_u; rw [dif_neg hm]
  have h1 : pad_u dim m proj1 = 0 := by unfold pad_u; rw [dif_neg hm]
  rw [h0, h1, Matrix.zero_mul, add_zero]

/-- Edge case: when control and target are the same qubit, pad_ctrl
    collapses to a single pad_u of the kernel `proj0 + proj1·A`. -/
theorem pad_ctrl_same_qubit (dim n : Nat) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_ctrl dim n n A = pad_u dim n (proj0 + proj1 * A) := by
  unfold pad_ctrl
  rw [pad_u_mul_pad_u, ← pad_u_add]

/-- σx's 3-chain at the padded level equals pad_u σx (cubes back to self). -/
theorem pad_u_σx_pow_three (dim n : Nat) :
    pad_u dim n σx * pad_u dim n σx * pad_u dim n σx = pad_u dim n σx :=
  pad_u_pow_three_eq dim n σx σx σx_pow_three

/-- σy's 3-chain at the padded level equals pad_u σy. -/
theorem pad_u_σy_pow_three (dim n : Nat) :
    pad_u dim n σy * pad_u dim n σy * pad_u dim n σy = pad_u dim n σy :=
  pad_u_pow_three_eq dim n σy σy σy_pow_three

/-- σz's 3-chain at the padded level equals pad_u σz. -/
theorem pad_u_σz_pow_three (dim n : Nat) :
    pad_u dim n σz * pad_u dim n σz * pad_u dim n σz = pad_u dim n σz :=
  pad_u_pow_three_eq dim n σz σz σz_pow_three

/-- Hadamard's 3-chain at the padded level equals pad_u hMatrix. -/
theorem pad_u_hMatrix_pow_three (dim n : Nat) :
    pad_u dim n hMatrix * pad_u dim n hMatrix * pad_u dim n hMatrix = pad_u dim n hMatrix :=
  pad_u_pow_three_eq dim n hMatrix hMatrix hMatrix_pow_three

open BaseUCom in
/-- `ID n ≡ SKIP` for any well-typed `n < dim`.
    SQIR/Equivalences.v line 11. -/
theorem ID_equiv_SKIP {dim : Nat} {n : Nat} (h : n < dim) (h0 : 0 < dim) :
    UCom.equiv (ID n : BaseUCom dim) (SKIP) := by
  show pad_u dim n (rotation 0 0 0) = pad_u dim 0 (rotation 0 0 0)
  rw [rotation_I, pad_u_id h, pad_u_id h0]

open BaseUCom in
/-- `SKIP ; c ≡ c` — left identity. Follows from `pad_u_id` and `Matrix.one_mul`. -/
theorem SKIP_id_l {dim : Nat} (c : BaseUCom dim) (h : 0 < dim) :
    UCom.equiv (UCom.seq (SKIP : BaseUCom dim) c) c := by
  show uc_eval c * uc_eval (SKIP : BaseUCom dim) = uc_eval c
  show uc_eval c * pad_u dim 0 (rotation 0 0 0) = uc_eval c
  rw [rotation_I, pad_u_id h, Matrix.mul_one]

open BaseUCom in
/-- `c ; SKIP ≡ c` — right identity. -/
theorem SKIP_id_r {dim : Nat} (c : BaseUCom dim) (h : 0 < dim) :
    UCom.equiv (UCom.seq c (SKIP : BaseUCom dim)) c := by
  show pad_u dim 0 (rotation 0 0 0) * uc_eval c = uc_eval c
  rw [rotation_I, pad_u_id h, Matrix.one_mul]

/-! ## Sequential composition is congruent w.r.t. equivalence -/

/-- `useq_congruence`: if `c₁ ≡ c₁'` and `c₂ ≡ c₂'`, then `c₁;c₂ ≡ c₁';c₂'`.
    SQIR/UnitarySem.v line 78. -/
theorem useq_congruence {dim : Nat} {c₁ c₁' c₂ c₂' : BaseUCom dim}
    (h₁ : UCom.equiv c₁ c₁') (h₂ : UCom.equiv c₂ c₂') :
    UCom.equiv (UCom.seq c₁ c₂) (UCom.seq c₁' c₂') := by
  show uc_eval c₂ * uc_eval c₁ = uc_eval c₂' * uc_eval c₁'
  rw [show uc_eval c₁ = uc_eval c₁' from h₁,
      show uc_eval c₂ = uc_eval c₂' from h₂]

/-- Left congruence: if `c₂ ≡ c₂'`, then `c₁;c₂ ≡ c₁;c₂'`. -/
theorem useq_congruence_l {dim : Nat} {c₂ c₂' : BaseUCom dim} (c₁ : BaseUCom dim)
    (h₂ : UCom.equiv c₂ c₂') :
    UCom.equiv (UCom.seq c₁ c₂) (UCom.seq c₁ c₂') :=
  useq_congruence (UCom.equiv_refl c₁) h₂

/-- Right congruence: if `c₁ ≡ c₁'`, then `c₁;c₂ ≡ c₁';c₂`. -/
theorem useq_congruence_r {dim : Nat} {c₁ c₁' : BaseUCom dim} (c₂ : BaseUCom dim)
    (h₁ : UCom.equiv c₁ c₁') :
    UCom.equiv (UCom.seq c₁ c₂) (UCom.seq c₁' c₂) :=
  useq_congruence h₁ (UCom.equiv_refl c₂)

/-! ## Roadmap (each is one or more autoresearch ticks)

  Filling in this file's sorries unlocks Shor-correctness work. Priority:

  1. **`pad_u`**: implement via Kronecker products
     `(I ^⊗ n) ⊗ M ⊗ (I ^⊗ (dim - n - 1))`. ~50 lines + `simp` lemmas.
     Reference: `SQIR/QuantumLib/Pad.v` lines ~50-150 in original Coq.

  2. **`pad_ctrl`**: implement via case-split on m < n vs m > n. The
     control on qubit m and target on qubit n is more delicate; SQIR
     uses helper `pad_ctrl1`/`pad_ctrl2` for the two orderings. ~80 lines.

  3. **Single-qubit gate matrix lemmas**: prove
     `rotation_H : rotation (π/2) 0 π = !![1/√2, 1/√2; 1/√2, -1/√2] / √2`
     and similarly for X, Y, Z, T, S. Each is `simp` + `Real.cos_pi_div_two`
     etc. ~5 lines each, ~10 lemmas total.

  4. **Self-inverse properties**: `X · X = I`, `H · H = I`, `T · T = S`,
     `CNOT · CNOT = I`. These are circuit-equivalence lemmas of the form
     `seq (X n) (X n) ≡ ID n`. They follow from (3) once `pad_u` is in place.

  5. **CCX correctness**: prove that the 7-T `CCX` decomposition (defined
     in `QuantumGate.lean`) has the same semantics as the abstract
     Toffoli matrix. This is the single biggest milestone in the early
     framework — it bridges RCIR-level (where CCX is primitive) to
     unitary-level (where it's a long sequence). SQIR proves this in
     `GateDecompositions.v`; ~200 lines.

  6. **QFT and QPE**: build on top of the above. See
     `Framework/QFT.lean` and `Framework/QPE.lean` (not yet created).

  7. **Shor-end-to-end**: the Mt. Everest. Combines (6) with
     `Framework.Gate` (RCIR adders/multipliers) via a "lift" relating the
     two semantic levels. ~years of research-level work in any proof
     assistant.

-/

end FormalRV.Framework
