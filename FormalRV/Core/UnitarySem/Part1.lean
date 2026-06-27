/- UnitarySem — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
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


end FormalRV.Framework
