/- UnitarySem — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Core.UnitarySem.Part1

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker  -- enables `A ⊗ₖ B` notation for Matrix.kronecker

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


end FormalRV.Framework
