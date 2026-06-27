/- PadActionGateEntry — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Core.PadAction.PadActionGateEntry.EntryFormulaAndBasisAction

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker

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


end FormalRV.Framework
