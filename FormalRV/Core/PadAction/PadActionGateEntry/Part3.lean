/- PadActionGateEntry — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Core.PadAction.PadActionGateEntry.Part2

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker

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


end FormalRV.Framework
