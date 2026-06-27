/- PadActionGateEntry — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Core.PadAction.PadActionGateEntry.FToVecBridge

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker

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
