import FormalRV.Core.UnitarySem
import FormalRV.Core.QuantumLib
import FormalRV.Core.PadAction.PadActionDefinitions
import FormalRV.Core.PadAction.PadActionGateEntry

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker

/-- Padded version: `pad_u Z · pad_u S = pad_u S†`. -/
theorem pad_u_σz_mul_pad_u_sMatrix (dim n : Nat) :
    pad_u dim n σz * pad_u dim n sMatrix = pad_u dim n sdagMatrix := by
  rw [pad_u_mul_pad_u, σz_mul_sMatrix]

/-- Padded version: `pad_u Z · pad_u S† = pad_u S`. -/
theorem pad_u_σz_mul_pad_u_sdagMatrix (dim n : Nat) :
    pad_u dim n σz * pad_u dim n sdagMatrix = pad_u dim n sMatrix := by
  rw [pad_u_mul_pad_u, σz_mul_sdagMatrix]

/-- Circuit equivalence: `S q ; Z q ≡ S† q` — Z·S = S† via σz_mul_sMatrix. -/
theorem S_Z_eq_SDAG {dim n : Nat} :
    uc_eval (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.Z n))
      = uc_eval (BaseUCom.SDAG n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 Real.pi) * pad_u dim n (rotation 0 0 (Real.pi/2))
        = pad_u dim n (rotation 0 0 (-(Real.pi/2)))
  rw [rotation_S, rotation_Z, rotation_SDAG, pad_u_σz_mul_pad_u_sMatrix]

/-- Circuit equivalence: `S† q ; Z q ≡ S q` — Z·S† = S via σz_mul_sdagMatrix. -/
theorem SDAG_Z_eq_S {dim n : Nat} :
    uc_eval (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.Z n))
      = uc_eval (BaseUCom.S n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 Real.pi) * pad_u dim n (rotation 0 0 (-(Real.pi/2)))
        = pad_u dim n (rotation 0 0 (Real.pi/2))
  rw [rotation_S, rotation_Z, rotation_SDAG, pad_u_σz_mul_pad_u_sdagMatrix]

/-- Circuit equivalence: `S q ; S q ; S q ≡ S† q`. Lift of `sMatrix_pow_three`
    (S has order 4, so S³ = S^(-1) = S†). -/
theorem S_S_S_eq_SDAG {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
                       (BaseUCom.S n))
      = uc_eval (BaseUCom.SDAG n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (Real.pi / 2))
        * (pad_u dim n (rotation 0 0 (Real.pi / 2))
            * pad_u dim n (rotation 0 0 (Real.pi / 2)))
      = pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_S, rotation_SDAG, sMatrix_pow_three]

/-- Circuit equivalence: `S† q ; S† q ; S† q ≡ S q`. Dual of `S_S_S_eq_SDAG`. -/
theorem SDAG_SDAG_SDAG_eq_S {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.SDAG n))
                       (BaseUCom.SDAG n))
      = uc_eval (BaseUCom.S n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
        * (pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
            * pad_u dim n (rotation 0 0 (-(Real.pi / 2))))
      = pad_u dim n (rotation 0 0 (Real.pi / 2))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_SDAG, rotation_S, sdagMatrix_pow_three]

/-- `S q ; S q ; S q` acts as S† phase on `f_to_vec dim f` (S³ ≡ S†). -/
theorem f_to_vec_S_S_S (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
                       (BaseUCom.S n))
      * f_to_vec dim f
      = (if f n then -Complex.I else 1) • f_to_vec dim f := by
  rw [S_S_S_eq_SDAG]
  exact f_to_vec_SDAG_uc_eval dim n h f

/-- `S† q ; S† q ; S† q` acts as S phase on `f_to_vec dim f` (S†³ ≡ S). -/
theorem f_to_vec_SDAG_SDAG_SDAG (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.SDAG n))
                       (BaseUCom.SDAG n))
      * f_to_vec dim f
      = (if f n then Complex.I else 1) • f_to_vec dim f := by
  rw [SDAG_SDAG_SDAG_eq_S]
  exact f_to_vec_S_uc_eval dim n h f

/-- Circuit equivalence: `H q ; H q ; H q ≡ H q`. Lift of `hMatrix_pow_three`. -/
theorem H_H_H_eq_H {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
                       (BaseUCom.H n))
      = uc_eval (BaseUCom.H n : BaseUCom dim) := by
  show pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
        * (pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
            * pad_u dim n (rotation (Real.pi/2) 0 Real.pi))
      = pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_H, hMatrix_pow_three]

/-- `H q ; H q ; H q` acts as a single H on `f_to_vec dim f`. -/
theorem f_to_vec_H_H_H (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
                       (BaseUCom.H n))
      * f_to_vec dim f
      = uc_eval (BaseUCom.H n : BaseUCom dim) * f_to_vec dim f := by
  rw [H_H_H_eq_H]

/-- Circuit equivalence: `X q ; X q ; X q ≡ X q`. Lift of `σx_pow_three`. -/
theorem X_X_X_eq_X {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.X n : BaseUCom dim) (BaseUCom.X n))
                       (BaseUCom.X n))
      = uc_eval (BaseUCom.X n : BaseUCom dim) := by
  show pad_u dim n (rotation Real.pi 0 Real.pi)
        * (pad_u dim n (rotation Real.pi 0 Real.pi)
            * pad_u dim n (rotation Real.pi 0 Real.pi))
      = pad_u dim n (rotation Real.pi 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_X, σx_pow_three]

/-- Circuit equivalence: `Y q ; Y q ; Y q ≡ Y q`. Lift of `σy_pow_three`. -/
theorem Y_Y_Y_eq_Y {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))
                       (BaseUCom.Y n))
      = uc_eval (BaseUCom.Y n : BaseUCom dim) := by
  show pad_u dim n (rotation Real.pi (Real.pi/2) (Real.pi/2))
        * (pad_u dim n (rotation Real.pi (Real.pi/2) (Real.pi/2))
            * pad_u dim n (rotation Real.pi (Real.pi/2) (Real.pi/2)))
      = pad_u dim n (rotation Real.pi (Real.pi/2) (Real.pi/2))
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_Y, σy_pow_three]

/-- Circuit equivalence: `Z q ; Z q ; Z q ≡ Z q`. Lift of `σz_pow_three`. -/
theorem Z_Z_Z_eq_Z {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.Z n : BaseUCom dim) (BaseUCom.Z n))
                       (BaseUCom.Z n))
      = uc_eval (BaseUCom.Z n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 Real.pi)
        * (pad_u dim n (rotation 0 0 Real.pi)
            * pad_u dim n (rotation 0 0 Real.pi))
      = pad_u dim n (rotation 0 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_Z, σz_pow_three]

/-- `S† q ; S† q` acts as Z on `f_to_vec dim f` (since (S†)² = Z). -/
theorem f_to_vec_SDAG_SDAG (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.SDAG n))
      * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [show uc_eval (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.SDAG n))
        = uc_eval (BaseUCom.Z n : BaseUCom dim) from SDAG_SDAG_eq_Z]
  exact f_to_vec_Z_uc_eval dim n h f

/-- `(exp(iπ/4))² = I` (used for T² = S). -/
theorem exp_pi4_sq_eq_I :
    (Complex.exp (Complex.I * (Real.pi / 4)))^2 = Complex.I := by
  rw [show (Complex.exp (Complex.I * (Real.pi / 4)))^2
        = Complex.exp (Complex.I * (Real.pi / 4) * 2) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show Complex.I * (Real.pi / 4) * 2 = (Real.pi : ℂ) / 2 * Complex.I from by ring]
  exact Complex.exp_pi_div_two_mul_I

/-- `tMatrix * tMatrix = sMatrix` (T² = S, since (exp(iπ/4))² = exp(iπ/2) = I). -/
theorem tMatrix_mul_tMatrix : tMatrix * tMatrix = sMatrix := by
  unfold tMatrix sMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  -- Residue at (1,1): exp(iπ/4) * exp(iπ/4) = I
  rw [show Complex.exp (Complex.I * (Real.pi / 4)) * Complex.exp (Complex.I * (Real.pi / 4))
        = (Complex.exp (Complex.I * (Real.pi / 4)))^2 from by ring]
  exact exp_pi4_sq_eq_I

/-- `T⁴ = Z` at the matrix level — chain of `T² = S` and `S² = Z`. -/
theorem tMatrix_pow_four : tMatrix * tMatrix * tMatrix * tMatrix = σz := by
  rw [Matrix.mul_assoc (tMatrix * tMatrix) tMatrix tMatrix,
      tMatrix_mul_tMatrix, sMatrix_mul_sMatrix]

/-- `S⁴ = I` at the matrix level — chain of `S² = Z` and `Z² = I`. -/
theorem sMatrix_pow_four : sMatrix * sMatrix * sMatrix * sMatrix = σi := by
  rw [Matrix.mul_assoc (sMatrix * sMatrix) sMatrix sMatrix,
      sMatrix_mul_sMatrix, σz_mul_σz]

/-- Circuit equivalence: `T q ; T q ; T q ; T q ≡ Z q`. Lifts `tMatrix_pow_four`
    via three `pad_u_mul_pad_u` collapses. -/
theorem T_T_T_T_eq_Z {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.T n : BaseUCom dim) (BaseUCom.T n))
                       (BaseUCom.T n)) (BaseUCom.T n))
      = uc_eval (BaseUCom.Z n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (Real.pi/4))
        * (pad_u dim n (rotation 0 0 (Real.pi/4))
            * (pad_u dim n (rotation 0 0 (Real.pi/4))
                * pad_u dim n (rotation 0 0 (Real.pi/4))))
      = pad_u dim n (rotation 0 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u]
  rw [rotation_T, rotation_Z, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      tMatrix_pow_four]

/-- Circuit equivalence: `H q ; H q ; H q ; H q ≡ ID q`. Lifts
    `hMatrix_pow_four`. Note: H² ≡ ID is stronger; this is included for
    symmetry with the T⁴/S⁴/T†⁴/S†⁴ family. -/
theorem H_H_H_H_eq_ID {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
                       (BaseUCom.H n)) (BaseUCom.H n))
      = uc_eval (BaseUCom.ID n : BaseUCom dim) := by
  show pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
        * (pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
            * (pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
                * pad_u dim n (rotation (Real.pi/2) 0 Real.pi)))
      = pad_u dim n (rotation 0 0 0)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u]
  rw [rotation_H, rotation_I, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hMatrix_pow_four]

/-- Circuit equivalence: `S q ; S q ; S q ; S q ≡ ID q`. Lifts `sMatrix_pow_four`. -/
theorem S_S_S_S_eq_ID {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
                       (BaseUCom.S n)) (BaseUCom.S n))
      = uc_eval (BaseUCom.ID n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (Real.pi/2))
        * (pad_u dim n (rotation 0 0 (Real.pi/2))
            * (pad_u dim n (rotation 0 0 (Real.pi/2))
                * pad_u dim n (rotation 0 0 (Real.pi/2))))
      = pad_u dim n (rotation 0 0 0)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u]
  rw [rotation_S, rotation_I, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      sMatrix_pow_four]

/-- `T q ; T q ; T q ; T q` acts as Z phase on `f_to_vec dim f`. -/
theorem f_to_vec_T_T_T_T (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.T n : BaseUCom dim) (BaseUCom.T n))
                       (BaseUCom.T n)) (BaseUCom.T n))
      * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [T_T_T_T_eq_Z]
  exact f_to_vec_Z_uc_eval dim n h f

/-- `H q ; H q ; H q ; H q` acts as identity on `f_to_vec dim f`. -/
theorem f_to_vec_H_H_H_H (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
                       (BaseUCom.H n)) (BaseUCom.H n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [H_H_H_H_eq_ID]
  exact f_to_vec_ID h f

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: H⁵ = H at basis level

/-- `H q ; H q ; H q ; H q ; H q` acts as a single `H q` on `f_to_vec dim f`
    (H⁵ = H, since H⁴ = ID). **Relational form**: H|b⟩ = (|0⟩ ± |1⟩)/√2 is not
    a basis state, so the cleanest statement is `uc_eval(H⁵) · v = uc_eval(H) · v`.
    Mirrors `f_to_vec_Y_Y_Y_Y_Y` (Iter 133) — same proof structure as Y⁵ since both
    have order-4 = ID without a closed-form basis-state expression. -/
theorem f_to_vec_H_H_H_H_H (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
              (BaseUCom.H n)) (BaseUCom.H n)) (BaseUCom.H n))
      * f_to_vec dim f
      = uc_eval (BaseUCom.H n : BaseUCom dim) * f_to_vec dim f := by
  -- uc_eval(seq^4 H) * f_to_vec f = H * (uc_eval(seq^3 H) * f_to_vec f) by uc_eval_seq_mul.
  -- Inner uc_eval(seq^3 H) * f_to_vec f = f_to_vec f by f_to_vec_H_H_H_H (H⁴ = ID).
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_H_H_H dim n h f]

/-- `S q ; S q ; S q ; S q` acts as identity on `f_to_vec dim f`. -/
theorem f_to_vec_S_S_S_S (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
                       (BaseUCom.S n)) (BaseUCom.S n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [S_S_S_S_eq_ID]
  exact f_to_vec_ID h f

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: S⁵ = S at basis level

/-- `S q ; S q ; S q ; S q ; S q` acts as a single `S q` on `f_to_vec dim f`
    (S⁵ = S, since S⁴ = ID). **Closed-form** result via `f_to_vec_S_uc_eval`:
    `(if f n then Complex.I else 1) • f_to_vec dim f`. Diagonal-phase variant
    of Z⁵; S maps |b⟩ to i^b |b⟩, so the basis-state action is just a phase
    factor. Completes the diagonal-phase order-5 family alongside `f_to_vec_Z_Z_Z_Z_Z`
    (Iter 132 SQIR-tick). -/
theorem f_to_vec_S_S_S_S_S (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
              (BaseUCom.S n)) (BaseUCom.S n)) (BaseUCom.S n))
      * f_to_vec dim f
      = (if f n then Complex.I else 1) • f_to_vec dim f := by
  -- uc_eval(seq^4 S) * f_to_vec f = S * (uc_eval(seq^3 S) * f_to_vec f) by uc_eval_seq_mul.
  -- Inner uc_eval(seq^3 S) * f_to_vec f = f_to_vec f by f_to_vec_S_S_S_S (S⁴ = ID).
  -- Then S * f_to_vec f = (i^[f n]) • f_to_vec f by f_to_vec_S_uc_eval.
  rw [uc_eval_seq_mul]
  rw [f_to_vec_S_S_S_S dim n h f]
  exact f_to_vec_S_uc_eval dim n h f

/-- `(exp(-iπ/4))² = -I`. -/
theorem exp_neg_pi4_sq_eq_neg_I :
    (Complex.exp (-(Complex.I * (Real.pi / 4))))^2 = -Complex.I := by
  rw [show (Complex.exp (-(Complex.I * (Real.pi / 4))))^2
        = Complex.exp (-(Complex.I * (Real.pi / 4)) * 2) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show -(Complex.I * (Real.pi / 4)) * 2 = -((Real.pi : ℂ) / 2 * Complex.I) from by ring]
  rw [Complex.exp_neg]
  rw [Complex.exp_pi_div_two_mul_I]
  exact Complex.inv_I

/-- `tdagMatrix * tdagMatrix = sdagMatrix` (T†² = S†). -/
theorem tdagMatrix_mul_tdagMatrix : tdagMatrix * tdagMatrix = sdagMatrix := by
  unfold tdagMatrix sdagMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  -- Residue at (1,1): exp(-iπ/4) * exp(-iπ/4) = -I
  rw [show Complex.exp (-(Complex.I * (Real.pi / 4)))
        * Complex.exp (-(Complex.I * (Real.pi / 4)))
        = (Complex.exp (-(Complex.I * (Real.pi / 4))))^2 from by ring]
  exact exp_neg_pi4_sq_eq_neg_I

/-- Circuit equivalence: `T† q ; T† q ≡ S† q`. -/
theorem TDAG_TDAG_eq_SDAG {dim : Nat} (n : Nat) :
    uc_eval (UCom.seq (BaseUCom.TDAG n : BaseUCom dim) (BaseUCom.TDAG n))
      = uc_eval (BaseUCom.SDAG n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi / 4)))
        * pad_u dim n (rotation 0 0 (-(Real.pi / 4)))
      = pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
  rw [rotation_TDAG, rotation_SDAG, pad_u_mul_pad_u, tdagMatrix_mul_tdagMatrix]

/-- `T† q ; T† q` acts as S† phase on `f_to_vec dim f` (since (T†)² = S†). -/
theorem f_to_vec_TDAG_TDAG (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.TDAG n : BaseUCom dim) (BaseUCom.TDAG n))
      * f_to_vec dim f
      = (if f n then -Complex.I else 1) • f_to_vec dim f := by
  rw [show uc_eval (UCom.seq (BaseUCom.TDAG n : BaseUCom dim) (BaseUCom.TDAG n))
        = uc_eval (BaseUCom.SDAG n : BaseUCom dim) from TDAG_TDAG_eq_SDAG n]
  exact f_to_vec_SDAG_uc_eval dim n h f

/-- `T†⁴ = Z` at the matrix level — chain of `T†² = S†` and `S†² = Z`. -/
theorem tdagMatrix_pow_four :
    tdagMatrix * tdagMatrix * tdagMatrix * tdagMatrix = σz := by
  rw [Matrix.mul_assoc (tdagMatrix * tdagMatrix) tdagMatrix tdagMatrix,
      tdagMatrix_mul_tdagMatrix, sdagMatrix_mul_sdagMatrix]

/-- `T⁵ = Z · T` — direct corollary of T⁴ = Z. -/
theorem tMatrix_pow_five :
    tMatrix * tMatrix * tMatrix * tMatrix * tMatrix = σz * tMatrix := by
  rw [tMatrix_pow_four]

/-- `T†⁵ = Z · T†` — direct corollary of T†⁴ = Z. -/
theorem tdagMatrix_pow_five :
    tdagMatrix * tdagMatrix * tdagMatrix * tdagMatrix * tdagMatrix = σz * tdagMatrix := by
  rw [tdagMatrix_pow_four]

/-- S has order 4 at the padded level: S · S · S · S = 1 (chain form). -/
theorem pad_u_sMatrix_pow_four {dim n : Nat} (h : n < dim) :
    pad_u dim n sMatrix * pad_u dim n sMatrix * pad_u dim n sMatrix * pad_u dim n sMatrix
      = (1 : Square dim) :=
  pad_u_pow_four_eq_one h sMatrix sMatrix_pow_four

/-- `S†⁴ = I` at the matrix level — chain of `S†² = Z` and `Z² = I`. -/
theorem sdagMatrix_pow_four :
    sdagMatrix * sdagMatrix * sdagMatrix * sdagMatrix = σi := by
  rw [Matrix.mul_assoc (sdagMatrix * sdagMatrix) sdagMatrix sdagMatrix,
      sdagMatrix_mul_sdagMatrix, σz_mul_σz]

/-- S† has order 4 at the padded level: S† · S† · S† · S† = 1 (chain form). -/
theorem pad_u_sdagMatrix_pow_four {dim n : Nat} (h : n < dim) :
    pad_u dim n sdagMatrix * pad_u dim n sdagMatrix * pad_u dim n sdagMatrix * pad_u dim n sdagMatrix
      = (1 : Square dim) :=
  pad_u_pow_four_eq_one h sdagMatrix sdagMatrix_pow_four

/-- T's 4-chain at the padded level equals pad_u σz (the padded Z gate).
    Reflects T⁴ = Z; no `n < dim` hypothesis needed. -/
theorem pad_u_tMatrix_pow_four (dim n : Nat) :
    pad_u dim n tMatrix * pad_u dim n tMatrix * pad_u dim n tMatrix * pad_u dim n tMatrix
      = pad_u dim n σz :=
  pad_u_pow_four_eq dim n tMatrix σz tMatrix_pow_four

/-- T†'s 4-chain at the padded level equals pad_u σz. Reflects T†⁴ = Z. -/
theorem pad_u_tdagMatrix_pow_four (dim n : Nat) :
    pad_u dim n tdagMatrix * pad_u dim n tdagMatrix * pad_u dim n tdagMatrix * pad_u dim n tdagMatrix
      = pad_u dim n σz :=
  pad_u_pow_four_eq dim n tdagMatrix σz tdagMatrix_pow_four

/-- T's 2-chain at the padded level equals pad_u sMatrix. Reflects T² = S. -/
theorem pad_u_tMatrix_mul_tMatrix (dim n : Nat) :
    pad_u dim n tMatrix * pad_u dim n tMatrix = pad_u dim n sMatrix :=
  pad_u_pow_two_eq dim n tMatrix sMatrix tMatrix_mul_tMatrix

/-- S's 2-chain at the padded level equals pad_u σz. Reflects S² = Z. -/
theorem pad_u_sMatrix_mul_sMatrix (dim n : Nat) :
    pad_u dim n sMatrix * pad_u dim n sMatrix = pad_u dim n σz :=
  pad_u_pow_two_eq dim n sMatrix σz sMatrix_mul_sMatrix

/-- T†'s 2-chain at the padded level equals pad_u sdagMatrix. Reflects T†² = S†. -/
theorem pad_u_tdagMatrix_mul_tdagMatrix (dim n : Nat) :
    pad_u dim n tdagMatrix * pad_u dim n tdagMatrix = pad_u dim n sdagMatrix :=
  pad_u_pow_two_eq dim n tdagMatrix sdagMatrix tdagMatrix_mul_tdagMatrix

/-- S†'s 2-chain at the padded level equals pad_u σz. Reflects S†² = Z. -/
theorem pad_u_sdagMatrix_mul_sdagMatrix (dim n : Nat) :
    pad_u dim n sdagMatrix * pad_u dim n sdagMatrix = pad_u dim n σz :=
  pad_u_pow_two_eq dim n sdagMatrix σz sdagMatrix_mul_sdagMatrix

/-- S's 3-chain at the padded level equals pad_u sdagMatrix. Reflects S³ = S†. -/
theorem pad_u_sMatrix_pow_three (dim n : Nat) :
    pad_u dim n sMatrix * pad_u dim n sMatrix * pad_u dim n sMatrix
      = pad_u dim n sdagMatrix :=
  pad_u_pow_three_eq dim n sMatrix sdagMatrix sMatrix_pow_three

/-- S†'s 3-chain at the padded level equals pad_u sMatrix. Reflects S†³ = S. -/
theorem pad_u_sdagMatrix_pow_three (dim n : Nat) :
    pad_u dim n sdagMatrix * pad_u dim n sdagMatrix * pad_u dim n sdagMatrix
      = pad_u dim n sMatrix :=
  pad_u_pow_three_eq dim n sdagMatrix sMatrix sdagMatrix_pow_three

/-- `S⁵ = S`. Follows from S⁴ = I + Matrix.one_mul. -/
theorem sMatrix_pow_five :
    sMatrix * sMatrix * sMatrix * sMatrix * sMatrix = sMatrix := by
  rw [sMatrix_pow_four, σi_eq_one, Matrix.one_mul]

/-- `S†⁵ = S†`. -/
theorem sdagMatrix_pow_five :
    sdagMatrix * sdagMatrix * sdagMatrix * sdagMatrix * sdagMatrix = sdagMatrix := by
  rw [sdagMatrix_pow_four, σi_eq_one, Matrix.one_mul]

/-- S's 5-chain at the padded level equals pad_u sMatrix. Reflects S⁵ = S. -/
theorem pad_u_sMatrix_pow_five (dim n : Nat) :
    pad_u dim n sMatrix * pad_u dim n sMatrix * pad_u dim n sMatrix * pad_u dim n sMatrix * pad_u dim n sMatrix
      = pad_u dim n sMatrix :=
  pad_u_pow_five_eq dim n sMatrix sMatrix sMatrix_pow_five

/-- S†'s 5-chain at the padded level equals pad_u sdagMatrix. Reflects S†⁵ = S†. -/
theorem pad_u_sdagMatrix_pow_five (dim n : Nat) :
    pad_u dim n sdagMatrix * pad_u dim n sdagMatrix * pad_u dim n sdagMatrix * pad_u dim n sdagMatrix * pad_u dim n sdagMatrix
      = pad_u dim n sdagMatrix :=
  pad_u_pow_five_eq dim n sdagMatrix sdagMatrix sdagMatrix_pow_five

/-- T's 5-chain at the padded level equals pad_u (σz·T). Reflects T⁵ = Z·T. -/
theorem pad_u_tMatrix_pow_five (dim n : Nat) :
    pad_u dim n tMatrix * pad_u dim n tMatrix * pad_u dim n tMatrix * pad_u dim n tMatrix * pad_u dim n tMatrix
      = pad_u dim n (σz * tMatrix) :=
  pad_u_pow_five_eq dim n tMatrix (σz * tMatrix) tMatrix_pow_five

/-- T†'s 5-chain at the padded level equals pad_u (σz·T†). Reflects T†⁵ = Z·T†. -/
theorem pad_u_tdagMatrix_pow_five (dim n : Nat) :
    pad_u dim n tdagMatrix * pad_u dim n tdagMatrix * pad_u dim n tdagMatrix * pad_u dim n tdagMatrix * pad_u dim n tdagMatrix
      = pad_u dim n (σz * tdagMatrix) :=
  pad_u_pow_five_eq dim n tdagMatrix (σz * tdagMatrix) tdagMatrix_pow_five

/-- Circuit equivalence: `T† q ; T† q ; T† q ; T† q ≡ Z q`.
    Lifts `tdagMatrix_pow_four`. -/
theorem TDAG_TDAG_TDAG_TDAG_eq_Z {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.TDAG n : BaseUCom dim)
                       (BaseUCom.TDAG n)) (BaseUCom.TDAG n)) (BaseUCom.TDAG n))
      = uc_eval (BaseUCom.Z n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi/4)))
        * (pad_u dim n (rotation 0 0 (-(Real.pi/4)))
            * (pad_u dim n (rotation 0 0 (-(Real.pi/4)))
                * pad_u dim n (rotation 0 0 (-(Real.pi/4)))))
      = pad_u dim n (rotation 0 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u]
  rw [rotation_TDAG, rotation_Z, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      tdagMatrix_pow_four]

/-- Circuit equivalence: `S† q ; S† q ; S† q ; S† q ≡ ID q`.
    Lifts `sdagMatrix_pow_four`. -/
theorem SDAG_SDAG_SDAG_SDAG_eq_ID {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.SDAG n : BaseUCom dim)
                       (BaseUCom.SDAG n)) (BaseUCom.SDAG n)) (BaseUCom.SDAG n))
      = uc_eval (BaseUCom.ID n : BaseUCom dim) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi/2)))
        * (pad_u dim n (rotation 0 0 (-(Real.pi/2)))
            * (pad_u dim n (rotation 0 0 (-(Real.pi/2)))
                * pad_u dim n (rotation 0 0 (-(Real.pi/2)))))
      = pad_u dim n (rotation 0 0 0)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u]
  rw [rotation_SDAG, rotation_I, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      sdagMatrix_pow_four]

/-- `T† q ; T† q ; T† q ; T† q` acts as Z phase on `f_to_vec dim f`. -/
theorem f_to_vec_TDAG_TDAG_TDAG_TDAG (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.TDAG n : BaseUCom dim)
                       (BaseUCom.TDAG n)) (BaseUCom.TDAG n)) (BaseUCom.TDAG n))
      * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [TDAG_TDAG_TDAG_TDAG_eq_Z]
  exact f_to_vec_Z_uc_eval dim n h f

/-- `S† q ; S† q ; S† q ; S† q` acts as identity on `f_to_vec dim f`. -/
theorem f_to_vec_SDAG_SDAG_SDAG_SDAG (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.SDAG n : BaseUCom dim)
                       (BaseUCom.SDAG n)) (BaseUCom.SDAG n)) (BaseUCom.SDAG n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [SDAG_SDAG_SDAG_SDAG_eq_ID]
  exact f_to_vec_ID h f

-- Note: `S_S_eq_Z` (the circuit equivalence S;S ≡ Z) already exists in
-- UnitarySem.lean line 578, proven via rotation_Rz_compose. Our
-- sMatrix_mul_sMatrix above gives an alternative matrix-level proof
-- (useful for f_to_vec-level rewriting).

/-- Circuit equivalence: `S q ; S† q ≡ ID` (uc_eval = identity matrix). -/
theorem S_SDAG_eq_id {dim n : Nat} (h : n < dim) :
    uc_eval (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.SDAG n))
      = (1 : Square dim) := by
  show pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
        * pad_u dim n (rotation 0 0 (Real.pi / 2))
      = 1
  rw [rotation_S, rotation_SDAG, pad_u_mul_pad_u, sdagMatrix_mul_sMatrix, pad_u_id h]

/-- Circuit equivalence: `S† q ; S q ≡ ID`. -/
theorem SDAG_S_eq_id {dim n : Nat} (h : n < dim) :
    uc_eval (UCom.seq (BaseUCom.SDAG n : BaseUCom dim) (BaseUCom.S n))
      = (1 : Square dim) := by
  show pad_u dim n (rotation 0 0 (Real.pi / 2))
        * pad_u dim n (rotation 0 0 (-(Real.pi / 2)))
      = 1
  rw [rotation_S, rotation_SDAG, pad_u_mul_pad_u, sMatrix_mul_sdagMatrix, pad_u_id h]

/-- `T† q ; T q` is identity (matrix-level proof). -/
theorem f_to_vec_TDAG_then_T (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.TDAG n : BaseUCom dim) (BaseUCom.T n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  show (pad_u dim n (rotation 0 0 (Real.pi / 4))
        * pad_u dim n (rotation 0 0 (-(Real.pi / 4)))) * f_to_vec dim f = _
  rw [rotation_T, rotation_TDAG, pad_u_mul_pad_u, tMatrix_mul_tdagMatrix, pad_u_id h, Matrix.one_mul]

/-- `Y q ; Y q` is identity (matrix-level proof).
    σy is its own inverse (σy²=I), so the matrix-level shortcut applies. -/
theorem f_to_vec_Y_Y (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  show (pad_u dim n (rotation Real.pi (Real.pi/2) (Real.pi/2))
        * pad_u dim n (rotation Real.pi (Real.pi/2) (Real.pi/2))) * f_to_vec dim f = _
  rw [rotation_Y, pad_u_mul_pad_u, σy_mul_σy, pad_u_id h, Matrix.one_mul]

/-- `H q ; H q` is identity. Cleanest proof via the matrix-level identity
    `hMatrix_mul_hMatrix` (already proven in UnitarySem) — avoids the
    superposition-cancellation route. -/
theorem f_to_vec_H_H (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  show (pad_u dim n (rotation (Real.pi / 2) 0 Real.pi)
        * pad_u dim n (rotation (Real.pi / 2) 0 Real.pi)) * f_to_vec dim f = _
  rw [rotation_H, pad_u_mul_pad_u, hMatrix_mul_hMatrix, pad_u_id h, Matrix.one_mul]

/-! ## Validation: chaining works for T;T (T² phase) -/

/-- Chaining check: applying T twice on `f_to_vec dim f` gives a `T²` phase factor.
    Validates the `uc_eval_seq_mul` + `mul_smul_state` + `f_to_vec_T_uc_eval`
    chain works as expected. This is the simplest non-trivial multi-gate
    composition through `f_to_vec`. -/
theorem f_to_vec_T_T (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.T n : BaseUCom dim) (BaseUCom.T n))
      * f_to_vec dim f
      = (if f n then Complex.exp (Complex.I * (Real.pi / 4))
                    * Complex.exp (Complex.I * (Real.pi / 4))
              else 1)
        • f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_T_uc_eval dim n h f]
  rw [mul_smul_state]
  rw [f_to_vec_T_uc_eval dim n h f]
  rw [smul_smul]
  congr 1
  by_cases hfn : f n <;> simp [hfn]

/-- Chaining check: applying T then T† gives no phase change (T†T = id). -/
theorem f_to_vec_TDAG_T (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.T n : BaseUCom dim) (BaseUCom.TDAG n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_T_uc_eval dim n h f]
  rw [mul_smul_state]
  rw [f_to_vec_TDAG_uc_eval dim n h f]
  rw [smul_smul]
  -- Need: (if f n then exp(-iπ/4) else 1) * (if f n then exp(iπ/4) else 1) = 1
  rw [show ((if f n then Complex.exp (Complex.I * (Real.pi / 4)) else (1 : ℂ))
            * (if f n then Complex.exp (-(Complex.I * (Real.pi / 4))) else (1 : ℂ)))
          = 1 from by
    by_cases hfn : f n
    · simp [hfn, ← Complex.exp_add]
    · simp [hfn]]
  rw [one_smul]

/-! ## CCX prefix: H c; CNOT b c

    First non-trivial 2-gate composition involving Hadamard. After H c:
    superposition of two basis states. CNOT b c on each branch flips the
    c-bit conditional on b-bit, so the final updated functions become
    `update f c (f b)` and `update f c (!f b)`. -/

theorem f_to_vec_H_CNOT (dim b c : Nat) (hb : b < dim) (hc : c < dim)
    (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c))
      * f_to_vec dim f
      = (Real.sqrt 2 / 2 : ℂ) • f_to_vec dim (update f c (f b))
        + ((if f c then (-1 : ℂ) else 1) * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (!f b)) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_uc_eval dim c hc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim b c (update f c false) hb hc hbc]
  rw [f_to_vec_CNOT_proved dim b c (update f c true) hb hc hbc]
  -- Simplify the nested update expressions to the desired form.
  -- Simplify the inner xor expression: bit c of (update f c v) = v;
  -- bit b of (update f c v) = f b (since b ≠ c).
  rw [show (update f c false) c = false from update_eq f c false]
  rw [show (update f c true) c = true from update_eq f c true]
  rw [show (update f c false) b = f b from update_neq f c b false hbc]
  rw [show (update f c true) b = f b from update_neq f c b true hbc]
  -- xor false (f b) = f b; xor true (f b) = !f b
  simp only [Bool.false_xor, Bool.true_xor]
  -- Then update_idem collapses the nested updates.
  rw [update_idem, update_idem]

/-! ## CCX prefix: H c; CNOT b c; T† c

    3-gate prefix. After H+CNOT we have 2 branches with c-bit = f b vs !f b.
    Applying T† c picks up a phase `exp(-i·π/4)` if the branch's c-bit is 1,
    `1` if 0. The phases differ between the branches. -/

theorem f_to_vec_H_CNOT_TDAG (dim b c : Nat) (hb : b < dim) (hc : c < dim)
    (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c))
                      (BaseUCom.TDAG c))
      * f_to_vec dim f
      = ((if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (f b))
        + ((if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (!f b)) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_CNOT dim b c hb hc hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_TDAG_uc_eval dim c hc (update f c (f b))]
  rw [f_to_vec_TDAG_uc_eval dim c hc (update f c (!f b))]
  rw [show (update f c (f b)) c = f b from update_eq f c (f b)]
  rw [show (update f c (!f b)) c = !f b from update_eq f c (!f b)]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: H c; CNOT b c; T† c; CNOT a c

    4-gate prefix. The CNOT a c flips the c-bit XOR with a-bit. Phases
    from T† c carry through unchanged (CNOT is unitary, doesn't add phase). -/

theorem f_to_vec_H_CNOT_TDAG_CNOT (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
      * f_to_vec dim f
      = ((if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (xor (f b) (f a)))
        + ((if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (xor (!f b) (f a))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_CNOT_TDAG dim b c hb hc hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim a c (update f c (f b)) ha hc hac]
  rw [f_to_vec_CNOT_proved dim a c (update f c (!f b)) ha hc hac]
  -- Simplify each branch's update.
  -- branch 0: update (update f c (f b)) c (xor ((update f c (f b)) c) ((update f c (f b)) a))
  --         = update (update f c (f b)) c (xor (f b) (f a))    [by update_eq, update_neq with a ≠ c]
  --         = update f c (xor (f b) (f a))                       [by update_idem]
  rw [show (update f c (f b)) c = f b from update_eq f c (f b)]
  rw [show (update f c (!f b)) c = !f b from update_eq f c (!f b)]
  rw [show (update f c (f b)) a = f a from update_neq f c a (f b) hac]
  rw [show (update f c (!f b)) a = f a from update_neq f c a (!f b) hac]
  rw [update_idem, update_idem]

/-! ## CCX prefix: H c; CNOT b c; T† c; CNOT a c; T c (5 gates, ends s1+T)

    First gate of `s2`. T c picks up phase exp(iπ/4) on each branch when
    its c-bit is 1. Branch 0 c-bit = xor(f b)(f a); branch 1 c-bit =
    xor(!f b)(f a). These bits are complementary (always differ). -/

theorem f_to_vec_CCX_prefix_5 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
      * f_to_vec dim f
      = ((if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (xor (f b) (f a)))
        + ((if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (xor (!f b) (f a))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_CNOT_TDAG_CNOT dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_T_uc_eval dim c hc (update f c (xor (f b) (f a)))]
  rw [f_to_vec_T_uc_eval dim c hc (update f c (xor (!f b) (f a)))]
  rw [show (update f c (xor (f b) (f a))) c = xor (f b) (f a)
      from update_eq f c (xor (f b) (f a))]
  rw [show (update f c (xor (!f b) (f a))) c = xor (!f b) (f a)
      from update_eq f c (xor (!f b) (f a))]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + CNOT b c (6 gates)

    Gate 6: CNOT b c. Each branch's c-bit XORs with f b (since b is unchanged).
    Branch 0 c-bit was xor(f b)(f a), now becomes f a (self-cancellation).
    Branch 1 c-bit was xor(!f b)(f a), now becomes !f a. -/

theorem f_to_vec_CCX_prefix_6 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
      * f_to_vec dim f
      = ((if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (f a))
        + ((if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (!f a)) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_5 dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim b c (update f c (xor (f b) (f a))) hb hc hbc]
  rw [f_to_vec_CNOT_proved dim b c (update f c (xor (!f b) (f a))) hb hc hbc]
  rw [show (update f c (xor (f b) (f a))) c = xor (f b) (f a)
      from update_eq f c (xor (f b) (f a))]
  rw [show (update f c (xor (!f b) (f a))) c = xor (!f b) (f a)
      from update_eq f c (xor (!f b) (f a))]
  rw [show (update f c (xor (f b) (f a))) b = f b
      from update_neq f c b (xor (f b) (f a)) hbc]
  rw [show (update f c (xor (!f b) (f a))) b = f b
      from update_neq f c b (xor (!f b) (f a)) hbc]
  rw [show xor (xor (f b) (f a)) (f b) = f a from by
      cases f b <;> cases f a <;> decide]
  rw [show xor (xor (!f b) (f a)) (f b) = !f a from by
      cases f b <;> cases f a <;> decide]
  rw [update_idem, update_idem]

/-! ## CCX prefix: ... + T† c (7 gates)

    Gate 7: T† c (third gate of s2). Adds phase exp(-iπ/4) per branch
    when branch's c-bit is 1. Branch 0 c-bit = f a, branch 1 = !f a. -/

theorem f_to_vec_CCX_prefix_7 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
      * f_to_vec dim f
      = ((if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (f a))
        + ((if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (!f a)) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_6 dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_TDAG_uc_eval dim c hc (update f c (f a))]
  rw [f_to_vec_TDAG_uc_eval dim c hc (update f c (!f a))]
  rw [show (update f c (f a)) c = f a from update_eq f c (f a)]
  rw [show (update f c (!f a)) c = !f a from update_eq f c (!f a)]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + CNOT a c (8 gates, ends s2)

    Gate 8 = last gate of s2. CNOT a c flips c-bit XOR with a-bit.
    Branch 0: xor(f a)(f a) = false. Branch 1: xor(!f a)(f a) = true.
    After this gate, the two branches have FIXED c-bits — the f-dependence
    in the c-bit has been fully absorbed into the phase factors. -/

theorem f_to_vec_CCX_prefix_8 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
      * f_to_vec dim f
      = ((if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + ((if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_7 dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim a c (update f c (f a)) ha hc hac]
  rw [f_to_vec_CNOT_proved dim a c (update f c (!f a)) ha hc hac]
  rw [show (update f c (f a)) c = f a from update_eq f c (f a)]
  rw [show (update f c (!f a)) c = !f a from update_eq f c (!f a)]
  rw [show (update f c (f a)) a = f a from update_neq f c a (f a) hac]
  rw [show (update f c (!f a)) a = f a from update_neq f c a (!f a) hac]
  rw [show xor (f a) (f a) = false from by cases f a <;> decide]
  rw [show xor (!f a) (f a) = true from by cases f a <;> decide]
  rw [update_idem, update_idem]

/-! ## CCX prefix: ... + CNOT a b (9 gates, start of s3)

    Gate 9 = first gate of s3. CNOT a b — control a, target b. This is
    the FIRST gate that doesn't touch c. b-bit XORs with a-bit. Each
    branch gains a NESTED update (at c, then at b). Phases unchanged. -/

theorem f_to_vec_CCX_prefix_9 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
      * f_to_vec dim f
      = ((if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update (update f c false) b (xor (f b) (f a)))
        + ((if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update (update f c true) b (xor (f b) (f a))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_8 dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim a b (update f c false) ha hb hab]
  rw [f_to_vec_CNOT_proved dim a b (update f c true) ha hb hab]
  -- (update f c v) b = f b (b ≠ c), (update f c v) a = f a (a ≠ c)
  rw [show (update f c false) b = f b from update_neq f c b false hbc]
  rw [show (update f c false) a = f a from update_neq f c a false hac]
  rw [show (update f c true) b = f b from update_neq f c b true hbc]
  rw [show (update f c true) a = f a from update_neq f c a true hac]

/-! ## CCX prefix: ... + T† b (10 gates)

    Gate 10: T† b. b-bit phase factor. After CNOT a b, both branches
    have b-bit = xor(f b)(f a) — SAME for both branches. So both branches
    pick up the same phase factor (no new asymmetry). -/

theorem f_to_vec_CCX_prefix_10 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
      * f_to_vec dim f
      = ((if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update (update f c false) b (xor (f b) (f a)))
        + ((if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update (update f c true) b (xor (f b) (f a))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_9 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_TDAG_uc_eval dim b hb (update (update f c false) b (xor (f b) (f a)))]
  rw [f_to_vec_TDAG_uc_eval dim b hb (update (update f c true) b (xor (f b) (f a)))]
  -- (update _ b w) b = w
  rw [show (update (update f c false) b (xor (f b) (f a))) b = xor (f b) (f a)
      from update_eq _ b (xor (f b) (f a))]
  rw [show (update (update f c true) b (xor (f b) (f a))) b = xor (f b) (f a)
      from update_eq _ b (xor (f b) (f a))]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + CNOT a b (11 gates, ends s3)

    Gate 11 = last gate of s3. CNOT a b again — un-does gate 9's b-bit XOR.
    State b-bit returns to f b. After update_idem (collapse double-b update)
    and update_self (resetting b to f b is no-op), the state simplifies
    back to `update f c {false,true}`. -/

theorem f_to_vec_CCX_prefix_11 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
        (BaseUCom.CNOT a b))
      * f_to_vec dim f
      = ((if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + ((if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_10 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim a b
      (update (update f c false) b (xor (f b) (f a))) ha hb hab]
  rw [f_to_vec_CNOT_proved dim a b
      (update (update f c true) b (xor (f b) (f a))) ha hb hab]
  -- (update _ b w) b = w; (update (update f c v) b w) a = f a (a ≠ b, a ≠ c)
  rw [show (update (update f c false) b (xor (f b) (f a))) b = xor (f b) (f a)
      from update_eq _ b (xor (f b) (f a))]
  rw [show (update (update f c true) b (xor (f b) (f a))) b = xor (f b) (f a)
      from update_eq _ b (xor (f b) (f a))]
  rw [show (update (update f c false) b (xor (f b) (f a))) a = f a from by
      rw [update_neq _ b a (xor (f b) (f a)) hab,
          update_neq _ c a false hac]]
  rw [show (update (update f c true) b (xor (f b) (f a))) a = f a from by
      rw [update_neq _ b a (xor (f b) (f a)) hab,
          update_neq _ c a true hac]]
  -- xor (xor (f b) (f a)) (f a) = f b
  rw [show xor (xor (f b) (f a)) (f a) = f b from by
      cases f b <;> cases f a <;> decide]
  -- update_idem collapses the double-b update; update_self collapses (update _ b (f b))
  rw [update_idem, update_idem]
  -- Now: update (update f c false) b (f b) needs (update f c false) b = f b first
  rw [show update (update f c false) b (f b)
        = update (update f c false) b ((update f c false) b) from by
      rw [update_neq _ c b false hbc]]
  rw [show update (update f c true) b (f b)
        = update (update f c true) b ((update f c true) b) from by
      rw [update_neq _ c b true hbc]]
  rw [update_self, update_self]

/-! ## CCX prefix: ... + T a (12 gates)

    Gate 12 = T a (start of s4). a-bit phase factor.
    Both branches' a-bit is f a (a is unchanged through all previous gates,
    and (update f c v) a = f a for a ≠ c). Same phase on both branches. -/

theorem f_to_vec_CCX_prefix_12 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
        (BaseUCom.CNOT a b))
        (BaseUCom.T a))
      * f_to_vec dim f
      = ((if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + ((if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_11 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_T_uc_eval dim a ha (update f c false)]
  rw [f_to_vec_T_uc_eval dim a ha (update f c true)]
  rw [show (update f c false) a = f a from update_neq f c a false hac]
  rw [show (update f c true) a = f a from update_neq f c a true hac]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + T b (13 gates)

    Gate 13 = T b. b-bit phase factor. Both branches' b-bit is f b
    (b is unchanged after gate 11's un-do). Same phase on both. -/

theorem f_to_vec_CCX_prefix_13 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
        (BaseUCom.CNOT a b))
        (BaseUCom.T a))
        (BaseUCom.T b))
      * f_to_vec dim f
      = ((if f b then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + ((if f b then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_12 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_T_uc_eval dim b hb (update f c false)]
  rw [f_to_vec_T_uc_eval dim b hb (update f c true)]
  rw [show (update f c false) b = f b from update_neq f c b false hbc]
  rw [show (update f c true) b = f b from update_neq f c b true hbc]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + T c (14 gates)

    Gate 14 = T c. c-bit phase factor. Branch 0 c-bit = false (no phase),
    branch 1 c-bit = true (phase exp(iπ/4)). Last asymmetry-introducing
    gate before the final H bifurcation. -/

theorem f_to_vec_CCX_prefix_14 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
        (BaseUCom.CNOT a b))
        (BaseUCom.T a))
        (BaseUCom.T b))
        (BaseUCom.T c))
      * f_to_vec dim f
      = ((1 : ℂ)
          * (if f b then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + (Complex.exp (Complex.I * (Real.pi / 4))
           * (if f b then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_13 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_T_uc_eval dim c hc (update f c false)]
  rw [f_to_vec_T_uc_eval dim c hc (update f c true)]
  rw [show (update f c false) c = false from update_eq f c false]
  rw [show (update f c true) c = true from update_eq f c true]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; simp
  · congr 1
    simp only [if_true]
    ring

/-! ## Algebraic infrastructure for the 7-T phase cancellation

    Identities involving `Complex.exp (i·π/4)` that the CCX_PHASE_CANCEL
    step will need. Each is independent of the circuit machinery. -/

/-- exp(iπ/4) · exp(-iπ/4) = 1. -/
theorem exp_pi4_mul_exp_neg_pi4 :
    Complex.exp (Complex.I * (Real.pi / 4))
      * Complex.exp (-(Complex.I * (Real.pi / 4))) = 1 := by
  rw [← Complex.exp_add]
  rw [show Complex.I * (Real.pi / 4) + -(Complex.I * (Real.pi / 4)) = 0 from by ring]
  exact Complex.exp_zero

/-- exp(-iπ/4) · exp(iπ/4) = 1. -/
theorem exp_neg_pi4_mul_exp_pi4 :
    Complex.exp (-(Complex.I * (Real.pi / 4)))
      * Complex.exp (Complex.I * (Real.pi / 4)) = 1 := by
  rw [mul_comm]; exact exp_pi4_mul_exp_neg_pi4

/-- exp(iπ/4)^2 · exp(-iπ/4)^2 = 1. -/
theorem exp_pi4_sq_mul_exp_neg_pi4_sq :
    (Complex.exp (Complex.I * (Real.pi / 4)))^2
      * (Complex.exp (-(Complex.I * (Real.pi / 4))))^2 = 1 := by
  rw [show (Complex.exp (Complex.I * (Real.pi / 4)))^2
        * (Complex.exp (-(Complex.I * (Real.pi / 4))))^2
        = (Complex.exp (Complex.I * (Real.pi / 4))
           * Complex.exp (-(Complex.I * (Real.pi / 4))))^2 from by ring]
  rw [exp_pi4_mul_exp_neg_pi4]
  ring

/-- exp(iπ/4)^4 = exp(iπ) = -1. -/
theorem exp_pi4_pow_four :
    (Complex.exp (Complex.I * (Real.pi / 4)))^4 = -1 := by
  rw [show (Complex.exp (Complex.I * (Real.pi / 4)))^4
        = Complex.exp (Complex.I * (Real.pi / 4) * 4) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show Complex.I * (Real.pi / 4) * 4 = (Real.pi : ℂ) * Complex.I from by ring]
  exact Complex.exp_pi_mul_I

/-- exp(-iπ/4)^4 = exp(-iπ) = -1. Dagger version of `exp_pi4_pow_four`. -/
theorem exp_neg_pi4_pow_four :
    (Complex.exp (-(Complex.I * (Real.pi / 4))))^4 = -1 := by
  rw [show (Complex.exp (-(Complex.I * (Real.pi / 4))))^4
        = Complex.exp (-(Complex.I * (Real.pi / 4)) * 4) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show -(Complex.I * (Real.pi / 4)) * 4 = -((Real.pi : ℂ) * Complex.I) from by ring]
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]
  ring

/-- exp(iπ/4)^2 = exp(iπ/2) = i. The basic π/4 → π/2 squaring identity.
    Useful for further reducing 2-factor exp products inside the CCX
    phase-cancellation cases. -/
theorem exp_pi4_pow_two_eq_I :
    (Complex.exp (Complex.I * (Real.pi / 4)))^2 = Complex.I := by
  rw [show (Complex.exp (Complex.I * (Real.pi / 4)))^2
        = Complex.exp (Complex.I * (Real.pi / 4) * 2) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show Complex.I * (Real.pi / 4) * 2 = (Real.pi / 2 : ℂ) * Complex.I from by ring]
  exact Complex.exp_pi_div_two_mul_I

/-- exp(-iπ/4)^2 = exp(-iπ/2) = -i. Dagger version. -/
theorem exp_neg_pi4_pow_two_eq_neg_I :
    (Complex.exp (-(Complex.I * (Real.pi / 4))))^2 = -Complex.I := by
  rw [show (Complex.exp (-(Complex.I * (Real.pi / 4))))^2
        = Complex.exp (-(Complex.I * (Real.pi / 4)) * 2) from by
      rw [← Complex.exp_nat_mul]; ring_nf]
  rw [show -(Complex.I * (Real.pi / 4)) * 2 = -((Real.pi / 2 : ℂ) * Complex.I) from by ring]
  rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I]
  simp [Complex.inv_I]

/-- 4-factor alternating pattern: `e * e⁻¹ * e * e⁻¹ = 1` where
    `e = exp(iπ/4)`. This product appears in CCX_PHASE_CANCEL α₁
    expressions for cases where (f a, f b) = (F, F). 1-line proof
    via repeated `exp_pi4_mul_exp_neg_pi4` after associativity. -/
theorem exp_pi4_alt_four :
    Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (-(Complex.I * (Real.pi / 4)))
    * Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (-(Complex.I * (Real.pi / 4))) = 1 := by
  rw [show Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
     = (Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4))))
       * (Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))) from by ring]
  rw [exp_pi4_mul_exp_neg_pi4]
  ring

/-- 4-factor consecutive-grouping pattern: `e * e * e⁻¹ * e⁻¹ = 1` where
    `e = exp(iπ/4)`. Appears in CCX_PHASE_CANCEL α₁ for (F,T,*) and
    (T,F,*) cases (2 positive π/4 factors then 2 negative). -/
theorem exp_pi4_consec_four :
    Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (-(Complex.I * (Real.pi / 4)))
    * Complex.exp (-(Complex.I * (Real.pi / 4))) = 1 := by
  rw [show Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
     = (Complex.exp (Complex.I * (Real.pi / 4)))^2
       * (Complex.exp (-(Complex.I * (Real.pi / 4))))^2 from by ring]
  exact exp_pi4_sq_mul_exp_neg_pi4_sq

/-- 4-factor palindrome pattern: `e * e⁻¹ * e⁻¹ * e = 1` where
    `e = exp(iπ/4)`. Appears in CCX_PHASE_CANCEL α₀ for (T,F,*) cases. -/
theorem exp_pi4_palindrome_four :
    Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (-(Complex.I * (Real.pi / 4)))
    * Complex.exp (-(Complex.I * (Real.pi / 4)))
    * Complex.exp (Complex.I * (Real.pi / 4)) = 1 := by
  rw [show Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (Complex.I * (Real.pi / 4))
     = (Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (-(Complex.I * (Real.pi / 4))))
       * (Complex.exp (-(Complex.I * (Real.pi / 4)))
       * Complex.exp (Complex.I * (Real.pi / 4))) from by ring]
  rw [exp_pi4_mul_exp_neg_pi4, exp_neg_pi4_mul_exp_pi4]
  ring

/-- 4-factor uniform-product pattern: `e * e * e * e = -1` where
    `e = exp(iπ/4)`. Appears in CCX_PHASE_CANCEL α₁ for (T,T,*) cases.
    Equivalent to `exp_pi4_pow_four` but in mul-of-mul form. -/
theorem exp_pi4_mul_four_eq_neg_one :
    Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (Complex.I * (Real.pi / 4)) = -1 := by
  rw [show Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (Complex.I * (Real.pi / 4))
       * Complex.exp (Complex.I * (Real.pi / 4))
     = (Complex.exp (Complex.I * (Real.pi / 4)))^4 from by ring]
  exact exp_pi4_pow_four

/-- (√2/2)² = 1/2 in ℂ. -/
theorem sqrt2_div2_sq : ((Real.sqrt 2 : ℂ) / 2) * ((Real.sqrt 2 : ℂ) / 2) = 1/2 := by
  have h : ((Real.sqrt 2 : ℂ))^2 = 2 := by
    have hreal : ((Real.sqrt 2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    exact_mod_cast hreal
  field_simp
  linear_combination h

/-- Hadamard sandwich: `H X H = Z`. -/
theorem hMatrix_σx_hMatrix : hMatrix * σx * hMatrix = σz := by
  unfold hMatrix σx σz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try linear_combination 2 * sqrt2_div2_sq) <;>
    (try linear_combination -2 * sqrt2_div2_sq)

/-- Hadamard sandwich: `H Z H = X`. Dual of `hMatrix_σx_hMatrix`. -/
theorem hMatrix_σz_hMatrix : hMatrix * σz * hMatrix = σx := by
  unfold hMatrix σz σx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try linear_combination 2 * sqrt2_div2_sq) <;>
    (try linear_combination -2 * sqrt2_div2_sq)

/-- Hadamard sandwich: `H Y H = -Y`. The Y axis flips under Hadamard
    conjugation (Y is anti-symmetric under the X↔Z basis swap). -/
theorem hMatrix_σy_hMatrix : hMatrix * σy * hMatrix = -σy := by
  unfold hMatrix σy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply] <;>
    (try linear_combination 2 * Complex.I * sqrt2_div2_sq) <;>
    (try linear_combination -(2 * Complex.I) * sqrt2_div2_sq)

/-- S sandwich: `S X S† = Y`. The S gate maps X to Y under conjugation
    (a 90° rotation in the X-Y plane). -/
theorem sMatrix_σx_sdagMatrix : sMatrix * σx * sdagMatrix = σy := by
  unfold sMatrix σx sdagMatrix σy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- S sandwich: `S Y S† = -X`. -/
theorem sMatrix_σy_sdagMatrix : sMatrix * σy * sdagMatrix = -σx := by
  unfold sMatrix σy sdagMatrix σx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- S sandwich: `S Z S† = Z`. The Z axis is fixed by S (since both are
    Z-axis rotations and commute). -/
theorem sMatrix_σz_sdagMatrix : sMatrix * σz * sdagMatrix = σz := by
  unfold sMatrix σz sdagMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Dual S†-sandwich: `S† X S = -Y`. Inverse rotation of `S X S† = Y`. -/
theorem sdagMatrix_σx_sMatrix : sdagMatrix * σx * sMatrix = -σy := by
  unfold sdagMatrix σx sMatrix σy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Dual S†-sandwich: `S† Y S = X`. -/
theorem sdagMatrix_σy_sMatrix : sdagMatrix * σy * sMatrix = σx := by
  unfold sdagMatrix σy sMatrix σx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Dual S†-sandwich: `S† Z S = Z`. -/
theorem sdagMatrix_σz_sMatrix : sdagMatrix * σz * sMatrix = σz := by
  unfold sdagMatrix σz sMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- T-sandwich: `T Z T† = Z`. T is a Z-axis rotation (by π/4) so it
    commutes with σz; the sandwich therefore acts trivially. -/
theorem tMatrix_σz_tdagMatrix : tMatrix * σz * tdagMatrix = σz := by
  unfold tMatrix σz tdagMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
          ← Complex.exp_add, Complex.exp_zero]

/-- T†-sandwich: `T† Z T = Z`. Dual of `tMatrix_σz_tdagMatrix`. -/
theorem tdagMatrix_σz_tMatrix : tdagMatrix * σz * tMatrix = σz := by
  unfold tdagMatrix σz tMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
          ← Complex.exp_add, Complex.exp_zero]

/-- Circuit equivalence: `H q ; X q ; H q ≡ Z q`. This is the
    canonical Hadamard sandwich identity at the circuit level — lifts
    the matrix identity `hMatrix * σx * hMatrix = σz` (theorem
    `hMatrix_σx_hMatrix`) through `pad_u_mul_pad_u`. -/
theorem H_X_H_eq_Z {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.X n))
                       (BaseUCom.H n))
      = uc_eval (BaseUCom.Z n : BaseUCom dim) := by
  show pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
        * (pad_u dim n (rotation Real.pi 0 Real.pi)
            * pad_u dim n (rotation (Real.pi/2) 0 Real.pi))
      = pad_u dim n (rotation 0 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_H, rotation_X, rotation_Z, hMatrix_σx_hMatrix]

/-- Circuit equivalence: `H q ; Z q ; H q ≡ X q`. Dual sandwich. -/
theorem H_Z_H_eq_X {dim n : Nat} :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.Z n))
                       (BaseUCom.H n))
      = uc_eval (BaseUCom.X n : BaseUCom dim) := by
  show pad_u dim n (rotation (Real.pi/2) 0 Real.pi)
        * (pad_u dim n (rotation 0 0 Real.pi)
            * pad_u dim n (rotation (Real.pi/2) 0 Real.pi))
      = pad_u dim n (rotation Real.pi 0 Real.pi)
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, ← Matrix.mul_assoc,
      rotation_H, rotation_Z, rotation_X, hMatrix_σz_hMatrix]

end FormalRV.Framework
