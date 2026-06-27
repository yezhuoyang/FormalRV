/- PadActionComposite — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
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


end FormalRV.Framework
