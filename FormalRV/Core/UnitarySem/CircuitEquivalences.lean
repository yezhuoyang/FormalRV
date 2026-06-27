/- UnitarySem — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Core.UnitarySem.UnitarySemantics

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker  -- enables `A ⊗ₖ B` notation for Matrix.kronecker

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


end FormalRV.Framework
