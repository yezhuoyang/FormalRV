/-
  FormalRV.PauliRotation.Correctness.CircuitIdentities
  ────────────────────────────────────────
  THE REUSABLE CIRCUIT-IDENTITY LIBRARY of the semantic core (John's
  directive: standard identities proven ONCE, abstractly, so every gate-row
  proof becomes a short structural derivation instead of an entrywise
  computation).

  Everything is stated over ABSTRACT matrices `M N : Matrix m m ℂ` with the
  involution / anticommutation hypotheses (`M² = 1`, `MN = −NM`) — the only
  facts Pauli axes actually provide — so each identity instantiates at 2×2
  Paulis AND at `axisMat n P` for any width and wires:

    §1  Angle-doubling rows: `T² = S`, `S² = Z-level`, `(π/2)² = π`.
    §2  THE PUSH RULE (`rot_quarter_push`): a π/4 rotation moves past ANY
        rotation about an anticommuting axis by conjugating the axis,
        `N ↦ (−i)·MN` — the Litinski commutation rule at matrix level.
    §3  THE BRAID (`rot_braid`): for anticommuting involutions,
        `M_{π/4} · N_{π/4} · M_{π/4} = (−i) · (M+N)/√2` — the generalized
        Hadamard, DERIVED from push + merge (no entry computations).
    §4  Instantiations: `dict_H_from_braid` re-derives `Dictionary.dict_H`
        structurally; `axisMat_anticomm` upgrades the sign theorem to the
        anticommuting case; `hGate_denote` gives THE n-QUBIT H ROW — the
        dictionary's three rotations at ANY wire `q < n` denote the
        generalized Hadamard about `(X_q + Z_q)/√2`.
-/
import FormalRV.PauliRotation.Semantics.CommBridge
import FormalRV.PauliRotation.Compiler.Scheduler
import FormalRV.PauliRotation.Correctness.SingleQubitRows

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ## §1. Angle-doubling rows (named corollaries of the merge law). -/

/-- Two T-level rotations make an S-level rotation. -/
theorem rot_eighth_sq {M : Matrix m m ℂ} (hM : M * M = 1) :
    rotOf (Real.pi / 8) M * rotOf (Real.pi / 8) M = rotOf (Real.pi / 4) M := by
  rw [rotOf_mul_same hM]
  congr 1
  ring

/-- Two S-level rotations make a Pauli-level rotation. -/
theorem rot_quarter_sq {M : Matrix m m ℂ} (hM : M * M = 1) :
    rotOf (Real.pi / 4) M * rotOf (Real.pi / 4) M = rotOf (Real.pi / 2) M := by
  rw [rotOf_mul_same hM]
  congr 1
  ring

/-- Two Pauli-level rotations make the global phase `−1`. -/
theorem rot_half_sq {M : Matrix m m ℂ} (hM : M * M = 1) :
    rotOf (Real.pi / 2) M * rotOf (Real.pi / 2) M = -1 := by
  rw [rotOf_mul_same hM]
  rw [show Real.pi / 2 + Real.pi / 2 = Real.pi by ring, rotOf_pi]

/-! ## §2. The push rule. -/

/-- `M·N·M = −N` for an involution `M` anticommuting with `N` — the workhorse
conjugation fact. -/
theorem conj_anticomm {M N : Matrix m m ℂ} (hM : M * M = 1)
    (hMN : M * N = -(N * M)) : M * N * M = -N := by
  rw [hMN, Matrix.neg_mul, Matrix.mul_assoc, hM, Matrix.mul_one]

/-- The conjugated axis `(−i)·MN` is again an involution. -/
theorem conj_axis_invol {M N : Matrix m m ℂ} (hM : M * M = 1)
    (hN : N * N = 1) (hMN : M * N = -(N * M)) :
    ((-Complex.I) • (M * N)) * ((-Complex.I) • (M * N)) = 1 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h1 : M * N * (M * N) = -(N * (M * M) * N) := by
    rw [← Matrix.mul_assoc, conj_anticomm hM hMN, Matrix.neg_mul, hM,
        Matrix.mul_one]
  rw [h1, hM, Matrix.mul_one, hN, smul_neg, neg_mul_neg, Complex.I_mul_I]
  module

/-- **THE PUSH RULE**: a π/4 rotation about `M` moves past a rotation about
an anticommuting axis `N` (ANY angle) by conjugating the axis to `(−i)·MN`
— the Litinski commutation rule at the matrix level. -/
theorem rot_quarter_push {M N : Matrix m m ℂ} (hM : M * M = 1)
    (hMN : M * N = -(N * M)) (φ : ℝ) :
    rotOf (Real.pi / 4) M * rotOf φ N
      = rotOf φ ((-Complex.I) • (M * N)) * rotOf (Real.pi / 4) M := by
  have hMNM : M * N * M = -N := conj_anticomm hM hMN
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  unfold rotOf
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.mul_one]
  rw [show M * N * M = -N from hMNM]
  ring_nf
  simp only [Complex.I_sq, hI3]
  module

/-! ## §3. The braid (generalized Hadamard). -/

/-- **THE BRAID IDENTITY**: for anticommuting involutions,
`M_{π/4} · N_{π/4} · M_{π/4} = (−i) • (M + N)/√2` — the generalized
Hadamard, derived structurally: push, merge the two `M`-rotations to a
Pauli, expand the conjugated quarter-rotation.  No entry computations. -/
theorem rot_braid {M N : Matrix m m ℂ} (hM : M * M = 1)
    (hMN : M * N = -(N * M)) :
    rotOf (Real.pi / 4) M * rotOf (Real.pi / 4) N * rotOf (Real.pi / 4) M
      = (-Complex.I) • ((((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ) • (M + N)) := by
  have hMNM : M * N * M = -N := conj_anticomm hM hMN
  have hexp : rotOf (Real.pi / 4) ((-Complex.I) • (M * N))
      = (((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ) • (1 : Matrix m m ℂ)
        - (((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ) • (M * N) := by
    unfold rotOf
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four, smul_smul]
    congr 1
    rw [show ((((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ) * Complex.I) * (-Complex.I)
          = (((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ) * (-(Complex.I * Complex.I))
        from by ring, Complex.I_mul_I]
    ring_nf
  rw [rot_quarter_push hM hMN, Matrix.mul_assoc, rot_quarter_sq hM,
      rotOf_pi_div_two, hexp, sub_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul,
      show M * N * M = -N from hMNM]
  module

/-! ## §4. Instantiations. -/

/-- The 2×2 anticommutation `Z·X = −X·Z`, from the proven sign table. -/
theorem pauliZX_anticomm :
    Pauli.toMatrix .Z * Pauli.toMatrix .X
      = -(Pauli.toMatrix .X * Pauli.toMatrix .Z) := by
  have h := pauli_mul_sign .Z .X
  simpa [pauliAC] using h

/-- The Hadamard is the normalized anticommuting sum `(X + Z)/√2`. -/
theorem hMat_eq_sum :
    hMat = (((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ)
      • (Pauli.toMatrix .X + Pauli.toMatrix .Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, Pauli.toMatrix]

/-- **`dict_H`, re-derived structurally from the braid** — the same theorem
as `Dictionary.dict_H`, now a three-line corollary of the reusable identity
instead of an entrywise computation. -/
theorem dict_H_from_braid :
    rotOf (Real.pi / 4) (Pauli.toMatrix .Z)
        * rotOf (Real.pi / 4) (Pauli.toMatrix .X)
        * rotOf (Real.pi / 4) (Pauli.toMatrix .Z)
      = (-Complex.I) • hMat := by
  rw [rot_braid (Pauli.toMatrix_mul_self .Z) pauliZX_anticomm, hMat_eq_sum,
      add_comm]

/-- **Anticommutation bridge**: an ODD anticommuting-overlap count makes the
axis matrices anticommute (the odd twin of `axisMat_comm_of_commF`). -/
theorem axisMat_anticomm (n : Nat) {P Q : PauliProduct}
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (h : acCount P Q % 2 = 1) :
    axisMat n P * axisMat n Q = -(axisMat n Q * axisMat n P) := by
  have hsign := opsMat_mul_sign n (kindFn P) (kindFn Q)
  rw [acCount_dense n P Q hs hw] at hsign
  unfold axisMat
  rw [hsign, Odd.neg_one_pow (Nat.odd_iff.mpr h), neg_smul, one_smul]

/-- The single-qubit Z/X axes at the same wire anticommute syntactically. -/
theorem acCount_ZX_self (q : Nat) :
    acCount [(⟨q, .z⟩ : PFactor)] [(⟨q, .x⟩ : PFactor)] = 1 := by
  simp [acCount, overlapMismatch]

/-- **THE n-QUBIT H ROW**: at ANY wire `q < n`, the dictionary's three
π/4 rotations (`hGate q`) denote the generalized Hadamard about
`(X_q + Z_q)/√2`, with the explicit global phase `−i` — obtained by
instantiating the braid at the axis matrices.  This is the first full
n-qubit row of the dictionary leg. -/
theorem hGate_denote (n q : Nat) (hq : q + 1 ≤ n) :
    seqDenote n ((hGate q).flatten)
      = (-Complex.I) • ((((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ)
          • (axisMat n [⟨q, .z⟩] + axisMat n [⟨q, .x⟩])) := by
  have hwidth : PauliProduct.width [(⟨q, .z⟩ : PFactor)] ≤ n := by
    simp [PauliProduct.width]
    omega
  have hanti : axisMat n [(⟨q, .z⟩ : PFactor)] * axisMat n [(⟨q, .x⟩ : PFactor)]
      = -(axisMat n [(⟨q, .x⟩ : PFactor)] * axisMat n [(⟨q, .z⟩ : PFactor)]) :=
    axisMat_anticomm n (by simp [sortedStrict]) hwidth
      (by rw [acCount_ZX_self])
  have hbraid := rot_braid (axisMat_mul_self n [(⟨q, .z⟩ : PFactor)]) hanti
  show ((1 * Rot.denote n ⟨false, .piQuarter, [⟨q, .z⟩]⟩)
        * Rot.denote n ⟨false, .piQuarter, [⟨q, .x⟩]⟩)
      * Rot.denote n ⟨false, .piQuarter, [⟨q, .z⟩]⟩ = _
  rw [Matrix.one_mul]
  show (rotOf (Rot.theta ⟨false, .piQuarter, [⟨q, .z⟩]⟩) (axisMat n [⟨q, .z⟩])
        * rotOf (Rot.theta ⟨false, .piQuarter, [⟨q, .x⟩]⟩) (axisMat n [⟨q, .x⟩]))
      * rotOf (Rot.theta ⟨false, .piQuarter, [⟨q, .z⟩]⟩) (axisMat n [⟨q, .z⟩]) = _
  simp only [Rot.theta, RAngle.val, if_false, Bool.false_eq_true]
  rw [hbraid]

end FormalRV.PauliRotation
