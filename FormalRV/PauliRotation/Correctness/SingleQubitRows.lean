/-
  FormalRV.PauliRotation.Correctness.SingleQubitRows
  ──────────────────────────────────────────────────
  The SINGLE-QUBIT rows of the gate dictionary, proven at the 2x2 level
  (each with its EXPLICIT global phase `phaseC θ`):

      Z-axis : rotOf θ Z  =  diag(e^{−iθ}, e^{iθ})      (generic θ)
      T  row : rotOf (π/8) Z  =  e^{−iπ/8} • diag(1, e^{iπ/4})
      S  row : rotOf (π/4) Z  =  e^{−iπ/4} • diag(1, i)
      Z/X rows : rotOf (π/2) P = (−i) • P               (rotOf_pi_div_two)
      H  row : Z_{π/4}·X_{π/4}·Z_{π/4} = e^{−iπ/4} • H

  These are exactly the 2×2 facts the n-qubit lift consumes; the lift
  itself lives in `GateRows`/`CCZRow`/`CCXRow` and assembles in
  `Assembly` (`gateRots_denote_applyNat`) — the dictionary leg is CLOSED.
-/
import FormalRV.PauliRotation.Semantics.Core

namespace FormalRV.PauliRotation

open FormalRV.BQCode
open Matrix

/-! ## §1. Global phases. -/

/-- `e^{iθ}` (the global phases the dictionary tracks explicitly). -/
noncomputable def phaseC (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

theorem phaseC_eq (θ : ℝ) :
    phaseC θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [phaseC, Complex.exp_mul_I]
  simp [Complex.ofReal_cos, Complex.ofReal_sin]

theorem phaseC_add (a b : ℝ) : phaseC a * phaseC b = phaseC (a + b) := by
  rw [phaseC, phaseC, phaseC, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## §2. Z-axis rotations are phase diagonals (generic, radical-free). -/

/-- **Generic Z-row**: a Z-rotation by ANY angle is the diagonal phase pair
`diag(e^{−iθ}, e^{iθ})`. -/
theorem rotZ_eq_diag (θ : ℝ) :
    rotOf θ (Pauli.toMatrix .Z) = !![phaseC (-θ), 0; 0, phaseC θ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotOf, Pauli.toMatrix, phaseC_eq, Real.cos_neg, Real.sin_neg]
  ring

/-- **The T row**: the π/8 Z-rotation IS the T gate, up to the explicit
global phase `e^{−iπ/8}`. -/
theorem dict_T :
    rotOf (Real.pi / 8) (Pauli.toMatrix .Z)
      = phaseC (-(Real.pi / 8)) • !![1, 0; 0, phaseC (Real.pi / 4)] := by
  have h8 : phaseC (-(Real.pi / 8)) * phaseC (Real.pi / 4)
      = phaseC (Real.pi / 8) := by
    rw [phaseC_add]
    congr 1
    ring
  rw [rotZ_eq_diag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, ← h8]

/-- **The S row**: the π/4 Z-rotation IS the S gate, up to `e^{−iπ/4}`. -/
theorem dict_S :
    rotOf (Real.pi / 4) (Pauli.toMatrix .Z)
      = phaseC (-(Real.pi / 4)) • !![1, 0; 0, Complex.I] := by
  have hI : phaseC (Real.pi / 2) = Complex.I := by
    rw [phaseC_eq]
    simp
  have h4 : phaseC (-(Real.pi / 4)) * phaseC (Real.pi / 2)
      = phaseC (Real.pi / 4) := by
    rw [phaseC_add]
    congr 1
    ring
  rw [rotZ_eq_diag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, ← h4, hI]

/-! ## §3. The H row — the hard single-qubit case (three π/4 rotations). -/

/-- The Hadamard matrix. -/
noncomputable def hMat : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ) / 2) • !![1, 1; 1, -1]

/-- **The H row**: the dictionary's `Z_{π/4} · X_{π/4} · Z_{π/4}` IS the
Hadamard, up to the explicit global phase `−i = e^{−iπ/2}` — the keystone
single-qubit fact for compiling H (and hence CCX = H·CCZ·H).

(NB the phase: the first draft claimed `e^{−iπ/4}` and the entrywise proof
REFUTED it — the dictionary leg is exactly the kind of fact that must be
proven, not asserted.) -/
theorem dict_H :
    rotOf (Real.pi / 4) (Pauli.toMatrix .Z)
        * rotOf (Real.pi / 4) (Pauli.toMatrix .X)
        * rotOf (Real.pi / 4) (Pauli.toMatrix .Z)
      = (-Complex.I) • hMat := by
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hs3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℝ) := by
    rw [pow_succ, hs2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [rotOf, Pauli.toMatrix, hMat, Real.cos_pi_div_four,
       Real.sin_pi_div_four, Matrix.mul_apply, Fin.sum_univ_two,
       Matrix.smul_apply]
     try ring_nf
     try simp [Complex.I_sq, hs3]
     try ring_nf)

end FormalRV.PauliRotation
