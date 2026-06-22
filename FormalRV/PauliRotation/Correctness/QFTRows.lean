/-
  FormalRV.PauliRotation.Correctness.QFTRows
  ──────────────────────────────
  THE QFT-SIDE GATE ROW: the banded inverse QFT's kept ladder gate — the
  controlled-S† on adjacent wires — has its semantic row proven by the CCZ
  recipe (three commuting Z-type diagonals folding by phase-exponent
  addition):

      `seqDenote n (csDagRots t) = e^{iπ/8} • csDagMat n t`

  where `csDagMat` is the controlled-S† diagonal (`−i` exactly on the
  both-bits-set states).  With this row, EVERY constituent of the compiled
  banded IQFT / QPE has proven semantics: H (`hGate_denote`), CS† (here),
  the bit-reversal SWAPs' CNOTs (`cnot_rots_applyNat`), and the
  modular-exponentiation oracle (`gateRotSchedule_applyNat`, since the
  oracle is Gate-IR).

  HONEST BOUNDARY (unchanged, by design): the exact QFT is NOT expressible
  at the four discrete angles — only the banded circuit compiles, and the
  dropped `m ≥ 2` tail carries the error budget already derived in
  `QFT/AQFTCompile.lean`.  Assembling these operator rows into a single
  `uc_eval`/`IQFT_matrix`-facing statement is the BaseUCom bridge, a
  separate (unstarted) leg.
-/
import FormalRV.PauliRotation.Correctness.CCZRow
import FormalRV.PauliRotation.Compiler.QFTLadder

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-- **The controlled-S† diagonal** on wires `(t, t+1)`: `−i` exactly when
both bits are set. -/
noncomputable def csDagMat (n t : Nat) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.diagonal (fun m =>
    if (m : Nat).testBit t && (m : Nat).testBit (t + 1)
    then -Complex.I else 1)

/-- **THE CS† ROW**: the banded IQFT's kept ladder gate — three π/8
rotations — denotes the controlled-S† diagonal, with the explicit global
phase `e^{iπ/8}`. -/
theorem csDag_rots_denote (n t : Nat) (ht : t + 1 < n) :
    seqDenote n (csDagRots t) = phaseC (Real.pi / 8) • csDagMat n t := by
  have htn : t < n := by omega
  show ((1 * Rot.denote n ⟨false, .piEighth, [⟨t, .z⟩, ⟨t + 1, .z⟩]⟩)
        * Rot.denote n ⟨true, .piEighth, [⟨t + 1, .z⟩]⟩)
        * Rot.denote n ⟨true, .piEighth, [⟨t, .z⟩]⟩ = _
  rw [Matrix.one_mul]
  simp only [Rot.denote, Rot.theta, RAngle.val, Bool.false_eq_true, if_false,
    if_true]
  rw [axisMat_single_z_diag n t htn, axisMat_single_z_diag n (t + 1) ht,
      axisMat_zz_diag n t (t + 1) (by omega) ht]
  simp only [rotOf_diagonal, Matrix.diagonal_mul_diagonal]
  rw [csDagMat, show phaseC (Real.pi / 8)
        • Matrix.diagonal (fun m : Fin (2 ^ n) =>
            if (m : Nat).testBit t && (m : Nat).testBit (t + 1)
            then -Complex.I else 1)
      = Matrix.diagonal (fun m : Fin (2 ^ n) =>
          phaseC (Real.pi / 8) *
            (if (m : Nat).testBit t && (m : Nat).testBit (t + 1)
             then -Complex.I else 1)) from by
        ext a b
        by_cases hab : a = b <;> simp [hab]]
  congr 1
  funext m
  have hA : (Real.cos (Real.pi / 8) : ℂ)
      - (Real.sin (Real.pi / 8) : ℂ) * Complex.I = phaseC (-(Real.pi / 8)) := by
    rw [phaseC_eq, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hB : (Real.cos (Real.pi / 8) : ℂ)
      + (Real.sin (Real.pi / 8) : ℂ) * Complex.I = phaseC (Real.pi / 8) := by
    rw [phaseC_eq]
  have hNegI : -Complex.I = phaseC (-(Real.pi / 2)) := by
    rw [phaseC_eq, Real.cos_neg, Real.sin_neg]
    simp
  simp only [Real.cos_neg, Real.sin_neg, zsgn]
  by_cases bt : (m : Nat).testBit t <;>
    by_cases bt' : (m : Nat).testBit (t + 1) <;>
      simp only [bt, bt', Bool.false_eq_true, Bool.and_true, Bool.and_false,
        if_true, reduceIte, mul_one, Complex.ofReal_neg, neg_mul,
        sub_neg_eq_add, mul_neg, neg_neg] <;>
      simp only [hA, hB, phaseC_add]
  · rw [show (-(Real.pi / 8) + -(Real.pi / 8) + -(Real.pi / 8) : ℝ)
        = Real.pi / 8 + -(Real.pi / 2) from by ring,
        ← phaseC_add, ← hNegI]
    ring
  · congr 1
    ring
  · congr 1
    ring
  · congr 1
    ring

end FormalRV.PauliRotation
