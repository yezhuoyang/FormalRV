/-
  FormalRV.PauliRotation.Correctness.CCZRow
  ─────────────────────────────
  THE CCZ ROW: the seven π/8 rotations of the dictionary's CCZ phase
  polynomial (`cczGate x y z`) denote EXACTLY the CCZ diagonal — entry `−1`
  precisely on basis states with all three bits set — with the explicit
  global phase `e^{−iπ/8}`.

  The derivation is fully structural, using the whole library at once:
    • every axis is a product of single-`Z` diagonals
      (`axisMat_cons_split` + `axisMat_single_z_diag`);
    • `rotOf` of a diagonal is a diagonal (`rotOf_diagonal`);
    • the seven diagonals multiply pointwise (`diagonal_mul_diagonal`);
    • each per-basis factor is a UNIT PHASE `e^{∓iπ/8}` and the product
      folds by exponent addition (`phaseC_add`) — the eight parity cases
      give exponent `−π/8` everywhere except the all-set case, where
      `7π/8 = −π/8 + π` flips the sign.  This is the formal content of the
      `EightTToCCZScheme` phase polynomial at the matrix level.
-/
import FormalRV.PauliRotation.Semantics.BasisAction

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-! ## §1. Diagonal infrastructure. -/

/-- `rotOf` of a diagonal matrix is the diagonal of pointwise rotations. -/
theorem rotOf_diagonal {N : Type*} [Fintype N] [DecidableEq N]
    (θ : ℝ) (d : N → ℂ) :
    rotOf θ (Matrix.diagonal d)
      = Matrix.diagonal (fun i =>
          (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I * d i) := by
  unfold rotOf
  ext i j
  by_cases h : i = j <;>
    simp [h, mul_assoc]

/-- A sorted axis splits off its head factor multiplicatively. -/
theorem axisMat_cons_split (n : Nat) (f : PFactor) (P : PauliProduct)
    (hs : sortedStrict (f :: P) = true) :
    axisMat n (f :: P) = axisMat n [f] * axisMat n P := by
  unfold axisMat
  rw [opsMat_mul_pointwise n _ _ (fun k => by
    by_cases hf : f.qubit = k
    · right
      exact hf ▸ kindFn_eq_I_of_lt_lbound (sorted_cons_lbound hs) (by omega)
    · left
      rw [kindFn_single, if_neg hf])]
  congr 1
  funext i
  rw [mulP, kindFn_single]
  by_cases hf : f.qubit = i
  · have hb : (f.qubit == i) = true := by simpa using hf
    rw [if_pos hf, if_neg (pkindToBQ_ne_I _)]
    simp [kindFn, List.find?_cons_of_pos, hb]
  · have hb : (f.qubit == i) = false := by simpa using hf
    rw [if_neg hf, if_pos rfl]
    simp [kindFn, List.find?_cons_of_neg, hb]

/-- The single-`Z` sign at a wire. -/
noncomputable def zsgn (q : Nat) (m : Fin (2 ^ n)) : ℂ :=
  if (m : Nat).testBit q then -1 else 1

/-- The `ZZ` pair axis is the product diagonal. -/
theorem axisMat_zz_diag (n x y : Nat) (hxy : x < y) (hy : y < n) :
    axisMat n [(⟨x, .z⟩ : PFactor), ⟨y, .z⟩]
      = Matrix.diagonal (fun m => zsgn x m * zsgn y m) := by
  rw [axisMat_cons_split n ⟨x, .z⟩ [⟨y, .z⟩] (by simp [sortedStrict, hxy]),
      axisMat_single_z_diag n x (by omega), axisMat_single_z_diag n y hy,
      Matrix.diagonal_mul_diagonal]
  rfl

/-- The `ZZZ` triple axis is the product diagonal. -/
theorem axisMat_zzz_diag (n x y z : Nat) (hxy : x < y) (hyz : y < z)
    (hz : z < n) :
    axisMat n [(⟨x, .z⟩ : PFactor), ⟨y, .z⟩, ⟨z, .z⟩]
      = Matrix.diagonal (fun m => zsgn x m * (zsgn y m * zsgn z m)) := by
  rw [axisMat_cons_split n ⟨x, .z⟩ [⟨y, .z⟩, ⟨z, .z⟩]
        (by simp [sortedStrict, hxy, hyz]),
      axisMat_single_z_diag n x (by omega),
      axisMat_zz_diag n y z hyz hz, Matrix.diagonal_mul_diagonal]
  rfl

/-! ## §2. Phase-factor rows. -/

theorem phase_factor_pos (θ : ℝ) :
    (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I * 1 = phaseC (-θ) := by
  rw [phaseC_eq, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem phase_factor_neg (θ : ℝ) :
    (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I * (-1) = phaseC θ := by
  rw [phaseC_eq]
  ring

/-- `−1` as the phase `e^{iπ}`. -/
theorem neg_one_eq_phaseC_pi : (-1 : ℂ) = phaseC Real.pi := by
  rw [phaseC_eq]
  simp

/-! ## §3. The CCZ matrix and THE CCZ ROW. -/

/-- **The CCZ diagonal**: `−1` exactly on the all-three-bits-set states. -/
noncomputable def cczMat (n x y z : Nat) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.diagonal (fun m =>
    if (m : Nat).testBit x && (m : Nat).testBit y && (m : Nat).testBit z
    then -1 else 1)

/-- **THE CCZ ROW**: the dictionary's seven π/8 rotations denote the CCZ
diagonal, with the explicit global phase `e^{−iπ/8}` — the matrix-level
content of the seven-rotation phase polynomial. -/
theorem ccz_rots_denote (n x y z : Nat) (hxy : x < y) (hyz : y < z)
    (hz : z < n) :
    seqDenote n ((cczGate x y z).flatten)
      = phaseC (-(Real.pi / 8)) • cczMat n x y z := by
  have hx : x < n := by omega
  have hy : y < n := by omega
  show ((((((1 * Rot.denote n ⟨false, .piEighth, [⟨x, .z⟩, ⟨y, .z⟩, ⟨z, .z⟩]⟩)
        * Rot.denote n ⟨true, .piEighth, [⟨y, .z⟩, ⟨z, .z⟩]⟩)
        * Rot.denote n ⟨true, .piEighth, [⟨x, .z⟩, ⟨z, .z⟩]⟩)
        * Rot.denote n ⟨true, .piEighth, [⟨x, .z⟩, ⟨y, .z⟩]⟩)
        * Rot.denote n ⟨false, .piEighth, [⟨z, .z⟩]⟩)
        * Rot.denote n ⟨false, .piEighth, [⟨y, .z⟩]⟩)
        * Rot.denote n ⟨false, .piEighth, [⟨x, .z⟩]⟩ = _
  rw [Matrix.one_mul]
  simp only [Rot.denote, Rot.theta, RAngle.val, Bool.false_eq_true, if_false,
    if_true]
  rw [axisMat_single_z_diag n x hx, axisMat_single_z_diag n y hy,
      axisMat_single_z_diag n z hz, axisMat_zz_diag n x y hxy hy,
      axisMat_zz_diag n x z (by omega) hz, axisMat_zz_diag n y z hyz hz,
      axisMat_zzz_diag n x y z hxy hyz hz]
  simp only [rotOf_diagonal, Matrix.diagonal_mul_diagonal]
  rw [cczMat, show phaseC (-(Real.pi / 8))
        • Matrix.diagonal (fun m : Fin (2 ^ n) =>
            if (m : Nat).testBit x && (m : Nat).testBit y && (m : Nat).testBit z
            then (-1 : ℂ) else 1)
      = Matrix.diagonal (fun m : Fin (2 ^ n) =>
          phaseC (-(Real.pi / 8)) *
            (if (m : Nat).testBit x && (m : Nat).testBit y && (m : Nat).testBit z
             then (-1 : ℂ) else 1)) from by
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
  have hNeg : -phaseC (-(Real.pi / 8)) = phaseC (-(Real.pi / 8) + Real.pi) := by
    rw [← phaseC_add, ← neg_one_eq_phaseC_pi]
    ring
  simp only [Real.cos_neg, Real.sin_neg, zsgn]
  by_cases bx : (m : Nat).testBit x <;>
    by_cases by' : (m : Nat).testBit y <;>
      by_cases bz : (m : Nat).testBit z <;>
        simp only [bx, by', bz, Bool.false_eq_true, Bool.and_true,
          Bool.and_false, if_true, reduceIte, mul_one,
          Complex.ofReal_neg, neg_mul, sub_neg_eq_add,
          mul_neg, neg_neg] <;>
        simp only [hA, hB, phaseC_add] <;>
        (try rw [hNeg]) <;>
        (congr 1
         ring)

end FormalRV.PauliRotation
