/-
  FormalRV.PauliRotation.Semantics.Core
  ────────────────────────────────
  Matrix semantics for the Pauli-rotation IR — BY REUSE of the proven
  PPM matrix layer (`PPM/Semantics/LogicalState.lean`):

    • a rotation `e^{-iθP}` denotes  `cos θ • 1 − (i sin θ) • P.toMatrix`
      (exact, since `P² = 1` — no matrix exponential needed);
    • the axis matrix comes from the EXISTING Kronecker interpretation
      `PauliString.toMatrix` through a sparse → dense bridge, inheriting the
      proven involution `toMatrix_mul_self`;
    • a layer denotes the product of its rotations; a program the
      composition of its layers (later layers act on the left).

  §2 proves the core rotation algebra over ANY involutive matrix:
  same-axis rotations MERGE angles (`rotOf_mul_same`), inverses CANCEL
  (`rotOf_cancel`), `π` rotations are the global phase `−1` (`rotOf_pi`) —
  these are the engines behind every optimization rule in `Rules.lean`.
-/
import FormalRV.PauliRotation.Syntax
import FormalRV.PPM.Semantics.LogicalState
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-! ## §1. Angle values. -/

/-- The real angle of each discrete level. -/
noncomputable def RAngle.val : RAngle → ℝ
  | .pi        => Real.pi
  | .piHalf    => Real.pi / 2
  | .piQuarter => Real.pi / 4
  | .piEighth  => Real.pi / 8

/-- The signed rotation angle of a rotation statement. -/
noncomputable def Rot.theta (r : Rot) : ℝ :=
  if r.neg then -r.angle.val else r.angle.val

/-! ## §2. The rotation operator over an involutive matrix.

For `M² = 1` the exponential `e^{-iθM}` is EXACTLY `cos θ • 1 − (i sin θ) • M`
(split the series into even/odd powers), so we take the closed form as the
definition — no analysis needed, and the algebra below is complete. -/

variable {m : Type*} [DecidableEq m]

/-- `e^{-iθM}` for involutive `M`, in closed form. -/
noncomputable def rotOf (θ : ℝ) (M : Matrix m m ℂ) : Matrix m m ℂ :=
  (Real.cos θ : ℂ) • 1 - ((Real.sin θ : ℂ) * Complex.I) • M

@[simp] theorem rotOf_zero (M : Matrix m m ℂ) : rotOf 0 M = 1 := by
  simp [rotOf]

/-- **π rotations are the global phase −1** — independent of the axis. -/
@[simp] theorem rotOf_pi (M : Matrix m m ℂ) : rotOf Real.pi M = -1 := by
  simp [rotOf]

@[simp] theorem rotOf_neg_pi (M : Matrix m m ℂ) : rotOf (-Real.pi) M = -1 := by
  simp [rotOf]

/-- **π/2 rotations are the Pauli itself, up to the global phase −i.** -/
theorem rotOf_pi_div_two (M : Matrix m m ℂ) :
    rotOf (Real.pi / 2) M = (-Complex.I) • M := by
  simp [rotOf, neg_smul]

theorem rotOf_neg_pi_div_two (M : Matrix m m ℂ) :
    rotOf (-(Real.pi / 2)) M = Complex.I • M := by
  unfold rotOf
  rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  module

/-- **The merge law**: same-axis rotations compose by ADDING angles.
This is the engine of rotation-merging optimization. -/
theorem rotOf_mul_same [Fintype m] {M : Matrix m m ℂ} (hM : M * M = 1) (θ φ : ℝ) :
    rotOf θ M * rotOf φ M = rotOf (θ + φ) M := by
  unfold rotOf
  rw [Real.cos_add, Real.sin_add]
  push_cast
  rw [sub_mul, mul_sub, mul_sub]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hM, smul_smul]
  ring_nf
  rw [Complex.I_sq]
  module

/-- **The cancellation law**: a rotation and its inverse compose to the
identity. -/
theorem rotOf_cancel [Fintype m] {M : Matrix m m ℂ} (hM : M * M = 1) (θ : ℝ) :
    rotOf θ M * rotOf (-θ) M = 1 := by
  rw [rotOf_mul_same hM, add_neg_cancel, rotOf_zero]

/-- **Commuting axes give commuting rotations** (any angles) — the engine
behind parallel layers and rotation reordering. -/
theorem rotOf_comm [Fintype m] {M N : Matrix m m ℂ} (h : M * N = N * M) (θ φ : ℝ) :
    rotOf θ M * rotOf φ N = rotOf φ N * rotOf θ M := by
  unfold rotOf
  rw [sub_mul, mul_sub, mul_sub, sub_mul, mul_sub, mul_sub]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, h]
  ring_nf
  module

/-! ## §3. Sparse axis → dense string → matrix (the reuse bridge). -/

/-- A sparse kind as a dense single-qubit Pauli (`BQCode` enum, the one with
the proven matrix interpretation). -/
def pkindToBQ : PKind → Pauli
  | .x => .X
  | .y => .Y
  | .z => .Z

/-- The dense Pauli a sparse axis applies at qubit `i` (`I` off-support). -/
def kindFn (P : PauliProduct) (i : Nat) : Pauli :=
  match P.find? (fun f => f.qubit == i) with
  | some f => pkindToBQ f.kind
  | none   => Pauli.I

/-- The dense ops list of a sparse axis at width `n`. -/
def toDenseOps (n : Nat) (P : PauliProduct) : PauliString :=
  (List.range n).map (kindFn P)

@[simp] theorem toDenseOps_length (n : Nat) (P : PauliProduct) :
    (toDenseOps n P).length = n := by
  simp [toDenseOps]

/-- The `2^n × 2^n` Kronecker interpretation of a dense qubit-indexed Pauli
assignment — the same recursion shape as the proven
`BQCode.PauliString.toMatrix` (qubit 0 is the innermost factor), but indexed
by a FUNCTION `Nat → Pauli`, so that two axes can be inducted on
simultaneously without dependent-length friction. -/
noncomputable def opsMat : (n : Nat) → (Nat → Pauli) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0,     _ => 1
  | n + 1, f =>
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (opsMat n (fun i => f (i + 1))) (f 0).toMatrix)

/-- The axis as a `2^n × 2^n` matrix. -/
noncomputable def axisMat (n : Nat) (P : PauliProduct) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  opsMat n (kindFn P)

/-- `opsMat` is an involution (each Kronecker factor squares to `1`, by the
proven single-qubit `Pauli.toMatrix_mul_self`). -/
theorem opsMat_mul_self (n : Nat) (f : Nat → Pauli) :
    opsMat n f * opsMat n f = 1 := by
  induction n generalizing f with
  | zero => exact one_mul 1
  | succ n ih =>
      show Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (· * · : ℂ → ℂ → ℂ)
            (opsMat n (fun i => f (i + 1))) (f 0).toMatrix)
        * Matrix.reindex finProdFinEquiv finProdFinEquiv
            (Matrix.kroneckerMap (· * ·)
              (opsMat n (fun i => f (i + 1))) (f 0).toMatrix)
        = 1
      rw [Matrix.reindex_apply,
          Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
          ← Matrix.mul_kronecker_mul, ih, Pauli.toMatrix_mul_self,
          Matrix.kroneckerMap_one_one (· * ·) zero_mul mul_zero (one_mul 1)]
      exact Matrix.submatrix_one _ finProdFinEquiv.symm.injective

/-- The axis matrix is an involution. -/
theorem axisMat_mul_self (n : Nat) (P : PauliProduct) :
    axisMat n P * axisMat n P = 1 :=
  opsMat_mul_self n (kindFn P)

/-! ## §4. Denotation of rotations, layers, programs. -/

/-- One rotation as a `2^n × 2^n` operator. -/
noncomputable def Rot.denote (n : Nat) (r : Rot) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  rotOf r.theta (axisMat n r.axis)

/-- A layer as the product of its rotations (well-formed layers commute
pairwise, so the listed order is one valid serialization). -/
noncomputable def RotLayer.denote (n : Nat) (L : RotLayer) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (L.map (Rot.denote n)).prod

/-- A program as the composition of its layers.  CONVENTION: programs
execute left-to-right, so later layers multiply on the LEFT
(`⟦L :: p⟧ = ⟦p⟧ ⬝ ⟦L⟧`, matching `(U_k ⋯ U_1)ψ`). -/
noncomputable def RotProg.denote (n : Nat) : RotProg → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | []     => 1
  | L :: p => RotProg.denote n p * RotLayer.denote n L

/-! ## §5. First denotation laws. -/

@[simp] theorem RotLayer.denote_nil (n : Nat) : RotLayer.denote n [] = 1 := rfl

theorem RotLayer.denote_cons (n : Nat) (r : Rot) (L : RotLayer) :
    RotLayer.denote n (r :: L) = Rot.denote n r * RotLayer.denote n L := by
  simp [RotLayer.denote]

theorem RotProg.denote_append (n : Nat) (p q : RotProg) :
    RotProg.denote n (p ++ q) = RotProg.denote n q * RotProg.denote n p := by
  induction p with
  | nil => simp [RotProg.denote]
  | cons L t ih =>
      show RotProg.denote n (t ++ q) * RotLayer.denote n L = _
      rw [ih, Matrix.mul_assoc]
      rfl

/-- **Same-axis merge at the denotation level**: two rotations about the
same axis compose into the angle-sum rotation. -/
theorem Rot.denote_mul_same_axis (n : Nat) (r s : Rot) (h : r.axis = s.axis) :
    Rot.denote n r * Rot.denote n s
      = rotOf (r.theta + s.theta) (axisMat n r.axis) := by
  unfold Rot.denote
  rw [h, rotOf_mul_same (axisMat_mul_self n s.axis)]

/-- The angle-flipped inverse of a rotation. -/
def Rot.inv (r : Rot) : Rot := { r with neg := !r.neg }

@[simp] theorem Rot.inv_axis (r : Rot) : r.inv.axis = r.axis := rfl

theorem Rot.inv_theta (r : Rot) : r.inv.theta = -r.theta := by
  cases r with
  | mk neg angle axis => cases neg <;> simp [Rot.theta, Rot.inv]

/-- **Cancellation at the denotation level**: `r · r⁻¹ = 1`. -/
theorem Rot.denote_mul_inv (n : Nat) (r : Rot) :
    Rot.denote n r * Rot.denote n r.inv = 1 := by
  rw [Rot.denote_mul_same_axis n r r.inv rfl.symm.symm, Rot.inv_theta,
      add_neg_cancel, rotOf_zero]

/-- **π rotations are global phases at the denotation level** — whatever the
axis, a `±π` rotation denotes `−1`. -/
theorem Rot.denote_pi (n : Nat) (r : Rot) (h : r.angle = .pi) :
    Rot.denote n r = -1 := by
  unfold Rot.denote Rot.theta
  rw [h]
  cases hneg : r.neg <;> simp [RAngle.val]

end FormalRV.PauliRotation
