/-
  FormalRV.Framework.UnitaryOps — circuit operations beyond `useq`.

  Lean translation of `SQIR/SQIR/UnitaryOps.v` (1482 LOC of Coq).
  This file builds on `Framework.UnitarySem`. SQIR's UnitaryOps.v contains:
    - inversion (`invert`)
    - control / classical projection
    - iteration (`niter`)
    - parallel composition (`npar`)
    - reversal of qubits

  Many lemmas in this file depend on `pad_ctrl` (currently sorried) and
  on per-gate matrix equivalences. Where dependencies aren't filled, we
  state the theorem and `sorry` it with a clear note.

  Status: scaffolding. Each translation goes in dependency order.
-/
import FormalRV.Core.UnitarySem

namespace FormalRV.Framework

namespace BaseUCom
open BaseUnitary

/-! ## Inversion (translation of `Fixpoint invert` from UnitaryOps.v lines 17-23)

    For each base unitary, `invert` produces the matrix-adjoint:
    - `R θ ϕ λ` → `R (-θ) (-λ) (-ϕ)` (rotation adjoint formula)
    - `CNOT` → `CNOT` (CNOT is self-adjoint)
    - sequential composition reverses + inverts each piece. -/

/-- Invert a `BaseUCom`, producing the unitary that undoes it. -/
noncomputable def invert {dim : Nat} : BaseUCom dim → BaseUCom dim
  | UCom.seq c₁ c₂              => UCom.seq (invert c₂) (invert c₁)
  | UCom.app1 (R θ ϕ lam) n     => UCom.app1 (R (-θ) (-lam) (-ϕ)) n
  | UCom.app2 BaseUnitary.CNOT m n => UCom.app2 BaseUnitary.CNOT m n
  | UCom.app3 _ _ _ _           => SKIP   -- no 3-qubit primitives in BaseUnitary

/-- Inverting CNOT is CNOT (CNOT is self-adjoint, so invert is the identity
    on the syntactic level for this gate).
    SQIR/UnitaryOps.v line 57. -/
@[simp] theorem invert_CNOT {dim : Nat} (m n : Nat) :
    invert (CNOT m n : BaseUCom dim) = CNOT m n := rfl

/-- Inverting a single-qubit `app1 (R θ ϕ lam) n` syntactically rewrites
    parameters as `R (-θ) (-lam) (-ϕ)`. Pure definitional unfolding —
    useful as a `@[simp]` lemma for circuit normalization. -/
@[simp] theorem invert_app1 {dim : Nat} (θ ϕ lam : ℝ) (n : Nat) :
    invert (UCom.app1 (R θ ϕ lam) n : BaseUCom dim)
      = UCom.app1 (R (-θ) (-lam) (-ϕ)) n := rfl

/-- Inverting a sequence reverses the order. -/
@[simp] theorem invert_seq {dim : Nat} (c₁ c₂ : BaseUCom dim) :
    invert (UCom.seq c₁ c₂) = UCom.seq (invert c₂) (invert c₁) := rfl

/-- WellTyped of a sequence is iff WellTyped of both pieces. Useful as
    a simp normalization: reduces structural WellTyped goals on seq
    to component goals. -/
theorem WellTyped_seq_iff {dim : Nat} (c1 c2 : BaseUCom dim) :
    UCom.WellTyped dim (UCom.seq c1 c2)
      ↔ UCom.WellTyped dim c1 ∧ UCom.WellTyped dim c2 := by
  constructor
  · intro h
    cases h with
    | seq h1 h2 => exact ⟨h1, h2⟩
  · intro ⟨h1, h2⟩
    exact UCom.WellTyped.seq h1 h2

/-- WellTyped of a 1-qubit application is iff the qubit index is in range. -/
theorem WellTyped_app1_iff {dim : Nat} (u : BaseUnitary 1) (n : Nat) :
    UCom.WellTyped dim (UCom.app1 u n : BaseUCom dim) ↔ n < dim := by
  constructor
  · intro h; cases h with | app1 hn => exact hn
  · intro hn; exact UCom.WellTyped.app1 hn

/-- WellTyped of a 2-qubit application is iff both indices are in range
    and they are distinct. -/
theorem WellTyped_app2_iff {dim : Nat} (u : BaseUnitary 2) (m n : Nat) :
    UCom.WellTyped dim (UCom.app2 u m n : BaseUCom dim)
      ↔ m < dim ∧ n < dim ∧ m ≠ n := by
  constructor
  · intro h; cases h with | app2 hm hn hmn => exact ⟨hm, hn, hmn⟩
  · intro ⟨hm, hn, hmn⟩; exact UCom.WellTyped.app2 hm hn hmn

/-- `X n` is WellTyped when `n < dim`. -/
theorem X_well_typed {dim : Nat} (n : Nat) (h : n < dim) :
    UCom.WellTyped dim (X n : BaseUCom dim) :=
  UCom.WellTyped.app1 h

/-- `Y n` is WellTyped when `n < dim`. -/
theorem Y_well_typed {dim : Nat} (n : Nat) (h : n < dim) :
    UCom.WellTyped dim (Y n : BaseUCom dim) :=
  UCom.WellTyped.app1 h

/-- `Z n` is WellTyped when `n < dim`. -/
theorem Z_well_typed {dim : Nat} (n : Nat) (h : n < dim) :
    UCom.WellTyped dim (Z n : BaseUCom dim) :=
  UCom.WellTyped.app1 h

/-- `H n` is WellTyped when `n < dim`. -/
theorem H_well_typed {dim : Nat} (n : Nat) (h : n < dim) :
    UCom.WellTyped dim (H n : BaseUCom dim) :=
  UCom.WellTyped.app1 h

/-- `T n` is WellTyped when `n < dim`. -/
theorem T_well_typed {dim : Nat} (n : Nat) (h : n < dim) :
    UCom.WellTyped dim (T n : BaseUCom dim) :=
  UCom.WellTyped.app1 h

/-- `TDAG n` is WellTyped when `n < dim`. -/
theorem TDAG_well_typed {dim : Nat} (n : Nat) (h : n < dim) :
    UCom.WellTyped dim (TDAG n : BaseUCom dim) :=
  UCom.WellTyped.app1 h

/-- `S n` is WellTyped when `n < dim`. -/
theorem S_well_typed {dim : Nat} (n : Nat) (h : n < dim) :
    UCom.WellTyped dim (S n : BaseUCom dim) :=
  UCom.WellTyped.app1 h

/-- `SDAG n` is WellTyped when `n < dim`. -/
theorem SDAG_well_typed {dim : Nat} (n : Nat) (h : n < dim) :
    UCom.WellTyped dim (SDAG n : BaseUCom dim) :=
  UCom.WellTyped.app1 h

/-- `ID n` is WellTyped when `n < dim`. -/
theorem ID_well_typed {dim : Nat} (n : Nat) (h : n < dim) :
    UCom.WellTyped dim (ID n : BaseUCom dim) :=
  UCom.WellTyped.app1 h

/-- `Rz θ n` is WellTyped when `n < dim` (parametric). -/
theorem Rz_well_typed {dim : Nat} (θ : ℝ) (n : Nat) (h : n < dim) :
    UCom.WellTyped dim (Rz θ n : BaseUCom dim) :=
  UCom.WellTyped.app1 h

/-- `CNOT m n` is WellTyped when both qubits are in range and distinct. -/
theorem CNOT_well_typed {dim : Nat} (m n : Nat)
    (hm : m < dim) (hn : n < dim) (hmn : m ≠ n) :
    UCom.WellTyped dim (CNOT m n : BaseUCom dim) :=
  UCom.WellTyped.app2 hm hn hmn

/-- `SWAP m n` is WellTyped when both qubits are in range and distinct.
    SWAP unfolds to a 3-CNOT chain — apply WellTyped_seq_iff repeatedly
    plus CNOT_well_typed for each piece. -/
theorem SWAP_well_typed {dim : Nat} (m n : Nat)
    (hm : m < dim) (hn : n < dim) (hmn : m ≠ n) :
    UCom.WellTyped dim (SWAP m n : BaseUCom dim) := by
  show UCom.WellTyped dim (UCom.seq (CNOT m n) (UCom.seq (CNOT n m) (CNOT m n)))
  refine UCom.WellTyped.seq (CNOT_well_typed _ _ hm hn hmn) ?_
  refine UCom.WellTyped.seq (CNOT_well_typed _ _ hn hm (Ne.symm hmn)) ?_
  exact CNOT_well_typed _ _ hm hn hmn

/-- `CCX a b c` (Toffoli, 15-gate decomposition) is WellTyped when all
    three qubits are in range and pairwise distinct. -/
theorem CCX_well_typed {dim : Nat} (a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    UCom.WellTyped dim (CCX a b c : BaseUCom dim) := by
  refine UCom.WellTyped.seq ?_ (UCom.WellTyped.seq ?_ (UCom.WellTyped.seq ?_ ?_))
  · -- s₁: H c ; CNOT b c ; T† c ; CNOT a c
    refine UCom.WellTyped.seq (H_well_typed _ hc) ?_
    refine UCom.WellTyped.seq (CNOT_well_typed _ _ hb hc hbc) ?_
    refine UCom.WellTyped.seq (TDAG_well_typed _ hc) ?_
    exact CNOT_well_typed _ _ ha hc hac
  · -- s₂: T c ; CNOT b c ; T† c ; CNOT a c
    refine UCom.WellTyped.seq (T_well_typed _ hc) ?_
    refine UCom.WellTyped.seq (CNOT_well_typed _ _ hb hc hbc) ?_
    refine UCom.WellTyped.seq (TDAG_well_typed _ hc) ?_
    exact CNOT_well_typed _ _ ha hc hac
  · -- s₃: CNOT a b ; T† b ; CNOT a b
    refine UCom.WellTyped.seq (CNOT_well_typed _ _ ha hb hab) ?_
    refine UCom.WellTyped.seq (TDAG_well_typed _ hb) ?_
    exact CNOT_well_typed _ _ ha hb hab
  · -- s₄: T a ; T b ; T c ; H c
    refine UCom.WellTyped.seq (T_well_typed _ ha) ?_
    refine UCom.WellTyped.seq (T_well_typed _ hb) ?_
    refine UCom.WellTyped.seq (T_well_typed _ hc) ?_
    exact H_well_typed _ hc

/-- `CCZ a b c` (controlled-controlled-Z, 13-gate decomposition: CCX
    without the framing Hadamards) is WellTyped when all three qubits
    are in range and pairwise distinct. -/
theorem CCZ_well_typed {dim : Nat} (a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    UCom.WellTyped dim (CCZ a b c : BaseUCom dim) := by
  refine UCom.WellTyped.seq ?_ (UCom.WellTyped.seq ?_ (UCom.WellTyped.seq ?_ ?_))
  · -- s₁: CNOT b c ; T† c ; CNOT a c
    refine UCom.WellTyped.seq (CNOT_well_typed _ _ hb hc hbc) ?_
    refine UCom.WellTyped.seq (TDAG_well_typed _ hc) ?_
    exact CNOT_well_typed _ _ ha hc hac
  · -- s₂: T c ; CNOT b c ; T† c ; CNOT a c
    refine UCom.WellTyped.seq (T_well_typed _ hc) ?_
    refine UCom.WellTyped.seq (CNOT_well_typed _ _ hb hc hbc) ?_
    refine UCom.WellTyped.seq (TDAG_well_typed _ hc) ?_
    exact CNOT_well_typed _ _ ha hc hac
  · -- s₃: CNOT a b ; T† b ; CNOT a b
    refine UCom.WellTyped.seq (CNOT_well_typed _ _ ha hb hab) ?_
    refine UCom.WellTyped.seq (TDAG_well_typed _ hb) ?_
    exact CNOT_well_typed _ _ ha hb hab
  · -- s₄: T a ; T b ; T c
    refine UCom.WellTyped.seq (T_well_typed _ ha) ?_
    refine UCom.WellTyped.seq (T_well_typed _ hb) ?_
    exact T_well_typed _ hc

/-- `invert` preserves WellTyped: if c is WellTyped on dim qubits then so
    is invert c. The app3 case (no 3-qubit primitives in BaseUnitary) maps
    to SKIP which needs 0 < dim — derived from any of the qubit indices. -/
theorem WellTyped_invert {dim : Nat} (c : BaseUCom dim)
    (h : UCom.WellTyped dim c) : UCom.WellTyped dim (invert c) := by
  induction c with
  | seq c1 c2 ih1 ih2 =>
    cases h with
    | seq h1 h2 => exact UCom.WellTyped.seq (ih2 h2) (ih1 h1)
  | app1 u n =>
    cases h with
    | app1 hn =>
      cases u
      exact UCom.WellTyped.app1 hn
  | app2 u m n =>
    cases h with
    | app2 hm hn hmn =>
      cases u
      exact UCom.WellTyped.app2 hm hn hmn
  | app3 _ m n p =>
    cases h with
    | app3 hm _ _ _ _ _ =>
      exact UCom.WellTyped.app1 (Nat.lt_of_le_of_lt (Nat.zero_le m) hm)

/-- Inverting a Z-rotation negates the angle. Matrix-level equivalence
    since `invert (R 0 0 θ) = R (-0) (-θ) (-0)` syntactically while
    `Rz (-θ) = R 0 0 (-θ)` — the two rotations agree pointwise (both
    diag(1, exp(-iθ))). SQIR/UnitaryOps.v: `invert_Rz`. -/
theorem invert_Rz {dim : Nat} (θ : ℝ) (q : Nat) :
    UCom.equiv (invert (Rz θ q : BaseUCom dim)) (Rz (-θ) q) := by
  show pad_u dim q (rotation (-0) (-θ) (-0)) = pad_u dim q (rotation 0 0 (-θ))
  congr 1
  unfold rotation
  ext i j
  fin_cases i <;> fin_cases j <;> simp [neg_zero]

/-- Inverting T gives T† at the matrix level. -/
theorem invert_T {dim : Nat} (q : Nat) :
    UCom.equiv (invert (T q : BaseUCom dim)) (TDAG q) := by
  show pad_u dim q (rotation (-0) (-(Real.pi/4)) (-0))
        = pad_u dim q (rotation 0 0 (-(Real.pi/4)))
  congr 1
  unfold rotation
  ext i j
  fin_cases i <;> fin_cases j <;> simp [neg_zero]

/-- Inverting S gives S† at the matrix level. -/
theorem invert_S {dim : Nat} (q : Nat) :
    UCom.equiv (invert (S q : BaseUCom dim)) (SDAG q) := by
  show pad_u dim q (rotation (-0) (-(Real.pi/2)) (-0))
        = pad_u dim q (rotation 0 0 (-(Real.pi/2)))
  congr 1
  unfold rotation
  ext i j
  fin_cases i <;> fin_cases j <;> simp [neg_zero]

/-- Inverting T† gives T at the matrix level (the reverse direction). -/
theorem invert_TDAG {dim : Nat} (q : Nat) :
    UCom.equiv (invert (TDAG q : BaseUCom dim)) (T q) := by
  show pad_u dim q (rotation (-0) (-(-(Real.pi/4))) (-0))
        = pad_u dim q (rotation 0 0 (Real.pi/4))
  congr 1
  unfold rotation
  ext i j
  fin_cases i <;> fin_cases j <;> simp [neg_zero]

/-- Inverting S† gives S at the matrix level. -/
theorem invert_SDAG {dim : Nat} (q : Nat) :
    UCom.equiv (invert (SDAG q : BaseUCom dim)) (S q) := by
  show pad_u dim q (rotation (-0) (-(-(Real.pi/2))) (-0))
        = pad_u dim q (rotation 0 0 (Real.pi/2))
  congr 1
  unfold rotation
  ext i j
  fin_cases i <;> fin_cases j <;> simp [neg_zero]

/-- Inverting SKIP is SKIP — the trivial 0-angle rotation is its own inverse
    (no matrix-equiv needed; directly syntactic via neg_zero). -/
@[simp] theorem invert_SKIP {dim : Nat} : invert (SKIP : BaseUCom dim) = SKIP := by
  show UCom.app1 (R (-0) (-0) (-0)) 0 = UCom.app1 (R 0 0 0) 0
  simp only [neg_zero]

/-- `invert (SKIP ; c) = (invert c) ; SKIP` — direct corollary of invert_seq + invert_SKIP. -/
@[simp] theorem invert_seq_SKIP_l {dim : Nat} (c : BaseUCom dim) :
    invert (UCom.seq SKIP c) = UCom.seq (invert c) SKIP := by
  rw [invert_seq, invert_SKIP]

/-- `invert (c ; SKIP) = SKIP ; (invert c)` — direct corollary of invert_seq + invert_SKIP. -/
@[simp] theorem invert_seq_SKIP_r {dim : Nat} (c : BaseUCom dim) :
    invert (UCom.seq c SKIP) = UCom.seq SKIP (invert c) := by
  rw [invert_seq, invert_SKIP]

/-- `invert (ID q) ≡ ID q` — the identity gate is its own inverse at the
    matrix level. ID q is just SKIP at qubit q (rotation 0 0 0), and
    invert maps (R 0 0 0) → (R (-0) (-0) (-0)) which simp closes via neg_zero. -/
theorem invert_ID {dim : Nat} (q : Nat) :
    UCom.equiv (invert (ID q : BaseUCom dim)) (ID q) := by
  show pad_u dim q (rotation (-0) (-0) (-0)) = pad_u dim q (rotation 0 0 0)
  simp only [neg_zero]

/-- `invert (Z q) ≡ Z q` — Z is its own inverse since Z² = I (involution).
    At the matrix level, both sides reduce to σz: the LHS rotation
    `(-0) (-π) (-0)` is diag(1, exp(-iπ)) = diag(1, -1), the RHS rotation
    `0 0 π` is diag(1, exp(iπ)) = diag(1, -1). -/
theorem invert_Z {dim : Nat} (q : Nat) :
    UCom.equiv (invert (Z q : BaseUCom dim)) (Z q) := by
  show pad_u dim q (rotation (-0) (-Real.pi) (-0))
        = pad_u dim q (rotation 0 0 Real.pi)
  congr 1
  rw [neg_zero]
  unfold rotation
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Complex.exp_neg, Complex.exp_pi_mul_I, Real.cos_zero,
          Real.sin_zero, Complex.ofReal_zero, mul_zero, zero_mul,
          Complex.exp_zero]

/-- `invert (X q) ≡ X q` — X is its own inverse (involution: X² = I).
    Both rotations evaluate to σx; the off-diagonal entries match via
    `sin(-π/2) = -sin(π/2)` and the exp factors cancel via
    `Complex.exp_pi_mul_I` / `Complex.exp_neg`. -/
theorem invert_X {dim : Nat} (q : Nat) :
    UCom.equiv (invert (X q : BaseUCom dim)) (X q) := by
  show pad_u dim q (rotation (-Real.pi) (-Real.pi) (-0))
        = pad_u dim q (rotation Real.pi 0 Real.pi)
  congr 1
  rw [neg_zero]
  unfold rotation
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Complex.exp_neg, Complex.exp_pi_mul_I, Real.cos_neg,
          Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two,
          Complex.ofReal_zero, Complex.exp_zero,
          Complex.ofReal_neg, neg_div]

/-- `invert (Y q) ≡ Y q` — Y is its own inverse (involution: Y² = I).
    Both rotations evaluate to σy. The off-diagonal entries match
    via `sin(-π/2) = -1` combined with `exp(-iπ/2) = -i`. -/
theorem invert_Y {dim : Nat} (q : Nat) :
    UCom.equiv (invert (Y q : BaseUCom dim)) (Y q) := by
  show pad_u dim q (rotation (-Real.pi) (-(Real.pi/2)) (-(Real.pi/2)))
        = pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))
  congr 1
  unfold rotation
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Complex.exp_neg, Complex.exp_pi_mul_I,
          Complex.exp_pi_div_two_mul_I, Real.cos_neg, Real.sin_neg,
          Real.cos_pi_div_two, Real.sin_pi_div_two,
          Complex.ofReal_neg, neg_div]

/-- `invert (H q) ≡ H q` — Hadamard is its own inverse (involution: H² = I).
    Both rotations evaluate to hMatrix. Unlike X/Y/Z, all four matrix
    entries are non-zero (±1/√2), so each cell needs `cos(π/4)` /
    `sin(π/4)` reductions plus the exp factor cancellations. -/
theorem invert_H {dim : Nat} (q : Nat) :
    UCom.equiv (invert (H q : BaseUCom dim)) (H q) := by
  show pad_u dim q (rotation (-(Real.pi/2)) (-Real.pi) (-0))
        = pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
  congr 1
  rw [neg_zero]
  unfold rotation
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Complex.exp_neg, Complex.exp_pi_mul_I, Real.cos_neg,
          Real.sin_neg, Complex.ofReal_zero, Complex.exp_zero,
          Complex.ofReal_neg, neg_div]

/-- Involutivity of `invert`: `invert (invert c) = c` syntactically.
    `BaseUnitary 3` has no constructors, so the `app3` case is vacuous;
    the other cases reduce by recursion (`seq` via the IH, `app1` via
    `neg_neg`, `app2` via `cases u`). -/
theorem invert_invert {dim : Nat} (c : BaseUCom dim) :
    invert (invert c) = c := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ => rw [invert_seq, invert_seq, ih₁, ih₂]
  | app1 u n =>
      cases u with
      | R θ ϕ lam => simp [invert_app1, neg_neg]
  | app2 u m n => cases u; rfl
  | app3 u _ _ _ => cases u


/-! ## Iteration: apply a circuit n times in sequence (`niter`).

    SQIR's `niter`: applied N times = `c ; c ; ... ; c`. Used in many
    SQIR examples (Grover iteration, etc.). -/

/-- `niter n c` applies circuit `c` exactly `n` times in sequence.
    Base case: `niter 0 c = SKIP`. -/
def niter {dim : Nat} (n : Nat) (c : BaseUCom dim) : BaseUCom dim :=
  match n with
  | 0     => SKIP
  | k + 1 => UCom.seq c (niter k c)

@[simp] theorem niter_zero {dim : Nat} (c : BaseUCom dim) : niter 0 c = SKIP := rfl

@[simp] theorem niter_succ {dim : Nat} (n : Nat) (c : BaseUCom dim) :
    niter (n + 1) c = UCom.seq c (niter n c) := rfl

/-- Definitional unfolding of `uc_eval` on `niter 0`: equals SKIP's matrix. -/
theorem uc_eval_niter_zero {dim : Nat} (c : BaseUCom dim) :
    uc_eval (niter 0 c) = uc_eval (SKIP : BaseUCom dim) := rfl

/-- Definitional unfolding of `uc_eval` on `niter (n+1)`. -/
theorem uc_eval_niter_succ {dim : Nat} (n : Nat) (c : BaseUCom dim) :
    uc_eval (niter (n + 1) c) = uc_eval (niter n c) * uc_eval c := rfl

/-- `niter 1 c ≡ c ; SKIP`. (And `c ; SKIP ≡ c` by `SKIP_id_r`.) -/
theorem niter_one_eq {dim : Nat} (c : BaseUCom dim) :
    niter 1 c = UCom.seq c SKIP := rfl

/-- `niter 1 c ≡ c` (under `UCom.equiv`). Combines `niter_one_eq` with
    `SKIP_id_r` (the right-skip elimination). -/
theorem niter_one {dim : Nat} (c : BaseUCom dim) (h : 0 < dim) :
    UCom.equiv (niter 1 c) c := by
  show uc_eval (niter 1 c) = uc_eval c
  rw [niter_one_eq]
  exact SKIP_id_r c h

/-- `uc_eval (niter n c) = (uc_eval c)^n` — n-fold iteration is the
    n-th matrix power. Note: at `n=0` returns the SKIP matrix
    (`pad_u dim 0 σi`), which equals `(uc_eval c)^0 = 1` only when
    `dim > 0`. For unrestricted `n`, this requires `0 < dim`. -/
theorem uc_eval_niter {dim : Nat} (h : 0 < dim) (n : Nat) (c : BaseUCom dim) :
    uc_eval (niter n c) = (uc_eval c)^n := by
  induction n with
  | zero =>
      show uc_eval (SKIP : BaseUCom dim) = 1
      show pad_u dim 0 (rotation 0 0 0) = 1
      rw [rotation_I, pad_u_id h]
  | succ k ih =>
      show uc_eval (UCom.seq c (niter k c)) = _
      rw [show uc_eval (UCom.seq c (niter k c)) = uc_eval (niter k c) * uc_eval c from rfl]
      rw [ih, pow_succ]

/-- `niter k1 c ; niter k2 c ≡ niter (k1 + k2) c` — niter is additive
    in the iteration count, mirroring `pow_add` at the matrix level.
    Requires `0 < dim` since the n=0 base of niter relies on `pad_u_id`. -/
theorem niter_add {dim : Nat} (k1 k2 : Nat) (c : BaseUCom dim) (hd : 0 < dim) :
    UCom.equiv (UCom.seq (niter k2 c) (niter k1 c)) (niter (k1 + k2) c) := by
  show uc_eval (niter k1 c) * uc_eval (niter k2 c) = uc_eval (niter (k1 + k2) c)
  rw [uc_eval_niter hd k1, uc_eval_niter hd k2, uc_eval_niter hd (k1 + k2),
      pow_add]

/-- `niter (k1 * k2) c ≡ niter k2 (niter k1 c)` — composing iterations
    matches `pow_mul` at the matrix level: A^(k1*k2) = (A^k1)^k2. -/
theorem niter_mul {dim : Nat} (k1 k2 : Nat) (c : BaseUCom dim) (hd : 0 < dim) :
    UCom.equiv (niter (k1 * k2) c) (niter k2 (niter k1 c)) := by
  show uc_eval (niter (k1 * k2) c) = uc_eval (niter k2 (niter k1 c))
  rw [uc_eval_niter hd, uc_eval_niter hd, uc_eval_niter hd, ← pow_mul]

/-- `niter` preserves equivalence: if c ≡ c' then niter k c ≡ niter k c'.
    Direct congruence — uc_eval (niter k c) = (uc_eval c)^k depends only
    on uc_eval c, so equal evals give equal powers. -/
theorem niter_congr {dim : Nat} (k : Nat) (c c' : BaseUCom dim)
    (h : UCom.equiv c c') (hd : 0 < dim) :
    UCom.equiv (niter k c) (niter k c') := by
  show uc_eval (niter k c) = uc_eval (niter k c')
  rw [uc_eval_niter hd, uc_eval_niter hd, h]

/-- `niter k c` is WellTyped on dim qubits when `c` is WellTyped and `0 < dim`.
    The 0 < dim is needed for the niter 0 = SKIP base case. -/
theorem niter_well_typed {dim : Nat} (k : Nat) (c : BaseUCom dim)
    (hc : UCom.WellTyped dim c) (hd : 0 < dim) :
    UCom.WellTyped dim (niter k c) := by
  induction k with
  | zero => exact UCom.WellTyped.app1 hd
  | succ k ih => exact UCom.WellTyped.seq hc ih

/-- Generic template: if `niter 2 c ≡ ID q`, then `niter 3 c ≡ c`.
    Lifts X³=X, Y³=Y, Z³=Z, H³=H to a single parametric pattern.
    Proof: niter 3 c = c ; niter 2 c, so uc_eval = uc_eval(niter 2 c) ·
    uc_eval c = 1 · uc_eval c = uc_eval c (via the hypothesis). -/
theorem niter_three_self_inv_eq_self {dim : Nat} (q : Nat) (hq : q < dim)
    (c : BaseUCom dim) (h : UCom.equiv (niter 2 c) (ID q)) :
    UCom.equiv (niter 3 c) c := by
  show uc_eval (niter 2 c) * uc_eval c = uc_eval c
  rw [show uc_eval (niter 2 c) = uc_eval (ID q : BaseUCom dim) from h]
  show pad_u dim q (rotation 0 0 0) * uc_eval c = uc_eval c
  rw [rotation_I, pad_u_id hq, Matrix.one_mul]


/-- `niter k (Rz θ q) ≡ Rz (k·θ) q` — iterating a Z-rotation k times gives
    a single Z-rotation by k·θ. Parametric BaseUCom-level lift of
    `rotation_Rz_pow`. Requires `q < dim` (else pad_u_pow doesn't apply). -/
theorem niter_Rz {dim : Nat} (q : Nat) (h : q < dim) (θ : ℝ) (k : Nat) :
    UCom.equiv (niter k (Rz θ q : BaseUCom dim)) (Rz (k * θ) q) := by
  have hd : 0 < dim := q.zero_le.trans_lt h
  show uc_eval (niter k (Rz θ q)) = uc_eval (Rz (k * θ) q : BaseUCom dim)
  rw [uc_eval_niter hd k]
  show (pad_u dim q (rotation 0 0 θ))^k = pad_u dim q (rotation 0 0 (k * θ))
  rw [← pad_u_pow h, rotation_Rz_pow]

/-- `niter k (T q) ≡ Rz (k·π/4) q` — T iteration as a single Z-rotation. -/
theorem niter_T_eq_Rz {dim : Nat} (q : Nat) (h : q < dim) (k : Nat) :
    UCom.equiv (niter k (T q : BaseUCom dim)) (Rz (k * (Real.pi/4)) q) :=
  niter_Rz q h (Real.pi/4) k

/-- `niter k (TDAG q) ≡ Rz (-k·π/4) q` — T† iteration as a single Z-rotation. -/
theorem niter_TDAG_eq_Rz {dim : Nat} (q : Nat) (h : q < dim) (k : Nat) :
    UCom.equiv (niter k (TDAG q : BaseUCom dim)) (Rz (k * (-(Real.pi/4))) q) :=
  niter_Rz q h (-(Real.pi/4)) k

/-- `niter k (S q) ≡ Rz (k·π/2) q` — S iteration as a single Z-rotation. -/
theorem niter_S_eq_Rz {dim : Nat} (q : Nat) (h : q < dim) (k : Nat) :
    UCom.equiv (niter k (S q : BaseUCom dim)) (Rz (k * (Real.pi/2)) q) :=
  niter_Rz q h (Real.pi/2) k

/-- `niter k (SDAG q) ≡ Rz (-k·π/2) q` — S† iteration as a single Z-rotation. -/
theorem niter_SDAG_eq_Rz {dim : Nat} (q : Nat) (h : q < dim) (k : Nat) :
    UCom.equiv (niter k (SDAG q : BaseUCom dim)) (Rz (k * (-(Real.pi/2))) q) :=
  niter_Rz q h (-(Real.pi/2)) k

/-- `niter k (Z q) ≡ Rz (k·π) q` — Z iteration as a single Z-rotation
    (since Z = Rz π definitionally). -/
theorem niter_Z_eq_Rz {dim : Nat} (q : Nat) (h : q < dim) (k : Nat) :
    UCom.equiv (niter k (Z q : BaseUCom dim)) (Rz (k * Real.pi) q) :=
  niter_Rz q h Real.pi k

/-- `niter k (ID q) ≡ Rz (k·0) q ≡ Rz 0 q ≡ ID q` — ID iteration is just ID
    (degenerate but consistent: ID q = Rz 0 q definitionally). -/
theorem niter_ID_eq_Rz {dim : Nat} (q : Nat) (h : q < dim) (k : Nat) :
    UCom.equiv (niter k (ID q : BaseUCom dim)) (Rz (k * 0) q) :=
  niter_Rz q h 0 k

/-- `niter k (ID q) ≡ ID q` for any k — ID iteration collapses back to ID.
    Combines niter_ID_eq_Rz with the fact that k·0 = 0 and Rz 0 ≡ ID. -/
theorem niter_ID_eq_ID {dim : Nat} (q : Nat) (h : q < dim) (k : Nat) :
    UCom.equiv (niter k (ID q : BaseUCom dim)) (ID q) := by
  have h1 := niter_ID_eq_Rz q h k
  have h2 : ((k : ℕ) : ℝ) * 0 = 0 := by simp
  rw [h2] at h1
  exact h1.trans (Rz_0_id q)

/-- Most general template: if `niter m c ≡ ID q` (c has order dividing m),
    then `niter (m*k) c ≡ ID q` for any k. Combines niter_mul, niter_congr,
    and niter_ID_eq_ID. Generalizes both `niter_two_mul_self_inv_eq_ID`
    (m=2) and order-4 lifts. -/
theorem niter_mul_eq_ID_of_eq_ID {dim : Nat} (q : Nat) (hq : q < dim)
    (c : BaseUCom dim) (m : Nat) (h : UCom.equiv (niter m c) (ID q)) (k : Nat) :
    UCom.equiv (niter (m * k) c) (ID q) := by
  have hd : 0 < dim := q.zero_le.trans_lt hq
  exact (niter_mul m k c hd).trans
        ((niter_congr k _ _ h hd).trans (niter_ID_eq_ID q hq k))

/-- Specialization to order-2: if `niter 2 c ≡ ID q` (gate is involutive
    at dim level), then `niter (2*k) c ≡ ID q` for any k. -/
theorem niter_two_mul_self_inv_eq_ID {dim : Nat} (q : Nat) (hq : q < dim)
    (c : BaseUCom dim) (h : UCom.equiv (niter 2 c) (ID q)) (k : Nat) :
    UCom.equiv (niter (2 * k) c) (ID q) :=
  niter_mul_eq_ID_of_eq_ID q hq c 2 h k

/-- Divisibility version: if `niter m c ≡ ID q` and `m ∣ n`, then
    `niter n c ≡ ID q`. The most ergonomic interface — destructures
    the divisor witness and applies the multiplication template. -/
theorem niter_eq_ID_of_dvd {dim : Nat} (q : Nat) (hq : q < dim)
    (c : BaseUCom dim) (m : Nat) (h : UCom.equiv (niter m c) (ID q))
    (n : Nat) (hdvd : m ∣ n) :
    UCom.equiv (niter n c) (ID q) := by
  obtain ⟨k, hk⟩ := hdvd
  rw [hk]
  exact niter_mul_eq_ID_of_eq_ID q hq c m h k

/-- Additive periodicity template: if `niter m c ≡ ID q`, then for any `n`,
    `niter (m + n) c ≡ niter n c` — adding a full period to the iteration
    count leaves the gate sequence unchanged. The dual to
    `niter_eq_ID_of_dvd`: shifts iteration counts by multiples of the order. -/
theorem niter_add_of_eq_ID {dim : Nat} (q : Nat) (hq : q < dim)
    (c : BaseUCom dim) (m : Nat) (h : UCom.equiv (niter m c) (ID q)) (n : Nat) :
    UCom.equiv (niter (m + n) c) (niter n c) := by
  have hd : 0 < dim := q.zero_le.trans_lt hq
  show uc_eval (niter (m + n) c) = uc_eval (niter n c)
  rw [uc_eval_niter hd, uc_eval_niter hd, pow_add,
      show (uc_eval c) ^ m = uc_eval (niter m c) from (uc_eval_niter hd m c).symm, h,
      uc_eval_ID_eq_one hq, one_mul]

/-- Successor specialization: if `niter m c ≡ ID q`, then `niter (m+1) c ≡ c`.
    The most common application — n = 1 case of `niter_add_of_eq_ID`,
    composed with `niter_one`. -/
theorem niter_succ_of_eq_ID {dim : Nat} (q : Nat) (hq : q < dim)
    (c : BaseUCom dim) (m : Nat) (h : UCom.equiv (niter m c) (ID q)) :
    UCom.equiv (niter (m + 1) c) c :=
  (niter_add_of_eq_ID q hq c m h 1).trans (niter_one c (q.zero_le.trans_lt hq))


/-- `niter 8 (T q) ≡ ID q` — T has order 8 (T⁸ = I), since 8·(π/4) = 2π
    and Rz(2π) is the identity. The matrix-level T⁸ identity that's been
    pending since we deferred the chain-form tMatrix_pow_eight. -/
theorem niter_eight_T_eq_ID {dim : Nat} (q : Nat) (h : q < dim) :
    UCom.equiv (niter 8 (T q : BaseUCom dim)) (ID q) := by
  have h1 := niter_T_eq_Rz q h 8
  have h2 : ((8 : ℕ) : ℝ) * (Real.pi / 4) = 2 * Real.pi := by push_cast; ring
  rw [h2] at h1
  exact h1.trans (Rz_2pi_id q)

/-- `niter 8 (TDAG q) ≡ ID q` — T† also has order 8 (T†⁸ = I), since
    8·(-π/4) = -2π and Rz(-2π) is the identity. Symmetric companion to
    niter_eight_T_eq_ID. -/
theorem niter_eight_TDAG_eq_ID {dim : Nat} (q : Nat) (h : q < dim) :
    UCom.equiv (niter 8 (TDAG q : BaseUCom dim)) (ID q) := by
  have h1 := niter_TDAG_eq_Rz q h 8
  have h2 : ((8 : ℕ) : ℝ) * (-(Real.pi / 4)) = -(2 * Real.pi) := by push_cast; ring
  rw [h2] at h1
  exact h1.trans (Rz_neg_2pi_id q)

/-- `niter 16 (T q) ≡ ID q` — T has order 8, so order 16 = order 8 · 2. -/
theorem niter_sixteen_T_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 16 (T q : BaseUCom dim)) (ID q) :=
  niter_mul_eq_ID_of_eq_ID q hq (T q) 8 (niter_eight_T_eq_ID q hq) 2

/-- `niter 16 (TDAG q) ≡ ID q` — symmetric companion. -/
theorem niter_sixteen_TDAG_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 16 (TDAG q : BaseUCom dim)) (ID q) :=
  niter_mul_eq_ID_of_eq_ID q hq (TDAG q) 8 (niter_eight_TDAG_eq_ID q hq) 2

/-- `niter 9 (T q) ≡ T q` — T⁹ = T⁸·T = I·T = T. 1-line application of
    `niter_succ_of_eq_ID` to `niter_eight_T_eq_ID`. -/
theorem niter_nine_T_eq_T {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 9 (T q : BaseUCom dim)) (T q) :=
  niter_succ_of_eq_ID q hq (T q) 8 (niter_eight_T_eq_ID q hq)

/-- `niter 9 (TDAG q) ≡ TDAG q` — symmetric companion. -/
theorem niter_nine_TDAG_eq_TDAG {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 9 (TDAG q : BaseUCom dim)) (TDAG q) :=
  niter_succ_of_eq_ID q hq (TDAG q) 8 (niter_eight_TDAG_eq_ID q hq)

/-- `niter 17 (T q) ≡ T q` — same template applied to the order-16 fact:
    T¹⁷ = T¹⁶·T = I·T = T. 1-line application of `niter_succ_of_eq_ID`. -/
theorem niter_seventeen_T_eq_T {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 17 (T q : BaseUCom dim)) (T q) :=
  niter_succ_of_eq_ID q hq (T q) 16 (niter_sixteen_T_eq_ID q hq)

/-- `niter 17 (TDAG q) ≡ TDAG q` — symmetric companion. -/
theorem niter_seventeen_TDAG_eq_TDAG {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 17 (TDAG q : BaseUCom dim)) (TDAG q) :=
  niter_succ_of_eq_ID q hq (TDAG q) 16 (niter_sixteen_TDAG_eq_ID q hq)

/-- `niter 4 (S q) ≡ ID q` — S has order 4 (S⁴ = I), since 4·(π/2) = 2π.
    Companion to niter_eight_T_eq_ID with k=4 instead of 8. -/
theorem niter_four_S_eq_ID {dim : Nat} (q : Nat) (h : q < dim) :
    UCom.equiv (niter 4 (S q : BaseUCom dim)) (ID q) := by
  have h1 := niter_S_eq_Rz q h 4
  have h2 : ((4 : ℕ) : ℝ) * (Real.pi / 2) = 2 * Real.pi := by push_cast; ring
  rw [h2] at h1
  exact h1.trans (Rz_2pi_id q)

/-- `niter 4 (SDAG q) ≡ ID q` — S† also has order 4. -/
theorem niter_four_SDAG_eq_ID {dim : Nat} (q : Nat) (h : q < dim) :
    UCom.equiv (niter 4 (SDAG q : BaseUCom dim)) (ID q) := by
  have h1 := niter_SDAG_eq_Rz q h 4
  have h2 : ((4 : ℕ) : ℝ) * (-(Real.pi / 2)) = -(2 * Real.pi) := by push_cast; ring
  rw [h2] at h1
  exact h1.trans (Rz_neg_2pi_id q)

/-- `niter 8 (S q) ≡ ID q` — S has order 4, so order 8 = order 4 · 2.
    1-line application of niter_mul_eq_ID_of_eq_ID with m=4, k=2. -/
theorem niter_eight_S_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 8 (S q : BaseUCom dim)) (ID q) :=
  niter_mul_eq_ID_of_eq_ID q hq (S q) 4 (niter_four_S_eq_ID q hq) 2

/-- `niter 8 (SDAG q) ≡ ID q` — symmetric companion. -/
theorem niter_eight_SDAG_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 8 (SDAG q : BaseUCom dim)) (ID q) :=
  niter_mul_eq_ID_of_eq_ID q hq (SDAG q) 4 (niter_four_SDAG_eq_ID q hq) 2

/-- `niter 9 (S q) ≡ S q` — S has order 4, S⁹ = S^(4·2+1) = (S⁴)²·S = I·S.
    1-line application of `niter_succ_of_eq_ID` to `niter_eight_S_eq_ID`. -/
theorem niter_nine_S_eq_S {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 9 (S q : BaseUCom dim)) (S q) :=
  niter_succ_of_eq_ID q hq (S q) 8 (niter_eight_S_eq_ID q hq)

/-- `niter 9 (SDAG q) ≡ SDAG q` — symmetric companion. -/
theorem niter_nine_SDAG_eq_SDAG {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 9 (SDAG q : BaseUCom dim)) (SDAG q) :=
  niter_succ_of_eq_ID q hq (SDAG q) 8 (niter_eight_SDAG_eq_ID q hq)

/-- `niter 2 (Z q) ≡ ID q` — Z has order 2 (Z² = I), since 2·π = 2π and
    Rz(2π) is the identity. Companion to niter_two_Z_eq_SKIP but stated
    with ID q on the RHS. -/
theorem niter_two_Z_eq_ID {dim : Nat} (q : Nat) (h : q < dim) :
    UCom.equiv (niter 2 (Z q : BaseUCom dim)) (ID q) := by
  have h1 := niter_Z_eq_Rz q h 2
  have h2 : ((2 : ℕ) : ℝ) * Real.pi = 2 * Real.pi := by push_cast; ring
  rw [h2] at h1
  exact h1.trans (Rz_2pi_id q)


/-- `niter 2 (X q) ≡ SKIP` — applying X twice via iteration is identity.
    A demonstration of `uc_eval_niter` + the matrix-level σx² = σi. -/
theorem niter_two_X_eq_SKIP {dim : Nat} (q : Nat) (hq : q < dim) (hd : 0 < dim) :
    UCom.equiv (niter 2 (X q : BaseUCom dim)) SKIP := by
  show uc_eval (niter 2 (X q)) = uc_eval (SKIP : BaseUCom dim)
  rw [uc_eval_niter hd 2]
  show (pad_u dim q (rotation Real.pi 0 Real.pi))^2 = pad_u dim 0 (rotation 0 0 0)
  rw [rotation_X, rotation_I, sq, pad_u_mul_pad_u, σx_mul_σx, pad_u_id hq, pad_u_id hd]

/-- `niter 2 (Z q) ≡ SKIP` — Z is involutive. -/
theorem niter_two_Z_eq_SKIP {dim : Nat} (q : Nat) (hq : q < dim) (hd : 0 < dim) :
    UCom.equiv (niter 2 (Z q : BaseUCom dim)) SKIP := by
  show uc_eval (niter 2 (Z q)) = uc_eval (SKIP : BaseUCom dim)
  rw [uc_eval_niter hd 2]
  show (pad_u dim q (rotation 0 0 Real.pi))^2 = pad_u dim 0 (rotation 0 0 0)
  rw [rotation_Z, rotation_I, sq, pad_u_mul_pad_u, σz_mul_σz, pad_u_id hq, pad_u_id hd]

/-- `niter 2 (H q) ≡ SKIP` — H is involutive. -/
theorem niter_two_H_eq_SKIP {dim : Nat} (q : Nat) (hq : q < dim) (hd : 0 < dim) :
    UCom.equiv (niter 2 (H q : BaseUCom dim)) SKIP := by
  show uc_eval (niter 2 (H q)) = uc_eval (SKIP : BaseUCom dim)
  rw [uc_eval_niter hd 2]
  show (pad_u dim q (rotation (Real.pi/2) 0 Real.pi))^2 = pad_u dim 0 (rotation 0 0 0)
  rw [rotation_H, rotation_I, sq, pad_u_mul_pad_u, hMatrix_mul_hMatrix,
      pad_u_id hq, pad_u_id hd]

/-- `niter 2 (Y q) ≡ SKIP` — Y is involutive. -/
theorem niter_two_Y_eq_SKIP {dim : Nat} (q : Nat) (hq : q < dim) (hd : 0 < dim) :
    UCom.equiv (niter 2 (Y q : BaseUCom dim)) SKIP := by
  show uc_eval (niter 2 (Y q)) = uc_eval (SKIP : BaseUCom dim)
  rw [uc_eval_niter hd 2]
  show (pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2)))^2
        = pad_u dim 0 (rotation 0 0 0)
  rw [rotation_Y, rotation_I, sq, pad_u_mul_pad_u, σy_mul_σy,
      pad_u_id hq, pad_u_id hd]

/-- `niter 2 (X q) ≡ ID q`. Combines `niter_two_X_eq_SKIP` with
    `ID_equiv_SKIP.symm` (no Z-rotation argument needed since X is on
    a different axis). -/
theorem niter_two_X_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 2 (X q : BaseUCom dim)) (ID q) := by
  have hd : 0 < dim := q.zero_le.trans_lt hq
  exact (niter_two_X_eq_SKIP q hq hd).trans (ID_equiv_SKIP hq hd).symm

/-- `niter 2 (Y q) ≡ ID q`. -/
theorem niter_two_Y_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 2 (Y q : BaseUCom dim)) (ID q) := by
  have hd : 0 < dim := q.zero_le.trans_lt hq
  exact (niter_two_Y_eq_SKIP q hq hd).trans (ID_equiv_SKIP hq hd).symm

/-- `niter 2 (H q) ≡ ID q`. -/
theorem niter_two_H_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 2 (H q : BaseUCom dim)) (ID q) := by
  have hd : 0 < dim := q.zero_le.trans_lt hq
  exact (niter_two_H_eq_SKIP q hq hd).trans (ID_equiv_SKIP hq hd).symm

/-- `niter 3 (X q) ≡ X q` — X cubed equals X (involution). -/
theorem niter_three_X_eq_X {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 3 (X q : BaseUCom dim)) (X q) := by
  show uc_eval (niter 3 (X q)) = uc_eval (X q : BaseUCom dim)
  rw [uc_eval_niter hd 3]
  show (pad_u dim q (rotation Real.pi 0 Real.pi))^3
        = pad_u dim q (rotation Real.pi 0 Real.pi)
  rw [show ((pad_u dim q (rotation Real.pi 0 Real.pi)) : Square dim)^3
        = pad_u dim q (rotation Real.pi 0 Real.pi)
          * pad_u dim q (rotation Real.pi 0 Real.pi)
          * pad_u dim q (rotation Real.pi 0 Real.pi)
        from by rw [pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_X, σx_pow_three]

/-- `niter 3 (Y q) ≡ Y q` — Y cubed equals Y. -/
theorem niter_three_Y_eq_Y {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 3 (Y q : BaseUCom dim)) (Y q) := by
  show uc_eval (niter 3 (Y q)) = uc_eval (Y q : BaseUCom dim)
  rw [uc_eval_niter hd 3]
  show (pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2)))^3
        = pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))
  rw [show ((pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))) : Square dim)^3
        = pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))
          * pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))
          * pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))
        from by rw [pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_Y, σy_pow_three]

/-- `niter 3 (Z q) ≡ Z q` — Z cubed equals Z. -/
theorem niter_three_Z_eq_Z {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 3 (Z q : BaseUCom dim)) (Z q) := by
  show uc_eval (niter 3 (Z q)) = uc_eval (Z q : BaseUCom dim)
  rw [uc_eval_niter hd 3]
  show (pad_u dim q (rotation 0 0 Real.pi))^3 = pad_u dim q (rotation 0 0 Real.pi)
  rw [show ((pad_u dim q (rotation 0 0 Real.pi)) : Square dim)^3
        = pad_u dim q (rotation 0 0 Real.pi)
          * pad_u dim q (rotation 0 0 Real.pi)
          * pad_u dim q (rotation 0 0 Real.pi)
        from by rw [pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_Z, σz_pow_three]

/-- `niter 3 (H q) ≡ H q` — H cubed equals H. -/
theorem niter_three_H_eq_H {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 3 (H q : BaseUCom dim)) (H q) := by
  show uc_eval (niter 3 (H q)) = uc_eval (H q : BaseUCom dim)
  rw [uc_eval_niter hd 3]
  show (pad_u dim q (rotation (Real.pi/2) 0 Real.pi))^3
        = pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
  rw [show ((pad_u dim q (rotation (Real.pi/2) 0 Real.pi)) : Square dim)^3
        = pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
          * pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
          * pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
        from by rw [pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, rotation_H, hMatrix_pow_three]

/-- `niter n (ID q) ≡ SKIP` for any `n` — iterating the identity gate is identity.
    Parameterized over n: ID iterated any number of times is SKIP. -/
theorem niter_ID_eq_SKIP {dim : Nat} (n : Nat) (q : Nat) (hq : q < dim) (hd : 0 < dim) :
    UCom.equiv (niter n (ID q : BaseUCom dim)) SKIP := by
  show uc_eval (niter n (ID q)) = uc_eval (SKIP : BaseUCom dim)
  rw [uc_eval_niter hd n]
  show (pad_u dim q (rotation 0 0 0))^n = pad_u dim 0 (rotation 0 0 0)
  rw [rotation_I, pad_u_id hq, pad_u_id hd, one_pow]

/-- `niter n SKIP ≡ SKIP` for any `n` — iterating SKIP is SKIP. -/
theorem niter_SKIP_eq_SKIP {dim : Nat} (n : Nat) (hd : 0 < dim) :
    UCom.equiv (niter n (SKIP : BaseUCom dim)) SKIP := by
  show uc_eval (niter n (SKIP : BaseUCom dim)) = uc_eval (SKIP : BaseUCom dim)
  rw [uc_eval_niter hd n]
  show (pad_u dim 0 (rotation 0 0 0))^n = pad_u dim 0 (rotation 0 0 0)
  rw [rotation_I, pad_u_id hd, one_pow]

/-! ## Parallel composition: apply a single-qubit gate to all qubits (`npar`).

    SQIR's `npar`: produces `g 0 ; g 1 ; ... ; g (n-1)` for a per-qubit gate
    constructor `g : Nat → BaseUCom dim`. Used to build column-Hadamards
    (every qubit gets H), the input layer of QPE/Grover. -/

/-- `npar n g` applies the per-qubit gate `g k` to qubits 0, 1, ..., n−1
    sequentially. Base case `npar 0 _ = SKIP`. -/
def npar {dim : Nat} (n : Nat) (g : Nat → BaseUCom dim) : BaseUCom dim :=
  match n with
  | 0     => SKIP
  | k + 1 => UCom.seq (npar k g) (g k)

@[simp] theorem npar_zero {dim : Nat} (g : Nat → BaseUCom dim) : npar 0 g = SKIP := rfl

@[simp] theorem npar_succ {dim : Nat} (n : Nat) (g : Nat → BaseUCom dim) :
    npar (n + 1) g = UCom.seq (npar n g) (g n) := rfl

/-- Definitional unfolding of `uc_eval` on `npar 0`: equals SKIP's matrix. -/
theorem uc_eval_npar_zero {dim : Nat} (g : Nat → BaseUCom dim) :
    uc_eval (npar 0 g) = uc_eval (SKIP : BaseUCom dim) := rfl

/-- Definitional unfolding of `uc_eval` on `npar (n+1)`: gate `g n` applied last. -/
theorem uc_eval_npar_succ {dim : Nat} (n : Nat) (g : Nat → BaseUCom dim) :
    uc_eval (npar (n + 1) g) = uc_eval (g n) * uc_eval (npar n g) := rfl

/-- `npar n g` is WellTyped on `dim` qubits when every `g k` for `k < n` is
    WellTyped, plus `0 < dim` for the SKIP base case. Foundational lemma
    for npar_H_well_typed and other npar-based circuits. -/
theorem npar_well_typed {dim : Nat} (n : Nat) (g : Nat → BaseUCom dim) (hd : 0 < dim)
    (hg : ∀ k, k < n → UCom.WellTyped dim (g k)) :
    UCom.WellTyped dim (npar n g) := by
  induction n with
  | zero => exact UCom.WellTyped.app1 hd
  | succ n ih =>
    refine UCom.WellTyped.seq
      (ih (fun k hk => hg k (Nat.lt_of_lt_of_le hk (Nat.le_succ n)))) ?_
    exact hg n (Nat.lt_succ_self n)

/-- A column of Hadamards: `H 0 ; H 1 ; ... ; H (n-1)`. The QFT pre-rotation. -/
noncomputable def npar_H {dim : Nat} (n : Nat) : BaseUCom dim :=
  npar n (fun k => H k)

/-- `npar_H n` is WellTyped when `n ≤ dim` and `0 < dim`. Direct application
    of `npar_well_typed` with `g k = H k` (each H k requires k < dim). -/
theorem npar_H_well_typed {dim : Nat} (n : Nat) (h : n ≤ dim) (hd : 0 < dim) :
    UCom.WellTyped dim (npar_H n : BaseUCom dim) :=
  npar_well_typed n _ hd (fun _ hk =>
    UCom.WellTyped.app1 (Nat.lt_of_lt_of_le hk h))

/-- `npar_H 0 = SKIP` — empty Hadamard column is a no-op. -/
@[simp] theorem npar_H_zero {dim : Nat} : (npar_H 0 : BaseUCom dim) = SKIP := rfl

/-- `npar_H (n+1) = npar_H n ; H n` — adding one more Hadamard at the end. -/
@[simp] theorem npar_H_succ {dim : Nat} (n : Nat) :
    (npar_H (n + 1) : BaseUCom dim) = UCom.seq (npar_H n) (H n) := rfl

/-- Matrix form of npar_H's succ unfold: appending `H n` left-multiplies
    by `pad_u dim n hMatrix`. Useful for inductive arguments on QFT. -/
theorem uc_eval_npar_H_succ {dim : Nat} (n : Nat) :
    uc_eval (npar_H (n + 1) : BaseUCom dim)
      = pad_u dim n hMatrix * uc_eval (npar_H n) := by
  show pad_u dim n (rotation (Real.pi/2) 0 Real.pi) * uc_eval (npar_H n)
        = pad_u dim n hMatrix * uc_eval (npar_H n)
  rw [rotation_H]

/-- Matrix form of npar_H's zero unfold: equals SKIP's matrix. Trivial rfl. -/
theorem uc_eval_npar_H_zero {dim : Nat} :
    uc_eval (npar_H 0 : BaseUCom dim) = uc_eval (SKIP : BaseUCom dim) := rfl

/-- npar_H 0 evaluates to the global identity matrix (when 0 < dim).
    SKIP's matrix is `pad_u dim 0 σi = 1` via `rotation_I` + `pad_u_id`. -/
theorem uc_eval_npar_H_zero_eq_one {dim : Nat} (h : 0 < dim) :
    uc_eval (npar_H 0 : BaseUCom dim) = (1 : Square dim) := by
  show pad_u dim 0 (rotation 0 0 0) = 1
  rw [rotation_I, pad_u_id h]

/-! ## Projectors and classical states (UnitaryOps.v line ~315)

    `bool_to_matrix b` is the 2×2 projector onto computational basis state `|b⟩`:
    `bool_to_matrix false = !![1, 0; 0, 0] = proj0`,
    `bool_to_matrix true  = !![0, 0; 0, 1] = proj1`.

    `proj q dim b` is `pad_u dim q (bool_to_matrix b)` — the projector onto
    `|b⟩` at qubit `q` in a `dim`-qubit system. -/

/-- Map a bool to the corresponding 2×2 computational-basis projector. -/
def bool_to_matrix (b : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  if b then proj1 else proj0

/-- Computational-basis projector at qubit `q` in a `dim`-qubit system. -/
noncomputable def proj (q dim : Nat) (b : Bool) : Square dim :=
  pad_u dim q (bool_to_matrix b)

@[simp] theorem bool_to_matrix_false : bool_to_matrix false = proj0 := rfl
@[simp] theorem bool_to_matrix_true  : bool_to_matrix true  = proj1 := rfl

/-- `proj q dim b` is idempotent: applying it twice gives the same projector.
    Lift of `proj0_mul_proj0` / `proj1_mul_proj1` through `pad_u`. -/
theorem proj_mul_proj (q dim : Nat) (b : Bool) :
    proj q dim b * proj q dim b = proj q dim b := by
  unfold proj
  rw [pad_u_mul_pad_u]
  congr 1
  cases b
  · exact proj0_mul_proj0
  · exact proj1_mul_proj1

/-- Cross-product of basis-projector matrices vanishes when the bools differ. -/
theorem bool_to_matrix_mul_ne (b b' : Bool) (h : b ≠ b') :
    bool_to_matrix b * bool_to_matrix b' = 0 := by
  cases b <;> cases b'
  · exact absurd rfl h
  · exact proj0_mul_proj1
  · exact proj1_mul_proj0
  · exact absurd rfl h

/-- `proj q dim b * proj q dim b' = 0` when `b ≠ b'`. Orthogonality of
    computational-basis projectors at the n-qubit (padded) level. -/
theorem proj_mul_proj_ne (q dim : Nat) (b b' : Bool) (h : b ≠ b') :
    proj q dim b * proj q dim b' = 0 := by
  unfold proj
  rw [pad_u_mul_pad_u, bool_to_matrix_mul_ne b b' h, pad_u_zero]

/-- Completeness: `proj q dim true + proj q dim false = 1` (identity matrix)
    when `q < dim`. The two basis projectors at the same qubit sum to identity. -/
theorem proj_true_add_proj_false (q dim : Nat) (h : q < dim) :
    proj q dim true + proj q dim false = (1 : Square dim) := by
  unfold proj
  rw [← pad_u_add]
  rw [show (bool_to_matrix true + bool_to_matrix false : Matrix (Fin 2) (Fin 2) ℂ) = σi
        from by show proj1 + proj0 = σi; rw [add_comm]; exact proj0_add_proj1_eq_id]
  exact pad_u_id h

/-! ## Controlled rotation (Nielsen-Chuang decomposition)

    `controlled_R q t θ φ λ` is the standard 6-gate decomposition of a
    controlled single-qubit rotation R(θ,φ,λ) with control `q`, target
    `t`. Matrix semantics: `pad_ctrl dim q t (rotation θ φ λ)`. The proof
    of that matrix equality is `uc_eval_controlled_R_eq_pad_ctrl` in
    `FormalRV.SQIRPort.ControlledGates` (kept downstream to avoid an
    import cycle with `PadAction`). -/

/-- **Controlled-R(θ,φ,λ)** decomposition: 5-gate target-side circuit
    `Rz · CNOT · R · CNOT · R` plus a control-side `Rz((φ+λ)/2)` to
    absorb the global phase from the ABXBXC identity. Used by `control`
    for the `app1 R` branch. -/
noncomputable def controlled_R {dim : Nat} (q t : Nat) (θ φ lam : ℝ) :
    BaseUCom dim :=
  UCom.seq (Rz ((φ + lam)/2) q)
    (UCom.seq (Rz ((lam - φ)/2) t)
      (UCom.seq (CNOT q t)
        (UCom.seq (UCom.app1 (BaseUnitary.R (-θ/2) 0 (-(φ + lam)/2)) t)
          (UCom.seq (CNOT q t)
            (UCom.app1 (BaseUnitary.R (θ/2) φ 0) t)))))

/-! ## Control: build a controlled version of an arbitrary circuit

    `control q c` produces a unitary that applies `c` only when qubit `q` is
    in state |1⟩. Defined recursively on the circuit structure:
    - For `seq c₁ c₂`: control each piece then sequence
    - For `app1 (R θ ϕ λ) n`: replace with `controlled_R q n θ ϕ λ`
      (Nielsen-Chuang ABXBXC + control-phase decomposition).
    - For `app2 CNOT m n`: replace with CCX q m n (controlled-CNOT = Toffoli)
    - For `app3 _ _ _ _`: SKIP (no 3-qubit primitives in BaseUnitary)

    SQIR/UnitaryOps.v line 113. -/

/-- Controlled version of an arbitrary `BaseUCom`.
    The control on `q` makes every gate in `c` conditional on |q⟩=|1⟩. -/
noncomputable def control {dim : Nat} (q : Nat) : BaseUCom dim → BaseUCom dim
  | UCom.seq c₁ c₂              => UCom.seq (control q c₁) (control q c₂)
  | UCom.app1 (BaseUnitary.R θ φ lam) t => controlled_R q t θ φ lam
  | UCom.app2 BaseUnitary.CNOT m n => CCX q m n   -- controlled-CNOT = Toffoli
  | UCom.app3 _ _ _ _           => SKIP   -- no 3-qubit primitives

/-- Definitional unfolding: control distributes over sequencing. -/
@[simp] theorem control_seq {dim : Nat} (q : Nat) (c₁ c₂ : BaseUCom dim) :
    control q (UCom.seq c₁ c₂) = UCom.seq (control q c₁) (control q c₂) := rfl

/-- Definitional unfolding: control of an `R(θ,φ,λ)` gate on target `t`
    yields the `controlled_R` decomposition with control `q`. Since
    `BaseUnitary 1` has only the `R` constructor, this covers every
    `UCom.app1` case. -/
@[simp] theorem control_app1_R {dim : Nat} (q : Nat) (θ φ lam : ℝ) (t : Nat) :
    control q (UCom.app1 (BaseUnitary.R θ φ lam) t : BaseUCom dim)
      = controlled_R q t θ φ lam := rfl

/-- Definitional unfolding: control of CNOT is Toffoli (CCX). -/
@[simp] theorem control_CNOT {dim : Nat} (q m n : Nat) :
    control q (CNOT m n : BaseUCom dim) = CCX q m n := rfl

/-- Control of SKIP unfolds definitionally. SKIP = `ID 0 = app1 (R 0 0 0) 0`,
    so `control q SKIP = controlled_R q 0 0 0 0`. Semantically this equals
    `pad_ctrl dim q 0 (rotation 0 0 0) = pad_ctrl dim q 0 I = 1`; the
    semantic equivalence is proved downstream once `pad_ctrl` of an
    identity matrix is available (see `SQIRPort.ControlledGates`). -/
theorem control_SKIP_eq {dim : Nat} (q : Nat) :
    control q (SKIP : BaseUCom dim) = controlled_R q 0 0 0 0 := rfl

/-- Control of any ID gate unfolds definitionally to `controlled_R q m 0 0 0`,
    which is the matrix `pad_ctrl dim q m I = 1` semantically. -/
theorem control_ID_eq {dim : Nat} (q m : Nat) :
    control q (ID m : BaseUCom dim) = controlled_R q m 0 0 0 := rfl

/-! ## is_fresh: a qubit doesn't appear in a circuit (UnitaryOps.v line 159) -/

/-- `q` is "fresh" with respect to circuit `c` iff `c` doesn't act on qubit `q`.
    This is the classical syntactic criterion for safe controlled-circuit
    construction (control on a qubit not used by the body). -/
def is_fresh {dim : Nat} (q : Nat) : BaseUCom dim → Prop
  | UCom.seq c₁ c₂   => is_fresh q c₁ ∧ is_fresh q c₂
  | UCom.app1 _ n    => q ≠ n
  | UCom.app2 _ m n  => q ≠ m ∧ q ≠ n
  | UCom.app3 _ a b c => q ≠ a ∧ q ≠ b ∧ q ≠ c

/-- `is_fresh` characterization for X. -- SQIR/SQIR/UnitaryOps.v line 197: fresh_X. -/
theorem fresh_X {dim : Nat} (q₁ q₂ : Nat) :
    q₁ ≠ q₂ ↔ is_fresh q₁ (X q₂ : BaseUCom dim) := Iff.rfl

/-- `is_fresh` characterization for Z. -/
theorem fresh_Z {dim : Nat} (q₁ q₂ : Nat) :
    q₁ ≠ q₂ ↔ is_fresh q₁ (Z q₂ : BaseUCom dim) := Iff.rfl

/-- `is_fresh` characterization for Y. -/
theorem fresh_Y {dim : Nat} (q₁ q₂ : Nat) :
    q₁ ≠ q₂ ↔ is_fresh q₁ (Y q₂ : BaseUCom dim) := Iff.rfl

/-- `is_fresh` characterization for H. -- SQIR/SQIR/UnitaryOps.v line 205: fresh_H. -/
theorem fresh_H {dim : Nat} (q₁ q₂ : Nat) :
    q₁ ≠ q₂ ↔ is_fresh q₁ (H q₂ : BaseUCom dim) := Iff.rfl

/-- `is_fresh` characterization for T. -/
theorem fresh_T {dim : Nat} (q₁ q₂ : Nat) :
    q₁ ≠ q₂ ↔ is_fresh q₁ (T q₂ : BaseUCom dim) := Iff.rfl

/-- `is_fresh` characterization for S. -/
theorem fresh_S {dim : Nat} (q₁ q₂ : Nat) :
    q₁ ≠ q₂ ↔ is_fresh q₁ (S q₂ : BaseUCom dim) := Iff.rfl

/-- `is_fresh` characterization for TDAG. -/
theorem fresh_TDAG {dim : Nat} (q₁ q₂ : Nat) :
    q₁ ≠ q₂ ↔ is_fresh q₁ (TDAG q₂ : BaseUCom dim) := Iff.rfl

/-- `is_fresh` characterization for SDAG. -/
theorem fresh_SDAG {dim : Nat} (q₁ q₂ : Nat) :
    q₁ ≠ q₂ ↔ is_fresh q₁ (SDAG q₂ : BaseUCom dim) := Iff.rfl

/-- `is_fresh` characterization for CNOT. Both qubits must differ from `a`.
    -- SQIR/SQIR/UnitaryOps.v line 213: fresh_CNOT. -/
theorem fresh_CNOT {dim : Nat} (a b c : Nat) :
    (a ≠ b ∧ a ≠ c) ↔ is_fresh a (CNOT b c : BaseUCom dim) := Iff.rfl

/-- `is_fresh` distributes over sequential composition: `q` is fresh in
    `c1 ; c2` iff fresh in both. By definition. -/
theorem fresh_seq {dim : Nat} (q : Nat) (c₁ c₂ : BaseUCom dim) :
    is_fresh q (UCom.seq c₁ c₂) ↔ is_fresh q c₁ ∧ is_fresh q c₂ := Iff.rfl

/-- `is_fresh q SKIP` iff `q ≠ 0` (since `SKIP = ID 0`). -/
theorem fresh_SKIP {dim : Nat} (q : Nat) :
    q ≠ 0 ↔ is_fresh q (SKIP : BaseUCom dim) := Iff.rfl

/-- Forward direction of SQIR's `fresh_CCX`: if `q` differs from all three
    target qubits, it's fresh in the 15-gate CCX decomposition.
    -- SQIR/SQIR/UnitaryOps.v line 231 (forward direction). -/
theorem fresh_CCX_mp {dim : Nat} (q a b c : Nat)
    (ha : q ≠ a) (hb : q ≠ b) (hc : q ≠ c) :
    is_fresh q (CCX a b c : BaseUCom dim) := by
  unfold CCX
  refine ⟨?_, ?_, ?_, ?_⟩
  -- s₁: H c ; CNOT b c ; T† c ; CNOT a c
  · exact ⟨hc, ⟨hb, hc⟩, hc, ha, hc⟩
  -- s₂: T c ; CNOT b c ; T† c ; CNOT a c
  · exact ⟨hc, ⟨hb, hc⟩, hc, ha, hc⟩
  -- s₃: CNOT a b ; T† b ; CNOT a b
  · exact ⟨⟨ha, hb⟩, hb, ⟨ha, hb⟩⟩
  -- s₄: T a ; T b ; T c ; H c
  · exact ⟨ha, hb, hc, hc⟩

/-- Backward direction of SQIR's `fresh_CCX`: extract the three inequalities.
    -- SQIR/SQIR/UnitaryOps.v line 231 (backward direction). -/
theorem fresh_CCX_mpr {dim : Nat} (q a b c : Nat)
    (h : is_fresh q (CCX a b c : BaseUCom dim)) :
    q ≠ a ∧ q ≠ b ∧ q ≠ c := by
  unfold CCX at h
  -- h : is_fresh q s₁ ∧ is_fresh q s₂ ∧ is_fresh q s₃ ∧ is_fresh q s₄.
  -- s₄ = T a ; T b ; T c ; H c → ⟨q≠a, q≠b, q≠c, q≠c⟩, gives all three.
  obtain ⟨_, _, _, ha, hb, hc, _⟩ := h
  exact ⟨ha, hb, hc⟩

/-- SQIR's full `fresh_CCX` iff form. -/
theorem fresh_CCX {dim : Nat} (q a b c : Nat) :
    (q ≠ a ∧ q ≠ b ∧ q ≠ c) ↔ is_fresh q (CCX a b c : BaseUCom dim) :=
  ⟨fun ⟨ha, hb, hc⟩ => fresh_CCX_mp q a b c ha hb hc, fresh_CCX_mpr q a b c⟩

/-- Forward direction: q ≠ a/b/c → fresh in CCZ (the 13-gate decomposition). -/
theorem fresh_CCZ_mp {dim : Nat} (q a b c : Nat)
    (ha : q ≠ a) (hb : q ≠ b) (hc : q ≠ c) :
    is_fresh q (CCZ a b c : BaseUCom dim) := by
  unfold CCZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨⟨hb, hc⟩, hc, ha, hc⟩
  · exact ⟨hc, ⟨hb, hc⟩, hc, ha, hc⟩
  · exact ⟨⟨ha, hb⟩, hb, ⟨ha, hb⟩⟩
  · exact ⟨ha, hb, hc⟩

/-- Backward direction for CCZ: extract the three inequalities from is_fresh. -/
theorem fresh_CCZ_mpr {dim : Nat} (q a b c : Nat)
    (h : is_fresh q (CCZ a b c : BaseUCom dim)) :
    q ≠ a ∧ q ≠ b ∧ q ≠ c := by
  unfold CCZ at h
  obtain ⟨_, _, _, ha, hb, hc⟩ := h
  exact ⟨ha, hb, hc⟩

/-- Full iff form for CCZ. -/
theorem fresh_CCZ {dim : Nat} (q a b c : Nat) :
    (q ≠ a ∧ q ≠ b ∧ q ≠ c) ↔ is_fresh q (CCZ a b c : BaseUCom dim) :=
  ⟨fun ⟨ha, hb, hc⟩ => fresh_CCZ_mp q a b c ha hb hc, fresh_CCZ_mpr q a b c⟩

/-- `is_fresh` characterization for SWAP. SWAP = CNOT m n ; CNOT n m ; CNOT m n,
    so q is fresh iff q ≠ m and q ≠ n. -/
theorem fresh_SWAP {dim : Nat} (q m n : Nat) :
    (q ≠ m ∧ q ≠ n) ↔ is_fresh q (SWAP m n : BaseUCom dim) := by
  constructor
  · intro ⟨hm, hn⟩
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨hm, hn⟩
    · exact ⟨hn, hm⟩
    · exact ⟨hm, hn⟩
  · intro ⟨⟨hm, hn⟩, _, _⟩
    exact ⟨hm, hn⟩

/-- `is_fresh` distributes through `niter`'s successor: niter (n+1) c is
    `c ; niter n c`, so q is fresh iff fresh in both. -/
theorem fresh_niter_succ {dim : Nat} (q n : Nat) (c : BaseUCom dim) :
    is_fresh q (niter (n + 1) c) ↔ is_fresh q c ∧ is_fresh q (niter n c) := Iff.rfl

/-- `is_fresh` distributes through `npar`'s successor: npar (n+1) g is
    `npar n g ; g n`, so q is fresh iff fresh in both. -/
theorem fresh_npar_succ {dim : Nat} (q n : Nat) (g : Nat → BaseUCom dim) :
    is_fresh q (npar (n + 1) g) ↔ is_fresh q (npar n g) ∧ is_fresh q (g n) := Iff.rfl

/-- If `q` is fresh in `c` (and q ≠ 0 for the SKIP base case), then `q` is
    fresh in any iteration `niter n c`. -/
theorem fresh_niter {dim : Nat} (q n : Nat) (c : BaseUCom dim)
    (hc : is_fresh q c) (hq : q ≠ 0) :
    is_fresh q (niter n c) := by
  induction n with
  | zero => exact hq
  | succ k ih => exact ⟨hc, ih⟩

/-- If `q` is fresh in `g k` for every k < n (and q ≠ 0), then `q` is fresh
    in `npar n g`. -/
theorem fresh_npar {dim : Nat} (q n : Nat) (g : Nat → BaseUCom dim)
    (hg : ∀ k, k < n → is_fresh q (g k)) (hq : q ≠ 0) :
    is_fresh q (npar n g) := by
  induction n with
  | zero => exact hq
  | succ k ih =>
      have ih' : is_fresh q (npar k g) := ih (fun j hj => hg j (by omega))
      exact ⟨ih', hg k (by omega)⟩

/-- `q ≥ n` and `q ≠ 0` is sufficient for `q` to be fresh in `npar_H n`
    (the column of Hadamards on qubits 0, 1, …, n−1). -/
theorem fresh_npar_H {dim : Nat} (q n : Nat) (hq : q ≥ n) (hq0 : q ≠ 0) :
    is_fresh q (npar_H n : BaseUCom dim) := by
  apply fresh_npar
  · intro k hk
    show q ≠ k
    omega
  · exact hq0

/-- Freshness for `controlled_R`: if `q1` is fresh from both the control
    qubit `q2` and target `t`, it is fresh from the entire decomposition. -/
theorem fresh_controlled_R {dim : Nat} (q1 q2 t : Nat) (θ φ lam : ℝ)
    (h12 : q1 ≠ q2) (h1t : q1 ≠ t) :
    is_fresh q1 (controlled_R q2 t θ φ lam : BaseUCom dim) := by
  unfold controlled_R Rz CNOT
  refine ⟨h12, h1t, ⟨h12, h1t⟩, h1t, ⟨h12, h1t⟩, h1t⟩

/-- Forward direction of SQIR's `fresh_control`: q1 ≠ q2 and is_fresh q1 c
    (and q1 ≠ 0 for the SKIP fallback in `control`'s app3 case) imply
    is_fresh q1 (control q2 c).
    -- SQIR/SQIR/UnitaryOps.v line 241: fresh_control (forward direction). -/
theorem fresh_control_mp {dim : Nat} (q1 q2 : Nat) (c : BaseUCom dim)
    (h12 : q1 ≠ q2) (hc : is_fresh q1 c) (hq0 : q1 ≠ 0) :
    is_fresh q1 (control q2 c) := by
  induction c with
  | seq c1 c2 ih1 ih2 =>
      exact ⟨ih1 hc.1, ih2 hc.2⟩
  | app1 u n =>
      cases u with
      | R θ φ lam => exact fresh_controlled_R q1 q2 n θ φ lam h12 hc
  | app2 u m n =>
      cases u
      exact fresh_CCX_mp q1 q2 m n h12 hc.1 hc.2
  | app3 _ _ _ _ => exact hq0

/-- Demo of niter_eq_ID_of_dvd: `niter 6 (X q) ≡ ID q` (X has order 2,
    and 2 ∣ 6). Shows the ergonomic 1-line invocation with `decide` for
    the divisibility witness. -/
theorem niter_six_X_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 6 (X q : BaseUCom dim)) (ID q) :=
  niter_eq_ID_of_dvd q hq (X q) 2 (niter_two_X_eq_ID q hq) 6 (by decide)

/-- Demo of niter_eq_ID_of_dvd at order 4: `niter 12 (S q) ≡ ID q`
    (S has order 4, and 4 ∣ 12). -/
theorem niter_twelve_S_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 12 (S q : BaseUCom dim)) (ID q) :=
  niter_eq_ID_of_dvd q hq (S q) 4 (niter_four_S_eq_ID q hq) 12 (by decide)

/-- Composed demo: `niter 13 (S q) ≡ S q` — combines the two parametric
    templates `niter_eq_ID_of_dvd` (to reach order 12) and
    `niter_succ_of_eq_ID` (to lift to 13). 1-line application showing how
    multiple parametric templates compose. -/
theorem niter_thirteen_S_eq_S {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 13 (S q : BaseUCom dim)) (S q) :=
  niter_succ_of_eq_ID q hq (S q) 12 (niter_twelve_S_eq_ID q hq)

/-- Symmetric companion: `niter 12 (SDAG q) ≡ ID q` (SDAG also has
    order 4, and 4 ∣ 12). -/
theorem niter_twelve_SDAG_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 12 (SDAG q : BaseUCom dim)) (ID q) :=
  niter_eq_ID_of_dvd q hq (SDAG q) 4 (niter_four_SDAG_eq_ID q hq) 12 (by decide)

/-- Symmetric companion: `niter 13 (SDAG q) ≡ SDAG q`. -/
theorem niter_thirteen_SDAG_eq_SDAG {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 13 (SDAG q : BaseUCom dim)) (SDAG q) :=
  niter_succ_of_eq_ID q hq (SDAG q) 12 (niter_twelve_SDAG_eq_ID q hq)

/-- Pauli-X period demo: `niter 7 (X q) ≡ X q` — X has order 2, so
    X⁷ = (X²)³·X = I·X. 1-line composition of `niter_succ_of_eq_ID`
    with `niter_six_X_eq_ID`. Demonstrates the templates work for
    period-2 (involution) bases just as for the higher-period T/S families. -/
theorem niter_seven_X_eq_X {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 7 (X q : BaseUCom dim)) (X q) :=
  niter_succ_of_eq_ID q hq (X q) 6 (niter_six_X_eq_ID q hq)

/-- Pauli-Z analog of `niter_six_X_eq_ID`: `niter 6 (Z q) ≡ ID q`
    (Z has order 2, 2 ∣ 6). -/
theorem niter_six_Z_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 6 (Z q : BaseUCom dim)) (ID q) :=
  niter_eq_ID_of_dvd q hq (Z q) 2 (niter_two_Z_eq_ID q hq) 6 (by decide)

/-- Pauli-Z period demo: `niter 7 (Z q) ≡ Z q`. -/
theorem niter_seven_Z_eq_Z {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 7 (Z q : BaseUCom dim)) (Z q) :=
  niter_succ_of_eq_ID q hq (Z q) 6 (niter_six_Z_eq_ID q hq)

/-- Pauli-Y analog: `niter 6 (Y q) ≡ ID q` (Y has order 2, 2 ∣ 6). -/
theorem niter_six_Y_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 6 (Y q : BaseUCom dim)) (ID q) :=
  niter_eq_ID_of_dvd q hq (Y q) 2 (niter_two_Y_eq_ID q hq) 6 (by decide)

/-- Pauli-Y period demo: `niter 7 (Y q) ≡ Y q`. -/
theorem niter_seven_Y_eq_Y {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 7 (Y q : BaseUCom dim)) (Y q) :=
  niter_succ_of_eq_ID q hq (Y q) 6 (niter_six_Y_eq_ID q hq)

/-- Hadamard analog: `niter 6 (H q) ≡ ID q` (H has order 2, 2 ∣ 6). -/
theorem niter_six_H_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 6 (H q : BaseUCom dim)) (ID q) :=
  niter_eq_ID_of_dvd q hq (H q) 2 (niter_two_H_eq_ID q hq) 6 (by decide)

/-- Hadamard period demo: `niter 7 (H q) ≡ H q`. Completes the X/Y/Z/H
    period-6 pair set. -/
theorem niter_seven_H_eq_H {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 7 (H q : BaseUCom dim)) (H q) :=
  niter_succ_of_eq_ID q hq (H q) 6 (niter_six_H_eq_ID q hq)

end BaseUCom
end FormalRV.Framework
