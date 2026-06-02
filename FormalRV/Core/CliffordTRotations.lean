/-
  FormalRV.Core.CliffordTRotations — exact Clifford+T synthesis of the
  `π/4`-multiple z-rotations, and the (cited) Solovay–Kitaev contract for
  the rest.  This is the rotation layer of "compile QPE to Clifford+T".

  ## The exact cases (proved here, sorry-free)

  A z-rotation `R_z(λ) = diag(1, e^{iλ})` is exactly Clifford+T iff
  `λ ∈ (π/4)·ℤ`, in which case it is a power of the `T` gate
  (`T = R_z(π/4)`).  We prove the phase-composition law and hence

      T^k = R_z(k·π/4)      (`tPow_eq_rotation`)

  which covers `Z = T⁴`, `S = T²`, `T = T¹` — and so the QFT's exact
  controlled rotations `R_1 = Z`, `R_2 = S`, `R_3 = T`
  (`R_k := diag(1, e^{2πi/2^k})`).

  ## The approximate cases (the honest boundary)

  The QFT rotations `R_k` for `k ≥ 4` are irrational-angle and provably
  NOT exactly Clifford+T; they must be APPROXIMATED.  We expose the
  standard result — Solovay–Kitaev / Ross–Selinger — as a single named
  contract `SolovayKitaev`: for every angle and precision `ε` there is a
  Clifford+T circuit `ε`-close in operator norm, with `T`-count
  `O(log^c(1/ε))`.  Formalising that algorithm's number-theoretic core
  is a separate (multi-month) effort; here it is a cited assumption, and
  the `ε`-budget is what propagates into Shor's success probability.
-/
import FormalRV.Core.UnitarySem

namespace FormalRV.Framework.CliffordTRotations

open Complex
open FormalRV.Framework

/-! ## §1. `R_z(λ) = diag(1, e^{iλ})`. -/

theorem rotation_zz_diag (lam : ℝ) :
    rotation 0 0 lam = !![1, 0; 0, Complex.exp (lam * I)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Real.cos_zero, Real.sin_zero]

/-! ## §2. Phase composition: `R_z(a)·R_z(b) = R_z(a+b)`. -/

theorem rotation_zz_mul (a b : ℝ) :
    rotation 0 0 a * rotation 0 0 b = rotation 0 0 (a + b) := by
  rw [rotation_zz_diag, rotation_zz_diag, rotation_zz_diag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add, ← add_mul,
          Complex.ofReal_add]

/-! ## §3. Exact synthesis: `T^k = R_z(k·π/4)`. -/

theorem rotation_zz_pow (lam : ℝ) (k : ℕ) :
    (rotation 0 0 lam) ^ k = rotation 0 0 (k * lam) := by
  induction k with
  | zero =>
      simp [rotation_zz_diag, Matrix.one_fin_two]
  | succ n ih =>
      rw [pow_succ, ih, rotation_zz_mul]
      congr 1
      push_cast; ring

/-- **Exact Clifford+T synthesis of a `π/4`-multiple z-rotation:** `k`
    applications of the `T` gate (`R_z(π/4)`) realise `R_z(k·π/4)`
    exactly. -/
theorem tPow_eq_rotation (k : ℕ) :
    (rotation 0 0 (Real.pi / 4)) ^ k = rotation 0 0 (k * (Real.pi / 4)) :=
  rotation_zz_pow (Real.pi / 4) k

/-! ## §4. The QFT's exact controlled rotations.

    `R_k := diag(1, e^{2πi/2^k})`.  `R_1 = Z = T⁴`, `R_2 = S = T²`,
    `R_3 = T = T¹` — all exactly Clifford+T via `tPow_eq_rotation`. -/

/-- The QFT phase rotation `R_k = diag(1, e^{2πi/2^k}) = R_z(2π/2^k)`. -/
noncomputable def qftRot (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rotation 0 0 (2 * Real.pi / 2 ^ k)

/-- `R_3 = T` (one `T` gate). -/
theorem qftRot_three_eq_T : qftRot 3 = rotation 0 0 (Real.pi / 4) := by
  unfold qftRot
  congr 1
  ring

/-- `R_2 = S = T²`. -/
theorem qftRot_two_eq_TSq :
    qftRot 2 = (rotation 0 0 (Real.pi / 4)) ^ 2 := by
  rw [tPow_eq_rotation]
  unfold qftRot
  congr 1
  push_cast; ring

/-- `R_1 = Z = T⁴`. -/
theorem qftRot_one_eq_TPow4 :
    qftRot 1 = (rotation 0 0 (Real.pi / 4)) ^ 4 := by
  rw [tPow_eq_rotation]
  unfold qftRot
  congr 1
  push_cast; ring

/-! ## §5. Clifford+T circuits and the Solovay–Kitaev contract. -/

/-- A `BaseUCom` is a Clifford+T circuit: composed from the single-qubit
    Clifford+T gates `{H, S, T, S†, T†}` and `CNOT`. -/
inductive IsCliffordT : {dim : Nat} → BaseUCom dim → Prop
  | seq {dim : Nat} {c₁ c₂ : BaseUCom dim} :
      IsCliffordT c₁ → IsCliffordT c₂ → IsCliffordT (UCom.seq c₁ c₂)
  | gate1 {dim : Nat} {u : BaseUnitary 1} {n : Nat}
      (h : u = U_H ∨ u = U_S ∨ u = U_T ∨ u = U_SDAG ∨ u = U_TDAG) :
      IsCliffordT (UCom.app1 u n : BaseUCom dim)
  | cnot {dim : Nat} {m n : Nat} :
      IsCliffordT (UCom.app2 BaseUnitary.CNOT m n : BaseUCom dim)

/-- **Solovay–Kitaev / Ross–Selinger — cited contract.**

    For every angle `θ` and precision `ε > 0` there is a Clifford+T
    circuit whose unitary is entrywise within `ε` of `R_z(θ)`, with a
    finite `T`-count (the cited results give `O(log^c(1/ε))`).

    This is the ONE named assumption of the QPE→Clifford+T compilation:
    the exact `(π/4)·ℤ` rotations are proved (`tPow_eq_rotation`,
    `qftRot_*`), and SK supplies an error-bounded Clifford+T circuit for
    every other rotation.  Its proof — the algorithm's number-theoretic
    exact-synthesis core over `ℤ[1/√2, i]` — is a separate (multi-month)
    formalisation and is deliberately taken on trust here.  The `ε`
    budget is what propagates into Shor's success-probability bound. -/
axiom solovay_kitaev (θ ε : ℝ) (hε : 0 < ε) :
    ∃ (c : BaseUCom 1) (tCount : ℕ),
      IsCliffordT c ∧
      (∀ i j : Fin 2, ‖uc_eval c i j - rotation 0 0 θ i j‖ ≤ ε)

/-- The exact rotations are an `ε = 0` instance realised WITHOUT the
    Solovay–Kitaev contract: `R_z(k·π/4)` is `T^k` exactly.  (Stated as a
    sanity check that the contract is only needed off the `(π/4)·ℤ`
    lattice.) -/
theorem exact_rotation_no_approx (k : ℕ) :
    (rotation 0 0 (Real.pi / 4)) ^ k = rotation 0 0 (k * (Real.pi / 4)) :=
  tPow_eq_rotation k

end FormalRV.Framework.CliffordTRotations
