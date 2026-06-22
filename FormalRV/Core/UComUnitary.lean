/-
  FormalRV.Core.UComUnitary — generic `WellTyped → unitary` for `uc_eval`.
  ════════════════════════════════════════════════════════════════════════════

  The matrix-unitarity obligation `(uc_eval c)ᴴ * uc_eval c = 1` for every well-typed circuit,
  built by structural induction over the `BaseUCom` AST.  This discharges the `hisom` hypothesis
  of the coset-Shor H4/H5 deviation bounds (each QPE stage is a `pmDist` isometry because its
  `uc_eval` is genuinely unitary — NOT merely a permutation; the inverse-QFT stage is a real
  unitary, which is exactly why the ℓ²/`pmDist` route was needed).

  Pieces:
    • `rotation_conjTranspose_mul` — the universal single-qubit gate `R(θ,ϕ,λ)` is unitary;
    • `pad_u_conjTranspose` / `pad_u_unitary` — padding a unitary 2×2 to `dim` qubits is unitary;
    • `ueval_cnot_unitary` — the CNOT semantics (`pad_ctrl … σx`) is unitary (self-adjoint involution);
    • `uc_eval_unitary_of_wellTyped` — the headline structural induction.

  Kernel-clean: no `sorry`, no `native_decide`, axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import FormalRV.Core.UnitaryOps

namespace FormalRV.Framework

open scoped BigOperators
open Matrix

/-! ## §1. The base single-qubit gate `rotation θ ϕ λ` is unitary. -/

/-- **`R(θ,ϕ,λ)` is unitary:** `(rotation θ ϕ λ)ᴴ * rotation θ ϕ λ = 1`.  Direct 2×2 computation:
    the off-diagonals cancel (the `exp` phases telescope) and the diagonals are `cos² + sin² = 1`. -/
theorem rotation_conjTranspose_mul (θ ϕ lam : ℝ) :
    (rotation θ ϕ lam).conjTranspose * rotation θ ϕ lam = 1 := by
  have hcomb : ∀ a b : ℂ, Complex.exp a * Complex.exp b = Complex.exp (a + b) :=
    fun a b => (Complex.exp_add a b).symm
  have hexp : ∀ z : ℂ, Complex.exp (-(z * Complex.I)) * Complex.exp (z * Complex.I) = 1 := by
    intro z; rw [hcomb]; rw [show -(z * Complex.I) + z * Complex.I = 0 from by ring, Complex.exp_zero]
  have htrig : (Real.cos (θ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ)
      + (Real.sin (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add,
        show Real.cos (θ / 2) * Real.cos (θ / 2) + Real.sin (θ / 2) * Real.sin (θ / 2)
          = 1 from by nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]]
    norm_num
  -- the two off-diagonal exp identities
  have h01 : Complex.exp (-(↑ϕ * Complex.I)) * Complex.exp ((↑ϕ + ↑lam) * Complex.I)
      = Complex.exp (↑lam * Complex.I) := by
    rw [hcomb, show -(↑ϕ * Complex.I) + (↑ϕ + ↑lam) * Complex.I = ↑lam * Complex.I from by ring]
  have h10 : Complex.exp (-((↑ϕ + ↑lam) * Complex.I)) * Complex.exp (↑ϕ * Complex.I)
      = Complex.exp (-(↑lam * Complex.I)) := by
    rw [hcomb, show -((↑ϕ + ↑lam) * Complex.I) + ↑ϕ * Complex.I = -(↑lam * Complex.I) from by ring]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, rotation, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.one_apply, Fin.mk_zero, Fin.mk_one,
      Complex.star_def, map_mul, map_neg, map_add, Complex.conj_ofReal, Complex.conj_I,
      ← Complex.exp_conj, mul_neg, neg_mul, reduceIte]
  · -- (0,0): cos² + sin² = 1
    linear_combination htrig + ((Real.sin (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ)) * hexp ↑ϕ
  · -- (0,1): off-diagonal cancels
    rw [if_neg (show ¬ (0 : Fin 2) = 1 from by decide)]
    linear_combination ((Real.sin (θ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ)) * h01
  · -- (1,0): off-diagonal cancels
    rw [if_neg (show ¬ (1 : Fin 2) = 0 from by decide)]
    linear_combination ((Real.sin (θ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ)) * h10
  · -- (1,1): sin² + cos² = 1
    linear_combination htrig
      + ((Real.sin (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ)) * hexp ↑lam
      + ((Real.cos (θ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ)) * hexp (↑ϕ + ↑lam)

/-! ## §2. Padding a unitary 2×2 to `dim` qubits preserves unitarity. -/

/-- **`pad_u` commutes with conjTranspose.**  `(pad_u dim n M)ᴴ = pad_u dim n Mᴴ`.  `pad_u` is a
    `reindex` of `(Iₙ ⊗ M) ⊗ Iₙ`; `conjTranspose` passes through the reindex (a `submatrix`) and
    distributes over the Kroneckers, fixing the identity factors. -/
theorem pad_u_conjTranspose (dim n : Nat) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (pad_u dim n M).conjTranspose = pad_u dim n M.conjTranspose := by
  by_cases h : n < dim
  · simp only [pad_u, dif_pos h, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
    congr 1
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker]
    simp only [Iₙ, Matrix.conjTranspose_one]
  · simp only [pad_u, dif_neg h, Matrix.conjTranspose_zero]

/-- **Padding a unitary 2×2 to `dim` qubits is unitary.**  `Mᴴ M = 1 ⇒ (pad_u dim n M)ᴴ ·
    pad_u dim n M = 1` (for `n < dim`).  `pad_u_conjTranspose` then `pad_u_mul_pad_u` then
    `pad_u_one`. -/
theorem pad_u_unitary (dim n : Nat) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hn : n < dim) (hM : M.conjTranspose * M = 1) :
    (pad_u dim n M).conjTranspose * pad_u dim n M = 1 := by
  rw [pad_u_conjTranspose, pad_u_mul_pad_u, hM, pad_u_one hn]

/-! ## §3. The CNOT semantics is unitary (self-adjoint projector decomposition). -/

/-- **CNOT is unitary.**  `ueval_cnot dim m n = pad_ctrl … σx = P₀ + P₁·X` (control `m`, target
    `n`, `m ≠ n`).  The base matrices `proj0`/`proj1`/`σx` are Hermitian, so `ueval_cnotᴴ =
    P₀ + X·P₁`; then the projector algebra (`P₀²=P₀`, `P₁²=P₁`, `P₀P₁=P₁P₀=0`, `σx²=σi`, the
    disjoint-qubit commutation `P₁X = XP₁`, `P₀+P₁=σi`) collapses the product to `1`. -/
theorem ueval_cnot_unitary (dim m n : Nat) (hm : m < dim) (hn : n < dim) (hmn : m ≠ n) :
    (ueval_cnot dim m n).conjTranspose * ueval_cnot dim m n = 1 := by
  have hp0 : proj0.conjTranspose = proj0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.conjTranspose_apply]
  have hp1 : proj1.conjTranspose = proj1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.conjTranspose_apply]
  have hsx : σx.conjTranspose = σx := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [σx, Matrix.conjTranspose_apply]
  -- the conjTranspose of CNOT.
  have hH : (ueval_cnot dim m n).conjTranspose
      = pad_u dim m proj0 + pad_u dim n σx * pad_u dim m proj1 := by
    show (pad_ctrl dim m n σx).conjTranspose = _
    unfold pad_ctrl
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
        pad_u_conjTranspose, pad_u_conjTranspose, pad_u_conjTranspose, hp0, hp1, hsx]
  -- the four product terms.
  have e1 : pad_u dim m proj0 * pad_u dim m proj0 = pad_u dim m proj0 := by
    rw [pad_u_mul_pad_u, proj0_mul_proj0]
  have e2 : pad_u dim m proj0 * (pad_u dim m proj1 * pad_u dim n σx) = 0 := by
    rw [← Matrix.mul_assoc, pad_u_mul_pad_u, proj0_mul_proj1, pad_u_zero, Matrix.zero_mul]
  have e3 : pad_u dim n σx * pad_u dim m proj1 * pad_u dim m proj0 = 0 := by
    rw [Matrix.mul_assoc, pad_u_mul_pad_u, proj1_mul_proj0, pad_u_zero, Matrix.mul_zero]
  have e4 : pad_u dim n σx * pad_u dim m proj1 * (pad_u dim m proj1 * pad_u dim n σx)
      = pad_u dim m proj1 := by
    rw [← Matrix.mul_assoc,
        Matrix.mul_assoc (pad_u dim n σx) (pad_u dim m proj1) (pad_u dim m proj1),
        pad_u_mul_pad_u, proj1_mul_proj1, Matrix.mul_assoc,
        pad_u_disjoint_comm dim m n proj1 σx hm hn hmn, ← Matrix.mul_assoc,
        pad_u_mul_pad_u, σx_mul_σx, pad_u_id hn, Matrix.one_mul]
  rw [hH]
  show (pad_u dim m proj0 + pad_u dim n σx * pad_u dim m proj1)
      * (pad_u dim m proj0 + pad_u dim m proj1 * pad_u dim n σx) = 1
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3, e4, add_zero, zero_add,
      ← pad_u_add, proj0_add_proj1_eq_id, pad_u_id hm]

/-! ## §4. The headline: every well-typed circuit's `uc_eval` is unitary. -/

/-- **`WellTyped ⇒ unitary`.**  For every well-typed `BaseUCom`, `(uc_eval c)ᴴ · uc_eval c = 1`.
    Structural induction: `seq` composes (the inner adjoint cancels), `app1` is `pad_u` of the
    unitary `rotation`, `app2` is `ueval_cnot`, and `app3` is vacuous (`BaseUnitary 3` is empty).
    This is GENUINE unitarity (covers the non-permutation inverse-QFT stage), not mere
    reindex/permutation invariance. -/
theorem uc_eval_unitary_of_wellTyped {dim : Nat} (c : BaseUCom dim)
    (h : UCom.WellTyped dim c) :
    (uc_eval c).conjTranspose * uc_eval c = 1 := by
  revert h
  induction c with
  | seq c1 c2 ih1 ih2 =>
    intro h
    cases h with
    | seq h1 h2 =>
      have hc1 := ih1 h1
      have hc2 := ih2 h2
      show (uc_eval c2 * uc_eval c1).conjTranspose * (uc_eval c2 * uc_eval c1) = 1
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc (uc_eval c1).conjTranspose,
          ← Matrix.mul_assoc (uc_eval c2).conjTranspose, hc2, Matrix.one_mul, hc1]
  | app1 u n =>
    intro h
    cases h with
    | app1 hn =>
      cases u with
      | R θ ϕ lam =>
        show (pad_u dim n (rotation θ ϕ lam)).conjTranspose * pad_u dim n (rotation θ ϕ lam) = 1
        exact pad_u_unitary dim n (rotation θ ϕ lam) hn (rotation_conjTranspose_mul θ ϕ lam)
  | app2 u m n =>
    intro h
    cases h with
    | app2 hm hn hmn =>
      cases u with
      | CNOT =>
        show (ueval_cnot dim m n).conjTranspose * ueval_cnot dim m n = 1
        exact ueval_cnot_unitary dim m n hm hn hmn
  | app3 u m n p =>
    intro _
    nomatch u

end FormalRV.Framework
