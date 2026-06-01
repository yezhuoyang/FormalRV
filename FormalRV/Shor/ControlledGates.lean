/-
  FormalRV.SQIRPort.ControlledGates

  Smallest-vertical-slice toward replacing the `control` stub in
  `Framework/UnitaryOps.lean:972`.

  Background:
  - `BaseUnitary 1` has ONE constructor: `R θ φ λ` (general single-qubit
    rotation). Gates like `X`, `H`, `T` are defined as specific R instances
    (`U_X := R π 0 π`, `U_H := R (π/2) 0 π`, `U_T := R 0 0 (π/4)`, etc.).
  - `BaseUnitary 2` has ONE constructor: `CNOT`.
  - There is NO `BaseUnitary 3` constructor — `CCX` is a derived 16-gate
    circuit (H, T, T†, CNOT). `UCom.app3` therefore has no real instances
    in `BaseUCom` and the `control q (UCom.app3 _ _ _ _) = SKIP` clause is
    vacuous.
  - The actual blocker is `control q (UCom.app1 _ _) = SKIP`, which strips
    every single-qubit gate from any controlled circuit. Because
    `BaseUnitary 1` is entirely `R θ φ λ`, the correct replacement must
    handle the full general rotation (no easy partial fix on `X` only at
    the BaseUnitary level).

  Modular-multiplier oracle gate-subset analysis:
  - `f_modmult_circuit` in `SQIRPort/Shor.lean` is itself an `axiom`
    (no concrete construction). The review chain uses an abstract
    `u : Nat → BaseUCom (n + anc)` constrained by `ModMulImpl u`.
  - A canonical RCIR implementation would use only `{X, CNOT, CCX}`,
    where `CCX` decomposes to `{H, T, T†, CNOT}`. So even the "X-only"
    intuition pulls in `H` and `T` via CCX.
  - For `QPE_MMI_correct`'s proof, the oracle is universally quantified
    over `BaseUCom`, so the fix must handle arbitrary `R θ φ λ`.

  This file's deliverable (Step 4 of the user's plan): introduce
  `controlled_X` as the simplest concrete case — it equals `CNOT` —
  and prove its matrix-level correctness via the framework's existing
  `pad_ctrl σx` definition. This is the BASE CASE for the future
  full controlled-R port; it does not yet fix `control` globally.

  The next theorems needed (sketched at the bottom of the file as
  future work) are:
  - `controlled_H_correct`: controlled-H = H-conjugated controlled-Z.
  - `controlled_Rz_correct`: controlled-Rz(λ) via Rz(λ/2); CNOT; Rz(-λ/2); CNOT.
  - `controlled_R_correct`: the full general-rotation decomposition.
  Each adds a piece of the future `control` rewrite without touching
  the global stub.
-/

import FormalRV.Core.QuantumGate
import FormalRV.Core.UnitarySem
import FormalRV.Core.UnitaryOps
import FormalRV.Core.PadAction
import FormalRV.Shor.QPE

namespace FormalRV.SQIRPort

open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-! ## Step 1: the simplest controlled gate — `controlled_X` -/

/-- **Controlled-X = CNOT** as a `BaseUCom` term.

This is the trivially-correct base case for any future fix of the
`control` stub: `control q (UCom.app1 U_X t)` should produce a
`BaseUCom` whose semantics equal `pad_ctrl dim q t σx`, and the
shortest such circuit is the framework's built-in `CNOT q t`.

The definition is intentionally `rfl`-equal to `CNOT q t` so that
downstream uses can be transparently swapped. -/
noncomputable def controlled_X {dim : Nat} (q t : Nat) : BaseUCom dim :=
  CNOT q t

/-! ## Step 2: matrix-level correctness theorem -/

/-- **`controlled_X`'s matrix semantics is `pad_ctrl dim q t σx`** —
the standard projector-decomposition form of a controlled-X gate.

This holds by `rfl` because `uc_eval (CNOT q t) = ueval_cnot dim q t
= pad_ctrl dim q t σx` (unfolding `uc_eval`'s app2 branch + the
definition of `ueval_cnot`).

This theorem is the **matrix-level** correctness claim for the
controlled-X gate; it is the form a future `control`-stub fix
would need to satisfy for the `app1 U_X` case. -/
theorem uc_eval_controlled_X_eq_pad_ctrl {dim : Nat} (q t : Nat) :
    uc_eval (controlled_X q t : BaseUCom dim) = pad_ctrl dim q t σx := rfl

/-! ## Step 3: basis-vector action correctness -/

/-- **`controlled_X` acts on basis states as expected**: on input
`|f(0)...f(dim-1)⟩`, it produces the state with bit `t` XORed with
bit `q`, i.e., classical controlled-X.

Direct lift of the framework's `f_to_vec_CNOT_proved`. Together with
`uc_eval_controlled_X_eq_pad_ctrl`, this gives both the matrix-level
and operational (basis-state) characterizations of controlled-X. -/
theorem controlled_X_acts_on_basis (n q t : Nat) (f : Nat → Bool)
    (hq : q < n) (ht : t < n) (hqt : q ≠ t) :
    uc_eval (controlled_X q t : BaseUCom n) * f_to_vec n f
      = f_to_vec n (update f t (xor (f t) (f q))) := by
  unfold controlled_X
  exact f_to_vec_CNOT_proved n q t f hq ht hqt

/-! ## Step 4: `controlled_Rz` — the controlled-Z-axis-phase gate

This is the smallest NONTRIVIAL controlled-rotation. Rotation convention
verified by inspection of `Framework/UnitarySem.lean:170`:

  `rotation θ φ λ = !![cos(θ/2),       -exp(iλ)·sin(θ/2);
                       exp(iφ)·sin(θ/2), exp(i(φ+λ))·cos(θ/2)]`

For `θ = 0, φ = 0`, this is `rotation 0 0 λ = !![1, 0; 0, exp(iλ)]`,
the **phase gate** `P(λ)`. (NOT the symmetric Rz form
`diag(exp(-iλ/2), exp(iλ/2))` — this framework's `U_Rz λ := R 0 0 λ`
matches the asymmetric Qiskit/SQIR convention.)

The standard decomposition of controlled-P(λ) is:

  CP(λ) = Rz(λ/2) q ; CNOT q t ; Rz(-λ/2) t ; CNOT q t ; Rz(λ/2) t

No additional control-qubit phase is needed because P(0)|0⟩ = |0⟩ has
no relative phase contribution. -/

/-- **Controlled-Rz (controlled-phase) decomposition.** SQIRPort-namespaced
local copy; the `{dim}`-polymorphic version
`FormalRV.Framework.BaseUCom.controlled_Rz` was moved into the
framework 2026-05-26 to support `QFTinv`'s replacement. Both have
identical bodies; references inside this file go through the local
copy. -/
noncomputable def controlled_Rz {dim : Nat} (q t : Nat) (lam : ℝ) : BaseUCom dim :=
  UCom.seq (BaseUCom.Rz (lam/2) q)
    (UCom.seq (BaseUCom.CNOT q t)
      (UCom.seq (BaseUCom.Rz (-(lam/2)) t)
        (UCom.seq (BaseUCom.CNOT q t)
          (BaseUCom.Rz (lam/2) t))))

/-- **`controlled_Rz` basis-vector action correctness** (the
arbitrary-dimensional theorem, per the user's "best outcome" target).

For any `dim`, `q < dim`, `t < dim`, `q ≠ t`, real angle `λ`, and
Boolean function `f`, the 5-gate decomposition above acting on
`f_to_vec dim f` gives `(if f q ∧ f t then exp(iλ) else 1) • f_to_vec
dim f` — exactly the controlled-phase action.

Proof: walk the 5-gate sequence one factor at a time using
`f_to_vec_Rz_uc_eval` (single-qubit Rz on basis state) and
`f_to_vec_CNOT_proved` (CNOT on basis state). The intermediate
`update` after CNOT is reversed by the second CNOT (the double
application is the identity on Booleans), so the final state is
`f_to_vec f` again, scaled by the product of three scalars
`c1 · c2 · c3`. A by-cases analysis on `(f q, f t)` shows
`c1 · c2 · c3 = if f q ∧ f t then exp(iλ) else 1`.

Kernel-clean. -/
theorem controlled_Rz_acts_on_basis_correct
    (dim q t : Nat) (hq : q < dim) (ht : t < dim) (hqt : q ≠ t)
    (lam : ℝ) (f : Nat → Bool) :
    uc_eval (controlled_Rz q t lam : BaseUCom dim) * f_to_vec dim f
      = (if f q ∧ f t then Complex.exp ((lam : ℂ) * Complex.I) else 1)
        • f_to_vec dim f := by
  unfold controlled_Rz
  simp only [uc_eval]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [f_to_vec_Rz_uc_eval dim q hq (lam/2) f]
  rw [Matrix.mul_smul, f_to_vec_CNOT_proved dim q t f hq ht hqt]
  rw [Matrix.mul_smul, f_to_vec_Rz_uc_eval dim t ht (-(lam/2))]
  rw [Matrix.mul_smul, Matrix.mul_smul]
  rw [Matrix.mul_smul, f_to_vec_CNOT_proved dim q t _ hq ht hqt]
  rw [Matrix.mul_smul, f_to_vec_Rz_uc_eval dim t ht (lam/2)]
  have h_q_in_g : (update f t (xor (f t) (f q))) q = f q := by
    have : q ≠ t := hqt; simp [update, this]
  have h_t_in_g : (update f t (xor (f t) (f q))) t = xor (f t) (f q) := by
    simp [update]
  have h_uu : update (update f t (xor (f t) (f q))) t
                (xor ((update f t (xor (f t) (f q))) t)
                     ((update f t (xor (f t) (f q))) q))
              = f := by
    rw [h_q_in_g, h_t_in_g]
    funext k
    by_cases h : k = t
    · rw [h]; simp [update]
    · simp [update, h]
  rw [h_uu]
  rw [smul_smul, smul_smul]
  congr 1
  by_cases hq_val : f q
  · by_cases ht_val : f t
    · simp [hq_val, ht_val]
      rw [← Complex.exp_add]; congr 1; ring
    · simp [hq_val, ht_val]
      rw [← Complex.exp_add]
      have h0 : ((↑lam / 2 : ℂ) * Complex.I + -(↑lam / 2 * Complex.I)) = 0 := by ring
      rw [h0, Complex.exp_zero]
  · by_cases ht_val : f t
    · simp [hq_val, ht_val]
      rw [← Complex.exp_add]
      have h0 : (-(↑lam / 2 * Complex.I) + (↑lam / 2 : ℂ) * Complex.I) = 0 := by ring
      rw [h0, Complex.exp_zero]
    · simp [hq_val, ht_val]

/-! ## Step 5: matrix-equality lifting — `matrix_eq_of_f_to_vec_action`

The framework's `matrix_eq_of_basis_action` in `Framework/PadAction.lean`
gives matrix equality from agreement on `basis_vector`-indexed columns.
The framework's `basis_vector_eq_f_to_vec_nat` bridges
`basis_vector (2^n) j = f_to_vec n (nat_to_funbool n j)` for `j < 2^n`.

Composing the two yields the desired "matrix from `f_to_vec`-action"
lifting lemma. This will be reusable for `controlled_R`, `controlled_H`,
`controlled_T`, and eventually the global `control` fix. -/

/-- **Matrix-equality lifting for `f_to_vec` action**: two square matrices
on `Fin (2^dim)` are equal iff they agree on every `f_to_vec dim f`
column.

Direct corollary of `Framework.matrix_eq_of_basis_action` plus the
`basis_vector ↔ f_to_vec` bridge `basis_vector_eq_f_to_vec_nat`. -/
theorem matrix_eq_of_f_to_vec_action {dim : Nat}
    (A B : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ)
    (h : ∀ f : Nat → Bool, A * f_to_vec dim f = B * f_to_vec dim f) :
    A = B := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat dim k.val k.isLt]
  exact h _

/-! ## Step 6: `pad_ctrl` basis-vector action for the diagonal rotation -/

/-- **`pad_ctrl` basis-vector action for `rotation 0 0 λ`**: the
projector-decomposition form of controlled-phase matches the
controlled-Rz semantics on `f_to_vec` basis states.

    pad_ctrl dim q t (rotation 0 0 λ) · f_to_vec dim f
      = (if f q ∧ f t then exp(iλ) else 1) • f_to_vec dim f.

Proof: unfold `pad_ctrl = pad_u q proj0 + pad_u q proj1 · pad_u t M`,
distribute over `+` and `*`, apply
`pad_u_proj0_on_f_to_vec`, `pad_u_proj1_on_f_to_vec`,
`f_to_vec_Rz_proved`, and case-split on `(f q, f t)`. -/
theorem pad_ctrl_Rz_acts_on_basis
    (dim q t : Nat) (hq : q < dim) (ht : t < dim)
    (lam : ℝ) (f : Nat → Bool) :
    pad_ctrl dim q t (rotation 0 0 lam) * f_to_vec dim f
      = (if f q ∧ f t then Complex.exp ((lam : ℂ) * Complex.I) else 1)
        • f_to_vec dim f := by
  unfold pad_ctrl
  rw [Matrix.add_mul, Matrix.mul_assoc]
  rw [pad_u_proj0_on_f_to_vec dim q hq f]
  rw [f_to_vec_Rz_proved dim t ht lam f]
  rw [Matrix.mul_smul]
  rw [pad_u_proj1_on_f_to_vec dim q hq f]
  by_cases hq_val : f q <;> by_cases ht_val : f t <;>
    simp [hq_val, ht_val]

/-! ## Step 7: matrix equality for `controlled_Rz` — final assembly -/

/-- **`controlled_Rz` matrix-equality correctness** (Phase 4.B's first
real building block):

    uc_eval (controlled_Rz q t λ : BaseUCom dim)
      = pad_ctrl dim q t (rotation 0 0 λ).

Closes the matrix-equality target by combining:
- `controlled_Rz_acts_on_basis_correct` (5-gate decomposition's action)
- `pad_ctrl_Rz_acts_on_basis` (projector form's action)
- `matrix_eq_of_f_to_vec_action` (matrix equality from basis-action).

Both sides agree pointwise on `f_to_vec`, hence are equal as matrices.
Kernel-clean. -/
theorem uc_eval_controlled_Rz_eq_pad_ctrl {dim : Nat}
    (q t : Nat) (hq : q < dim) (ht : t < dim) (hqt : q ≠ t)
    (lam : ℝ) :
    uc_eval (controlled_Rz q t lam : BaseUCom dim)
      = pad_ctrl dim q t (rotation 0 0 lam) := by
  apply matrix_eq_of_f_to_vec_action
  intro f
  rw [controlled_Rz_acts_on_basis_correct dim q t hq ht hqt lam f]
  rw [pad_ctrl_Rz_acts_on_basis dim q t hq ht lam f]

/-! ## Step 8: full controlled-R(θ,φ,λ) decomposition — pure 2×2 algebraic lemma

The general single-qubit rotation `rotation θ φ λ` admits the "ABXBXC"
decomposition (Nielsen-Chuang Lemma 4.3 adapted to this framework's
asymmetric `Rz = P` convention):

    rotation θ φ λ = exp(i(φ+λ)/2) • (A · σx · B · σx · C)

with
- C := rotation 0 0 ((λ-φ)/2)           [= P((λ-φ)/2)]
- B := rotation (-θ/2) 0 (-(φ+λ)/2)     [= Ry(-θ/2) · P(-(φ+λ)/2)]
- A := rotation (θ/2) φ 0               [= P(φ) · Ry(θ/2)]
- α := (φ+λ)/2                          (global phase, lifted to control via P(α))

Verified manually:
- A · B · C = I  (so controlled-U acts as identity when control is |0⟩)
- e^{iα} · A · X · B · X · C = rotation θ φ λ
  (so the circuit form does produce U when control is |1⟩, modulo the
  global phase that the control-side P(α) absorbs).

This is **Task 2** (the critical checkpoint per the user's staged plan):
the pure 2×2 matrix algebraic identity. If this closed, the
decomposition is correct; the remaining work is the circuit-level lift. -/

/-- **2×2 ABXBXC decomposition of `rotation θ φ λ`** — the pure single-
qubit matrix identity.

Proof: matrix extensionality on Fin 2 × Fin 2, then case-by-case
verification. Each of the 4 entries reduces to a product of complex
exponentials and trigonometric half-angle terms. Three helper
identities are used:

- `h_cos_half`: `cos(x/2) = cos²(x/4) - sin²(x/4)` (cos double-angle).
- `h_sin_half`: `sin(x/2) = 2 sin(x/4) cos(x/4)` (sin double-angle).
- Two complex-exp phase identities:
    * `exp((φ+λ)/2·I) · exp(-(λ+φ)/2·I) = 1` (cancellation)
    * `exp((φ+λ)/2·I) · exp((λ-φ)/2·I) = exp(λ·I)` (combination)

Plus `exp((φ+λ)·I) = exp(λ·I) · exp(φ·I)` for the (1,1) entry.

Kernel-clean. ~70 lines. -/
theorem rotation_eq_exp_smul_ABXBXC (θ φ lam : ℝ) :
    rotation θ φ lam
      = Complex.exp (((φ + lam) / 2 : ℂ) * Complex.I) •
        (rotation (θ/2) φ 0 * σx * rotation (-θ/2) 0 (-(φ + lam)/2) * σx
          * rotation 0 0 ((lam - φ)/2)) := by
  have h_cos_half : ∀ x : ℂ, Complex.cos (x/2) = Complex.cos (x/4)^2 - Complex.sin (x/4)^2 := by
    intro x
    have h := Complex.cos_two_mul (x/4)
    have hs : (Complex.sin (x/4))^2 = 1 - (Complex.cos (x/4))^2 := Complex.sin_sq (x/4)
    have hx : 2 * (x/4) = x/2 := by ring
    rw [hx] at h; linear_combination h + hs
  have h_sin_half : ∀ x : ℂ, Complex.sin (x/2) = 2 * Complex.sin (x/4) * Complex.cos (x/4) := by
    intro x
    have h := Complex.sin_two_mul (x/4)
    have hx : 2 * (x/4) = x/2 := by ring
    rw [hx] at h; exact h
  have h_θ2_div : (θ/2)/2 = θ/4 := by ring
  have h_negθ2_div : ((-θ/2))/2 = -(θ/4) := by ring
  have h_pc1 : (Complex.exp ((↑φ + ↑lam) / 2 * Complex.I) *
                Complex.exp (((-↑lam + -↑φ) / 2 : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_add]
    rw [show (((↑φ + ↑lam) / 2 * Complex.I + (-↑lam + -↑φ) / 2 * Complex.I) : ℂ) = 0 from by ring]
    exact Complex.exp_zero
  have h_pc2 : (Complex.exp ((↑φ + ↑lam) / 2 * Complex.I) *
                Complex.exp (((↑lam - ↑φ) / 2 : ℂ) * Complex.I))
                  = Complex.exp (↑lam * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h_phi_lam : Complex.exp ((↑φ + ↑lam) * Complex.I)
                  = Complex.exp (↑lam * Complex.I) * Complex.exp (↑φ * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, σx, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
          Real.cos_zero, Real.sin_zero, Complex.exp_zero, h_θ2_div, h_negθ2_div,
          Real.sin_neg, Real.cos_neg]
  · -- (0, 0)
    rw [h_cos_half θ]
    rw [show (Complex.exp ((↑φ + ↑lam) / 2 * Complex.I) *
              (-(Complex.sin (↑θ/4) * (Complex.exp ((-↑lam + -↑φ) / 2 * Complex.I) *
                                       Complex.sin (↑θ/4))) +
               Complex.cos (↑θ/4) * (Complex.exp ((-↑lam + -↑φ) / 2 * Complex.I) *
                                      Complex.cos (↑θ/4))) : ℂ)
            = (Complex.exp ((↑φ + ↑lam) / 2 * Complex.I) *
                Complex.exp ((-↑lam + -↑φ) / 2 * Complex.I)) *
              (Complex.cos (↑θ/4)^2 - Complex.sin (↑θ/4)^2) from by ring]
    rw [h_pc1, one_mul]
  · -- (0, 1)
    rw [h_sin_half θ]
    rw [show (Complex.exp ((↑φ + ↑lam) / 2 * Complex.I) *
              ((-(Complex.sin (↑θ/4) * Complex.cos (↑θ/4)) +
                -(Complex.cos (↑θ/4) * Complex.sin (↑θ/4))) *
               Complex.exp ((↑lam - ↑φ) / 2 * Complex.I)) : ℂ)
            = -((Complex.exp ((↑φ + ↑lam) / 2 * Complex.I) *
                  Complex.exp ((↑lam - ↑φ) / 2 * Complex.I)) *
                (2 * Complex.sin (↑θ/4) * Complex.cos (↑θ/4))) from by ring]
    rw [h_pc2]
  · -- (1, 0)
    rw [h_sin_half θ]
    rw [show (Complex.exp ((↑φ + ↑lam) / 2 * Complex.I) *
              (Complex.exp (↑φ * Complex.I) * Complex.cos (↑θ/4) *
                  (Complex.exp ((-↑lam + -↑φ) / 2 * Complex.I) * Complex.sin (↑θ/4)) +
               Complex.exp (↑φ * Complex.I) * Complex.sin (↑θ/4) *
                  (Complex.exp ((-↑lam + -↑φ) / 2 * Complex.I) * Complex.cos (↑θ/4))) : ℂ)
            = (Complex.exp ((↑φ + ↑lam) / 2 * Complex.I) *
                Complex.exp ((-↑lam + -↑φ) / 2 * Complex.I)) *
              Complex.exp (↑φ * Complex.I) *
              (2 * Complex.sin (↑θ/4) * Complex.cos (↑θ/4)) from by ring]
    rw [h_pc1, one_mul]
  · -- (1, 1)
    rw [h_cos_half θ]
    rw [show (Complex.exp ((↑φ + ↑lam) / 2 * Complex.I) *
              ((Complex.exp (↑φ * Complex.I) * Complex.cos (↑θ/4) * Complex.cos (↑θ/4) +
                -(Complex.exp (↑φ * Complex.I) * Complex.sin (↑θ/4) * Complex.sin (↑θ/4))) *
               Complex.exp ((↑lam - ↑φ) / 2 * Complex.I)) : ℂ)
            = (Complex.exp ((↑φ + ↑lam) / 2 * Complex.I) *
                Complex.exp ((↑lam - ↑φ) / 2 * Complex.I)) *
              Complex.exp (↑φ * Complex.I) *
              (Complex.cos (↑θ/4)^2 - Complex.sin (↑θ/4)^2) from by ring]
    rw [h_pc2, h_phi_lam]

/-! ## Step 9: `controlled_R` definition (Task 3)

The `controlled_R` definition now lives in `Framework/UnitaryOps.lean`
(near `control`) so the global `control` stub can use it. We re-export
it here via `open FormalRV.Framework.BaseUCom` (already in scope at
the top of this file). -/

/-! ## Step 10: roadmap to `uc_eval_controlled_R_eq_pad_ctrl`

With the 2×2 algebraic identity now proven (`rotation_eq_exp_smul_ABXBXC`),
the next-tick deliverable is the matrix-equality theorem

    uc_eval (controlled_R q t θ φ λ : BaseUCom dim)
      = pad_ctrl dim q t (rotation θ φ λ).

The cleanest path forward uses the framework's existing
`pad_u_disjoint_comm'` and `pad_u_pad_ctrl_disjoint_comm`
infrastructure (`Framework/UnitarySem.lean:~1083`). Sketch:

1. Expand `uc_eval (controlled_R ...)` via `uc_eval_seq` (in reverse
   order) into a product of `pad_u (rotation _ _ _)` and `ueval_cnot
   = pad_ctrl _ σx` matrices.

2. Factor out the control-qubit phase `pad_u q (rotation 0 0 ((φ+λ)/2))`
   using `pad_u_disjoint_comm'` (the control qubit is `q`, all other
   gates act on target `t`, with `q ≠ t`).

3. The remaining product (target-side: `A · X · B · X · C` lifted via
   `pad_u`) equals `pad_u t (A · σx · B · σx · C)` via repeated
   application of `pad_u_mul_pad_u` (composition of single-qubit gates
   at the same qubit).

4. Apply `rotation_eq_exp_smul_ABXBXC` to identify
   `A · σx · B · σx · C = exp(-i(φ+λ)/2) · rotation θ φ λ`.

5. Combine the control-side phase factor `pad_u q (rotation 0 0 ((φ+λ)/2))`
   with the target-side residual `pad_u t (rotation θ φ λ)` plus the
   control-side projector decomposition to recover
   `pad_ctrl dim q t (rotation θ φ λ)`. This step uses the
   `pad_ctrl = pad_u q proj0 + pad_u q proj1 * pad_u t M` definition
   plus careful handling of the projectors interacting with `rotation
   0 0 α` (P(α) acts diagonally so `proj0 · P(α) = proj0` and
   `proj1 · P(α) = e^{iα} · proj1`).

Estimated scope: 150-300 LOC. Each step has clear infrastructure in
the framework; the bulk is the projector-rotation algebra in step 5.

In parallel, two strictly smaller next-tick options:
- **`controlled_H`** as the special case `θ=π/2, φ=0, λ=π` after
  `controlled_R` is proven (~10 LOC).
- **`controlled_T`** as `θ=0, φ=0, λ=π/4` — this is actually a
  `controlled_Rz`-class gate, already covered by
  `uc_eval_controlled_Rz_eq_pad_ctrl`. -/

/-! ## Step 11: helpers toward `uc_eval_controlled_R_eq_pad_ctrl`

Per the user's staged plan: build the matrix-equality lift from the
2×2 algebraic identity via reusable helper lemmas. This pass closes
the projector-phase identities and the **control-phase absorption**
lemma (Task 2 in the user's plan). The remaining 5-gate-collapse
lemma (Task 3 / `pad_ctrl_circuit_collapse`) is the next block.

`UCom.seq` order (verified by inspection of `Framework/UnitarySem.lean:1191`):
`uc_eval (UCom.seq c₁ c₂) = uc_eval c₂ * uc_eval c₁`. Right-to-left
matrix composition. So the circuit
  `seq (Rz α q) (seq C_t (seq CNOT (seq B_t (seq CNOT A_t))))`
yields the matrix
  `pad_u t A * pad_ctrl q t σx * pad_u t B * pad_ctrl q t σx *
   pad_u t C * pad_u q P(α)`. -/

/-- **Projector-phase identity** for proj0 (single-qubit 2x2). -/
private theorem proj0_mul_rotation_phase (α : ℝ) :
    proj0 * rotation 0 0 α = proj0 := by
  unfold proj0 rotation
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_zero, Real.sin_zero,
          Complex.exp_zero]

/-- **Projector-phase identity** for proj1: produces a scalar `exp(iα)`. -/
private theorem proj1_mul_rotation_phase (α : ℝ) :
    proj1 * rotation 0 0 α = Complex.exp ((α : ℂ) * Complex.I) • proj1 := by
  unfold proj1 rotation
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two, Real.cos_zero,
          Real.sin_zero, Complex.exp_zero]

/-- **Control-phase absorption** (Task 2 / L1 of the user's plan).

When the control-side phase `pad_u q (rotation 0 0 α) = P(α)_q` is
applied AFTER (right-multiplied by) a `pad_ctrl q t M`, it gets absorbed
as a scalar `exp(iα)` on the inner target matrix:

    pad_ctrl dim q t M  *  pad_u dim q (rotation 0 0 α)
      =  pad_ctrl dim q t (exp(iα) • M).

Proof: expand `pad_ctrl = pad_u q proj0 + pad_u q proj1 · pad_u t M`,
distribute, commute the target-side `pad_u t M` past the control-side
phase via `pad_u_disjoint_comm'`, combine same-qubit projector·phase
products via `pad_u_mul_pad_u`, then apply the projector-phase identities
`proj0_mul_rotation_phase` (identity) and `proj1_mul_rotation_phase`
(scalar e^iα). Final scalar normalization via `pad_u_smul` +
`smul_mul_assoc` + `Matrix.mul_smul`.

Kernel-clean. ~12 lines after the helpers. -/
theorem pad_ctrl_mul_control_phase {dim : Nat} (q t : Nat) (hqt : q ≠ t)
    (α : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_ctrl dim q t M * pad_u dim q (rotation 0 0 α)
      = pad_ctrl dim q t (Complex.exp ((α : ℂ) * Complex.I) • M) := by
  unfold pad_ctrl
  rw [Matrix.add_mul]
  rw [pad_u_mul_pad_u dim q (rotation 0 0 α) proj0]
  rw [proj0_mul_rotation_phase]
  rw [Matrix.mul_assoc]
  rw [pad_u_disjoint_comm' dim t q M (rotation 0 0 α) (Ne.symm hqt)]
  rw [← Matrix.mul_assoc]
  rw [pad_u_mul_pad_u dim q (rotation 0 0 α) proj1]
  rw [proj1_mul_rotation_phase, pad_u_smul, smul_mul_assoc]
  congr 1
  rw [pad_u_smul, Matrix.mul_smul]

/-! ## Step 12: reusable helpers + `pad_ctrl_circuit_collapse`

Per the user's staged plan: build the 5-gate collapse lemma via
reusable helper lemmas (per-branch term collapse, two-branch
collapse, sandwich collapse, left/right absorption) so the result is
generic across future controlled-circuit proofs. -/

/-- **Per-branch term collapse.** A single `Pa_q * A_t * Pb_q * B_t`
product (with target factors `A`, `B` and control projectors `Pa`,
`Pb`) commutes the target through the control via `pad_u_disjoint_
comm'`, then combines same-qubit pad_u's via `pad_u_mul_pad_u`. -/
private theorem pad_branch_term (dim q t : Nat) (hqt : q ≠ t)
    (Pa Pb A B : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u dim q Pa * pad_u dim t A * (pad_u dim q Pb * pad_u dim t B)
      = pad_u dim q (Pa * Pb) * pad_u dim t (A * B) := by
  rw [← Matrix.mul_assoc (pad_u dim q Pa * pad_u dim t A) (pad_u dim q Pb) (pad_u dim t B)]
  rw [Matrix.mul_assoc (pad_u dim q Pa) (pad_u dim t A) (pad_u dim q Pb)]
  rw [pad_u_disjoint_comm' dim t q A Pb (Ne.symm hqt)]
  rw [← Matrix.mul_assoc (pad_u dim q Pa) (pad_u dim q Pb) (pad_u dim t A)]
  rw [pad_u_mul_pad_u dim q Pb Pa]
  rw [Matrix.mul_assoc]
  rw [pad_u_mul_pad_u dim t B A]

/-- **Two-branch collapse.** Multiplying two control-projector-branch
sums collapses via projector orthogonality (`proj0 · proj1 = 0`)
and idempotence (`proj0 · proj0 = proj0`):

    (P0·A0 + P1·A1) * (P0·B0 + P1·B1) = P0·(A0·B0) + P1·(A1·B1)

The cross terms vanish because the control projectors are orthogonal. -/
private theorem pad_ctrl_two_branch_collapse (dim q t : Nat) (hqt : q ≠ t)
    (A0 A1 B0 B1 : Matrix (Fin 2) (Fin 2) ℂ) :
    (pad_u dim q proj0 * pad_u dim t A0 + pad_u dim q proj1 * pad_u dim t A1) *
    (pad_u dim q proj0 * pad_u dim t B0 + pad_u dim q proj1 * pad_u dim t B1)
      = pad_u dim q proj0 * pad_u dim t (A0 * B0)
        + pad_u dim q proj1 * pad_u dim t (A1 * B1) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  rw [pad_branch_term dim q t hqt proj0 proj0 A0 B0]
  rw [pad_branch_term dim q t hqt proj0 proj1 A0 B1]
  rw [pad_branch_term dim q t hqt proj1 proj0 A1 B0]
  rw [pad_branch_term dim q t hqt proj1 proj1 A1 B1]
  rw [proj0_mul_proj0, proj1_mul_proj1, proj0_mul_proj1, proj1_mul_proj0]
  rw [pad_u_zero, Matrix.zero_mul, Matrix.zero_mul]
  abel

/-- Rewrite `pad_ctrl` in standard branch-sum form. Uses `pad_u_id`
to fold the trivial proj0 branch's target into the explicit `σi_t`
form needed by `pad_ctrl_two_branch_collapse`. -/
private theorem pad_ctrl_eq_branch_sum (dim q t : Nat) (ht : t < dim)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_ctrl dim q t M
      = pad_u dim q proj0 * pad_u dim t σi + pad_u dim q proj1 * pad_u dim t M := by
  unfold pad_ctrl
  rw [pad_u_id ht, Matrix.mul_one]

/-- **CNOT sandwich collapse.** The composition `CNOT * pad_u t N * CNOT`
collapses to a single projector-branch sum:

    pad_ctrl q t σx * pad_u t N * pad_ctrl q t σx
      = pad_u q proj0 * pad_u t N + pad_u q proj1 * pad_u t (σx · N · σx).

This is the central lemma for the 5-gate circuit collapse. The
proj0 branch leaves `N` untouched; the proj1 branch conjugates `N`
by `σx`. -/
private theorem cnot_sandwich_collapse (dim q t : Nat) (ht : t < dim) (hqt : q ≠ t)
    (N : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_ctrl dim q t σx * pad_u dim t N * pad_ctrl dim q t σx
      = pad_u dim q proj0 * pad_u dim t N
        + pad_u dim q proj1 * pad_u dim t (σx * N * σx) := by
  rw [pad_ctrl_eq_branch_sum dim q t ht σx]
  have step1 :
      (pad_u dim q proj0 * pad_u dim t σi + pad_u dim q proj1 * pad_u dim t σx) *
        pad_u dim t N
        = pad_u dim q proj0 * pad_u dim t N
          + pad_u dim q proj1 * pad_u dim t (σx * N) := by
    rw [Matrix.add_mul]
    rw [Matrix.mul_assoc (pad_u dim q proj0) (pad_u dim t σi) (pad_u dim t N)]
    rw [Matrix.mul_assoc (pad_u dim q proj1) (pad_u dim t σx) (pad_u dim t N)]
    rw [pad_u_mul_pad_u dim t N σi, pad_u_mul_pad_u dim t N σx]
    rw [σi_eq_one, Matrix.one_mul]
  rw [Matrix.mul_assoc (pad_u dim q proj0 * pad_u dim t σi + pad_u dim q proj1 * pad_u dim t σx)
        (pad_u dim t N)
        (pad_u dim q proj0 * pad_u dim t σi + pad_u dim q proj1 * pad_u dim t σx)]
  rw [← Matrix.mul_assoc]
  rw [step1]
  rw [pad_ctrl_two_branch_collapse dim q t hqt N (σx * N) σi σx]
  rw [σi_eq_one, Matrix.mul_one]

/-- **Right-absorption helper.** A `pad_u t X` factor on the right of
a projector-branch sum gets absorbed into both branches' target
matrices. -/
private theorem absorb_right_branch (dim q t : Nat)
    (A B X : Matrix (Fin 2) (Fin 2) ℂ) :
    (pad_u dim q proj0 * pad_u dim t A + pad_u dim q proj1 * pad_u dim t B) *
      pad_u dim t X
      = pad_u dim q proj0 * pad_u dim t (A * X)
        + pad_u dim q proj1 * pad_u dim t (B * X) := by
  rw [Matrix.add_mul]
  rw [Matrix.mul_assoc (pad_u dim q proj0) (pad_u dim t A) (pad_u dim t X)]
  rw [Matrix.mul_assoc (pad_u dim q proj1) (pad_u dim t B) (pad_u dim t X)]
  rw [pad_u_mul_pad_u dim t X A, pad_u_mul_pad_u dim t X B]

/-- **Left-absorption helper.** Symmetric to `absorb_right_branch` —
the `pad_u t X` factor must first commute through the control
projectors before absorbing into each target. -/
private theorem absorb_left_branch (dim q t : Nat) (hqt : q ≠ t)
    (A B X : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u dim t X *
      (pad_u dim q proj0 * pad_u dim t A + pad_u dim q proj1 * pad_u dim t B)
      = pad_u dim q proj0 * pad_u dim t (X * A)
        + pad_u dim q proj1 * pad_u dim t (X * B) := by
  rw [Matrix.mul_add]
  rw [← Matrix.mul_assoc (pad_u dim t X) (pad_u dim q proj0) (pad_u dim t A)]
  rw [pad_u_disjoint_comm' dim t q X proj0 (Ne.symm hqt)]
  rw [Matrix.mul_assoc (pad_u dim q proj0) (pad_u dim t X) (pad_u dim t A)]
  rw [pad_u_mul_pad_u dim t A X]
  rw [← Matrix.mul_assoc (pad_u dim t X) (pad_u dim q proj1) (pad_u dim t B)]
  rw [pad_u_disjoint_comm' dim t q X proj1 (Ne.symm hqt)]
  rw [Matrix.mul_assoc (pad_u dim q proj1) (pad_u dim t X) (pad_u dim t B)]
  rw [pad_u_mul_pad_u dim t B X]

/-- **5-gate circuit collapse.** Given `K · N · M = 1`, the 5-gate
sandwich `K_t · CNOT · N_t · CNOT · M_t` collapses to a single
`pad_ctrl` of the conjugated middle matrix:

    pad_u t K · pad_ctrl q t σx · pad_u t N · pad_ctrl q t σx · pad_u t M
      = pad_ctrl q t (K · σx · N · σx · M)

This is Task 3 / L2 of the user's plan. Proof flow: reassociate to
group the inner sandwich, apply `cnot_sandwich_collapse` for the
inner CNOT pair, then `absorb_left_branch` for the outer `K`,
`absorb_right_branch` for the outer `M`, then `h_abc` collapses the
proj0 branch to identity, leaving `pad_ctrl q t (K · σx · N · σx · M)`. -/
theorem pad_ctrl_circuit_collapse {dim : Nat}
    (q t : Nat) (hq : q < dim) (ht : t < dim) (hqt : q ≠ t)
    (M N K : Matrix (Fin 2) (Fin 2) ℂ) (h_abc : K * N * M = 1) :
    pad_u dim t K * pad_ctrl dim q t σx * pad_u dim t N * pad_ctrl dim q t σx *
        pad_u dim t M
      = pad_ctrl dim q t (K * σx * N * σx * M) := by
  have reassoc :
      pad_u dim t K * pad_ctrl dim q t σx * pad_u dim t N * pad_ctrl dim q t σx *
          pad_u dim t M
        = pad_u dim t K *
            (pad_ctrl dim q t σx * pad_u dim t N * pad_ctrl dim q t σx) *
            pad_u dim t M := by
    rw [Matrix.mul_assoc (pad_u dim t K) (pad_ctrl dim q t σx) (pad_u dim t N)]
    rw [Matrix.mul_assoc (pad_u dim t K) (pad_ctrl dim q t σx * pad_u dim t N) (pad_ctrl dim q t σx)]
  rw [reassoc]
  rw [cnot_sandwich_collapse dim q t ht hqt N]
  rw [absorb_left_branch dim q t hqt N (σx * N * σx) K]
  rw [absorb_right_branch dim q t (K * N) (K * (σx * N * σx)) M]
  rw [show ((K * N) * M : Matrix (Fin 2) (Fin 2) ℂ) = 1 from h_abc]
  rw [show ((K * (σx * N * σx)) * M : Matrix (Fin 2) (Fin 2) ℂ) = K * σx * N * σx * M from by
    rw [← Matrix.mul_assoc K (σx * N) σx, ← Matrix.mul_assoc K σx N]]
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) = σi from σi_eq_one.symm]
  rw [← pad_ctrl_eq_branch_sum dim q t ht (K * σx * N * σx * M)]

/-- **ABC = I identity** for the three rotation matrices `A`, `B`, `C`
appearing in the Nielsen-Chuang controlled-R decomposition.
Concretely: `rotation (θ/2) φ 0 · rotation (-θ/2) 0 (-(φ+λ)/2) ·
rotation 0 0 ((λ-φ)/2) = I`. The proof reduces to (0,0): `cos² +
sin² = 1`; (0,1) and (1,0): both 0; (1,1): a phase-cancellation
identity combined with Pythagoras. This is the algebraic hypothesis
fed to `pad_ctrl_circuit_collapse` in the main matrix-equality
theorem. -/
private theorem rotation_ABC_eq_one (θ φ lam : ℝ) :
    rotation (θ/2) φ 0 * rotation (-θ/2) 0 (-(φ + lam)/2) * rotation 0 0 ((lam - φ)/2)
      = 1 := by
  have h_θ2_div : (θ/2)/2 = θ/4 := by ring
  have h_negθ2_div : ((-θ/2))/2 = -(θ/4) := by ring
  have h_phase_cancel :
      Complex.exp ((↑φ : ℂ) * Complex.I) *
      Complex.exp (((-↑lam - ↑φ) / 2 : ℂ) * Complex.I) *
      Complex.exp (((↑lam - ↑φ) / 2 : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    rw [show ((↑φ : ℂ) * Complex.I + (-↑lam - ↑φ) / 2 * Complex.I +
              (↑lam - ↑φ) / 2 * Complex.I : ℂ) = 0 from by ring]
    exact Complex.exp_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_zero, Real.sin_zero,
          Complex.exp_zero, h_θ2_div, h_negθ2_div, Real.sin_neg, Real.cos_neg]
  · have := Complex.sin_sq_add_cos_sq ((↑θ : ℂ) / 4)
    linear_combination this
  · ring
  · ring
  · have hsc := Complex.sin_sq_add_cos_sq ((↑θ : ℂ) / 4)
    linear_combination
      (Complex.exp ((↑φ : ℂ) * Complex.I) *
         Complex.exp (((-↑lam - ↑φ) / 2 : ℂ) * Complex.I) *
         Complex.exp (((↑lam - ↑φ) / 2 : ℂ) * Complex.I)) * hsc + h_phase_cancel

/-- **MATRIX-EQUALITY THEOREM for `controlled_R`** (the L3 capstone
of the user's plan): the matrix semantics of the `controlled_R q t
θ φ λ` circuit equals the projector-decomposition form
`pad_ctrl dim q t (rotation θ φ λ)`.

Proof flow:
1. Unfold `uc_eval` of the 6-gate `controlled_R` circuit to a
   matrix product `pad_u t A · CNOT · pad_u t B · CNOT · pad_u t C
   · pad_u q P((φ+λ)/2)` (where `A`, `B`, `C` are the rotation
   matrices in the decomposition).
2. Apply `pad_ctrl_circuit_collapse` to the first 5 factors, using
   `rotation_ABC_eq_one` as the `K·N·M = 1` hypothesis. Result:
   `pad_ctrl q t (A · σx · B · σx · C) · pad_u q P((φ+λ)/2)`.
3. Apply `pad_ctrl_mul_control_phase` to absorb the control-phase
   into the inner matrix as `exp(i(φ+λ)/2) • (A · σx · B · σx · C)`.
4. Apply `rotation_eq_exp_smul_ABXBXC` (the 2×2 algebra) backwards
   to identify this with `rotation θ φ λ`.

This is the structural theorem that, once `controlled_R` is wired
into the `control` stub (the global rewrite at
`Framework/UnitaryOps.lean:972`), justifies the `app1` branch's
matrix semantics — and hence unblocks `QPE_MMI_correct`. -/
theorem uc_eval_controlled_R_eq_pad_ctrl {dim : Nat}
    (q t : Nat) (hq : q < dim) (ht : t < dim) (hqt : q ≠ t) (θ φ lam : ℝ) :
    uc_eval (controlled_R q t θ φ lam : BaseUCom dim)
      = pad_ctrl dim q t (rotation θ φ lam) := by
  have h_unfold :
      uc_eval (controlled_R q t θ φ lam : BaseUCom dim)
        = pad_u dim t (rotation (θ/2) φ 0) *
          pad_ctrl dim q t σx *
          pad_u dim t (rotation (-θ/2) 0 (-(φ + lam)/2)) *
          pad_ctrl dim q t σx *
          pad_u dim t (rotation 0 0 ((lam - φ)/2)) *
          pad_u dim q (rotation 0 0 ((φ + lam)/2)) := by
    unfold controlled_R Rz
    rfl
  rw [h_unfold]
  rw [pad_ctrl_circuit_collapse q t hq ht hqt
        (rotation 0 0 ((lam - φ)/2))
        (rotation (-θ/2) 0 (-(φ + lam)/2))
        (rotation (θ/2) φ 0)
        (rotation_ABC_eq_one θ φ lam)]
  rw [pad_ctrl_mul_control_phase q t hqt ((φ + lam)/2) _]
  rw [show (((φ + lam) / 2 : ℝ) : ℂ) = (↑φ + ↑lam) / 2 from by push_cast; ring]
  rw [← rotation_eq_exp_smul_ABXBXC θ φ lam]

/-- **Framework-level wrapper**: the global `control` definition's
matrix semantics on the `app1 (R θ φ λ) t` case equals the projector
form `pad_ctrl dim q t (rotation θ φ λ)`.

This is the user-facing surface of the `control`-stub fix: any place
that uses `control q U` for a single-qubit `U = R θ φ λ` now has a
clean matrix semantics, not the previous `SKIP = 1` stub. Reduces by
definition to `controlled_R`, then chains to
`uc_eval_controlled_R_eq_pad_ctrl`. -/
theorem uc_eval_control_app1_R_eq_pad_ctrl {dim : Nat}
    (q t : Nat) (hq : q < dim) (ht : t < dim) (hqt : q ≠ t)
    (θ φ lam : ℝ) :
    uc_eval (control q (UCom.app1 (BaseUnitary.R θ φ lam) t : BaseUCom dim))
      = pad_ctrl dim q t (rotation θ φ lam) := by
  show uc_eval (controlled_R q t θ φ lam : BaseUCom dim) = _
  exact uc_eval_controlled_R_eq_pad_ctrl q t hq ht hqt θ φ lam

/-! ## Step 14: controlled-CNOT (CCX) projector decomposition

The other base case of the general controlled-circuit semantic theorem.
Uses the basis-action route: prove agreement on every `f_to_vec dim f`,
then lift via `matrix_eq_of_f_to_vec_action`. -/

/-- **CCX as a projector-decomposed controlled-CNOT** (matrix equality).
For pairwise-distinct in-range `q, m, n`,
`uc_eval (CCX q m n) = pad_u q proj0 + pad_u q proj1 · uc_eval (CNOT m n)`.

Proof: by `matrix_eq_of_f_to_vec_action`, suffices to check the basis-
vector action. `f_to_vec_CCX_proved` rewrites the LHS to
`f_to_vec dim (update f n (xor (f n) (f q && f m)))`; the RHS unfolds
via `f_to_vec_CNOT_proved` and the projector-on-f_to_vec lemmas. The
final case split on `f q` matches the two branches. -/
theorem uc_eval_CCX_eq_controlled_CNOT {dim : Nat} (q m n : Nat)
    (hq : q < dim) (hm : m < dim) (hn : n < dim)
    (hqm : q ≠ m) (hqn : q ≠ n) (hmn : m ≠ n) :
    uc_eval (BaseUCom.CCX q m n : BaseUCom dim)
      = pad_u dim q proj0
          + pad_u dim q proj1 * uc_eval (BaseUCom.CNOT m n : BaseUCom dim) := by
  apply matrix_eq_of_f_to_vec_action
  intro f
  rw [f_to_vec_CCX_proved dim q m n hq hm hn hqm hqn hmn f]
  rw [Matrix.add_mul, Matrix.mul_assoc, f_to_vec_CNOT_proved dim m n f hm hn hmn]
  rw [pad_u_proj0_on_f_to_vec dim q hq f,
      pad_u_proj1_on_f_to_vec dim q hq (update f n (xor (f n) (f m)))]
  rw [show update f n (xor (f n) (f m)) q = f q from update_neq f n q _ hqn]
  by_cases hfq : f q
  · simp [hfq]
  · simp [hfq]

/-- **Framework-level wrapper** for the `app2 CNOT` case: the new
`control` definition routes `app2 BaseUnitary.CNOT m n` to `CCX q m n`,
so the matrix semantics of `control q (app2 CNOT m n)` equals the
projector decomposition. -/
theorem uc_eval_control_app2_CNOT_eq_proj_decomp {dim : Nat} (q m n : Nat)
    (hq : q < dim) (hm : m < dim) (hn : n < dim)
    (hqm : q ≠ m) (hqn : q ≠ n) (hmn : m ≠ n) :
    uc_eval (control q (UCom.app2 BaseUnitary.CNOT m n : BaseUCom dim))
      = pad_u dim q proj0
          + pad_u dim q proj1 *
            uc_eval (UCom.app2 BaseUnitary.CNOT m n : BaseUCom dim) := by
  show uc_eval (BaseUCom.CCX q m n : BaseUCom dim) = _
  exact uc_eval_CCX_eq_controlled_CNOT q m n hq hm hn hqm hqn hmn

/-! ## Step 15: freshness-commutation + general controlled-circuit theorem

The last structural piece: for any well-typed `BaseUCom` whose qubit-set
avoids `q`, `uc_eval c` commutes with `pad_u dim q U` for ANY `U`. This
is the key sub-lemma for the inductive proof of the structural
controlled-circuit theorem below. -/

/-- **Freshness commutation.** If `q` is fresh in `c`, then `pad_u dim q U`
commutes with `uc_eval c` for any single-qubit matrix `U`.

Proof by induction on `c`:
- `seq`: commute through both halves via IH;
- `app1 (R θ φ λ) n`: `uc_eval = pad_u n (rotation θ φ λ)`, commutes
  by `pad_u_disjoint_comm'` using `q ≠ n`;
- `app2 CNOT m n`: `uc_eval = pad_ctrl m n σx`, commutes by
  `pad_u_pad_ctrl_disjoint_comm` using `q ≠ m ∧ q ≠ n`;
- `app3`: vacuous since `BaseUnitary 3` is empty. -/
theorem pad_u_comm_uc_eval_of_fresh {dim : Nat} (q : Nat) :
    ∀ (c : BaseUCom dim), is_fresh q c →
      ∀ (U : Matrix (Fin 2) (Fin 2) ℂ),
        pad_u dim q U * uc_eval c = uc_eval c * pad_u dim q U := by
  intro c
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
      intro h_fresh U
      obtain ⟨h₁, h₂⟩ := h_fresh
      show pad_u dim q U * (uc_eval c₂ * uc_eval c₁)
            = (uc_eval c₂ * uc_eval c₁) * pad_u dim q U
      rw [← Matrix.mul_assoc, ih₂ h₂ U, Matrix.mul_assoc, ih₁ h₁ U,
          ← Matrix.mul_assoc]
  | app1 u n =>
      intro h_fresh U
      cases u with
      | R θ φ lam =>
        show pad_u dim q U * pad_u dim n (rotation θ φ lam) = _
        exact pad_u_disjoint_comm' dim q n U (rotation θ φ lam) h_fresh
  | app2 u m n =>
      intro h_fresh U
      cases u
      show pad_u dim q U * pad_ctrl dim m n σx = _
      exact pad_u_pad_ctrl_disjoint_comm dim q m n U σx h_fresh.1 h_fresh.2
  | app3 u _ _ _ => intro _ _; cases u

/-! ### Same-qubit projector identities lifted to `pad_u` -/

private theorem padq_proj0_mul_proj0 (dim q : Nat) :
    pad_u dim q proj0 * pad_u dim q proj0 = pad_u dim q proj0 := by
  rw [pad_u_mul_pad_u dim q proj0 proj0, proj0_mul_proj0]

private theorem padq_proj1_mul_proj1 (dim q : Nat) :
    pad_u dim q proj1 * pad_u dim q proj1 = pad_u dim q proj1 := by
  rw [pad_u_mul_pad_u dim q proj1 proj1, proj1_mul_proj1]

private theorem padq_proj0_mul_proj1 (dim q : Nat) :
    pad_u dim q proj0 * pad_u dim q proj1 = 0 := by
  rw [pad_u_mul_pad_u dim q proj1 proj0, proj0_mul_proj1, pad_u_zero]

private theorem padq_proj1_mul_proj0 (dim q : Nat) :
    pad_u dim q proj1 * pad_u dim q proj0 = 0 := by
  rw [pad_u_mul_pad_u dim q proj0 proj1, proj1_mul_proj0, pad_u_zero]

/-- **GENERAL CONTROLLED-CIRCUIT SEMANTIC THEOREM**.

For any well-typed `BaseUCom dim` `c` and any fresh control qubit `q`,
the matrix semantics of the controlled circuit `control q c` is the
standard projector decomposition

    uc_eval (control q c) = P0_q + P1_q · uc_eval c.

Proof by induction on `c`:
- **`seq c₁ c₂`**: by IH on both halves, then projector algebra. After
  `Matrix.add_mul` / `Matrix.mul_add`, the four cross-terms simplify
  via `P0·P0 = P0`, `P0·P1 = P1·P0 = 0`, `P1·P1 = P1`, plus
  `pad_u_comm_uc_eval_of_fresh` to commute `U₂` past `P0` / `P1`.
- **`app1 (R θ φ λ) n`**: directly `uc_eval_control_app1_R_eq_pad_ctrl`
  + unfolding `pad_ctrl`.
- **`app2 CNOT m n`**: directly `uc_eval_control_app2_CNOT_eq_proj_decomp`.
- **`app3`**: vacuous since `BaseUnitary 3` is empty.

This is the user-facing surface of the `control`-stub fix: any place
that uses `control q U` for an arbitrary well-typed circuit `U`
(modular-multiplier oracle, QFT, etc.) now has clean controlled-U
matrix semantics. Downstream, this directly enables phase-kickback
chaining for `controlled_powers` and the `QPE_var_on_eigenstate` step
of `QPE_MMI_correct`. -/
theorem uc_eval_control_eq_proj_decomp {dim : Nat} (q : Nat) (c : BaseUCom dim)
    (hq : q < dim) (h_fresh : is_fresh q c) (h_wt : UCom.WellTyped dim c) :
    uc_eval (control q c)
      = pad_u dim q proj0 + pad_u dim q proj1 * uc_eval c := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
      obtain ⟨h_f1, h_f2⟩ := h_fresh
      cases h_wt with
      | seq h_wt1 h_wt2 =>
        show uc_eval (control q c₂) * uc_eval (control q c₁) = _
        rw [ih₁ h_f1 h_wt1, ih₂ h_f2 h_wt2]
        -- Goal:
        -- (P0 + P1 * U₂) * (P0 + P1 * U₁) = P0 + P1 * uc_eval (seq c₁ c₂)
        -- = P0 + P1 * (U₂ * U₁)
        show (pad_u dim q proj0 + pad_u dim q proj1 * uc_eval c₂) *
             (pad_u dim q proj0 + pad_u dim q proj1 * uc_eval c₁)
             = pad_u dim q proj0 + pad_u dim q proj1 * (uc_eval c₂ * uc_eval c₁)
        rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
        rw [padq_proj0_mul_proj0]
        rw [show pad_u dim q proj0 * (pad_u dim q proj1 * uc_eval c₁) = 0 from by
              rw [← Matrix.mul_assoc, padq_proj0_mul_proj1, Matrix.zero_mul]]
        rw [show pad_u dim q proj1 * uc_eval c₂ * pad_u dim q proj0 = 0 from by
              rw [Matrix.mul_assoc, ← pad_u_comm_uc_eval_of_fresh q c₂ h_f2 proj0,
                  ← Matrix.mul_assoc, padq_proj1_mul_proj0, Matrix.zero_mul]]
        rw [show pad_u dim q proj1 * uc_eval c₂ * (pad_u dim q proj1 * uc_eval c₁)
                = pad_u dim q proj1 * (uc_eval c₂ * uc_eval c₁) from by
              rw [Matrix.mul_assoc (pad_u dim q proj1) (uc_eval c₂)
                    (pad_u dim q proj1 * uc_eval c₁),
                  ← Matrix.mul_assoc (uc_eval c₂) (pad_u dim q proj1) (uc_eval c₁),
                  ← pad_u_comm_uc_eval_of_fresh q c₂ h_f2 proj1,
                  Matrix.mul_assoc (pad_u dim q proj1) (uc_eval c₂) (uc_eval c₁),
                  ← Matrix.mul_assoc (pad_u dim q proj1) (pad_u dim q proj1)
                    (uc_eval c₂ * uc_eval c₁),
                  padq_proj1_mul_proj1]]
        abel
  | app1 u n =>
      cases h_wt with
      | app1 hn =>
        cases u with
        | R θ φ lam =>
          have h12 : q ≠ n := h_fresh
          show uc_eval (control q (UCom.app1 (BaseUnitary.R θ φ lam) n)) = _
          rw [uc_eval_control_app1_R_eq_pad_ctrl q n hq hn h12 θ φ lam]
          show pad_ctrl dim q n (rotation θ φ lam) = _
          unfold pad_ctrl
          rfl
  | app2 u m n =>
      cases h_wt with
      | app2 hm hn hmn =>
        cases u
        have hqm : q ≠ m := h_fresh.1
        have hqn : q ≠ n := h_fresh.2
        show uc_eval (control q (UCom.app2 BaseUnitary.CNOT m n)) = _
        exact uc_eval_control_app2_CNOT_eq_proj_decomp q m n hq hm hn hqm hqn hmn
  | app3 u _ _ _ => cases u

/-! ## Step 16: phase kickback — controlled-circuit semantics on eigenstates

The first real QPE-semantic bridge: when the controlled body `c` has `ψ`
as an eigenstate with eigenvalue `ζ`, the controlled circuit acts as
the projector form `P0_q · ψ + ζ · (P1_q · ψ)`. This is the
**phase-kickback identity**: the eigenvalue `ζ` migrates to the
control-1 branch of the control qubit. -/

/-- **Single-control phase kickback (projector form).**

Given a well-typed circuit `c` with control qubit `q` fresh in `c`, and
a state `ψ` that is an eigenstate of `c` with eigenvalue `ζ`, the
matrix action of `control q c` on `ψ` is the projector decomposition

    `uc_eval (control q c) * ψ = (P0_q · ψ) + ζ · (P1_q · ψ)`

where `Pi_q = pad_u dim q proj_i` (i = 0, 1).

Proof: rewrite `uc_eval (control q c)` via `uc_eval_control_eq_proj_decomp`,
distribute via `Matrix.add_mul`, then substitute `h_eig` and pull the
scalar out via `Matrix.mul_smul`. ~3 lines. -/
theorem uc_eval_control_on_projector_decomp {dim : Nat}
    (q : Nat) (c : BaseUCom dim) (hq : q < dim)
    (h_fresh : is_fresh q c) (h_wt : UCom.WellTyped dim c)
    (ψ : Matrix (Fin (2^dim)) (Fin 1) ℂ)
    (ζ : ℂ) (h_eig : uc_eval c * ψ = ζ • ψ) :
    uc_eval (control q c) * ψ
      = pad_u dim q proj0 * ψ + ζ • (pad_u dim q proj1 * ψ) := by
  rw [uc_eval_control_eq_proj_decomp q c hq h_fresh h_wt]
  rw [Matrix.add_mul, Matrix.mul_assoc, h_eig, Matrix.mul_smul]

/-! ## Step 17: controlled-powers cascade (single-step) -/

/-- **Single-step cascade for `controlled_powers`.**

If after applying `controlled_powers f n` to `ψ` we obtain a state `φ`
that is an eigenstate of `f n` with eigenvalue `ζ`, then the next
iteration `controlled_powers f (n+1)` gives the projector-decomposition
form of phase-kickback on `φ`. This abstracts the cascade step so
callers can supply the intermediate `φ` and its eigen-relation directly
(useful when `φ ≠ ψ` because earlier controls have already updated the
control register, yet `φ` happens to still be an eigenstate of `f n`).

Proof: unfold `controlled_powers (n+1) = seq (controlled_powers n) (control n (f n))`,
substitute `h_prior` for the intermediate state, then apply
`uc_eval_control_on_projector_decomp`. ~5 lines. -/
theorem uc_eval_controlled_powers_succ_step {dim n : Nat}
    (f : Nat → BaseUCom dim) (hn : n < dim)
    (h_fresh : is_fresh n (f n))
    (h_wt : UCom.WellTyped dim (f n))
    (ψ φ : Matrix (Fin (2^dim)) (Fin 1) ℂ)
    (h_prior : uc_eval (controlled_powers f n) * ψ = φ)
    (ζ : ℂ) (h_eig : uc_eval (f n) * φ = ζ • φ) :
    uc_eval (controlled_powers f (n + 1)) * ψ
      = pad_u dim n proj0 * φ + ζ • (pad_u dim n proj1 * φ) := by
  rw [show uc_eval (controlled_powers f (n + 1)) * ψ
        = uc_eval (control n (f n)) * (uc_eval (controlled_powers f n) * ψ) from by
        rw [uc_eval_controlled_powers_succ, Matrix.mul_assoc]]
  rw [h_prior]
  exact uc_eval_control_on_projector_decomp n (f n) hn h_fresh h_wt φ ζ h_eig

/-! ## Step 18: full controlled-powers cascade theorem (common eigenstate)

Iterating the single-step cascade `uc_eval_controlled_powers_succ_step` over
all `m` qubits gives the full QPE phase-kickback identity:

    uc_eval (controlled_powers f m) * ψ = phase_projector_product ζ m * ψ

where `phase_projector_product ζ m` is the product (in the same order as
`uc_eval (controlled_powers f m)`) of the per-qubit phase projectors
`pad_u dim i proj0 + ζ i • pad_u dim i proj1`. -/

/-- **Per-qubit phase projector.** The matrix
`P0_i + ζ_i · P1_i` that the i-th controlled `f i` produces on an
eigenstate: identity on the control-0 branch, scaled by `ζ_i` on the
control-1 branch. -/
noncomputable def phase_projector {dim : Nat}
    (i : Nat) (ζ : ℂ) : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ :=
  pad_u dim i proj0 + ζ • pad_u dim i proj1

/-- Action of `phase_projector` on a state vector. -/
theorem phase_projector_apply {dim : Nat} (i : Nat) (ζ : ℂ)
    (ψ : Matrix (Fin (2^dim)) (Fin 1) ℂ) :
    @phase_projector dim i ζ * ψ
      = pad_u dim i proj0 * ψ + ζ • (pad_u dim i proj1 * ψ) := by
  unfold phase_projector
  rw [Matrix.add_mul, Matrix.smul_mul ζ (pad_u dim i proj1) ψ]

/-- **Recursive phase-projector product**, ordered to match
`uc_eval (controlled_powers f m)`: the latest projector is on the
LEFT (because `uc_eval (UCom.seq c₁ c₂) = uc_eval c₂ * uc_eval c₁`
and `controlled_powers f (n+1) = seq (controlled_powers f n) (control n (f n))`). -/
noncomputable def phase_projector_product {dim : Nat}
    (ζ : Nat → ℂ) : Nat → Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ
  | 0 => 1
  | n + 1 => phase_projector n (ζ n) * phase_projector_product ζ n

/-- A single `phase_projector` commutes with any matrix `M` that commutes
separately with both projectors `pad_u dim i proj0` and `pad_u dim i proj1`. -/
theorem phase_projector_commutes_uc_eval {dim : Nat}
    (i : Nat) (ζ : ℂ) (M : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ)
    (h_comm0 : pad_u dim i proj0 * M = M * pad_u dim i proj0)
    (h_comm1 : pad_u dim i proj1 * M = M * pad_u dim i proj1) :
    @phase_projector dim i ζ * M = M * @phase_projector dim i ζ := by
  unfold phase_projector
  rw [Matrix.add_mul, Matrix.mul_add, h_comm0]
  rw [show ζ • pad_u dim i proj1 * M = ζ • (pad_u dim i proj1 * M) from
      smul_mul_assoc ζ _ _]
  rw [h_comm1]
  rw [show ζ • (M * pad_u dim i proj1) = M * (ζ • pad_u dim i proj1) from by
      rw [Matrix.mul_smul]]

/-- `phase_projector_product ζ n` commutes with `M` whenever each of the
underlying single-qubit projector lifts `pad_u dim i b` (for `i < n`,
`b` either `proj0` or `proj1`, or any 2x2) commutes with `M`. -/
theorem phase_projector_product_commutes {dim : Nat}
    (ζ : Nat → ℂ) (M : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) :
    ∀ n,
      (∀ i, i < n → ∀ b : Matrix (Fin 2) (Fin 2) ℂ,
            pad_u dim i b * M = M * pad_u dim i b) →
      @phase_projector_product dim ζ n * M = M * @phase_projector_product dim ζ n := by
  intro n
  induction n with
  | zero =>
      intro _
      show (1 : Matrix _ _ _) * M = M * 1
      rw [Matrix.one_mul, Matrix.mul_one]
  | succ k ih =>
      intro h_comm
      show phase_projector k (ζ k) * @phase_projector_product dim ζ k * M
            = M * (phase_projector k (ζ k) * @phase_projector_product dim ζ k)
      rw [Matrix.mul_assoc]
      rw [ih (fun i hi b => h_comm i (Nat.lt_succ_of_lt hi) b)]
      rw [← Matrix.mul_assoc]
      rw [phase_projector_commutes_uc_eval k (ζ k) M
            (h_comm k (Nat.lt_succ_self k) proj0)
            (h_comm k (Nat.lt_succ_self k) proj1)]
      rw [Matrix.mul_assoc]

/-- **Full controlled-powers cascade on a common eigenstate.**

Given a state `ψ` that is a common eigenstate of each `f i` (for `i < m`)
with eigenvalue `ζ i`, and given the data-only commutation hypothesis
(each `pad_u dim i U` commutes with `uc_eval (f j)` for `i, j < m` — in
QPE this is automatic because the controls live on positions `< m` and
the `f j`s are shift-lifted to positions `≥ m`), the controlled-powers
cascade applied to `ψ` produces the phase-kickback state

    uc_eval (controlled_powers f m) * ψ = phase_projector_product ζ m * ψ.

Proof: induction on `m`. Base case `m = 0` uses
`uc_eval_controlled_powers_zero_eq_one`. The successor step uses
`uc_eval_controlled_powers_succ_step` with the intermediate state
`φ := phase_projector_product ζ k * ψ`; the eigen-relation on `φ`
follows from `phase_projector_product_commutes` plus the data-only
commutation hypothesis. -/
theorem uc_eval_controlled_powers_on_common_eigenstate_recursive
    {dim : Nat} (hd : 0 < dim) (f : Nat → BaseUCom dim)
    (ψ : Matrix (Fin (2^dim)) (Fin 1) ℂ) (ζ : Nat → ℂ) :
    ∀ m, (∀ i, i < m → i < dim) →
      (∀ i, i < m → is_fresh i (f i)) →
      (∀ i, i < m → UCom.WellTyped dim (f i)) →
      (∀ i j, i < m → j < m →
        ∀ U : Matrix (Fin 2) (Fin 2) ℂ,
          pad_u dim i U * uc_eval (f j) = uc_eval (f j) * pad_u dim i U) →
      (∀ i, i < m → uc_eval (f i) * ψ = ζ i • ψ) →
      uc_eval (controlled_powers f m) * ψ
        = @phase_projector_product dim ζ m * ψ := by
  intro m
  induction m with
  | zero =>
      intro _ _ _ _ _
      show uc_eval (controlled_powers f 0) * ψ = (1 : Matrix _ _ _) * ψ
      rw [uc_eval_controlled_powers_zero_eq_one f hd]
  | succ k ih =>
      intro h_lt h_fr h_wt h_comm h_eig
      have ih_app := ih
          (fun i hi => h_lt i (Nat.lt_succ_of_lt hi))
          (fun i hi => h_fr i (Nat.lt_succ_of_lt hi))
          (fun i hi => h_wt i (Nat.lt_succ_of_lt hi))
          (fun i j hi hj U => h_comm i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) U)
          (fun i hi => h_eig i (Nat.lt_succ_of_lt hi))
      set φ := @phase_projector_product dim ζ k * ψ
      have h_eig_φ : uc_eval (f k) * φ = ζ k • φ := by
        show uc_eval (f k) * (@phase_projector_product dim ζ k * ψ) = ζ k • (_ * ψ)
        rw [← Matrix.mul_assoc]
        rw [← phase_projector_product_commutes ζ (uc_eval (f k)) k
              (fun i hi b => h_comm i k (Nat.lt_succ_of_lt hi) (Nat.lt_succ_self k) b)]
        rw [Matrix.mul_assoc, h_eig k (Nat.lt_succ_self k), Matrix.mul_smul]
      have h_step := uc_eval_controlled_powers_succ_step f
        (h_lt k (Nat.lt_succ_self k))
        (h_fr k (Nat.lt_succ_self k))
        (h_wt k (Nat.lt_succ_self k))
        ψ φ ih_app (ζ k) h_eig_φ
      rw [h_step]
      -- Goal: pad_u k proj0 * φ + ζ k • (pad_u k proj1 * φ)
      --     = phase_projector_product ζ (k+1) * ψ
      -- RHS = phase_projector k (ζ k) * phase_projector_product ζ k * ψ
      --     = phase_projector k (ζ k) * φ            (folding φ definition)
      --     = pad_u k proj0 * φ + ζ k • (pad_u k proj1 * φ)  (phase_projector_apply)
      show pad_u dim k proj0 * φ + ζ k • (pad_u dim k proj1 * φ) =
            phase_projector k (ζ k) * @phase_projector_product dim ζ k * ψ
      rw [Matrix.mul_assoc]
      show pad_u dim k proj0 * φ + ζ k • (pad_u dim k proj1 * φ) =
            phase_projector k (ζ k) * φ
      rw [phase_projector_apply]

/-! ## Step 13: documentation — full control-stub-fix roadmap

The following declarations are intentionally NOT proved here; they
sketch the next pieces needed for the eventual `control`-stub fix.

(a) **`controlled_H q t`** — controlled-Hadamard, expressed as the
    standard Ry-cnot-Ry decomposition:

        controlled_H q t
          := UCom.seq (Ry (π/4) t)
               (UCom.seq (CNOT q t)
                 (Ry (-π/4) t))

    correctness target: matrix equality
    `uc_eval (controlled_H q t) = pad_ctrl dim q t hMatrix`.

(b) **`controlled_Rz q t λ`** — controlled-Rz(λ), expressed via:

        controlled_Rz q t λ
          := UCom.seq (Rz (λ/2) t)
               (UCom.seq (CNOT q t)
                 (UCom.seq (Rz (-λ/2) t) (CNOT q t)))

    correctness target: matrix equality
    `uc_eval (controlled_Rz q t λ) = pad_ctrl dim q t (rzMatrix λ)`.

(c) **`controlled_R q t θ φ λ`** — full general 1-qubit rotation
    controlled. The standard Nielsen-Chuang decomposition is:

        controlled_R q t θ φ λ
          := UCom.seq (UCom.app1 (R 0 0 ((λ - φ)/2)) t)
               (UCom.seq (CNOT q t)
                 (UCom.seq (UCom.app1 (R (-θ/2) 0 (-(φ+λ)/2)) t)
                   (UCom.seq (CNOT q t)
                     (UCom.app1 (R (θ/2) φ 0) t))))

    correctness target: matrix equality
    `uc_eval (controlled_R q t θ φ λ) = pad_ctrl dim q t (rotation θ φ λ)`.

    NOTE: this is the largest piece and the one that would unblock
    `QPE_MMI_correct`. It is the standard 4-gate-plus-1-phase
    decomposition; the correctness proof reduces to a 4×4 block
    matrix identity that takes ~200–500 lines.

Once all three above are proved, replacing the `control` stub at
`Framework/UnitaryOps.lean:972` with

  `control q (UCom.app1 (BaseUnitary.R θ φ λ) t) := controlled_R q t θ φ λ`

becomes the global rewrite, with the correctness of `controlled_R`
guaranteeing the soundness of `controlled_powers` and hence of QPE
phase kickback. -/

end FormalRV.SQIRPort
