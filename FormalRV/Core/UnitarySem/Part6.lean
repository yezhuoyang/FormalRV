/- UnitarySem — Part6 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Core.UnitarySem.Part5

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker  -- enables `A ⊗ₖ B` notation for Matrix.kronecker

/-! ## Pad_ctrl basic identities -/

/-- A controlled-identity gate is the global identity (both qubits valid).
    Whether the control fires or not, applying I has no effect, so the
    sum (proj0 + proj1·I) collapses to (proj0 + proj1) = σi → identity. -/
theorem pad_ctrl_id {dim m n : Nat} (hm : m < dim) (hn : n < dim) :
    pad_ctrl dim m n σi = (1 : Square dim) := by
  unfold pad_ctrl
  rw [pad_u_id hn, Matrix.mul_one, ← pad_u_add,
      proj0_add_proj1_eq_id, pad_u_id hm]

/-- A controlled-zero "gate" is just the projection on the control qubit at
    state |0⟩: when the control fires there's nothing to apply (target term
    vanishes). Mathematically `pad_ctrl _ _ _ 0 = pad_u _ _ proj0`. Useful
    as infrastructure for splitting pad_ctrl proofs additively. -/
theorem pad_ctrl_zero (dim m n : Nat) :
    pad_ctrl dim m n (0 : Matrix (Fin 2) (Fin 2) ℂ) = pad_u dim m proj0 := by
  unfold pad_ctrl
  rw [pad_u_zero, Matrix.mul_zero, add_zero]

/-- Scalar multiplication in the target argument: only the |1⟩ branch
    sees the scaling, since the |0⟩ branch (proj0) doesn't depend on the
    target operator. -/
theorem pad_ctrl_smul (dim m n : Nat) (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_ctrl dim m n (c • A)
      = pad_u dim m proj0 + c • (pad_u dim m proj1 * pad_u dim n A) := by
  unfold pad_ctrl
  rw [pad_u_smul, Matrix.mul_smul]

/-- Negation in the target argument: only the |1⟩ branch flips sign. -/
theorem pad_ctrl_neg (dim m n : Nat) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_ctrl dim m n (-A)
      = pad_u dim m proj0 - pad_u dim m proj1 * pad_u dim n A := by
  unfold pad_ctrl
  rw [pad_u_neg, Matrix.mul_neg, ← sub_eq_add_neg]

/-- Asymmetric additivity in the target: adding a second operator to the
    target produces the original pad_ctrl plus an extra |1⟩-branch term —
    the proj0 contribution doesn't double, since proj0 is target-independent. -/
theorem pad_ctrl_add (dim m n : Nat) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_ctrl dim m n (A + B)
      = pad_ctrl dim m n A + pad_u dim m proj1 * pad_u dim n B := by
  unfold pad_ctrl
  rw [pad_u_add, Matrix.mul_add, ← add_assoc]

/-- Asymmetric subtractivity in the target: subtracting a second operator
    from the target subtracts only an extra |1⟩-branch term. Corollary
    of `pad_ctrl_add` + `pad_u_neg` via `sub_eq_add_neg`. -/
theorem pad_ctrl_sub (dim m n : Nat) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_ctrl dim m n (A - B)
      = pad_ctrl dim m n A - pad_u dim m proj1 * pad_u dim n B := by
  simp only [sub_eq_add_neg]
  rw [pad_ctrl_add, pad_u_neg, Matrix.mul_neg]

/-- Boundary case: when the target qubit is out of dim range, the |1⟩-branch
    term vanishes and pad_ctrl reduces to just the proj0 padding. -/
theorem pad_ctrl_target_oob (dim m n : Nat) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hn : ¬n < dim) :
    pad_ctrl dim m n A = pad_u dim m proj0 := by
  unfold pad_ctrl
  have h : pad_u dim n A = 0 := by unfold pad_u; rw [dif_neg hn]
  rw [h, Matrix.mul_zero, add_zero]

/-- Boundary case: when the control qubit is out of dim range, both
    projector paddings vanish and pad_ctrl is just zero. -/
theorem pad_ctrl_control_oob (dim m n : Nat) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hm : ¬m < dim) :
    pad_ctrl dim m n A = 0 := by
  unfold pad_ctrl
  have h0 : pad_u dim m proj0 = 0 := by unfold pad_u; rw [dif_neg hm]
  have h1 : pad_u dim m proj1 = 0 := by unfold pad_u; rw [dif_neg hm]
  rw [h0, h1, Matrix.zero_mul, add_zero]

/-- Edge case: when control and target are the same qubit, pad_ctrl
    collapses to a single pad_u of the kernel `proj0 + proj1·A`. -/
theorem pad_ctrl_same_qubit (dim n : Nat) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_ctrl dim n n A = pad_u dim n (proj0 + proj1 * A) := by
  unfold pad_ctrl
  rw [pad_u_mul_pad_u, ← pad_u_add]

/-- σx's 3-chain at the padded level equals pad_u σx (cubes back to self). -/
theorem pad_u_σx_pow_three (dim n : Nat) :
    pad_u dim n σx * pad_u dim n σx * pad_u dim n σx = pad_u dim n σx :=
  pad_u_pow_three_eq dim n σx σx σx_pow_three

/-- σy's 3-chain at the padded level equals pad_u σy. -/
theorem pad_u_σy_pow_three (dim n : Nat) :
    pad_u dim n σy * pad_u dim n σy * pad_u dim n σy = pad_u dim n σy :=
  pad_u_pow_three_eq dim n σy σy σy_pow_three

/-- σz's 3-chain at the padded level equals pad_u σz. -/
theorem pad_u_σz_pow_three (dim n : Nat) :
    pad_u dim n σz * pad_u dim n σz * pad_u dim n σz = pad_u dim n σz :=
  pad_u_pow_three_eq dim n σz σz σz_pow_three

/-- Hadamard's 3-chain at the padded level equals pad_u hMatrix. -/
theorem pad_u_hMatrix_pow_three (dim n : Nat) :
    pad_u dim n hMatrix * pad_u dim n hMatrix * pad_u dim n hMatrix = pad_u dim n hMatrix :=
  pad_u_pow_three_eq dim n hMatrix hMatrix hMatrix_pow_three

open BaseUCom in
/-- `ID n ≡ SKIP` for any well-typed `n < dim`.
    SQIR/Equivalences.v line 11. -/
theorem ID_equiv_SKIP {dim : Nat} {n : Nat} (h : n < dim) (h0 : 0 < dim) :
    UCom.equiv (ID n : BaseUCom dim) (SKIP) := by
  show pad_u dim n (rotation 0 0 0) = pad_u dim 0 (rotation 0 0 0)
  rw [rotation_I, pad_u_id h, pad_u_id h0]

open BaseUCom in
/-- `SKIP ; c ≡ c` — left identity. Follows from `pad_u_id` and `Matrix.one_mul`. -/
theorem SKIP_id_l {dim : Nat} (c : BaseUCom dim) (h : 0 < dim) :
    UCom.equiv (UCom.seq (SKIP : BaseUCom dim) c) c := by
  show uc_eval c * uc_eval (SKIP : BaseUCom dim) = uc_eval c
  show uc_eval c * pad_u dim 0 (rotation 0 0 0) = uc_eval c
  rw [rotation_I, pad_u_id h, Matrix.mul_one]

open BaseUCom in
/-- `c ; SKIP ≡ c` — right identity. -/
theorem SKIP_id_r {dim : Nat} (c : BaseUCom dim) (h : 0 < dim) :
    UCom.equiv (UCom.seq c (SKIP : BaseUCom dim)) c := by
  show pad_u dim 0 (rotation 0 0 0) * uc_eval c = uc_eval c
  rw [rotation_I, pad_u_id h, Matrix.one_mul]

/-! ## Sequential composition is congruent w.r.t. equivalence -/

/-- `useq_congruence`: if `c₁ ≡ c₁'` and `c₂ ≡ c₂'`, then `c₁;c₂ ≡ c₁';c₂'`.
    SQIR/UnitarySem.v line 78. -/
theorem useq_congruence {dim : Nat} {c₁ c₁' c₂ c₂' : BaseUCom dim}
    (h₁ : UCom.equiv c₁ c₁') (h₂ : UCom.equiv c₂ c₂') :
    UCom.equiv (UCom.seq c₁ c₂) (UCom.seq c₁' c₂') := by
  show uc_eval c₂ * uc_eval c₁ = uc_eval c₂' * uc_eval c₁'
  rw [show uc_eval c₁ = uc_eval c₁' from h₁,
      show uc_eval c₂ = uc_eval c₂' from h₂]

/-- Left congruence: if `c₂ ≡ c₂'`, then `c₁;c₂ ≡ c₁;c₂'`. -/
theorem useq_congruence_l {dim : Nat} {c₂ c₂' : BaseUCom dim} (c₁ : BaseUCom dim)
    (h₂ : UCom.equiv c₂ c₂') :
    UCom.equiv (UCom.seq c₁ c₂) (UCom.seq c₁ c₂') :=
  useq_congruence (UCom.equiv_refl c₁) h₂

/-- Right congruence: if `c₁ ≡ c₁'`, then `c₁;c₂ ≡ c₁';c₂`. -/
theorem useq_congruence_r {dim : Nat} {c₁ c₁' : BaseUCom dim} (c₂ : BaseUCom dim)
    (h₁ : UCom.equiv c₁ c₁') :
    UCom.equiv (UCom.seq c₁ c₂) (UCom.seq c₁' c₂) :=
  useq_congruence h₁ (UCom.equiv_refl c₂)

/-! ## Roadmap (each is one or more autoresearch ticks)

  Filling in this file's sorries unlocks Shor-correctness work. Priority:

  1. **`pad_u`**: implement via Kronecker products
     `(I ^⊗ n) ⊗ M ⊗ (I ^⊗ (dim - n - 1))`. ~50 lines + `simp` lemmas.
     Reference: `SQIR/QuantumLib/Pad.v` lines ~50-150 in original Coq.

  2. **`pad_ctrl`**: implement via case-split on m < n vs m > n. The
     control on qubit m and target on qubit n is more delicate; SQIR
     uses helper `pad_ctrl1`/`pad_ctrl2` for the two orderings. ~80 lines.

  3. **Single-qubit gate matrix lemmas**: prove
     `rotation_H : rotation (π/2) 0 π = !![1/√2, 1/√2; 1/√2, -1/√2] / √2`
     and similarly for X, Y, Z, T, S. Each is `simp` + `Real.cos_pi_div_two`
     etc. ~5 lines each, ~10 lemmas total.

  4. **Self-inverse properties**: `X · X = I`, `H · H = I`, `T · T = S`,
     `CNOT · CNOT = I`. These are circuit-equivalence lemmas of the form
     `seq (X n) (X n) ≡ ID n`. They follow from (3) once `pad_u` is in place.

  5. **CCX correctness**: prove that the 7-T `CCX` decomposition (defined
     in `QuantumGate.lean`) has the same semantics as the abstract
     Toffoli matrix. This is the single biggest milestone in the early
     framework — it bridges RCIR-level (where CCX is primitive) to
     unitary-level (where it's a long sequence). SQIR proves this in
     `GateDecompositions.v`; ~200 lines.

  6. **QFT and QPE**: build on top of the above. See
     `Framework/QFT.lean` and `Framework/QPE.lean` (not yet created).

  7. **Shor-end-to-end**: the Mt. Everest. Combines (6) with
     `Framework.Gate` (RCIR adders/multipliers) via a "lift" relating the
     two semantic levels. ~years of research-level work in any proof
     assistant.

-/


end FormalRV.Framework
