/-
  FormalRV.Framework.GateDecompositions — gate identity theorems.

  Lean translation skeleton of `SQIR/SQIR/GateDecompositions.v` (1649 LOC
  of Coq). The headline target is `CCX_correct`: the 7-T Toffoli decomposition
  in `BaseUCom.CCX` has the same matrix semantics as the abstract Toffoli.

  ## Status (2026-05-05)
  - PROVEN in Lean: `toffoliMatrix_mul_toffoliMatrix` (Toffoli is involution).
  - DEFERRED to SQIR (G-T axioms): `f_to_vec_CCX`, `CCX_eq_toffoliMatrix`.
  See per-axiom docstrings for the closure plan and SQIR proof refs.
-/
import FormalRV.Core.UnitarySem
import FormalRV.Core.UnitaryOps
import FormalRV.Core.QuantumLib
import FormalRV.Core.PadAction

namespace FormalRV.Framework

/-! ## Toffoli matrix

    The CCX (Toffoli) gate as an 8×8 matrix in the computational basis.
    Acts as identity except: |110⟩ ↔ |111⟩.

    Standard form: rows/cols index `|abc⟩` for a, b, c ∈ {0, 1} as
    `4a + 2b + c`. -/

/-- The 8×8 Toffoli (CCX) matrix. -/
def toffoliMatrix : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 0]

/-- Toffoli is its own inverse. -/
theorem toffoliMatrix_mul_toffoliMatrix :
    toffoliMatrix * toffoliMatrix = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  unfold toffoliMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight]

/-! ## CCX correctness — the headline theorem of GateDecompositions.v

    The 7-T `CCX` decomposition (defined in `Framework/QuantumGate.lean`
    via `H ; CNOT ; T† ; CNOT ; T ; CNOT ; T† ; CNOT ; CNOT ; T† ; CNOT ;
    T ; T ; T ; H`) has the same matrix semantics as the abstract Toffoli.

    SQIR proves this in `GateDecompositions.v` via heavy `gridify` +
    matrix algebra (~200 LOC). Sorried here. -/

/-! ### `f_to_vec_CCX` — FAITHFUL translation of SQIR's CCX correctness theorem.
    SQIR/SQIR/UnitaryOps.v:
    ```coq
    Lemma f_to_vec_CCX : forall (dim a b c : nat) (f : nat -> bool),
       (a < dim)%nat -> (b < dim)%nat -> (c < dim)%nat -> a <> b -> a <> c -> b <> c ->
      (uc_eval (CCX a b c)) × (f_to_vec dim f)
          = f_to_vec dim (update f c (f c ⊕ (f a && f b))).
    ```
    Applied to a basis state |f⟩, `CCX a b c` flips bit `c` iff bits `a`
    and `b` are both 1. Proof in SQIR uses `gridify` — sorried here. -/

/-! ### G-T axioms: deferred to SQIR Coq proofs.
    Per CLAUDE.md: "intermediate Coq proofs are fine and will be cited from
    Lean as `axiom ... -- ref: SQIR/.../File.v#lemma_name`". These are the
    G-T axiom catalogue entries from this file. Each closes ZERO sorries and
    introduces ONE axiom whose statement is the byte-for-byte translation
    of the cited SQIR lemma. -/

/-- `f_to_vec_CCX` from SQIR. Action of the 7-T Toffoli decomposition on a
    basis state.

    PROVEN as `Framework.PadAction.f_to_vec_CCX_proved` modulo the named
    `CCX_PHASE_CANCEL` sorry (8-case Complex.exp algebra inside the
    underlying `f_to_vec_CCX_left_proved`). Re-exported here as a theorem
    matching SQIR's UnitaryOps.v signature. -/
theorem f_to_vec_CCX (dim a b c : Nat) (f : Nat → Bool)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim) * f_to_vec dim f
      = f_to_vec dim (update f c (xor (f c) (f a && f b))) :=
  f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc f

/-- Matrix-equality form of CCX correctness. Not a SQIR theorem (SQIR uses
    `f_to_vec_CCX`); kept for the review work.

    Proof: matrix_eq_of_basis_action reduces to 8 column-equality cases.
    Case k=0 discharged below; cases k ∈ {1..7} are named-sorried as
    `CCX_TOFFOLI_BASIS_k`. -/
theorem CCX_eq_toffoliMatrix :
    uc_eval (BaseUCom.CCX 0 1 2 : BaseUCom 3) = toffoliMatrix := by
  apply matrix_eq_of_basis_action
  intro k
  fin_cases k
  · -- k.val = 0
    show uc_eval (BaseUCom.CCX 0 1 2 : BaseUCom 3) * basis_vector (2^3) 0
       = toffoliMatrix * basis_vector (2^3) 0
    rw [basis_vector_eq_f_to_vec_nat 3 0 (by decide)]
    rw [f_to_vec_CCX_proved 3 0 1 2 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    have h_update : update (nat_to_funbool 3 0) 2
                      (xor (nat_to_funbool 3 0 2)
                           (nat_to_funbool 3 0 0 && nat_to_funbool 3 0 1))
                  = nat_to_funbool 3 0 := by
      rw [nat_to_funbool_3_0_eq_false 0,
          nat_to_funbool_3_0_eq_false 1,
          nat_to_funbool_3_0_eq_false 2]
      simp
      exact update_self _ _
    rw [h_update]
    rw [← basis_vector_eq_f_to_vec_nat 3 0 (by decide)]
    -- Goal: basis_vector (2^3) 0 = toffoliMatrix * basis_vector (2^3) 0
    symm
    ext i jj
    have hjj : jj = 0 := Subsingleton.elim _ _; subst hjj
    show (toffoliMatrix * basis_vector 8 0) i 0 = basis_vector 8 0 i 0
    rw [mul_basis_vector_apply toffoliMatrix 0 (by decide)]
    fin_cases i <;> simp [toffoliMatrix, basis_vector]
  · -- k.val = 1: f = (false, false, true). Toffoli is identity (f 0 && f 1 = false).
    show uc_eval (BaseUCom.CCX 0 1 2 : BaseUCom 3) * basis_vector (2^3) 1
       = toffoliMatrix * basis_vector (2^3) 1
    rw [basis_vector_eq_f_to_vec_nat 3 1 (by decide)]
    rw [f_to_vec_CCX_proved 3 0 1 2 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    have h_update : update (nat_to_funbool 3 1) 2
                      (xor (nat_to_funbool 3 1 2)
                           (nat_to_funbool 3 1 0 && nat_to_funbool 3 1 1))
                  = nat_to_funbool 3 1 := by
      rw [nat_to_funbool_3_1_zero, nat_to_funbool_3_1_one, nat_to_funbool_3_1_two]
      simp
      exact update_self _ _
    rw [h_update]
    rw [← basis_vector_eq_f_to_vec_nat 3 1 (by decide)]
    symm
    ext i jj
    have hjj : jj = 0 := Subsingleton.elim _ _; subst hjj
    show (toffoliMatrix * basis_vector 8 1) i 0 = basis_vector 8 1 i 0
    rw [mul_basis_vector_apply toffoliMatrix 1 (by decide)]
    fin_cases i <;> simp [toffoliMatrix, basis_vector]
  · -- k.val = 2: f = (false, true, false). Toffoli is identity (f 0 = false).
    show uc_eval (BaseUCom.CCX 0 1 2 : BaseUCom 3) * basis_vector (2^3) 2
       = toffoliMatrix * basis_vector (2^3) 2
    rw [basis_vector_eq_f_to_vec_nat 3 2 (by decide)]
    rw [f_to_vec_CCX_proved 3 0 1 2 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    have h_update : update (nat_to_funbool 3 2) 2
                      (xor (nat_to_funbool 3 2 2)
                           (nat_to_funbool 3 2 0 && nat_to_funbool 3 2 1))
                  = nat_to_funbool 3 2 := by
      rw [nat_to_funbool_3_2_zero, nat_to_funbool_3_2_one, nat_to_funbool_3_2_two]
      simp
      exact update_self _ _
    rw [h_update]
    rw [← basis_vector_eq_f_to_vec_nat 3 2 (by decide)]
    symm
    ext i jj
    have hjj : jj = 0 := Subsingleton.elim _ _; subst hjj
    show (toffoliMatrix * basis_vector 8 2) i 0 = basis_vector 8 2 i 0
    rw [mul_basis_vector_apply toffoliMatrix 2 (by decide)]
    fin_cases i <;> simp [toffoliMatrix, basis_vector]
  · -- k.val = 3: f = (false, true, true). Toffoli is identity (f 0 = false).
    show uc_eval (BaseUCom.CCX 0 1 2 : BaseUCom 3) * basis_vector (2^3) 3
       = toffoliMatrix * basis_vector (2^3) 3
    rw [basis_vector_eq_f_to_vec_nat 3 3 (by decide)]
    rw [f_to_vec_CCX_proved 3 0 1 2 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    have h_update : update (nat_to_funbool 3 3) 2
                      (xor (nat_to_funbool 3 3 2)
                           (nat_to_funbool 3 3 0 && nat_to_funbool 3 3 1))
                  = nat_to_funbool 3 3 := by
      rw [nat_to_funbool_3_3_zero, nat_to_funbool_3_3_one, nat_to_funbool_3_3_two]
      simp
      exact update_self _ _
    rw [h_update]
    rw [← basis_vector_eq_f_to_vec_nat 3 3 (by decide)]
    symm
    ext i jj
    have hjj : jj = 0 := Subsingleton.elim _ _; subst hjj
    show (toffoliMatrix * basis_vector 8 3) i 0 = basis_vector 8 3 i 0
    rw [mul_basis_vector_apply toffoliMatrix 3 (by decide)]
    fin_cases i <;> simp [toffoliMatrix, basis_vector]
  · -- k.val = 4: f = (true, false, false). Toffoli is identity (f 1 = false).
    show uc_eval (BaseUCom.CCX 0 1 2 : BaseUCom 3) * basis_vector (2^3) 4
       = toffoliMatrix * basis_vector (2^3) 4
    rw [basis_vector_eq_f_to_vec_nat 3 4 (by decide)]
    rw [f_to_vec_CCX_proved 3 0 1 2 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    have h_update : update (nat_to_funbool 3 4) 2
                      (xor (nat_to_funbool 3 4 2)
                           (nat_to_funbool 3 4 0 && nat_to_funbool 3 4 1))
                  = nat_to_funbool 3 4 := by
      rw [nat_to_funbool_3_4_zero, nat_to_funbool_3_4_one, nat_to_funbool_3_4_two]
      simp
      exact update_self _ _
    rw [h_update]
    rw [← basis_vector_eq_f_to_vec_nat 3 4 (by decide)]
    symm
    ext i jj
    have hjj : jj = 0 := Subsingleton.elim _ _; subst hjj
    show (toffoliMatrix * basis_vector 8 4) i 0 = basis_vector 8 4 i 0
    rw [mul_basis_vector_apply toffoliMatrix 4 (by decide)]
    fin_cases i <;> simp [toffoliMatrix, basis_vector]
  · -- k.val = 5: f = (true, false, true). Toffoli is identity (f 1 = false).
    show uc_eval (BaseUCom.CCX 0 1 2 : BaseUCom 3) * basis_vector (2^3) 5
       = toffoliMatrix * basis_vector (2^3) 5
    rw [basis_vector_eq_f_to_vec_nat 3 5 (by decide)]
    rw [f_to_vec_CCX_proved 3 0 1 2 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    have h_update : update (nat_to_funbool 3 5) 2
                      (xor (nat_to_funbool 3 5 2)
                           (nat_to_funbool 3 5 0 && nat_to_funbool 3 5 1))
                  = nat_to_funbool 3 5 := by
      rw [nat_to_funbool_3_5_zero, nat_to_funbool_3_5_one, nat_to_funbool_3_5_two]
      simp
      exact update_self _ _
    rw [h_update]
    rw [← basis_vector_eq_f_to_vec_nat 3 5 (by decide)]
    symm
    ext i jj
    have hjj : jj = 0 := Subsingleton.elim _ _; subst hjj
    show (toffoliMatrix * basis_vector 8 5) i 0 = basis_vector 8 5 i 0
    rw [mul_basis_vector_apply toffoliMatrix 5 (by decide)]
    fin_cases i <;> simp [toffoliMatrix, basis_vector]
  · -- k.val = 6: pattern (true, true, false). Toffoli FLIPS f 2: output index 7.
    show uc_eval (BaseUCom.CCX 0 1 2 : BaseUCom 3) * basis_vector (2^3) 6
       = toffoliMatrix * basis_vector (2^3) 6
    rw [basis_vector_eq_f_to_vec_nat 3 6 (by decide)]
    rw [f_to_vec_CCX_proved 3 0 1 2 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    rw [nat_to_funbool_3_6_zero, nat_to_funbool_3_6_one, nat_to_funbool_3_6_two]
    simp  -- xor false (true && true) = true
    -- LHS: f_to_vec 3 (update (nat_to_funbool 3 6) 2 true)
    -- Compute funbool_to_nat = 7 then convert to basis_vector 8 7
    have h_funbool : funbool_to_nat 3 (update (nat_to_funbool 3 6) 2 true) = 7 := by decide
    unfold f_to_vec
    rw [h_funbool]
    -- LHS: basis_vector (2^3) 7
    symm
    ext i jj
    have hjj : jj = 0 := Subsingleton.elim _ _; subst hjj
    show (toffoliMatrix * basis_vector 8 6) i 0 = basis_vector 8 7 i 0
    rw [mul_basis_vector_apply toffoliMatrix 6 (by decide)]
    fin_cases i <;> simp [toffoliMatrix, basis_vector]
  · -- k.val = 7: pattern (true, true, true). Toffoli FLIPS f 2: output index 6.
    show uc_eval (BaseUCom.CCX 0 1 2 : BaseUCom 3) * basis_vector (2^3) 7
       = toffoliMatrix * basis_vector (2^3) 7
    rw [basis_vector_eq_f_to_vec_nat 3 7 (by decide)]
    rw [f_to_vec_CCX_proved 3 0 1 2 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    rw [nat_to_funbool_3_7_zero, nat_to_funbool_3_7_one, nat_to_funbool_3_7_two]
    simp  -- xor true (true && true) = false
    -- LHS: f_to_vec 3 (update (nat_to_funbool 3 7) 2 false)
    have h_funbool : funbool_to_nat 3 (update (nat_to_funbool 3 7) 2 false) = 6 := by decide
    unfold f_to_vec
    rw [h_funbool]
    -- LHS: basis_vector (2^3) 6
    symm
    ext i jj
    have hjj : jj = 0 := Subsingleton.elim _ _; subst hjj
    show (toffoliMatrix * basis_vector 8 7) i 0 = basis_vector 8 6 i 0
    rw [mul_basis_vector_apply toffoliMatrix 7 (by decide)]
    fin_cases i <;> simp [toffoliMatrix, basis_vector]

open BaseUCom in
/-- `niter 4 (T q) ≡ Z q` — applying T four times via iteration equals Z.
    Combines `uc_eval_niter` with the matrix-level `tMatrix_pow_four`.
    Lives here because it needs both `niter` (UnitaryOps) and
    `tMatrix_pow_four` (PadAction). -/
theorem niter_four_T_eq_Z {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 4 (T q : BaseUCom dim)) (Z q) := by
  show uc_eval (niter 4 (T q)) = uc_eval (Z q : BaseUCom dim)
  rw [uc_eval_niter hd 4]
  show (pad_u dim q (rotation 0 0 (Real.pi/4)))^4 = pad_u dim q (rotation 0 0 Real.pi)
  rw [show ((pad_u dim q (rotation 0 0 (Real.pi/4))) : Square dim)^4
        = pad_u dim q (rotation 0 0 (Real.pi/4))
          * pad_u dim q (rotation 0 0 (Real.pi/4))
          * pad_u dim q (rotation 0 0 (Real.pi/4))
          * pad_u dim q (rotation 0 0 (Real.pi/4))
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u,
      rotation_T, rotation_Z, tMatrix_pow_four]

open BaseUCom in
/-- `niter 4 (TDAG q) ≡ Z q` — T†⁴ = Z (dagger version of `niter_four_T_eq_Z`). -/
theorem niter_four_TDAG_eq_Z {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 4 (TDAG q : BaseUCom dim)) (Z q) := by
  show uc_eval (niter 4 (TDAG q)) = uc_eval (Z q : BaseUCom dim)
  rw [uc_eval_niter hd 4]
  show (pad_u dim q (rotation 0 0 (-(Real.pi/4))))^4
       = pad_u dim q (rotation 0 0 Real.pi)
  rw [show ((pad_u dim q (rotation 0 0 (-(Real.pi/4)))) : Square dim)^4
        = pad_u dim q (rotation 0 0 (-(Real.pi/4)))
          * pad_u dim q (rotation 0 0 (-(Real.pi/4)))
          * pad_u dim q (rotation 0 0 (-(Real.pi/4)))
          * pad_u dim q (rotation 0 0 (-(Real.pi/4)))
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u,
      rotation_TDAG, rotation_Z, tdagMatrix_pow_four]

open BaseUCom in
/-- `niter 4 (S q) ≡ SKIP` — S has order 4 (S⁴ = I). -/
theorem niter_four_S_eq_SKIP {dim : Nat} (q : Nat) (hq : q < dim) (hd : 0 < dim) :
    UCom.equiv (niter 4 (S q : BaseUCom dim)) SKIP := by
  show uc_eval (niter 4 (S q)) = uc_eval (SKIP : BaseUCom dim)
  rw [uc_eval_niter hd 4]
  show (pad_u dim q (rotation 0 0 (Real.pi/2)))^4 = pad_u dim 0 (rotation 0 0 0)
  rw [show ((pad_u dim q (rotation 0 0 (Real.pi/2))) : Square dim)^4
        = pad_u dim q (rotation 0 0 (Real.pi/2))
          * pad_u dim q (rotation 0 0 (Real.pi/2))
          * pad_u dim q (rotation 0 0 (Real.pi/2))
          * pad_u dim q (rotation 0 0 (Real.pi/2))
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u,
      rotation_S, rotation_I, sMatrix_pow_four, pad_u_id hq, pad_u_id hd]

open BaseUCom in
/-- `niter 4 (SDAG q) ≡ SKIP` — S† has order 4 (S†⁴ = I). -/
theorem niter_four_SDAG_eq_SKIP {dim : Nat} (q : Nat) (hq : q < dim) (hd : 0 < dim) :
    UCom.equiv (niter 4 (SDAG q : BaseUCom dim)) SKIP := by
  show uc_eval (niter 4 (SDAG q)) = uc_eval (SKIP : BaseUCom dim)
  rw [uc_eval_niter hd 4]
  show (pad_u dim q (rotation 0 0 (-(Real.pi/2))))^4 = pad_u dim 0 (rotation 0 0 0)
  rw [show ((pad_u dim q (rotation 0 0 (-(Real.pi/2)))) : Square dim)^4
        = pad_u dim q (rotation 0 0 (-(Real.pi/2)))
          * pad_u dim q (rotation 0 0 (-(Real.pi/2)))
          * pad_u dim q (rotation 0 0 (-(Real.pi/2)))
          * pad_u dim q (rotation 0 0 (-(Real.pi/2)))
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u,
      rotation_SDAG, rotation_I, sdagMatrix_pow_four, pad_u_id hq, pad_u_id hd]

open BaseUCom in
/-- `niter 2 (T q) ≡ S q` — T² = S. -/
theorem niter_two_T_eq_S {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 2 (T q : BaseUCom dim)) (S q) := by
  show uc_eval (niter 2 (T q)) = uc_eval (S q : BaseUCom dim)
  rw [uc_eval_niter hd 2]
  show (pad_u dim q (rotation 0 0 (Real.pi/4)))^2
       = pad_u dim q (rotation 0 0 (Real.pi/2))
  rw [sq, pad_u_mul_pad_u, rotation_T, rotation_S, tMatrix_mul_tMatrix]

open BaseUCom in
/-- `niter 2 (TDAG q) ≡ SDAG q` — T†² = S†. -/
theorem niter_two_TDAG_eq_SDAG {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 2 (TDAG q : BaseUCom dim)) (SDAG q) := by
  show uc_eval (niter 2 (TDAG q)) = uc_eval (SDAG q : BaseUCom dim)
  rw [uc_eval_niter hd 2]
  show (pad_u dim q (rotation 0 0 (-(Real.pi/4))))^2
       = pad_u dim q (rotation 0 0 (-(Real.pi/2)))
  rw [sq, pad_u_mul_pad_u, rotation_TDAG, rotation_SDAG, tdagMatrix_mul_tdagMatrix]

open BaseUCom in
/-- `niter 2 (S q) ≡ Z q` — S² = Z. -/
theorem niter_two_S_eq_Z {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 2 (S q : BaseUCom dim)) (Z q) := by
  show uc_eval (niter 2 (S q)) = uc_eval (Z q : BaseUCom dim)
  rw [uc_eval_niter hd 2]
  show (pad_u dim q (rotation 0 0 (Real.pi/2)))^2
       = pad_u dim q (rotation 0 0 Real.pi)
  rw [sq, pad_u_mul_pad_u, rotation_S, rotation_Z, sMatrix_mul_sMatrix]

open BaseUCom in
/-- `niter 2 (SDAG q) ≡ Z q` — S†² = Z. -/
theorem niter_two_SDAG_eq_Z {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 2 (SDAG q : BaseUCom dim)) (Z q) := by
  show uc_eval (niter 2 (SDAG q)) = uc_eval (Z q : BaseUCom dim)
  rw [uc_eval_niter hd 2]
  show (pad_u dim q (rotation 0 0 (-(Real.pi/2))))^2
       = pad_u dim q (rotation 0 0 Real.pi)
  rw [sq, pad_u_mul_pad_u, rotation_SDAG, rotation_Z, sdagMatrix_mul_sdagMatrix]

open BaseUCom in
/-- `niter 3 (T q) ≡ T q ; S q` — T³ = T·S, since T² = S so T³ = (T²)·T = S·T,
    which at uc_eval level is `pad_u sMatrix * pad_u tMatrix = uc_eval (T q ; S q)`. -/
theorem niter_three_T_eq_TS {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 3 (T q : BaseUCom dim)) (UCom.seq (T q) (S q)) := by
  show uc_eval (niter 3 (T q)) = uc_eval (UCom.seq (T q) (S q))
  rw [uc_eval_niter hd 3]
  show (pad_u dim q (rotation 0 0 (Real.pi/4)))^3
        = pad_u dim q (rotation 0 0 (Real.pi/2)) * pad_u dim q (rotation 0 0 (Real.pi/4))
  rw [rotation_T, rotation_S]
  rw [show ((pad_u dim q tMatrix) : Square dim)^3
        = pad_u dim q tMatrix * pad_u dim q tMatrix * pad_u dim q tMatrix
        from by rw [pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, tMatrix_mul_tMatrix]

open BaseUCom in
/-- `niter 3 (TDAG q) ≡ TDAG q ; SDAG q` — T†³ = T†·S†, since T†² = S†. -/
theorem niter_three_TDAG_eq_TDAG_SDAG {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 3 (TDAG q : BaseUCom dim)) (UCom.seq (TDAG q) (SDAG q)) := by
  show uc_eval (niter 3 (TDAG q)) = uc_eval (UCom.seq (TDAG q) (SDAG q))
  rw [uc_eval_niter hd 3]
  show (pad_u dim q (rotation 0 0 (-(Real.pi/4))))^3
        = pad_u dim q (rotation 0 0 (-(Real.pi/2)))
          * pad_u dim q (rotation 0 0 (-(Real.pi/4)))
  rw [rotation_TDAG, rotation_SDAG]
  rw [show ((pad_u dim q tdagMatrix) : Square dim)^3
        = pad_u dim q tdagMatrix * pad_u dim q tdagMatrix * pad_u dim q tdagMatrix
        from by rw [pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, tdagMatrix_mul_tdagMatrix]

open BaseUCom in
/-- `niter 3 (S q) ≡ S† q` — S³ = S† (S has order 4). -/
theorem niter_three_S_eq_SDAG {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 3 (S q : BaseUCom dim)) (SDAG q) := by
  show uc_eval (niter 3 (S q)) = uc_eval (SDAG q : BaseUCom dim)
  rw [uc_eval_niter hd 3]
  show (pad_u dim q (rotation 0 0 (Real.pi/2)))^3
        = pad_u dim q (rotation 0 0 (-(Real.pi/2)))
  rw [show ((pad_u dim q (rotation 0 0 (Real.pi/2))) : Square dim)^3
        = pad_u dim q (rotation 0 0 (Real.pi/2))
          * pad_u dim q (rotation 0 0 (Real.pi/2))
          * pad_u dim q (rotation 0 0 (Real.pi/2))
        from by rw [pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u,
      rotation_S, rotation_SDAG, sMatrix_pow_three]

open BaseUCom in
/-- `niter 3 (SDAG q) ≡ S q` — S†³ = S. -/
theorem niter_three_SDAG_eq_S {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 3 (SDAG q : BaseUCom dim)) (S q) := by
  show uc_eval (niter 3 (SDAG q)) = uc_eval (S q : BaseUCom dim)
  rw [uc_eval_niter hd 3]
  show (pad_u dim q (rotation 0 0 (-(Real.pi/2))))^3
        = pad_u dim q (rotation 0 0 (Real.pi/2))
  rw [show ((pad_u dim q (rotation 0 0 (-(Real.pi/2)))) : Square dim)^3
        = pad_u dim q (rotation 0 0 (-(Real.pi/2)))
          * pad_u dim q (rotation 0 0 (-(Real.pi/2)))
          * pad_u dim q (rotation 0 0 (-(Real.pi/2)))
        from by rw [pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u,
      rotation_SDAG, rotation_S, sdagMatrix_pow_three]

open BaseUCom in
/-- `niter 4 (H q) ≡ SKIP` — H is involutive so H⁴ = I. -/
theorem niter_four_H_eq_SKIP {dim : Nat} (q : Nat) (hq : q < dim) (hd : 0 < dim) :
    UCom.equiv (niter 4 (H q : BaseUCom dim)) SKIP := by
  show uc_eval (niter 4 (H q)) = uc_eval (SKIP : BaseUCom dim)
  rw [uc_eval_niter hd 4]
  show (pad_u dim q (rotation (Real.pi/2) 0 Real.pi))^4 = pad_u dim 0 (rotation 0 0 0)
  rw [show ((pad_u dim q (rotation (Real.pi/2) 0 Real.pi)) : Square dim)^4
        = pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
          * pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
          * pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
          * pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u,
      rotation_H, rotation_I, hMatrix_pow_four, pad_u_id hq, pad_u_id hd]

open BaseUCom in
/-- `niter 4 (X q) ≡ SKIP` — X⁴ = (X²)² = I. -/
theorem niter_four_X_eq_SKIP {dim : Nat} (q : Nat) (hq : q < dim) (hd : 0 < dim) :
    UCom.equiv (niter 4 (X q : BaseUCom dim)) SKIP := by
  show uc_eval (niter 4 (X q)) = uc_eval (SKIP : BaseUCom dim)
  rw [uc_eval_niter hd 4]
  show (pad_u dim q (rotation Real.pi 0 Real.pi))^4 = pad_u dim 0 (rotation 0 0 0)
  rw [show ((pad_u dim q (rotation Real.pi 0 Real.pi)) : Square dim)^4
        = pad_u dim q (rotation Real.pi 0 Real.pi)
          * pad_u dim q (rotation Real.pi 0 Real.pi)
          * pad_u dim q (rotation Real.pi 0 Real.pi)
          * pad_u dim q (rotation Real.pi 0 Real.pi)
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u,
      rotation_X, rotation_I, σx_pow_four, pad_u_id hq, pad_u_id hd]

open BaseUCom in
/-- `niter 4 (Y q) ≡ SKIP` — Y⁴ = I. -/
theorem niter_four_Y_eq_SKIP {dim : Nat} (q : Nat) (hq : q < dim) (hd : 0 < dim) :
    UCom.equiv (niter 4 (Y q : BaseUCom dim)) SKIP := by
  show uc_eval (niter 4 (Y q)) = uc_eval (SKIP : BaseUCom dim)
  rw [uc_eval_niter hd 4]
  show (pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2)))^4
        = pad_u dim 0 (rotation 0 0 0)
  rw [show ((pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))) : Square dim)^4
        = pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))
          * pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))
          * pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))
          * pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u,
      rotation_Y, rotation_I, σy_pow_four, pad_u_id hq, pad_u_id hd]

open BaseUCom in
/-- `proj q dim false` annihilates `f_to_vec dim f` when `f q = true`,
    otherwise leaves it unchanged. Lift of `pad_u_proj0_on_f_to_vec`. -/
theorem proj_false_on_f_to_vec (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    proj n dim false * f_to_vec dim f = if f n then 0 else f_to_vec dim f := by
  show pad_u dim n proj0 * f_to_vec dim f = _
  exact pad_u_proj0_on_f_to_vec dim n h f

open BaseUCom in
/-- `proj q dim true` annihilates `f_to_vec dim f` when `f q = false`,
    otherwise leaves it unchanged. -/
theorem proj_true_on_f_to_vec (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    proj n dim true * f_to_vec dim f = if f n then f_to_vec dim f else 0 := by
  show pad_u dim n proj1 * f_to_vec dim f = _
  by_cases hfn : f n
  · rw [if_pos hfn]
    exact pad_u_proj1_on_f_to_vec dim n h f |>.trans (by rw [if_pos hfn])
  · rw [if_neg hfn]
    exact pad_u_proj1_on_f_to_vec dim n h f |>.trans (by rw [if_neg hfn])

open BaseUCom in
/-- `proj q dim b * f_to_vec dim f = f_to_vec dim f` when `f q = b`.
    Projection onto matching basis state acts as identity.
    -- SQIR/SQIR/UnitaryOps.v line 272: f_to_vec_proj_eq. -/
theorem f_to_vec_proj_eq (dim n : Nat) (h : n < dim) (b : Bool) (f : Nat → Bool)
    (hfn : f n = b) :
    proj n dim b * f_to_vec dim f = f_to_vec dim f := by
  cases b
  · rw [proj_false_on_f_to_vec dim n h f]
    simp [hfn]
  · rw [proj_true_on_f_to_vec dim n h f]
    simp [hfn]

open BaseUCom in
/-- `proj q dim b * f_to_vec dim f = 0` when `f q ≠ b`. Projection onto
    non-matching basis state annihilates.
    -- SQIR/SQIR/UnitaryOps.v line 288: f_to_vec_proj_neq. -/
theorem f_to_vec_proj_neq (dim n : Nat) (h : n < dim) (b : Bool) (f : Nat → Bool)
    (hfn : f n ≠ b) :
    proj n dim b * f_to_vec dim f = 0 := by
  cases b
  · rw [proj_false_on_f_to_vec dim n h f]
    have : f n = true := by cases h : f n <;> simp [h] at hfn ⊢
    simp [this]
  · rw [proj_true_on_f_to_vec dim n h f]
    have : f n = false := by cases h : f n <;> simp [h] at hfn ⊢
    simp [this]

open BaseUCom in
/-- `f_to_vec dim f` is the (f n)-eigenstate of `proj n dim`. Direct
    corollary of `f_to_vec_proj_eq` with `b = f n`.
    -- SQIR/SQIR/UnitaryOps.v line 306: f_to_vec_classical. -/
theorem f_to_vec_classical (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    proj n dim (f n) * f_to_vec dim f = f_to_vec dim f :=
  f_to_vec_proj_eq dim n h (f n) f rfl

open BaseUCom in
/-- Unified projector-on-f_to_vec lemma: scales by 1 or 0 depending on
    whether `f n` matches `b`.
    -- SQIR/SQIR/UnitaryOps.v line 363: f_to_vec_proj. -/
theorem f_to_vec_proj (dim n : Nat) (h : n < dim) (b : Bool) (f : Nat → Bool) :
    proj n dim b * f_to_vec dim f
      = (if f n = b then (1 : ℂ) else 0) • f_to_vec dim f := by
  by_cases hfn : f n = b
  · rw [if_pos hfn, one_smul]
    exact f_to_vec_proj_eq dim n h b f hfn
  · rw [if_neg hfn, zero_smul]
    exact f_to_vec_proj_neq dim n h b f hfn

open BaseUCom in
/-- `niter 4 (Z q) ≡ SKIP` — Z⁴ = I. -/
theorem niter_four_Z_eq_SKIP {dim : Nat} (q : Nat) (hq : q < dim) (hd : 0 < dim) :
    UCom.equiv (niter 4 (Z q : BaseUCom dim)) SKIP := by
  show uc_eval (niter 4 (Z q)) = uc_eval (SKIP : BaseUCom dim)
  rw [uc_eval_niter hd 4]
  show (pad_u dim q (rotation 0 0 Real.pi))^4 = pad_u dim 0 (rotation 0 0 0)
  rw [show ((pad_u dim q (rotation 0 0 Real.pi)) : Square dim)^4
        = pad_u dim q (rotation 0 0 Real.pi)
          * pad_u dim q (rotation 0 0 Real.pi)
          * pad_u dim q (rotation 0 0 Real.pi)
          * pad_u dim q (rotation 0 0 Real.pi)
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u,
      rotation_Z, rotation_I, σz_pow_four, pad_u_id hq, pad_u_id hd]

open BaseUCom in
/-- `niter 5 (T q) ≡ T q ; Z q` — T⁵ = Z·T, since T⁴ = Z. -/
theorem niter_five_T_eq_TZ {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 5 (T q : BaseUCom dim)) (UCom.seq (T q) (Z q)) := by
  show uc_eval (niter 5 (T q)) = uc_eval (UCom.seq (T q) (Z q))
  rw [uc_eval_niter hd 5]
  show (pad_u dim q (rotation 0 0 (Real.pi/4)))^5
        = pad_u dim q (rotation 0 0 Real.pi)
          * pad_u dim q (rotation 0 0 (Real.pi/4))
  rw [rotation_T, rotation_Z]
  rw [show ((pad_u dim q tMatrix) : Square dim)^5
        = pad_u dim q tMatrix * pad_u dim q tMatrix * pad_u dim q tMatrix
          * pad_u dim q tMatrix * pad_u dim q tMatrix
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u,
      tMatrix_pow_five, ← pad_u_mul_pad_u]

open BaseUCom in
/-- `niter 5 (TDAG q) ≡ TDAG q ; Z q` — T†⁵ = Z·T†, since T†⁴ = Z. -/
theorem niter_five_TDAG_eq_TDAG_Z {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 5 (TDAG q : BaseUCom dim)) (UCom.seq (TDAG q) (Z q)) := by
  show uc_eval (niter 5 (TDAG q)) = uc_eval (UCom.seq (TDAG q) (Z q))
  rw [uc_eval_niter hd 5]
  show (pad_u dim q (rotation 0 0 (-(Real.pi/4))))^5
        = pad_u dim q (rotation 0 0 Real.pi)
          * pad_u dim q (rotation 0 0 (-(Real.pi/4)))
  rw [rotation_TDAG, rotation_Z]
  rw [show ((pad_u dim q tdagMatrix) : Square dim)^5
        = pad_u dim q tdagMatrix * pad_u dim q tdagMatrix * pad_u dim q tdagMatrix
          * pad_u dim q tdagMatrix * pad_u dim q tdagMatrix
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u,
      tdagMatrix_pow_five, ← pad_u_mul_pad_u]

open BaseUCom in
/-- `niter 5 (S q) ≡ S q` — S⁵ = S, since S⁴ = I. -/
theorem niter_five_S_eq_S {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 5 (S q : BaseUCom dim)) (S q) := by
  show uc_eval (niter 5 (S q)) = uc_eval (S q : BaseUCom dim)
  rw [uc_eval_niter hd 5]
  show (pad_u dim q (rotation 0 0 (Real.pi/2)))^5
        = pad_u dim q (rotation 0 0 (Real.pi/2))
  rw [rotation_S]
  rw [show ((pad_u dim q sMatrix) : Square dim)^5
        = pad_u dim q sMatrix * pad_u dim q sMatrix * pad_u dim q sMatrix
          * pad_u dim q sMatrix * pad_u dim q sMatrix
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u,
      sMatrix_pow_five]

open BaseUCom in
/-- `niter 5 (SDAG q) ≡ SDAG q` — S†⁵ = S†, since S†⁴ = I. -/
theorem niter_five_SDAG_eq_SDAG {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 5 (SDAG q : BaseUCom dim)) (SDAG q) := by
  show uc_eval (niter 5 (SDAG q)) = uc_eval (SDAG q : BaseUCom dim)
  rw [uc_eval_niter hd 5]
  show (pad_u dim q (rotation 0 0 (-(Real.pi/2))))^5
        = pad_u dim q (rotation 0 0 (-(Real.pi/2)))
  rw [rotation_SDAG]
  rw [show ((pad_u dim q sdagMatrix) : Square dim)^5
        = pad_u dim q sdagMatrix * pad_u dim q sdagMatrix * pad_u dim q sdagMatrix
          * pad_u dim q sdagMatrix * pad_u dim q sdagMatrix
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u,
      sdagMatrix_pow_five]

open BaseUCom in
/-- `niter 5 (X q) ≡ X q` — X⁵ = X, since X² = I. -/
theorem niter_five_X_eq_X {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 5 (X q : BaseUCom dim)) (X q) := by
  show uc_eval (niter 5 (X q)) = uc_eval (X q : BaseUCom dim)
  rw [uc_eval_niter hd 5]
  show (pad_u dim q (rotation Real.pi 0 Real.pi))^5
        = pad_u dim q (rotation Real.pi 0 Real.pi)
  rw [rotation_X]
  rw [show ((pad_u dim q σx) : Square dim)^5
        = pad_u dim q σx * pad_u dim q σx * pad_u dim q σx
          * pad_u dim q σx * pad_u dim q σx
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, σx_pow_five]

open BaseUCom in
/-- `niter 5 (Y q) ≡ Y q` — Y⁵ = Y, since Y² = I. -/
theorem niter_five_Y_eq_Y {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 5 (Y q : BaseUCom dim)) (Y q) := by
  show uc_eval (niter 5 (Y q)) = uc_eval (Y q : BaseUCom dim)
  rw [uc_eval_niter hd 5]
  show (pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2)))^5
        = pad_u dim q (rotation Real.pi (Real.pi/2) (Real.pi/2))
  rw [rotation_Y]
  rw [show ((pad_u dim q σy) : Square dim)^5
        = pad_u dim q σy * pad_u dim q σy * pad_u dim q σy
          * pad_u dim q σy * pad_u dim q σy
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, σy_pow_five]

open BaseUCom in
/-- `niter 5 (Z q) ≡ Z q` — Z⁵ = Z, since Z² = I. -/
theorem niter_five_Z_eq_Z {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 5 (Z q : BaseUCom dim)) (Z q) := by
  show uc_eval (niter 5 (Z q)) = uc_eval (Z q : BaseUCom dim)
  rw [uc_eval_niter hd 5]
  show (pad_u dim q (rotation 0 0 Real.pi))^5
        = pad_u dim q (rotation 0 0 Real.pi)
  rw [rotation_Z]
  rw [show ((pad_u dim q σz) : Square dim)^5
        = pad_u dim q σz * pad_u dim q σz * pad_u dim q σz
          * pad_u dim q σz * pad_u dim q σz
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, σz_pow_five]

open BaseUCom in
/-- `niter 5 (H q) ≡ H q` — H⁵ = H, since H² = I. -/
theorem niter_five_H_eq_H {dim : Nat} (q : Nat) (hd : 0 < dim) :
    UCom.equiv (niter 5 (H q : BaseUCom dim)) (H q) := by
  show uc_eval (niter 5 (H q)) = uc_eval (H q : BaseUCom dim)
  rw [uc_eval_niter hd 5]
  show (pad_u dim q (rotation (Real.pi/2) 0 Real.pi))^5
        = pad_u dim q (rotation (Real.pi/2) 0 Real.pi)
  rw [rotation_H]
  rw [show ((pad_u dim q hMatrix) : Square dim)^5
        = pad_u dim q hMatrix * pad_u dim q hMatrix * pad_u dim q hMatrix
          * pad_u dim q hMatrix * pad_u dim q hMatrix
        from by rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul]]
  rw [pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, pad_u_mul_pad_u, hMatrix_pow_five]

open BaseUCom in
/-- `niter 4 (X q) ≡ ID q`. -/
theorem niter_four_X_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 4 (X q : BaseUCom dim)) (ID q) := by
  have hd : 0 < dim := q.zero_le.trans_lt hq
  exact (niter_four_X_eq_SKIP q hq hd).trans (ID_equiv_SKIP hq hd).symm

open BaseUCom in
/-- `niter 4 (Y q) ≡ ID q`. -/
theorem niter_four_Y_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 4 (Y q : BaseUCom dim)) (ID q) := by
  have hd : 0 < dim := q.zero_le.trans_lt hq
  exact (niter_four_Y_eq_SKIP q hq hd).trans (ID_equiv_SKIP hq hd).symm

open BaseUCom in
/-- `niter 4 (Z q) ≡ ID q`. -/
theorem niter_four_Z_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 4 (Z q : BaseUCom dim)) (ID q) := by
  have hd : 0 < dim := q.zero_le.trans_lt hq
  exact (niter_four_Z_eq_SKIP q hq hd).trans (ID_equiv_SKIP hq hd).symm

open BaseUCom in
/-- `niter 4 (H q) ≡ ID q`. -/
theorem niter_four_H_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 4 (H q : BaseUCom dim)) (ID q) := by
  have hd : 0 < dim := q.zero_le.trans_lt hq
  exact (niter_four_H_eq_SKIP q hq hd).trans (ID_equiv_SKIP hq hd).symm

open BaseUCom in
/-- `niter 8 (X q) ≡ ID q` — direct 1-line application of the
    `niter_two_mul_self_inv_eq_ID` template with k=4. -/
theorem niter_eight_X_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 8 (X q : BaseUCom dim)) (ID q) :=
  niter_two_mul_self_inv_eq_ID q hq (X q) (niter_two_X_eq_ID q hq) 4

open BaseUCom in
/-- `niter 8 (Y q) ≡ ID q`. -/
theorem niter_eight_Y_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 8 (Y q : BaseUCom dim)) (ID q) :=
  niter_two_mul_self_inv_eq_ID q hq (Y q) (niter_two_Y_eq_ID q hq) 4

open BaseUCom in
/-- `niter 8 (Z q) ≡ ID q`. -/
theorem niter_eight_Z_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 8 (Z q : BaseUCom dim)) (ID q) :=
  niter_two_mul_self_inv_eq_ID q hq (Z q) (niter_two_Z_eq_ID q hq) 4

open BaseUCom in
/-- `niter 8 (H q) ≡ ID q`. -/
theorem niter_eight_H_eq_ID {dim : Nat} (q : Nat) (hq : q < dim) :
    UCom.equiv (niter 8 (H q : BaseUCom dim)) (ID q) :=
  niter_two_mul_self_inv_eq_ID q hq (H q) (niter_two_H_eq_ID q hq) 4

end FormalRV.Framework
