import FormalRV.Core.UnitarySem
import FormalRV.Core.QuantumLib
import FormalRV.Core.PadAction.PadActionDefinitions
import FormalRV.Core.PadAction.PadActionComposite

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker

/-- `H q ; X q ; H q` acts as Z on `f_to_vec dim f` (Hadamard sandwich). -/
theorem f_to_vec_H_X_H (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.X n))
                       (BaseUCom.H n))
      * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  rw [H_X_H_eq_Z]
  exact f_to_vec_Z_uc_eval dim n h f

/-- `H q ; Z q ; H q` acts as X (bit flip) on `f_to_vec dim f`. -/
theorem f_to_vec_H_Z_H (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.Z n))
                       (BaseUCom.H n))
      * f_to_vec dim f
      = f_to_vec dim (update f n (!f n)) := by
  rw [H_Z_H_eq_X]
  exact f_to_vec_X_uc_eval dim n h f

/-- `H q ; Z q` and `X q ; H q` agree on `f_to_vec dim f`. Hadamard
    interchange at the f-coord level (lift of `H_comm_Z`). -/
theorem f_to_vec_H_comm_Z (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.Z n)) * f_to_vec dim f
      = uc_eval (UCom.seq (BaseUCom.X n) (BaseUCom.H n)) * f_to_vec dim f := by
  rw [H_comm_Z]

/-- `H q ; X q` and `Z q ; H q` agree on `f_to_vec dim f`. Dual interchange. -/
theorem f_to_vec_H_comm_X (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.X n)) * f_to_vec dim f
      = uc_eval (UCom.seq (BaseUCom.Z n) (BaseUCom.H n)) * f_to_vec dim f := by
  rw [H_comm_X]

/-! ## CCX final: gate 15 (H c) + phase cancellation

    Apply H c to the 14-gate prefix. Each branch bifurcates, giving 4
    sub-branches. The phase factors must arrange so that sub-branches
    cancel/combine to yield exactly `f_to_vec dim (update f c v)` where
    `v = xor (f c) (f a && f b)` — the Toffoli output.

    Structure of the proof:
    1. Apply prefix_14 to get the 2-branch state.
    2. Apply uc_eval_seq_mul + f_to_vec_H_uc_eval per branch.
    3. update_idem collapses (update (update f c v) c v') = update f c v'.
    4. The result is a 4-branch sum that the phase-cancellation step
       must collapse to the Toffoli output.

    The cancellation is intrinsically case-bound: 8 cases for
    (f a, f b, f c) ∈ {true, false}³. Each requires simplifying
    Complex.exp products to ±1 or ±exp(iπ/4) etc. This is the
    algebraic heart of the 7-T Toffoli identity.

    Below: the statement is the LEFT-ASSOCIATED 15-gate chain (matching
    our prefix_X chain). Bridging to SQIR's right-associated `CCX`
    follows from `useq_assoc` and is a separate theorem
    (`uc_eval_CCX_eq_left_assoc`, future tick). -/

theorem f_to_vec_CCX_left_proved (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
        (BaseUCom.CNOT a b))
        (BaseUCom.T a))
        (BaseUCom.T b))
        (BaseUCom.T c))
        (BaseUCom.H c))
      * f_to_vec dim f
      = f_to_vec dim (update f c (xor (f c) (f a && f b))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_14 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_H_uc_eval dim c hc (update f c false)]
  rw [f_to_vec_H_uc_eval dim c hc (update f c true)]
  rw [show (update f c false) c = false from update_eq f c false]
  rw [show (update f c true) c = true from update_eq f c true]
  -- update_idem to simplify nested updates at c
  rw [update_idem, update_idem]
  -- 8-case analysis on (f a, f b, f c) — each case has specific
  -- complex products that simplify to ±√2/2 etc.
  -- Split explicitly into named sub-cases so each can be closed
  -- independently in future ticks.
  cases hfa : f a
  · cases hfb : f b
    · cases hfc : f c
      · -- Case (F, F, F): α₀ = √2/2, α₁ = √2/2 (4-factor alternating)
        -- Expected: f_to_vec dim (update f c F)
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_alt_four]
        -- Collapse smul nesting via smul_smul + (√2/2)² = 1/2.
        simp only [one_mul, smul_smul, sqrt2_div2_sq]
        -- LHS has 4 terms with (1/2) coefficient; F1 terms cancel,
        -- F0 terms combine to 1•F0.
        module
      · -- Case (F, F, T): α₀ = √2/2, α₁ = -√2/2
        -- Expected: f_to_vec dim (update f c T)
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_alt_four]
        simp only [one_mul, smul_smul, sqrt2_div2_sq]
        module
    · cases hfc : f c
      · -- Case (F, T, F): α₀ uses alt-4, α₁ uses consec-4
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_alt_four]
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_consec_four]
        simp only [one_mul, smul_smul, sqrt2_div2_sq]
        module
      · -- Case (F, T, T): same as (F,T,F) but fc=T
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_alt_four]
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_consec_four]
        simp only [one_mul, smul_smul, sqrt2_div2_sq]
        module
  · cases hfb : f b
    · cases hfc : f c
      · -- Case (T, F, F): α₀ has e*e⁻¹*e⁻¹*e pattern (palindrome),
        -- α₁ has e*e*e⁻¹*e⁻¹ (consec-4)
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (Complex.I * (Real.pi / 4)) = (1 : ℂ)
            from exp_pi4_palindrome_four]
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_consec_four]
        simp only [one_mul, smul_smul, sqrt2_div2_sq]
        module
      · -- Case (T, F, T): same as (T,F,F) but fc=T
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (Complex.I * (Real.pi / 4)) = (1 : ℂ)
            from exp_pi4_palindrome_four]
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_consec_four]
        simp only [one_mul, smul_smul, sqrt2_div2_sq]
        module
    · cases hfc : f c
      · -- Case (T, T, F): α₀ uses consec-4, α₁ uses mul-4 (= -1)
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_consec_four]
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4)) = (-1 : ℂ)
            from exp_pi4_mul_four_eq_neg_one]
        simp only [one_mul, smul_smul, sqrt2_div2_sq, neg_one_mul, mul_neg_one,
                   mul_neg, neg_mul, neg_neg]
        module
      · -- Case (T, T, T): same as (T,T,F) but fc=T; α₁'s -1 from
        -- exp_pi4_pow_four cancels the -1 from (if fc then -1 else 1)
        simp_all
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * (Real.pi / 4)))
              * Complex.exp (-(Complex.I * (Real.pi / 4))) = (1 : ℂ)
            from exp_pi4_consec_four]
        rw [show Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (Complex.I * (Real.pi / 4)) = (-1 : ℂ)
            from exp_pi4_mul_four_eq_neg_one]
        simp only [one_mul, smul_smul, sqrt2_div2_sq, neg_one_mul, mul_neg_one,
                   mul_neg, neg_mul, neg_neg]
        module
  -- 8 named sub-cases, each requires explicit case analysis on r
  -- (r = false-update-index, true-update-index, or other) plus
  -- specific Complex.exp arithmetic. To discharge, would need
  -- ~50 LOC per case (8 × 50 = 400 LOC total).
  -- CCX_PHASE_CANCEL: 8 named sub-goals, each requiring complex
  -- arithmetic with exp(iπ/4) products. The exp_pi4_* helpers above
  -- give the canonical reductions but each case still needs:
  --   (1) explicit smul_add + smul_smul + add_smul to collect F0/F1 coeffs
  --   (2) ring_nf or linear_combination with exp_pi4_pow_four
  --   (3) potentially Matrix.ext to split into entry equations

/-! ## Bridge: SQIR's right-associated `BaseUCom.CCX` = left-associated chain

    `BaseUCom.CCX a b c` is built right-associated:
        seq s1 (seq s2 (seq s3 s4))
    where each sₖ is itself right-associated. Our `f_to_vec_CCX_left_proved`
    operates on the left-associated 15-gate chain. Since `useq_assoc` gives
    matrix-level equivalence, the two `uc_eval`s are equal — we just need
    to re-associate.

    Proof strategy: unfold both sides, `simp only [uc_eval_seq]` to expand
    `uc_eval (seq c1 c2) = uc_eval c2 * uc_eval c1`, then apply
    `Matrix.mul_assoc` enough times to canonicalize. -/

theorem uc_eval_CCX_eq_left_chain (dim a b c : Nat) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim)
      = uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
          (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
          (BaseUCom.CNOT a c))
          (BaseUCom.T c))
          (BaseUCom.CNOT b c))
          (BaseUCom.TDAG c))
          (BaseUCom.CNOT a c))
          (BaseUCom.CNOT a b))
          (BaseUCom.TDAG b))
          (BaseUCom.CNOT a b))
          (BaseUCom.T a))
          (BaseUCom.T b))
          (BaseUCom.T c))
          (BaseUCom.H c)) := by
  show uc_eval _ = uc_eval _
  unfold BaseUCom.CCX
  simp only [uc_eval_seq, Matrix.mul_assoc]

/-- SQIR-faithful form of `f_to_vec_CCX`, derived from the left-chain
    proof + right-association bridge. Matches the axiom statement in
    `Framework.GateDecompositions`. -/
theorem f_to_vec_CCX_proved (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim) * f_to_vec dim f
      = f_to_vec dim (update f c (xor (f c) (f a && f b))) := by
  rw [uc_eval_CCX_eq_left_chain]
  exact f_to_vec_CCX_left_proved dim a b c ha hb hc hab hac hbc f

/-- Corollary: when at least one control bit is 0, CCX leaves the state
    unchanged. -/
theorem f_to_vec_CCX_no_op (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool)
    (h : (f a && f b) = false) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim) * f_to_vec dim f
      = f_to_vec dim f := by
  rw [f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc f, h,
      Bool.xor_false, update_self]

/-- Corollary: when both control bits are 1, CCX flips the target bit. -/
theorem f_to_vec_CCX_flip (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool)
    (hfa : f a = true) (hfb : f b = true) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim) * f_to_vec dim f
      = f_to_vec dim (update f c (!f c)) := by
  rw [f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc f, hfa, hfb,
      Bool.and_self, Bool.xor_true]

/-- CCX is its own inverse on basis vectors: applying it twice returns the
    original state. Follows from `f_to_vec_CCX_proved` plus the fact that
    `update_neq` keeps the controls a, b unchanged across the inner update,
    so the second xor flips back what the first xor flipped.
    -- SQIR/SQIR/UnitaryOps.v analog: CCX is the Toffoli gate, an involution. -/
theorem f_to_vec_CCX_involutive (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim) *
      (uc_eval (BaseUCom.CCX a b c : BaseUCom dim) * f_to_vec dim f)
      = f_to_vec dim f := by
  rw [f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc f]
  rw [f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc _]
  -- Inner state: update f c (xor (f c) (f a && f b))
  -- Reading a, b through this update returns f a, f b since a ≠ c, b ≠ c.
  rw [update_neq f c a (xor (f c) (f a && f b)) hac,
      update_neq f c b (xor (f c) (f a && f b)) hbc,
      update_eq f c (xor (f c) (f a && f b))]
  -- Goal: f_to_vec dim (update (update f c (xor ...)) c
  --         (xor (xor (f c) (f a && f b)) (f a && f b))) = f_to_vec dim f
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false, update_idem, update_self]

/-- Two square matrices are equal iff their actions on all basis vectors agree. -/
theorem matrix_eq_of_basis_action {n : Nat} (M N : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ k : Fin n, M * basis_vector n k.val = N * basis_vector n k.val) :
    M = N := by
  ext i j
  have hj : M * basis_vector n j.val = N * basis_vector n j.val := h j
  have key : (M * basis_vector n j.val) i 0 = (N * basis_vector n j.val) i 0 := by rw [hj]
  rw [mul_basis_vector_apply M j.val j.isLt i] at key
  rw [mul_basis_vector_apply N j.val j.isLt i] at key
  exact key

/-- Inverse property: `funbool_to_nat n (nat_to_funbool n j) = j` for `j < 2^n`. -/
theorem funbool_to_nat_nat_to_funbool (n j : Nat) (h : j < 2^n) :
    funbool_to_nat n (nat_to_funbool n j) = j := by
  induction n generalizing j with
  | zero =>
      have : j = 0 := by simp at h; omega
      rw [this]; rfl
  | succ k ih =>
      rw [funbool_to_nat_succ]
      -- Top bit: nat_to_funbool (k+1) j k corresponds to bit position 0 of j.
      have h_top : nat_to_funbool (k+1) j k = decide (j % 2 = 1) := by
        unfold nat_to_funbool
        have h_zero : k + 1 - 1 - k = 0 := by omega
        simp [h_zero]
      rw [h_top]
      -- Lower bits: nat_to_funbool (k+1) j i = nat_to_funbool k (j/2) i for i < k.
      have h_lower : ∀ i, i < k →
          nat_to_funbool (k+1) j i = nat_to_funbool k (j/2) i := by
        intro i hi
        unfold nat_to_funbool
        have h_eq : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
        rw [h_eq, pow_succ]
        rw [show j / (2^(k-1-i) * 2) = j / 2 / 2^(k-1-i) from by
              rw [Nat.div_div_eq_div_mul]; ring_nf]
      rw [funbool_to_nat_congr k _ _ h_lower]
      have h_ih : j / 2 < 2^k := by
        rw [show 2^(k+1) = 2 * 2^k from by ring] at h
        omega
      rw [ih (j/2) h_ih]
      -- Goal: 2 * (j/2) + (if decide (j%2=1) then 1 else 0) = j
      by_cases h_mod : j % 2 = 1
      · rw [show (decide (j % 2 = 1) = true) from decide_eq_true h_mod]
        simp; omega
      · have h_mod_zero : j % 2 = 0 := by omega
        rw [show (decide (j % 2 = 1) = false) from decide_eq_false h_mod]
        simp; omega

/-- Bridge: every basis vector at index `j < 2^n` can be written as
    `f_to_vec` of the inverse-funbool-to-nat function. Nat-indexed form,
    avoids `Fin (2^n)` vs `Fin 8` unification friction. -/
theorem basis_vector_eq_f_to_vec_nat (n j : Nat) (h : j < 2^n) :
    basis_vector (2^n) j = f_to_vec n (nat_to_funbool n j) := by
  unfold f_to_vec
  congr 1
  exact (funbool_to_nat_nat_to_funbool n j h).symm

/-- Fin-indexed version (legacy). -/
theorem basis_vector_eq_f_to_vec_nat_to_funbool (n : Nat) (j : Fin (2^n)) :
    basis_vector (2^n) j.val = f_to_vec n (nat_to_funbool n j.val) :=
  basis_vector_eq_f_to_vec_nat n j.val j.isLt

/-- For k.val = 0: nat_to_funbool 3 0 i = false for all i. -/
theorem nat_to_funbool_3_0_eq_false (i : Nat) :
    nat_to_funbool 3 0 i = false := by
  unfold nat_to_funbool
  simp

/-- For k.val = 1 = 001₂: bit pattern is (false, false, true) at indices (0, 1, 2). -/
theorem nat_to_funbool_3_1_zero : nat_to_funbool 3 1 0 = false := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_1_one : nat_to_funbool 3 1 1 = false := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_1_two : nat_to_funbool 3 1 2 = true := by
  unfold nat_to_funbool; simp

/-- For k.val = 2 = 010₂: bit pattern (false, true, false). -/
theorem nat_to_funbool_3_2_zero : nat_to_funbool 3 2 0 = false := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_2_one : nat_to_funbool 3 2 1 = true := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_2_two : nat_to_funbool 3 2 2 = false := by
  unfold nat_to_funbool; simp

/-- For k.val = 3 = 011₂: bit pattern (false, true, true). -/
theorem nat_to_funbool_3_3_zero : nat_to_funbool 3 3 0 = false := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_3_one : nat_to_funbool 3 3 1 = true := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_3_two : nat_to_funbool 3 3 2 = true := by
  unfold nat_to_funbool; simp

/-- For k.val = 4 = 100₂: bit pattern (true, false, false). -/
theorem nat_to_funbool_3_4_zero : nat_to_funbool 3 4 0 = true := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_4_one : nat_to_funbool 3 4 1 = false := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_4_two : nat_to_funbool 3 4 2 = false := by
  unfold nat_to_funbool; simp

/-- For k.val = 5 = 101₂: bit pattern (true, false, true). -/
theorem nat_to_funbool_3_5_zero : nat_to_funbool 3 5 0 = true := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_5_one : nat_to_funbool 3 5 1 = false := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_5_two : nat_to_funbool 3 5 2 = true := by
  unfold nat_to_funbool; simp

/-- For k.val = 6 = 110₂: bit pattern (true, true, false). -/
theorem nat_to_funbool_3_6_zero : nat_to_funbool 3 6 0 = true := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_6_one : nat_to_funbool 3 6 1 = true := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_6_two : nat_to_funbool 3 6 2 = false := by
  unfold nat_to_funbool; simp

/-- For k.val = 7 = 111₂: bit pattern (true, true, true). -/
theorem nat_to_funbool_3_7_zero : nat_to_funbool 3 7 0 = true := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_7_one : nat_to_funbool 3 7 1 = true := by
  unfold nat_to_funbool; simp

theorem nat_to_funbool_3_7_two : nat_to_funbool 3 7 2 = true := by
  unfold nat_to_funbool; simp

-- NOTE: `CCX_eq_toffoliMatrix_proved` lives in `GateDecompositions.lean`
-- because it references `toffoliMatrix` which is defined there. Helpers used
-- there (matrix_eq_of_basis_action, basis_vector_eq_f_to_vec_nat,
-- nat_to_funbool, nat_to_funbool_3_0_eq_false) are all in this file.

/-- Matrix-level Toffoli involution: applying CCX twice is the identity matrix.
    Lifted from `f_to_vec_CCX_involutive` via `matrix_eq_of_basis_action`.
    -- SQIR/SQIR/UnitaryOps.v analog: CCX is self-inverse (involution). -/
theorem CCX_CCX_eq_one (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim) *
      uc_eval (BaseUCom.CCX a b c : BaseUCom dim)
    = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool, Matrix.mul_assoc,
      f_to_vec_CCX_involutive dim a b c ha hb hc hab hac hbc, Matrix.one_mul]

/-- UCom.equiv form of `CCX_CCX_eq_one`: at the circuit level,
    `CCX a b c ; CCX a b c ≅ ID 0` whenever `dim ≥ 1`. Useful for
    Toffoli-pair cancellation in circuit-level rewriting.
    -- SQIR/SQIR/Equivalences.v analog: SKIP-style identity (X_X_id pattern). -/
theorem CCX_CCX_id {dim : Nat} (a b c : Nat) (h0 : 0 < dim)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    UCom.equiv
      (UCom.seq (BaseUCom.CCX a b c : BaseUCom dim) (BaseUCom.CCX a b c))
      (BaseUCom.ID 0) := by
  show uc_eval (BaseUCom.CCX a b c : BaseUCom dim) *
         uc_eval (BaseUCom.CCX a b c : BaseUCom dim)
       = uc_eval (BaseUCom.ID 0 : BaseUCom dim)
  rw [uc_eval_ID_eq_one h0]
  exact CCX_CCX_eq_one dim a b c ha hb hc hab hac hbc

/-- `CCX a b c ; CCX a b c ; CCX a b c` acts as a single CCX on
    `f_to_vec dim f` (CCX³ = CCX, since CCX² = ID). Direct corollary
    of `CCX_CCX_eq_one` (matrix-level) + `f_to_vec_CCX_proved`.
    Completes the 3-chain family on basis states: X³, Z³, CNOT³, CCX³.
    -- SQIR/SQIR/UnitaryOps.v analog: Toffoli 3-chain identity. -/
theorem f_to_vec_CCX_CCX_CCX (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.CCX a b c : BaseUCom dim)
                                (BaseUCom.CCX a b c))
                       (BaseUCom.CCX a b c))
      * f_to_vec dim f
      = f_to_vec dim (update f c (xor (f c) (f a && f b))) := by
  -- Unfold outer seq, then inner seq, to get CCX * (CCX * (CCX * f_to_vec f)).
  rw [uc_eval_seq_mul, uc_eval_seq_mul]
  -- Innermost CCX * f_to_vec f reduces to f_to_vec (update ...) by f_to_vec_CCX_proved.
  rw [f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc f]
  -- Remaining outer two CCXs act on the updated f_to_vec; by involution, return as-is.
  exact f_to_vec_CCX_involutive dim a b c ha hb hc hab hac hbc _

/-- `X q ; X q ; X q ; X q ; X q` acts as a single X on `f_to_vec dim f`
    (X⁵ = X, since X⁴ = ID). Iter 101 extension of the basis-state
    Pauli-chain family. Useful for circuit-rewriting passes that
    encounter X-gate odd-length chains. -/
theorem f_to_vec_X_X_X_X_X (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.X n : BaseUCom dim) (BaseUCom.X n))
              (BaseUCom.X n)) (BaseUCom.X n)) (BaseUCom.X n))
      * f_to_vec dim f
      = f_to_vec dim (update f n (!f n)) := by
  -- uc_eval(seq^4 X) * f_to_vec f = X * (uc_eval(seq^3 X) * f_to_vec f) by uc_eval_seq_mul.
  -- Inner uc_eval(seq^3 X) * f_to_vec f = f_to_vec f by f_to_vec_X_X_X_X (X⁴ = ID).
  -- Then X * f_to_vec f = f_to_vec (update f n (!f n)) by f_to_vec_X_uc_eval.
  rw [uc_eval_seq_mul]
  rw [f_to_vec_X_X_X_X dim n h f]
  exact f_to_vec_X_uc_eval dim n h f

-- SQIR/SQIR/Equivalences.v (Pauli order-cycle analog of Z⁵ = Z): f_to_vec lift

/-- `Z q ; Z q ; Z q ; Z q ; Z q` acts as a single Z on `f_to_vec dim f`
    (Z⁵ = Z, since Z⁴ = ID). Mirrors `f_to_vec_X_X_X_X_X` (Iter 101)
    for the Pauli Z gate's cyclic phase action. Useful for circuit-
    rewriting passes that encounter Z-gate odd-length chains. -/
theorem f_to_vec_Z_Z_Z_Z_Z (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.Z n : BaseUCom dim) (BaseUCom.Z n))
              (BaseUCom.Z n)) (BaseUCom.Z n)) (BaseUCom.Z n))
      * f_to_vec dim f
      = (if f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  -- uc_eval(seq^4 Z) * f_to_vec f = Z * (uc_eval(seq^3 Z) * f_to_vec f) by uc_eval_seq_mul.
  -- Inner uc_eval(seq^3 Z) * f_to_vec f = f_to_vec f by f_to_vec_Z_Z_Z_Z (Z⁴ = ID).
  -- Then Z * f_to_vec f = (±1) • f_to_vec f by f_to_vec_Z_uc_eval.
  rw [uc_eval_seq_mul]
  rw [f_to_vec_Z_Z_Z_Z dim n h f]
  exact f_to_vec_Z_uc_eval dim n h f

-- SQIR/SQIR/Equivalences.v line 109: CNOT_CNOT_id

/-- Matrix-level CNOT involution: applying CNOT twice is the identity matrix.
    Lifted from `f_to_vec_CNOT_CNOT` via `matrix_eq_of_basis_action`. -/
theorem CNOT_CNOT_eq_one (dim i j : Nat)
    (hi : i < dim) (hj : j < dim) (hij : i ≠ j) :
    uc_eval (UCom.seq (BaseUCom.CNOT i j : BaseUCom dim) (BaseUCom.CNOT i j))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_CNOT_CNOT dim i j hi hj hij, Matrix.one_mul]

/-- UCom.equiv form of `CNOT_CNOT_eq_one`: at the circuit level,
    `CNOT i j ; CNOT i j ≅ ID 0` whenever `dim ≥ 1`. -/
theorem CNOT_CNOT_id {dim : Nat} (i j : Nat) (h0 : 0 < dim)
    (hi : i < dim) (hj : j < dim) (hij : i ≠ j) :
    UCom.equiv
      (UCom.seq (UCom.seq (BaseUCom.CNOT i j : BaseUCom dim) (BaseUCom.CNOT i j))
                (BaseUCom.ID 0))
      (BaseUCom.ID 0) := by
  show uc_eval (BaseUCom.ID 0 : BaseUCom dim) *
         uc_eval (UCom.seq (BaseUCom.CNOT i j : BaseUCom dim) (BaseUCom.CNOT i j))
       = uc_eval (BaseUCom.ID 0 : BaseUCom dim)
  rw [uc_eval_ID_eq_one h0, CNOT_CNOT_eq_one dim i j hi hj hij, Matrix.one_mul]

/-- **Seq-form basis-state lift** of `CCX_CCX_eq_one`. Cleaner
    statement than `f_to_vec_CCX_involutive` (product form): uses
    `UCom.seq` directly. Useful for chained rewrites at the seq
    level. -- SQIR/SQIR/Equivalences.v: CCX_CCX_id at basis state. -/
theorem f_to_vec_seq_CCX_CCX_eq_self (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.CCX a b c : BaseUCom dim) (BaseUCom.CCX a b c))
      * f_to_vec dim f
      = f_to_vec dim f := by
  show (uc_eval (BaseUCom.CCX a b c : BaseUCom dim)
        * uc_eval (BaseUCom.CCX a b c : BaseUCom dim))
       * f_to_vec dim f = f_to_vec dim f
  rw [CCX_CCX_eq_one dim a b c ha hb hc hab hac hbc, Matrix.one_mul]

/-- **Seq-form basis-state lift** of `CNOT_CNOT_eq_one`. The matrix-
    level theorem is ALREADY in seq form, so the `rw` applies
    directly without a `show`. -/
theorem f_to_vec_seq_CNOT_CNOT_eq_self (dim i j : Nat)
    (hi : i < dim) (hj : j < dim) (hij : i ≠ j) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.CNOT i j : BaseUCom dim) (BaseUCom.CNOT i j))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [CNOT_CNOT_eq_one dim i j hi hj hij, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v line 68: X_X_id

/-- Matrix-level X involution: applying X twice is the identity matrix.
    Lifted from `f_to_vec_X_X` via `matrix_eq_of_basis_action`.
    **Completes the X/CNOT/CCX matrix-level involution family** —
    each is a single-line application of the basis-action lift, using
    the existing per-gate basis-state involutions. -/
theorem X_X_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (BaseUCom.X n : BaseUCom dim) (BaseUCom.X n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_X_X dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v line ~71: Y_Y_id

/-- Matrix-level Y involution: applying Y twice is the identity matrix.
    Lifted from `f_to_vec_Y_Y` via `matrix_eq_of_basis_action`. -/
theorem Y_Y_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_Y_Y dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v line ~74: Z_Z_id

/-- Matrix-level Z involution: applying Z twice is the identity matrix.
    Lifted from `f_to_vec_Z_Z` via `matrix_eq_of_basis_action`. -/
theorem Z_Z_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (BaseUCom.Z n : BaseUCom dim) (BaseUCom.Z n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_Z_Z dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v line ~77: H_H_id

/-- Matrix-level H involution: applying H twice is the identity matrix.
    Lifted from `f_to_vec_H_H` via `matrix_eq_of_basis_action`.
    **Extends the Pauli involution family** (X/Y/Z/H) to matrix-level. -/
theorem H_H_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_H_H dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v: X⁴ = ID (order-4 identity for Pauli X)

/-- Matrix-level X order-4 identity: `X⁴ = 1`. Lifted from
    `f_to_vec_X_X_X_X` via `matrix_eq_of_basis_action`. Mirrors the
    pattern of `X_X_eq_one` but for the 4-chain. Useful for cyclic
    cancellation in circuits where X gates may appear an even number
    of times on the same qubit. -/
theorem X_X_X_X_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.X n : BaseUCom dim)
                                          (BaseUCom.X n))
                                (BaseUCom.X n))
                      (BaseUCom.X n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_X_X_X_X dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v: Z⁴ = ID (order-4 identity for Pauli Z)

/-- Matrix-level Z order-4 identity: `Z⁴ = 1`. Lifted from
    `f_to_vec_Z_Z_Z_Z` via `matrix_eq_of_basis_action`. -/
theorem Z_Z_Z_Z_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.Z n : BaseUCom dim)
                                          (BaseUCom.Z n))
                                (BaseUCom.Z n))
                      (BaseUCom.Z n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_Z_Z_Z_Z dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v: S⁴ = ID (order-4 identity for S phase gate)

/-- Matrix-level S order-4 identity: `S⁴ = 1`. Derived from
    existing `S_S_S_S_eq_ID` (RHS `uc_eval (BaseUCom.ID n)`) +
    `uc_eval_ID_eq_one` (converts to matrix `1` when `n < dim`). -/
theorem S_S_S_S_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
                       (BaseUCom.S n)) (BaseUCom.S n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  rw [S_S_S_S_eq_ID, uc_eval_ID_eq_one h]

-- SQIR/SQIR/Equivalences.v: H⁴ = ID

/-- Matrix-level H order-4 identity: `H⁴ = 1`. Direct lift of
    `H_H_H_H_eq_ID` via `uc_eval_ID_eq_one`. -/
theorem H_H_H_H_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
                       (BaseUCom.H n)) (BaseUCom.H n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  rw [H_H_H_H_eq_ID, uc_eval_ID_eq_one h]

-- SQIR/SQIR/Equivalences.v: Y⁴ = ID (order-4 identity for Pauli Y)

/-- Matrix-level Y order-4 identity: `Y⁴ = 1`. **Derived via
    composition** rather than f_to_vec lift (no
    `f_to_vec_Y_Y_Y_Y` exists). Strategy: reassociate
    `Y * (Y * (Y * Y))` to `(Y * Y) * (Y * Y)` via `Matrix.mul_assoc`,
    then collapse each pair via `Y_Y_eq_one`. -/
theorem Y_Y_Y_Y_eq_one (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.Y n : BaseUCom dim)
                                          (BaseUCom.Y n))
                                (BaseUCom.Y n))
                      (BaseUCom.Y n))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  -- uc_eval (UCom.seq ... Y) = Y * (Y * (Y * Y)) (left-associated bracket).
  show uc_eval (BaseUCom.Y n : BaseUCom dim)
        * (uc_eval (BaseUCom.Y n)
          * (uc_eval (BaseUCom.Y n) * uc_eval (BaseUCom.Y n))) = 1
  rw [← Matrix.mul_assoc
        (uc_eval (BaseUCom.Y n : BaseUCom dim))
        (uc_eval (BaseUCom.Y n))
        (uc_eval (BaseUCom.Y n) * uc_eval (BaseUCom.Y n))]
  -- Now: (Y * Y) * (Y * Y) = 1
  show (uc_eval (UCom.seq (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n)))
        * (uc_eval (UCom.seq (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))) = 1
  rw [Y_Y_eq_one dim n h, Matrix.one_mul]

/-- Basis-state lift of `Y_Y_Y_Y_eq_one` (matrix-level Y⁴ = 1).
    Useful for chaining at the f_to_vec layer (per-bit cascade
    correctness proofs needing Y-gate involution in 4-chain form). -/
theorem f_to_vec_Y_Y_Y_Y (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.Y n : BaseUCom dim)
                                          (BaseUCom.Y n))
                                (BaseUCom.Y n))
                      (BaseUCom.Y n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [Y_Y_Y_Y_eq_one dim n h, Matrix.one_mul]

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: Y⁵ = Y at basis level

/-- `Y q ; Y q ; Y q ; Y q ; Y q` acts as a single `Y q` on `f_to_vec dim f`
    (Y⁵ = Y, since Y⁴ = ID). **Relational form**: unlike X⁵ and Z⁵ which
    have closed-form basis-state results (`update` for X, `±1 •` for Z),
    Y introduces an `i·(-1)^b` phase that has no closed form on
    `f_to_vec dim f` alone. So the cleanest statement is
    `uc_eval(Y⁵) · v = uc_eval(Y) · v`. Completes the Pauli order-5
    basis-state family (X⁵/Y⁵/Z⁵) mirroring Iter 101 and the Iter 132
    SQIR-tick. -/
theorem f_to_vec_Y_Y_Y_Y_Y (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))
              (BaseUCom.Y n)) (BaseUCom.Y n)) (BaseUCom.Y n))
      * f_to_vec dim f
      = uc_eval (BaseUCom.Y n : BaseUCom dim) * f_to_vec dim f := by
  -- uc_eval(seq^4 Y) * f_to_vec f = Y * (uc_eval(seq^3 Y) * f_to_vec f) by uc_eval_seq_mul.
  -- Inner uc_eval(seq^3 Y) * f_to_vec f = f_to_vec f by f_to_vec_Y_Y_Y_Y (Y⁴ = ID).
  rw [uc_eval_seq_mul]
  rw [f_to_vec_Y_Y_Y_Y dim n h f]

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: Y⁵ = Y at matrix level

/-- **Matrix-level Y order-5 cyclic identity**: `Y⁵ = Y`. Direct
    consequence of `Y_Y_Y_Y_eq_one` (Y⁴ = 1) plus `Matrix.mul_one`.
    More useful than the f_to_vec form (Iter 133) when the input is
    NOT a basis state — e.g., during circuit-equivalence rewriting
    on arbitrary state vectors. Per Iter 132 reflection. -/
theorem Y_Y_Y_Y_Y_eq_Y (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))
              (BaseUCom.Y n)) (BaseUCom.Y n)) (BaseUCom.Y n))
      = uc_eval (BaseUCom.Y n : BaseUCom dim) := by
  -- uc_eval (seq^4 Y) unfolds (defeq) to Y * uc_eval(seq^3 Y).
  show uc_eval (BaseUCom.Y n : BaseUCom dim)
        * uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.Y n : BaseUCom dim) (BaseUCom.Y n))
                                       (BaseUCom.Y n)) (BaseUCom.Y n))
       = uc_eval (BaseUCom.Y n : BaseUCom dim)
  rw [Y_Y_Y_Y_eq_one dim n h, Matrix.mul_one]

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: Z⁵ = Z at matrix level

/-- **Matrix-level Z order-5 cyclic identity**: `Z⁵ = Z`. Direct
    consequence of `Z_Z_Z_Z_eq_one` (Z⁴ = 1) plus `Matrix.mul_one`.
    Mirrors `Y_Y_Y_Y_Y_eq_Y` (Iter 137) — same proof structure.
    Matrix-level form for circuit-equivalence proofs on arbitrary
    state vectors. -/
theorem Z_Z_Z_Z_Z_eq_Z (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.Z n : BaseUCom dim) (BaseUCom.Z n))
              (BaseUCom.Z n)) (BaseUCom.Z n)) (BaseUCom.Z n))
      = uc_eval (BaseUCom.Z n : BaseUCom dim) := by
  -- uc_eval (seq^4 Z) unfolds (defeq) to Z * uc_eval(seq^3 Z).
  show uc_eval (BaseUCom.Z n : BaseUCom dim)
        * uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.Z n : BaseUCom dim) (BaseUCom.Z n))
                                       (BaseUCom.Z n)) (BaseUCom.Z n))
       = uc_eval (BaseUCom.Z n : BaseUCom dim)
  rw [Z_Z_Z_Z_eq_one dim n h, Matrix.mul_one]

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: X⁵ = X at matrix level

/-- **Matrix-level X order-5 cyclic identity**: `X⁵ = X`. Direct
    consequence of `X_X_X_X_eq_one` (X⁴ = 1) plus `Matrix.mul_one`.
    Completes the Pauli matrix-level order-5 family (X/Y/Z all done
    after this — Y from Iter 137, Z from the Iter 144 SQIR-tick). -/
theorem X_X_X_X_X_eq_X (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.X n : BaseUCom dim) (BaseUCom.X n))
              (BaseUCom.X n)) (BaseUCom.X n)) (BaseUCom.X n))
      = uc_eval (BaseUCom.X n : BaseUCom dim) := by
  -- uc_eval (seq^4 X) unfolds (defeq) to X * uc_eval(seq^3 X).
  show uc_eval (BaseUCom.X n : BaseUCom dim)
        * uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.X n : BaseUCom dim) (BaseUCom.X n))
                                       (BaseUCom.X n)) (BaseUCom.X n))
       = uc_eval (BaseUCom.X n : BaseUCom dim)
  rw [X_X_X_X_eq_one dim n h, Matrix.mul_one]

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: H⁵ = H at matrix level

/-- **Matrix-level H order-5 cyclic identity**: `H⁵ = H`. Direct
    consequence of `H_H_H_H_eq_one` (H⁴ = 1) plus `Matrix.mul_one`.
    Mirrors `X_X_X_X_X_eq_X`/`Y_Y_Y_Y_Y_eq_Y`/`Z_Z_Z_Z_Z_eq_Z`,
    same proof shape. Matrix-level form for circuit-equivalence
    proofs on arbitrary state vectors (not just basis states). -/
theorem H_H_H_H_H_eq_H (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
              (BaseUCom.H n)) (BaseUCom.H n)) (BaseUCom.H n))
      = uc_eval (BaseUCom.H n : BaseUCom dim) := by
  -- uc_eval (seq^4 H) unfolds (defeq) to H * uc_eval(seq^3 H).
  show uc_eval (BaseUCom.H n : BaseUCom dim)
        * uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.H n : BaseUCom dim) (BaseUCom.H n))
                                       (BaseUCom.H n)) (BaseUCom.H n))
       = uc_eval (BaseUCom.H n : BaseUCom dim)
  rw [H_H_H_H_eq_one dim n h, Matrix.mul_one]

-- SQIR/SQIR/Equivalences.v cyclic-cancellation analog: S⁵ = S at matrix level

/-- **Matrix-level S order-5 cyclic identity**: `S⁵ = S`. Direct
    consequence of `S_S_S_S_eq_one` (S⁴ = 1) plus `Matrix.mul_one`.
    Same proof pattern as X/Y/Z/H matrix-level lifts. Completes
    the Clifford matrix-level order-5 family (X, Y, Z, H, S all
    done now). -/
theorem S_S_S_S_S_eq_S (dim n : Nat) (h : n < dim) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
              (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
              (BaseUCom.S n)) (BaseUCom.S n)) (BaseUCom.S n))
      = uc_eval (BaseUCom.S n : BaseUCom dim) := by
  -- uc_eval (seq^4 S) unfolds (defeq) to S * uc_eval(seq^3 S).
  show uc_eval (BaseUCom.S n : BaseUCom dim)
        * uc_eval (UCom.seq (UCom.seq (UCom.seq (BaseUCom.S n : BaseUCom dim) (BaseUCom.S n))
                                       (BaseUCom.S n)) (BaseUCom.S n))
       = uc_eval (BaseUCom.S n : BaseUCom dim)
  rw [S_S_S_S_eq_one dim n h, Matrix.mul_one]

/-- Toffoli control symmetry: swapping the two control qubits leaves
    the gate's matrix unchanged. Follows from `f_to_vec_CCX_proved`,
    which uses `f a && f b` — symmetric in `a, b` via `Bool.and_comm`.
    -- SQIR/SQIR/UnitaryOps.v analog: CCX a b c ≡ CCX b a c. -/
theorem CCX_control_symm {dim : Nat} (a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim)
      = uc_eval (BaseUCom.CCX b a c : BaseUCom dim) := by
  apply matrix_eq_of_basis_action
  intro k
  rw [basis_vector_eq_f_to_vec_nat_to_funbool,
      f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc,
      f_to_vec_CCX_proved dim b a c hb ha hc (Ne.symm hab) hbc hac,
      Bool.and_comm]

/-- UCom.equiv form of `CCX_control_symm`: at the circuit level,
    `CCX a b c ≅ CCX b a c`. Direct corollary since `UCom.equiv` is
    just `uc_eval` equality.
    -- SQIR/SQIR/Equivalences.v style. -/
theorem CCX_control_symm_equiv {dim : Nat} (a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    UCom.equiv (BaseUCom.CCX a b c : BaseUCom dim) (BaseUCom.CCX b a c) :=
  CCX_control_symm a b c ha hb hc hab hac hbc

/-- Basis-state lift of `CCX_control_symm`: applying CCX with controls
    `(a, b)` to `f_to_vec dim f` gives the same result as CCX with
    controls swapped `(b, a)`. Direct corollary, useful when the
    available rewriting form is on `f_to_vec`-applied form.
    -- SQIR/SQIR/UnitaryOps.v: CCX-control-symmetry at the basis level. -/
theorem f_to_vec_CCX_control_symm (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (BaseUCom.CCX a b c : BaseUCom dim) * f_to_vec dim f
      = uc_eval (BaseUCom.CCX b a c : BaseUCom dim) * f_to_vec dim f := by
  rw [CCX_control_symm a b c ha hb hc hab hac hbc]

end FormalRV.Framework
