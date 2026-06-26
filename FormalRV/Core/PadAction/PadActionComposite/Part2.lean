/- PadActionComposite — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Core.PadAction.PadActionComposite.Part1

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker

/-! ## Validation: chaining works for T;T (T² phase) -/

/-- Chaining check: applying T twice on `f_to_vec dim f` gives a `T²` phase factor.
    Validates the `uc_eval_seq_mul` + `mul_smul_state` + `f_to_vec_T_uc_eval`
    chain works as expected. This is the simplest non-trivial multi-gate
    composition through `f_to_vec`. -/
theorem f_to_vec_T_T (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.T n : BaseUCom dim) (BaseUCom.T n))
      * f_to_vec dim f
      = (if f n then Complex.exp (Complex.I * (Real.pi / 4))
                    * Complex.exp (Complex.I * (Real.pi / 4))
              else 1)
        • f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_T_uc_eval dim n h f]
  rw [mul_smul_state]
  rw [f_to_vec_T_uc_eval dim n h f]
  rw [smul_smul]
  congr 1
  by_cases hfn : f n <;> simp [hfn]

/-- Chaining check: applying T then T† gives no phase change (T†T = id). -/
theorem f_to_vec_TDAG_T (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.T n : BaseUCom dim) (BaseUCom.TDAG n))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_T_uc_eval dim n h f]
  rw [mul_smul_state]
  rw [f_to_vec_TDAG_uc_eval dim n h f]
  rw [smul_smul]
  -- Need: (if f n then exp(-iπ/4) else 1) * (if f n then exp(iπ/4) else 1) = 1
  rw [show ((if f n then Complex.exp (Complex.I * (Real.pi / 4)) else (1 : ℂ))
            * (if f n then Complex.exp (-(Complex.I * (Real.pi / 4))) else (1 : ℂ)))
          = 1 from by
    by_cases hfn : f n
    · simp [hfn, ← Complex.exp_add]
    · simp [hfn]]
  rw [one_smul]

/-! ## CCX prefix: H c; CNOT b c

    First non-trivial 2-gate composition involving Hadamard. After H c:
    superposition of two basis states. CNOT b c on each branch flips the
    c-bit conditional on b-bit, so the final updated functions become
    `update f c (f b)` and `update f c (!f b)`. -/

theorem f_to_vec_H_CNOT (dim b c : Nat) (hb : b < dim) (hc : c < dim)
    (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c))
      * f_to_vec dim f
      = (Real.sqrt 2 / 2 : ℂ) • f_to_vec dim (update f c (f b))
        + ((if f c then (-1 : ℂ) else 1) * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (!f b)) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_uc_eval dim c hc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim b c (update f c false) hb hc hbc]
  rw [f_to_vec_CNOT_proved dim b c (update f c true) hb hc hbc]
  -- Simplify the nested update expressions to the desired form.
  -- Simplify the inner xor expression: bit c of (update f c v) = v;
  -- bit b of (update f c v) = f b (since b ≠ c).
  rw [show (update f c false) c = false from update_eq f c false]
  rw [show (update f c true) c = true from update_eq f c true]
  rw [show (update f c false) b = f b from update_neq f c b false hbc]
  rw [show (update f c true) b = f b from update_neq f c b true hbc]
  -- xor false (f b) = f b; xor true (f b) = !f b
  simp only [Bool.false_xor, Bool.true_xor]
  -- Then update_idem collapses the nested updates.
  rw [update_idem, update_idem]

/-! ## CCX prefix: H c; CNOT b c; T† c

    3-gate prefix. After H+CNOT we have 2 branches with c-bit = f b vs !f b.
    Applying T† c picks up a phase `exp(-i·π/4)` if the branch's c-bit is 1,
    `1` if 0. The phases differ between the branches. -/

theorem f_to_vec_H_CNOT_TDAG (dim b c : Nat) (hb : b < dim) (hc : c < dim)
    (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c))
                      (BaseUCom.TDAG c))
      * f_to_vec dim f
      = ((if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (f b))
        + ((if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (!f b)) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_CNOT dim b c hb hc hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_TDAG_uc_eval dim c hc (update f c (f b))]
  rw [f_to_vec_TDAG_uc_eval dim c hc (update f c (!f b))]
  rw [show (update f c (f b)) c = f b from update_eq f c (f b)]
  rw [show (update f c (!f b)) c = !f b from update_eq f c (!f b)]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: H c; CNOT b c; T† c; CNOT a c

    4-gate prefix. The CNOT a c flips the c-bit XOR with a-bit. Phases
    from T† c carry through unchanged (CNOT is unitary, doesn't add phase). -/

theorem f_to_vec_H_CNOT_TDAG_CNOT (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
      * f_to_vec dim f
      = ((if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (xor (f b) (f a)))
        + ((if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (xor (!f b) (f a))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_CNOT_TDAG dim b c hb hc hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim a c (update f c (f b)) ha hc hac]
  rw [f_to_vec_CNOT_proved dim a c (update f c (!f b)) ha hc hac]
  -- Simplify each branch's update.
  -- branch 0: update (update f c (f b)) c (xor ((update f c (f b)) c) ((update f c (f b)) a))
  --         = update (update f c (f b)) c (xor (f b) (f a))    [by update_eq, update_neq with a ≠ c]
  --         = update f c (xor (f b) (f a))                       [by update_idem]
  rw [show (update f c (f b)) c = f b from update_eq f c (f b)]
  rw [show (update f c (!f b)) c = !f b from update_eq f c (!f b)]
  rw [show (update f c (f b)) a = f a from update_neq f c a (f b) hac]
  rw [show (update f c (!f b)) a = f a from update_neq f c a (!f b) hac]
  rw [update_idem, update_idem]

/-! ## CCX prefix: H c; CNOT b c; T† c; CNOT a c; T c (5 gates, ends s1+T)

    First gate of `s2`. T c picks up phase exp(iπ/4) on each branch when
    its c-bit is 1. Branch 0 c-bit = xor(f b)(f a); branch 1 c-bit =
    xor(!f b)(f a). These bits are complementary (always differ). -/

theorem f_to_vec_CCX_prefix_5 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
      * f_to_vec dim f
      = ((if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (xor (f b) (f a)))
        + ((if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (xor (!f b) (f a))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_H_CNOT_TDAG_CNOT dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_T_uc_eval dim c hc (update f c (xor (f b) (f a)))]
  rw [f_to_vec_T_uc_eval dim c hc (update f c (xor (!f b) (f a)))]
  rw [show (update f c (xor (f b) (f a))) c = xor (f b) (f a)
      from update_eq f c (xor (f b) (f a))]
  rw [show (update f c (xor (!f b) (f a))) c = xor (!f b) (f a)
      from update_eq f c (xor (!f b) (f a))]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + CNOT b c (6 gates)

    Gate 6: CNOT b c. Each branch's c-bit XORs with f b (since b is unchanged).
    Branch 0 c-bit was xor(f b)(f a), now becomes f a (self-cancellation).
    Branch 1 c-bit was xor(!f b)(f a), now becomes !f a. -/

theorem f_to_vec_CCX_prefix_6 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
      * f_to_vec dim f
      = ((if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (f a))
        + ((if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (!f a)) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_5 dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim b c (update f c (xor (f b) (f a))) hb hc hbc]
  rw [f_to_vec_CNOT_proved dim b c (update f c (xor (!f b) (f a))) hb hc hbc]
  rw [show (update f c (xor (f b) (f a))) c = xor (f b) (f a)
      from update_eq f c (xor (f b) (f a))]
  rw [show (update f c (xor (!f b) (f a))) c = xor (!f b) (f a)
      from update_eq f c (xor (!f b) (f a))]
  rw [show (update f c (xor (f b) (f a))) b = f b
      from update_neq f c b (xor (f b) (f a)) hbc]
  rw [show (update f c (xor (!f b) (f a))) b = f b
      from update_neq f c b (xor (!f b) (f a)) hbc]
  rw [show xor (xor (f b) (f a)) (f b) = f a from by
      cases f b <;> cases f a <;> decide]
  rw [show xor (xor (!f b) (f a)) (f b) = !f a from by
      cases f b <;> cases f a <;> decide]
  rw [update_idem, update_idem]

/-! ## CCX prefix: ... + T† c (7 gates)

    Gate 7: T† c (third gate of s2). Adds phase exp(-iπ/4) per branch
    when branch's c-bit is 1. Branch 0 c-bit = f a, branch 1 = !f a. -/

theorem f_to_vec_CCX_prefix_7 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
      * f_to_vec dim f
      = ((if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (f a))
        + ((if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c (!f a)) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_6 dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_TDAG_uc_eval dim c hc (update f c (f a))]
  rw [f_to_vec_TDAG_uc_eval dim c hc (update f c (!f a))]
  rw [show (update f c (f a)) c = f a from update_eq f c (f a)]
  rw [show (update f c (!f a)) c = !f a from update_eq f c (!f a)]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + CNOT a c (8 gates, ends s2)

    Gate 8 = last gate of s2. CNOT a c flips c-bit XOR with a-bit.
    Branch 0: xor(f a)(f a) = false. Branch 1: xor(!f a)(f a) = true.
    After this gate, the two branches have FIXED c-bits — the f-dependence
    in the c-bit has been fully absorbed into the phase factors. -/

theorem f_to_vec_CCX_prefix_8 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
      * f_to_vec dim f
      = ((if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + ((if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_7 dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim a c (update f c (f a)) ha hc hac]
  rw [f_to_vec_CNOT_proved dim a c (update f c (!f a)) ha hc hac]
  rw [show (update f c (f a)) c = f a from update_eq f c (f a)]
  rw [show (update f c (!f a)) c = !f a from update_eq f c (!f a)]
  rw [show (update f c (f a)) a = f a from update_neq f c a (f a) hac]
  rw [show (update f c (!f a)) a = f a from update_neq f c a (!f a) hac]
  rw [show xor (f a) (f a) = false from by cases f a <;> decide]
  rw [show xor (!f a) (f a) = true from by cases f a <;> decide]
  rw [update_idem, update_idem]

/-! ## CCX prefix: ... + CNOT a b (9 gates, start of s3)

    Gate 9 = first gate of s3. CNOT a b — control a, target b. This is
    the FIRST gate that doesn't touch c. b-bit XORs with a-bit. Each
    branch gains a NESTED update (at c, then at b). Phases unchanged. -/

theorem f_to_vec_CCX_prefix_9 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
      * f_to_vec dim f
      = ((if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update (update f c false) b (xor (f b) (f a)))
        + ((if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update (update f c true) b (xor (f b) (f a))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_8 dim a b c ha hb hc hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim a b (update f c false) ha hb hab]
  rw [f_to_vec_CNOT_proved dim a b (update f c true) ha hb hab]
  -- (update f c v) b = f b (b ≠ c), (update f c v) a = f a (a ≠ c)
  rw [show (update f c false) b = f b from update_neq f c b false hbc]
  rw [show (update f c false) a = f a from update_neq f c a false hac]
  rw [show (update f c true) b = f b from update_neq f c b true hbc]
  rw [show (update f c true) a = f a from update_neq f c a true hac]

/-! ## CCX prefix: ... + T† b (10 gates)

    Gate 10: T† b. b-bit phase factor. After CNOT a b, both branches
    have b-bit = xor(f b)(f a) — SAME for both branches. So both branches
    pick up the same phase factor (no new asymmetry). -/

theorem f_to_vec_CCX_prefix_10 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
      * f_to_vec dim f
      = ((if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update (update f c false) b (xor (f b) (f a)))
        + ((if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update (update f c true) b (xor (f b) (f a))) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_9 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_TDAG_uc_eval dim b hb (update (update f c false) b (xor (f b) (f a)))]
  rw [f_to_vec_TDAG_uc_eval dim b hb (update (update f c true) b (xor (f b) (f a)))]
  -- (update _ b w) b = w
  rw [show (update (update f c false) b (xor (f b) (f a))) b = xor (f b) (f a)
      from update_eq _ b (xor (f b) (f a))]
  rw [show (update (update f c true) b (xor (f b) (f a))) b = xor (f b) (f a)
      from update_eq _ b (xor (f b) (f a))]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring


end FormalRV.Framework
