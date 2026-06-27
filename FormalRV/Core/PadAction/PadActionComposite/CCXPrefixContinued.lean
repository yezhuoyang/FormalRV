/- PadActionComposite — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Core.PadAction.PadActionComposite.ChainValidationAndCCXPrefix

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker

/-! ## CCX prefix: ... + CNOT a b (11 gates, ends s3)

    Gate 11 = last gate of s3. CNOT a b again — un-does gate 9's b-bit XOR.
    State b-bit returns to f b. After update_idem (collapse double-b update)
    and update_self (resetting b to f b is no-op), the state simplifies
    back to `update f c {false,true}`. -/

theorem f_to_vec_CCX_prefix_11 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
        (BaseUCom.H c : BaseUCom dim) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.T c))
        (BaseUCom.CNOT b c))
        (BaseUCom.TDAG c))
        (BaseUCom.CNOT a c))
        (BaseUCom.CNOT a b))
        (BaseUCom.TDAG b))
        (BaseUCom.CNOT a b))
      * f_to_vec dim f
      = ((if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + ((if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_10 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_CNOT_proved dim a b
      (update (update f c false) b (xor (f b) (f a))) ha hb hab]
  rw [f_to_vec_CNOT_proved dim a b
      (update (update f c true) b (xor (f b) (f a))) ha hb hab]
  -- (update _ b w) b = w; (update (update f c v) b w) a = f a (a ≠ b, a ≠ c)
  rw [show (update (update f c false) b (xor (f b) (f a))) b = xor (f b) (f a)
      from update_eq _ b (xor (f b) (f a))]
  rw [show (update (update f c true) b (xor (f b) (f a))) b = xor (f b) (f a)
      from update_eq _ b (xor (f b) (f a))]
  rw [show (update (update f c false) b (xor (f b) (f a))) a = f a from by
      rw [update_neq _ b a (xor (f b) (f a)) hab,
          update_neq _ c a false hac]]
  rw [show (update (update f c true) b (xor (f b) (f a))) a = f a from by
      rw [update_neq _ b a (xor (f b) (f a)) hab,
          update_neq _ c a true hac]]
  -- xor (xor (f b) (f a)) (f a) = f b
  rw [show xor (xor (f b) (f a)) (f a) = f b from by
      cases f b <;> cases f a <;> decide]
  -- update_idem collapses the double-b update; update_self collapses (update _ b (f b))
  rw [update_idem, update_idem]
  -- Now: update (update f c false) b (f b) needs (update f c false) b = f b first
  rw [show update (update f c false) b (f b)
        = update (update f c false) b ((update f c false) b) from by
      rw [update_neq _ c b false hbc]]
  rw [show update (update f c true) b (f b)
        = update (update f c true) b ((update f c true) b) from by
      rw [update_neq _ c b true hbc]]
  rw [update_self, update_self]

/-! ## CCX prefix: ... + T a (12 gates)

    Gate 12 = T a (start of s4). a-bit phase factor.
    Both branches' a-bit is f a (a is unchanged through all previous gates,
    and (update f c v) a = f a for a ≠ c). Same phase on both branches. -/

theorem f_to_vec_CCX_prefix_12 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
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
      * f_to_vec dim f
      = ((if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + ((if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_11 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_T_uc_eval dim a ha (update f c false)]
  rw [f_to_vec_T_uc_eval dim a ha (update f c true)]
  rw [show (update f c false) a = f a from update_neq f c a false hac]
  rw [show (update f c true) a = f a from update_neq f c a true hac]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + T b (13 gates)

    Gate 13 = T b. b-bit phase factor. Both branches' b-bit is f b
    (b is unchanged after gate 11's un-do). Same phase on both. -/

theorem f_to_vec_CCX_prefix_13 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
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
      * f_to_vec dim f
      = ((if f b then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + ((if f b then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_12 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_T_uc_eval dim b hb (update f c false)]
  rw [f_to_vec_T_uc_eval dim b hb (update f c true)]
  rw [show (update f c false) b = f b from update_neq f c b false hbc]
  rw [show (update f c true) b = f b from update_neq f c b true hbc]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-! ## CCX prefix: ... + T c (14 gates)

    Gate 14 = T c. c-bit phase factor. Branch 0 c-bit = false (no phase),
    branch 1 c-bit = true (phase exp(iπ/4)). Last asymmetry-introducing
    gate before the final H bifurcation. -/

theorem f_to_vec_CCX_prefix_14 (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
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
      * f_to_vec dim f
      = ((1 : ℂ)
          * (if f b then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (if xor (f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
          * (if f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
          * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c false)
        + (Complex.exp (Complex.I * (Real.pi / 4))
           * (if f b then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f a then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if xor (f b) (f a) then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if !f a then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (if xor (!f b) (f a) then Complex.exp (Complex.I * (Real.pi / 4)) else 1)
           * (if f c then (-1 : ℂ) else 1)
           * (if !f b then Complex.exp (-(Complex.I * (Real.pi / 4))) else 1)
           * (Real.sqrt 2 / 2 : ℂ))
          • f_to_vec dim (update f c true) := by
  rw [uc_eval_seq_mul]
  rw [f_to_vec_CCX_prefix_13 dim a b c ha hb hc hab hac hbc f]
  rw [mul_add_state]
  rw [mul_smul_state, mul_smul_state]
  rw [f_to_vec_T_uc_eval dim c hc (update f c false)]
  rw [f_to_vec_T_uc_eval dim c hc (update f c true)]
  rw [show (update f c false) c = false from update_eq f c false]
  rw [show (update f c true) c = true from update_eq f c true]
  rw [smul_smul, smul_smul]
  congr 1
  · congr 1; simp
  · congr 1
    simp only [if_true]
    ring


end FormalRV.Framework
