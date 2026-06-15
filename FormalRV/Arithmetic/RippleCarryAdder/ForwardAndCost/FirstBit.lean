/-
  FormalRV.Arithmetic.RippleCarryAdder.ForwardAndCost.FirstBit
  Faithful FIRST bit-step (part 3/5): its correctness, T and gate counts, matrix
  level reversibility, and the first-bit disjointness derivation.
  Builds on `InteriorBit`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.ForwardAndCost.InteriorBit

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-- T-count of the first-bit step: 7 (1 Toffoli; 2 CXs are tcount-0). -/
theorem tcount_gidney_adder_bit_step_faithful_first :
    tcount gidney_adder_bit_step_faithful_first = 7 := by
  unfold gidney_adder_bit_step_faithful_first
  rfl

/-- Gate count of the first-bit step: 3 (vs 4 for interior bits;
    no chain CX). -/
theorem gcount_gidney_adder_bit_step_faithful_first :
    gcount gidney_adder_bit_step_faithful_first = 3 := by
  unfold gidney_adder_bit_step_faithful_first
  rfl

/-- **First-bit correctness on classical basis states** (Iter 65).
    Proves `gidney_adder_bit_step_faithful_first` acts on `f_to_vec
    dim f` to produce `f_to_vec dim (gidney_first_bit_post_state f)`.
    Proof via two applications of `gate_seq_acts_on_basis` + the
    per-gate primitives. -/
theorem gidney_adder_bit_step_faithful_first_correct
    (dim : Nat) (f : Nat → Bool)
    (hr0 : read_idx 0 < dim) (ht0 : target_idx 0 < dim)
    (hc0 : carry_idx 0 < dim) (hr1 : read_idx 1 < dim)
    (ht1 : target_idx 1 < dim)
    (h_rt : read_idx 0 ≠ target_idx 0)
    (h_rc : read_idx 0 ≠ carry_idx 0)
    (h_tc : target_idx 0 ≠ carry_idx 0)
    (h_c_r1 : carry_idx 0 ≠ read_idx 1)
    (h_c_t1 : carry_idx 0 ≠ target_idx 1) :
    uc_eval (Gate.toUCom dim gidney_adder_bit_step_faithful_first)
      * f_to_vec dim f
      = f_to_vec dim (gidney_first_bit_post_state f) := by
  unfold gidney_adder_bit_step_faithful_first gidney_first_bit_post_state
  -- Two nested seq's: seq (seq CCX CX_r1) CX_t1
  apply gate_seq_acts_on_basis dim _ _ f _ _
  · apply gate_seq_acts_on_basis dim _ _ f _ _
    · -- CCX: write (read[0] ∧ target[0]) into carry[0]
      exact gate_ccx_acts_on_basis dim _ _ _ hr0 ht0 hc0 h_rt h_rc h_tc f
    · -- CX (propagation to read[1])
      exact gate_cx_acts_on_basis dim _ _ hc0 hr1 h_c_r1 _
  · -- CX (propagation to target[1])
    exact gate_cx_acts_on_basis dim _ _ hc0 ht1 h_c_t1 _

/-- The first-bit disjointness conditions are all decidable from the
    indexing (read_idx 0 = 0, target_idx 0 = 1, carry_idx 0 = 2,
    read_idx 1 = 3, target_idx 1 = 4). At dim ≥ 5 all 10 conditions
    hold. -/
theorem first_bit_disjointness_of_dim_bound (dim : Nat) (h : 5 ≤ dim) :
    read_idx 0 < dim ∧ target_idx 0 < dim ∧ carry_idx 0 < dim
    ∧ read_idx 1 < dim ∧ target_idx 1 < dim
    ∧ read_idx 0 ≠ target_idx 0 ∧ read_idx 0 ≠ carry_idx 0
    ∧ target_idx 0 ≠ carry_idx 0
    ∧ carry_idx 0 ≠ read_idx 1 ∧ carry_idx 0 ≠ target_idx 1 := by
  unfold read_idx target_idx carry_idx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- T-count of the first-bit gate-reverse: 7 (matches forward). -/
theorem tcount_gidney_adder_bit_step_faithful_first_reverse :
    tcount gidney_adder_bit_step_faithful_first_reverse = 7 := by
  unfold gidney_adder_bit_step_faithful_first_reverse
  rfl

/-- Gate-count of the first-bit gate-reverse: 3 (matches forward). -/
theorem gcount_gidney_adder_bit_step_faithful_first_reverse :
    gcount gidney_adder_bit_step_faithful_first_reverse = 3 := by
  unfold gidney_adder_bit_step_faithful_first_reverse
  rfl

/-- **First-bit forward · reverse = identity** at matrix level.
    The two propagation CXs cancel pairwise (CNOT involution), and
    the CCX-pair cancels (CCX involution).

    Mirrors Iter 69's `..._faithful_last_fwd_rev_id` pattern but for
    the first-bit step (3 gates instead of 2). -/
theorem gidney_adder_bit_step_faithful_first_fwd_rev_eq_one
    (dim : Nat)
    (hr0 : read_idx 0 < dim) (ht0 : target_idx 0 < dim)
    (hc0 : carry_idx 0 < dim) (hr1 : read_idx 1 < dim) (ht1 : target_idx 1 < dim)
    (h_rt : read_idx 0 ≠ target_idx 0)
    (h_rc : read_idx 0 ≠ carry_idx 0)
    (h_tc : target_idx 0 ≠ carry_idx 0)
    (h_c_r1 : carry_idx 0 ≠ read_idx 1)
    (h_c_t1 : carry_idx 0 ≠ target_idx 1) :
    uc_eval (Gate.toUCom dim
              (Gate.seq gidney_adder_bit_step_faithful_first
                        gidney_adder_bit_step_faithful_first_reverse))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  unfold gidney_adder_bit_step_faithful_first
         gidney_adder_bit_step_faithful_first_reverse
  -- Abbreviate the four matrices: C = CCX, R = CX(carry_0, read_1),
  -- T = CX(carry_0, target_1). Forward gates left-to-right: C, R, T.
  -- uc_eval(fwd) = T*R*C; uc_eval(rev) = C*R*T.
  -- Composition (seq fwd rev): uc_eval(rev) * uc_eval(fwd) = C*R*T*T*R*C.
  -- Plan: reassoc to expose T*T pair → 1, then R*R pair → 1, then C*C → 1.
  show
    (uc_eval (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0) : BaseUCom dim)
      * (uc_eval (BaseUCom.CNOT (carry_idx 0) (read_idx 1))
        * uc_eval (BaseUCom.CNOT (carry_idx 0) (target_idx 1))))
    * (uc_eval (BaseUCom.CNOT (carry_idx 0) (target_idx 1))
      * (uc_eval (BaseUCom.CNOT (carry_idx 0) (read_idx 1))
        * uc_eval (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0)))) = 1
  -- Step 1: outer Matrix.mul_assoc to flatten left bracket.
  rw [Matrix.mul_assoc
        (uc_eval (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0) : BaseUCom dim))
        (uc_eval (BaseUCom.CNOT (carry_idx 0) (read_idx 1))
          * uc_eval (BaseUCom.CNOT (carry_idx 0) (target_idx 1)))
        (uc_eval (BaseUCom.CNOT (carry_idx 0) (target_idx 1))
          * (uc_eval (BaseUCom.CNOT (carry_idx 0) (read_idx 1))
            * uc_eval (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0))))]
  -- Goal: C * ((R*T) * (T * (R*C))) = 1
  rw [Matrix.mul_assoc
        (uc_eval (BaseUCom.CNOT (carry_idx 0) (read_idx 1) : BaseUCom dim))
        (uc_eval (BaseUCom.CNOT (carry_idx 0) (target_idx 1)))
        (uc_eval (BaseUCom.CNOT (carry_idx 0) (target_idx 1))
          * (uc_eval (BaseUCom.CNOT (carry_idx 0) (read_idx 1))
            * uc_eval (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0))))]
  -- Goal: C * (R * (T * (T * (R*C)))) = 1
  rw [← Matrix.mul_assoc
        (uc_eval (BaseUCom.CNOT (carry_idx 0) (target_idx 1) : BaseUCom dim))
        (uc_eval (BaseUCom.CNOT (carry_idx 0) (target_idx 1)))
        (uc_eval (BaseUCom.CNOT (carry_idx 0) (read_idx 1))
          * uc_eval (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0)))]
  -- Goal: C * (R * ((T*T) * (R*C))) = 1
  -- Collapse T*T = uc_eval(seq T T) = 1 via CNOT_CNOT_eq_one
  show uc_eval (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0) : BaseUCom dim)
        * (uc_eval (BaseUCom.CNOT (carry_idx 0) (read_idx 1))
          * (uc_eval (UCom.seq (BaseUCom.CNOT (carry_idx 0) (target_idx 1) : BaseUCom dim)
                                (BaseUCom.CNOT (carry_idx 0) (target_idx 1)))
            * (uc_eval (BaseUCom.CNOT (carry_idx 0) (read_idx 1))
              * uc_eval (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0))))) = 1
  rw [CNOT_CNOT_eq_one dim (carry_idx 0) (target_idx 1) hc0 ht1 h_c_t1]
  rw [Matrix.one_mul]
  -- Goal: C * (R * (R * C)) = 1
  rw [← Matrix.mul_assoc
        (uc_eval (BaseUCom.CNOT (carry_idx 0) (read_idx 1) : BaseUCom dim))
        (uc_eval (BaseUCom.CNOT (carry_idx 0) (read_idx 1)))
        (uc_eval (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0)))]
  -- Goal: C * ((R * R) * C) = 1
  show uc_eval (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0) : BaseUCom dim)
        * (uc_eval (UCom.seq (BaseUCom.CNOT (carry_idx 0) (read_idx 1) : BaseUCom dim)
                              (BaseUCom.CNOT (carry_idx 0) (read_idx 1)))
          * uc_eval (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0))) = 1
  rw [CNOT_CNOT_eq_one dim (carry_idx 0) (read_idx 1) hc0 hr1 h_c_r1]
  rw [Matrix.one_mul]
  -- Goal: C * C = 1 (CCX involution)
  show uc_eval (UCom.seq (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0)
                          : BaseUCom dim)
                         (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0))) = 1
  exact CCX_CCX_eq_one dim _ _ _ hr0 ht0 hc0 h_rt h_rc h_tc

end FormalRV.BQAlgo
