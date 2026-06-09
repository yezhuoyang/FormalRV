/-
  FormalRV.Arithmetic.RippleCarryAdder.ForwardAndCost.InteriorBit
  Faithful INTERIOR bit-step (part 2/5): its basis-state correctness, T and gate
  counts, matrix-level reversibility, and the per-bit BitDisjointness derivation.
  Builds on `SkeletonCost`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.ForwardAndCost.SkeletonCost

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-! ## Correctness theorems (Iter 52, 2026-05-12)

    **First real semantic-correctness theorems for the review** —
    proving that the Lean Gate IR construction actually computes the
    function it claims to. Per CLAUDE.md hard rule "arithmetic-only
    verifications don't count": these are the review upgrades from
    "scaffolded" (count-only) to "verified" (count + semantics).

    Uses the reusable bridge `gate_ccx_acts_on_basis` (and `_cx_`,
    `_seq_`) from
    [BQAlgo/Correctness.lean](BQAlgo/Correctness.lean). -/

/-- **`gidney_adder_bit_step 0` correctness**: on a classical basis
    state, the i=0 step XORs `(read[0] ∧ target[0])` into `carry[0]`.
    This is the Toffoli action: `(a, b, c) ↦ (a, b, c ⊕ (a ∧ b))`. -/
theorem gidney_adder_bit_step_0_correct (dim : Nat) (f : Nat → Bool)
    (h0 : read_idx 0 < dim) (h1 : target_idx 0 < dim) (h2 : carry_idx 0 < dim) :
    uc_eval (Gate.toUCom dim (gidney_adder_bit_step 0)) * f_to_vec dim f
      = f_to_vec dim
          (update f (carry_idx 0)
            (xor (f (carry_idx 0)) (f (read_idx 0) && f (target_idx 0)))) := by
  -- Unfold to the CCX form (i=0 branch of gidney_adder_bit_step)
  show uc_eval (Gate.toUCom dim
                  (Gate.CCX (read_idx 0) (target_idx 0) (carry_idx 0)))
        * f_to_vec dim f
        = _
  -- Apply the reusable CCX basis-action lemma
  apply gate_ccx_acts_on_basis dim (read_idx 0) (target_idx 0) (carry_idx 0)
        h0 h1 h2
  · -- read_idx 0 = 0, target_idx 0 = 1, so 0 ≠ 1
    decide
  · -- read_idx 0 = 0, carry_idx 0 = 2, so 0 ≠ 2
    decide
  · -- target_idx 0 = 1, carry_idx 0 = 2, so 1 ≠ 2
    decide

/-- T-count of the faithful interior bit-step: still 7 (1 Toffoli +
    3 CXs, with CXs contributing 0 T). Matches qianxu's "q_A Toffoli
    gates per q_A-bit adder" claim. -/
theorem tcount_gidney_adder_bit_step_faithful_interior (i : Nat) :
    tcount (gidney_adder_bit_step_faithful_interior i) = 7 := by
  unfold gidney_adder_bit_step_faithful_interior
  rfl

/-- Gate count of the faithful interior bit-step: **4 gates** (vs the
    simplified encoding's 2). The 2 extra CXs are the propagation
    CXs the Iter 19 encoding was missing. -/
theorem gcount_gidney_adder_bit_step_faithful_interior (i : Nat) :
    gcount (gidney_adder_bit_step_faithful_interior i) = 4 := by
  unfold gidney_adder_bit_step_faithful_interior
  rfl

/-- Concrete: at i=3 (interior bit), the faithful encoding has tcount 7
    and gcount 4. -/
example : tcount (gidney_adder_bit_step_faithful_interior 3) = 7 := by decide

example : gcount (gidney_adder_bit_step_faithful_interior 3) = 4 := by decide

/-- **T-count of the faithful interior cascade is `7n`**, matching the
    paper-claimed q_A Toffolis per q_A-bit adder. Same headline count
    as the Iter 20 simplified cascade — the propagation CXs are
    tcount-zero so they don't change the T-count, only the gate
    count. -/
theorem tcount_gidney_adder_forward_faithful_interior (n : Nat) :
    tcount (gidney_adder_forward_faithful_interior n) = 7 * n := by
  induction n with
  | zero => decide
  | succ n ih =>
    show tcount (Gate.seq (gidney_adder_forward_faithful_interior n)
                          (gidney_adder_bit_step_faithful_interior (n + 1)))
           = 7 * (n + 1)
    simp [tcount, ih, tcount_gidney_adder_bit_step_faithful_interior]
    omega

/-- **Gate count is `4n`** (vs the Iter 20 simplified cascade's `2n`).
    This is the **honest gate-count comparison** between the
    Lean-faithful encoding and qianxu Fig. 4(a). -/
theorem gcount_gidney_adder_forward_faithful_interior (n : Nat) :
    gcount (gidney_adder_forward_faithful_interior n) = 4 * n := by
  induction n with
  | zero => decide
  | succ n ih =>
    show gcount (Gate.seq (gidney_adder_forward_faithful_interior n)
                          (gidney_adder_bit_step_faithful_interior (n + 1)))
           = 4 * (n + 1)
    simp [gcount, ih, gcount_gidney_adder_bit_step_faithful_interior]
    omega

/-- Concrete: at n=33 (RSA-2048 adder block), faithful interior cascade
    has 231 T-gates (33 Toffolis × 7) and 132 total gates (33 × 4). -/
example : tcount (gidney_adder_forward_faithful_interior 33) = 231 := by decide

example : gcount (gidney_adder_forward_faithful_interior 33) = 132 := by decide

/-- The faithful cascade matches the simplified cascade's T-count
    (both 7n) but NOT its gate count (simplified: ~2n; faithful: 4n).
    This formalizes the review narrative: paper's "q_A Toffolis" count
    is preserved by either encoding, but only the faithful encoding
    correctly implements the carry. -/
theorem faithful_and_simplified_tcount_agree (n : Nat) :
    tcount (gidney_adder_forward_faithful_interior n)
      = tcount (gidney_adder_forward n) := by
  rw [tcount_gidney_adder_forward_faithful_interior,
      tcount_gidney_adder_forward]

/-- **Faithful bit-step correctness on classical basis states**
    (Iter 57). For `i ≥ 1` interior bits, the four-gate sequence
    acts on `f_to_vec dim f` to produce the chained-update state
    `gidney_bit_step_faithful_post_state i f`. Proved by three
    applications of the reusable `gate_seq_acts_on_basis` bridge
    + the per-gate primitives `gate_ccx_acts_on_basis` and
    `gate_cx_acts_on_basis`. -/
theorem gidney_adder_bit_step_faithful_interior_correct
    (dim i : Nat) (f : Nat → Bool)
    (hri : read_idx i < dim) (hti : target_idx i < dim)
    (hci : carry_idx i < dim) (hcim1 : carry_idx (i - 1) < dim)
    (hri1 : read_idx (i + 1) < dim) (hti1 : target_idx (i + 1) < dim)
    (h_rt : read_idx i ≠ target_idx i)
    (h_rc : read_idx i ≠ carry_idx i)
    (h_tc : target_idx i ≠ carry_idx i)
    (h_cc : carry_idx (i - 1) ≠ carry_idx i)
    (h_ci_ri1 : carry_idx i ≠ read_idx (i + 1))
    (h_ci_ti1 : carry_idx i ≠ target_idx (i + 1)) :
    uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_interior i))
      * f_to_vec dim f
      = f_to_vec dim (gidney_bit_step_faithful_post_state i f) := by
  unfold gidney_adder_bit_step_faithful_interior
         gidney_bit_step_faithful_post_state
  -- Apply gate_seq three times, threading the intermediate basis-state functions
  apply gate_seq_acts_on_basis dim _ _ f _ _
  · -- Inner three sequences: seq (seq (CCX) (CX_chain)) (CX_prop_a)
    apply gate_seq_acts_on_basis dim _ _ f _ _
    · -- Inner two: seq (CCX) (CX_chain)
      apply gate_seq_acts_on_basis dim _ _ f _ _
      · -- CCX acts: writes (read ∧ target) into carry[i]
        exact gate_ccx_acts_on_basis dim _ _ _ hri hti hci h_rt h_rc h_tc f
      · -- CX (chain): writes carry[i-1] into carry[i]
        exact gate_cx_acts_on_basis dim _ _ hcim1 hci h_cc _
    · -- CX (propagation to read[i+1]): writes carry[i] into read[i+1]
      exact gate_cx_acts_on_basis dim _ _ hci hri1 h_ci_ri1 _
  · -- CX (propagation to target[i+1]): writes carry[i] into target[i+1]
    exact gate_cx_acts_on_basis dim _ _ hci hti1 h_ci_ti1 _

/-- T-count of interior gate-reverse: 7 (matches forward). -/
theorem tcount_gidney_adder_bit_step_faithful_interior_reverse (i : Nat) :
    tcount (gidney_adder_bit_step_faithful_interior_reverse i) = 7 := by
  unfold gidney_adder_bit_step_faithful_interior_reverse
  rfl

/-- Gate-count of interior gate-reverse: 4 (matches forward). -/
theorem gcount_gidney_adder_bit_step_faithful_interior_reverse (i : Nat) :
    gcount (gidney_adder_bit_step_faithful_interior_reverse i) = 4 := by
  unfold gidney_adder_bit_step_faithful_interior_reverse
  rfl

/-- **Interior forward · reverse = identity** at matrix level. The 3
    CXs cancel pairwise (CNOT involution × 3) and the CCX-pair
    cancels. Mirrors Iter 81's first-bit pattern but with one more
    gate (4 gates → 4 involution pairs). -/
theorem gidney_adder_bit_step_faithful_interior_fwd_rev_eq_one
    (dim i : Nat)
    (hri : read_idx i < dim) (hti : target_idx i < dim)
    (hci : carry_idx i < dim) (hcim1 : carry_idx (i - 1) < dim)
    (hri1 : read_idx (i + 1) < dim) (hti1 : target_idx (i + 1) < dim)
    (h_rt : read_idx i ≠ target_idx i)
    (h_rc : read_idx i ≠ carry_idx i)
    (h_tc : target_idx i ≠ carry_idx i)
    (h_cc : carry_idx (i - 1) ≠ carry_idx i)
    (h_ci_ri1 : carry_idx i ≠ read_idx (i + 1))
    (h_ci_ti1 : carry_idx i ≠ target_idx (i + 1)) :
    uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_bit_step_faithful_interior i)
                        (gidney_adder_bit_step_faithful_interior_reverse i)))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  unfold gidney_adder_bit_step_faithful_interior
         gidney_adder_bit_step_faithful_interior_reverse
  -- Abbreviate: C = CCX, X = CX_chain, R = CX_prop_r, T = CX_prop_t.
  -- Forward gates left-to-right (in time): C, X, R, T.
  --   uc_eval(fwd) = T * (R * (X * C))
  -- Reverse: T, R, X, C → uc_eval(rev) = C * (X * (R * T))
  -- Composition: uc_eval(rev) * uc_eval(fwd) = C * X * R * T * T * R * X * C
  -- Collapse T*T, R*R, X*X, C*C (in that order) via Matrix.mul_assoc + CNOT/CCX involution.
  show
    (uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
      * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
        * (uc_eval (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1)))
          * uc_eval (BaseUCom.CNOT (carry_idx i) (target_idx (i + 1))))))
    * (uc_eval (BaseUCom.CNOT (carry_idx i) (target_idx (i + 1)))
      * (uc_eval (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1)))
        * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
          * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i))))) = 1
  -- Step 1: outer Matrix.mul_assoc to expose `(X*(R*T)) * (T*(R*(X*C)))`
  rw [Matrix.mul_assoc
        (uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim))
        (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
          * (uc_eval (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1)))
            * uc_eval (BaseUCom.CNOT (carry_idx i) (target_idx (i + 1)))))
        (uc_eval (BaseUCom.CNOT (carry_idx i) (target_idx (i + 1)))
          * (uc_eval (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1)))
            * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
              * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)))))]
  rw [Matrix.mul_assoc
        (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i) : BaseUCom dim))
        (uc_eval (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1)))
          * uc_eval (BaseUCom.CNOT (carry_idx i) (target_idx (i + 1))))
        (uc_eval (BaseUCom.CNOT (carry_idx i) (target_idx (i + 1)))
          * (uc_eval (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1)))
            * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
              * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)))))]
  rw [Matrix.mul_assoc
        (uc_eval (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1)) : BaseUCom dim))
        (uc_eval (BaseUCom.CNOT (carry_idx i) (target_idx (i + 1))))
        (uc_eval (BaseUCom.CNOT (carry_idx i) (target_idx (i + 1)))
          * (uc_eval (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1)))
            * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
              * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)))))]
  rw [← Matrix.mul_assoc
        (uc_eval (BaseUCom.CNOT (carry_idx i) (target_idx (i + 1)) : BaseUCom dim))
        (uc_eval (BaseUCom.CNOT (carry_idx i) (target_idx (i + 1))))
        (uc_eval (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1)))
          * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
            * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i))))]
  -- Collapse T*T = uc_eval(seq T T) = 1
  show uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
        * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
          * (uc_eval (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1)))
            * (uc_eval (UCom.seq (BaseUCom.CNOT (carry_idx i) (target_idx (i + 1))
                                  : BaseUCom dim)
                                 (BaseUCom.CNOT (carry_idx i) (target_idx (i + 1))))
              * (uc_eval (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1)))
                * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
                  * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i))))))) = 1
  rw [CNOT_CNOT_eq_one dim (carry_idx i) (target_idx (i + 1)) hci hti1 h_ci_ti1]
  rw [Matrix.one_mul]
  -- Goal: C * (X * (R * (R * (X * C)))) = 1
  -- Collapse R*R now
  rw [← Matrix.mul_assoc
        (uc_eval (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1)) : BaseUCom dim))
        (uc_eval (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1))))
        (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
          * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)))]
  show uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
        * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
          * (uc_eval (UCom.seq (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1))
                                : BaseUCom dim)
                               (BaseUCom.CNOT (carry_idx i) (read_idx (i + 1))))
            * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
              * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i))))) = 1
  rw [CNOT_CNOT_eq_one dim (carry_idx i) (read_idx (i + 1)) hci hri1 h_ci_ri1]
  rw [Matrix.one_mul]
  -- Goal: C * (X * (X * C)) = 1
  -- Collapse X*X (chain CX pair)
  rw [← Matrix.mul_assoc
        (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i) : BaseUCom dim))
        (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i)))
        (uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)))]
  show uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
        * (uc_eval (UCom.seq (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i)
                              : BaseUCom dim)
                             (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i)))
          * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i))) = 1
  rw [CNOT_CNOT_eq_one dim (carry_idx (i - 1)) (carry_idx i) hcim1 hci h_cc]
  rw [Matrix.one_mul]
  -- Goal: C * C = 1 (CCX involution)
  show uc_eval (UCom.seq (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)
                          : BaseUCom dim)
                         (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i))) = 1
  exact CCX_CCX_eq_one dim _ _ _ hri hti hci h_rt h_rc h_tc

/-- **Parametric BitDisjointness derivation (Iter 61)**: all 12
    disjointness conditions follow from a single dim-size bound
    `3*i + 5 ≤ dim` (covering the highest qubit index `target_idx
    (i+1) = 3i+4`), plus `1 ≤ i` (so `carry_idx (i-1)` is a distinct
    qubit). Reduces the review interface from 12 manual conditions to
    a single `omega`-style bound, per the new CLAUDE.md hard rule on
    reusable framework + readability. -/
theorem bit_disjointness_of_dim_bound (dim i : Nat)
    (h1 : 1 ≤ i) (hd : 3 * i + 5 ≤ dim) :
    BitDisjointness dim i where
  hri      := by unfold read_idx; omega
  hti      := by unfold target_idx; omega
  hci      := by unfold carry_idx; omega
  hcim1    := by unfold carry_idx; omega
  hri1     := by unfold read_idx; omega
  hti1     := by unfold target_idx; omega
  h_rt     := by unfold read_idx target_idx; omega
  h_rc     := by unfold read_idx carry_idx; omega
  h_tc     := by unfold target_idx carry_idx; omega
  h_cc     := by unfold carry_idx; omega
  h_ci_ri1 := by unfold carry_idx read_idx; omega
  h_ci_ti1 := by unfold carry_idx target_idx; omega

/-- **Cascade-level dim bound** suffices to derive BitDisjointness at
    every i in 1..n: a single `3*n + 5 ≤ dim` assumption covers all
    interior bits. Reduces the cascade-correctness interface to ONE
    quantifier-free hypothesis. -/
theorem bit_disjointness_for_cascade (dim n : Nat) (h : 3 * n + 5 ≤ dim) :
    ∀ i, 1 ≤ i → i ≤ n → BitDisjointness dim i := by
  intro i h1 hni
  apply bit_disjointness_of_dim_bound dim i h1
  -- 3*i + 5 ≤ 3*n + 5 ≤ dim
  have : 3 * i + 5 ≤ 3 * n + 5 := by omega
  omega

/-- Concrete: at RSA-2048 (q_A = 33), dim ≥ 3·33 + 5 = 104 suffices.
    Note that `adder_n_qubits 33 = 3·33 + 2 = 101`; the +3 over
    adder_n_qubits comes from the "next bit" propagation indices
    used by the interior bit-step. -/
example : 3 * 33 + 5 ≤ 104 := by decide

end FormalRV.BQAlgo
