import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Corpus.PaperClaims
import FormalRV.PPM.GidneyAND
import Mathlib.Tactic.IntervalCases
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderDefinitions

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-- Smoke: 4-bit adder uses 14 qubits (matches Fig. 4(a)). -/
example : adder_n_qubits 4 = 14 := by decide

/-- Smoke: indexing is monotone within a bit position. -/
example : read_idx 0 = 0 ∧ target_idx 0 = 1 ∧ carry_idx 0 = 2 := by
  decide

/-- Smoke: indexing is monotone across bit positions. -/
example : read_idx 1 = 3 ∧ target_idx 1 = 4 ∧ carry_idx 1 = 5 := by
  decide

/-- T-count of one stub unit = 7 (single CCX inside MAJ). -/
theorem tcount_ripple_carry_unit_stub (i : Nat) :
    tcount (ripple_carry_unit_stub i) = 7 := by
  simp [ripple_carry_unit_stub, MAJ_meets_paper_claim, paper_claim_MAJ_tcount]

/-- Each Gidney-adder forward step is exactly 1 Toffoli = 7 T-gates.
    Proof: CCX contributes 7 T; CX (if present) contributes 0. -/
theorem tcount_gidney_adder_bit_step (i : Nat) :
    tcount (gidney_adder_bit_step i) = 7 := by
  unfold gidney_adder_bit_step
  split <;> rfl

/-- Concrete smoke checks: tcount per step is 7 for any specific i. -/
example : tcount (gidney_adder_bit_step 0) = 7 := by decide

example : tcount (gidney_adder_bit_step 5) = 7 := tcount_gidney_adder_bit_step 5

example : tcount (gidney_adder_bit_step 100) = 7 := tcount_gidney_adder_bit_step 100

/-- Gate-count of one bit step is exactly 1 Toffoli — derived
    from the inner gate sequence. The +1 from any CX (i>0 case)
    is also counted in gcount (each CX = 1 gate). -/
theorem gcount_gidney_adder_bit_step (i : Nat) :
    gcount (gidney_adder_bit_step i) = if i = 0 then 1 else 2 := by
  unfold gidney_adder_bit_step
  split <;> rfl

/-- T-count of the full n-bit Gidney forward cascade: 7n (1 Toffoli ×
    7 T per bit × n bits). **First gate-derived recovery of qianxu
    Eq. E3's "q_A Toffoli gates" for the q_A-bit adder** — the
    adder-side analog of `tcount_prefix_and_cascade` for the lookup. -/
theorem tcount_gidney_adder_forward (n : Nat) :
    tcount (gidney_adder_forward n) = 7 * n := by
  induction n with
  | zero => decide
  | succ n ih =>
    show tcount (Gate.seq (gidney_adder_forward n) (gidney_adder_bit_step n))
           = 7 * (n + 1)
    simp [tcount, ih, tcount_gidney_adder_bit_step]
    omega

/-- Concrete: 4-bit Gidney forward cascade has 28 T-gates = 4 Toffolis. -/
example : tcount (gidney_adder_forward 4) = 28 := by decide

/-- A 33-bit Gidney forward cascade (qianxu's RSA-2048 adder block, q_A=33,
    Eq. E3) has 33 Toffolis = 231 T-gates. -/
example : tcount (gidney_adder_forward 33) = 7 * 33 :=
  tcount_gidney_adder_forward 33

/-- T-count of the reverse pass: also `7n` (same Toffolis, different order). -/
theorem tcount_gidney_adder_uncompute (n : Nat) :
    tcount (gidney_adder_uncompute n) = 7 * n := by
  induction n with
  | zero => decide
  | succ n ih =>
    show tcount (Gate.seq (gidney_adder_bit_step n) (gidney_adder_uncompute n))
           = 7 * (n + 1)
    simp [tcount, ih, tcount_gidney_adder_bit_step]
    omega

/-- The final CX cascade is tcount-zero (only CXs, no Toffolis). -/
theorem tcount_gidney_final_cx_cascade (n : Nat) :
    tcount (gidney_final_cx_cascade n) = 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    show tcount (Gate.seq (gidney_final_cx_cascade n)
                          (Gate.CX (read_idx n) (target_idx n))) = 0
    simp [tcount, ih]

/-- **Total T-count of the full n-bit Gidney adder (no-measurement
    upper bound): `14 n`**. Composition: forward (7n) + reverse (7n) +
    final CX (0). Under measurement-based uncomputation, the reverse
    contributes 0 — that's the optimization qianxu's "q_A Toffoli gates"
    claim relies on. The 14n here is the gate-level no-optimization
    bound; the 7n claim requires the measurement trick. -/
theorem tcount_gidney_adder_full (n : Nat) :
    tcount (gidney_adder_full n) = 14 * n := by
  unfold gidney_adder_full
  simp [tcount, tcount_gidney_adder_forward, tcount_gidney_adder_uncompute,
        tcount_gidney_final_cx_cascade]
  omega

/-- Concrete: 4-bit full Gidney adder = 56 T (= 8 Toffolis × 7T). -/
example : tcount (gidney_adder_full 4) = 56 := by decide

/-! ## Bridge to PaperClaims (Iter 22, 2026-05-12)

    `gidney_total_toffolis_n_bit_adder n := n` in PaperClaims was a
    paper-stated number (qianxu p. 22 "q_A Toffoli gates"). The
    forward-cascade T-count theorem above now lets us **derive it from
    the gate sequence**: each Toffoli contributes 7 T-gates, so
    `tcount (gidney_adder_forward n) = 7 · n` implies the Toffoli count
    is exactly `n`. Below makes this connection formal. -/

/-- **Bridge theorem**: the T-count of the Lean-encoded Gidney forward
    cascade equals `7 ·` the paper-claim Toffoli count. This connects
    the gate-derived value in `RippleCarryAdder.lean` to the data def
    in `PaperClaims.lean`, formally certifying that the latter is no
    longer paper-stated but Lean-gate-sequence-derived. -/
theorem gidney_adder_forward_tcount_matches_PaperClaims (n : Nat) :
    tcount (gidney_adder_forward n) = 7 * gidney_total_toffolis_n_bit_adder n := by
  rw [tcount_gidney_adder_forward]
  unfold gidney_total_toffolis_n_bit_adder gidney_adder_toffolis_per_bit_qrisp
  omega

/-- Concrete bridge check at n=33 (RSA-2048 q_A=33 case): 33 Toffolis =
    231 T-gates, both sides agree. -/
example :
    tcount (gidney_adder_forward 33) = 7 * gidney_total_toffolis_n_bit_adder 33 :=
  gidney_adder_forward_tcount_matches_PaperClaims 33

/-! ## Review finding: no-measurement vs measurement gap (Iter 25)

    **Structural review finding**: qianxu Eq. E3 claims `q_A Toffoli
    gates per q_A-bit adder` (T-count = 7 q_A). Our gate-faithful
    Lean encoding `gidney_adder_full n` produces **14 n T-gates** —
    a factor of 2 more.

    The factor-of-2 gap is **the Gidney measurement-based AND-
    uncomputation trick** (Gidney 2018, arXiv:1709.06648), which
    qianxu cites but does not formalize. Under this trick:
    - Forward Gidney-AND: 1 Toffoli (~4 T after T-decomposition,
      or 7 T under textbook 7-T decomposition we use).
    - Reverse Gidney-AND: **0 Toffolis** — measurement + CX + classical
      conditional gives the inverse for free.

    Our `gidney_adder_full` includes the explicit reverse cascade
    (uncomputation as a Toffoli), so its `tcount` is 14n. The paper's
    7n claim implicitly requires the measurement-based optimization,
    which we have NOT yet formalized in Lean (that lives in the QEC
    layer, Phase B of CLAUDE.md roadmap).

    **This means**: the 7n claim is **load-bearing on an unformalized
    optimization**. The Lean review certifies the 14n upper bound, NOT
    the 7n paper claim. The gap is reproducible (constant factor of 2)
    and structural (not arithmetic error). -/

/-- **Review finding theorem**: the no-measurement gate-level T-count of
    the n-bit Gidney adder is exactly `2 ·` the paper's measurement-
    based claim. This is the formal statement of the structural
    Gidney-optimization assumption. -/
theorem gidney_no_measurement_vs_measurement_gap (n : Nat) :
    tcount (gidney_adder_full n)
      = 2 * (7 * gidney_total_toffolis_n_bit_adder n) := by
  rw [tcount_gidney_adder_full]
  unfold gidney_total_toffolis_n_bit_adder gidney_adder_toffolis_per_bit_qrisp
  omega

/-- Concrete: at n=33 (RSA-2048 adder block), no-measurement bound is
    14 × 33 = 462 T-gates, vs paper's 7 × 33 = 231 T-gates. -/
example :
    tcount (gidney_adder_full 33) = 462
    ∧ 7 * gidney_total_toffolis_n_bit_adder 33 = 231 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **Review-gap closure theorem**: the n-bit Gidney adder T-count
    with measurement-based uncomputation equals `7n`, matching qianxu
    Eq. E3's claim. This is the formal derivation of the previously
    paper-stated count from the Lean-encoded Gidney-AND primitive. -/
theorem gidney_adder_full_with_measurement_uncompute_tcount_eq (n : Nat) :
    gidney_adder_full_with_measurement_uncompute_tcount n = 7 * n := by
  unfold gidney_adder_full_with_measurement_uncompute_tcount
         gidney_adder_bit_with_measurement_uncompute_tcount
  rfl

/-- **The review-gap factor of 2** is now explicit: the gate-explicit
    14n bound (`tcount_gidney_adder_full n`) is exactly `2 ×` the
    measurement-uncomputation 7n bound. Both are formally derived in
    Lean; the difference is the Gidney trick. -/
theorem gidney_full_vs_measurement_uncompute_factor (n : Nat) :
    tcount (gidney_adder_full n)
      = 2 * gidney_adder_full_with_measurement_uncompute_tcount n := by
  rw [tcount_gidney_adder_full,
      gidney_adder_full_with_measurement_uncompute_tcount_eq]
  omega

/-- Concrete RSA-2048 (q_A=33): with Gidney measurement trick,
    T-count = 231 (paper figure); without, 462 (Lean explicit-reverse). -/
example :
    gidney_adder_full_with_measurement_uncompute_tcount 33 = 231
    ∧ tcount (gidney_adder_full 33) = 462 := by
  refine ⟨?_, ?_⟩ <;> decide

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

/-- T-count of the last-bit step: 7 (1 Toffoli; CX is tcount-0). -/
theorem tcount_gidney_adder_bit_step_faithful_last (i : Nat) :
    tcount (gidney_adder_bit_step_faithful_last i) = 7 := by
  unfold gidney_adder_bit_step_faithful_last
  rfl

/-- Gate count of the last-bit step: **2** (vs interior's 4, first-
    bit's 3). The last bit drops both propagation CXs. -/
theorem gcount_gidney_adder_bit_step_faithful_last (i : Nat) :
    gcount (gidney_adder_bit_step_faithful_last i) = 2 := by
  unfold gidney_adder_bit_step_faithful_last
  rfl

/-- **Last-bit correctness on classical basis states** (Iter 67). -/
theorem gidney_adder_bit_step_faithful_last_correct
    (dim i : Nat) (f : Nat → Bool)
    (hri : read_idx i < dim) (hti : target_idx i < dim)
    (hci : carry_idx i < dim) (hcim1 : carry_idx (i - 1) < dim)
    (h_rt : read_idx i ≠ target_idx i)
    (h_rc : read_idx i ≠ carry_idx i)
    (h_tc : target_idx i ≠ carry_idx i)
    (h_cc : carry_idx (i - 1) ≠ carry_idx i) :
    uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_last i))
      * f_to_vec dim f
      = f_to_vec dim (gidney_last_bit_post_state i f) := by
  unfold gidney_adder_bit_step_faithful_last gidney_last_bit_post_state
  apply gate_seq_acts_on_basis dim _ _ f _ _
  · -- CCX: write (read ∧ target) into carry[i]
    exact gate_ccx_acts_on_basis dim _ _ _ hri hti hci h_rt h_rc h_tc f
  · -- CX (chain): write carry[i-1] into carry[i]
    exact gate_cx_acts_on_basis dim _ _ hcim1 hci h_cc _

/- Three-tier adder summary (regular comment, not docstring): per
   CLAUDE.md hard rules, the adder side now has Verified-tier
   coverage at all three boundary cases:
   - i = 0 (first bit): 3 gates (CCX + 2 propagation CXs), tcount=7,
     gcount=3. Iter 65 correctness.
   - i ≥ 1, not last (interior): 4 gates (CCX + chain + 2 prop),
     tcount=7, gcount=4. Iter 55-57 correctness.
   - i = last interior: 2 gates (CCX + chain), tcount=7, gcount=2.
     Iter 67 correctness (above).
   All three preserve the per-Toffoli figure (1 CCX = 7 T) but have
   different gate counts. The review's per-bit Toffoli count of q_A
   holds across all bit positions. -/

/-- **Forward · reverse (last-bit) = identity on basis states**.
    The two CX gates cancel (CX involution); the two CCX gates
    cancel (CCX involution). Composed correctly via the reusable
    framework. -/
theorem gidney_adder_bit_step_faithful_last_fwd_rev_id
    (dim i : Nat) (f : Nat → Bool)
    (hri : read_idx i < dim) (hti : target_idx i < dim)
    (hci : carry_idx i < dim) (hcim1 : carry_idx (i - 1) < dim)
    (h_rt : read_idx i ≠ target_idx i)
    (h_rc : read_idx i ≠ carry_idx i)
    (h_tc : target_idx i ≠ carry_idx i)
    (h_cc : carry_idx (i - 1) ≠ carry_idx i) :
    uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_bit_step_faithful_last i)
                        (gidney_adder_bit_step_faithful_last_reverse i)))
      * f_to_vec dim f
      = f_to_vec dim f := by
  -- The composition is (CCX; CX); (CX; CCX). uc_eval is right-to-
  -- left mul on seq, so the full matrix is uc_eval CCX * uc_eval CX
  -- * uc_eval CX * uc_eval CCX. Inner CX-pair = 1 (CNOT_CNOT_eq_one);
  -- outer CCX-pair = 1 (CCX_CCX_eq_one). Final matrix is 1; applied
  -- to f_to_vec gives f_to_vec.
  unfold gidney_adder_bit_step_faithful_last
         gidney_adder_bit_step_faithful_last_reverse
  -- Step 1: prove the composed matrix equals 1 (independent of v)
  have hM : uc_eval (Gate.toUCom dim
        (Gate.seq (Gate.seq
                    (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))
                    (Gate.CX (carry_idx (i - 1)) (carry_idx i)))
                  (Gate.seq
                    (Gate.CX (carry_idx (i - 1)) (carry_idx i))
                    (Gate.CCX (read_idx i) (target_idx i) (carry_idx i)))))
        = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
    -- Step a: collapse Gate.toUCom + uc_eval semantics. The outer seq
    -- evaluates as `uc_eval rev * uc_eval fwd`, etc.
    show (uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
          * uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i)))
          * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
             * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i))) = 1
    -- Step b: reassociate and use the seq-form involution lemmas
    -- (which are uc_eval (seq CNOT CNOT) = 1, etc., where uc_eval seq
    -- unfolds to right * left mul)
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (uc_eval (BaseUCom.CNOT _ _))
                            (uc_eval (BaseUCom.CNOT _ _))
                            (uc_eval (BaseUCom.CCX _ _ _))]
    -- `uc_eval CNOT * uc_eval CNOT` IS `uc_eval (seq CNOT CNOT)` by
    -- defeq; use `show` to align with CNOT_CNOT_eq_one's statement
    show uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
         * (uc_eval (UCom.seq (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
                              (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i)))
            * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)))
         = 1
    rw [CNOT_CNOT_eq_one dim (carry_idx (i - 1)) (carry_idx i) hcim1 hci h_cc]
    rw [Matrix.one_mul]
    -- Now: uc_eval CCX * uc_eval CCX = 1, again use seq form via show
    show uc_eval (UCom.seq (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
                           (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)))
         = 1
    exact CCX_CCX_eq_one dim _ _ _ hri hti hci h_rt h_rc h_tc
  -- Step 2: apply matrix · v = v when matrix = 1
  rw [hM, Matrix.one_mul]

/-- **Faithful n-bit cascade correctness**: given disjointness on each
    bit position 1..n, the cascade acts on `f_to_vec dim f` to produce
    `f_to_vec dim (gidney_cascade_post_state n f)`. Proof by induction
    on n. **First Verified-tier theorem for the n-bit Gidney
    adder forward cascade.** -/
theorem gidney_adder_forward_faithful_interior_correct
    (dim : Nat) (hdim : 0 < dim) (f : Nat → Bool) :
    ∀ n, (∀ i, 1 ≤ i → i ≤ n → BitDisjointness dim i) →
    uc_eval (Gate.toUCom dim (gidney_adder_forward_faithful_interior n))
      * f_to_vec dim f
      = f_to_vec dim (gidney_cascade_post_state n f)
  | 0    , _ => by
      show uc_eval (Gate.toUCom dim Gate.I) * f_to_vec dim f = f_to_vec dim f
      rw [Gate.toUCom_I]
      show uc_eval (BaseUCom.ID 0 : BaseUCom dim) * f_to_vec dim f
            = f_to_vec dim f
      rw [uc_eval_ID_eq_one hdim, Matrix.one_mul]
  | n + 1, hyp => by
      show uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_forward_faithful_interior n)
                        (gidney_adder_bit_step_faithful_interior (n + 1))))
            * f_to_vec dim f
            = f_to_vec dim (gidney_cascade_post_state (n + 1) f)
      apply gate_seq_acts_on_basis dim _ _ f (gidney_cascade_post_state n f) _
      · -- IH: cascade of n bits is correct
        exact gidney_adder_forward_faithful_interior_correct dim hdim f n
                (fun i h1 hn => hyp i h1 (Nat.le_succ_of_le hn))
      · -- Per-bit correctness at i = n+1, applied to the post-cascade state
        have d := hyp (n + 1) (Nat.le_add_left 1 n) (Nat.le_refl _)
        exact gidney_adder_bit_step_faithful_interior_correct
                dim (n + 1) _
                d.hri d.hti d.hci d.hcim1 d.hri1 d.hti1
                d.h_rt d.h_rc d.h_tc d.h_cc d.h_ci_ri1 d.h_ci_ti1

/-- Action of the simplified `gidney_adder_bit_step (i+1)` on basis
    states: XORs `(read[i+1] ∧ target[i+1]) ⊕ carry[i]` into `carry[i+1]`.
    **This is NOT Gidney's actual carry** (see review-gap note above);
    proving it here makes the discrepancy explicit. -/
theorem gidney_adder_bit_step_succ_simplified (dim i : Nat) (f : Nat → Bool)
    (hri : read_idx (i+1) < dim) (hti : target_idx (i+1) < dim)
    (hci : carry_idx (i+1) < dim) (hci' : carry_idx i < dim)
    (hrt : read_idx (i+1) ≠ target_idx (i+1))
    (hrc : read_idx (i+1) ≠ carry_idx (i+1))
    (htc : target_idx (i+1) ≠ carry_idx (i+1))
    (hcc : carry_idx i ≠ carry_idx (i+1)) :
    let f' := update f (carry_idx (i+1))
                (xor (f (carry_idx (i+1)))
                     (f (read_idx (i+1)) && f (target_idx (i+1))))
    uc_eval (Gate.toUCom dim (gidney_adder_bit_step (i+1))) * f_to_vec dim f
      = f_to_vec dim
          (update f' (carry_idx (i+1))
            (xor (f' (carry_idx (i+1))) (f' (carry_idx i)))) := by
  intro f'
  -- gidney_adder_bit_step (i+1) ↦ Gate.seq (CCX ...) (CX carry[i] carry[i+1])
  show uc_eval (Gate.toUCom dim
          (Gate.seq (Gate.CCX (read_idx (i+1)) (target_idx (i+1))
                              (carry_idx (i+1)))
                    (Gate.CX (carry_idx i) (carry_idx (i+1)))))
        * f_to_vec dim f = _
  apply gate_seq_acts_on_basis dim _ _ f f' _
  · -- First gate (CCX) acts: XOR (read ∧ target) into carry
    exact gate_ccx_acts_on_basis dim _ _ _ hri hti hci hrt hrc htc f
  · -- Second gate (CX) acts on the post-CCX state f': XOR f'(carry[i]) into f'(carry[i+1])
    exact gate_cx_acts_on_basis dim (carry_idx i) (carry_idx (i+1))
            hci' hci hcc f'

/-- T-count of the gate-reverse: same 7 as forward (same gates, swapped order). -/
theorem tcount_gidney_adder_bit_step_reverse (i : Nat) :
    tcount (gidney_adder_bit_step_reverse i) = 7 := by
  unfold gidney_adder_bit_step_reverse
  split <;> rfl

/-- Gate-count of the gate-reverse: 1 at i=0, 2 at i>0 (matches forward). -/
theorem gcount_gidney_adder_bit_step_reverse (i : Nat) :
    gcount (gidney_adder_bit_step_reverse i) = (if i = 0 then 1 else 2) := by
  unfold gidney_adder_bit_step_reverse
  split <;> rfl

/-- **Matrix-level per-bit involution**: `bit_step i · bit_step_reverse i = 1`.
    Proven for all `i` (both branches) under the standard bit-disjointness
    hypotheses. The i = 0 branch needs `read_idx 0 = 0, target_idx 0 = 1,
    carry_idx 0 = 2` (auto-derived from the `read_idx`/`target_idx`/`carry_idx`
    defs and the disjointness hypotheses); the i > 0 branch mirrors
    `gidney_adder_bit_step_faithful_last_fwd_rev_id` (Iter 69) structurally.

    **This is the per-bit collapse used in Iter 74's cascade induction**:
    `uc_eval (cascade (n+1) · uncompute (n+1))` re-associates to
    `uc_eval (cascade n) · uc_eval (bit_step n · bit_step_reverse n)
     · uc_eval (uncompute n)`, and the middle factor collapses to 1
    by this lemma. -/
theorem gidney_adder_bit_step_fwd_rev_eq_one (dim i : Nat)
    (hri : read_idx i < dim) (hti : target_idx i < dim)
    (hci : carry_idx i < dim)
    (h_rt : read_idx i ≠ target_idx i)
    (h_rc : read_idx i ≠ carry_idx i)
    (h_tc : target_idx i ≠ carry_idx i)
    (hcim1 : i ≠ 0 → carry_idx (i - 1) < dim)
    (h_cc : i ≠ 0 → carry_idx (i - 1) ≠ carry_idx i) :
    uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_bit_step i)
                        (gidney_adder_bit_step_reverse i)))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  by_cases hi0 : i = 0
  · -- i = 0: both reduce to the same single CCX; hcim1/h_cc not needed
    subst hi0
    have e1 : gidney_adder_bit_step 0
            = Gate.CCX (read_idx 0) (target_idx 0) (carry_idx 0) := by
      unfold gidney_adder_bit_step; rfl
    have e2 : gidney_adder_bit_step_reverse 0
            = Gate.CCX (read_idx 0) (target_idx 0) (carry_idx 0) := by
      unfold gidney_adder_bit_step_reverse; rfl
    rw [e1, e2, Gate.toUCom_seq, Gate.toUCom_CCX]
    show uc_eval (UCom.seq (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0)
                            : BaseUCom dim)
                           (BaseUCom.CCX (read_idx 0) (target_idx 0) (carry_idx 0))) = 1
    exact CCX_CCX_eq_one dim _ _ _ hri hti hci h_rt h_rc h_tc
  · -- i ≠ 0: (CCX·CX) · (CX·CCX) collapses via CNOT involution then CCX involution
    have hcim1' := hcim1 hi0
    have h_cc' := h_cc hi0
    have e1 : gidney_adder_bit_step i =
        Gate.seq (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))
                 (Gate.CX (carry_idx (i - 1)) (carry_idx i)) := by
      unfold gidney_adder_bit_step; rw [if_neg hi0]
    have e2 : gidney_adder_bit_step_reverse i =
        Gate.seq (Gate.CX (carry_idx (i - 1)) (carry_idx i))
                 (Gate.CCX (read_idx i) (target_idx i) (carry_idx i)) := by
      unfold gidney_adder_bit_step_reverse; rw [if_neg hi0]
    rw [e1, e2]
    -- Mirror Iter 69's proof structure (lines 908-945)
    show (uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
          * uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i)))
          * (uc_eval (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
             * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i))) = 1
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (uc_eval (BaseUCom.CNOT _ _))
                            (uc_eval (BaseUCom.CNOT _ _))
                            (uc_eval (BaseUCom.CCX _ _ _))]
    show uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i) : BaseUCom dim)
         * (uc_eval (UCom.seq (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i))
                              (BaseUCom.CNOT (carry_idx (i - 1)) (carry_idx i)))
            * uc_eval (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)))
         = 1
    rw [CNOT_CNOT_eq_one dim (carry_idx (i - 1)) (carry_idx i) hcim1' hci h_cc']
    rw [Matrix.one_mul]
    show uc_eval (UCom.seq (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i)
                            : BaseUCom dim)
                           (BaseUCom.CCX (read_idx i) (target_idx i) (carry_idx i))) = 1
    exact CCX_CCX_eq_one dim _ _ _ hri hti hci h_rt h_rc h_tc

/-- T-count of the proper reverse: 7n (same gates, reversed). -/
theorem tcount_gidney_adder_uncompute_proper (n : Nat) :
    tcount (gidney_adder_uncompute_proper n) = 7 * n := by
  induction n with
  | zero => decide
  | succ n ih =>
    show tcount (Gate.seq (gidney_adder_bit_step_reverse n)
                          (gidney_adder_uncompute_proper n))
           = 7 * (n + 1)
    simp [tcount, ih, tcount_gidney_adder_bit_step_reverse]
    omega

/-- **Matrix-level forward · proper-uncompute = identity**. The
    n-bit Gidney forward cascade composed with its proper
    (gate-reversed) uncomputation is the identity matrix. Proof
    by structural recursion on n, mirroring Iter 74's
    `prefix_and_cascade_uncompute_eq_one`.

    **Hypothesis**: a single `3 * n ≤ dim` bound suffices (the
    highest qubit touched at bit position k is `carry_idx k = 3k+2`,
    so all bits 0..n-1 fit when `3n ≤ dim`).

    **Fourth Verified-tier review chain** (adder side, mirror of
    Iter 74). Confirms that the simplified-bit-step forward cascade
    IS reversible by its proper inverse without measurement. -/
theorem gidney_adder_forward_uncompute_proper_eq_one
    (dim : Nat) (hdim : 0 < dim) :
    ∀ n, 3 * n ≤ dim →
    uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_forward n)
                        (gidney_adder_uncompute_proper n)))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ)
  | 0    , _ => by
      -- forward 0 = uncompute_proper 0 = Gate.I. uc_eval(seq I I) = 1·1 = 1.
      show uc_eval (Gate.toUCom dim (Gate.I : Gate)) *
             uc_eval (Gate.toUCom dim (Gate.I : Gate)) = 1
      rw [Gate.toUCom_I, uc_eval_ID_eq_one hdim, Matrix.one_mul]
  | n + 1, hbnd => by
      have ih : uc_eval (Gate.toUCom dim
                  (Gate.seq (gidney_adder_forward n)
                            (gidney_adder_uncompute_proper n))) = 1 := by
        apply gidney_adder_forward_uncompute_proper_eq_one dim hdim n
        omega
      -- Derive disjointness for bit position n from the cascade-dim bound.
      have hri  : read_idx n < dim := by unfold read_idx; omega
      have hti  : target_idx n < dim := by unfold target_idx; omega
      have hci  : carry_idx n < dim := by unfold carry_idx; omega
      have h_rt : read_idx n ≠ target_idx n := by
        unfold read_idx target_idx; omega
      have h_rc : read_idx n ≠ carry_idx n := by
        unfold read_idx carry_idx; omega
      have h_tc : target_idx n ≠ carry_idx n := by
        unfold target_idx carry_idx; omega
      have hcim1 : n ≠ 0 → carry_idx (n - 1) < dim := fun _ => by
        unfold carry_idx; omega
      have h_cc : n ≠ 0 → carry_idx (n - 1) ≠ carry_idx n := fun hne => by
        unfold carry_idx
        -- n ≠ 0 implies n ≥ 1, so 3*(n-1) + 2 = 3n - 1 ≠ 3n + 2
        have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hne
        omega
      have hstep := gidney_adder_bit_step_fwd_rev_eq_one dim n
                     hri hti hci h_rt h_rc h_tc hcim1 h_cc
      -- After pattern-match, the goal WHNF-reduces to the 4-factor form
      show (uc_eval (Gate.toUCom dim (gidney_adder_uncompute_proper n))
              * uc_eval (Gate.toUCom dim (gidney_adder_bit_step_reverse n)))
            * (uc_eval (Gate.toUCom dim (gidney_adder_bit_step n))
              * uc_eval (Gate.toUCom dim (gidney_adder_forward n))) = 1
      rw [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc
            (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_reverse n)))
            (uc_eval (Gate.toUCom dim (gidney_adder_bit_step n)))
            (uc_eval (Gate.toUCom dim (gidney_adder_forward n)))]
      -- Middle pair = uc_eval (toUCom (seq bit_step bit_step_reverse)) by defeq
      show uc_eval (Gate.toUCom dim (gidney_adder_uncompute_proper n)) *
            (uc_eval (Gate.toUCom dim
                       (Gate.seq (gidney_adder_bit_step n)
                                 (gidney_adder_bit_step_reverse n)))
              * uc_eval (Gate.toUCom dim (gidney_adder_forward n))) = 1
      rw [hstep, Matrix.one_mul]
      exact ih

/-- T-count of the propagation cascade: `7n` (each bit contributes
    1 Toffoli). -/
theorem tcount_gidney_adder_forward_with_propagation : ∀ n,
    tcount (gidney_adder_forward_with_propagation n) = 7 * n
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      show tcount (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                            (gidney_adder_bit_step_faithful_interior (n + 1)))
            = 7 * (n + 2)
      simp [tcount, tcount_gidney_adder_forward_with_propagation (n + 1),
            tcount_gidney_adder_bit_step_faithful_interior]
      omega

/-- Gate-count of the propagation cascade. Bit 0 contributes 3
    gates (1 CCX + 2 propagation CXs); each interior bit
    contributes 4 (1 CCX + 1 chain CX + 2 propagation CXs).
    Total: `3 + 4·(n-1) = 4n - 1` for `n ≥ 1`.

    Edge cases: `n=0` gives 0 gates; for n ≥ 1 the formula
    `4n - 1` holds. We state it as `4n + (if n = 0 then 0 else -1)`
    to handle both cleanly — but Nat doesn't support negative,
    so we split into two clauses. -/
theorem gcount_gidney_adder_forward_with_propagation : ∀ n,
    gcount (gidney_adder_forward_with_propagation n)
      = if n = 0 then 0 else 4 * n - 1
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      show gcount (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                            (gidney_adder_bit_step_faithful_interior (n + 1)))
            = if (n + 2) = 0 then 0 else 4 * (n + 2) - 1
      rw [if_neg (Nat.succ_ne_zero (n + 1))]
      have ih := gcount_gidney_adder_forward_with_propagation (n + 1)
      rw [if_neg (Nat.succ_ne_zero n)] at ih
      show gcount (gidney_adder_forward_with_propagation (n + 1))
            + gcount (gidney_adder_bit_step_faithful_interior (n + 1))
            = 4 * (n + 2) - 1
      rw [ih, gcount_gidney_adder_bit_step_faithful_interior]
      omega

/-- T-count of the faithful full forward cascade: `7n` for `n ≥ 2`.
    Matches qianxu Eq. E3's `q_A` Toffolis per adder (T-count =
    7 · q_A). -/
theorem tcount_gidney_adder_forward_faithful_full (n : Nat) :
    tcount (gidney_adder_forward_faithful_full (n + 2)) = 7 * (n + 2) := by
  show tcount (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                        (gidney_adder_bit_step_faithful_last (n + 1)))
        = 7 * (n + 2)
  simp [tcount, tcount_gidney_adder_forward_with_propagation,
        tcount_gidney_adder_bit_step_faithful_last]
  omega

/-- Gate-count of the faithful full forward cascade: `4n - 3` for
    `n ≥ 2`. Decomposes as 3 (first) + 4·(n-2) (interiors) + 2
    (last) = 4n - 3. -/
theorem gcount_gidney_adder_forward_faithful_full (n : Nat) :
    gcount (gidney_adder_forward_faithful_full (n + 2)) = 4 * (n + 2) - 3 := by
  show gcount (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                        (gidney_adder_bit_step_faithful_last (n + 1)))
        = 4 * (n + 2) - 3
  have hp := gcount_gidney_adder_forward_with_propagation (n + 1)
  rw [if_neg (Nat.succ_ne_zero n)] at hp
  show gcount (gidney_adder_forward_with_propagation (n + 1))
        + gcount (gidney_adder_bit_step_faithful_last (n + 1))
        = 4 * (n + 2) - 3
  rw [hp, gcount_gidney_adder_bit_step_faithful_last]
  omega

/-- Concrete: 4-bit faithful Gidney adder = 28 T-gates = 4 Toffolis.
    (Matches `qq_gidney_adder.py` for a 4-bit instance.) -/
example : tcount (gidney_adder_forward_faithful_full 4) = 28 :=
  tcount_gidney_adder_forward_faithful_full 2

/-- Concrete: 33-bit faithful Gidney adder (RSA-2048 q_A=33 block) =
    231 T-gates = 33 Toffolis. -/
example : tcount (gidney_adder_forward_faithful_full 33) = 7 * 33 :=
  tcount_gidney_adder_forward_faithful_full 31

/-- **Propagation cascade correctness**: given a single dim-bound
    `3 * n + 2 ≤ dim` (covering all qubits up through bit position
    n-1's propagation to bit n), the cascade acts on `f_to_vec dim f`
    to produce `f_to_vec dim (gidney_propagation_post_state n f)`.

    Proof by structural recursion on the three-clause def:
    - n=0: Gate.I, trivially preserves.
    - n=1: apply `gidney_adder_bit_step_faithful_first_correct` with
      first-bit disjointness derived from dim ≥ 5.
    - n+2: `gate_seq_acts_on_basis` + IH (propagation n+1) +
      per-bit interior correctness at position n+1 (via
      `bit_disjointness_of_dim_bound`). -/
theorem gidney_adder_forward_with_propagation_correct
    (dim : Nat) (hdim : 0 < dim) (f : Nat → Bool) :
    ∀ n, 3 * n + 2 ≤ dim →
    uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation n))
      * f_to_vec dim f
      = f_to_vec dim (gidney_propagation_post_state n f)
  | 0    , _ => by
      show uc_eval (Gate.toUCom dim (Gate.I : Gate)) * f_to_vec dim f = f_to_vec dim f
      rw [Gate.toUCom_I, uc_eval_ID_eq_one hdim, Matrix.one_mul]
  | 1    , hbd => by
      -- propagation 1 = first; apply first-bit correctness
      show uc_eval (Gate.toUCom dim gidney_adder_bit_step_faithful_first)
            * f_to_vec dim f = f_to_vec dim (gidney_first_bit_post_state f)
      have fb := first_bit_disjointness_of_dim_bound dim (by omega : 5 ≤ dim)
      obtain ⟨hr0, ht0, hc0, hr1, ht1, h_rt0, h_rc0, h_tc0, h_c_r1, h_c_t1⟩ := fb
      exact gidney_adder_bit_step_faithful_first_correct dim f
              hr0 ht0 hc0 hr1 ht1 h_rt0 h_rc0 h_tc0 h_c_r1 h_c_t1
  | n + 2, hbd => by
      show uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                        (gidney_adder_bit_step_faithful_interior (n + 1))))
            * f_to_vec dim f
            = f_to_vec dim (gidney_propagation_post_state (n + 2) f)
      apply gate_seq_acts_on_basis dim _ _ f
              (gidney_propagation_post_state (n + 1) f) _
      · exact gidney_adder_forward_with_propagation_correct dim hdim f (n + 1)
                (by omega)
      · have d := bit_disjointness_of_dim_bound dim (n + 1)
                    (by omega) (by omega)
        exact gidney_adder_bit_step_faithful_interior_correct
                dim (n + 1) _
                d.hri d.hti d.hci d.hcim1 d.hri1 d.hti1
                d.h_rt d.h_rc d.h_tc d.h_cc d.h_ci_ri1 d.h_ci_ti1

/-- **Faithful full forward cascade correctness** (Phase A review
    anchor at the basis-state level): on `(n+2)`-bit input `f`, the
    cascade `gidney_adder_forward_faithful_full (n+2)` acts as
    `gidney_forward_faithful_full_post_state (n+2)` on basis states.

    Combines `gidney_adder_forward_with_propagation_correct`
    (propagation, this iter) with `gidney_adder_bit_step_faithful_last_correct`
    (last bit, Iter 67). Single dim-bound hypothesis `3*(n+2) ≤ dim`
    covers all qubits including the (n+1)-th carry. -/
theorem gidney_adder_forward_faithful_full_correct
    (dim : Nat) (hdim : 0 < dim) (f : Nat → Bool) (n : Nat)
    (hbd : 3 * (n + 2) ≤ dim) :
    uc_eval (Gate.toUCom dim (gidney_adder_forward_faithful_full (n + 2)))
      * f_to_vec dim f
      = f_to_vec dim (gidney_forward_faithful_full_post_state (n + 2) f) := by
  show uc_eval (Gate.toUCom dim
          (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                    (gidney_adder_bit_step_faithful_last (n + 1))))
        * f_to_vec dim f
        = f_to_vec dim
            (gidney_last_bit_post_state (n + 1)
              (gidney_propagation_post_state (n + 1) f))
  apply gate_seq_acts_on_basis dim _ _ f
          (gidney_propagation_post_state (n + 1) f) _
  · -- Propagation cascade correctness (just proven above)
    exact gidney_adder_forward_with_propagation_correct dim hdim f (n + 1)
            (by omega)
  · -- Last-bit correctness at position n+1
    -- The propagation cascade's post-state has the same qubit layout as f
    -- (only modifies certain qubits, all of them < dim by the dim bound).
    -- last-bit needs: read_(n+1), target_(n+1), carry_(n+1), carry_n < dim
    --  + pairwise disjoint indices.
    exact gidney_adder_bit_step_faithful_last_correct dim (n + 1) _
            (by unfold read_idx; omega)
            (by unfold target_idx; omega)
            (by unfold carry_idx; omega)
            (by unfold carry_idx; omega)
            (by unfold read_idx target_idx; omega)
            (by unfold read_idx carry_idx; omega)
            (by unfold target_idx carry_idx; omega)
            (by unfold carry_idx; omega)

/-- **Final CX cascade correctness** on classical basis states.
    Single dim-bound hypothesis `3 * n ≤ dim` covers all qubits
    `target_idx (n-1) = 3n - 2 < dim` (for n ≥ 1).

    Proof by structural recursion on `n`:
    - n = 0: cascade is `Gate.I`; trivially preserves.
    - n + 1: `gate_seq_acts_on_basis` + IH + per-step
      `gate_cx_acts_on_basis` with disjointness via `omega`. -/
theorem gidney_final_cx_cascade_correct
    (dim : Nat) (hdim : 0 < dim) (f : Nat → Bool) :
    ∀ n, 3 * n ≤ dim →
    uc_eval (Gate.toUCom dim (gidney_final_cx_cascade n)) * f_to_vec dim f
      = f_to_vec dim (gidney_final_cx_cascade_post_state n f)
  | 0    , _   => by
      show uc_eval (Gate.toUCom dim (Gate.I : Gate)) * f_to_vec dim f = f_to_vec dim f
      rw [Gate.toUCom_I, uc_eval_ID_eq_one hdim, Matrix.one_mul]
  | n + 1, hbd => by
      show uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_final_cx_cascade n)
                        (Gate.CX (read_idx n) (target_idx n))))
            * f_to_vec dim f
            = f_to_vec dim (gidney_final_cx_cascade_post_state (n + 1) f)
      apply gate_seq_acts_on_basis dim _ _ f
              (gidney_final_cx_cascade_post_state n f) _
      · -- IH
        exact gidney_final_cx_cascade_correct dim hdim f n (by omega)
      · -- Per-step CX correctness
        exact gate_cx_acts_on_basis dim _ _
                (by unfold read_idx; omega)
                (by unfold target_idx; omega)
                (by unfold read_idx target_idx; omega)
                _

/-- T-count of the propagation reverse cascade: 7n (same gates as
    forward, reversed). -/
theorem tcount_gidney_adder_forward_with_propagation_reverse : ∀ n,
    tcount (gidney_adder_forward_with_propagation_reverse n) = 7 * n
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      show tcount (Gate.seq (gidney_adder_bit_step_faithful_interior_reverse (n + 1))
                            (gidney_adder_forward_with_propagation_reverse (n + 1)))
            = 7 * (n + 2)
      simp [tcount,
            tcount_gidney_adder_bit_step_faithful_interior_reverse,
            tcount_gidney_adder_forward_with_propagation_reverse (n + 1)]
      omega

/-- T-count of the faithful full reverse cascade: 7n for `n ≥ 2`. -/
theorem tcount_gidney_adder_forward_faithful_full_reverse (n : Nat) :
    tcount (gidney_adder_forward_faithful_full_reverse (n + 2)) = 7 * (n + 2) := by
  show tcount (Gate.seq (gidney_adder_bit_step_faithful_last_reverse (n + 1))
                        (gidney_adder_forward_with_propagation_reverse (n + 1)))
        = 7 * (n + 2)
  -- last_reverse i = seq (CX_chain) (CCX), so tcount = 7
  have h_last : tcount (gidney_adder_bit_step_faithful_last_reverse (n + 1)) = 7 := by
    unfold gidney_adder_bit_step_faithful_last_reverse
    rfl
  simp [tcount, h_last,
        tcount_gidney_adder_forward_with_propagation_reverse]
  omega

/-- **Cascade-level forward · reverse = identity** for the propagation
    cascade. By structural recursion on `n`: collapse the middle
    `interior fwd · interior rev` pair via Iter 82's
    `..._interior_fwd_rev_eq_one`, then apply IH.

    Base cases:
    - n = 0: both are Gate.I; product is ID·ID = 1.
    - n = 1: just first_fwd · first_rev = 1 by Iter 81's involution.

    Inductive step n+2: `(forward (n+1) ; interior (n+1)) ;
                         (interior_reverse (n+1) ; reverse (n+1))`.
    Reassociate matrix product, collapse middle interior pair via
    Iter 82, drop via Matrix.one_mul, apply IH on forward (n+1) ·
    reverse (n+1). -/
theorem gidney_adder_forward_with_propagation_fwd_rev_eq_one
    (dim : Nat) (hdim : 0 < dim) :
    ∀ n, 3 * n + 2 ≤ dim →
    uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_forward_with_propagation n)
                        (gidney_adder_forward_with_propagation_reverse n)))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ)
  | 0    , _ => by
      show uc_eval (Gate.toUCom dim (Gate.I : Gate)) *
             uc_eval (Gate.toUCom dim (Gate.I : Gate)) = 1
      rw [Gate.toUCom_I, uc_eval_ID_eq_one hdim, Matrix.one_mul]
  | 1    , hbd => by
      -- propagation 1 = first; apply Iter 81's first-bit involution.
      show uc_eval (Gate.toUCom dim
              (Gate.seq gidney_adder_bit_step_faithful_first
                        gidney_adder_bit_step_faithful_first_reverse)) = 1
      have fb := first_bit_disjointness_of_dim_bound dim (by omega : 5 ≤ dim)
      obtain ⟨hr0, ht0, hc0, hr1, ht1, h_rt, h_rc, h_tc, h_c_r1, h_c_t1⟩ := fb
      exact gidney_adder_bit_step_faithful_first_fwd_rev_eq_one dim
              hr0 ht0 hc0 hr1 ht1 h_rt h_rc h_tc h_c_r1 h_c_t1
  | n + 2, hbd => by
      have ih : uc_eval (Gate.toUCom dim
                  (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                            (gidney_adder_forward_with_propagation_reverse (n + 1)))) = 1 := by
        apply gidney_adder_forward_with_propagation_fwd_rev_eq_one dim hdim (n + 1)
        omega
      have d := bit_disjointness_of_dim_bound dim (n + 1) (by omega) (by omega)
      have hstep := gidney_adder_bit_step_faithful_interior_fwd_rev_eq_one
                      dim (n + 1) d.hri d.hti d.hci d.hcim1 d.hri1 d.hti1
                      d.h_rt d.h_rc d.h_tc d.h_cc d.h_ci_ri1 d.h_ci_ti1
      -- Goal after pattern-match:
      -- uc_eval (toUCom (seq (seq fwd_(n+1) interior_(n+1))
      --                      (seq interior_rev_(n+1) rev_(n+1)))) = 1
      -- Which is uc_eval(rev_(n+1)) * uc_eval(interior_rev_(n+1))
      --        * uc_eval(interior_(n+1)) * uc_eval(fwd_(n+1)) = 1.
      show (uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation_reverse (n + 1)))
              * uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_interior_reverse (n + 1))))
            * (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_interior (n + 1)))
              * uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation (n + 1)))) = 1
      rw [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc
            (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_interior_reverse (n + 1))))
            (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_interior (n + 1))))
            (uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation (n + 1))))]
      -- Middle pair = uc_eval (toUCom (seq interior interior_reverse)) by defeq.
      show uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation_reverse (n + 1)))
            * (uc_eval (Gate.toUCom dim
                         (Gate.seq (gidney_adder_bit_step_faithful_interior (n + 1))
                                   (gidney_adder_bit_step_faithful_interior_reverse (n + 1))))
              * uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation (n + 1)))) = 1
      rw [hstep, Matrix.one_mul]
      exact ih

/-- **Faithful full forward · reverse = identity (cascade level)**
    for the `(n+2)`-bit Gidney adder. Combines
    `..._with_propagation_fwd_rev_eq_one` (propagation cascade) +
    Iter 69's `..._last_fwd_rev_id` (last bit) via matrix reassociation. -/
theorem gidney_adder_forward_faithful_full_fwd_rev_eq_one
    (dim : Nat) (hdim : 0 < dim) (n : Nat)
    (hbd : 3 * (n + 2) ≤ dim) :
    uc_eval (Gate.toUCom dim
              (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                        (gidney_adder_forward_faithful_full_reverse (n + 2))))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  -- After pattern match, the full faithful's def expands to:
  --   seq (seq propagation_(n+1) last_(n+1)) (seq last_reverse_(n+1) propagation_reverse_(n+1))
  -- uc_eval = uc_eval(prop_rev_(n+1)) * uc_eval(last_rev_(n+1))
  --         * uc_eval(last_(n+1)) * uc_eval(prop_(n+1))
  have hprop : uc_eval (Gate.toUCom dim
                (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                          (gidney_adder_forward_with_propagation_reverse (n + 1)))) = 1 := by
    apply gidney_adder_forward_with_propagation_fwd_rev_eq_one dim hdim (n + 1)
    omega
  -- Iter 69's last-bit fwd·rev acts on f_to_vec; we need its matrix-level form.
  -- Iter 69's `..._faithful_last_fwd_rev_id` is f_to_vec form;
  -- We need to extract a matrix-level lemma. Let's use matrix_eq_of_basis_action.
  -- Actually, we have it from Iter 67 last-bit's f_to_vec correctness composed with
  -- the reverse direction. Let me use a direct approach:
  -- last_(n+1) followed by last_reverse_(n+1) at gate level is exactly CCX·CX·CX·CCX,
  -- which is uc_eval CCX * uc_eval CX * uc_eval CX * uc_eval CCX in matrix form.
  -- CX·CX = 1 and CCX·CCX = 1, so the product is 1.
  -- Construct this inline (like Iter 69 did at the f_to_vec level, but matrix-level):
  have hlast : uc_eval (Gate.toUCom dim
                (Gate.seq (gidney_adder_bit_step_faithful_last (n + 1))
                          (gidney_adder_bit_step_faithful_last_reverse (n + 1)))) = 1 := by
    unfold gidney_adder_bit_step_faithful_last
           gidney_adder_bit_step_faithful_last_reverse
    -- Forward: CCX ; CX(chain). Reverse: CX(chain) ; CCX.
    -- uc_eval(fwd) = CX_chain * CCX. uc_eval(rev) = CCX * CX_chain.
    -- Compose: (CCX * CX_chain) * (CX_chain * CCX) = CCX * (CX_chain * CX_chain) * CCX.
    show (uc_eval (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1))
                    : BaseUCom dim)
          * uc_eval (BaseUCom.CNOT (carry_idx (n + 1 - 1)) (carry_idx (n + 1))))
          * (uc_eval (BaseUCom.CNOT (carry_idx (n + 1 - 1)) (carry_idx (n + 1)))
            * uc_eval (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1)))) = 1
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc
          (uc_eval (BaseUCom.CNOT (carry_idx (n + 1 - 1)) (carry_idx (n + 1)) : BaseUCom dim))
          (uc_eval (BaseUCom.CNOT (carry_idx (n + 1 - 1)) (carry_idx (n + 1))))
          (uc_eval (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1))))]
    show uc_eval (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1))
                  : BaseUCom dim)
          * (uc_eval (UCom.seq (BaseUCom.CNOT (carry_idx (n + 1 - 1)) (carry_idx (n + 1))
                                : BaseUCom dim)
                               (BaseUCom.CNOT (carry_idx (n + 1 - 1)) (carry_idx (n + 1))))
            * uc_eval (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1)))) = 1
    rw [CNOT_CNOT_eq_one dim (carry_idx (n + 1 - 1)) (carry_idx (n + 1))
          (by unfold carry_idx; omega) (by unfold carry_idx; omega)
          (by unfold carry_idx; omega)]
    rw [Matrix.one_mul]
    show uc_eval (UCom.seq (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1))
                            : BaseUCom dim)
                           (BaseUCom.CCX (read_idx (n + 1)) (target_idx (n + 1)) (carry_idx (n + 1)))) = 1
    exact CCX_CCX_eq_one dim _ _ _
            (by unfold read_idx; omega)
            (by unfold target_idx; omega)
            (by unfold carry_idx; omega)
            (by unfold read_idx target_idx; omega)
            (by unfold read_idx carry_idx; omega)
            (by unfold target_idx carry_idx; omega)
  -- Combine: full = seq (seq prop last) (seq last_rev prop_rev).
  show (uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation_reverse (n + 1)))
          * uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_last_reverse (n + 1))))
        * (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_last (n + 1)))
          * uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation (n + 1)))) = 1
  rw [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
        (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_last_reverse (n + 1))))
        (uc_eval (Gate.toUCom dim (gidney_adder_bit_step_faithful_last (n + 1))))
        (uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation (n + 1))))]
  -- Middle pair = uc_eval(toUCom(seq last last_reverse)) by defeq
  show uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation_reverse (n + 1)))
        * (uc_eval (Gate.toUCom dim
                     (Gate.seq (gidney_adder_bit_step_faithful_last (n + 1))
                               (gidney_adder_bit_step_faithful_last_reverse (n + 1))))
          * uc_eval (Gate.toUCom dim (gidney_adder_forward_with_propagation (n + 1)))) = 1
  rw [hlast, Matrix.one_mul]
  exact hprop

/-- T-count of the full no-measurement faithful adder for `(n+2)`
    bits: `14(n+2)`. Derived from the gate sequence:
    7(n+2) (forward) + 0 (final CX = pure CXs) + 7(n+2) (reverse). -/
theorem tcount_gidney_adder_full_faithful_no_measurement (n : Nat) :
    tcount (gidney_adder_full_faithful_no_measurement (n + 2)) = 14 * (n + 2) := by
  show tcount (Gate.seq
                (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                          (gidney_final_cx_cascade (n + 2)))
                (gidney_adder_forward_faithful_full_reverse (n + 2)))
        = 14 * (n + 2)
  simp [tcount, tcount_gidney_adder_forward_faithful_full,
        tcount_gidney_final_cx_cascade,
        tcount_gidney_adder_forward_faithful_full_reverse]
  omega

/-- Concrete: 4-bit full faithful adder = 56 T-gates = 8 Toffolis. -/
example : tcount (gidney_adder_full_faithful_no_measurement 4) = 56 :=
  tcount_gidney_adder_full_faithful_no_measurement 2

/-- Concrete: 33-bit full faithful adder (RSA-2048 q_A=33) =
    14 · 33 = 462 T-gates = 66 Toffolis. **No-measurement
    upper bound** (Gidney measurement trick would halve this to
    33 Toffolis = 231 T). -/
example : tcount (gidney_adder_full_faithful_no_measurement 33) = 14 * 33 :=
  tcount_gidney_adder_full_faithful_no_measurement 31

/-- **Gate-faithful no-measurement vs measurement-trick factor**
    (Iter 88). Strengthens `gidney_full_vs_measurement_uncompute_factor`
    (Iter 25, simplified bit-step) to the **gate-faithful** Gidney
    adder. The faithful encoding emits the same Toffoli count (14n
    T-gates), but is now backed by `qq_gidney_adder.py`'s full gate
    sequence and the Phase A semantic/structural correctness chain
    (Iter 65/57/67 per-bit + Iter 80 cascade forward + Iter 83
    matrix-level inverse + Iter 86 reverse correctness).

    The factor of 2 remains the **measurement-uncomputation review
    gap**: faithful no-measurement T-count = 14n = 2 · (measurement
    paper-claim count 7n). -/
theorem gidney_adder_full_faithful_no_measurement_vs_measurement_factor
    (n : Nat) :
    tcount (gidney_adder_full_faithful_no_measurement (n + 2))
      = 2 * gidney_adder_full_with_measurement_uncompute_tcount (n + 2) := by
  rw [tcount_gidney_adder_full_faithful_no_measurement,
      gidney_adder_full_with_measurement_uncompute_tcount_eq]
  omega

end FormalRV.BQAlgo
