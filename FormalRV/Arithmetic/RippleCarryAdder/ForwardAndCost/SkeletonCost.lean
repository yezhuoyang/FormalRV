/-
  FormalRV.Arithmetic.RippleCarryAdder.ForwardAndCost.SkeletonCost
  Cost lemmas (part 1/5): T and gate counts of the cost-only skeleton cascades, the
  PaperClaims Toffoli-count bridge, and the no-measurement-vs-measurement
  factor-of-2 gap. Supporting lemmas; the faithful backbone is `FaithfulBackbone`.
-/
import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Framework.PaperClaims
import FormalRV.PPM.GidneyAND
import Mathlib.Tactic.IntervalCases
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderPostStates
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderCostSkeleton

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

end FormalRV.BQAlgo
