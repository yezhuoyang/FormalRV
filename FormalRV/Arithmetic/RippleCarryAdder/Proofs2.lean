import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Corpus.PaperClaims
import FormalRV.PPM.GidneyAND
import Mathlib.Tactic.IntervalCases
import FormalRV.Arithmetic.RippleCarryAdder.Defs
import FormalRV.Arithmetic.RippleCarryAdder.Proofs1

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-- Concrete RSA-2048 (q_A=33): with Gidney measurement trick,
    T-count = 231 (paper figure); without (faithful gate-explicit),
    462 — the factor of 2 review gap. -/
example :
    gidney_adder_full_with_measurement_uncompute_tcount 33 = 231
    ∧ tcount (gidney_adder_full_faithful_no_measurement 33) = 462 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **Reverse cascade correctness on basis states** — derived as a
    corollary of Iter 80 (forward correctness) + Iter 83 (matrix-
    level forward · reverse = 1). On any classical basis state
    `f_to_vec dim (gidney_forward_faithful_full_post_state (n+2) f)`,
    the reverse cascade produces back `f_to_vec dim f`. -/
theorem gidney_adder_forward_faithful_full_reverse_correct
    (dim : Nat) (hdim : 0 < dim) (f : Nat → Bool) (n : Nat)
    (hbd : 3 * (n + 2) ≤ dim) :
    uc_eval (Gate.toUCom dim (gidney_adder_forward_faithful_full_reverse (n + 2)))
      * f_to_vec dim (gidney_forward_faithful_full_post_state (n + 2) f)
      = f_to_vec dim f := by
  -- Strategy: rewrite the post-state expression via the FORWARD
  -- correctness theorem (Iter 80), then apply the matrix-level
  -- fwd · rev = 1 (Iter 83).
  have hfwd := gidney_adder_forward_faithful_full_correct dim hdim f n hbd
  have hinv := gidney_adder_forward_faithful_full_fwd_rev_eq_one dim hdim n hbd
  rw [← hfwd]
  rw [← Matrix.mul_assoc]
  -- Goal: (uc_eval(rev) * uc_eval(fwd)) * f_to_vec(f) = f_to_vec(f)
  -- `uc_eval (Gate.toUCom dim (Gate.seq fwd rev))` is defeq to
  -- `uc_eval (toUCom rev) * uc_eval (toUCom fwd)` (via uc_eval's seq clause).
  show uc_eval (Gate.toUCom dim
                  (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                            (gidney_adder_forward_faithful_full_reverse (n + 2))))
        * f_to_vec dim f = f_to_vec dim f
  rw [hinv, Matrix.one_mul]

/-! ## Full adder structural unfolding theorem (Iter 87, 2026-05-12)

    Compose the three per-leg correctness theorems
    (Iter 80 forward, Iter 85 final CX, Iter 86 reverse) via
    `gate_seq_acts_on_basis` to give a **structural unfolding** of
    the full adder's action on basis states.

    The unfolding **stops just before the reverse step**, leaving
    `uc_eval(reverse) * f_to_vec(cx_post(forward_post f))` on the
    RHS. To convert this to a final closed-form post-state, one
    would need to express how the reverse cascade acts on the
    cx-modified state — which depends on the arithmetic
    interpretation (a + b mod 2^n on the target register). That
    closed-form is the **Iter 88-89 capstone** task. -/

/-- **Full faithful adder structural unfolding** on classical basis
    states. The action of `gidney_adder_full_faithful_no_measurement`
    on `f_to_vec dim f` is expressed as:

      uc_eval(reverse) * f_to_vec(cx_post(forward_post f))

    where `forward_post = gidney_forward_faithful_full_post_state` and
    `cx_post = gidney_final_cx_cascade_post_state`. The reverse
    cascade is left symbolic; closing it to a final basis state
    requires the arithmetic-semantics theorem (Iter 88-89).

    This unfolding gives the structural skeleton needed to derive
    the end-to-end `(a, b, 0) → (a, a+b mod 2^n, 0)` theorem. -/
theorem gidney_adder_full_faithful_no_measurement_unfold
    (dim : Nat) (hdim : 0 < dim) (f : Nat → Bool) (n : Nat)
    (hbd : 3 * (n + 2) ≤ dim) :
    uc_eval (Gate.toUCom dim (gidney_adder_full_faithful_no_measurement (n + 2)))
      * f_to_vec dim f
      = uc_eval (Gate.toUCom dim (gidney_adder_forward_faithful_full_reverse (n + 2)))
          * f_to_vec dim
              (gidney_final_cx_cascade_post_state (n + 2)
                (gidney_forward_faithful_full_post_state (n + 2) f)) := by
  -- Combine forward + final CX into a single basis-state action via gate_seq.
  have h_fwd_cx : uc_eval (Gate.toUCom dim
                    (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                              (gidney_final_cx_cascade (n + 2))))
                  * f_to_vec dim f
                  = f_to_vec dim
                      (gidney_final_cx_cascade_post_state (n + 2)
                        (gidney_forward_faithful_full_post_state (n + 2) f)) := by
    apply gate_seq_acts_on_basis dim _ _ f
            (gidney_forward_faithful_full_post_state (n + 2) f) _
    · exact gidney_adder_forward_faithful_full_correct dim hdim f n hbd
    · exact gidney_final_cx_cascade_correct dim hdim
              (gidney_forward_faithful_full_post_state (n + 2) f) (n + 2)
              (by omega)
  -- gidney_adder_full_faithful_no_measurement (n+2) =
  --   seq (seq forward_faithful_full final_cx_cascade) forward_faithful_full_reverse
  -- uc_eval(seq (seq A B) C) = uc_eval(C) * uc_eval(seq A B) (by uc_eval semantics)
  show uc_eval (Gate.toUCom dim (gidney_adder_forward_faithful_full_reverse (n + 2)))
        * uc_eval (Gate.toUCom dim
                    (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                              (gidney_final_cx_cascade (n + 2))))
        * f_to_vec dim f
        = uc_eval (Gate.toUCom dim (gidney_adder_forward_faithful_full_reverse (n + 2)))
            * f_to_vec dim
                (gidney_final_cx_cascade_post_state (n + 2)
                  (gidney_forward_faithful_full_post_state (n + 2) f))
  rw [Matrix.mul_assoc]
  rw [h_fwd_cx]

/-- First-bit step on zero input gives zero. Each of the three
    updates writes `xor false false = false`, hence is a no-op by
    `Function.update_eq_self`. -/
theorem gidney_first_bit_post_state_on_zero :
    gidney_first_bit_post_state zeroF = zeroF := by
  unfold gidney_first_bit_post_state zeroF
  simp

/-- Bit-step (interior) on zero input gives zero. Same pattern as
    first-bit: each update writes false. -/
theorem gidney_bit_step_faithful_post_state_on_zero (i : Nat) :
    gidney_bit_step_faithful_post_state i zeroF = zeroF := by
  unfold gidney_bit_step_faithful_post_state zeroF
  simp

/-- Last-bit step on zero input gives zero. -/
theorem gidney_last_bit_post_state_on_zero (i : Nat) :
    gidney_last_bit_post_state i zeroF = zeroF := by
  unfold gidney_last_bit_post_state zeroF
  simp

/-- Propagation cascade on zero input gives zero. Induction on n. -/
theorem gidney_propagation_post_state_on_zero : ∀ n,
    gidney_propagation_post_state n zeroF = zeroF
  | 0     => rfl
  | 1     => gidney_first_bit_post_state_on_zero
  | n + 2 => by
      show gidney_bit_step_faithful_post_state (n + 1)
            (gidney_propagation_post_state (n + 1) zeroF) = zeroF
      rw [gidney_propagation_post_state_on_zero (n + 1)]
      exact gidney_bit_step_faithful_post_state_on_zero (n + 1)

/-- Full forward cascade on zero input gives zero. -/
theorem gidney_forward_faithful_full_post_state_on_zero : ∀ n,
    gidney_forward_faithful_full_post_state n zeroF = zeroF
  | 0     => rfl
  | 1     => rfl
  | n + 2 => by
      show gidney_last_bit_post_state (n + 1)
            (gidney_propagation_post_state (n + 1) zeroF) = zeroF
      rw [gidney_propagation_post_state_on_zero (n + 1)]
      exact gidney_last_bit_post_state_on_zero (n + 1)

/-- Final CX cascade on zero input gives zero. Induction on n —
    each CX(read_i, target_i) writes `target_i ⊕= false = target_i`,
    a no-op. -/
theorem gidney_final_cx_cascade_post_state_on_zero : ∀ n,
    gidney_final_cx_cascade_post_state n zeroF = zeroF
  | 0     => rfl
  | n + 1 => by
      show update (gidney_final_cx_cascade_post_state n zeroF)
              (target_idx n)
              (xor (gidney_final_cx_cascade_post_state n zeroF (target_idx n))
                   (gidney_final_cx_cascade_post_state n zeroF (read_idx n)))
            = zeroF
      rw [gidney_final_cx_cascade_post_state_on_zero n]
      simp [zeroF]

/-- **End-to-end smoke test**: full faithful Gidney adder on the
    all-zero input gives back the all-zero output. The simplest
    arithmetic claim `0 + 0 = 0 mod 2^n` verified at the gate level.

    Proof: combine Iter 87's structural unfolding with the zero-input
    lemmas above to reduce the full adder's action to
    `uc_eval(reverse) * f_to_vec(zero)`. Then apply Iter 86's reverse
    correctness (with f = zero, since `forward_post(zero) = zero`)
    to get `f_to_vec(zero)`. -/
theorem gidney_adder_full_faithful_no_measurement_on_zero
    (dim : Nat) (hdim : 0 < dim) (n : Nat)
    (hbd : 3 * (n + 2) ≤ dim) :
    uc_eval (Gate.toUCom dim (gidney_adder_full_faithful_no_measurement (n + 2)))
      * f_to_vec dim zeroF
      = f_to_vec dim zeroF := by
  rw [gidney_adder_full_faithful_no_measurement_unfold dim hdim zeroF n hbd]
  rw [gidney_forward_faithful_full_post_state_on_zero (n + 2)]
  rw [gidney_final_cx_cascade_post_state_on_zero (n + 2)]
  -- Goal: uc_eval(reverse) * f_to_vec(zero) = f_to_vec(zero).
  -- This is Iter 86's reverse correctness with f = zero, after we
  -- show that forward_post(zero) = zero (so the post_state arg = zero).
  -- But reverse_correct's statement is `uc_eval(rev) * f_to_vec(post_state f) = f_to_vec(f)`.
  -- With f = zero, post_state(zero) = zero, so LHS = uc_eval(rev) * f_to_vec(zero)
  -- and RHS = f_to_vec(zero). Use this directly:
  have h := gidney_adder_forward_faithful_full_reverse_correct dim hdim zeroF n hbd
  rw [gidney_forward_faithful_full_post_state_on_zero (n + 2)] at h
  exact h

/-- **Concrete forward action check** at every qubit position for
    the 2-bit adder on `inputF_1_plus_0`. After the forward cascade
    (first-bit step + last-bit step):
    - read_0 stays 1 (CCX has read_0 as control; control=1 but target_0=0, so CCX writes 1 ∧ 0 = 0 into carry — no change)
    - target_0 stays 0
    - carry_0 = 0 (read_0 ∧ target_0 = 1 ∧ 0 = 0)
    - read_1, target_1, carry_1 all stay 0 (no propagation since carry_0 = 0).

    All 6 positions evaluate by `decide`, confirming the forward
    cascade preserves the state on this input. The arithmetic
    interpretation: forward correctly determines that no carries
    are generated. -/
example :
    let post := gidney_forward_faithful_full_post_state 2 inputF_1_plus_0
    post 0 = true ∧ post 1 = false ∧ post 2 = false
    ∧ post 3 = false ∧ post 4 = false ∧ post 5 = false := by decide

/-- **Concrete final-CX action check** for the 2-bit adder on the
    forward-post-state above. The final CX cascade applies:
    - CX(read_0, target_0): target_0 ⊕= read_0 = 0 ⊕ 1 = 1.
    - CX(read_1, target_1): target_1 ⊕= read_1 = 0 ⊕ 0 = 0.

    After final CX, target = (1, 0), the sum 1 + 0 = 1 ✓. -/
example :
    let post := gidney_final_cx_cascade_post_state 2
                (gidney_forward_faithful_full_post_state 2 inputF_1_plus_0)
    post 0 = true ∧ post 1 = true ∧ post 2 = false
    ∧ post 3 = false ∧ post 4 = false ∧ post 5 = false := by decide

/-- **Forward post-state on (1, 1) input**: carry_0 generated,
    propagation flips read_1 and target_1 to 1, but the last-bit
    step's CCX·CX leaves carry_1 = 0. -/
example :
    let post := gidney_forward_faithful_full_post_state 2 inputF_1_plus_1
    post 0 = true   -- read_0 = 1 (unchanged)
    ∧ post 1 = true   -- target_0 = 1 (unchanged by forward; CCX only writes carry)
    ∧ post 2 = true   -- carry_0 = 1 ∧ 1 = 1 (generated!)
    ∧ post 3 = true   -- read_1 = 0 ⊕ carry_0 = 1 (propagated)
    ∧ post 4 = true   -- target_1 = 0 ⊕ carry_0 = 1 (propagated)
    ∧ post 5 = false  -- carry_1 = (read_1' ∧ target_1') ⊕ carry_0 = 1 ⊕ 1 = 0
    := by decide

/-- **Final CX post-state on (1, 1) input**: `target_0 = 0`
    (sum-bit-0 = a XOR b XOR carry_in = 1 ⊕ 1 ⊕ 0 = 0 ✓),
    `target_1 = 0` (at this point target_1 is XOR'd by post-CX
    read_1=1, so 1 ⊕ 1 = 0 — NOT the sum bit; the reverse cascade
    is needed to restore target_1 = 1 via the propagation undo). -/
example :
    let post := gidney_final_cx_cascade_post_state 2
                (gidney_forward_faithful_full_post_state 2 inputF_1_plus_1)
    post 0 = true     -- read_0 = 1 (unchanged)
    ∧ post 1 = false  -- target_0 = 1 ⊕ 1 = 0 (sum bit 0)
    ∧ post 2 = true   -- carry_0 unchanged
    ∧ post 3 = true   -- read_1 unchanged
    ∧ post 4 = false  -- target_1 = 1 ⊕ 1 = 0 (pre-reverse)
    ∧ post 5 = false  -- carry_1 unchanged
    := by decide

/-- **Forward post-state on (3, 1) input** (9 qubits checked). -/
example :
    let post := gidney_forward_faithful_full_post_state 3 inputF_3_plus_1
    post 0 = true     -- read_0 = 1 (unchanged)
    ∧ post 1 = true   -- target_0 = 1 (unchanged by forward CCX)
    ∧ post 2 = true   -- carry_0 = 1 ∧ 1 = 1 (generated)
    ∧ post 3 = false  -- read_1 = 1 ⊕ carry_0 = 0 (propagated)
    ∧ post 4 = true   -- target_1 = 0 ⊕ carry_0 = 1 (propagated)
    ∧ post 5 = true   -- carry_1 = (0 ∧ 1) ⊕ 1 = 1 (chain carry)
    ∧ post 6 = true   -- read_2 = 0 ⊕ carry_1 = 1 (propagated)
    ∧ post 7 = true   -- target_2 = 0 ⊕ carry_1 = 1 (propagated)
    ∧ post 8 = false  -- carry_2 = (1 ∧ 1) ⊕ 1 = 0 (last-bit chain)
    := by decide

/-- **Final CX post-state on (3, 1) input**: target = (0, 1, 0) =
    "010" LSB-first = **2**, NOT the expected sum 4 = "100".
    The reverse cascade is required to flip target_2 from 0 to 1
    (via interior_reverse's CX(carry_1, target_2)) to obtain the
    correct sum. Same review pattern as Iter 106's 2-bit `1+1=2`. -/
example :
    let post := gidney_final_cx_cascade_post_state 3
                (gidney_forward_faithful_full_post_state 3 inputF_3_plus_1)
    post 0 = true     -- read_0 = 1
    ∧ post 1 = false  -- target_0 = 1 ⊕ 1 = 0 (sum bit 0 ✓)
    ∧ post 2 = true   -- carry_0 = 1
    ∧ post 3 = false  -- read_1 = 0
    ∧ post 4 = true   -- target_1 = 1 ⊕ 0 = 1 (sum bit 1 = a_1⊕b_1⊕carry_0 = 1⊕0⊕1 = 0... let me re-check)
    ∧ post 5 = true   -- carry_1 = 1
    ∧ post 6 = true   -- read_2 = 1
    ∧ post 7 = false  -- target_2 = 1 ⊕ 1 = 0 (pre-reverse; reverse will flip to 1)
    ∧ post 8 = false  -- carry_2 = 0
    := by decide

/-- **Forward post-state on (7, 1) input** at all 12 qubits.
    Carry chain: carry_0=1, carry_1=1, carry_2=1, carry_3=0 (last-
    bit step's chain CX cancels). Propagation flips read_1, read_2,
    read_3 (via CX with carries of 1) and target_1, target_2, target_3. -/
example :
    let post := gidney_forward_faithful_full_post_state 4 inputF_7_plus_1
    post 0 = true     -- read_0 = 1
    ∧ post 1 = true   -- target_0 = 1
    ∧ post 2 = true   -- carry_0 = 1
    ∧ post 3 = false  -- read_1 = 1 ⊕ 1 = 0
    ∧ post 4 = true   -- target_1 = 0 ⊕ 1 = 1
    ∧ post 5 = true   -- carry_1 = (0 ∧ 1) ⊕ 1 = 1
    ∧ post 6 = false  -- read_2 = 1 ⊕ 1 = 0
    ∧ post 7 = true   -- target_2 = 0 ⊕ 1 = 1
    ∧ post 8 = true   -- carry_2 = (0 ∧ 1) ⊕ 1 = 1
    ∧ post 9 = true   -- read_3 = 0 ⊕ 1 = 1
    ∧ post 10 = true  -- target_3 = 0 ⊕ 1 = 1
    ∧ post 11 = false -- carry_3 = (1 ∧ 1) ⊕ 1 = 0
    := by decide

/-- **Final CX post-state on (7, 1) input**: target_0 = 1⊕1 = 0
    (sum bit 0), target_3 = 1⊕1 = 0 (NOT the sum bit 3, which
    should be 1 for 8 = "1000" binary; the reverse cascade is
    needed to flip target_3 from 0 to 1). -/
example :
    let post := gidney_final_cx_cascade_post_state 4
                (gidney_forward_faithful_full_post_state 4 inputF_7_plus_1)
    post 0 = true     -- read_0
    ∧ post 1 = false  -- target_0 = 1 ⊕ 1 = 0 (sum bit 0 ✓)
    ∧ post 2 = true   -- carry_0
    ∧ post 3 = false  -- read_1
    ∧ post 4 = true   -- target_1 = 1 ⊕ 0 = 1 (= read_1=0, unchanged)
    ∧ post 5 = true   -- carry_1
    ∧ post 6 = false  -- read_2
    ∧ post 7 = true   -- target_2 = 1 ⊕ 0 = 1 (unchanged)
    ∧ post 8 = true   -- carry_2
    ∧ post 9 = true   -- read_3
    ∧ post 10 = false -- target_3 = 1 ⊕ 1 = 0 (pre-reverse)
    ∧ post 11 = false -- carry_3
    := by decide

/-- **Smoke test on `inputF_1_plus_1` (a=1, b=1)**: starting from
    the post-final-CX state `(read=(1,0), target=(0,0), carry=(1,0))`
    after the 2-bit Gidney adder's forward + final CX, the first-bit
    reverse acts on it. Verify the post-state via decide. -/
example :
    -- Starting state after forward + final CX on inputF_1_plus_1:
    -- (1, 0, 1, 1, 0, 0) i.e., read=(1,1), target=(0,0), carry=(1,0).
    -- Wait this is 2-bit case, but first_bit_reverse uses bit 0 + bit 1
    -- indices, applied to a 6-qubit state.
    -- After first-bit reverse on this state:
    -- - CX(2, 4): target_1 ⊕= carry_0(=1) → target_1 = 0 ⊕ 1 = 1.
    -- - CX(2, 3): read_1 ⊕= carry_0(=1) → read_1 = 1 ⊕ 1 = 0.
    -- - CCX(0, 1, 2): carry_0 ⊕= read_0(=1) ∧ target_0(=0) → carry_0 = 1 ⊕ 0 = 1.
    let prev := gidney_final_cx_cascade_post_state 2
                (gidney_forward_faithful_full_post_state 2 inputF_1_plus_1)
    let post := gidney_first_bit_reverse_post_state prev
    post 0 = true   -- read_0
    ∧ post 1 = false  -- target_0
    ∧ post 2 = true   -- carry_0 (still 1 — dirty per Iter 106 finding)
    ∧ post 3 = false  -- read_1 (restored)
    ∧ post 4 = true   -- target_1 (now sum bit 1 = 1, was 0 after final-CX)
    ∧ post 5 = false  -- carry_1
    := by decide

/-- **Smoke test on `inputF_3_plus_1`**: starting from the
    post-(forward+final-CX) state of the 3-bit adder, apply the
    interior-bit reverse at i=1. Verify the post-state at all 9
    qubits via decide. -/
example :
    let prev := gidney_final_cx_cascade_post_state 3
                (gidney_forward_faithful_full_post_state 3 inputF_3_plus_1)
    let post := gidney_interior_bit_reverse_post_state 1 prev
    -- The interior reverse at i=1 undoes propagation to bit 2
    -- (CX(carry_1, read_2/target_2)) and the chain CX at bit 1.
    post 0 = true   -- read_0 unchanged
    ∧ post 1 = false  -- target_0 unchanged
    ∧ post 2 = true   -- carry_0 unchanged
    ∧ post 3 = false  -- read_1 unchanged (this reverse doesn't touch read_1 directly)
    ∧ post 4 = true   -- target_1 unchanged
    ∧ post 5 = false  -- carry_1 (undone via chain CX + CCX): was 1, after CX(carry_0=1, carry_1)=0, after CCX(r_1=0 ∧ t_1=1)=0 stays 0
    ∧ post 6 = false  -- read_2 (was 1, undone via CX with carry_1=1 → flipped to 0)
    ∧ post 7 = true   -- target_2 (was 0 after CX, now 0 ⊕ carry_1(was 1, now updated) — needs careful eval)
    ∧ post 8 = false  -- carry_2 unchanged
    := by decide

/-- **Smoke test on `inputF_7_plus_1`**: starting from the
    post-(forward+final-CX) state of the 4-bit (a=7, b=1) adder,
    apply the last-bit reverse at i=3. The chain CX flips carry_3
    from 0 to 1 (since carry_2=1); the CCX undo then conditions on
    (read_3=1, target_3=0) → AND=false, so carry_3 stays at 1.
    Verify the post-state at all 12 qubits via decide. -/
example :
    let prev := gidney_final_cx_cascade_post_state 4
                (gidney_forward_faithful_full_post_state 4 inputF_7_plus_1)
    let post := gidney_last_bit_reverse_post_state 3 prev
    -- The last-bit reverse at i=3 only touches carry_3 (qubit 11).
    -- All other qubits remain at their post-final-CX values.
    post 0 = true     -- read_0 unchanged
    ∧ post 1 = false  -- target_0 unchanged (sum bit 0)
    ∧ post 2 = true   -- carry_0 unchanged
    ∧ post 3 = false  -- read_1 unchanged
    ∧ post 4 = true   -- target_1 unchanged
    ∧ post 5 = true   -- carry_1 unchanged
    ∧ post 6 = false  -- read_2 unchanged
    ∧ post 7 = true   -- target_2 unchanged
    ∧ post 8 = true   -- carry_2 unchanged
    ∧ post 9 = true   -- read_3 unchanged
    ∧ post 10 = false -- target_3 unchanged (pre full reverse cascade)
    ∧ post 11 = true  -- carry_3: was 0, after CX with carry_2=1 → 1, after CCX (read_3=1 ∧ target_3=0)=0 → stays 1
    := by decide

/-- **Smoke lemma**: carry with carry-in zero, both inputs zero,
    yields zero. SQIR's `carry_false_0_l` analog
    ([ModMult.v:514](../../../SQIR/examples/shor/ModMult.v)). -/
theorem Adder.carry_false_zero (n : Nat) :
    Adder.carry false n (fun _ => false) (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ k ih =>
      unfold Adder.carry
      simp [ih]

/-- **Smoke lemma**: carry is symmetric in its two bit-stream
    arguments. SQIR's `carry_sym` analog
    ([ModMult.v:506](../../../SQIR/examples/shor/ModMult.v)). -/
theorem Adder.carry_sym (b₀ : Bool) (n : Nat) (f g : Nat → Bool) :
    Adder.carry b₀ n f g = Adder.carry b₀ n g f := by
  induction n with
  | zero => rfl
  | succ k ih =>
      unfold Adder.carry
      rw [ih]
      -- (f k && g k) ⊕ (g k && c) ⊕ (f k && c)
      --   = (g k && f k) ⊕ (f k && c) ⊕ (g k && c)
      -- by Bool.xor_comm + Bool.and_comm
      cases f k <;> cases g k <;> cases Adder.carry b₀ k g f <;> decide

/-- **Smoke lemma**: sum-bit at position 0 with carry-in zero is
    just `f 0 ⊕ g 0`. Direct from def + carry's base case. -/
theorem Adder.sumfb_zero (f g : Nat → Bool) :
    Adder.sumfb false f g 0 = xor (f 0) (g 0) := by
  unfold Adder.sumfb Adder.carry
  cases f 0 <;> cases g 0 <;> decide

/-- **Carry recurrence in explicit form**: `Adder.carry b₀ (n+1) f g`
    equals `MAJ(f n, g n, Adder.carry b₀ n f g)` written out via XOR
    and AND. Auxiliary lemma for downstream proofs that need the
    recurrence as a rewrite rule (rather than via `unfold`, which
    expands too aggressively). -/
theorem Adder.carry_succ (b₀ : Bool) (n : Nat) (f g : Nat → Bool) :
    Adder.carry b₀ (n + 1) f g
      = xor (xor (f n && g n) (g n && Adder.carry b₀ n f g))
            (f n && Adder.carry b₀ n f g) := rfl

/-! ### Classical-correctness bridge: `sumfb` ↔ `Nat.testBit` (Iter 158)

    SQIR's
    [`sumfb_correct_carry0`](../../../SQIR/examples/shor/ModMult.v:769)
    is the load-bearing classical lemma:

    ```
    Lemma sumfb_correct_carry0 :
      forall x y, sumfb false (nat2fb x) (nat2fb y) = nat2fb (x + y).
    ```

    It says: the bit-level sum (`Adder.sumfb`) on the bit-streams
    of two Nats equals the bit-stream of their integer sum.
    Combined with "quantum cascade preserves the bit-level invariant"
    (to be proven in later ticks), this gives the headline
    semantic correctness theorem.

    This tick STATES the lemma + decide-witnesses on small (a, b, i).
    The full proof needs an inductive argument coupling
    `Nat.testBit (a+b) i` to the recursive carry computation —
    Mathlib doesn't expose a direct `testBit_add` lemma, so the
    proof is non-trivial.

    Named-sorried as `TODO_sumfb_eq_testBit_add`. Future ticks
    close it via induction on `i` with `Nat.shiftRight_succ` +
    case analysis on the bottom bits of `a` and `b`. -/

/-- **Base case of the classical-correctness bridge** (Iter 163,
    new):  `(a + b).testBit 0 = a.testBit 0 ⊕ b.testBit 0`.

    This is the i=0 specialization of
    `Adder.sumfb_eq_testBit_add`. The proof goes via Nat's
    mod-2 arithmetic: `Nat.testBit n 0 ↔ n % 2 = 1`, and
    `(a + b) % 2 = (a % 2 + b % 2) % 2` (which equals
    `a % 2 ⊕ b % 2` for Bool-valued mods).

    This closes the base case of the planned induction on i for
    `TODO_sumfb_eq_testBit_add`. -/
theorem Adder.testBit_add_zero (a b : Nat) :
    (a + b).testBit 0 = xor (a.testBit 0) (b.testBit 0) := by
  -- Nat.testBit_zero : n.testBit 0 = decide (n % 2 = 1) — or
  -- the equivalent boolean form. Let's use simp + omega via
  -- mod-2 case analysis.
  simp only [Nat.testBit_zero]
  -- Goal: ((a + b) % 2 == 1) = ((a % 2 == 1) ⊕ (b % 2 == 1))
  -- (or similar form). Case-split on (a % 2) and (b % 2).
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hab : (a + b) % 2 = 0 ∨ (a + b) % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hab with hab | hab <;>
    simp_all <;> omega

/-- **Carry-shift auxiliary lemma** (Iter 199, 2026-05-13). Relates
    `Adder.carry b₀ (k+1)` on (a, b) to `Adder.carry initial k` on
    (a/2, b/2), where `initial = Adder.carry b₀ 1 a b = MAJ(a_0, b_0, b₀)`.

    Proof by induction on k: the carry recurrence `carry _ (k+1) = MAJ(...)`
    + `Nat.testBit_add_one` gives `(a/2).testBit m = a.testBit (m+1)`. -/
lemma Adder.carry_shift_one (b₀ : Bool) (a b k : Nat) :
    Adder.carry b₀ (k + 1) (fun i => a.testBit i) (fun i => b.testBit i)
    = Adder.carry (Adder.carry b₀ 1 (fun i => a.testBit i) (fun i => b.testBit i))
        k (fun i => (a / 2).testBit i) (fun i => (b / 2).testBit i) := by
  induction k with
  | zero => rfl
  | succ m ih =>
      -- LHS: carry b₀ (m+2) ab = MAJ(a_{m+1}, b_{m+1}, carry b₀ (m+1) ab)
      -- RHS (m+1): carry init (m+1) (a/2)bit (b/2)bit
      --         = MAJ((a/2)_m, (b/2)_m, carry init m ...)
      -- After unfolding both sides: substitute IH and testBit_add_one.
      rw [show m + 1 + 1 = m + 2 from rfl, Adder.carry_succ b₀ (m + 1),
          show (Adder.carry _ (m + 1) (fun i => (a / 2).testBit i)
                  (fun i => (b / 2).testBit i))
              = _ from Adder.carry_succ _ m _ _,
          ih, Nat.testBit_add_one a m, Nat.testBit_add_one b m]

/-- **Strengthened classical-correctness bridge with carry-in**
    (Iter 196, 2026-05-13). Generalizes `Adder.sumfb_eq_testBit_add`
    by adding a carry-in parameter `b₀ : Bool`, which lets the
    inductive step thread through `Nat.testBit_add_one` + `Nat.add_div`
    decomposition cleanly.

    Base case (i=0) is the existing `Adder.testBit_add_zero` analog
    extended with b₀; succ case is named-sorried per Iter 190's
    strategy doc (uses the gen IH applied to a/2, b/2, new carry-in
    derived from `Nat.add_div` decomposition). -/
theorem Adder.sumfb_eq_testBit_add_gen (b₀ : Bool) (a b i : Nat) :
    Adder.sumfb b₀ (fun k => a.testBit k) (fun k => b.testBit k) i
      = (a + b + b₀.toNat).testBit i := by
  induction i generalizing a b b₀ with
  | zero =>
      -- Base case: sumfb b₀ ab 0 = xor (xor b₀ a_0) b_0
      --          = (a + b + b₀.toNat).testBit 0
      -- Mod-2 case-bash on a%2, b%2, plus b₀: Bool.
      simp only [Adder.sumfb, Adder.carry, Nat.testBit_zero]
      have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
      have hb0 : b₀.toNat = 0 ∨ b₀.toNat = 1 := by
        cases b₀ <;> simp [Bool.toNat]
      have hsum : (a + b + b₀.toNat) % 2 = 0 ∨ (a + b + b₀.toNat) % 2 = 1 := by omega
      cases b₀ <;>
        (rcases ha with ha | ha <;> rcases hb with hb | hb <;>
         rcases hsum with hsum | hsum <;>
         simp_all [Bool.toNat] <;> omega)
  | succ k ih =>
      -- Strategy: apply IH with new args (carry b₀ 1 a b, a/2, b/2),
      -- using carry_shift_one + h_div arithmetic identity.
      have h_div : (a + b + b₀.toNat) / 2
                 = (a/2) + (b/2)
                   + (Adder.carry b₀ 1 (fun i => a.testBit i)
                        (fun i => b.testBit i)).toNat := by
        cases b₀ <;>
          rcases (show a % 2 = 0 ∨ a % 2 = 1 from by omega) with ha | ha <;>
          rcases (show b % 2 = 0 ∨ b % 2 = 1 from by omega) with hb | hb <;>
          simp [Adder.carry, Nat.testBit_zero, Bool.toNat, ha, hb] <;>
          omega
      rw [Nat.testBit_add_one, h_div, ← ih]
      -- Goal: sumfb b₀ a.testBit b.testBit (k+1) = sumfb (carry _) (a/2)bit (b/2)bit k
      -- Unfold sumfb on both sides, use carry_shift_one + testBit_add_one.
      show xor (xor (Adder.carry b₀ (k + 1) _ _) (a.testBit (k + 1))) (b.testBit (k + 1))
         = xor (xor (Adder.carry _ k _ _) ((a/2).testBit k)) ((b/2).testBit k)
      rw [Adder.carry_shift_one, Nat.testBit_add_one a k, Nat.testBit_add_one b k]

/-- **The classical-correctness bridge, parametric** (Iter 196 PROVEN
    via gen helper). `sumfb` on Nat-derived bit-streams equals
    `testBit (a+b)`. SQIR's `sumfb_correct_carry0` analog.

    Was sorried as `TODO_sumfb_eq_testBit_add` until Iter 196.
    Now derived from `Adder.sumfb_eq_testBit_add_gen` by specializing
    `b₀ = false` (and using `Bool.toNat false = 0`). Iter 196 also
    introduced a new sorry `TODO_sumfb_eq_testBit_add_gen_succ` for
    the gen-helper's succ case. Net sorry delta = 0; the new sorry
    has cleaner inductive structure. -/
theorem Adder.sumfb_eq_testBit_add (a b i : Nat) :
    Adder.sumfb false (fun k => a.testBit k) (fun k => b.testBit k) i
      = (a + b).testBit i := by
  -- Specialize the gen helper to b₀ = false (toNat = 0, so a + b + 0 = a + b).
  have h := Adder.sumfb_eq_testBit_add_gen false a b i
  simpa [Bool.toNat] using h

/-- **Small-instance validation** of the bridge at `(a=3, b=1)`.
    Sum = 4 = 0b100. Decide-witnesses confirm the statement
    `sumfb false ... i = (3+1).testBit i` for i = 0, 1, 2, 3. -/
example :
    Adder.sumfb false (fun k => (3 : Nat).testBit k)
                      (fun k => (1 : Nat).testBit k) 0
      = ((3 : Nat) + 1).testBit 0
    ∧ Adder.sumfb false (fun k => (3 : Nat).testBit k)
                        (fun k => (1 : Nat).testBit k) 1
        = ((3 : Nat) + 1).testBit 1
    ∧ Adder.sumfb false (fun k => (3 : Nat).testBit k)
                        (fun k => (1 : Nat).testBit k) 2
        = ((3 : Nat) + 1).testBit 2
    ∧ Adder.sumfb false (fun k => (3 : Nat).testBit k)
                        (fun k => (1 : Nat).testBit k) 3
        = ((3 : Nat) + 1).testBit 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold Adder.sumfb Adder.carry; decide)

/-- **Small-instance validation** at `(a=7, b=1)`. Sum = 8 = 0b1000.
    Bit 0/1/2 of 8 = false; bit 3 of 8 = true. -/
example :
    Adder.sumfb false (fun k => (7 : Nat).testBit k)
                      (fun k => (1 : Nat).testBit k) 0
      = ((7 : Nat) + 1).testBit 0
    ∧ Adder.sumfb false (fun k => (7 : Nat).testBit k)
                        (fun k => (1 : Nat).testBit k) 3
        = ((7 : Nat) + 1).testBit 3 := by
  refine ⟨?_, ?_⟩ <;> (unfold Adder.sumfb Adder.carry; decide)

/-- **Validation on the (7, 1) 4-bit case**: decide-witnesses that
    the invariant predicate is SATISFIED by the actual forward
    cascade post-state computed by
    `gidney_forward_faithful_full_post_state 4 inputF_7_plus_1`.

    This confirms the invariant statement matches the observed
    post-state (Iter 116's decide-table). The parametric "for all
    `a b n`" claim will be a separate SORRIED theorem below. -/
example :
    Gidney.forward_cascade_post_invariant 4 7 1
      (gidney_forward_faithful_full_post_state 4 inputF_7_plus_1) := by
  intro i hi
  -- Case-split on i: 4 cases (0, 1, 2, 3). Manual match since
  -- `interval_cases` is not imported in this file.
  match i, hi with
  | 0, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 2, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 3, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | _ + 4, hbig => omega

/-- **Validation on (3, 1) n=3 k=1**: after the first-bit step
    (k=1) on `adder_input_F 3 3 1`, the propagation invariant
    holds at all 3 positions. Decide-witness via manual match. -/
example :
    Gidney.propagation_step_invariant 1 3 3 1
      (gidney_propagation_post_state 1 (adder_input_F 3 3 1)) := by
  intro j hj
  match j, hj with
  | 0, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 2, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | _ + 3, h => omega

/- **`TODO_gidney_forward_cascade_invariant` REMOVED (Iter 214,
   2026-05-13)**. Originally sorried at this location (Iter 159), the
   theorem `forward_cascade_post_invariant` was superseded by Iter 188-189's
   `Gidney.post_last_bit_invariant_holds`, which is FULLY PROVEN
   parametrically and captures the same content (modulo the predicate
   choice). The `Gidney.forward_cascade_post_invariant` def above
   remains as historical record of the original Iter 159 attempt. -/

/-! ### Per-bit-step preservation lemma skeletons (Iter 160, 2026-05-13)

    Per the proof decomposition in AutoScript/goal.md, the
    SQIR-style induction over n requires per-bit-step preservation
    lemmas. Three step types (first / interior / last), each takes
    a step-i invariant + the corresponding gate-step's classical
    action (`gidney_first_bit_post_state`, etc.) and produces the
    step-(i+1) invariant.

    This tick STATES the three preservation lemmas as named
    placeholders. Future ticks prove each (likely via case analysis
    on `a_i`, `b_i`, `c_i` — each `Bool` has 2 values, so 8 inner
    cases per step type, decide-able once unfolded).

    These follow SQIR's MAJseq'_correct induction structure:
    base case = first-bit-step preservation (analog of MAJ at i=0);
    inductive step = interior-bit preservation (analog of MAJ at i+1).
    Last-bit step is the n=n termination, no analog needed in SQIR
    because Cuccaro is uniform. -/

/-- **Preliminary lemma** (partial — bottom 3 positions only):
    `adder_input_F n a b` evaluates as expected at qubit indices
    0, 1, 2 (positions handled by the first-bit step). -/
theorem adder_input_F_at_bottom (n a b : Nat) :
    adder_input_F n a b 2 = false := rfl

/-- **`adder_input_F` at `read_idx j`**: evaluates to
    `a.testBit j` when `j < n`. -/
theorem adder_input_F_at_read_idx
    (n a b j : Nat) (hj : j < n) :
    adder_input_F n a b (read_idx j) = a.testBit j := by
  have h_mod : (read_idx j) % 3 = 0 := by unfold read_idx; omega
  have h_div : (read_idx j) / 3 = j := by unfold read_idx; omega
  show (match (read_idx j) % 3 with
        | 0 => decide ((read_idx j) / 3 < n) && a.testBit ((read_idx j) / 3)
        | 1 => decide ((read_idx j) / 3 < n) && b.testBit ((read_idx j) / 3)
        | _ => false) = a.testBit j
  rw [h_mod, h_div]
  simp [hj]

/-- **`adder_input_F` at `target_idx j`**: evaluates to
    `b.testBit j` when `j < n`. -/
theorem adder_input_F_at_target_idx
    (n a b j : Nat) (hj : j < n) :
    adder_input_F n a b (target_idx j) = b.testBit j := by
  have h_mod : (target_idx j) % 3 = 1 := by unfold target_idx; omega
  have h_div : (target_idx j) / 3 = j := by unfold target_idx; omega
  show (match (target_idx j) % 3 with
        | 0 => decide ((target_idx j) / 3 < n) && a.testBit ((target_idx j) / 3)
        | 1 => decide ((target_idx j) / 3 < n) && b.testBit ((target_idx j) / 3)
        | _ => false) = b.testBit j
  rw [h_mod, h_div]
  simp [hj]

/-- **`adder_input_F` at `carry_idx j`**: always `false` (carry
    register starts clean). No bound on `j` needed. -/
theorem adder_input_F_at_carry_idx
    (n a b j : Nat) :
    adder_input_F n a b (carry_idx j) = false := by
  have h_mod : (carry_idx j) % 3 = 2 := by unfold carry_idx; omega
  show (match (carry_idx j) % 3 with
        | 0 => decide ((carry_idx j) / 3 < n) && a.testBit ((carry_idx j) / 3)
        | 1 => decide ((carry_idx j) / 3 < n) && b.testBit ((carry_idx j) / 3)
        | _ => false) = false
  rw [h_mod]

/-- **`adder_input_F` evaluation at the 5 first-bit-step positions**
    (Iter 165). Closes the gap between `adder_input_F n a b` (which
    is parameterized by Nat `n a b`) and `(a.testBit 0, b.testBit 0,
    false, a.testBit 1, b.testBit 1)` (which is pure Bool).

    The hypothesis `hn : 1 < n` is needed for positions 3 and 4
    (where `k / 3 = 1`, so `decide (1 < n) = true` is required to
    reduce the `decide` guard).

    Together with `gidney_first_bit_post_state_in_bits` (Iter 164),
    this unblocks the proof of `TODO_gidney_first_bit_preserves`. -/
theorem adder_input_F_at_first_bit_positions
    (n a b : Nat) (hn : 1 < n) :
    adder_input_F n a b 0 = a.testBit 0
    ∧ adder_input_F n a b 1 = b.testBit 0
    ∧ adder_input_F n a b 2 = false
    ∧ adder_input_F n a b 3 = a.testBit 1
    ∧ adder_input_F n a b 4 = b.testBit 1 := by
  have h0 : (0 : Nat) < n := by omega
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · -- adder_input_F at 0: match 0%3=0, so `decide (0<n) && a.testBit 0`
    show (decide (0 < n) && a.testBit 0) = a.testBit 0
    simp [h0]
  · show (decide (0 < n) && b.testBit 0) = b.testBit 0
    simp [h0]
  · show (decide (1 < n) && a.testBit 1) = a.testBit 1
    simp [hn]
  · show (decide (1 < n) && b.testBit 1) = b.testBit 1
    simp [hn]

/-- **Base case k=0 of the cascade induction** (Iter 176, PROVEN).
    The invariant `Gidney.propagation_step_invariant 0 n a b`
    holds for the input `adder_input_F n a b`.

    `propagation_post_state 0 f = f`, so this reduces to showing
    `adder_input_F` has the right values at all positions. Uses
    the 3 evaluation lemmas above. -/
theorem Gidney.propagation_step_invariant_base_k0
    (n a b : Nat) (_ha : a < 2^n) (_hb : b < 2^n) :
    Gidney.propagation_step_invariant 0 n a b
      (gidney_propagation_post_state 0 (adder_input_F n a b)) := by
  show Gidney.propagation_step_invariant 0 n a b (adder_input_F n a b)
  intro j hj
  refine ⟨?_, ?_, ?_⟩
  · rw [adder_input_F_at_carry_idx]
    simp  -- j < 0 is false
  · rw [adder_input_F_at_read_idx _ _ _ _ hj]
    by_cases hj0 : j ≤ 0
    · have : j = 0 := by omega
      subst this
      simp [Adder.carry]
    · simp [hj0]
  · rw [adder_input_F_at_target_idx _ _ _ _ hj]
    by_cases hj0 : j ≤ 0
    · have : j = 0 := by omega
      subst this
      simp [Adder.carry]
    · simp [hj0]

-- Gidney.propagation_step_invariant_k1 moved to after
-- gidney_first_bit_preserves below (forward-reference fix).

/-- **Last-bit smoke-test** (Iter 169): apply `gidney_last_bit_post_state` at
    i=1 to the post-first-bit state of `inputF_1_plus_1` (2-bit adder).
    Expected: carry_1 = MAJ(0, 0, 1) = 0 (chain CX cancels CCX write).

    Note: `gidney_last_bit_post_state` was originally defined at
    line 1081 (Iter 67). This tick adds the bit-extraction lemma. -/
example :
    let pre := gidney_first_bit_post_state inputF_1_plus_1
    let post := gidney_last_bit_post_state 1 pre
    post (carry_idx 1) = false
    := by decide

/-- **Bit-extraction helper for last-bit step** (Iter 169).
    Mirrors Iter 164 (first-bit) and Iter 167 (interior). Last
    step has only 2 gates; single conjunct (only carry_i is
    touched). -/
theorem gidney_last_bit_post_state_in_bits
    (i : Nat) (hi : 0 < i) (f : Nat → Bool)
    (h_cinit : f (carry_idx i) = false) :
    (gidney_last_bit_post_state i f) (carry_idx i)
      = xor (f (read_idx i) && f (target_idx i)) (f (carry_idx (i - 1))) := by
  have h_cim1_ci : carry_idx (i - 1) ≠ carry_idx i := by
    unfold carry_idx; omega
  unfold gidney_last_bit_post_state
  -- 2 updates: gate 1 (CCX writes c_i), gate 2 (chain CX adds c_{i-1}).
  rw [update_eq,                              -- f₂ at c_i = (f₁ at c_i) ⊕ (f₁ at c_{i-1})
      update_eq,                              -- f₁ at c_i = f(c_i) ⊕ (f(r_i) ∧ f(t_i))
      update_neq _ _ _ _ h_cim1_ci,         -- f₁ at c_{i-1} = f at c_{i-1}
      h_cinit]
  simp

/-! ### Frame conditions for per-step actions (Iter 173)

    For cascade composition we need to know which positions each
    step-type modifies. Each step's post-state def is a chain of
    `update` calls; positions OUTSIDE the touched set retain the
    input value (via `update_neq`).

    These frame conditions are building blocks for the
    forward-cascade composition theorem (`TODO_gidney_forward_cascade_invariant`).
    Each is a small omega + `update_neq` proof. -/

/-- **First-bit step frame condition**: positions other than
    {carry_0, read_1, target_1} (= {2, 3, 4}) are unchanged. -/
theorem gidney_first_bit_post_state_preserves_outside
    (f : Nat → Bool) (k : Nat)
    (h_c0 : k ≠ carry_idx 0)
    (h_r1 : k ≠ read_idx 1)
    (h_t1 : k ≠ target_idx 1) :
    (gidney_first_bit_post_state f) k = f k := by
  unfold gidney_first_bit_post_state
  rw [update_neq _ _ _ _ h_t1, update_neq _ _ _ _ h_r1,
      update_neq _ _ _ _ h_c0]

/-- **Last-bit step frame condition**: positions other than
    {carry_i} are unchanged. (Last-bit only writes to carry_i.) -/
theorem gidney_last_bit_post_state_preserves_outside
    (i : Nat) (f : Nat → Bool) (k : Nat)
    (h_ci : k ≠ carry_idx i) :
    (gidney_last_bit_post_state i f) k = f k := by
  unfold gidney_last_bit_post_state
  rw [update_neq _ _ _ _ h_ci, update_neq _ _ _ _ h_ci]

/-- **Last-bit-step preservation theorem (PROVEN, Iter 171)**.
    Adapter from Iter 169's bit-extraction helper to the
    carry recurrence. Simpler than interior (no propagation).

    Given a state `f` satisfying the "step (i-1) END invariant"
    (i.e., position i-1 fully processed, position i clean):
    - `f(read_i) = a_i ⊕ c`, `f(target_i) = b_i ⊕ c`
    - `f(carry_{i-1}) = c` where `c = Adder.carry false i a.testBit b.testBit`
    - `f(carry_i) = false`

    Applying `gidney_last_bit_post_state i` yields:
    - `post(carry_i) = c_{i+1} = Adder.carry false (i+1) a.testBit b.testBit`

    No propagation to position (i+1) since this is the last bit.
    The carry-out identity `((a⊕c) ∧ (b⊕c)) ⊕ c = MAJ(a,b,c)` is
    the same as interior. -/
theorem gidney_last_bit_preserves (i a b : Nat) (hi : 0 < i) (f : Nat → Bool)
    (h_ri : f (read_idx i)
              = xor (a.testBit i) (Adder.carry false i a.testBit b.testBit))
    (h_ti : f (target_idx i)
              = xor (b.testBit i) (Adder.carry false i a.testBit b.testBit))
    (h_cim1 : f (carry_idx (i - 1))
                = Adder.carry false i a.testBit b.testBit)
    (h_ci : f (carry_idx i) = false) :
    (gidney_last_bit_post_state i f) (carry_idx i)
      = Adder.carry false (i + 1) a.testBit b.testBit := by
  rw [gidney_last_bit_post_state_in_bits i hi f h_ci, h_ri, h_ti, h_cim1,
      Adder.carry_succ]
  generalize Adder.carry false i a.testBit b.testBit = c
  cases a.testBit i <;> cases b.testBit i <;> cases c <;> rfl

/-- **Smoke-test**: `gidney_interior_bit_post_state 1` on the
    (3, 1) 3-bit input matches the existing decide-witnessed
    post-state. Validates the def's correctness on a concrete
    instance before attempting the parametric bit-extraction
    proof. -/
example :
    -- The interior step at i=1 transforms inputF_3_plus_1's post-first-bit state.
    -- inputF_3_plus_1 (a=3, b=1) → first-bit step → interior step at i=1.
    let post_first := gidney_first_bit_post_state inputF_3_plus_1
    let post_interior := gidney_interior_bit_post_state 1 post_first
    -- Expected at i=1: carry_1 = c_2 = MAJ(a_1, b_1, c_1) = MAJ(1, 0, 1) = 1.
    -- read_2 = a_2 ⊕ c_2 = 0 ⊕ 1 = 1.  But wait a_2 for a=3 is bit 2 = 0.
    -- target_2 = b_2 ⊕ c_2 = 0 ⊕ 1 = 1.
    post_interior (carry_idx 1) = true   -- c_2 = 1
    ∧ post_interior (read_idx 2) = true  -- a_2 ⊕ c_2 = 0 ⊕ 1 = 1
    ∧ post_interior (target_idx 2) = true -- b_2 ⊕ c_2 = 0 ⊕ 1 = 1
    := by decide

/-- **Bridge lemma** (Iter 172): the Iter 166-defined
    `gidney_interior_bit_post_state` is identical to the existing
    `gidney_bit_step_faithful_post_state` (line 570) used by the
    propagation cascade. Same 4-update body. Provable by `rfl`.

    Iter 166 inadvertently introduced this duplicate def. The
    bridge lets us apply Iter 170's `gidney_interior_bit_preserves`
    (which uses the Iter 166 name) to the cascade's interior steps
    (which use the existing name). -/
theorem gidney_interior_bit_post_state_eq
    (i : Nat) (f : Nat → Bool) :
    gidney_interior_bit_post_state i f
      = gidney_bit_step_faithful_post_state i f := rfl

/-- **Interior-bit step frame condition** (Iter 173): positions
    other than {carry_i, read_{i+1}, target_{i+1}} are unchanged
    by the interior-bit step at position `i`. -/
theorem gidney_interior_bit_post_state_preserves_outside
    (i : Nat) (f : Nat → Bool) (k : Nat)
    (h_ci : k ≠ carry_idx i)
    (h_ri1 : k ≠ read_idx (i + 1))
    (h_ti1 : k ≠ target_idx (i + 1)) :
    (gidney_interior_bit_post_state i f) k = f k := by
  unfold gidney_interior_bit_post_state
  rw [update_neq _ _ _ _ h_ti1, update_neq _ _ _ _ h_ri1,
      update_neq _ _ _ _ h_ci, update_neq _ _ _ _ h_ci]

/-- **Bit-extraction helper for interior step** (Iter 167, PROVEN).
    Analog of Iter 164's first-bit version. Proven via `omega`-
    derived index inequalities + `update_neq` chain. -/
theorem gidney_interior_bit_post_state_in_bits
    (i : Nat) (hi : 0 < i) (f : Nat → Bool)
    (h_cinit : f (carry_idx i) = false) :
    (gidney_interior_bit_post_state i f) (carry_idx i)
      = xor (f (read_idx i) && f (target_idx i)) (f (carry_idx (i - 1)))
    ∧ (gidney_interior_bit_post_state i f) (read_idx (i + 1))
        = xor (f (read_idx (i + 1)))
              ((gidney_interior_bit_post_state i f) (carry_idx i))
    ∧ (gidney_interior_bit_post_state i f) (target_idx (i + 1))
        = xor (f (target_idx (i + 1)))
              ((gidney_interior_bit_post_state i f) (carry_idx i)) := by
  -- Index inequalities (omega over read_idx i = 3i, target_idx i = 3i+1,
  -- carry_idx i = 3i+2, etc., with hi : 0 < i).
  have h_ri_ci : read_idx i ≠ carry_idx i := by
    unfold read_idx carry_idx; omega
  have h_ti_ci : target_idx i ≠ carry_idx i := by
    unfold target_idx carry_idx; omega
  have h_cim1_ci : carry_idx (i - 1) ≠ carry_idx i := by
    unfold carry_idx; omega
  have h_ri1_ci : read_idx (i + 1) ≠ carry_idx i := by
    unfold read_idx carry_idx; omega
  have h_ti1_ci : target_idx (i + 1) ≠ carry_idx i := by
    unfold target_idx carry_idx; omega
  have h_ti1_ri1 : target_idx (i + 1) ≠ read_idx (i + 1) := by
    unfold target_idx read_idx; omega
  unfold gidney_interior_bit_post_state
  refine ⟨?_, ?_, ?_⟩
  · -- post(carry_i): chain through 4 updates, picking up gate-1+gate-2 writes.
    rw [update_neq _ _ _ _ h_ti1_ci.symm,   -- f₄: gate 4 update at target_{i+1}, not carry_i
        update_neq _ _ _ _ h_ri1_ci.symm,   -- f₃: gate 3 update at read_{i+1}, not carry_i
        update_eq,                             -- f₂: gate 2 update at carry_i (hit!)
        update_eq,                             -- f₁: gate 1 update at carry_i (hit!)
        update_neq _ _ _ _ h_cim1_ci,        -- f₁ query at carry_{i-1} not c_i (no .symm!)
        h_cinit]
    simp
  · -- post(read_{i+1}): gate 4 doesn't touch r_{i+1}; gate 3 writes there.
    rw [update_neq _ _ _ _ h_ti1_ri1.symm,  -- f₄: gate 4 at target_{i+1}, not r_{i+1}
        update_eq]                             -- f₃: gate 3 at r_{i+1} (hit!)
    -- f₂(r_{i+1}) = f(r_{i+1}) via update_neq through gates 1 + 2 (which update c_i).
    rw [update_neq _ _ _ _ h_ri1_ci, update_neq _ _ _ _ h_ri1_ci]
    -- Goal: xor (f r_{i+1}) (f₂ c_i) = xor (f r_{i+1}) (post c_i)
    -- where post c_i in the outer goal = f₄ c_i. Show they're equal via congr.
    congr 1
    rw [update_neq _ _ _ _ h_ti1_ci.symm, update_neq _ _ _ _ h_ri1_ci.symm]
  · -- post(target_{i+1}): gate 4 writes there.
    rw [update_eq]                             -- f₄: gate 4 at t_{i+1} (hit!)
    -- f₃(t_{i+1}) chain: f₂(t_{i+1}) ← f₁(t_{i+1}) ← f(t_{i+1}).
    rw [update_neq _ _ _ _ h_ti1_ri1,        -- f₃: gate 3 at r_{i+1} ≠ t_{i+1}
        update_neq _ _ _ _ h_ti1_ci,         -- f₂: gate 2 at c_i ≠ t_{i+1}
        update_neq _ _ _ _ h_ti1_ci]          -- f₁: gate 1 at c_i ≠ t_{i+1}
    -- f₃(c_i): gate 3 at r_{i+1} ≠ c_i, so f₃(c_i) = f₂(c_i).
    rw [update_neq _ _ _ _ h_ri1_ci.symm]
    -- Goal: xor (f t_{i+1}) (f₂ c_i) = xor (f t_{i+1}) (post c_i)
    congr 1
    rw [update_neq _ _ _ _ h_ti1_ci.symm, update_neq _ _ _ _ h_ri1_ci.symm]

/-- **Interior-bit-step preservation theorem (PROVEN, Iter 170)**.
    Adapter from Iter 167's bit-extraction helper to the
    classical-carry-recurrence form.

    Given a state `f` satisfying the "step (i-1) END invariant":
    - `f(read_i) = a_i ⊕ c`, `f(target_i) = b_i ⊕ c` (propagated by prev step)
    - `f(carry_{i-1}) = c` (carry from prev step)
    - `f(carry_i) = false` (carry register unmodified up to position i)
    - `f(read_{i+1}) = a_{i+1}`, `f(target_{i+1}) = b_{i+1}` (unchanged from input)

    Applying `gidney_interior_bit_post_state i` yields a state
    satisfying the "step i END invariant":
    - `post(carry_i) = c_{i+1} = Adder.carry false (i+1) a.testBit b.testBit`
    - `post(read_{i+1}) = a_{i+1} ⊕ c_{i+1}`
    - `post(target_{i+1}) = b_{i+1} ⊕ c_{i+1}`

    The carry-out identity: `((a_i ⊕ c) ∧ (b_i ⊕ c)) ⊕ c = MAJ(a_i, b_i, c)`. -/
theorem gidney_interior_bit_preserves (i a b : Nat) (hi : 0 < i) (f : Nat → Bool)
    (h_ri : f (read_idx i)
              = xor (a.testBit i) (Adder.carry false i a.testBit b.testBit))
    (h_ti : f (target_idx i)
              = xor (b.testBit i) (Adder.carry false i a.testBit b.testBit))
    (h_cim1 : f (carry_idx (i - 1))
                = Adder.carry false i a.testBit b.testBit)
    (h_ci : f (carry_idx i) = false)
    (h_ri1 : f (read_idx (i + 1)) = a.testBit (i + 1))
    (h_ti1 : f (target_idx (i + 1)) = b.testBit (i + 1)) :
    let post := gidney_interior_bit_post_state i f
    post (carry_idx i) = Adder.carry false (i + 1) a.testBit b.testBit
    ∧ post (read_idx (i + 1))
        = xor (a.testBit (i + 1)) (Adder.carry false (i + 1) a.testBit b.testBit)
    ∧ post (target_idx (i + 1))
        = xor (b.testBit (i + 1)) (Adder.carry false (i + 1) a.testBit b.testBit)
    := by
  -- Apply the in-bits helper (Iter 167).
  obtain ⟨hp_c, hp_r, hp_t⟩ :=
    gidney_interior_bit_post_state_in_bits i hi f h_ci
  -- Substitute the input hypotheses into hp_c.
  rw [h_ri, h_ti, h_cim1] at hp_c
  -- Now hp_c : post(c_i) = ((a_i ⊕ c) ∧ (b_i ⊕ c)) ⊕ c
  --   where c = Adder.carry false i a.testBit b.testBit
  -- We need: post(c_i) = Adder.carry false (i+1) a.testBit b.testBit
  --        = MAJ(a_i, b_i, c)
  -- Prove the carry equality first; read/target follow.
  have h_carry : (gidney_interior_bit_post_state i f) (carry_idx i)
                  = Adder.carry false (i + 1) a.testBit b.testBit := by
    rw [hp_c, Adder.carry_succ]
    -- LHS: ((a_i ⊕ c) ∧ (b_i ⊕ c)) ⊕ c
    -- RHS: (a_i ∧ b_i) ⊕ (b_i ∧ c) ⊕ (a_i ∧ c)   where c = Adder.carry false i ...
    -- Both are MAJ(a_i, b_i, c). Generalize c to a free Bool var, case-bash.
    generalize Adder.carry false i a.testBit b.testBit = c
    cases a.testBit i <;> cases b.testBit i <;> cases c <;> rfl
  refine ⟨h_carry, ?_, ?_⟩
  · -- post(read_{i+1}) = f(read_{i+1}) ⊕ post(carry_i) = a_{i+1} ⊕ c_{i+1}
    rw [hp_r, h_ri1, h_carry]
  · -- post(target_{i+1}) = f(target_{i+1}) ⊕ post(carry_i) = b_{i+1} ⊕ c_{i+1}
    rw [hp_t, h_ti1, h_carry]

/-- **Bit-extraction helper for first-bit step** (Iter 164):
    captures the classical action of `gidney_first_bit_post_state`
    on an arbitrary input function `f`, parameterized by the 5
    relevant bit values at positions 0, 1, 2, 3, 4.

    Per Iter 162 reflection pattern A (bit-extraction): take
    Bool values as inputs, NOT a free Nat. This avoids the
    "decide on free Nat vars" obstacle entirely — the proof is
    pure Bool case-analysis (16 sub-goals over the 4 free Bool
    vars).

    The relationship: `gidney_first_bit_post_state f` at
    positions 2 (carry_0), 3 (read_1), 4 (target_1):
    - post 2 = f 0 ∧ f 1                       (CCX write)
    - post 3 = f 3 ⊕ (f 0 ∧ f 1)               (CX propagation)
    - post 4 = f 4 ⊕ (f 0 ∧ f 1)               (CX propagation)

    Note `f 2` (= carry_0's initial value) is XOR'd into the
    CCX write, but for our adder input `f 2 = false`, so the
    XOR is trivial. We absorb this via `h2 : f 2 = false`. -/
theorem gidney_first_bit_post_state_in_bits
    (f : Nat → Bool) (h2 : f 2 = false) :
    (gidney_first_bit_post_state f) 2 = (f 0 && f 1)
    ∧ (gidney_first_bit_post_state f) 3 = xor (f 3) (f 0 && f 1)
    ∧ (gidney_first_bit_post_state f) 4 = xor (f 4) (f 0 && f 1) := by
  -- Unfold gidney_first_bit_post_state. It's 3 nested updates at positions
  -- 2 (carry_idx 0), 3 (read_idx 1), 4 (target_idx 1).
  -- Use the project's update_apply theorem (definitional unfolding).
  unfold gidney_first_bit_post_state
  simp only [carry_idx, read_idx, target_idx, update_apply,
             show (3 : Nat) * 0 = 0 from rfl,
             show (3 : Nat) * 1 = 3 from rfl,
             show (3 : Nat) * 0 + 1 = 1 from rfl,
             show (3 : Nat) * 0 + 2 = 2 from rfl,
             show (3 : Nat) * 1 + 1 = 4 from rfl,
             h2]
  refine ⟨?_, ?_, ?_⟩ <;>
    (cases f 0 <;> cases f 1 <;> cases f 3 <;> cases f 4 <;> decide)

/-- **First-bit-step preservation theorem (PROVEN, Iter 165)**:
    applying `gidney_first_bit_post_state` to the encoded input
    `adder_input_F n a b` (with `n ≥ 2`) produces a state where
    `carry_0 = c_1`, `read_1 = a_1 ⊕ c_1`, `target_1 = b_1 ⊕ c_1`,
    where `c_1 = Adder.carry false 1 (a.testBit) (b.testBit) =
    a_0 ∧ b_0`.

    **Proof** (post Iter 162 reflection's pattern A bit-extraction):
    glue `gidney_first_bit_post_state_in_bits` (Iter 164, pure
    Bool case-bash) with `adder_input_F_at_first_bit_positions`
    (Iter 165 preliminary, uses `hn : 1 < n` to evaluate the
    `decide` guards).

    Closes the original `TODO_gidney_first_bit_preserves` from
    Iter 160. -/
theorem gidney_first_bit_preserves (n a b : Nat)
    (hn : 1 < n) (_ha : a < 2^n) (_hb : b < 2^n) :
    let post := gidney_first_bit_post_state (adder_input_F n a b)
    post (carry_idx 0)
      = Adder.carry false 1 (a.testBit) (b.testBit)
    ∧ post (read_idx 1)
      = xor (a.testBit 1) (Adder.carry false 1 (a.testBit) (b.testBit))
    ∧ post (target_idx 1)
      = xor (b.testBit 1) (Adder.carry false 1 (a.testBit) (b.testBit)) := by
  -- Pull out the 5 input bit values via Iter 165 helper.
  obtain ⟨h0, h1, h2, h3, h4⟩ :=
    adder_input_F_at_first_bit_positions n a b hn
  -- Apply Iter 164 bit-extraction helper. Need h2 : f 2 = false.
  have hpost := gidney_first_bit_post_state_in_bits (adder_input_F n a b) h2
  -- hpost gives the post-state at positions 2, 3, 4 in terms of f 0, 1, 3, 4.
  -- Substitute f 0 = a.testBit 0, f 1 = b.testBit 0, f 3 = a.testBit 1, f 4 = b.testBit 1.
  rw [h0, h1, h3, h4] at hpost
  -- carry_idx 0 = 2, read_idx 1 = 3, target_idx 1 = 4. Unfold positions.
  show gidney_first_bit_post_state (adder_input_F n a b) 2 = _
    ∧ gidney_first_bit_post_state (adder_input_F n a b) 3 = _
    ∧ gidney_first_bit_post_state (adder_input_F n a b) 4 = _
  -- Adder.carry false 1 = a.testBit 0 && b.testBit 0 (unfold the recursion).
  -- hpost says post 2 = a.testBit 0 && b.testBit 0, post 3 = xor (a.testBit 1) (a.testBit 0 && b.testBit 0), etc.
  -- The RHS uses `Adder.carry false 1 a.testBit b.testBit` which unfolds to same expression.
  refine ⟨?_, ?_, ?_⟩
  · rw [hpost.1]
    -- Goal: a.testBit 0 && b.testBit 0 = Adder.carry false 1 a.testBit b.testBit
    unfold Adder.carry
    -- Adder.carry false 0 ... = false; then (a0 ∧ b0) ⊕ (b0 ∧ false) ⊕ (a0 ∧ false) = a0 ∧ b0
    cases a.testBit 0 <;> cases b.testBit 0 <;> rfl
  · rw [hpost.2.1]
    unfold Adder.carry
    cases a.testBit 0 <;> cases b.testBit 0 <;> cases a.testBit 1 <;> rfl
  · rw [hpost.2.2]
    unfold Adder.carry
    cases a.testBit 0 <;> cases b.testBit 0 <;> cases b.testBit 1 <;> rfl

/-- **Inductive step k=0 → k=1 of cascade induction** (Iter 177, PROVEN).
    Applying `gidney_first_bit_post_state` to `adder_input_F n a b`
    produces a state satisfying step-1 invariant. Uses
    `gidney_first_bit_preserves` (touched positions) + frame
    condition + adder_input_F evaluations (outside positions). -/
theorem Gidney.propagation_step_invariant_k1
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    Gidney.propagation_step_invariant 1 n a b
      (gidney_propagation_post_state 1 (adder_input_F n a b)) := by
  show Gidney.propagation_step_invariant 1 n a b
        (gidney_first_bit_post_state (adder_input_F n a b))
  obtain ⟨hp_c0, hp_r1, hp_t1⟩ :=
    gidney_first_bit_preserves n a b hn ha hb
  have h_r0_c0 : read_idx 0 ≠ carry_idx 0 := by unfold read_idx carry_idx; omega
  have h_r0_r1 : read_idx 0 ≠ read_idx 1 := by unfold read_idx; omega
  have h_r0_t1 : read_idx 0 ≠ target_idx 1 := by
    unfold read_idx target_idx; omega
  have h_t0_c0 : target_idx 0 ≠ carry_idx 0 := by
    unfold target_idx carry_idx; omega
  have h_t0_r1 : target_idx 0 ≠ read_idx 1 := by
    unfold target_idx read_idx; omega
  have h_t0_t1 : target_idx 0 ≠ target_idx 1 := by unfold target_idx; omega
  intro j hj
  refine ⟨?_, ?_, ?_⟩
  · by_cases hj_lt : j < 1
    · have hj0 : j = 0 := by omega
      subst hj0
      simp only [hj_lt]
      simpa using hp_c0
    · simp only [hj_lt, if_false]
      have h_cj_c0 : carry_idx j ≠ carry_idx 0 := by unfold carry_idx; omega
      have h_cj_r1 : carry_idx j ≠ read_idx 1 := by
        unfold carry_idx read_idx; omega
      have h_cj_t1 : carry_idx j ≠ target_idx 1 := by
        unfold carry_idx target_idx; omega
      rw [gidney_first_bit_post_state_preserves_outside _ _
            h_cj_c0 h_cj_r1 h_cj_t1]
      exact adder_input_F_at_carry_idx n a b j
  · by_cases hj_le1 : j ≤ 1
    · match j, hj_le1 with
      | 0, _ =>
        simp only [show (0 : Nat) ≤ 1 from by decide, if_true]
        rw [gidney_first_bit_post_state_preserves_outside _ _
              h_r0_c0 h_r0_r1 h_r0_t1]
        rw [adder_input_F_at_read_idx n a b 0 (by omega)]
        simp [Adder.carry]
      | 1, _ =>
        simp only [show (1 : Nat) ≤ 1 from by decide, if_true]
        simpa using hp_r1
    · simp only [hj_le1, if_false]
      have h_rj_c0 : read_idx j ≠ carry_idx 0 := by
        unfold read_idx carry_idx; omega
      have h_rj_r1 : read_idx j ≠ read_idx 1 := by unfold read_idx; omega
      have h_rj_t1 : read_idx j ≠ target_idx 1 := by
        unfold read_idx target_idx; omega
      rw [gidney_first_bit_post_state_preserves_outside _ _
            h_rj_c0 h_rj_r1 h_rj_t1]
      exact adder_input_F_at_read_idx n a b j hj
  · by_cases hj_le1 : j ≤ 1
    · match j, hj_le1 with
      | 0, _ =>
        simp only [show (0 : Nat) ≤ 1 from by decide, if_true]
        rw [gidney_first_bit_post_state_preserves_outside _ _
              h_t0_c0 h_t0_r1 h_t0_t1]
        rw [adder_input_F_at_target_idx n a b 0 (by omega)]
        simp [Adder.carry]
      | 1, _ =>
        simp only [show (1 : Nat) ≤ 1 from by decide, if_true]
        simpa using hp_t1
    · simp only [hj_le1, if_false]
      have h_tj_c0 : target_idx j ≠ carry_idx 0 := by
        unfold target_idx carry_idx; omega
      have h_tj_r1 : target_idx j ≠ read_idx 1 := by
        unfold target_idx read_idx; omega
      have h_tj_t1 : target_idx j ≠ target_idx 1 := by
        unfold target_idx; omega
      rw [gidney_first_bit_post_state_preserves_outside _ _
            h_tj_c0 h_tj_r1 h_tj_t1]
      exact adder_input_F_at_target_idx n a b j hj

/-- **Inductive step k → k+1 of cascade induction** (Iter 178, SORRIED).
    For k ≥ 1 (so we apply an interior step at position k), if the
    state satisfies step-k invariant, then applying the interior
    step at position k yields a state satisfying step-(k+1)
    invariant.

    Connects to the cascade via:
    `gidney_propagation_post_state (k + 2) f =
       gidney_bit_step_faithful_post_state (k + 1)
         (gidney_propagation_post_state (k + 1) f)`

    i.e., the recursive step. With the bridge `gidney_interior_bit_post_state_eq`,
    we can use `gidney_interior_bit_preserves` (Iter 170) for the
    touched positions + `gidney_interior_bit_post_state_preserves_outside`
    (Iter 173) for the rest.

    SORRIED — the full proof requires extracting hypotheses from
    h_prev (the step-k invariant) at 6+ positions, then applying
    the interior preserves + frame condition. Estimated ~50-80
    lines of careful Lean. Punted to keep this tick bounded; the
    pattern is established by Iter 177's first-bit version.

    See [Iter 174 reflection](AutoScript/reflection.md) for the
    completion plan. -/
theorem TODO_gidney_propagation_step_invariant_step
    (k n a b : Nat) (hk : 1 ≤ k) (hk_n : k + 1 < n)
    (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n)
    (h_prev : Gidney.propagation_step_invariant k n a b
                (gidney_propagation_post_state k (adder_input_F n a b))) :
    Gidney.propagation_step_invariant (k + 1) n a b
      (gidney_propagation_post_state (k + 1) (adder_input_F n a b)) := by
  -- Step 1: unfold the cascade at (k+1) using k ≥ 1 (i.e., k+1 = (k-1)+2).
  have h_rec : gidney_propagation_post_state (k + 1) (adder_input_F n a b)
             = gidney_interior_bit_post_state k
                (gidney_propagation_post_state k (adder_input_F n a b)) := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rfl
  rw [h_rec]
  set f_prev := gidney_propagation_post_state k (adder_input_F n a b) with hf_prev
  -- Step 2: extract f_prev's values at positions k-1, k, k+1 from h_prev.
  have hk_lt_n : k < n := by omega
  have hkm1_lt_n : k - 1 < n := by omega
  have hk1_lt_n : k + 1 < n := hk_n
  have h_ck_raw  := (h_prev k       hk_lt_n).1
  have h_rk_raw  := (h_prev k       hk_lt_n).2.1
  have h_tk_raw  := (h_prev k       hk_lt_n).2.2
  have h_ckm1_raw := (h_prev (k - 1) hkm1_lt_n).1
  have h_rk1_raw := (h_prev (k + 1) hk1_lt_n).2.1
  have h_tk1_raw := (h_prev (k + 1) hk1_lt_n).2.2
  have h_ri : f_prev (read_idx k)
              = xor (a.testBit k) (Adder.carry false k a.testBit b.testBit) := by
    rw [h_rk_raw]; simp
  have h_ti : f_prev (target_idx k)
              = xor (b.testBit k) (Adder.carry false k a.testBit b.testBit) := by
    rw [h_tk_raw]; simp
  have h_cim1 : f_prev (carry_idx (k - 1))
                = Adder.carry false k a.testBit b.testBit := by
    rw [h_ckm1_raw]
    have hkm1_lt_k : k - 1 < k := by omega
    have h_succ : k - 1 + 1 = k := by omega
    simp [hkm1_lt_k, h_succ]
  have h_ci : f_prev (carry_idx k) = false := by
    rw [h_ck_raw]; simp
  have h_ri1 : f_prev (read_idx (k + 1)) = a.testBit (k + 1) := by
    rw [h_rk1_raw]
    have hne : ¬ (k + 1 ≤ k) := by omega
    simp [hne]
  have h_ti1 : f_prev (target_idx (k + 1)) = b.testBit (k + 1) := by
    rw [h_tk1_raw]
    have hne : ¬ (k + 1 ≤ k) := by omega
    simp [hne]
  -- Step 3: apply Iter 170's gidney_interior_bit_preserves at i = k.
  obtain ⟨hp_c, hp_r, hp_t⟩ :=
    gidney_interior_bit_preserves k a b hk f_prev h_ri h_ti h_cim1 h_ci h_ri1 h_ti1
  -- Step 4: prove the step-(k+1) invariant.
  intro j hj
  refine ⟨?_, ?_, ?_⟩
  · -- carry_j conjunct: split on j = k (preserved cell) vs j ≠ k (frame).
    by_cases hjk : j = k
    · subst hjk
      have hjj1 : j < j + 1 := by omega
      simp only [hjj1, if_true]
      simpa using hp_c
    · have h_cj_ck  : carry_idx j ≠ carry_idx k        := by
        unfold carry_idx; omega
      have h_cj_rk1 : carry_idx j ≠ read_idx (k + 1)   := by
        unfold carry_idx read_idx; omega
      have h_cj_tk1 : carry_idx j ≠ target_idx (k + 1) := by
        unfold carry_idx target_idx; omega
      rw [gidney_interior_bit_post_state_preserves_outside _ _ _
            h_cj_ck h_cj_rk1 h_cj_tk1]
      rw [(h_prev j hj).1]
      by_cases hjk_lt : j < k
      · simp [hjk_lt, show j < k + 1 from by omega]
      · have hne : ¬ (j < k + 1) := by omega
        simp [hjk_lt, hne]
  · -- read_j conjunct: split on j = k+1 (preserved cell) vs j ≠ k+1 (frame).
    by_cases hjk1 : j = k + 1
    · subst hjk1
      rw [if_pos (le_refl (k + 1))]
      simpa using hp_r
    · have h_rj_ck  : read_idx j ≠ carry_idx k        := by
        unfold read_idx carry_idx; omega
      have h_rj_rk1 : read_idx j ≠ read_idx (k + 1)   := by
        unfold read_idx; omega
      have h_rj_tk1 : read_idx j ≠ target_idx (k + 1) := by
        unfold read_idx target_idx; omega
      rw [gidney_interior_bit_post_state_preserves_outside _ _ _
            h_rj_ck h_rj_rk1 h_rj_tk1]
      rw [(h_prev j hj).2.1]
      by_cases hjk_le : j ≤ k
      · simp [hjk_le, show j ≤ k + 1 from by omega]
      · have hne : ¬ (j ≤ k + 1) := by omega
        simp [hjk_le, hne]
  · -- target_j conjunct: same structure as read_j.
    by_cases hjk1 : j = k + 1
    · subst hjk1
      rw [if_pos (le_refl (k + 1))]
      simpa using hp_t
    · have h_tj_ck  : target_idx j ≠ carry_idx k        := by
        unfold target_idx carry_idx; omega
      have h_tj_rk1 : target_idx j ≠ read_idx (k + 1)   := by
        unfold target_idx read_idx; omega
      have h_tj_tk1 : target_idx j ≠ target_idx (k + 1) := by
        unfold target_idx; omega
      rw [gidney_interior_bit_post_state_preserves_outside _ _ _
            h_tj_ck h_tj_rk1 h_tj_tk1]
      rw [(h_prev j hj).2.2]
      by_cases hjk_le : j ≤ k
      · simp [hjk_le, show j ≤ k + 1 from by omega]
      · have hne : ¬ (j ≤ k + 1) := by omega
        simp [hjk_le, hne]

/-- **Parametric propagation invariant** (Iter 179, PROVEN — but
    depends on Iter 178's sorried step lemma). By induction on `k`:
    - Base case k=0: `propagation_step_invariant_base_k0`.
    - k=1: `propagation_step_invariant_k1`.
    - k ≥ 2: `TODO_gidney_propagation_step_invariant_step`.

    The result: for any k with `k + 1 ≤ n`,
    `gidney_propagation_post_state k (adder_input_F n a b)`
    satisfies the step-k invariant.

    With the structural recursion form, the induction goes
    via `Nat.rec`. -/
theorem Gidney.propagation_step_invariant_holds
    (k n a b : Nat) (hkn : k < n) (hn : 1 < n)
    (ha : a < 2^n) (hb : b < 2^n) :
    Gidney.propagation_step_invariant k n a b
      (gidney_propagation_post_state k (adder_input_F n a b)) := by
  induction k with
  | zero =>
      exact Gidney.propagation_step_invariant_base_k0 n a b ha hb
  | succ m ih =>
      -- ih : k = m gives the invariant at step m.
      have hmn : m < n := by omega
      have h_prev := ih hmn
      by_cases hm0 : m = 0
      · -- m = 0, so m + 1 = 1: use the Iter 177 k=1 lemma directly.
        subst hm0
        exact Gidney.propagation_step_invariant_k1 n a b hn ha hb
      · -- m ≥ 1: use the Iter 178 step lemma.
        have hm1 : 1 ≤ m := by omega
        have hm_plus_1_n : m + 1 < n := by omega
        exact TODO_gidney_propagation_step_invariant_step
                m n a b hm1 hm_plus_1_n hn ha hb h_prev

/-- **Generic ↔ concrete check #1**: `adder_input_F 2 1 0` matches
    `inputF_1_plus_0` at all 6 qubits of the 2-bit adder. -/
example :
    (∀ k, k < 6 →
       adder_input_F 2 1 0 k = inputF_1_plus_0 k) := by decide

/-- **Generic ↔ concrete check #2**: `adder_input_F 2 1 1` matches
    `inputF_1_plus_1` at all 6 qubits. -/
example :
    (∀ k, k < 6 →
       adder_input_F 2 1 1 k = inputF_1_plus_1 k) := by decide

/-- **Generic ↔ concrete check #3**: `adder_input_F 3 3 1` matches
    `inputF_3_plus_1` at all 9 qubits. -/
example :
    (∀ k, k < 9 →
       adder_input_F 3 3 1 k = inputF_3_plus_1 k) := by decide

/-- **Generic ↔ concrete check #4**: `adder_input_F 4 7 1` matches
    `inputF_7_plus_1` at all 12 qubits. -/
example :
    (∀ k, k < 12 →
       adder_input_F 4 7 1 k = inputF_7_plus_1 k) := by decide

/-- **Classical sum-bit concrete check**: bit 0 of (7+1)=8 is 0,
    bit 1 is 0, bit 2 is 0, bit 3 is 1 (binary "1000"). -/
example :
    adder_sum_bit_classical 7 1 0 = false
    ∧ adder_sum_bit_classical 7 1 1 = false
    ∧ adder_sum_bit_classical 7 1 2 = false
    ∧ adder_sum_bit_classical 7 1 3 = true := by decide

/-- **Decide-witness for `post_last_bit_invariant` on (n=2, a=1, b=1)**
    (Iter 187). Validates that after forward cascade only (no
    final-CX), `target_1 = b_1 ⊕ c_1 = 0 ⊕ 1 = 1` (still propagated,
    not yet canceled). This is the state BEFORE the final-CX layer. -/
example :
    Gidney.post_last_bit_invariant 2 1 1
      (gidney_forward_faithful_full_post_state 2 (adder_input_F 2 1 1)) := by
  intro j hj
  match j, hj with
  | 0, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | _ + 2, h => omega

end FormalRV.BQAlgo
