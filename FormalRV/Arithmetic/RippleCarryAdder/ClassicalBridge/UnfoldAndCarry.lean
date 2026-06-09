/-
  FormalRV.Arithmetic.RippleCarryAdder.ClassicalBridge.UnfoldAndCarry
  Part 1/4: full-adder structural unfolding + reverse-cascade correctness on
  basis states, zero-input lemmas, the RSA-2048 T-count example, and the
  `Adder.carry`/`sumfb` algebra helpers (carry_succ/carry_sym/...). Supporting
  lemmas; the propagation-invariant backbone is `PropagationInvariantBackbone`.
-/
import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Framework.PaperClaims
import FormalRV.PPM.GidneyAND
import Mathlib.Tactic.IntervalCases
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderDef
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderForwardAndCost

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

end FormalRV.BQAlgo
