/-
  FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderPostStates
  ───────────────────────────────────────────────────────────────
  The basis-state "semantic shadow" of the Gidney adder: for each gate / cascade
  in `RippleCarryAdderDef.lean`, the `Nat → Bool` post-state function describing
  its classical action, plus the `Prop`-valued correctness invariants the proofs
  reason about. **Definitions only — no proofs.**

  This is internal PROOF VOCABULARY: the supporting files
  (`RippleCarryAdderForwardAndCost`, `RippleCarryAdderClassicalBridge`,
  `RippleCarryAdderDecideWitnesses`, `RippleCarryAdderPropagationReverse`,
  `RippleCarryAdderUncomputeCascade`) state their lemmas against these. The
  reader-facing headlines are in `RippleCarryAdderCorrectness.lean`.
-/
import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Framework.PaperClaims
import FormalRV.PPM.Magic.GidneyAND
import Mathlib.Tactic.IntervalCases
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderSpec

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-! ## Per-bit-step post-states (forward) -/

/-- Post-state of `gidney_adder_bit_step_faithful_interior i`: CCX writes the
AND into `carry[i]`, chain-CX adds `carry[i-1]`, then 2 propagation CXs XOR
`carry[i]` into `read[i+1]` / `target[i+1]`. -/
def gidney_bit_step_faithful_post_state (i : Nat) (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f  (carry_idx i)
              (xor (f (carry_idx i))
                   (f (read_idx i) && f (target_idx i)))
  let f₂ := update f₁ (carry_idx i)
              (xor (f₁ (carry_idx i)) (f₁ (carry_idx (i - 1))))
  let f₃ := update f₂ (read_idx (i + 1))
              (xor (f₂ (read_idx (i + 1))) (f₂ (carry_idx i)))
  let f₄ := update f₃ (target_idx (i + 1))
              (xor (f₃ (target_idx (i + 1))) (f₃ (carry_idx i)))
  f₄

/-- Post-state of `gidney_adder_bit_step_faithful_first` (no chain CX). -/
def gidney_first_bit_post_state (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f  (carry_idx 0)
              (xor (f (carry_idx 0))
                   (f (read_idx 0) && f (target_idx 0)))
  let f₂ := update f₁ (read_idx 1)
              (xor (f₁ (read_idx 1)) (f₁ (carry_idx 0)))
  let f₃ := update f₂ (target_idx 1)
              (xor (f₂ (target_idx 1)) (f₂ (carry_idx 0)))
  f₃

/-- Post-state of `gidney_adder_bit_step_faithful_last i` (no propagation). -/
def gidney_last_bit_post_state (i : Nat) (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f (carry_idx i)
              (xor (f (carry_idx i))
                   (f (read_idx i) && f (target_idx i)))
  update f₁ (carry_idx i)
    (xor (f₁ (carry_idx i)) (f₁ (carry_idx (i - 1))))

/-- Post-state of the interior 4-gate step at `i ≥ 1` (alias-shaped twin of
`gidney_bit_step_faithful_post_state`, kept for the bridge lemma). -/
def gidney_interior_bit_post_state (i : Nat) (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f (carry_idx i)
              (xor (f (carry_idx i)) (f (read_idx i) && f (target_idx i)))
  let f₂ := update f₁ (carry_idx i)
              (xor (f₁ (carry_idx i)) (f₁ (carry_idx (i - 1))))
  let f₃ := update f₂ (read_idx (i + 1))
              (xor (f₂ (read_idx (i + 1))) (f₂ (carry_idx i)))
  let f₄ := update f₃ (target_idx (i + 1))
              (xor (f₃ (target_idx (i + 1))) (f₃ (carry_idx i)))
  f₄

/-! ## Per-bit-step post-states (reverse) -/

/-- Post-state of `gidney_adder_bit_step_faithful_first_reverse` (3 gates,
gate-reversed). -/
def gidney_first_bit_reverse_post_state (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f (target_idx 1)
              (xor (f (target_idx 1)) (f (carry_idx 0)))
  let f₂ := update f₁ (read_idx 1)
              (xor (f₁ (read_idx 1)) (f₁ (carry_idx 0)))
  update f₂ (carry_idx 0)
    (xor (f₂ (carry_idx 0)) (f₂ (read_idx 0) && f₂ (target_idx 0)))

/-- Post-state of `gidney_adder_bit_step_faithful_interior_reverse i` (4 gates,
gate-reversed). -/
def gidney_interior_bit_reverse_post_state (i : Nat) (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f (target_idx (i + 1))
              (xor (f (target_idx (i + 1))) (f (carry_idx i)))
  let f₂ := update f₁ (read_idx (i + 1))
              (xor (f₁ (read_idx (i + 1))) (f₁ (carry_idx i)))
  let f₃ := update f₂ (carry_idx i)
              (xor (f₂ (carry_idx i)) (f₂ (carry_idx (i - 1))))
  update f₃ (carry_idx i)
    (xor (f₃ (carry_idx i)) (f₃ (read_idx i) && f₃ (target_idx i)))

/-- Post-state of `gidney_adder_bit_step_faithful_last_reverse i` (2 gates,
gate-reversed). -/
def gidney_last_bit_reverse_post_state (i : Nat) (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f (carry_idx i)
              (xor (f (carry_idx i)) (f (carry_idx (i - 1))))
  update f₁ (carry_idx i)
    (xor (f₁ (carry_idx i)) (f₁ (read_idx i) && f₁ (target_idx i)))

/-! ## Cascade post-states -/

/-- Fold of `gidney_bit_step_faithful_post_state` over bits `1..n` (matches
`gidney_adder_forward_faithful_interior`). -/
def gidney_cascade_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0    , f => f
  | n + 1, f =>
      gidney_bit_step_faithful_post_state (n + 1)
        (gidney_cascade_post_state n f)

/-- Post-state of `gidney_adder_forward_with_propagation n`. -/
def gidney_propagation_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0    , f => f
  | 1    , f => gidney_first_bit_post_state f
  | n + 2, f =>
      gidney_bit_step_faithful_post_state (n + 1)
        (gidney_propagation_post_state (n + 1) f)

/-- Post-state of `gidney_adder_forward_faithful_full` (propagation then last). -/
def gidney_forward_faithful_full_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0    , f => f
  | 1    , f => f
  | n + 2, f =>
      gidney_last_bit_post_state (n + 1)
        (gidney_propagation_post_state (n + 1) f)

/-- Post-state of `gidney_final_cx_cascade n`: XOR `read[i]` into `target[i]`
for `i = 0..n-1`. -/
def gidney_final_cx_cascade_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0    , f => f
  | n + 1, f =>
      let f' := gidney_final_cx_cascade_post_state n f
      update f' (target_idx n) (xor (f' (target_idx n)) (f' (read_idx n)))

/-- Post-state of `gidney_adder_forward_with_propagation_reverse`. -/
def gidney_propagation_reverse_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0       , f => f
  | 1       , f => gidney_first_bit_reverse_post_state f
  | n + 2   , f =>
      gidney_propagation_reverse_post_state (n + 1)
        (gidney_interior_bit_reverse_post_state (n + 1) f)

/-- Post-state of `gidney_adder_forward_faithful_full_reverse` (last-reverse then
propagation-reverse). -/
def gidney_full_reverse_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0       , f => f
  | 1       , f => f
  | n + 2   , f =>
      gidney_propagation_reverse_post_state (n + 1)
        (gidney_last_bit_reverse_post_state (n + 1) f)

/-! ## Per-bit disjointness -/

/-- **Bit-disjointness hypothesis for bit `i`**: the 12 index-distinctness /
in-range conditions needed for the per-bit interior correctness theorem. -/
structure BitDisjointness (dim i : Nat) : Prop where
  hri    : read_idx i < dim
  hti    : target_idx i < dim
  hci    : carry_idx i < dim
  hcim1  : carry_idx (i - 1) < dim
  hri1   : read_idx (i + 1) < dim
  hti1   : target_idx (i + 1) < dim
  h_rt   : read_idx i ≠ target_idx i
  h_rc   : read_idx i ≠ carry_idx i
  h_tc   : target_idx i ≠ carry_idx i
  h_cc   : carry_idx (i - 1) ≠ carry_idx i
  h_ci_ri1 : carry_idx i ≠ read_idx (i + 1)
  h_ci_ti1 : carry_idx i ≠ target_idx (i + 1)

/-! ## Correctness invariants

These `∀ j, …` predicates characterize a post-state `post` in terms of the
classical carry chain (`Adder.carry`) and the sum spec (`adder_sum_bit_classical`).
They are the non-trivial induction predicates the proofs track. -/

/-- End-of-forward-cascade invariant: `read_i = a_i ⊕ c_i`, `target_i = b_i ⊕ c_i`,
`carry_i = c_{i+1}`. -/
def Gidney.forward_cascade_post_invariant
    (n a b : Nat) (post : Nat → Bool) : Prop :=
  ∀ i, i < n →
    post (read_idx i)
      = xor (a.testBit i) (Adder.carry false i (a.testBit) (b.testBit))
    ∧ post (target_idx i)
        = xor (b.testBit i) (Adder.carry false i (a.testBit) (b.testBit))
    ∧ post (carry_idx i)
        = Adder.carry false (i + 1) (a.testBit) (b.testBit)

/-- Step-indexed propagation invariant: after `k` steps, positions `< k` (carry)
/ `≤ k` (read, target) are propagated, the rest unchanged. -/
def Gidney.propagation_step_invariant
    (k n a b : Nat) (post : Nat → Bool) : Prop :=
  ∀ j, j < n →
    -- carry_j: processed iff j < k
    (post (carry_idx j) =
      if j < k then Adder.carry false (j + 1) a.testBit b.testBit
      else false)
    ∧ -- read_j: propagated iff j ≤ k
    (post (read_idx j) =
      if j ≤ k then
        xor (a.testBit j) (Adder.carry false j a.testBit b.testBit)
      else a.testBit j)
    ∧ -- target_j: same as read_j but with b
    (post (target_idx j) =
      if j ≤ k then
        xor (b.testBit j) (Adder.carry false j a.testBit b.testBit)
      else b.testBit j)

/-- End-state invariant after the forward cascade only (no final-CX):
`carry_j = c_{j+1}`, `read_j = a_j ⊕ c_j`, `target_j = b_j ⊕ c_j`. -/
def Gidney.post_last_bit_invariant
    (n a b : Nat) (post : Nat → Bool) : Prop :=
  ∀ j, j < n →
    (post (carry_idx j)
      = Adder.carry false (j + 1) a.testBit b.testBit)
    ∧ (post (read_idx j)
        = xor (a.testBit j) (Adder.carry false j a.testBit b.testBit))
    ∧ (post (target_idx j)
        = xor (b.testBit j) (Adder.carry false j a.testBit b.testBit))

/-- End-state invariant after forward + final-CX: `target_j = a_j ⊕ b_j` (the
`c_j` contributions cancel — the reverse cascade re-XORs them to finish the sum). -/
def Gidney.post_forward_final_cx_invariant
    (n a b : Nat) (post : Nat → Bool) : Prop :=
  ∀ j, j < n →
    (post (carry_idx j)
      = Adder.carry false (j + 1) a.testBit b.testBit)
    ∧ (post (read_idx j)
        = xor (a.testBit j) (Adder.carry false j a.testBit b.testBit))
    ∧ (post (target_idx j)
        = xor (a.testBit j) (b.testBit j))

/-- Post-full-reverse invariant: `target_j = sum_j` and `read_j = a_j` (carries
left dirty). The structural refinement of the headline correctness. -/
def Gidney.post_full_reverse_invariant
    (n a b : Nat) (post : Nat → Bool) : Prop :=
  ∀ j, j < n →
    (post (target_idx j) = adder_sum_bit_classical a b j)
    ∧ (post (read_idx j) = a.testBit j)

/-- Step-indexed reverse-cascade invariant: after `k` reverse steps, positions
`j ∈ [n-k, n-1]` are corrected (`target_j = sum_j`, `read_j = a_j`). At `k = n`
this is `post_full_reverse_invariant`. -/
def Gidney.reverse_step_invariant
    (k n a b : Nat) (post : Nat → Bool) : Prop :=
  ∀ j, n - k ≤ j → j < n →
    (post (target_idx j) = adder_sum_bit_classical a b j)
    ∧ (post (read_idx j) = a.testBit j)

end FormalRV.BQAlgo
