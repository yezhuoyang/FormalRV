/-
  FormalRV.Arithmetic.RippleCarryAdder.PropagationReverse.ApplyNatBridge
  Part 2/4: the `Gate.applyNat` bridge — per-bit-step rfl wrappers, n-bit
  forward/reverse cascade applyNat forms, decoder bounds, the full-adder applyNat
  identity, the applyNat-form target/read correctness lift, the does-not-clear-
  carries finding, and the patched n=2/n=3 exhaustive decide tests.
  Builds on `SemanticCorrectness`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.PropagationReverse.SemanticCorrectness

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-! ## `Gate.applyNat` bridge for the Gidney faithful bit-step family

The three existing `gidney_*_correct` theorems (interior, first, last)
are stated in the `uc_eval (Gate.toUCom dim _) * f_to_vec dim f
= f_to_vec dim (post_state f)` form.  The matching `Gate.applyNat`
identities follow by definitional unfolding alone — they are `rfl`
proofs.  Their value lies in giving downstream modular-multiplier
correctness proofs a *Boolean-level* description of the adder that
needs no matrix/`f_to_vec` machinery.

Together with `Gate.applyNat_oob` (in `BQAlgo/Correctness.lean`) and
`Gate.applyNat_eq_encodeDataZeroAnc_of_data_anc` (in
`BQAlgo/MCPBridge.lean`), these wrappers complete the route from the
existing Gidney bit-step corpus to the `MultiplyCircuitProperty`
obligation of `f_modmult_circuit_MMI`. -/

/-- `Gate.applyNat` form of `gidney_adder_bit_step_0_correct`.  The
i=0 step is a single CCX; its applyNat semantics matches the
single-bit Toffoli update directly. -/
theorem gidney_adder_bit_step_0_applyNat (f : Nat → Bool) :
    Gate.applyNat (gidney_adder_bit_step 0) f
      = update f (carry_idx 0)
          (xor (f (carry_idx 0))
               (f (read_idx 0) && f (target_idx 0))) := by
  rfl

/-- `Gate.applyNat` form of `gidney_adder_bit_step_faithful_first_correct`.
The first-bit step's `applyNat` action is exactly the three-update
chain captured by `gidney_first_bit_post_state`. -/
theorem gidney_adder_bit_step_faithful_first_applyNat (f : Nat → Bool) :
    Gate.applyNat gidney_adder_bit_step_faithful_first f
      = gidney_first_bit_post_state f := by
  rfl

/-- `Gate.applyNat` form of `gidney_adder_bit_step_faithful_interior_correct`.
The interior step's `applyNat` action is exactly the four-update
chain captured by `gidney_bit_step_faithful_post_state`. -/
theorem gidney_adder_bit_step_faithful_interior_applyNat
    (i : Nat) (f : Nat → Bool) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior i) f
      = gidney_bit_step_faithful_post_state i f := by
  rfl

/-- `Gate.applyNat` form of `gidney_adder_bit_step_faithful_last_correct`.
The last-bit step's `applyNat` action is exactly the two-update
chain captured by `gidney_last_bit_post_state`. -/
theorem gidney_adder_bit_step_faithful_last_applyNat
    (i : Nat) (f : Nat → Bool) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last i) f
      = gidney_last_bit_post_state i f := by
  rfl

/-! ## `Gate.applyNat` form for the n-bit Gidney forward pass

Compositional wrappers that lift the per-bit-step `Gate.applyNat`
identities (above) into full-cascade `Gate.applyNat` statements.
All three are proved by structural recursion on `n` using the
per-bit-step wrappers; each non-base case is a single `rw` through
the recursion + the per-step wrapper, followed by `rfl`.

Together they describe the Boolean action of the **forward direction**
of the Gidney faithful adder: propagation cascade (`n` faithful interior
bit-steps), full forward pass (propagation + last-bit step), and final
CX cascade (`read[i] → target[i]` XOR for `i = 0..n-1`).  The reverse
half (needed for the full no-measurement adder) follows the same
pattern; the arithmetic-semantics theorem that connects the chained
`post_state` to `(read, target, carry) ↦ (read, read+target mod 2^n, 0)`
is a separate, still-open obligation (Iter 88-89 in the existing
review). -/

/-- `Gate.applyNat` form of the final CX cascade.  The cascade is a
sequence of `CX(read[i], target[i])` for `i = 0..n-1`; its `applyNat`
action is the chained `update` exactly captured by
`gidney_final_cx_cascade_post_state`. -/
theorem gidney_final_cx_cascade_applyNat :
    ∀ (n : Nat) (f : Nat → Bool),
      Gate.applyNat (gidney_final_cx_cascade n) f
        = gidney_final_cx_cascade_post_state n f
  | 0,     _ => rfl
  | n + 1, f => by
      show Gate.applyNat (Gate.CX (read_idx n) (target_idx n))
            (Gate.applyNat (gidney_final_cx_cascade n) f)
        = update (gidney_final_cx_cascade_post_state n f)
            (target_idx n)
            (xor (gidney_final_cx_cascade_post_state n f (target_idx n))
                 (gidney_final_cx_cascade_post_state n f (read_idx n)))
      rw [gidney_final_cx_cascade_applyNat n f]
      rfl

/-- `Gate.applyNat` form of the n-bit Gidney forward propagation
cascade.  Composes per-bit-step `Gate.applyNat` identities (Tick B)
via the seq case.  Base cases (`n = 0, 1`) and the inductive case all
reduce to a single rewrite through the recursive identity + the
per-step wrapper. -/
theorem gidney_adder_forward_with_propagation_applyNat :
    ∀ (n : Nat) (f : Nat → Bool),
      Gate.applyNat (gidney_adder_forward_with_propagation n) f
        = gidney_propagation_post_state n f
  | 0,     _ => rfl
  | 1,     _ => rfl
  | n + 2, f => by
      show Gate.applyNat (gidney_adder_bit_step_faithful_interior (n + 1))
            (Gate.applyNat (gidney_adder_forward_with_propagation (n + 1)) f)
        = gidney_bit_step_faithful_post_state (n + 1)
            (gidney_propagation_post_state (n + 1) f)
      rw [gidney_adder_forward_with_propagation_applyNat (n + 1) f,
          gidney_adder_bit_step_faithful_interior_applyNat]

/-- `Gate.applyNat` form of the full Gidney forward pass.  The
`applyNat` action is the propagation post-state through bit n-1
chained with the last-bit step at position n-1. -/
theorem gidney_adder_forward_faithful_full_applyNat :
    ∀ (n : Nat) (f : Nat → Bool),
      Gate.applyNat (gidney_adder_forward_faithful_full n) f
        = gidney_forward_faithful_full_post_state n f
  | 0,     _ => rfl
  | 1,     _ => rfl
  | n + 2, f => by
      show Gate.applyNat (gidney_adder_bit_step_faithful_last (n + 1))
            (Gate.applyNat (gidney_adder_forward_with_propagation (n + 1)) f)
        = gidney_last_bit_post_state (n + 1)
            (gidney_propagation_post_state (n + 1) f)
      rw [gidney_adder_forward_with_propagation_applyNat (n + 1) f,
          gidney_adder_bit_step_faithful_last_applyNat]

/-- Decoder bound: `read_val < 2^n` for any bit-function. -/
theorem gidney_read_val_lt : ∀ (n : Nat) (f : Nat → Bool),
    gidney_read_val n f < 2^n
  | 0,     _ => by simp [gidney_read_val]
  | n + 1, f => by
      unfold gidney_read_val
      have ih := gidney_read_val_lt n f
      rcases f (read_idx n) <;> simp <;> (rw [pow_succ]; omega)

/-- Decoder bound: `target_val < 2^n`. -/
theorem gidney_target_val_lt : ∀ (n : Nat) (f : Nat → Bool),
    gidney_target_val n f < 2^n
  | 0,     _ => by simp [gidney_target_val]
  | n + 1, f => by
      unfold gidney_target_val
      have ih := gidney_target_val_lt n f
      rcases f (target_idx n) <;> simp <;> (rw [pow_succ]; omega)

/-- Decoder bound: `carry_val < 2^n`. -/
theorem gidney_carry_val_lt : ∀ (n : Nat) (f : Nat → Bool),
    gidney_carry_val n f < 2^n
  | 0,     _ => by simp [gidney_carry_val]
  | n + 1, f => by
      unfold gidney_carry_val
      have ih := gidney_carry_val_lt n f
      rcases f (carry_idx n) <;> simp <;> (rw [pow_succ]; omega)

/-- **Target register is correct**: after the full faithful no-measurement
adder, target encodes `1 + 1 = 2`. -/
example :
    gidney_target_val 2
      (Gate.applyNat (gidney_adder_full_faithful_no_measurement 2)
        inputF_1_plus_1_tickD) = 2 := by decide

/-- **Read register is preserved**: after the full faithful no-measurement
adder, read = 1 (unchanged). -/
example :
    gidney_read_val 2
      (Gate.applyNat (gidney_adder_full_faithful_no_measurement 2)
        inputF_1_plus_1_tickD) = 1 := by decide

/-- **Carry register is NOT cleared**: after the full faithful
no-measurement adder, carry = 3 (binary `11`), not 0.  This is the
open gap that blocks a verified modular adder built on this circuit. -/
example :
    gidney_carry_val 2
      (Gate.applyNat (gidney_adder_full_faithful_no_measurement 2)
        inputF_1_plus_1_tickD) = 3 := by decide

/-! ## `Gate.applyNat` wrappers for the Gidney reverse cascade

Mirror of the forward-direction Tick B/C wrappers, lifting the per-bit
reverse steps and the full reverse cascade into `Gate.applyNat`
identities.  Each per-step wrapper is `rfl` (the `*_reverse_post_state`
definitions at Iter 191 are written as exactly the update chains that
`Gate.applyNat` produces); the cascade wrappers chain those rfls via
structural recursion using `rw`.

Combined with `gidney_adder_full_faithful_no_measurement_applyNat`
below, these connect the existing Iter 191 reverse-cascade analysis
(which proves target-bit correctness via `decide`-witnesses) to the
`Gate.applyNat` framework.  This is the missing infrastructure that
lets future modmult-correctness work reason about the full adder's
classical action without descending into the matrix layer. -/

/-- `Gate.applyNat` form of the first-bit reverse step. -/
theorem gidney_adder_bit_step_faithful_first_reverse_applyNat
    (f : Nat → Bool) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f
      = gidney_first_bit_reverse_post_state f := by rfl

/-- `Gate.applyNat` form of the interior-bit reverse step. -/
theorem gidney_adder_bit_step_faithful_interior_reverse_applyNat
    (i : Nat) (f : Nat → Bool) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f
      = gidney_interior_bit_reverse_post_state i f := by rfl

/-- `Gate.applyNat` form of the last-bit reverse step. -/
theorem gidney_adder_bit_step_faithful_last_reverse_applyNat
    (i : Nat) (f : Nat → Bool) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f
      = gidney_last_bit_reverse_post_state i f := by rfl

/-- `Gate.applyNat` form of the n-bit propagation reverse cascade. -/
theorem gidney_adder_forward_with_propagation_reverse_applyNat :
    ∀ (n : Nat) (f : Nat → Bool),
      Gate.applyNat (gidney_adder_forward_with_propagation_reverse n) f
        = gidney_propagation_reverse_post_state n f
  | 0,     _ => rfl
  | 1,     _ => rfl
  | n + 2, f => by
      show Gate.applyNat (gidney_adder_forward_with_propagation_reverse (n + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (n + 1)) f)
        = gidney_propagation_reverse_post_state (n + 1)
            (gidney_interior_bit_reverse_post_state (n + 1) f)
      rw [gidney_adder_bit_step_faithful_interior_reverse_applyNat,
          gidney_adder_forward_with_propagation_reverse_applyNat (n + 1)]

/-- `Gate.applyNat` form of the full Gidney reverse cascade. -/
theorem gidney_adder_forward_faithful_full_reverse_applyNat :
    ∀ (n : Nat) (f : Nat → Bool),
      Gate.applyNat (gidney_adder_forward_faithful_full_reverse n) f
        = gidney_full_reverse_post_state n f
  | 0,     _ => rfl
  | 1,     _ => rfl
  | n + 2, f => by
      show Gate.applyNat (gidney_adder_forward_with_propagation_reverse (n + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1)) f)
        = gidney_propagation_reverse_post_state (n + 1)
            (gidney_last_bit_reverse_post_state (n + 1) f)
      rw [gidney_adder_bit_step_faithful_last_reverse_applyNat,
          gidney_adder_forward_with_propagation_reverse_applyNat (n + 1)]

/-- `Gate.applyNat` form of the full faithful no-measurement Gidney
adder for `n ≥ 2` (the only width at which the adder does non-trivial
work; `n = 0` and `n = 1` are `Gate.I`).  Composes the three Tick C
forward wrappers + the new reverse wrapper. -/
theorem gidney_adder_full_faithful_no_measurement_applyNat
    (n : Nat) (f : Nat → Bool) :
    Gate.applyNat (gidney_adder_full_faithful_no_measurement (n + 2)) f
      = gidney_full_reverse_post_state (n + 2)
          (gidney_final_cx_cascade_post_state (n + 2)
            (gidney_forward_faithful_full_post_state (n + 2) f)) := by
  show Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2))
        (Gate.applyNat (gidney_final_cx_cascade (n + 2))
          (Gate.applyNat (gidney_adder_forward_faithful_full (n + 2)) f))
    = gidney_full_reverse_post_state (n + 2)
        (gidney_final_cx_cascade_post_state (n + 2)
          (gidney_forward_faithful_full_post_state (n + 2) f))
  rw [gidney_adder_forward_faithful_full_applyNat,
      gidney_final_cx_cascade_applyNat,
      gidney_adder_forward_faithful_full_reverse_applyNat]

/-! ## `Gate.applyNat` lift of the Iter 191 arithmetic-correctness theorems

The headline arithmetic-correctness theorem `gidney_classical_action_with_reverse`
(Iter 207, 2026-05-13) is stated against the chained `post_state`
expression
`gidney_full_reverse_post_state n (gidney_final_cx_cascade_post_state n
  (gidney_forward_faithful_full_post_state n (adder_input_F n a b)))`.

The Tick E wrapper `gidney_adder_full_faithful_no_measurement_applyNat`
shows that this chained `post_state` equals `Gate.applyNat
(gidney_adder_full_faithful_no_measurement n) (adder_input_F n a b)`.
Combining the two gives `Gate.applyNat`-form correctness for the
**target** and **read** registers (both already proved by the Iter 191+
work in chained-post_state form).

The matching **carry** statement is FALSE in general — see
`gidney_adder_full_does_not_clear_carries_in_general` below.  This
is the structural defect that blocks Tick D's modular adder. -/

/-- **`Gate.applyNat`-form arithmetic correctness, target register.**
For `n ≥ 2`, the full faithful Gidney adder applied to the standard
2-operand input encoding writes the correct sum bits into the target
register.  Lift of `gidney_classical_action_with_reverse` (Iter 207)
through `gidney_adder_full_faithful_no_measurement_applyNat`. -/
theorem gidney_adder_full_faithful_no_measurement_target_correct
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    ∀ i, i < n →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement n)
        (adder_input_F n a b) (target_idx i)
      = adder_sum_bit_classical a b i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  intro i hi
  rw [gidney_adder_full_faithful_no_measurement_applyNat m
        (adder_input_F (m + 2) a b)]
  exact gidney_classical_action_with_reverse (m + 2) a b hn ha hb i hi

/-- **`Gate.applyNat`-form read-register preservation, j = 0.** -/
theorem gidney_adder_full_faithful_no_measurement_read_correct_0
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    Gate.applyNat (gidney_adder_full_faithful_no_measurement n)
        (adder_input_F n a b) (read_idx 0)
      = a.testBit 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [gidney_adder_full_faithful_no_measurement_applyNat m
        (adder_input_F (m + 2) a b)]
  exact gidney_classical_action_with_reverse_read_0 (m + 2) a b hn ha hb

/-- **`Gate.applyNat`-form read-register preservation, j = 1.** -/
theorem gidney_adder_full_faithful_no_measurement_read_correct_1
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    Gate.applyNat (gidney_adder_full_faithful_no_measurement n)
        (adder_input_F n a b) (read_idx 1)
      = a.testBit 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [gidney_adder_full_faithful_no_measurement_applyNat m
        (adder_input_F (m + 2) a b)]
  exact gidney_classical_action_with_reverse_read_1 (m + 2) a b hn ha hb

/-- **`Gate.applyNat`-form read-register preservation, j ≥ 2.** -/
theorem gidney_adder_full_faithful_no_measurement_read_correct_geq_2
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n)
    (j : Nat) (hj : 2 ≤ j) (hjn : j < n) :
    Gate.applyNat (gidney_adder_full_faithful_no_measurement n)
        (adder_input_F n a b) (read_idx j)
      = a.testBit j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [gidney_adder_full_faithful_no_measurement_applyNat m
        (adder_input_F (m + 2) a b)]
  exact gidney_classical_action_with_reverse_read_geq_2 (m + 2) a b hn ha hb
          j hj hjn

/-- **`Gate.applyNat`-form read-register preservation, all positions.**
Assembles the three cases above. -/
theorem gidney_adder_full_faithful_no_measurement_read_correct
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    ∀ i, i < n →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement n)
        (adder_input_F n a b) (read_idx i)
      = a.testBit i := by
  intro i hi
  match i, hi with
  | 0, _ =>
      exact gidney_adder_full_faithful_no_measurement_read_correct_0 n a b hn ha hb
  | 1, _ =>
      exact gidney_adder_full_faithful_no_measurement_read_correct_1 n a b hn ha hb
  | j + 2, hi' =>
      exact gidney_adder_full_faithful_no_measurement_read_correct_geq_2 n a b
              hn ha hb (j + 2) (by omega) hi'

/-- **Formalized Tick D finding**: the full faithful no-measurement
Gidney adder does NOT clear the carry register in general.

Proof: machine-checked counterexample at `(n=2, a=1, b=1, i=0)`.  The
existing Iter 191 work proves target-bit correctness and read-register
preservation, but does NOT — and CANNOT, as this theorem shows —
also establish carry-zeroing.

This is the precise structural defect that blocks a verified
modular adder built on this circuit: modular reduction requires
clean ancillas to compare and conditionally subtract, but the
existing adder leaves carries dirty whenever the carry chain is
non-trivial. -/
theorem gidney_adder_full_does_not_clear_carries_in_general :
    ¬ (∀ n a b, 1 < n → a < 2^n → b < 2^n → ∀ i, i < n →
        (Gate.applyNat (gidney_adder_full_faithful_no_measurement n)
          (adder_input_F n a b)) (carry_idx i) = false) := by
  intro h
  have h1 := h 2 1 1 (by decide) (by decide) (by decide) 0 (by decide)
  revert h1
  decide

/-- **Patched adder clears carries — n=2 exhaustive**.  Over all
`(a, b) ∈ [0, 4) × [0, 4)`, every carry position of the patched full
faithful no-measurement Gidney adder is `false`. -/
theorem patched_n2_clears_carries :
    ∀ a b, a < 4 → b < 4 → ∀ i, i < 2 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched 2)
        (adder_input_F 2 a b) (carry_idx i) = false := by
  intro a b ha hb i hi
  interval_cases a <;> interval_cases b <;> interval_cases i <;> decide

/-- **Patched adder target correctness — n=2 exhaustive**. -/
theorem patched_n2_target_correct :
    ∀ a b, a < 4 → b < 4 → ∀ i, i < 2 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched 2)
          (adder_input_F 2 a b) (target_idx i)
        = adder_sum_bit_classical a b i := by
  intro a b ha hb i hi
  interval_cases a <;> interval_cases b <;> interval_cases i <;> decide

/-- **Patched adder read preservation — n=2 exhaustive**. -/
theorem patched_n2_read_preserved :
    ∀ a b, a < 4 → b < 4 → ∀ i, i < 2 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched 2)
          (adder_input_F 2 a b) (read_idx i)
        = a.testBit i := by
  intro a b ha hb i hi
  interval_cases a <;> interval_cases b <;> interval_cases i <;> decide

/-- **Patched adder clears carries — n=3 exhaustive**.  192 cases. -/
theorem patched_n3_clears_carries :
    ∀ a b, a < 8 → b < 8 → ∀ i, i < 3 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched 3)
        (adder_input_F 3 a b) (carry_idx i) = false := by
  intro a b ha hb i hi
  interval_cases a <;> interval_cases b <;> interval_cases i <;> decide

/-- **Patched adder target correctness — n=3 exhaustive**.  192 cases. -/
theorem patched_n3_target_correct :
    ∀ a b, a < 8 → b < 8 → ∀ i, i < 3 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched 3)
          (adder_input_F 3 a b) (target_idx i)
        = adder_sum_bit_classical a b i := by
  intro a b ha hb i hi
  interval_cases a <;> interval_cases b <;> interval_cases i <;> decide

/-- **Patched adder read preservation — n=3 exhaustive**.  192 cases. -/
theorem patched_n3_read_preserved :
    ∀ a b, a < 8 → b < 8 → ∀ i, i < 3 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched 3)
          (adder_input_F 3 a b) (read_idx i)
        = a.testBit i := by
  intro a b ha hb i hi
  interval_cases a <;> interval_cases b <;> interval_cases i <;> decide

end FormalRV.BQAlgo
