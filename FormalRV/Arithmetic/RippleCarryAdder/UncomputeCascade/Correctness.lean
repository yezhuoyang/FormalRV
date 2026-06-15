/-
  FormalRV.Arithmetic.RippleCarryAdder.UncomputeCascade.Correctness
  Patched full-adder correctness (part 2/3): per-register correctness, the
  packaged correctness theorem, and the bits-parametric decode
  `gidney_adder_patched_target_decode`. Builds on `FrameLemmas`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.UncomputeCascade.FrameLemmas

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-! ## Patched full-adder correctness (Deliverables C + D)

Combine the cascade-level frame theorems with the existing Iter 191
target/read correctness for the unpatched full adder, plus this
session's arbitrary-n carry-clearance for the patched full adder. -/

/-- **Patched full adder, target register correctness** (Deliverable C₁). -/
theorem gidney_adder_full_faithful_no_measurement_patched_target_correct
    (n a b : Nat) (ha : a < 2^(n + 2)) (hb : b < 2^(n + 2)) :
    ∀ i, i < n + 2 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched (n + 2))
        (adder_input_F (n + 2) a b) (target_idx i)
      = adder_sum_bit_classical a b i := by
  intro i hi
  show Gate.applyNat (gidney_adder_forward_faithful_full_reverse_patched (n + 2))
        (Gate.applyNat (gidney_final_cx_cascade (n + 2))
          (Gate.applyNat (gidney_adder_forward_faithful_full (n + 2))
            (adder_input_F (n + 2) a b)))
        (target_idx i) = adder_sum_bit_classical a b i
  rw [gidney_adder_forward_faithful_full_applyNat,
      gidney_final_cx_cascade_applyNat,
      patched_full_reverse_eq_unpatched_at_target n _ i]
  have h := gidney_adder_full_faithful_no_measurement_target_correct (n + 2) a b
              (by omega) ha hb i hi
  rw [show gidney_final_cx_cascade_post_state (n + 2)
            (gidney_forward_faithful_full_post_state (n + 2) (adder_input_F (n + 2) a b))
          = Gate.applyNat (gidney_final_cx_cascade (n + 2))
              (Gate.applyNat (gidney_adder_forward_faithful_full (n + 2))
                (adder_input_F (n + 2) a b))
        by rw [gidney_adder_forward_faithful_full_applyNat,
               gidney_final_cx_cascade_applyNat]]
  exact h

/-- **Patched full adder, read register preservation** (Deliverable C₂). -/
theorem gidney_adder_full_faithful_no_measurement_patched_read_preserved
    (n a b : Nat) (ha : a < 2^(n + 2)) (hb : b < 2^(n + 2)) :
    ∀ i, i < n + 2 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched (n + 2))
        (adder_input_F (n + 2) a b) (read_idx i)
      = a.testBit i := by
  intro i hi
  show Gate.applyNat (gidney_adder_forward_faithful_full_reverse_patched (n + 2))
        (Gate.applyNat (gidney_final_cx_cascade (n + 2))
          (Gate.applyNat (gidney_adder_forward_faithful_full (n + 2))
            (adder_input_F (n + 2) a b)))
        (read_idx i) = a.testBit i
  rw [gidney_adder_forward_faithful_full_applyNat,
      gidney_final_cx_cascade_applyNat,
      patched_full_reverse_eq_unpatched_at_read n _ i]
  have h := gidney_adder_full_faithful_no_measurement_read_correct (n + 2) a b
              (by omega) ha hb i hi
  rw [show gidney_final_cx_cascade_post_state (n + 2)
            (gidney_forward_faithful_full_post_state (n + 2) (adder_input_F (n + 2) a b))
          = Gate.applyNat (gidney_final_cx_cascade (n + 2))
              (Gate.applyNat (gidney_adder_forward_faithful_full (n + 2))
                (adder_input_F (n + 2) a b))
        by rw [gidney_adder_forward_faithful_full_applyNat,
               gidney_final_cx_cascade_applyNat]]
  exact h

/-- **Full patched-adder correctness — packaged theorem** (Deliverable D).
For the Option-1 carry-clearing patched Gidney adder on `adder_input_F (n+2) a b`:
1. The read register is preserved (= original `a` bits).
2. The target register equals the classical sum bits.
3. The carry register is fully cleared. -/
theorem gidney_adder_full_faithful_no_measurement_patched_correct
    (n a b : Nat) (ha : a < 2^(n + 2)) (hb : b < 2^(n + 2)) :
    (∀ i, i < n + 2 →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched (n + 2))
          (adder_input_F (n + 2) a b) (read_idx i)
        = a.testBit i)
    ∧ (∀ i, i < n + 2 →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched (n + 2))
          (adder_input_F (n + 2) a b) (target_idx i)
        = adder_sum_bit_classical a b i)
    ∧ (∀ i, i ≤ n + 1 →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched (n + 2))
          (adder_input_F (n + 2) a b) (carry_idx i) = false) := by
  refine ⟨?_, ?_, ?_⟩
  · exact gidney_adder_full_faithful_no_measurement_patched_read_preserved n a b ha hb
  · exact gidney_adder_full_faithful_no_measurement_patched_target_correct n a b ha hb
  · exact gidney_adder_full_faithful_no_measurement_patched_clears_carries n a b ha hb

/-! ## Reusable patched-adder primitives (toward modular addition)

Three primitives the modular-addition layer will call:
1. A `bits`-parameter version of the packaged correctness theorem
   (Deliverable A of the user's "primitive" tick).
2. The natural-number decoding of the target register: after the
   adder runs on `(a, b)`, the target register holds `(a + b) mod 2^bits`
   (Deliverable B).
3. (Future) `Gate.WellTyped` for the patched adder. -/

/-- Helper: `x % 2^(n+1) = x % 2^n + (testBit x n) * 2^n`.  Standard
identity, not in mathlib in this exact form. -/
theorem nat_mod_two_pow_succ_eq (x n : Nat) :
    x % 2^(n + 1) = x % 2^n + (if x.testBit n then 2^n else 0) := by
  have step1 : x % 2^(n+1) = x % 2^n + (x / 2^n % 2) * 2^n := by
    rw [pow_succ, Nat.mod_mul, Nat.mul_comm (2^n) _]
  rw [step1]
  congr 1
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : x / 2^n % 2 = 1
  · simp [h]
  · have h_zero : x / 2^n % 2 = 0 := by
      have := Nat.mod_lt (x / 2^n) (by decide : (0:Nat) < 2)
      omega
    simp [h_zero]

/-- If a bit-function's target-register positions match the bits of `S`,
then `gidney_target_val` decodes the target register to `S % 2^bits`. -/
theorem gidney_target_val_eq_sum_when_bits_match
    (bits S : Nat) (f : Nat → Bool)
    (h : ∀ i, i < bits → f (target_idx i) = S.testBit i) :
    gidney_target_val bits f = S % 2^bits := by
  induction bits with
  | zero => simp [gidney_target_val, Nat.mod_one]
  | succ k ih =>
      have h_k : f (target_idx k) = S.testBit k := h k (by omega)
      have ih_inst : gidney_target_val k f = S % 2^k := by
        apply ih; intro i hi; exact h i (by omega)
      unfold gidney_target_val
      rw [ih_inst, h_k, nat_mod_two_pow_succ_eq]

/-- **Deliverable A**: bits-parameter wrapper of the packaged
correctness theorem.  For any `bits ≥ 2` and `a, b < 2^bits`, the
patched full faithful no-measurement Gidney adder preserves the
read register, writes the classical sum bits into the target
register, and clears the carry register. -/
theorem gidney_adder_full_faithful_no_measurement_patched_correct_bits
    (bits a b : Nat) (hbits : 2 ≤ bits) (ha : a < 2^bits) (hb : b < 2^bits) :
    (∀ i, i < bits →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits a b) (read_idx i) = a.testBit i)
    ∧ (∀ i, i < bits →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits a b) (target_idx i) = (a + b).testBit i)
    ∧ (∀ i, i < bits →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits a b) (carry_idx i) = false) := by
  obtain ⟨n, rfl⟩ : ∃ n, bits = n + 2 := ⟨bits - 2, by omega⟩
  obtain ⟨hr, ht, hc⟩ := gidney_adder_full_faithful_no_measurement_patched_correct n a b ha hb
  refine ⟨hr, ?_, ?_⟩
  · intro i hi
    have h := ht i hi
    rw [h]; rfl
  · intro i hi
    apply hc i; omega

/-- **Deliverable B**: decoded target-register correctness.  After
the patched full faithful no-measurement Gidney adder runs on
`adder_input_F bits a b`, the target register decodes to
`(a + b) mod 2^bits`. -/
theorem gidney_adder_patched_target_decode
    (bits a b : Nat) (hbits : 2 ≤ bits) (ha : a < 2^bits) (hb : b < 2^bits) :
    gidney_target_val bits
      (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
        (adder_input_F bits a b))
    = (a + b) % 2^bits := by
  apply gidney_target_val_eq_sum_when_bits_match bits (a + b) _
  intro i hi
  obtain ⟨_, ht, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                          bits a b hbits ha hb
  exact ht i hi

end FormalRV.BQAlgo
