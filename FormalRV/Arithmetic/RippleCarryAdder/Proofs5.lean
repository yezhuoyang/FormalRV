import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Corpus.PaperClaims
import FormalRV.PPM.GidneyAND
import Mathlib.Tactic.IntervalCases
import FormalRV.Arithmetic.RippleCarryAdder.Defs
import FormalRV.Arithmetic.RippleCarryAdder.Proofs4

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-- Unpatched full reverse cascade commutes with update at `c[j]` (`j > n+1`). -/
theorem unpatched_full_reverse_commute_update_at_c_above
    (n : Nat) (g : Nat → Bool) (v : Bool) (j : Nat) (hj : j > n + 1) :
    Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2)) (update g (carry_idx j) v)
      = update (Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2)) g)
          (carry_idx j) v := by
  show Gate.applyNat (gidney_adder_forward_with_propagation_reverse (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1))
          (update g (carry_idx j) v))
    = update (Gate.applyNat (gidney_adder_forward_with_propagation_reverse (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1)) g))
        (carry_idx j) v
  rw [unpatched_last_reverse_commute_update_at_c_above (n + 1) (by omega) g j (by omega) v]
  rw [unpatched_propagation_reverse_commute_update_at_c_above n _ v j (by omega)]

/-- **Input-independence of the unpatched propagation cascade** (Deliverable A):
changing the input at `carry_idx (m+1)` (above the cascade's range)
does not affect the output at any other position. -/
theorem unpatched_propagation_reverse_indep_input_at_c_above
    (m : Nat) (g : Nat → Bool) (v : Bool) (k : Nat) (h_k : k ≠ carry_idx (m + 1)) :
    Gate.applyNat (gidney_adder_forward_with_propagation_reverse (m + 1))
      (update g (carry_idx (m + 1)) v) k
    = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (m + 1)) g k := by
  rw [unpatched_propagation_reverse_commute_update_at_c_above m g v (m + 1) (by omega)]
  rw [update_neq _ _ _ _ h_k]

/-- Input-independence of the unpatched full reverse cascade at `c[n+2]`. -/
theorem unpatched_full_reverse_indep_input_at_c_above
    (n : Nat) (g : Nat → Bool) (v : Bool) (k : Nat) (h_k : k ≠ carry_idx (n + 2)) :
    Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2))
      (update g (carry_idx (n + 2)) v) k
    = Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2)) g k := by
  rw [unpatched_full_reverse_commute_update_at_c_above n g v (n + 2) (by omega)]
  rw [update_neq _ _ _ _ h_k]

/-! ## Cascade-level "patched = unpatched at non-carry" theorems (Deliverable B) -/

/-- Patched propagation cascade equals unpatched at `target_idx i`. -/
theorem patched_unpatched_propagation_reverse_eq_at_target (m : Nat) :
    ∀ (g : Nat → Bool) (i : Nat),
      Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (m + 1)) g
        (target_idx i)
        = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (m + 1)) g
            (target_idx i) := by
  induction m with
  | zero =>
      intro g i
      apply patched_first_reverse_eq_unpatched_at_non_c0
      unfold target_idx carry_idx; omega
  | succ k' ih =>
      intro g i
      show Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (k' + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched (k' + 1)) g)
            (target_idx i)
        = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (k' + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (k' + 1)) g)
            (target_idx i)
      set s_p := Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched (k' + 1)) g
      set s_u := Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (k' + 1)) g
      rw [ih s_p i]
      have h_sp_form : s_p = update s_u (carry_idx (k' + 1)) (s_p (carry_idx (k' + 1))) := by
        funext k
        by_cases h_k : k = carry_idx (k' + 1)
        · subst h_k; rw [update_eq]
        · rw [update_neq _ _ _ _ h_k]
          exact patched_interior_reverse_eq_unpatched_at_non_ci (k' + 1) g k h_k
      rw [h_sp_form]
      apply unpatched_propagation_reverse_indep_input_at_c_above k' s_u _ (target_idx i)
      unfold target_idx carry_idx; omega

/-- Patched propagation cascade equals unpatched at `read_idx i`. -/
theorem patched_unpatched_propagation_reverse_eq_at_read (m : Nat) :
    ∀ (g : Nat → Bool) (i : Nat),
      Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (m + 1)) g
        (read_idx i)
        = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (m + 1)) g
            (read_idx i) := by
  induction m with
  | zero =>
      intro g i
      apply patched_first_reverse_eq_unpatched_at_non_c0
      unfold read_idx carry_idx; omega
  | succ k' ih =>
      intro g i
      show Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (k' + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched (k' + 1)) g)
            (read_idx i)
        = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (k' + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (k' + 1)) g)
            (read_idx i)
      set s_p := Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched (k' + 1)) g
      set s_u := Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (k' + 1)) g
      rw [ih s_p i]
      have h_sp_form : s_p = update s_u (carry_idx (k' + 1)) (s_p (carry_idx (k' + 1))) := by
        funext k
        by_cases h_k : k = carry_idx (k' + 1)
        · subst h_k; rw [update_eq]
        · rw [update_neq _ _ _ _ h_k]
          exact patched_interior_reverse_eq_unpatched_at_non_ci (k' + 1) g k h_k
      rw [h_sp_form]
      apply unpatched_propagation_reverse_indep_input_at_c_above k' s_u _ (read_idx i)
      unfold read_idx carry_idx; omega

/-- Patched full reverse cascade equals unpatched at `target_idx i`. -/
theorem patched_full_reverse_eq_unpatched_at_target
    (n : Nat) (g : Nat → Bool) (i : Nat) :
    Gate.applyNat (gidney_adder_forward_faithful_full_reverse_patched (n + 2)) g (target_idx i)
      = Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2)) g (target_idx i) := by
  show Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1)) g)
        (target_idx i)
    = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1)) g)
        (target_idx i)
  set s_p := Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1)) g
  set s_u := Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1)) g
  rw [patched_unpatched_propagation_reverse_eq_at_target n s_p i]
  have h_sp_form : s_p = update s_u (carry_idx (n + 1)) (s_p (carry_idx (n + 1))) := by
    funext k
    by_cases h_k : k = carry_idx (n + 1)
    · subst h_k; rw [update_eq]
    · rw [update_neq _ _ _ _ h_k]
      exact patched_last_reverse_eq_unpatched_at_non_ci (n + 1) g k h_k
  rw [h_sp_form]
  apply unpatched_propagation_reverse_indep_input_at_c_above n s_u _ (target_idx i)
  unfold target_idx carry_idx; omega

/-- Patched full reverse cascade equals unpatched at `read_idx i`. -/
theorem patched_full_reverse_eq_unpatched_at_read
    (n : Nat) (g : Nat → Bool) (i : Nat) :
    Gate.applyNat (gidney_adder_forward_faithful_full_reverse_patched (n + 2)) g (read_idx i)
      = Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2)) g (read_idx i) := by
  show Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1)) g)
        (read_idx i)
    = Gate.applyNat (gidney_adder_forward_with_propagation_reverse (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1)) g)
        (read_idx i)
  set s_p := Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1)) g
  set s_u := Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1)) g
  rw [patched_unpatched_propagation_reverse_eq_at_read n s_p i]
  have h_sp_form : s_p = update s_u (carry_idx (n + 1)) (s_p (carry_idx (n + 1))) := by
    funext k
    by_cases h_k : k = carry_idx (n + 1)
    · subst h_k; rw [update_eq]
    · rw [update_neq _ _ _ _ h_k]
      exact patched_last_reverse_eq_unpatched_at_non_ci (n + 1) g k h_k
  rw [h_sp_form]
  apply unpatched_propagation_reverse_indep_input_at_c_above n s_u _ (read_idx i)
  unfold read_idx carry_idx; omega

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

/-! ## WellTyped for the patched Gidney adder (Deliverable C)

Structural proof that the full patched faithful no-measurement
Gidney adder is `Gate.WellTyped` at the natural dimension
`adder_n_qubits bits = 3 * bits + 2`.

Proof structure:
1. Per-step WellTyped (6 lemmas: faithful_first/interior/last and
   their patched-reverse counterparts).
2. Cascade WellTyped by induction over the recursive cascade
   definitions (5 lemmas: forward_with_propagation, forward_faithful_full,
   final_cx_cascade, propagation_reverse_patched,
   forward_faithful_full_reverse_patched).
3. Full adder WellTyped by composing the three components. -/

theorem gidney_adder_bit_step_faithful_first_wellTyped
    (bits : Nat) (hbits : 2 ≤ bits) :
    Gate.WellTyped (adder_n_qubits bits) gidney_adder_bit_step_faithful_first := by
  unfold gidney_adder_bit_step_faithful_first adder_n_qubits
  simp only [Gate.WellTyped]
  unfold carry_idx target_idx read_idx
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals omega

theorem gidney_adder_bit_step_faithful_interior_wellTyped
    (bits i : Nat) (hi_pos : 0 < i) (hi_lt : i < bits) :
    Gate.WellTyped (adder_n_qubits bits)
      (gidney_adder_bit_step_faithful_interior i) := by
  unfold gidney_adder_bit_step_faithful_interior adder_n_qubits
  simp only [Gate.WellTyped]
  unfold carry_idx target_idx read_idx
  refine ⟨⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals omega

theorem gidney_adder_bit_step_faithful_last_wellTyped
    (bits i : Nat) (hi_pos : 0 < i) (hi_lt : i < bits) :
    Gate.WellTyped (adder_n_qubits bits)
      (gidney_adder_bit_step_faithful_last i) := by
  unfold gidney_adder_bit_step_faithful_last adder_n_qubits
  simp only [Gate.WellTyped]
  unfold carry_idx target_idx read_idx
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals omega

theorem gidney_adder_bit_step_faithful_first_reverse_patched_wellTyped
    (bits : Nat) (hbits : 2 ≤ bits) :
    Gate.WellTyped (adder_n_qubits bits)
      gidney_adder_bit_step_faithful_first_reverse_patched := by
  unfold gidney_adder_bit_step_faithful_first_reverse_patched
         gidney_adder_bit_step_faithful_first_reverse adder_n_qubits
  simp only [Gate.WellTyped]
  unfold carry_idx target_idx read_idx
  refine ⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals omega

theorem gidney_adder_bit_step_faithful_interior_reverse_patched_wellTyped
    (bits i : Nat) (hi_pos : 0 < i) (hi_lt : i < bits) :
    Gate.WellTyped (adder_n_qubits bits)
      (gidney_adder_bit_step_faithful_interior_reverse_patched i) := by
  unfold gidney_adder_bit_step_faithful_interior_reverse_patched
         gidney_adder_bit_step_faithful_interior_reverse adder_n_qubits
  simp only [Gate.WellTyped]
  unfold carry_idx target_idx read_idx
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals omega

theorem gidney_adder_bit_step_faithful_last_reverse_patched_wellTyped
    (bits i : Nat) (hi_pos : 0 < i) (hi_lt : i < bits) :
    Gate.WellTyped (adder_n_qubits bits)
      (gidney_adder_bit_step_faithful_last_reverse_patched i) := by
  unfold gidney_adder_bit_step_faithful_last_reverse_patched
         gidney_adder_bit_step_faithful_last_reverse adder_n_qubits
  simp only [Gate.WellTyped]
  unfold carry_idx target_idx read_idx
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals omega

theorem gidney_adder_forward_with_propagation_wellTyped
    (bits : Nat) (hb2 : 2 ≤ bits) :
    ∀ k, k ≤ bits →
      Gate.WellTyped (adder_n_qubits bits)
        (gidney_adder_forward_with_propagation k) := by
  intro k
  induction k with
  | zero =>
      intro _
      show Gate.WellTyped (adder_n_qubits bits) Gate.I
      simp [Gate.WellTyped, adder_n_qubits]
  | succ k' ih =>
      intro hk
      match k' with
      | 0 =>
          show Gate.WellTyped _ gidney_adder_bit_step_faithful_first
          exact gidney_adder_bit_step_faithful_first_wellTyped bits hb2
      | k'' + 1 =>
          show Gate.WellTyped _ (Gate.seq _ _)
          refine ⟨ih (by omega), ?_⟩
          exact gidney_adder_bit_step_faithful_interior_wellTyped bits (k''+1)
                  (by omega) (by omega)

theorem gidney_adder_forward_faithful_full_wellTyped
    (bits : Nat) (hb2 : 2 ≤ bits) :
    Gate.WellTyped (adder_n_qubits bits)
      (gidney_adder_forward_faithful_full bits) := by
  obtain ⟨n, rfl⟩ : ∃ n, bits = n + 2 := ⟨bits - 2, by omega⟩
  show Gate.WellTyped _ (Gate.seq _ _)
  refine ⟨?_, ?_⟩
  · exact gidney_adder_forward_with_propagation_wellTyped (n + 2)
            (by omega) (n + 1) (by omega)
  · exact gidney_adder_bit_step_faithful_last_wellTyped (n + 2) (n + 1)
            (by omega) (by omega)

theorem gidney_final_cx_cascade_wellTyped
    (bits : Nat) :
    ∀ k, k ≤ bits →
      Gate.WellTyped (adder_n_qubits bits) (gidney_final_cx_cascade k) := by
  intro k
  induction k with
  | zero =>
      intro _
      show Gate.WellTyped _ Gate.I
      simp [Gate.WellTyped, adder_n_qubits]
  | succ k' ih =>
      intro hk
      show Gate.WellTyped _ (Gate.seq _ _)
      refine ⟨ih (by omega), ?_⟩
      show Gate.WellTyped (adder_n_qubits bits)
            (Gate.CX (read_idx k') (target_idx k'))
      unfold adder_n_qubits read_idx target_idx
      simp only [Gate.WellTyped]
      refine ⟨?_, ?_, ?_⟩
      all_goals omega

theorem gidney_adder_forward_with_propagation_reverse_patched_wellTyped
    (bits : Nat) (hb2 : 2 ≤ bits) :
    ∀ k, k ≤ bits →
      Gate.WellTyped (adder_n_qubits bits)
        (gidney_adder_forward_with_propagation_reverse_patched k) := by
  intro k
  induction k with
  | zero =>
      intro _
      show Gate.WellTyped _ Gate.I
      simp [Gate.WellTyped, adder_n_qubits]
  | succ k' ih =>
      intro hk
      match k' with
      | 0 =>
          show Gate.WellTyped _ gidney_adder_bit_step_faithful_first_reverse_patched
          exact gidney_adder_bit_step_faithful_first_reverse_patched_wellTyped bits hb2
      | k'' + 1 =>
          show Gate.WellTyped _ (Gate.seq _ _)
          refine ⟨?_, ih (by omega)⟩
          exact gidney_adder_bit_step_faithful_interior_reverse_patched_wellTyped bits (k''+1)
                  (by omega) (by omega)

theorem gidney_adder_forward_faithful_full_reverse_patched_wellTyped
    (bits : Nat) (hb2 : 2 ≤ bits) :
    Gate.WellTyped (adder_n_qubits bits)
      (gidney_adder_forward_faithful_full_reverse_patched bits) := by
  obtain ⟨n, rfl⟩ : ∃ n, bits = n + 2 := ⟨bits - 2, by omega⟩
  show Gate.WellTyped _ (Gate.seq _ _)
  refine ⟨?_, ?_⟩
  · exact gidney_adder_bit_step_faithful_last_reverse_patched_wellTyped (n+2) (n+1)
            (by omega) (by omega)
  · exact gidney_adder_forward_with_propagation_reverse_patched_wellTyped (n+2)
            (by omega) (n+1) (by omega)

/-- **Deliverable C**: full patched-adder WellTyped at the natural
dimension `adder_n_qubits bits = 3 * bits + 2`. -/
theorem gidney_adder_full_faithful_no_measurement_patched_wellTyped
    (bits : Nat) (hb2 : 2 ≤ bits) :
    Gate.WellTyped (adder_n_qubits bits)
      (gidney_adder_full_faithful_no_measurement_patched bits) := by
  obtain ⟨n, rfl⟩ : ∃ n, bits = n + 2 := ⟨bits - 2, by omega⟩
  show Gate.WellTyped _ (Gate.seq (Gate.seq _ _) _)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact gidney_adder_forward_faithful_full_wellTyped (n + 2) (by omega)
  · exact gidney_final_cx_cascade_wellTyped (n + 2) (n + 2) (by omega)
  · exact gidney_adder_forward_faithful_full_reverse_patched_wellTyped (n + 2) (by omega)

/-- **Deliverable D**: bundled reusable patched-adder primitive
combining WellTyped, decoded target correctness, read preservation,
and carry clearing — the single theorem the modular-addition layer
should call. -/
theorem gidney_adder_patched_primitive
    (bits a b : Nat) (hbits : 2 ≤ bits) (ha : a < 2^bits) (hb : b < 2^bits) :
    Gate.WellTyped (adder_n_qubits bits)
      (gidney_adder_full_faithful_no_measurement_patched bits)
    ∧ gidney_target_val bits
        (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits a b))
      = (a + b) % 2^bits
    ∧ (∀ i, i < bits →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits a b) (read_idx i) = a.testBit i)
    ∧ (∀ i, i < bits →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits a b) (carry_idx i) = false) := by
  obtain ⟨hr, _, hc⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                          bits a b hbits ha hb
  refine ⟨?_, ?_, hr, hc⟩
  · exact gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  · exact gidney_adder_patched_target_decode bits a b hbits ha hb

end FormalRV.BQAlgo
