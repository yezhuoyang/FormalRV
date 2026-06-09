/-
  FormalRV.Arithmetic.RippleCarryAdder.UncomputeCascade.WellTypedBackbone
  BACKBONE (part 3/3): the WellTyped induction for the patched adder, then THE
  bundled reusable primitive `gidney_adder_patched_primitive` (WellTyped +
  decoded target = (a+b) mod 2^bits + read preservation + carry clearing) — the
  single theorem the modular-adder layer calls. Builds on `Correctness`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.UncomputeCascade.Correctness

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

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
