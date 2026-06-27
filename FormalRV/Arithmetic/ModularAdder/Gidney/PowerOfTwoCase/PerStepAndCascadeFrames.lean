/- PowerOfTwoCase — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModularAdder.Gidney.PowerOfTwoCase.WidenedModAddPipeline

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ### Per-step frame lemmas -/

theorem gidney_adder_bit_step_faithful_first_preserves_above
    (f : Nat → Bool) (p : Nat) (hp : 5 ≤ p) :
    Gate.applyNat gidney_adder_bit_step_faithful_first f p = f p := by
  unfold gidney_adder_bit_step_faithful_first
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX]
  have h0 : p ≠ carry_idx 0 := by unfold carry_idx; omega
  have h1 : p ≠ read_idx 1 := by unfold read_idx; omega
  have h2 : p ≠ target_idx 1 := by unfold target_idx; omega
  rw [update_neq _ _ _ _ h2, update_neq _ _ _ _ h1, update_neq _ _ _ _ h0]

theorem gidney_adder_bit_step_faithful_interior_preserves_above
    (i : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * i + 5 ≤ p) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior i) f p = f p := by
  unfold gidney_adder_bit_step_faithful_interior
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX]
  have h_ci : p ≠ carry_idx i := by unfold carry_idx; omega
  have h_ri1 : p ≠ read_idx (i+1) := by unfold read_idx; omega
  have h_ti1 : p ≠ target_idx (i+1) := by unfold target_idx; omega
  rw [update_neq _ _ _ _ h_ti1, update_neq _ _ _ _ h_ri1, update_neq _ _ _ _ h_ci,
      update_neq _ _ _ _ h_ci]

theorem gidney_adder_bit_step_faithful_last_preserves_above
    (i : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * i + 3 ≤ p) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last i) f p = f p := by
  unfold gidney_adder_bit_step_faithful_last
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX]
  have h_ci : p ≠ carry_idx i := by unfold carry_idx; omega
  rw [update_neq _ _ _ _ h_ci, update_neq _ _ _ _ h_ci]

theorem gidney_adder_bit_step_faithful_first_reverse_preserves_above
    (f : Nat → Bool) (p : Nat) (hp : 5 ≤ p) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f p = f p := by
  unfold gidney_adder_bit_step_faithful_first_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX]
  have h0 : p ≠ carry_idx 0 := by unfold carry_idx; omega
  have h1 : p ≠ read_idx 1 := by unfold read_idx; omega
  have h2 : p ≠ target_idx 1 := by unfold target_idx; omega
  rw [update_neq _ _ _ _ h0, update_neq _ _ _ _ h1, update_neq _ _ _ _ h2]

theorem gidney_adder_bit_step_faithful_interior_reverse_preserves_above
    (i : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * i + 5 ≤ p) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f p = f p := by
  unfold gidney_adder_bit_step_faithful_interior_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX]
  have h_ci : p ≠ carry_idx i := by unfold carry_idx; omega
  have h_ri1 : p ≠ read_idx (i+1) := by unfold read_idx; omega
  have h_ti1 : p ≠ target_idx (i+1) := by unfold target_idx; omega
  rw [update_neq _ _ _ _ h_ci, update_neq _ _ _ _ h_ci, update_neq _ _ _ _ h_ri1,
      update_neq _ _ _ _ h_ti1]

theorem gidney_adder_bit_step_faithful_last_reverse_preserves_above
    (i : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * i + 3 ≤ p) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f p = f p := by
  unfold gidney_adder_bit_step_faithful_last_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX]
  have h_ci : p ≠ carry_idx i := by unfold carry_idx; omega
  rw [update_neq _ _ _ _ h_ci, update_neq _ _ _ _ h_ci]

theorem gidney_adder_bit_step_faithful_first_reverse_patched_preserves_above
    (f : Nat → Bool) (p : Nat) (hp : 5 ≤ p) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse_patched f p = f p := by
  unfold gidney_adder_bit_step_faithful_first_reverse_patched
  rw [Gate.applyNat_seq]
  have h0 : p ≠ carry_idx 0 := by unfold carry_idx; omega
  rw [Gate.applyNat_CX, update_neq _ _ _ _ h0]
  exact gidney_adder_bit_step_faithful_first_reverse_preserves_above f p hp

theorem gidney_adder_bit_step_faithful_interior_reverse_patched_preserves_above
    (i : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * i + 5 ≤ p) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched i) f p = f p := by
  unfold gidney_adder_bit_step_faithful_interior_reverse_patched
  rw [Gate.applyNat_seq]
  have h_ci : p ≠ carry_idx i := by unfold carry_idx; omega
  rw [Gate.applyNat_CX, update_neq _ _ _ _ h_ci]
  exact gidney_adder_bit_step_faithful_interior_reverse_preserves_above i f p hp

theorem gidney_adder_bit_step_faithful_last_reverse_patched_preserves_above
    (i : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * i + 3 ≤ p) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched i) f p = f p := by
  unfold gidney_adder_bit_step_faithful_last_reverse_patched
  rw [Gate.applyNat_seq]
  have h_ci : p ≠ carry_idx i := by unfold carry_idx; omega
  rw [Gate.applyNat_CX, update_neq _ _ _ _ h_ci]
  exact gidney_adder_bit_step_faithful_last_reverse_preserves_above i f p hp

/-! ### Cascade frame lemmas -/

/-- `forward_with_propagation k` preserves positions `≥ 3 * k + 2`. -/
theorem gidney_adder_forward_with_propagation_preserves_above
    (k : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * k + 2 ≤ p) :
    Gate.applyNat (gidney_adder_forward_with_propagation k) f p = f p := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      match k with
      | 0 =>
          show Gate.applyNat gidney_adder_bit_step_faithful_first f p = f p
          exact gidney_adder_bit_step_faithful_first_preserves_above f p (by omega)
      | k + 1 =>
          show Gate.applyNat (Gate.seq (gidney_adder_forward_with_propagation (k+1))
                                       (gidney_adder_bit_step_faithful_interior (k+1))) f p = f p
          rw [Gate.applyNat_seq]
          rw [gidney_adder_bit_step_faithful_interior_preserves_above (k+1) _ p (by omega)]
          exact ih _ (by omega)

/-- `forward_with_propagation_reverse_patched k` preserves positions `≥ 3 * k + 2`. -/
theorem gidney_adder_forward_with_propagation_reverse_patched_preserves_above
    (k : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * k + 2 ≤ p) :
    Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched k) f p = f p := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      match k with
      | 0 =>
          show Gate.applyNat gidney_adder_bit_step_faithful_first_reverse_patched f p = f p
          exact gidney_adder_bit_step_faithful_first_reverse_patched_preserves_above f p (by omega)
      | k + 1 =>
          show Gate.applyNat (Gate.seq (gidney_adder_bit_step_faithful_interior_reverse_patched (k+1))
                                       (gidney_adder_forward_with_propagation_reverse_patched (k+1)))
                  f p = f p
          rw [Gate.applyNat_seq]
          rw [ih _ (by omega)]
          exact gidney_adder_bit_step_faithful_interior_reverse_patched_preserves_above
                  (k+1) f p (by omega)


end FormalRV.BQAlgo
