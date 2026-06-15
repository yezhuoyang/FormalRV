import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.ModMult.Internal.Encoding
import FormalRV.Arithmetic.ModMult.Internal.Spec
import FormalRV.Arithmetic.ModMult.Internal.QStart
import FormalRV.Arithmetic.ModMult.Internal.Family
import FormalRV.Arithmetic.ModMult.Internal.PrefixInvariant

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-- q_start port of `modmult_swap_acc_mult_aux_at_target_out_range` (line 3118).
At an accumulator bit `i ≥ k`, swap output = input. -/
theorem modmult_swap_acc_mult_at_target_out_range_qstart
    (bits q_start k i : Nat) (hk : k ≤ bits) (hi_ge : k ≤ i) (hi_bits : i < bits)
    (f : Nat → Bool) :
    Gate.applyNat (modmult_swap_acc_mult_aux_qstart bits q_start k) f
        (modmult_target_idx_qstart q_start i)
      = f (modmult_target_idx_qstart q_start i) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [modmult_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (modmult_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    have h_i_ne_n : i ≠ n := by omega
    have h_ne_mult_n :
        modmult_target_idx_qstart q_start i
          ≠ mult_control_idx_qstart bits q_start n :=
      modmult_target_idx_ne_mult_control_idx_qstart bits q_start i n hi_bits
    have h_ne_target_n :
        modmult_target_idx_qstart q_start i ≠ modmult_target_idx_qstart q_start n := by
      unfold modmult_target_idx_qstart; omega
    rw [update_neq _ _ _ _ h_ne_mult_n]
    rw [update_neq _ _ _ _ h_ne_target_n]
    exact ih (by omega) (by omega)

/-- q_start port of `modmult_swap_acc_mult_aux_at_target_in_range` (line 3139).
At an accumulator bit `i < k`, swap output = input at the matched
multiplier position. -/
theorem modmult_swap_acc_mult_at_target_in_range_qstart
    (bits q_start k i : Nat) (hk : k ≤ bits) (hi_k : i < k) (f : Nat → Bool) :
    Gate.applyNat (modmult_swap_acc_mult_aux_qstart bits q_start k) f
        (modmult_target_idx_qstart q_start i)
      = f (mult_control_idx_qstart bits q_start i) := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hn_lt : n < bits := by omega
    have hi_bits : i < bits := by omega
    rw [modmult_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (modmult_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    by_cases hi_eq : i = n
    · subst hi_eq
      rw [update_neq _ _ _ _
            (modmult_target_idx_ne_mult_control_idx_qstart bits q_start i i hi_bits)]
      rw [update_eq]
      exact modmult_swap_acc_mult_at_mult_out_range_qstart bits q_start i i
              (by omega) (le_refl _) hi_bits f
    · have h_ne_mult_n :
          modmult_target_idx_qstart q_start i
            ≠ mult_control_idx_qstart bits q_start n :=
        modmult_target_idx_ne_mult_control_idx_qstart bits q_start i n hi_bits
      have h_ne_target_n :
          modmult_target_idx_qstart q_start i ≠ modmult_target_idx_qstart q_start n := by
        unfold modmult_target_idx_qstart; omega
      rw [update_neq _ _ _ _ h_ne_mult_n]
      rw [update_neq _ _ _ _ h_ne_target_n]
      exact ih (by omega) (by omega)

/-- q_start port of `modmult_swap_acc_mult_aux_at_mult_in_range` (line 3164).
At a multiplier bit `i < k`, swap output = input at matched target. -/
theorem modmult_swap_acc_mult_at_mult_in_range_qstart
    (bits q_start k i : Nat) (hk : k ≤ bits) (hi_k : i < k) (f : Nat → Bool) :
    Gate.applyNat (modmult_swap_acc_mult_aux_qstart bits q_start k) f
        (mult_control_idx_qstart bits q_start i)
      = f (modmult_target_idx_qstart q_start i) := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hn_lt : n < bits := by omega
    have hi_bits : i < bits := by omega
    rw [modmult_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (modmult_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    by_cases hi_eq : i = n
    · subst hi_eq
      rw [update_eq]
      exact modmult_swap_acc_mult_at_target_out_range_qstart bits q_start i i
              (by omega) (le_refl _) hi_bits f
    · have h_ne_mult_n :
          mult_control_idx_qstart bits q_start i
            ≠ mult_control_idx_qstart bits q_start n := by
        intro heq
        exact hi_eq (mult_control_idx_injective_qstart bits q_start i n heq)
      have h_ne_target_n :
          mult_control_idx_qstart bits q_start i
            ≠ modmult_target_idx_qstart q_start n :=
        (modmult_target_idx_ne_mult_control_idx_qstart bits q_start n i hn_lt).symm
      rw [update_neq _ _ _ _ h_ne_mult_n]
      rw [update_neq _ _ _ _ h_ne_target_n]
      exact ih (by omega) (by omega)

/-- q_start port of `modmult_swap_acc_mult_aux_at_other` (line 3189).
At any position outside the swap range, output = input. -/
theorem modmult_swap_acc_mult_at_other_qstart
    (bits q_start k q : Nat) (hk : k ≤ bits) (f : Nat → Bool)
    (h_q_not_target : ∀ i, i < k → q ≠ modmult_target_idx_qstart q_start i)
    (h_q_not_mult : ∀ i, i < k → q ≠ mult_control_idx_qstart bits q_start i) :
    Gate.applyNat (modmult_swap_acc_mult_aux_qstart bits q_start k) f q = f q := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [modmult_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (modmult_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    have h_q_ne_target_n : q ≠ modmult_target_idx_qstart q_start n :=
      h_q_not_target n (by omega)
    have h_q_ne_mult_n : q ≠ mult_control_idx_qstart bits q_start n :=
      h_q_not_mult n (by omega)
    rw [update_neq _ _ _ _ h_q_ne_mult_n]
    rw [update_neq _ _ _ _ h_q_ne_target_n]
    exact ih (by omega)
            (fun i hi => h_q_not_target i (by omega))
            (fun i hi => h_q_not_mult i (by omega))

/-! ### Full swap correctness on `mult_input_F_qstart`. -/

/-- q_start port of `modmult_swap_acc_mult_apply` (line 3215).  Full SWAP
correctness on `mult_input_F_qstart`. -/
theorem modmult_swap_acc_mult_apply_qstart
    (bits q_start m acc : Nat) (hbits : 1 ≤ bits)
    (hm : m < 2^bits) (hacc : acc < 2^bits) :
    Gate.applyNat (modmult_swap_acc_mult_qstart bits q_start)
        (mult_input_F_qstart bits q_start m acc)
      = mult_input_F_qstart bits q_start acc m := by
  unfold modmult_swap_acc_mult_qstart
  funext q
  by_cases h_target : ∃ i, i < bits ∧ q = modmult_target_idx_qstart q_start i
  · obtain ⟨i, hi, hq_eq⟩ := h_target
    rw [hq_eq]
    rw [modmult_swap_acc_mult_at_target_in_range_qstart bits q_start bits i (le_refl _) hi]
    rw [mult_input_control_bit_qstart bits q_start m acc i hi]
    show m.testBit i = mult_input_F_qstart bits q_start acc m
                          (modmult_target_idx_qstart q_start i)
    unfold mult_input_F_qstart
    rw [modmult_target_idx_qstart_value]
    rw [if_pos (by omega : q_start + 2 * i + 1 < q_start + 2 * bits + 1)]
    exact (cuccaro_input_F_at_b q_start i false 0 m).symm
  · by_cases h_mult : ∃ i, i < bits ∧ q = mult_control_idx_qstart bits q_start i
    · obtain ⟨i, hi, hq_eq⟩ := h_mult
      rw [hq_eq]
      rw [modmult_swap_acc_mult_at_mult_in_range_qstart bits q_start bits i (le_refl _) hi]
      have h_lhs : mult_input_F_qstart bits q_start m acc
                     (modmult_target_idx_qstart q_start i) = acc.testBit i := by
        unfold mult_input_F_qstart modmult_target_idx_qstart
        rw [if_pos (by omega : q_start + 2 * i + 1 < q_start + 2 * bits + 1)]
        exact cuccaro_input_F_at_b q_start i false 0 acc
      rw [h_lhs]
      exact (mult_input_control_bit_qstart bits q_start acc m i hi).symm
    · have h_not_target : ∀ i, i < bits → q ≠ modmult_target_idx_qstart q_start i := by
        intros i hi heq
        exact h_target ⟨i, hi, heq⟩
      have h_not_mult :
          ∀ i, i < bits → q ≠ mult_control_idx_qstart bits q_start i := by
        intros i hi heq
        exact h_mult ⟨i, hi, heq⟩
      rw [modmult_swap_acc_mult_at_other_qstart bits q_start bits q (le_refl _) _
            h_not_target h_not_mult]
      by_cases hq_ws : q < q_start + 2 * bits + 1
      · unfold mult_input_F_qstart
        rw [if_pos hq_ws, if_pos hq_ws]
        unfold cuccaro_input_F
        by_cases hq_below : q < q_start
        · rw [if_pos hq_below, if_pos hq_below]
        · push_neg at hq_below
          rw [if_neg (by omega : ¬ q < q_start),
              if_neg (by omega : ¬ q < q_start)]
          by_cases hq_q_start : q - q_start = 0
          · rw [if_pos hq_q_start, if_pos hq_q_start]
          · rw [if_neg hq_q_start, if_neg hq_q_start]
            by_cases hq_odd : (q - q_start) % 2 = 1
            · rw [if_pos hq_odd, if_pos hq_odd]
              exfalso
              have hi_bound : (q - q_start - 1) / 2 < bits := by omega
              have h_eq : q = modmult_target_idx_qstart q_start
                                ((q - q_start - 1) / 2) := by
                unfold modmult_target_idx_qstart; omega
              exact h_not_target ((q - q_start - 1) / 2) hi_bound h_eq
            · rw [if_neg hq_odd, if_neg hq_odd]
      · push_neg at hq_ws
        unfold mult_input_F_qstart
        rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1)]
        rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1)]
        by_cases hq_in_mult : q < q_start + 2 * bits + 1 + bits
        · rw [if_pos hq_in_mult, if_pos hq_in_mult]
          exfalso
          set k := q - (q_start + 2 * bits + 1)
          have hk_lt : k < bits := by omega
          have hq_eq : q = mult_control_idx_qstart bits q_start k := by
            unfold mult_control_idx_qstart; omega
          exact h_not_mult k hk_lt hq_eq
        · rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1 + bits)]
          rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1 + bits)]

theorem modmult_target_idx_ne_mult_control_idx
    (bits i j : Nat) (hi : i < bits) :
    modmult_target_idx i ≠ mult_control_idx bits j := by
  unfold modmult_target_idx mult_control_idx
  omega

theorem modmult_swap_acc_mult_aux_succ_eq (bits k : Nat) :
    modmult_swap_acc_mult_aux bits (k + 1)
      = Gate.seq (modmult_swap_acc_mult_aux bits k)
          (qubit_swap (modmult_target_idx k) (mult_control_idx bits k)) := rfl

/-- **WellTyped for `modmult_swap_acc_mult_aux`.** -/
theorem modmult_swap_acc_mult_aux_wellTyped
    (bits k : Nat) (hbits : 1 ≤ bits) (hk : k ≤ bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits) (modmult_swap_acc_mult_aux bits k) := by
  induction k with
  | zero =>
    show 0 < sqir_modmult_rev_anc bits
    unfold sqir_modmult_rev_anc; omega
  | succ n ih =>
    rw [modmult_swap_acc_mult_aux_succ_eq]
    refine ⟨ih (by omega), ?_⟩
    apply qubit_swap_wellTyped
    · unfold modmult_target_idx sqir_modmult_rev_anc; omega
    · exact mult_control_idx_lt_sqir_dim bits n (by omega)
    · exact modmult_target_idx_ne_mult_control_idx bits n n (by omega)

theorem modmult_swap_acc_mult_wellTyped
    (bits : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits) (modmult_swap_acc_mult bits) :=
  modmult_swap_acc_mult_aux_wellTyped bits bits hbits (le_refl _)

end FormalRV.BQAlgo
