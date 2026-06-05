import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultDefinitions
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultPrefixInvariant

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-- q_start port of `sqir_swap_acc_mult_aux_at_target_out_range` (line 3118).
At an accumulator bit `i ≥ k`, swap output = input. -/
theorem sqir_swap_acc_mult_at_target_out_range_qstart
    (bits q_start k i : Nat) (hk : k ≤ bits) (hi_ge : k ≤ i) (hi_bits : i < bits)
    (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux_qstart bits q_start k) f
        (sqir_target_idx_qstart q_start i)
      = f (sqir_target_idx_qstart q_start i) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [sqir_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    have h_i_ne_n : i ≠ n := by omega
    have h_ne_mult_n :
        sqir_target_idx_qstart q_start i
          ≠ sqir_mult_control_idx_qstart bits q_start n :=
      sqir_target_idx_ne_mult_control_idx_qstart bits q_start i n hi_bits
    have h_ne_target_n :
        sqir_target_idx_qstart q_start i ≠ sqir_target_idx_qstart q_start n := by
      unfold sqir_target_idx_qstart; omega
    rw [update_neq _ _ _ _ h_ne_mult_n]
    rw [update_neq _ _ _ _ h_ne_target_n]
    exact ih (by omega) (by omega)

/-- q_start port of `sqir_swap_acc_mult_aux_at_target_in_range` (line 3139).
At an accumulator bit `i < k`, swap output = input at the matched
multiplier position. -/
theorem sqir_swap_acc_mult_at_target_in_range_qstart
    (bits q_start k i : Nat) (hk : k ≤ bits) (hi_k : i < k) (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux_qstart bits q_start k) f
        (sqir_target_idx_qstart q_start i)
      = f (sqir_mult_control_idx_qstart bits q_start i) := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hn_lt : n < bits := by omega
    have hi_bits : i < bits := by omega
    rw [sqir_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    by_cases hi_eq : i = n
    · subst hi_eq
      rw [update_neq _ _ _ _
            (sqir_target_idx_ne_mult_control_idx_qstart bits q_start i i hi_bits)]
      rw [update_eq]
      exact sqir_swap_acc_mult_at_mult_out_range_qstart bits q_start i i
              (by omega) (le_refl _) hi_bits f
    · have h_ne_mult_n :
          sqir_target_idx_qstart q_start i
            ≠ sqir_mult_control_idx_qstart bits q_start n :=
        sqir_target_idx_ne_mult_control_idx_qstart bits q_start i n hi_bits
      have h_ne_target_n :
          sqir_target_idx_qstart q_start i ≠ sqir_target_idx_qstart q_start n := by
        unfold sqir_target_idx_qstart; omega
      rw [update_neq _ _ _ _ h_ne_mult_n]
      rw [update_neq _ _ _ _ h_ne_target_n]
      exact ih (by omega) (by omega)

/-- q_start port of `sqir_swap_acc_mult_aux_at_mult_in_range` (line 3164).
At a multiplier bit `i < k`, swap output = input at matched target. -/
theorem sqir_swap_acc_mult_at_mult_in_range_qstart
    (bits q_start k i : Nat) (hk : k ≤ bits) (hi_k : i < k) (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux_qstart bits q_start k) f
        (sqir_mult_control_idx_qstart bits q_start i)
      = f (sqir_target_idx_qstart q_start i) := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hn_lt : n < bits := by omega
    have hi_bits : i < bits := by omega
    rw [sqir_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    by_cases hi_eq : i = n
    · subst hi_eq
      rw [update_eq]
      exact sqir_swap_acc_mult_at_target_out_range_qstart bits q_start i i
              (by omega) (le_refl _) hi_bits f
    · have h_ne_mult_n :
          sqir_mult_control_idx_qstart bits q_start i
            ≠ sqir_mult_control_idx_qstart bits q_start n := by
        intro heq
        exact hi_eq (sqir_mult_control_idx_injective_qstart bits q_start i n heq)
      have h_ne_target_n :
          sqir_mult_control_idx_qstart bits q_start i
            ≠ sqir_target_idx_qstart q_start n :=
        (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n i hn_lt).symm
      rw [update_neq _ _ _ _ h_ne_mult_n]
      rw [update_neq _ _ _ _ h_ne_target_n]
      exact ih (by omega) (by omega)

/-- q_start port of `sqir_swap_acc_mult_aux_at_other` (line 3189).
At any position outside the swap range, output = input. -/
theorem sqir_swap_acc_mult_at_other_qstart
    (bits q_start k q : Nat) (hk : k ≤ bits) (f : Nat → Bool)
    (h_q_not_target : ∀ i, i < k → q ≠ sqir_target_idx_qstart q_start i)
    (h_q_not_mult : ∀ i, i < k → q ≠ sqir_mult_control_idx_qstart bits q_start i) :
    Gate.applyNat (sqir_swap_acc_mult_aux_qstart bits q_start k) f q = f q := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [sqir_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    have h_q_ne_target_n : q ≠ sqir_target_idx_qstart q_start n :=
      h_q_not_target n (by omega)
    have h_q_ne_mult_n : q ≠ sqir_mult_control_idx_qstart bits q_start n :=
      h_q_not_mult n (by omega)
    rw [update_neq _ _ _ _ h_q_ne_mult_n]
    rw [update_neq _ _ _ _ h_q_ne_target_n]
    exact ih (by omega)
            (fun i hi => h_q_not_target i (by omega))
            (fun i hi => h_q_not_mult i (by omega))

/-! ### Full swap correctness on `sqir_mult_input_F_qstart`. -/

/-- q_start port of `sqir_swap_acc_mult_apply` (line 3215).  Full SWAP
correctness on `sqir_mult_input_F_qstart`. -/
theorem sqir_swap_acc_mult_apply_qstart
    (bits q_start m acc : Nat) (hbits : 1 ≤ bits)
    (hm : m < 2^bits) (hacc : acc < 2^bits) :
    Gate.applyNat (sqir_swap_acc_mult_qstart bits q_start)
        (sqir_mult_input_F_qstart bits q_start m acc)
      = sqir_mult_input_F_qstart bits q_start acc m := by
  unfold sqir_swap_acc_mult_qstart
  funext q
  by_cases h_target : ∃ i, i < bits ∧ q = sqir_target_idx_qstart q_start i
  · obtain ⟨i, hi, hq_eq⟩ := h_target
    rw [hq_eq]
    rw [sqir_swap_acc_mult_at_target_in_range_qstart bits q_start bits i (le_refl _) hi]
    rw [sqir_mult_input_control_bit_qstart bits q_start m acc i hi]
    show m.testBit i = sqir_mult_input_F_qstart bits q_start acc m
                          (sqir_target_idx_qstart q_start i)
    unfold sqir_mult_input_F_qstart
    rw [sqir_target_idx_qstart_value]
    rw [if_pos (by omega : q_start + 2 * i + 1 < q_start + 2 * bits + 1)]
    exact (cuccaro_input_F_at_b q_start i false 0 m).symm
  · by_cases h_mult : ∃ i, i < bits ∧ q = sqir_mult_control_idx_qstart bits q_start i
    · obtain ⟨i, hi, hq_eq⟩ := h_mult
      rw [hq_eq]
      rw [sqir_swap_acc_mult_at_mult_in_range_qstart bits q_start bits i (le_refl _) hi]
      have h_lhs : sqir_mult_input_F_qstart bits q_start m acc
                     (sqir_target_idx_qstart q_start i) = acc.testBit i := by
        unfold sqir_mult_input_F_qstart sqir_target_idx_qstart
        rw [if_pos (by omega : q_start + 2 * i + 1 < q_start + 2 * bits + 1)]
        exact cuccaro_input_F_at_b q_start i false 0 acc
      rw [h_lhs]
      exact (sqir_mult_input_control_bit_qstart bits q_start acc m i hi).symm
    · have h_not_target : ∀ i, i < bits → q ≠ sqir_target_idx_qstart q_start i := by
        intros i hi heq
        exact h_target ⟨i, hi, heq⟩
      have h_not_mult :
          ∀ i, i < bits → q ≠ sqir_mult_control_idx_qstart bits q_start i := by
        intros i hi heq
        exact h_mult ⟨i, hi, heq⟩
      rw [sqir_swap_acc_mult_at_other_qstart bits q_start bits q (le_refl _) _
            h_not_target h_not_mult]
      by_cases hq_ws : q < q_start + 2 * bits + 1
      · unfold sqir_mult_input_F_qstart
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
              have h_eq : q = sqir_target_idx_qstart q_start
                                ((q - q_start - 1) / 2) := by
                unfold sqir_target_idx_qstart; omega
              exact h_not_target ((q - q_start - 1) / 2) hi_bound h_eq
            · rw [if_neg hq_odd, if_neg hq_odd]
      · push_neg at hq_ws
        unfold sqir_mult_input_F_qstart
        rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1)]
        rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1)]
        by_cases hq_in_mult : q < q_start + 2 * bits + 1 + bits
        · rw [if_pos hq_in_mult, if_pos hq_in_mult]
          exfalso
          set k := q - (q_start + 2 * bits + 1)
          have hk_lt : k < bits := by omega
          have hq_eq : q = sqir_mult_control_idx_qstart bits q_start k := by
            unfold sqir_mult_control_idx_qstart; omega
          exact h_not_mult k hk_lt hq_eq
        · rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1 + bits)]
          rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1 + bits)]

theorem sqir_target_idx_ne_mult_control_idx
    (bits i j : Nat) (hi : i < bits) :
    sqir_target_idx i ≠ sqir_mult_control_idx bits j := by
  unfold sqir_target_idx sqir_mult_control_idx
  omega

theorem sqir_swap_acc_mult_aux_succ_eq (bits k : Nat) :
    sqir_swap_acc_mult_aux bits (k + 1)
      = Gate.seq (sqir_swap_acc_mult_aux bits k)
          (qubit_swap (sqir_target_idx k) (sqir_mult_control_idx bits k)) := rfl

/-- **WellTyped for `sqir_swap_acc_mult_aux`.** -/
theorem sqir_swap_acc_mult_aux_wellTyped
    (bits k : Nat) (hbits : 1 ≤ bits) (hk : k ≤ bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits) (sqir_swap_acc_mult_aux bits k) := by
  induction k with
  | zero =>
    show 0 < sqir_modmult_rev_anc bits
    unfold sqir_modmult_rev_anc; omega
  | succ n ih =>
    rw [sqir_swap_acc_mult_aux_succ_eq]
    refine ⟨ih (by omega), ?_⟩
    apply qubit_swap_wellTyped
    · unfold sqir_target_idx sqir_modmult_rev_anc; omega
    · exact sqir_mult_control_idx_lt_sqir_dim bits n (by omega)
    · exact sqir_target_idx_ne_mult_control_idx bits n n (by omega)

theorem sqir_swap_acc_mult_wellTyped
    (bits : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits) (sqir_swap_acc_mult bits) :=
  sqir_swap_acc_mult_aux_wellTyped bits bits hbits (le_refl _)

/-! ## Per-position behavior of `sqir_swap_acc_mult_aux`. -/

/-- **At a multiplier bit `i ≥ k`, swap output = input.** -/
theorem sqir_swap_acc_mult_aux_at_mult_out_range
    (bits k i : Nat) (hk : k ≤ bits) (hi_ge : k ≤ i) (hi_bits : i < bits) (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux bits k) f (sqir_mult_control_idx bits i)
      = f (sqir_mult_control_idx bits i) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [sqir_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (sqir_target_idx_ne_mult_control_idx bits n n hn_lt)]
    have h_i_ne_n : i ≠ n := by omega
    have h_ne_mult_n : sqir_mult_control_idx bits i ≠ sqir_mult_control_idx bits n := by
      intro heq
      exact h_i_ne_n (sqir_mult_control_idx_injective bits i n heq)
    have h_ne_target_n : sqir_mult_control_idx bits i ≠ sqir_target_idx n :=
      (sqir_target_idx_ne_mult_control_idx bits n i hn_lt).symm
    rw [update_neq _ _ _ _ h_ne_mult_n]
    rw [update_neq _ _ _ _ h_ne_target_n]
    exact ih (by omega) (by omega)

/-- **At an accumulator bit `i ≥ k`, swap output = input.** -/
theorem sqir_swap_acc_mult_aux_at_target_out_range
    (bits k i : Nat) (hk : k ≤ bits) (hi_ge : k ≤ i) (hi_bits : i < bits) (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux bits k) f (sqir_target_idx i)
      = f (sqir_target_idx i) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [sqir_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (sqir_target_idx_ne_mult_control_idx bits n n hn_lt)]
    have h_i_ne_n : i ≠ n := by omega
    have h_ne_mult_n : sqir_target_idx i ≠ sqir_mult_control_idx bits n :=
      sqir_target_idx_ne_mult_control_idx bits i n hi_bits
    have h_ne_target_n : sqir_target_idx i ≠ sqir_target_idx n := by
      unfold sqir_target_idx; omega
    rw [update_neq _ _ _ _ h_ne_mult_n]
    rw [update_neq _ _ _ _ h_ne_target_n]
    exact ih (by omega) (by omega)

/-- **At an accumulator bit `i < k`, swap output = input at the matched
multiplier position.** -/
theorem sqir_swap_acc_mult_aux_at_target_in_range
    (bits k i : Nat) (hk : k ≤ bits) (hi_k : i < k) (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux bits k) f (sqir_target_idx i)
      = f (sqir_mult_control_idx bits i) := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hn_lt : n < bits := by omega
    have hi_bits : i < bits := by omega
    rw [sqir_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (sqir_target_idx_ne_mult_control_idx bits n n hn_lt)]
    by_cases hi_eq : i = n
    · subst hi_eq
      rw [update_neq _ _ _ _ (sqir_target_idx_ne_mult_control_idx bits i i hi_bits)]
      rw [update_eq]
      exact sqir_swap_acc_mult_aux_at_mult_out_range bits i i (by omega) (le_refl _) hi_bits f
    · have h_ne_mult_n : sqir_target_idx i ≠ sqir_mult_control_idx bits n :=
        sqir_target_idx_ne_mult_control_idx bits i n hi_bits
      have h_ne_target_n : sqir_target_idx i ≠ sqir_target_idx n := by
        unfold sqir_target_idx; omega
      rw [update_neq _ _ _ _ h_ne_mult_n]
      rw [update_neq _ _ _ _ h_ne_target_n]
      exact ih (by omega) (by omega)

/-- **At a multiplier bit `i < k`, swap output = input at matched target.** -/
theorem sqir_swap_acc_mult_aux_at_mult_in_range
    (bits k i : Nat) (hk : k ≤ bits) (hi_k : i < k) (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux bits k) f (sqir_mult_control_idx bits i)
      = f (sqir_target_idx i) := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hn_lt : n < bits := by omega
    have hi_bits : i < bits := by omega
    rw [sqir_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (sqir_target_idx_ne_mult_control_idx bits n n hn_lt)]
    by_cases hi_eq : i = n
    · subst hi_eq
      rw [update_eq]
      exact sqir_swap_acc_mult_aux_at_target_out_range bits i i (by omega) (le_refl _) hi_bits f
    · have h_ne_mult_n : sqir_mult_control_idx bits i ≠ sqir_mult_control_idx bits n := by
        intro heq
        exact hi_eq (sqir_mult_control_idx_injective bits i n heq)
      have h_ne_target_n : sqir_mult_control_idx bits i ≠ sqir_target_idx n :=
        (sqir_target_idx_ne_mult_control_idx bits n i hn_lt).symm
      rw [update_neq _ _ _ _ h_ne_mult_n]
      rw [update_neq _ _ _ _ h_ne_target_n]
      exact ih (by omega) (by omega)

/-- **At any position outside the swap range, output = input.** -/
theorem sqir_swap_acc_mult_aux_at_other
    (bits k q : Nat) (hk : k ≤ bits) (f : Nat → Bool)
    (h_q_not_target : ∀ i, i < k → q ≠ sqir_target_idx i)
    (h_q_not_mult : ∀ i, i < k → q ≠ sqir_mult_control_idx bits i) :
    Gate.applyNat (sqir_swap_acc_mult_aux bits k) f q = f q := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [sqir_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (sqir_target_idx_ne_mult_control_idx bits n n hn_lt)]
    have h_q_ne_target_n : q ≠ sqir_target_idx n := h_q_not_target n (by omega)
    have h_q_ne_mult_n : q ≠ sqir_mult_control_idx bits n := h_q_not_mult n (by omega)
    rw [update_neq _ _ _ _ h_q_ne_mult_n]
    rw [update_neq _ _ _ _ h_q_ne_target_n]
    exact ih (by omega)
            (fun i hi => h_q_not_target i (by omega))
            (fun i hi => h_q_not_mult i (by omega))

/-! ## Full swap correctness on `sqir_mult_input_F`. -/

/-- **Sanity helper:** `sqir_target_idx i = 2 + 2*i + 1`. -/
theorem sqir_target_idx_value (i : Nat) :
    sqir_target_idx i = 2 + 2 * i + 1 := rfl

/-- **Full SWAP correctness on `sqir_mult_input_F`.** -/
theorem sqir_swap_acc_mult_apply
    (bits m acc : Nat) (hbits : 1 ≤ bits)
    (hm : m < 2^bits) (hacc : acc < 2^bits) :
    Gate.applyNat (sqir_swap_acc_mult bits) (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits acc m := by
  unfold sqir_swap_acc_mult
  funext q
  -- Case split on q's role.
  by_cases h_target : ∃ i, i < bits ∧ q = sqir_target_idx i
  · obtain ⟨i, hi, hq_eq⟩ := h_target
    rw [hq_eq]
    rw [sqir_swap_acc_mult_aux_at_target_in_range bits bits i (le_refl _) hi]
    rw [sqir_mult_input_control_bit bits m acc i hi]
    -- RHS: sqir_mult_input_F bits acc m at sqir_target_idx i = m.testBit i.
    -- sqir_target_idx i = 2 + 2*i + 1 — workspace.
    show m.testBit i = sqir_mult_input_F bits acc m (sqir_target_idx i)
    unfold sqir_mult_input_F
    rw [sqir_target_idx_value]
    rw [if_pos (by omega : 2 + 2 * i + 1 < 2 + 2 * bits + 1)]
    exact (cuccaro_input_F_at_b 2 i false 0 m).symm
  · by_cases h_mult : ∃ i, i < bits ∧ q = sqir_mult_control_idx bits i
    · obtain ⟨i, hi, hq_eq⟩ := h_mult
      rw [hq_eq]
      rw [sqir_swap_acc_mult_aux_at_mult_in_range bits bits i (le_refl _) hi]
      -- LHS: input (target_idx i) = acc.testBit i.
      have h_lhs : sqir_mult_input_F bits m acc (sqir_target_idx i) = acc.testBit i := by
        unfold sqir_mult_input_F sqir_target_idx
        rw [if_pos (by omega : 2 + 2 * i + 1 < 2 + 2 * bits + 1)]
        exact cuccaro_input_F_at_b 2 i false 0 acc
      rw [h_lhs]
      -- RHS: sqir_mult_input_F bits acc m at sqir_mult_control_idx bits i = acc.testBit i.
      exact (sqir_mult_input_control_bit bits acc m i hi).symm
    · -- Other positions: unchanged by swap, AND sqir_mult_input_F at q with swapped args
      --   equals sqir_mult_input_F at q with original args (since both depend only on
      --   workspace structure, not m or acc, at these positions).
      have h_not_target : ∀ i, i < bits → q ≠ sqir_target_idx i := by
        intros i hi heq
        exact h_target ⟨i, hi, heq⟩
      have h_not_mult : ∀ i, i < bits → q ≠ sqir_mult_control_idx bits i := by
        intros i hi heq
        exact h_mult ⟨i, hi, heq⟩
      rw [sqir_swap_acc_mult_aux_at_other bits bits q (le_refl _) _ h_not_target h_not_mult]
      -- Now: sqir_mult_input_F bits m acc q = sqir_mult_input_F bits acc m q.
      -- For workspace q (not target bit): depends only on q's position class.
      -- For mult register q (not mult_i for any i): impossible — q outside layout.
      -- For above-layout q: both = false.
      by_cases hq_ws : q < 2 + 2 * bits + 1
      · -- Workspace q.  q is not a target bit (h_not_target).
        unfold sqir_mult_input_F
        rw [if_pos hq_ws, if_pos hq_ws]
        -- cuccaro_input_F at q for both sides: depends only on q since a = 0, c_in = false.
        -- Only the "b" (target) bits depend on acc/m.  We need to show q isn't a target bit.
        unfold cuccaro_input_F
        by_cases hq_below : q < 2
        · rw [if_pos hq_below, if_pos hq_below]
        · push_neg at hq_below
          rw [if_neg (by omega : ¬ q < 2), if_neg (by omega : ¬ q < 2)]
          by_cases hq_q_start : q - 2 = 0
          · rw [if_pos hq_q_start, if_pos hq_q_start]
          · rw [if_neg hq_q_start, if_neg hq_q_start]
            by_cases hq_odd : (q - 2) % 2 = 1
            · -- Odd: would be target bit.  But q is not a target bit by h_not_target.
              rw [if_pos hq_odd, if_pos hq_odd]
              -- Goal: acc.testBit ((q - 2 - 1) / 2) = m.testBit ((q - 2 - 1) / 2)
              -- Wait, both functions return b.testBit ... where b is the second
              -- argument (target value).  In our case b = acc on LHS, b = m on RHS.
              -- But we said q is not a target bit; in cuccaro_input_F, the
              -- "b position" is q_start + 2*i + 1 for some i.  We have q ≥ 2, q - 2 = 2*i + 1
              -- for some i ≥ 0.  Need i < bits for it to be a "target bit" in our layout.
              -- Since q < 2 + 2*bits + 1, q - 2 < 2*bits + 1, so 2*i + 1 < 2*bits + 1, i.e., i < bits.
              -- So q IS a target bit (sqir_target_idx i = 2 + 2*i + 1 = q).
              -- Contradiction with h_not_target.
              exfalso
              have hi_bound : (q - 2 - 1) / 2 < bits := by omega
              have h_eq : q = sqir_target_idx ((q - 2 - 1) / 2) := by
                unfold sqir_target_idx; omega
              exact h_not_target ((q - 2 - 1) / 2) hi_bound h_eq
            · rw [if_neg hq_odd, if_neg hq_odd]
      · -- q ≥ 2 + 2*bits + 1.  Could be a multiplier bit (but excluded) or above-layout.
        push_neg at hq_ws
        unfold sqir_mult_input_F
        rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
        rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
        by_cases hq_in_mult : q < 2 + 2 * bits + 1 + bits
        · -- q in multiplier register.
          rw [if_pos hq_in_mult, if_pos hq_in_mult]
          -- The mult value depends on the first arg.  LHS = m.testBit ..., RHS = acc.testBit ...
          -- But h_not_mult says q ≠ sqir_mult_control_idx bits i for any i < bits.
          -- For q in [2 + 2*bits + 1, 2 + 2*bits + 1 + bits), q = 2 + 2*bits + 1 + k
          --   where k = q - (2 + 2*bits + 1) < bits.  So q = sqir_mult_control_idx bits k.
          -- Contradiction with h_not_mult.
          exfalso
          set k := q - (2 + 2 * bits + 1)
          have hk_lt : k < bits := by omega
          have hq_eq : q = sqir_mult_control_idx bits k := by
            unfold sqir_mult_control_idx; omega
          exact h_not_mult k hk_lt hq_eq
        · -- q ≥ 2 + 2*bits + 1 + bits: above layout.  Both = false.
          rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]
          rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]

/-! ## Tick 77 — Task 4: Modular inverse arithmetic. -/

/-- **Modular inverse clear arithmetic.**

If `(a * ainv) % N = 1`, then
`(x + ((N - ainv) % N) * ((a * x) % N)) % N = 0`. -/
theorem sqir_modmult_inverse_clear_arith
    (N a ainv x : Nat) (hN_pos : 0 < N) (hx : x < N) (h_ainv_le : ainv ≤ N)
    (h_inv : (a * ainv) % N = 1) :
    (x + ((N - ainv) % N) * ((a * x) % N)) % N = 0 := by
  -- Step 0: combine the inner mods.
  have h_combined :
      (x + ((N - ainv) % N) * ((a * x) % N)) % N
        = (x + (N - ainv) * (a * x)) % N := by
    rw [Nat.add_mod x (((N - ainv) % N) * ((a * x) % N)) N]
    rw [← Nat.mul_mod]
    rw [← Nat.add_mod]
  rw [h_combined]
  -- Step 1: (N - ainv) * (a * x) = N*(a*x) - ainv*(a*x).
  have h_sub : (N - ainv) * (a * x) = N * (a * x) - ainv * (a * x) :=
    Nat.sub_mul N ainv (a * x)
  rw [h_sub]
  -- Step 2: x + (N * (a*x) - ainv * (a*x)).
  -- Since ainv * (a*x) ≤ N * (a*x) (because ainv ≤ N), and N*(a*x) ≤ x + N*(a*x):
  have h_le1 : ainv * (a * x) ≤ N * (a * x) := Nat.mul_le_mul_right _ h_ainv_le
  have h_le2 : ainv * (a * x) ≤ x + N * (a * x) := by omega
  -- Rewrite: x + (N * (a*x) - ainv * (a*x)) = (x + N * (a*x)) - ainv * (a*x).
  have h_assoc : x + (N * (a * x) - ainv * (a * x))
                = (x + N * (a * x)) - ainv * (a * x) := by omega
  rw [h_assoc]
  -- Now: ((x + N*(a*x)) - ainv*(a*x)) % N = 0.
  -- Let A = x + N*(a*x), B = ainv*(a*x).  Then A ≥ B and we want (A - B) % N = 0.
  set A := x + N * (a * x) with hA_def
  set B := ainv * (a * x) with hB_def
  have hB_le_A : B ≤ A := h_le2
  -- A % N = x.
  have hA_mod : A % N = x := by
    rw [hA_def, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hx
  -- B % N = x.
  have hB_mod : B % N = x := by
    rw [hB_def]
    rw [show ainv * (a * x) = (a * ainv) * x by ring]
    rw [Nat.mul_mod, h_inv, Nat.one_mul, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hx
  -- ((A - B) % N + B % N) % N = A % N (by sub_add_cancel + add_mod).
  have h_sub_add : (A - B) + B = A := Nat.sub_add_cancel hB_le_A
  have h_eq : ((A - B) + B) % N = A % N := by rw [h_sub_add]
  have h_eq_split : ((A - B) % N + B % N) % N = A % N := by
    rw [← Nat.add_mod]; exact h_eq
  rw [hA_mod, hB_mod] at h_eq_split
  -- h_eq_split : ((A - B) % N + x) % N = x.  Let R = (A - B) % N.
  set R := (A - B) % N with hR_def
  have hR_lt : R < N := Nat.mod_lt _ hN_pos
  -- (R + x) % N = x, R < N, x < N → R = 0.
  by_contra h_R_ne
  have h_R_pos : R > 0 := Nat.pos_of_ne_zero h_R_ne
  rcases Nat.lt_or_ge (R + x) N with h_lt | h_ge
  · rw [Nat.mod_eq_of_lt h_lt] at h_eq_split
    omega
  · have h_RpX_eq : (R + x) % N = R + x - N := by
      rw [Nat.mod_eq_sub_mod h_ge]
      exact Nat.mod_eq_of_lt (by omega : R + x - N < N)
    rw [h_RpX_eq] at h_eq_split
    omega

/-! ## Tick 77 — Task 5: In-place target theorem. -/

/-- **In-place modular multiplier candidate target theorem.**

After applying the in-place wrapper to `(x, 0)`, the resulting state is
`((a*x) % N, 0)` — i.e., the original "multiplier" register now holds
the product, and the accumulator is cleared. -/
theorem sqir_modmult_inplace_candidate_state_eq
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv) (sqir_mult_input_F bits x 0)
      = sqir_mult_input_F bits ((a * x) % N) 0 := by
  unfold sqir_modmult_inplace_candidate
  simp only [Gate.applyNat_seq]
  -- Step 1: Compute (x, 0) → (x, (a*x) % N).
  have hx_lt_pow : x < 2^bits := Nat.lt_of_lt_of_le hx hN
  rw [sqir_modmult_const_gate_state_eq_from bits N a x 0 hbits hN_pos hN hN2 hN_pos hx_lt_pow]
  simp only [Nat.zero_add]
  -- Step 2: Swap → ((a*x) % N, x).
  have hax_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have hax_lt_pow : (a * x) % N < 2^bits := Nat.lt_of_lt_of_le hax_lt_N hN
  rw [sqir_swap_acc_mult_apply bits x ((a * x) % N) hbits hx_lt_pow hax_lt_pow]
  -- Step 3: Uncompute with c = (N - ainv) % N.
  -- Now input is sqir_mult_input_F bits ((a*x) % N) x.
  rw [sqir_modmult_const_gate_state_eq_from bits N ((N - ainv) % N) ((a * x) % N) x
        hbits hN_pos hN hN2 hx hax_lt_pow]
  -- Result: sqir_mult_input_F bits ((a*x) % N) ((x + ((N - ainv) % N) * ((a*x) % N)) % N).
  -- By inverse arithmetic, the accumulator = 0.
  congr 1
  exact sqir_modmult_inverse_clear_arith N a ainv x hN_pos hx h_ainv_le h_inv

/-! ## R7d^xxix-L-3.15g.2 — Headline: q_start in-place modular
       multiplier state equality.

Built on:
- `sqir_modmult_const_gate_state_eq_from_qstart` (this file, L-3.15g).
- `sqir_swap_acc_mult_apply_qstart` (this file, L-3.15g.2 above).
- `sqir_modmult_inverse_clear_arith` (q_start-INDEPENDENT, above). -/

/-- q_start port of `sqir_modmult_inplace_candidate_state_eq`.

After applying the q_start in-place wrapper to `(x, 0)`, the resulting
state is `((a*x) % N, 0)` — the original "multiplier" register now
holds the product, and the accumulator is cleared. -/
theorem sqir_modmult_inplace_candidate_state_eq_qstart
    (bits q_start N a ainv x flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat
        (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
        (sqir_mult_input_F_qstart bits q_start x 0)
      = sqir_mult_input_F_qstart bits q_start ((a * x) % N) 0 := by
  unfold sqir_modmult_inplace_candidate_qstart
  simp only [Gate.applyNat_seq]
  -- Step 1: compute (x, 0) → (x, (a*x) % N).
  have hx_lt_pow : x < 2^bits := Nat.lt_of_lt_of_le hx hN
  rw [sqir_modmult_const_gate_state_eq_from_qstart bits q_start N a x 0 flagPos dim
        hbits hN_pos hN hN2 hN_pos hx_lt_pow h_flag_lt_qstart h_workspace
        h_dim_covers_mult]
  simp only [Nat.zero_add]
  -- Step 2: swap → ((a*x) % N, x).
  have hax_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have hax_lt_pow : (a * x) % N < 2^bits := Nat.lt_of_lt_of_le hax_lt_N hN
  rw [sqir_swap_acc_mult_apply_qstart bits q_start x ((a * x) % N) hbits
        hx_lt_pow hax_lt_pow]
  -- Step 3: uncompute with c = (N - ainv) % N.
  rw [sqir_modmult_const_gate_state_eq_from_qstart bits q_start N ((N - ainv) % N)
        ((a * x) % N) x flagPos dim
        hbits hN_pos hN hN2 hx hax_lt_pow h_flag_lt_qstart h_workspace
        h_dim_covers_mult]
  congr 1
  exact sqir_modmult_inverse_clear_arith N a ainv x hN_pos hx h_ainv_le h_inv

/-! ## R7d^xxix-L-3.15h — q_start in-place-clean bundle (the MCP
       prerequisite immediately below the MCP layer).

The hard-coded MCP headline at line 4218 wraps the in-place candidate
inside a `Gate.shift bits ∘ reverse_register_swap` adapter (which
re-encodes between the external `encodeDataZeroAnc` layout and the
internal SQIR layout).  That outer adapter is built on the fixed
`q_start = 2` constants in `sqir_mult_control_idx bits 0 = 2*bits + 1`
and would need a parallel q_start-parametric reverse-register adapter
plus its disjointness / well-typed / correctness chain to lift.

Per the L-3.15h fallback policy, this sub-tick lands the **clean
bundle immediately below the MCP layer** (the q_start port of
`sqir_modmult_inplace_candidate_clean`, line 3733).  The bundle
restates the in-place state-eq pointwise via the existing q_start
decoded-helper layer (lines 2488–2640), and is the input that an
adapter-bridge MCP port would consume verbatim.

Concretely the bundle yields:
- decoded target = 0;
- decoded read = 0;
- every position below `q_start` is `false` (the q_start generalisation
  of the old `flag_0`/`flag_1` conjuncts);
- top-carry = `false`;
- multiplier register decodes to `((a*x) % N).testBit k`.

Deferred to L-3.15h.2 (full MCP port):
- `sqir_modmult_rev_anc_qstart`, `sqir_total_dim_qstart`;
- `sqir_mult_input_F_shifted_qstart` (shift by `bits`);
- `sqir_encode_to_mult_adapter_qstart` + disjointness/WellTyped/
  correctness/involution/reverse chain;
- `sqir_modmult_inplace_shifted_qstart` + `_correct` + `_wellTyped`;
- `sqir_modmult_MCP_gate_qstart` + `_apply_encode` + `_wellTyped`;
- `sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty_qstart`. -/

/-- q_start port of `sqir_modmult_inplace_candidate_target_decode`
(line 3708): after the in-place wrapper, the decoded target value is `0`. -/
theorem sqir_modmult_inplace_candidate_target_decode_qstart
    (bits q_start N a ainv x flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0))
      = 0 := by
  rw [sqir_modmult_inplace_candidate_state_eq_qstart bits q_start N a ainv x
        flagPos dim hbits hN_pos hN hN2 h_ainv_le hx h_inv
        h_flag_lt_qstart h_workspace h_dim_covers_mult]
  exact sqir_mult_input_target_decode_qstart bits q_start ((a * x) % N) 0
          (Nat.two_pow_pos bits)

/-- q_start port of `sqir_modmult_inplace_candidate_mult_bit` (line 3721):
the multiplier register decodes bit-by-bit to `((a*x) % N).testBit k`. -/
theorem sqir_modmult_inplace_candidate_mult_bit_qstart
    (bits q_start N a ainv x k flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) (hk : k < bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat
        (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
        (sqir_mult_input_F_qstart bits q_start x 0)
        (sqir_mult_control_idx_qstart bits q_start k)
      = ((a * x) % N).testBit k := by
  rw [sqir_modmult_inplace_candidate_state_eq_qstart bits q_start N a ainv x
        flagPos dim hbits hN_pos hN hN2 h_ainv_le hx h_inv
        h_flag_lt_qstart h_workspace h_dim_covers_mult]
  exact sqir_mult_input_control_bit_qstart bits q_start ((a * x) % N) 0 k hk

/-- q_start port of `sqir_modmult_inplace_candidate_clean` (line 3733).

The clean bundle restating the in-place state-eq pointwise:
* `cuccaro_target_val = 0`;
* `cuccaro_read_val = 0`;
* every position below `q_start` is `false` (q_start generalisation of
  the old `flag_0`/`flag_1` conjuncts at positions 0 and 1);
* top-carry position `q_start + 2*bits` is `false`;
* multiplier-bit decoding at every `sqir_mult_control_idx_qstart bits q_start k`
  equals `((a*x) % N).testBit k`. -/
theorem sqir_modmult_inplace_candidate_clean_qstart
    (bits q_start N a ainv x flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0)) = 0
    ∧ cuccaro_read_val bits q_start
        (Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0)) = 0
    ∧ (∀ q, q < q_start →
        Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0) q = false)
    ∧ Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0) (q_start + 2 * bits) = false
    ∧ ∀ k, k < bits →
        Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0)
          (sqir_mult_control_idx_qstart bits q_start k)
          = ((a * x) % N).testBit k := by
  have h_state := sqir_modmult_inplace_candidate_state_eq_qstart bits q_start N a ainv x
    flagPos dim hbits hN_pos hN hN2 h_ainv_le hx h_inv
    h_flag_lt_qstart h_workspace h_dim_covers_mult
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h_state]
    exact sqir_mult_input_target_decode_qstart bits q_start ((a * x) % N) 0
            (Nat.two_pow_pos bits)
  · rw [h_state]; exact sqir_mult_input_read_decode_qstart bits q_start ((a * x) % N) 0
  · intro q hq
    rw [h_state]
    exact sqir_mult_input_at_below_qstart_eq_false_qstart bits q_start
            ((a * x) % N) 0 q hq
  · rw [h_state]
    exact sqir_mult_input_top_carry_false_qstart bits q_start ((a * x) % N) 0 hbits
  · intro k hk
    rw [h_state]
    exact sqir_mult_input_control_bit_qstart bits q_start ((a * x) % N) 0 k hk

/-! ## Tick 77 — Task 6: Clean workspace bundle for in-place wrapper. -/

/-- **In-place modular multiplier candidate, target decoded.** -/
theorem sqir_modmult_inplace_candidate_target_decode
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv) (sqir_mult_input_F bits x 0))
      = 0 := by
  rw [sqir_modmult_inplace_candidate_state_eq bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv]
  exact sqir_mult_input_target_decode bits ((a * x) % N) 0 (Nat.two_pow_pos bits)

/-- **In-place modular multiplier candidate, multiplier register decoded
to `(a*x) % N`.** -/
theorem sqir_modmult_inplace_candidate_mult_bit
    (bits N a ainv x k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) (hk : k < bits) :
    Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
        (sqir_mult_input_F bits x 0) (sqir_mult_control_idx bits k)
      = ((a * x) % N).testBit k := by
  rw [sqir_modmult_inplace_candidate_state_eq bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv]
  exact sqir_mult_input_control_bit bits ((a * x) % N) 0 k hk

/-- **In-place modular multiplier — clean bundle.** -/
theorem sqir_modmult_inplace_candidate_clean
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
          (sqir_mult_input_F bits x 0)) = 0
    ∧ cuccaro_read_val bits 2
        (Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
          (sqir_mult_input_F bits x 0)) = 0
    ∧ Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
          (sqir_mult_input_F bits x 0) 0 = false
    ∧ Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
          (sqir_mult_input_F bits x 0) 1 = false
    ∧ Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
          (sqir_mult_input_F bits x 0) (2 + 2 * bits) = false
    ∧ ∀ k, k < bits →
        Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
          (sqir_mult_input_F bits x 0) (sqir_mult_control_idx bits k)
          = ((a * x) % N).testBit k := by
  have h_state := sqir_modmult_inplace_candidate_state_eq bits N a ainv x
    hbits hN_pos hN hN2 h_ainv_le hx h_inv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_state]; exact sqir_mult_input_target_decode bits ((a * x) % N) 0 (Nat.two_pow_pos bits)
  · rw [h_state]; exact sqir_mult_input_read_decode bits ((a * x) % N) 0
  · rw [h_state]; exact sqir_mult_input_flag_0_false bits ((a * x) % N) 0
  · rw [h_state]; exact sqir_mult_input_flag_1_false bits ((a * x) % N) 0
  · rw [h_state]; exact sqir_mult_input_top_carry_false bits ((a * x) % N) 0 hbits
  · intro k hk
    rw [h_state]
    exact sqir_mult_input_control_bit bits ((a * x) % N) 0 k hk

theorem sqir_mult_input_F_shifted_below_bits
    (bits x acc q : Nat) (hq : q < bits) :
    sqir_mult_input_F_shifted bits x acc q = false := by
  unfold sqir_mult_input_F_shifted; rw [if_pos hq]

theorem sqir_mult_input_F_shifted_above_bits
    (bits x acc q : Nat) (hq : bits ≤ q) :
    sqir_mult_input_F_shifted bits x acc q
      = sqir_mult_input_F bits x acc (q - bits) := by
  unfold sqir_mult_input_F_shifted; rw [if_neg (Nat.not_lt.mpr hq)]

theorem sqir_mult_input_F_shifted_at_shifted_control_bit
    (bits x acc k : Nat) (hk : k < bits) :
    sqir_mult_input_F_shifted bits x acc (bits + sqir_mult_control_idx bits k)
      = x.testBit k := by
  rw [sqir_mult_input_F_shifted_above_bits bits x acc _ (by omega)]
  rw [show bits + sqir_mult_control_idx bits k - bits = sqir_mult_control_idx bits k from by omega]
  exact sqir_mult_input_control_bit bits x acc k hk

theorem Gate.shift_seq (off : Nat) (g h : Gate) :
    Gate.shift off (Gate.seq g h)
      = Gate.seq (Gate.shift off g) (Gate.shift off h) := rfl

/-- **At positions below `off`, a shifted gate acts as identity.** -/
theorem Gate.applyNat_shift_at_lo
    (off : Nat) (g : Gate) (f : Nat → Bool) (q : Nat) (hq : q < off) :
    Gate.applyNat (Gate.shift off g) f q = f q := by
  induction g generalizing f with
  | I => rfl
  | X p =>
    show update f (off + p) (! f (off + p)) q = f q
    rw [update_neq _ _ _ _ (by omega : q ≠ off + p)]
  | CX a b =>
    show update f (off + b) (xor (f (off + b)) (f (off + a))) q = f q
    rw [update_neq _ _ _ _ (by omega : q ≠ off + b)]
  | CCX a b c =>
    show update f (off + c) (xor (f (off + c)) (f (off + a) && f (off + b))) q = f q
    rw [update_neq _ _ _ _ (by omega : q ≠ off + c)]
  | seq g₁ g₂ ih₁ ih₂ =>
    show Gate.applyNat (Gate.shift off g₂) (Gate.applyNat (Gate.shift off g₁) f) q = f q
    rw [ih₂]
    exact ih₁ f

/-- **At positions ≥ `off`, a shifted gate acts as the original gate
on the function `r ↦ f (off + r)`.** -/
theorem Gate.applyNat_shift_at_hi
    (off : Nat) (g : Gate) (f : Nat → Bool) (q : Nat) (hq : off ≤ q) :
    Gate.applyNat (Gate.shift off g) f q
      = Gate.applyNat g (fun r => f (off + r)) (q - off) := by
  induction g generalizing f q with
  | I =>
    show f q = f (off + (q - off))
    congr 1; omega
  | X p =>
    show update f (off + p) (! f (off + p)) q
        = update (fun r => f (off + r)) p (! (fun r => f (off + r)) p) (q - off)
    by_cases h_eq : q = off + p
    · subst h_eq
      rw [update_eq, show off + p - off = p from by omega, update_eq]
    · rw [update_neq _ _ _ _ h_eq]
      have h_ne : q - off ≠ p := fun h => h_eq (by omega)
      rw [update_neq _ _ _ _ h_ne]
      show f q = f (off + (q - off))
      congr 1; omega
  | CX a b =>
    show update f (off + b) (xor (f (off + b)) (f (off + a))) q
        = update (fun r => f (off + r)) b
            (xor ((fun r => f (off + r)) b) ((fun r => f (off + r)) a)) (q - off)
    by_cases h_eq : q = off + b
    · subst h_eq
      rw [update_eq, show off + b - off = b from by omega, update_eq]
    · rw [update_neq _ _ _ _ h_eq]
      have h_ne : q - off ≠ b := fun h => h_eq (by omega)
      rw [update_neq _ _ _ _ h_ne]
      show f q = f (off + (q - off))
      congr 1; omega
  | CCX a b c =>
    show update f (off + c) (xor (f (off + c)) (f (off + a) && f (off + b))) q
        = update (fun r => f (off + r)) c
            (xor ((fun r => f (off + r)) c)
              ((fun r => f (off + r)) a && (fun r => f (off + r)) b))
            (q - off)
    by_cases h_eq : q = off + c
    · subst h_eq
      rw [update_eq, show off + c - off = c from by omega, update_eq]
    · rw [update_neq _ _ _ _ h_eq]
      have h_ne : q - off ≠ c := fun h => h_eq (by omega)
      rw [update_neq _ _ _ _ h_ne]
      show f q = f (off + (q - off))
      congr 1; omega
  | seq g₁ g₂ ih₁ ih₂ =>
    show Gate.applyNat (Gate.shift off g₂) (Gate.applyNat (Gate.shift off g₁) f) q
        = Gate.applyNat g₂ (Gate.applyNat g₁ (fun r => f (off + r))) (q - off)
    rw [ih₂ (Gate.applyNat (Gate.shift off g₁) f) q hq]
    congr 1
    funext r
    by_cases hr : off ≤ off + r
    · rw [ih₁ f (off + r) hr]
      congr 1; omega
    · exfalso; omega

/-- **Gate.shift is WellTyped at the larger dimension.** -/
theorem Gate.shift_wellTyped
    {off dim : Nat} {g : Gate} (h : Gate.WellTyped dim g) :
    Gate.WellTyped (off + dim) (Gate.shift off g) := by
  induction g with
  | I =>
    show 0 < off + dim
    exact Nat.lt_of_lt_of_le h (Nat.le_add_left dim off)
  | X q =>
    show off + q < off + dim
    have : q < dim := h
    omega
  | CX a b =>
    obtain ⟨ha, hb, hab⟩ := h
    show off + a < off + dim ∧ off + b < off + dim ∧ off + a ≠ off + b
    refine ⟨by omega, by omega, ?_⟩
    intro heq; exact hab (by omega)
  | CCX a b c =>
    obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := h
    show off + a < off + dim ∧ off + b < off + dim ∧ off + c < off + dim
        ∧ off + a ≠ off + b ∧ off + a ≠ off + c ∧ off + b ≠ off + c
    refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
    · intro heq; exact hab (by omega)
    · intro heq; exact hac (by omega)
    · intro heq; exact hbc (by omega)
  | seq g₁ g₂ ih₁ ih₂ =>
    refine ⟨ih₁ h.1, ih₂ h.2⟩

/-- Disjointness of swap ranges (used in `reverse_register_swap` lemmas). -/
theorem sqir_encode_to_mult_adapter_disjoint (bits : Nat) :
    0 + bits ≤ bits + sqir_mult_control_idx bits 0
      ∨ bits + sqir_mult_control_idx bits 0 + bits ≤ 0 := by
  left; unfold sqir_mult_control_idx; omega

theorem sqir_encode_to_mult_adapter_wellTyped
    (bits : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (sqir_total_dim bits) (sqir_encode_to_mult_adapter bits) := by
  unfold sqir_encode_to_mult_adapter sqir_total_dim
  apply reverse_register_swap_wellTyped
  · unfold sqir_modmult_rev_anc; omega
  · unfold sqir_modmult_rev_anc; omega
  · unfold sqir_mult_control_idx sqir_modmult_rev_anc; omega
  · exact sqir_encode_to_mult_adapter_disjoint bits

/-- Helper: workspace value of `cuccaro_input_F 2 false 0 0` is always false. -/
theorem cuccaro_input_F_zero_at_workspace
    (q : Nat) (hq : q < 2 + 2 * (0 : Nat) + 1 ∨ True) :
    cuccaro_input_F 2 false 0 0 q = false := by
  unfold cuccaro_input_F
  by_cases h_lt : q < 2
  · rw [if_pos h_lt]
  · rw [if_neg h_lt]
    set i := q - 2
    by_cases hi_0 : i = 0
    · rw [if_pos hi_0]
    · rw [if_neg hi_0]
      by_cases hi_odd : i % 2 = 1
      · rw [if_pos hi_odd]; exact Nat.zero_testBit _
      · rw [if_neg hi_odd]; exact Nat.zero_testBit _

/-- **Adapter correctness: `encodeDataZeroAnc → sqir_mult_input_F_shifted`.** -/
theorem sqir_encode_to_mult_adapter_correct
    (bits x : Nat) (hbits : 1 ≤ bits) (hx : x < 2^bits) :
    Gate.applyNat (sqir_encode_to_mult_adapter bits)
        (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
      = sqir_mult_input_F_shifted bits x 0 := by
  funext q
  unfold sqir_encode_to_mult_adapter
  set offB := bits + sqir_mult_control_idx bits 0 with h_offB_def
  have h_offB_val : offB = 2 + 2 * bits + 1 + bits := by
    rw [h_offB_def]; unfold sqir_mult_control_idx; omega
  have h_disjoint : 0 + bits ≤ offB ∨ offB + bits ≤ 0 :=
    sqir_encode_to_mult_adapter_disjoint bits
  have h_anc_pos : 0 < sqir_modmult_rev_anc bits := by unfold sqir_modmult_rev_anc; omega
  by_cases hq_lo : q < bits
  · -- Encoded data position: at_A with j = q.
    rw [sqir_mult_input_F_shifted_below_bits bits x 0 q hq_lo]
    conv_lhs => rw [show q = 0 + q from by omega]
    unfold reverse_register_swap
    rw [reverse_register_swap_aux_at_A bits 0 offB bits _ q hq_lo h_disjoint (le_refl _)]
    have h_anc_idx_lt : offB + (bits - 1 - q) - bits < sqir_modmult_rev_anc bits := by
      rw [h_offB_val]; unfold sqir_modmult_rev_anc; omega
    have h_anc_eq : offB + (bits - 1 - q) = bits + (offB + (bits - 1 - q) - bits) := by
      rw [h_offB_val]; omega
    rw [h_anc_eq, encodeDataZeroAnc_anc hx h_anc_idx_lt]
  · push_neg at hq_lo
    by_cases hq_in_mult : offB ≤ q ∧ q < offB + bits
    · obtain ⟨h_q_ge, h_q_lt⟩ := hq_in_mult
      have h_j'_lt : bits - 1 - (q - offB) < bits := by omega
      -- RHS first: convert to shifted_control_bit form.
      have h_q_minus_bits : q - bits = sqir_mult_control_idx bits (q - offB) := by
        rw [h_offB_val] at h_q_ge h_q_lt; unfold sqir_mult_control_idx; omega
      rw [sqir_mult_input_F_shifted_above_bits bits x 0 q (by omega)]
      rw [h_q_minus_bits]
      rw [sqir_mult_input_control_bit bits x 0 (q - offB) (by omega)]
      -- LHS:
      have h_q_eq : q = offB + (bits - 1 - (bits - 1 - (q - offB))) := by omega
      conv_lhs => rw [h_q_eq]
      unfold reverse_register_swap
      rw [reverse_register_swap_aux_at_B bits 0 offB bits _ (bits - 1 - (q - offB))
            h_j'_lt h_disjoint (le_refl _)]
      simp only [Nat.zero_add]
      rw [encodeDataZeroAnc_data hx h_j'_lt]
      unfold FormalRV.Framework.nat_to_funbool
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have h_exp_eq : bits - 1 - (bits - 1 - (q - offB)) = q - offB := by omega
      rw [h_exp_eq]
    · -- Other positions: identity.
      have h_not_in_swap_range : ¬ (offB ≤ q ∧ q < offB + bits) := hq_in_mult
      have h_lhs_id : Gate.applyNat (reverse_register_swap_aux bits 0 offB bits)
                          (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x) q
                        = encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x q := by
        apply reverse_register_swap_aux_at_other bits 0 offB bits _ q h_disjoint (le_refl _)
        intro i hi
        refine ⟨by omega, ?_⟩
        intro heq
        exact h_not_in_swap_range ⟨by omega, by omega⟩
      unfold reverse_register_swap
      rw [h_lhs_id]
      rw [sqir_mult_input_F_shifted_above_bits bits x 0 q hq_lo]
      by_cases hq_below_offB : q < offB
      · -- q ∈ [bits, offB).  Both false.
        have h_anc_idx_lt : q - bits < sqir_modmult_rev_anc bits := by
          rw [h_offB_val] at hq_below_offB; unfold sqir_modmult_rev_anc; omega
        have h_eq : q = bits + (q - bits) := by omega
        rw [h_eq, encodeDataZeroAnc_anc hx h_anc_idx_lt]
        -- RHS: q - bits ∈ [0, 2*bits + 3).  In workspace.
        unfold sqir_mult_input_F
        rw [if_pos (by rw [h_offB_val] at hq_below_offB; omega
                      : bits + (q - bits) - bits < 2 + 2 * bits + 1)]
        rw [show bits + (q - bits) - bits = q - bits from by omega]
        exact (cuccaro_input_F_zero_at_workspace (q - bits) (Or.inr trivial)).symm
      · push_neg at hq_below_offB
        -- q ≥ offB + bits.  Encoded false, RHS false.
        have h_q_minus_eq : bits + (q - bits) - bits = q - bits := by omega
        have h_RHS_false : sqir_mult_input_F bits x 0 (q - bits) = false := by
          unfold sqir_mult_input_F
          rw [if_neg (by rw [h_offB_val] at hq_below_offB; omega
                        : ¬ q - bits < 2 + 2 * bits + 1)]
          rw [if_neg (by rw [h_offB_val] at hq_below_offB; omega
                        : ¬ q - bits < 2 + 2 * bits + 1 + bits)]
        rw [h_RHS_false]
        rw [show q = bits + (q - bits) from by omega]
        by_cases h_q_minus_lt_anc : q - bits < sqir_modmult_rev_anc bits
        · exact encodeDataZeroAnc_anc hx h_q_minus_lt_anc
        · push_neg at h_q_minus_lt_anc
          exact encodeDataZeroAnc_oob h_anc_pos
                (by omega : bits + sqir_modmult_rev_anc bits ≤ bits + (q - bits))

/-! ## Tick 78 — Adapter involution + reverse direction. -/

/-- **General reverse-register-swap involution.**  Applying
`reverse_register_swap n offsetA offsetB` twice yields identity, given
disjoint ranges. -/
theorem reverse_register_swap_involution_general
    (n offsetA offsetB : Nat)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA)
    (f : Nat → Bool) :
    Gate.applyNat (reverse_register_swap n offsetA offsetB)
      (Gate.applyNat (reverse_register_swap n offsetA offsetB) f)
    = f := by
  unfold reverse_register_swap
  funext q
  by_cases h_in_A : offsetA ≤ q ∧ q < offsetA + n
  · obtain ⟨h_q_lo, h_q_hi⟩ := h_in_A
    set j := q - offsetA with hj_def
    have hj_lt : j < n := by omega
    have h_q_eq : q = offsetA + j := by omega
    conv_lhs => rw [h_q_eq]
    rw [reverse_register_swap_aux_at_A n offsetA offsetB n _ j hj_lt h_disjoint (le_refl _)]
    rw [reverse_register_swap_aux_at_B n offsetA offsetB n _ j hj_lt h_disjoint (le_refl _)]
    congr 1; omega
  · by_cases h_in_B : offsetB ≤ q ∧ q < offsetB + n
    · obtain ⟨h_q_lo, h_q_hi⟩ := h_in_B
      set j := n - 1 - (q - offsetB) with hj_def
      have hj_lt : j < n := by omega
      have h_q_eq : q = offsetB + (n - 1 - j) := by omega
      conv_lhs => rw [h_q_eq]
      rw [reverse_register_swap_aux_at_B n offsetA offsetB n _ j hj_lt h_disjoint (le_refl _)]
      rw [reverse_register_swap_aux_at_A n offsetA offsetB n _ j hj_lt h_disjoint (le_refl _)]
      congr 1; omega
    · -- q outside both ranges.
      push_neg at h_in_A h_in_B
      have h_outside : ∀ i, i < n →
          q ≠ offsetA + i ∧ q ≠ offsetB + (n - 1 - i) := by
        intro i hi
        refine ⟨?_, ?_⟩
        · by_contra heq; exact absurd (Nat.le_refl q) (by omega)
        · intro heq
          have h_q_ge_B : offsetB ≤ q := by omega
          have h_q_lt_B_n : q < offsetB + n := by omega
          exact absurd (h_in_B h_q_ge_B) (by omega)
      rw [reverse_register_swap_aux_at_other n offsetA offsetB n _ q h_disjoint (le_refl _) h_outside]
      rw [reverse_register_swap_aux_at_other n offsetA offsetB n _ q h_disjoint (le_refl _) h_outside]

/-- **Adapter is self-inverse.** -/
theorem sqir_encode_to_mult_adapter_involution
    (bits : Nat) (f : Nat → Bool) :
    Gate.applyNat (sqir_encode_to_mult_adapter bits)
      (Gate.applyNat (sqir_encode_to_mult_adapter bits) f) = f := by
  unfold sqir_encode_to_mult_adapter
  exact reverse_register_swap_involution_general bits 0 _
    (sqir_encode_to_mult_adapter_disjoint bits) f

/-- **Adapter reverse direction: `sqir_mult_input_F_shifted → encodeDataZeroAnc`.** -/
theorem sqir_encode_to_mult_adapter_reverse
    (bits y : Nat) (hbits : 1 ≤ bits) (hy : y < 2^bits) :
    Gate.applyNat (sqir_encode_to_mult_adapter bits)
        (sqir_mult_input_F_shifted bits y 0)
      = encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) y := by
  have h_forward := sqir_encode_to_mult_adapter_correct bits y hbits hy
  -- applyNat adapter (encoded y) = shifted y.
  -- So applyNat adapter (shifted y) = applyNat adapter (applyNat adapter (encoded y)) = encoded y.
  have h_invol := sqir_encode_to_mult_adapter_involution bits
                    (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) y)
  rw [h_forward] at h_invol
  exact h_invol

/-- **Shifted in-place multiplier correctness.** -/
theorem sqir_modmult_inplace_shifted_correct
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (sqir_modmult_inplace_shifted bits N a ainv)
        (sqir_mult_input_F_shifted bits x 0)
      = sqir_mult_input_F_shifted bits ((a * x) % N) 0 := by
  unfold sqir_modmult_inplace_shifted
  funext q
  by_cases hq_lo : q < bits
  · rw [Gate.applyNat_shift_at_lo bits _ _ q hq_lo]
    rw [sqir_mult_input_F_shifted_below_bits bits x 0 q hq_lo]
    rw [sqir_mult_input_F_shifted_below_bits bits ((a * x) % N) 0 q hq_lo]
  · push_neg at hq_lo
    rw [Gate.applyNat_shift_at_hi bits _ _ q hq_lo]
    rw [sqir_mult_input_F_shifted_above_bits bits ((a * x) % N) 0 q hq_lo]
    have h_inner_eq : (fun r => sqir_mult_input_F_shifted bits x 0 (bits + r))
                    = sqir_mult_input_F bits x 0 := by
      funext r
      rw [sqir_mult_input_F_shifted_above_bits bits x 0 (bits + r) (by omega)]
      congr 1; omega
    rw [h_inner_eq]
    rw [sqir_modmult_inplace_candidate_state_eq bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv]

theorem sqir_modmult_inplace_shifted_wellTyped
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    Gate.WellTyped (sqir_total_dim bits) (sqir_modmult_inplace_shifted bits N a ainv) := by
  unfold sqir_modmult_inplace_shifted sqir_total_dim
  apply Gate.shift_wellTyped
  -- Need: WellTyped (sqir_modmult_rev_anc bits) (sqir_modmult_inplace_candidate bits N a ainv).
  -- The in-place candidate = seq const_gate (seq swap const_gate).
  unfold sqir_modmult_inplace_candidate
  refine ⟨?_, ?_, ?_⟩
  · exact sqir_modmult_prefix_gate_wellTyped bits N a bits hbits hN_pos hN hN2 (le_refl _)
  · exact sqir_swap_acc_mult_wellTyped bits hbits
  · exact sqir_modmult_prefix_gate_wellTyped bits N ((N - ainv) % N) bits
            hbits hN_pos hN hN2 (le_refl _)

/-- **MCP-layout gate apply theorem.**

The composed gate maps `encodeDataZeroAnc bits anc x` to
`encodeDataZeroAnc bits anc ((a*x) % N)`. -/
theorem sqir_modmult_MCP_gate_apply_encode
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (sqir_modmult_MCP_gate bits N a ainv)
        (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
      = encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) ((a * x) % N) := by
  unfold sqir_modmult_MCP_gate
  simp only [Gate.applyNat_seq]
  have hx_lt_pow : x < 2^bits := Nat.lt_of_lt_of_le hx hN
  rw [sqir_encode_to_mult_adapter_correct bits x hbits hx_lt_pow]
  rw [sqir_modmult_inplace_shifted_correct bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv]
  have h_ax_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have h_ax_lt_pow : (a * x) % N < 2^bits := Nat.lt_of_lt_of_le h_ax_lt_N hN
  exact sqir_encode_to_mult_adapter_reverse bits ((a * x) % N) hbits h_ax_lt_pow

/-- **MCP-layout gate WellTyped.** -/
theorem sqir_modmult_MCP_gate_wellTyped
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    Gate.WellTyped (sqir_total_dim bits) (sqir_modmult_MCP_gate bits N a ainv) := by
  unfold sqir_modmult_MCP_gate
  refine ⟨?_, ?_, ?_⟩
  · exact sqir_encode_to_mult_adapter_wellTyped bits hbits
  · exact sqir_modmult_inplace_shifted_wellTyped bits N a ainv hbits hN_pos hN hN2
  · exact sqir_encode_to_mult_adapter_wellTyped bits hbits

/-! ## Tick 78 — Task 7: MultiplyCircuitProperty bridge. -/

/-- **HEADLINE: MCP-layout gate satisfies `MultiplyCircuitProperty`.** -/
theorem sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    FormalRV.SQIRPort.MultiplyCircuitProperty a N bits (sqir_modmult_rev_anc bits)
      (Gate.toUCom (sqir_total_dim bits) (sqir_modmult_MCP_gate bits N a ainv)) := by
  unfold sqir_total_dim
  apply toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc
    (sqir_modmult_MCP_gate_wellTyped bits N a ainv hbits hN_pos hN hN2)
    hN
  intro x hx
  exact sqir_modmult_MCP_gate_apply_encode bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv

/-! ## Tick 79 — Verified ModMulImpl family.

### Layout and sizing decision (documented as Route B)

The original SQIR axiom site (`Shor.lean:4570`) declares:
  axiom f_modmult_circuit : (a ainv N n : Nat) → Nat → BaseUCom (n + modmult_rev_anc n)
where `modmult_rev_anc n = 2 * n + 1`, giving total dim `3 * n + 1`.

Our verified MCP gate has total dim `(n + 1) + sqir_modmult_rev_anc (n + 1) = 4 * n + 15`
because:
1. `BasicSetting` only guarantees `2^n ≤ 2 * N`, NOT `2 * N ≤ 2^n`.  The
   `BasicSetting_twoN_le_pow_succ` lemma gives `2 * N ≤ 2 ^ (n + 1)`, so
   we instantiate at `bits = n + 1`.
2. The SQIR-faithful workspace requires `3 * (n + 1) + 11 = 3 * n + 14`
   ancilla bits, which exceeds the placeholder's `2 * (n+1) + 1`.

**Route B (verified parallel family)**: we land a new family
`f_modmult_circuit_verified` at dimension `(n + 1) + sqir_modmult_rev_anc (n + 1)`,
prove `ModMulImpl` + `uc_well_typed` at that dimension, and document the
exact dimension mismatch with the original placeholder.  The original
axiom names remain untouched; downstream theorems that take
`ModMulImpl ... f` as a hypothesis can be instantiated with our family
at dimension `n + 1` (with appropriate dimension/ancilla bookkeeping). -/

/-- **Per-iterate modular inverse arithmetic.**

If `(a * ainv) % N = 1` and `N ≥ 2`, then for every `i`,
`((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1`. -/
theorem pow_iter_inverse_mod
    (a ainv N i : Nat) (hN_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    ((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1 := by
  rw [← Nat.mul_mod]
  rw [← Nat.mul_pow]
  rw [Nat.pow_mod]
  rw [h_inv]
  rw [one_pow]
  exact Nat.mod_eq_of_lt hN_ge_2

/-- **MCP up-to-mod lifting.**  If a unitary satisfies
`MultiplyCircuitProperty (c % N)`, then it also satisfies
`MultiplyCircuitProperty c` (since `(c * x) % N = ((c % N) * x) % N`). -/
theorem MultiplyCircuitProperty_of_mod
    {c N n anc : Nat} {U : FormalRV.Framework.BaseUCom (n + anc)}
    (hN_pos : 0 < N) (h_modN : FormalRV.SQIRPort.MultiplyCircuitProperty (c % N) N n anc U) :
    FormalRV.SQIRPort.MultiplyCircuitProperty c N n anc U := by
  unfold FormalRV.SQIRPort.MultiplyCircuitProperty at h_modN ⊢
  intro x hx
  have h_eq : c * x % N = c % N * x % N := by
    conv_lhs => rw [Nat.mul_mod]
    conv_rhs => rw [Nat.mul_mod]
    rw [Nat.mod_mod]
  rw [h_eq]
  exact h_modN x hx

/-- **Per-iterate `MultiplyCircuitProperty` for the verified family.** -/
theorem f_modmult_circuit_verified_per_iterate
    (a ainv N n i : Nat) (hN_ge_2 : 2 ≤ N) (hN : N ≤ 2^(n + 1)) (hN2 : 2 * N ≤ 2^(n + 1))
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.MultiplyCircuitProperty
      (a^(2^i)) N (n + 1) (sqir_modmult_rev_anc (n + 1))
      (f_modmult_circuit_verified a ainv N n i) := by
  unfold f_modmult_circuit_verified
  have hN_pos : 0 < N := by omega
  have h_ainv_lt_N : (ainv^(2^i)) % N < N := Nat.mod_lt _ hN_pos
  have h_ainv_le : (ainv^(2^i)) % N ≤ N := Nat.le_of_lt h_ainv_lt_N
  have h_inv_i : ((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1 :=
    pow_iter_inverse_mod a ainv N i hN_ge_2 h_inv
  -- Reframe via mod-up-to lift.
  apply MultiplyCircuitProperty_of_mod hN_pos
  -- Goal: MultiplyCircuitProperty ((a^(2^i)) % N) N (n+1) anc (Gate.toUCom ... MCP_gate)
  show FormalRV.SQIRPort.MultiplyCircuitProperty
    ((a^(2^i)) % N) N (n + 1) (sqir_modmult_rev_anc (n + 1))
    (Gate.toUCom ((n + 1) + sqir_modmult_rev_anc (n + 1))
      (sqir_modmult_MCP_gate (n + 1) N ((a^(2^i)) % N) ((ainv^(2^i)) % N)))
  have h_mcp := sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty
    (n + 1) N ((a^(2^i)) % N) ((ainv^(2^i)) % N)
    (by omega : 1 ≤ n + 1) hN_pos hN hN2 h_ainv_le h_inv_i
  unfold sqir_total_dim at h_mcp
  exact h_mcp

/-- **`ModMulImpl` for the verified family.** -/
theorem f_modmult_circuit_verified_MMI
    (a ainv N n : Nat) (hN_ge_2 : 2 ≤ N) (hN : N ≤ 2^(n + 1)) (hN2 : 2 * N ≤ 2^(n + 1))
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.ModMulImpl a N (n + 1) (sqir_modmult_rev_anc (n + 1))
      (f_modmult_circuit_verified a ainv N n) := by
  intro i
  exact f_modmult_circuit_verified_per_iterate a ainv N n i hN_ge_2 hN hN2 h_inv

/-- **`uc_well_typed` for every iterate of the verified family.** -/
theorem f_modmult_circuit_verified_uc_well_typed
    (a ainv N n : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^(n + 1)) (hN2 : 2 * N ≤ 2^(n + 1)) :
    ∀ i, FormalRV.SQIRPort.uc_well_typed (f_modmult_circuit_verified a ainv N n i) := by
  intro i
  unfold f_modmult_circuit_verified
  apply uc_well_typed_toUCom_of_Gate_WellTyped
  have h_wt := sqir_modmult_MCP_gate_wellTyped (n + 1) N
    ((a^(2^i)) % N) ((ainv^(2^i)) % N) (by omega : 1 ≤ n + 1) hN_pos hN hN2
  unfold sqir_total_dim at h_wt
  exact h_wt

/-! ### BasicSetting bridge for the verified family. -/

/-- **`ModMulImpl` from `BasicSetting`** (n+1 dimension). -/
theorem f_modmult_circuit_verified_MMI_from_BasicSetting
    (a r N m n ainv : Nat) (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.ModMulImpl a N (n + 1) (sqir_modmult_rev_anc (n + 1))
      (f_modmult_circuit_verified a ainv N n) := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have h_N_ge_2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h_lt | h_ge
    · exfalso
      have hN_eq : N = 1 := by omega
      rw [hN_eq, Nat.mod_one] at h_inv
      exact absurd h_inv (by decide)
    · exact h_ge
  have hN : N ≤ 2 ^ (n + 1) := by
    have h1 : N ≤ 2 * N := by omega
    have h2 : 2 * N ≤ 2 ^ (n + 1) := hN2
    omega
  exact f_modmult_circuit_verified_MMI a ainv N n h_N_ge_2 hN hN2 h_inv

/-- **`uc_well_typed` from `BasicSetting`**. -/
theorem f_modmult_circuit_verified_uc_well_typed_from_BasicSetting
    (a r N m n ainv : Nat) (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n) :
    ∀ i, FormalRV.SQIRPort.uc_well_typed (f_modmult_circuit_verified a ainv N n i) := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have hN : N ≤ 2 ^ (n + 1) := by
    have h1 : N ≤ 2 * N := by omega
    have h2 : 2 * N ≤ 2 ^ (n + 1) := hN2
    omega
  exact f_modmult_circuit_verified_uc_well_typed a ainv N n hN_pos hN hN2

/-- **MMI for the bits-parameterized family.** -/
theorem f_modmult_circuit_verified_bits_MMI
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_ge_2 : 2 ≤ N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.ModMulImpl a N bits (sqir_modmult_rev_anc bits)
      (f_modmult_circuit_verified_bits a ainv N bits) := by
  intro i
  unfold f_modmult_circuit_verified_bits
  have hN_pos : 0 < N := by omega
  have h_ainv_lt_N : (ainv^(2^i)) % N < N := Nat.mod_lt _ hN_pos
  have h_ainv_le : (ainv^(2^i)) % N ≤ N := Nat.le_of_lt h_ainv_lt_N
  have h_inv_i : ((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1 :=
    pow_iter_inverse_mod a ainv N i hN_ge_2 h_inv
  apply MultiplyCircuitProperty_of_mod hN_pos
  have h_mcp := sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty
    bits N ((a^(2^i)) % N) ((ainv^(2^i)) % N) hbits hN_pos hN hN2 h_ainv_le h_inv_i
  unfold sqir_total_dim at h_mcp
  exact h_mcp

/-- **uc_well_typed for the bits-parameterized family.** -/
theorem f_modmult_circuit_verified_bits_uc_well_typed
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    ∀ i, FormalRV.SQIRPort.uc_well_typed (f_modmult_circuit_verified_bits a ainv N bits i) := by
  intro i
  unfold f_modmult_circuit_verified_bits
  apply uc_well_typed_toUCom_of_Gate_WellTyped
  have h_wt := sqir_modmult_MCP_gate_wellTyped bits N
    ((a^(2^i)) % N) ((ainv^(2^i)) % N) hbits hN_pos hN hN2
  unfold sqir_total_dim at h_wt
  exact h_wt

/-- **Verified Shor probability bound — bits-parameterized.**

If the user provides `BasicSetting a r N m bits` (which is generally
INCOMPATIBLE with our sizing requirement `2 * N ≤ 2^bits` — see the
documentation block above), the Shor success-probability bound holds
for the verified family at dimension `bits + sqir_modmult_rev_anc bits`.

In practice, both hypotheses can be simultaneously satisfied ONLY when
`2 * N = 2^bits` (i.e., `N` is a power of 2).  For general `N`, this
theorem is vacuous — see Status D in PROGRESS.md / Tick 80 commit. -/
theorem Shor_correct_with_sqir_verified_modmult_bits
    (a r N m bits ainv : Nat) (hbits : 1 ≤ bits)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m bits)
    (hN2 : 2 * N ≤ 2^bits)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
      (sqir_modmult_rev_anc bits)
      (f_modmult_circuit_verified_bits a ainv N bits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have h_basic_destruct := h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic_destruct
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _h_ord, _, hN_lt, _⟩ := h_basic_destruct
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have h_N_ge_2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h_lt | h_ge
    · exfalso
      have hN_eq : N = 1 := by omega
      rw [hN_eq, Nat.mod_one] at h_inv
      exact absurd h_inv (by decide)
    · exact h_ge
  have hN : N ≤ 2 ^ bits := Nat.le_of_lt hN_lt
  exact FormalRV.SQIRPort.Shor_correct_var a r N m bits
    (sqir_modmult_rev_anc bits) (f_modmult_circuit_verified_bits a ainv N bits)
    h_basic
    (f_modmult_circuit_verified_bits_MMI a ainv N bits hbits h_N_ge_2 hN hN2 h_inv)
    (fun i _ => f_modmult_circuit_verified_bits_uc_well_typed a ainv N bits
                  hbits hN_pos hN hN2 i)

end FormalRV.BQAlgo
