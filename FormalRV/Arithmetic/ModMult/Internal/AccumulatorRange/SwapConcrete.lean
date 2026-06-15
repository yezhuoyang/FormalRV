import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.ModMult.Internal.Encoding
import FormalRV.Arithmetic.ModMult.Internal.Spec
import FormalRV.Arithmetic.ModMult.Internal.QStart
import FormalRV.Arithmetic.ModMult.Internal.Family
import FormalRV.Arithmetic.ModMult.Internal.PrefixInvariant
import FormalRV.Arithmetic.ModMult.Internal.AccumulatorRange.SwapQStart

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
/-! ## Per-position behavior of `modmult_swap_acc_mult_aux`. -/

/-- **At a multiplier bit `i ≥ k`, swap output = input.** -/
theorem modmult_swap_acc_mult_aux_at_mult_out_range
    (bits k i : Nat) (hk : k ≤ bits) (hi_ge : k ≤ i) (hi_bits : i < bits) (f : Nat → Bool) :
    Gate.applyNat (modmult_swap_acc_mult_aux bits k) f (mult_control_idx bits i)
      = f (mult_control_idx bits i) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [modmult_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (modmult_target_idx_ne_mult_control_idx bits n n hn_lt)]
    have h_i_ne_n : i ≠ n := by omega
    have h_ne_mult_n : mult_control_idx bits i ≠ mult_control_idx bits n := by
      intro heq
      exact h_i_ne_n (mult_control_idx_injective bits i n heq)
    have h_ne_target_n : mult_control_idx bits i ≠ modmult_target_idx n :=
      (modmult_target_idx_ne_mult_control_idx bits n i hn_lt).symm
    rw [update_neq _ _ _ _ h_ne_mult_n]
    rw [update_neq _ _ _ _ h_ne_target_n]
    exact ih (by omega) (by omega)

/-- **At an accumulator bit `i ≥ k`, swap output = input.** -/
theorem modmult_swap_acc_mult_aux_at_target_out_range
    (bits k i : Nat) (hk : k ≤ bits) (hi_ge : k ≤ i) (hi_bits : i < bits) (f : Nat → Bool) :
    Gate.applyNat (modmult_swap_acc_mult_aux bits k) f (modmult_target_idx i)
      = f (modmult_target_idx i) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [modmult_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (modmult_target_idx_ne_mult_control_idx bits n n hn_lt)]
    have h_i_ne_n : i ≠ n := by omega
    have h_ne_mult_n : modmult_target_idx i ≠ mult_control_idx bits n :=
      modmult_target_idx_ne_mult_control_idx bits i n hi_bits
    have h_ne_target_n : modmult_target_idx i ≠ modmult_target_idx n := by
      unfold modmult_target_idx; omega
    rw [update_neq _ _ _ _ h_ne_mult_n]
    rw [update_neq _ _ _ _ h_ne_target_n]
    exact ih (by omega) (by omega)

/-- **At an accumulator bit `i < k`, swap output = input at the matched
multiplier position.** -/
theorem modmult_swap_acc_mult_aux_at_target_in_range
    (bits k i : Nat) (hk : k ≤ bits) (hi_k : i < k) (f : Nat → Bool) :
    Gate.applyNat (modmult_swap_acc_mult_aux bits k) f (modmult_target_idx i)
      = f (mult_control_idx bits i) := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hn_lt : n < bits := by omega
    have hi_bits : i < bits := by omega
    rw [modmult_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (modmult_target_idx_ne_mult_control_idx bits n n hn_lt)]
    by_cases hi_eq : i = n
    · subst hi_eq
      rw [update_neq _ _ _ _ (modmult_target_idx_ne_mult_control_idx bits i i hi_bits)]
      rw [update_eq]
      exact modmult_swap_acc_mult_aux_at_mult_out_range bits i i (by omega) (le_refl _) hi_bits f
    · have h_ne_mult_n : modmult_target_idx i ≠ mult_control_idx bits n :=
        modmult_target_idx_ne_mult_control_idx bits i n hi_bits
      have h_ne_target_n : modmult_target_idx i ≠ modmult_target_idx n := by
        unfold modmult_target_idx; omega
      rw [update_neq _ _ _ _ h_ne_mult_n]
      rw [update_neq _ _ _ _ h_ne_target_n]
      exact ih (by omega) (by omega)

/-- **At a multiplier bit `i < k`, swap output = input at matched target.** -/
theorem modmult_swap_acc_mult_aux_at_mult_in_range
    (bits k i : Nat) (hk : k ≤ bits) (hi_k : i < k) (f : Nat → Bool) :
    Gate.applyNat (modmult_swap_acc_mult_aux bits k) f (mult_control_idx bits i)
      = f (modmult_target_idx i) := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hn_lt : n < bits := by omega
    have hi_bits : i < bits := by omega
    rw [modmult_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (modmult_target_idx_ne_mult_control_idx bits n n hn_lt)]
    by_cases hi_eq : i = n
    · subst hi_eq
      rw [update_eq]
      exact modmult_swap_acc_mult_aux_at_target_out_range bits i i (by omega) (le_refl _) hi_bits f
    · have h_ne_mult_n : mult_control_idx bits i ≠ mult_control_idx bits n := by
        intro heq
        exact hi_eq (mult_control_idx_injective bits i n heq)
      have h_ne_target_n : mult_control_idx bits i ≠ modmult_target_idx n :=
        (modmult_target_idx_ne_mult_control_idx bits n i hn_lt).symm
      rw [update_neq _ _ _ _ h_ne_mult_n]
      rw [update_neq _ _ _ _ h_ne_target_n]
      exact ih (by omega) (by omega)

/-- **At any position outside the swap range, output = input.** -/
theorem modmult_swap_acc_mult_aux_at_other
    (bits k q : Nat) (hk : k ≤ bits) (f : Nat → Bool)
    (h_q_not_target : ∀ i, i < k → q ≠ modmult_target_idx i)
    (h_q_not_mult : ∀ i, i < k → q ≠ mult_control_idx bits i) :
    Gate.applyNat (modmult_swap_acc_mult_aux bits k) f q = f q := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [modmult_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (modmult_target_idx_ne_mult_control_idx bits n n hn_lt)]
    have h_q_ne_target_n : q ≠ modmult_target_idx n := h_q_not_target n (by omega)
    have h_q_ne_mult_n : q ≠ mult_control_idx bits n := h_q_not_mult n (by omega)
    rw [update_neq _ _ _ _ h_q_ne_mult_n]
    rw [update_neq _ _ _ _ h_q_ne_target_n]
    exact ih (by omega)
            (fun i hi => h_q_not_target i (by omega))
            (fun i hi => h_q_not_mult i (by omega))

/-! ## Full swap correctness on `modmult_input_F`. -/

/-- **Sanity helper:** `modmult_target_idx i = 2 + 2*i + 1`. -/
theorem modmult_target_idx_value (i : Nat) :
    modmult_target_idx i = 2 + 2 * i + 1 := rfl

/-- **Full SWAP correctness on `modmult_input_F`.** -/
theorem modmult_swap_acc_mult_apply
    (bits m acc : Nat) (hbits : 1 ≤ bits)
    (hm : m < 2^bits) (hacc : acc < 2^bits) :
    Gate.applyNat (modmult_swap_acc_mult bits) (modmult_input_F bits m acc)
      = modmult_input_F bits acc m := by
  unfold modmult_swap_acc_mult
  funext q
  -- Case split on q's role.
  by_cases h_target : ∃ i, i < bits ∧ q = modmult_target_idx i
  · obtain ⟨i, hi, hq_eq⟩ := h_target
    rw [hq_eq]
    rw [modmult_swap_acc_mult_aux_at_target_in_range bits bits i (le_refl _) hi]
    rw [mult_input_control_bit bits m acc i hi]
    -- RHS: modmult_input_F bits acc m at modmult_target_idx i = m.testBit i.
    -- modmult_target_idx i = 2 + 2*i + 1 — workspace.
    show m.testBit i = modmult_input_F bits acc m (modmult_target_idx i)
    unfold modmult_input_F
    rw [modmult_target_idx_value]
    rw [if_pos (by omega : 2 + 2 * i + 1 < 2 + 2 * bits + 1)]
    exact (cuccaro_input_F_at_b 2 i false 0 m).symm
  · by_cases h_mult : ∃ i, i < bits ∧ q = mult_control_idx bits i
    · obtain ⟨i, hi, hq_eq⟩ := h_mult
      rw [hq_eq]
      rw [modmult_swap_acc_mult_aux_at_mult_in_range bits bits i (le_refl _) hi]
      -- LHS: input (modmult_target_idx i) = acc.testBit i.
      have h_lhs : modmult_input_F bits m acc (modmult_target_idx i) = acc.testBit i := by
        unfold modmult_input_F modmult_target_idx
        rw [if_pos (by omega : 2 + 2 * i + 1 < 2 + 2 * bits + 1)]
        exact cuccaro_input_F_at_b 2 i false 0 acc
      rw [h_lhs]
      -- RHS: modmult_input_F bits acc m at mult_control_idx bits i = acc.testBit i.
      exact (mult_input_control_bit bits acc m i hi).symm
    · -- Other positions: unchanged by swap, AND modmult_input_F at q with swapped args
      --   equals modmult_input_F at q with original args (since both depend only on
      --   workspace structure, not m or acc, at these positions).
      have h_not_target : ∀ i, i < bits → q ≠ modmult_target_idx i := by
        intros i hi heq
        exact h_target ⟨i, hi, heq⟩
      have h_not_mult : ∀ i, i < bits → q ≠ mult_control_idx bits i := by
        intros i hi heq
        exact h_mult ⟨i, hi, heq⟩
      rw [modmult_swap_acc_mult_aux_at_other bits bits q (le_refl _) _ h_not_target h_not_mult]
      -- Now: modmult_input_F bits m acc q = modmult_input_F bits acc m q.
      -- For workspace q (not target bit): depends only on q's position class.
      -- For mult register q (not mult_i for any i): impossible — q outside layout.
      -- For above-layout q: both = false.
      by_cases hq_ws : q < 2 + 2 * bits + 1
      · -- Workspace q.  q is not a target bit (h_not_target).
        unfold modmult_input_F
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
              -- So q IS a target bit (modmult_target_idx i = 2 + 2*i + 1 = q).
              -- Contradiction with h_not_target.
              exfalso
              have hi_bound : (q - 2 - 1) / 2 < bits := by omega
              have h_eq : q = modmult_target_idx ((q - 2 - 1) / 2) := by
                unfold modmult_target_idx; omega
              exact h_not_target ((q - 2 - 1) / 2) hi_bound h_eq
            · rw [if_neg hq_odd, if_neg hq_odd]
      · -- q ≥ 2 + 2*bits + 1.  Could be a multiplier bit (but excluded) or above-layout.
        push_neg at hq_ws
        unfold modmult_input_F
        rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
        rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
        by_cases hq_in_mult : q < 2 + 2 * bits + 1 + bits
        · -- q in multiplier register.
          rw [if_pos hq_in_mult, if_pos hq_in_mult]
          -- The mult value depends on the first arg.  LHS = m.testBit ..., RHS = acc.testBit ...
          -- But h_not_mult says q ≠ mult_control_idx bits i for any i < bits.
          -- For q in [2 + 2*bits + 1, 2 + 2*bits + 1 + bits), q = 2 + 2*bits + 1 + k
          --   where k = q - (2 + 2*bits + 1) < bits.  So q = mult_control_idx bits k.
          -- Contradiction with h_not_mult.
          exfalso
          set k := q - (2 + 2 * bits + 1)
          have hk_lt : k < bits := by omega
          have hq_eq : q = mult_control_idx bits k := by
            unfold mult_control_idx; omega
          exact h_not_mult k hk_lt hq_eq
        · -- q ≥ 2 + 2*bits + 1 + bits: above layout.  Both = false.
          rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]
          rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]

end FormalRV.BQAlgo
