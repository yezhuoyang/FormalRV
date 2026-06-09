import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultEncoding
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSpec
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultQStart
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultFamily
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSizing
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultPrefixInvariant
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultAccumulatorRangeInverseAndInPlace

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
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

end FormalRV.BQAlgo
