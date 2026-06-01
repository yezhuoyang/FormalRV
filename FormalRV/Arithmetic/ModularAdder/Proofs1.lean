import FormalRV.Arithmetic.RippleCarryAdder
import Mathlib.Data.Nat.Bitwise
import FormalRV.Arithmetic.ModularAdder.Defs

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Power-of-2 modular adder (the easy case)

The patched Gidney adder implements `(a + b) mod 2^bits` in the
target register when applied to `adder_input_F bits a b`.  With
`a = c` (constant in the read register) and `b = x` (data in the
target register), the output target register decodes to
`(x + c) mod 2^bits`.

This is just a renaming wrapper around
`gidney_adder_patched_target_decode` (in `RippleCarryAdder.lean`),
exposed under a name the modular-multiplication layer can call
directly. -/

/-- **The patched Gidney adder implements `(x + c) mod 2^bits`.**
With the constant `c` placed in the read register and the data `x`
placed in the target register, applying the patched full faithful
no-measurement Gidney adder writes `(x + c) mod 2^bits` into the
target register. -/
theorem patched_adder_add_const_pow2
    (bits c x : Nat) (hbits : 2 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits) :
    gidney_target_val bits
      (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
        (adder_input_F bits c x))
    = addConstPow2Spec bits c x := by
  unfold addConstPow2Spec
  rw [Nat.add_comm x c]
  exact gidney_adder_patched_target_decode bits c x hbits hc hx

/-- **Bundled `(x + c) mod 2^bits` primitive.**  Combines the
power-of-2 modular-addition spec, the patched-adder WellTyped, the
read-register preservation (constant `c` survives), and the carry
clearing (workspace zeroed) — the single theorem a modular-
multiplication layer should call when adding a constant modulo
`2^bits`. -/
theorem patched_adder_add_const_pow2_bundled
    (bits c x : Nat) (hbits : 2 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits) :
    Gate.WellTyped (adder_n_qubits bits)
      (gidney_adder_full_faithful_no_measurement_patched bits)
    ∧ gidney_target_val bits
        (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits c x))
      = addConstPow2Spec bits c x
    ∧ (∀ i, i < bits →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits c x) (read_idx i) = c.testBit i)
    ∧ (∀ i, i < bits →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits c x) (carry_idx i) = false) := by
  obtain ⟨hwt, _, hr, hc_clear⟩ :=
    gidney_adder_patched_primitive bits c x hbits hc hx
  exact ⟨hwt, patched_adder_add_const_pow2 bits c x hbits hc hx, hr, hc_clear⟩

/-- **The patched Gidney adder with `read = 2^bits - N` implements
the wraparound subtraction**.  For `0 < N ≤ 2^bits` and `x < 2^bits`,
applying the patched adder to `adder_input_F bits (2^bits - N) x`
decodes the target register to `(x + (2^bits - N)) mod 2^bits`. -/
theorem patched_adder_sub_const_pow2
    (bits N x : Nat) (hbits : 2 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    gidney_target_val bits
      (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
        (adder_input_F bits (2^bits - N) x))
    = subConstPow2Spec bits N x := by
  unfold subConstPow2Spec
  have h_c : 2^bits - N < 2^bits := by
    have h2pos : 0 < 2^bits := Nat.two_pow_pos bits
    omega
  exact patched_adder_add_const_pow2 bits (2^bits - N) x hbits h_c hx

/-! ## Arithmetic split-case lemmas

These recover the two natural arithmetic specializations of
`subConstPow2Spec`:

* When `N ≤ x` (no underflow), the wraparound result equals the
  ordinary Nat subtraction `x - N`.
* When `x < N` (underflow), the wraparound result equals
  `x + 2^bits - N` (a value in `[2^bits - N, 2^bits - 1]`).

Together they characterize the subtraction modulo `2^bits` without
ever using saturated Nat subtraction. -/

/-- No-underflow case: `N ≤ x` ⇒ `subConstPow2Spec bits N x = x - N`. -/
theorem subConstPow2Spec_of_le
    (bits N x : Nat) (hN : N ≤ 2^bits) (hx : x < 2^bits) (hle : N ≤ x) :
    subConstPow2Spec bits N x = x - N := by
  unfold subConstPow2Spec
  have h_eq : x + (2^bits - N) = (x - N) + 2^bits := by omega
  rw [h_eq, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- Underflow case: `x < N` ⇒ `subConstPow2Spec bits N x = x + 2^bits - N`. -/
theorem subConstPow2Spec_of_lt
    (bits N x : Nat) (hN : N ≤ 2^bits) (hx_lt : x < N) :
    subConstPow2Spec bits N x = x + 2^bits - N := by
  unfold subConstPow2Spec
  have h2pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_lt : x + (2^bits - N) < 2^bits := by omega
  rw [Nat.mod_eq_of_lt h_lt]
  omega

/-- Arithmetic high-bit lemma, no-underflow case: when `N ≤ x` the
widened result equals `x - N`, which fits in `bits` bits, so bit
`bits` is `false`. -/
theorem subConstPow2WideSpec_high_bit_of_le
    (bits N x : Nat) (hN : N ≤ 2^bits) (hx : x < 2^bits) (hle : N ≤ x) :
    (subConstPow2WideSpec bits N x).testBit bits = false := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_eq : subConstPow2WideSpec bits N x = x - N := by
    unfold subConstPow2WideSpec
    have h_eq2 : x + (2^(bits + 1) - N) = (x - N) + 2^(bits + 1) := by omega
    rw [h_eq2, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h_eq]
  exact Nat.testBit_lt_two_pow (by omega)

/-- Arithmetic high-bit lemma, underflow case: when `x < N ≤ 2^bits`
the widened result lies in `[2^bits, 2^(bits+1))`, so bit `bits` is `true`. -/
theorem subConstPow2WideSpec_high_bit_of_lt
    (bits N x : Nat) (hN : N ≤ 2^bits) (hx_lt : x < N) :
    (subConstPow2WideSpec bits N x).testBit bits = true := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_2pos : 0 < 2^(bits + 1) := Nat.two_pow_pos (bits + 1)
  have h_eq : subConstPow2WideSpec bits N x = x + 2^(bits+1) - N := by
    unfold subConstPow2WideSpec
    have h_lt : x + (2^(bits+1) - N) < 2^(bits+1) := by omega
    rw [Nat.mod_eq_of_lt h_lt]
    omega
  rw [h_eq]
  have h_lo : 2^bits ≤ x + 2^(bits+1) - N := by omega
  have h_hi : x + 2^(bits+1) - N < 2^(bits + 1) := by omega
  exact Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h_lo h_hi

/-- **Main high-bit theorem**: bit `bits` of the widened-subtraction
result is exactly the comparison flag `decide (x < N)`. -/
theorem subConstPow2WideSpec_high_bit
    (bits N x : Nat) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    (subConstPow2WideSpec bits N x).testBit bits = decide (x < N) := by
  by_cases h : x < N
  · rw [decide_eq_true h]
    exact subConstPow2WideSpec_high_bit_of_lt bits N x hN h
  · rw [decide_eq_false (by omega)]
    exact subConstPow2WideSpec_high_bit_of_le bits N x hN hx (by omega)

/-- **Gate-level underflow flag theorem** (Deliverable C).
Instantiating the patched Gidney adder at width `bits + 1` with
`read = 2^(bits + 1) - N`, the target bit at position `bits` is
exactly `decide (x < N)`. -/
theorem patched_adder_sub_const_underflow_flag
    (bits N x : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.applyNat
      (gidney_adder_full_faithful_no_measurement_patched (bits + 1))
      (adder_input_F (bits + 1) (2^(bits + 1) - N) x)
      (target_idx bits)
    = decide (x < N) := by
  have h_hb : 2 ≤ bits + 1 := by omega
  have h_2pos : 0 < 2^(bits + 1) := Nat.two_pow_pos (bits + 1)
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_a : 2^(bits + 1) - N < 2^(bits + 1) := by omega
  have h_b : x < 2^(bits + 1) := by omega
  obtain ⟨_, ht, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                          (bits + 1) (2^(bits + 1) - N) x h_hb h_a h_b
  have h := ht bits (by omega)
  rw [h]
  -- Goal: ((2^(bits+1) - N) + x).testBit bits = decide (x < N)
  have h_mod_eq : (((2^(bits+1) - N) + x) % 2^(bits+1)).testBit bits
                  = ((2^(bits+1) - N) + x).testBit bits := by
    rw [Nat.testBit_mod_two_pow]
    simp [show bits < bits + 1 from by omega]
  rw [← h_mod_eq]
  -- Now: testBit bits of the modded value
  rw [show (((2^(bits+1) - N) + x) % 2^(bits+1))
        = subConstPow2WideSpec bits N x from by
        unfold subConstPow2WideSpec; congr 1; omega]
  exact subConstPow2WideSpec_high_bit bits N x hN hx

/-- **Helper**: bit `i` of `y + 2^n` equals bit `i` of `y` when `i < n`
(adding a power of 2 at position `n` doesn't affect lower bits). -/
theorem testBit_add_two_pow_below
    (y i n : Nat) (h : i < n) :
    (y + 2^n).testBit i = y.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  congr 1
  have h_pow : (2:Nat)^n = 2^i * 2^(n - i) := by
    rw [← pow_add]; congr 1; omega
  rw [h_pow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i)]
  have h_ni : 0 < n - i := by omega
  have h_2pow_even : (2:Nat)^(n - i) % 2 = 0 := by
    have h_split : n - i = (n - i - 1) + 1 := by omega
    rw [h_split, pow_succ]
    exact Nat.mul_mod_left (2^(n - i - 1)) 2
  rw [Nat.add_mod, h_2pow_even, Nat.add_zero, Nat.mod_mod]

/-- **Gate-level low-bits theorem** (Deliverable D).  At the widened
adder, the lower `bits` target positions decode to the bits of
`subConstPow2Spec bits N x` — i.e., they hold the wraparound
subtraction value (mod `2^bits`) just as the narrow adder would. -/
theorem patched_adder_sub_const_low_bits
    (bits N x i : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < 2^bits) (hi : i < bits) :
    Gate.applyNat
      (gidney_adder_full_faithful_no_measurement_patched (bits + 1))
      (adder_input_F (bits + 1) (2^(bits + 1) - N) x)
      (target_idx i)
    = (subConstPow2Spec bits N x).testBit i := by
  have h_hb : 2 ≤ bits + 1 := by omega
  have h_2pos : 0 < 2^(bits + 1) := Nat.two_pow_pos (bits + 1)
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_a : 2^(bits + 1) - N < 2^(bits + 1) := by omega
  have h_b : x < 2^(bits + 1) := by omega
  obtain ⟨_, ht, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                          (bits + 1) (2^(bits + 1) - N) x h_hb h_a h_b
  have h := ht i (by omega)
  rw [h]
  unfold subConstPow2Spec
  rw [Nat.testBit_mod_two_pow]
  simp [show i < bits from hi]
  have h_rearrange : (2^(bits+1) - N) + x = (x + (2^bits - N)) + 2^bits := by omega
  rw [h_rearrange]
  exact testBit_add_two_pow_below _ i bits hi

/-! ### Deliverable B — preservation / read-idx action lemmas -/

/-- Outside the read register's `[0, bits)` window, `prepareMaskedConstRead`
acts as the identity (in particular: target, carry, and `flagIdx` are
preserved). -/
theorem prepareMaskedConstRead_preserves_outside
    (bits N flagIdx : Nat) (f : Nat → Bool) (p : Nat)
    (h : ∀ i, i < bits → p ≠ read_idx i) :
    Gate.applyNat (prepareMaskedConstRead bits N flagIdx) f p = f p := by
  induction bits with
  | zero => rfl
  | succ k ih =>
      have ih_inst : Gate.applyNat (prepareMaskedConstRead k N flagIdx) f p = f p := by
        apply ih; intro i hi; exact h i (by omega)
      have h_p_rk : p ≠ read_idx k := h k (by omega)
      show Gate.applyNat (if N.testBit k = true then Gate.CX flagIdx (read_idx k) else Gate.I)
            (Gate.applyNat (prepareMaskedConstRead k N flagIdx) f) p = f p
      split
      · simp only [Gate.applyNat_CX]
        rw [update_neq _ _ _ _ h_p_rk]
        exact ih_inst
      · exact ih_inst

/-- At `read_idx j` (for `j < bits`), `prepareMaskedConstRead` XORs the
existing value with `f flagIdx && N.testBit j` — i.e. it conditionally
flips the read bit based on the flag and the constant pattern. -/
theorem prepareMaskedConstRead_at_read_idx
    (bits N flagIdx : Nat) (f : Nat → Bool) (j : Nat) (hj : j < bits)
    (h_flag_disj_read : ∀ i, i < bits → flagIdx ≠ read_idx i) :
    Gate.applyNat (prepareMaskedConstRead bits N flagIdx) f (read_idx j) =
    xor (f (read_idx j)) (f flagIdx && N.testBit j) := by
  induction bits with
  | zero => omega
  | succ k ih =>
      show Gate.applyNat (if N.testBit k = true then Gate.CX flagIdx (read_idx k) else Gate.I)
            (Gate.applyNat (prepareMaskedConstRead k N flagIdx) f) (read_idx j) = _
      by_cases hjk : j < k
      · have h_rk_neq_rj : read_idx j ≠ read_idx k := by unfold read_idx; omega
        split
        · simp only [Gate.applyNat_CX]
          rw [update_neq _ _ _ _ h_rk_neq_rj]
          exact ih hjk (fun i hi => h_flag_disj_read i (by omega))
        · exact ih hjk (fun i hi => h_flag_disj_read i (by omega))
      · have hjeq : j = k := by omega
        rw [hjeq]
        have h_frame_rk : Gate.applyNat (prepareMaskedConstRead k N flagIdx) f (read_idx k)
                         = f (read_idx k) := by
          apply prepareMaskedConstRead_preserves_outside
          intro i hi; unfold read_idx; omega
        have h_frame_flag : Gate.applyNat (prepareMaskedConstRead k N flagIdx) f flagIdx
                           = f flagIdx := by
          apply prepareMaskedConstRead_preserves_outside
          intro i hi; exact h_flag_disj_read i (by omega)
        split
        next h_test =>
          simp only [Gate.applyNat_CX]
          rw [update_eq, h_frame_rk, h_frame_flag, h_test]
          simp [Bool.xor_comm]
        next h_test =>
          have h_test_false : N.testBit k = false := by
            cases hN_t : N.testBit k
            · rfl
            · exact absurd hN_t h_test
          show Gate.applyNat (prepareMaskedConstRead k N flagIdx) f (read_idx k) = _
          rw [h_frame_rk, h_test_false]
          simp

/-! ### Generic frame lemma for well-typed gates

A `Gate.WellTyped dim g` gate commutes with `update _ p v` whenever
`p ≥ dim`.  This lets us slip an "out-of-band" flag bit past any
in-range gate sequence — crucial for the conditional add-back proof. -/

/-- Any `WellTyped dim` gate commutes with `update _ p v` for `p ≥ dim`. -/
theorem applyNat_commute_update_above_dim
    (dim : Nat) (g : Gate) (h_wt : Gate.WellTyped dim g)
    (f : Nat → Bool) (p : Nat) (v : Bool) (h_p : dim ≤ p) :
    Gate.applyNat g (update f p v) = update (Gate.applyNat g f) p v := by
  induction g generalizing f with
  | I => rfl
  | X q =>
      have hq : q < dim := h_wt
      have h_q_p : q ≠ p := by omega
      simp only [Gate.applyNat_X]
      rw [update_neq _ _ _ _ h_q_p]
      exact update_update_comm f p q v _ h_q_p.symm
  | CX c t =>
      obtain ⟨hc, ht, _⟩ := h_wt
      have h_p_c : p ≠ c := by omega
      have h_p_t : p ≠ t := by omega
      exact applyNat_CX_commute_update_disjoint c t f p v h_p_c h_p_t
  | CCX a b c =>
      obtain ⟨ha, hb, hc, _, _, _⟩ := h_wt
      have h_p_a : p ≠ a := by omega
      have h_p_b : p ≠ b := by omega
      have h_p_c : p ≠ c := by omega
      exact applyNat_CCX_commute_update_disjoint a b c f p v h_p_a h_p_b h_p_c
  | seq g₁ g₂ ih₁ ih₂ =>
      obtain ⟨hwt₁, hwt₂⟩ := h_wt
      apply applyNat_seq_commute_update _ _ _ _ _ (ih₁ hwt₁) (ih₂ hwt₂)

/-! ### `adder_input_F` evaluation helpers -/

theorem adder_input_F_at_read_idx_eq
    (n a b j : Nat) (hj : j < n) :
    adder_input_F n a b (read_idx j) = a.testBit j := by
  unfold adder_input_F
  have h_mod : (read_idx j) % 3 = 0 := by unfold read_idx; omega
  have h_div : (read_idx j) / 3 = j := by unfold read_idx; omega
  rw [h_mod, h_div]
  simp [hj]

theorem adder_input_F_eq_outside_read_in_range
    (n a b k : Nat) (h : ∀ j, j < n → k ≠ read_idx j) :
    adder_input_F n a b k = adder_input_F n 0 b k := by
  unfold adder_input_F
  rcases h_mod : k % 3 with _ | _ | _
  · have h_k_eq : k = read_idx (k / 3) := by unfold read_idx; omega
    by_cases hkn : k / 3 < n
    · exfalso; apply h (k / 3) hkn; exact h_k_eq
    · simp [hkn]
  · rfl
  · rfl

/-- **Key intermediate theorem.**  Applying `prepareMaskedConstRead` to
`update (adder_input_F bits 0 x) flagIdx flag` yields
`update (adder_input_F bits (if flag then N else 0) x) flagIdx flag` —
i.e. the read register has been re-loaded with the **conditionally
masked** constant `flag ∧ N`. -/
theorem prepareMaskedConstRead_yields_input_F
    (bits N flagIdx x : Nat) (flag : Bool)
    (h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j) :
    Gate.applyNat (prepareMaskedConstRead bits N flagIdx)
      (update (adder_input_F bits 0 x) flagIdx flag)
    = update (adder_input_F bits (if flag then N else 0) x) flagIdx flag := by
  funext k
  by_cases h_k_flag : k = flagIdx
  · rw [h_k_flag]
    rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ flagIdx h_disj]
    rw [update_eq, update_eq]
  · by_cases h_k_read : ∃ j, j < bits ∧ k = read_idx j
    · obtain ⟨j, hj, h_kj⟩ := h_k_read
      rw [h_kj]
      rw [h_kj] at h_k_flag
      have h_rj_ne_flag : read_idx j ≠ flagIdx := h_k_flag
      rw [prepareMaskedConstRead_at_read_idx bits N flagIdx _ j hj h_disj]
      rw [update_neq _ _ _ _ h_rj_ne_flag, update_eq, update_neq _ _ _ _ h_rj_ne_flag]
      rw [adder_input_F_at_read_idx_eq bits 0 x j hj]
      rw [Nat.zero_testBit, Bool.false_xor]
      rw [adder_input_F_at_read_idx_eq bits _ x j hj]
      cases flag with
      | true => simp
      | false => simp [Nat.zero_testBit]
    · have h_k_read' : ∀ j, j < bits → k ≠ read_idx j := by
        intro j hj h_eq; exact h_k_read ⟨j, hj, h_eq⟩
      rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ k h_k_read']
      rw [update_neq _ _ _ _ h_k_flag, update_neq _ _ _ _ h_k_flag]
      rw [adder_input_F_eq_outside_read_in_range bits 0 x k h_k_read',
          ← adder_input_F_eq_outside_read_in_range bits (if flag then N else 0) x k h_k_read']

/-! ### Deliverable D — target decode theorem

The headline correctness theorem of this iteration. -/

/-- **Conditional add-back target decode.**  Applied to
`update (adder_input_F bits 0 x) flagIdx flag` (read register zero,
target register `x`, carry register zero, flag at `flagIdx`), the
`conditionalAddConstGate` produces target register equal to
`(x + (if flag then N else 0)) mod 2^bits`. -/
theorem conditionalAddConstGate_target_decode
    (bits N flagIdx x : Nat) (flag : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (h_flag : adder_n_qubits bits ≤ flagIdx) :
    gidney_target_val bits
      (Gate.applyNat (conditionalAddConstGate bits N flagIdx)
        (update (adder_input_F bits 0 x) flagIdx flag))
    = (x + (if flag then N else 0)) % 2^bits := by
  have h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j := by
    intro j hj
    unfold adder_n_qubits read_idx at *
    omega
  have h_disj_t : ∀ j, j < bits → flagIdx ≠ target_idx j := by
    intro j hj
    unfold adder_n_qubits target_idx at *
    omega
  have h_c_lt : (if flag then N else 0) < 2^bits := by
    cases flag with
    | true => exact hN
    | false => exact Nat.two_pow_pos bits
  unfold conditionalAddConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareMaskedConstRead_yields_input_F bits N flagIdx x flag h_disj]
  have h_wt : Gate.WellTyped (adder_n_qubits bits)
              (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  rw [applyNat_commute_update_above_dim (adder_n_qubits bits) _ h_wt _ _ _ h_flag]
  apply gidney_target_val_eq_sum_when_bits_match bits (x + (if flag then N else 0))
  intro i hi
  have h_target_neq_read : ∀ j, j < bits → target_idx i ≠ read_idx j := by
    intro j _; unfold target_idx read_idx; omega
  rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ (target_idx i) h_target_neq_read]
  have h_target_ne_flag : target_idx i ≠ flagIdx := (h_disj_t i hi).symm
  rw [update_neq _ _ _ _ h_target_ne_flag]
  obtain ⟨_, h_target, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                              bits (if flag then N else 0) x hbits h_c_lt hx
  rw [h_target i hi, Nat.add_comm]

/-! ### Frame / restoration / WellTyped deliverables

Five additional theorems that promote `conditionalAddConstGate` from a
"target-only" primitive to a fully reusable building block: read
register restored to zero, carry register cleared, flag preserved,
gate WellTyped in an enlarged dimension, and a bundled `_clean` form. -/

/-- **WellTyped monotonicity**: `WellTyped` is preserved under dimension
enlargement.  Generic helper, applies to any `Gate`. -/
theorem Gate.WellTyped.mono {dim dim' : Nat} {g : Gate}
    (h : Gate.WellTyped dim g) (h_le : dim ≤ dim') :
    Gate.WellTyped dim' g := by
  induction g with
  | I =>
      show 0 < dim'
      have : 0 < dim := h; omega
  | X q =>
      show q < dim'
      have : q < dim := h; omega
  | CX a b =>
      obtain ⟨_, _, hab⟩ := h
      exact ⟨by omega, by omega, hab⟩
  | CCX a b c =>
      obtain ⟨_, _, _, hab, hac, hbc⟩ := h
      exact ⟨by omega, by omega, by omega, hab, hac, hbc⟩
  | seq g₁ g₂ ih₁ ih₂ =>
      obtain ⟨hwt₁, hwt₂⟩ := h
      exact ⟨ih₁ hwt₁, ih₂ hwt₂⟩

/-- `prepareMaskedConstRead` is `WellTyped` in dimension `flagIdx + 1`
whenever the flag is placed above the adder's working register. -/
theorem prepareMaskedConstRead_wellTyped
    (bits N flagIdx : Nat) (h_flag : adder_n_qubits bits ≤ flagIdx) :
    Gate.WellTyped (flagIdx + 1) (prepareMaskedConstRead bits N flagIdx) := by
  induction bits with
  | zero =>
      show 0 < flagIdx + 1; omega
  | succ k ih =>
      show Gate.WellTyped (flagIdx + 1) _
      have h_flag_k : adder_n_qubits k ≤ flagIdx := by
        unfold adder_n_qubits at *; omega
      refine ⟨ih h_flag_k, ?_⟩
      by_cases h_test : N.testBit k
      · simp [h_test]
        unfold adder_n_qubits read_idx at *
        exact ⟨by omega, by omega, by omega⟩
      · simp [h_test]
        show 0 < flagIdx + 1; omega

/-- **Deliverable A — read register restored.**  After the full
conditional add-back, every in-range read position is back to zero
(the read register served only as a scratch space during the
underlying adder). -/
theorem conditionalAddConstGate_read_restored
    (bits N x flagIdx : Nat) (flag : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    ∀ i, i < bits →
      Gate.applyNat (conditionalAddConstGate bits N flagIdx)
        (update (adder_input_F bits 0 x) flagIdx flag) (read_idx i)
      = false := by
  intro i hi
  have h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j := by
    intro j hj
    unfold adder_n_qubits read_idx at *; omega
  have h_c_lt : (if flag then N else 0) < 2^bits := by
    cases flag with
    | true => exact hN
    | false => exact Nat.two_pow_pos bits
  unfold conditionalAddConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareMaskedConstRead_yields_input_F bits N flagIdx x flag h_disj]
  have h_wt : Gate.WellTyped (adder_n_qubits bits)
              (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  rw [applyNat_commute_update_above_dim (adder_n_qubits bits) _ h_wt _ _ _ hflagIdx]
  rw [prepareMaskedConstRead_at_read_idx bits N flagIdx _ i hi h_disj]
  have h_read_ne_flag : read_idx i ≠ flagIdx := (h_disj i hi).symm
  rw [update_neq _ _ _ _ h_read_ne_flag, update_eq]
  obtain ⟨h_read, _, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                            bits (if flag then N else 0) x hbits h_c_lt hx
  rw [h_read i hi]
  cases flag with
  | true => simp
  | false => simp [Nat.zero_testBit]

/-- **Deliverable B — carry register cleared.**  Every in-range carry
position is `false` after the full conditional add-back (carries are
fully cleared by the inner patched Gidney adder, and the outer prep
cascade touches no carry positions). -/
theorem conditionalAddConstGate_carries_cleared
    (bits N x flagIdx : Nat) (flag : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    ∀ i, i < bits →
      Gate.applyNat (conditionalAddConstGate bits N flagIdx)
        (update (adder_input_F bits 0 x) flagIdx flag) (carry_idx i)
      = false := by
  intro i hi
  have h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j := by
    intro j hj
    unfold adder_n_qubits read_idx at *; omega
  have h_disj_c : ∀ j, j < bits → flagIdx ≠ carry_idx j := by
    intro j hj
    unfold adder_n_qubits carry_idx at *; omega
  have h_c_lt : (if flag then N else 0) < 2^bits := by
    cases flag with
    | true => exact hN
    | false => exact Nat.two_pow_pos bits
  unfold conditionalAddConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareMaskedConstRead_yields_input_F bits N flagIdx x flag h_disj]
  have h_wt : Gate.WellTyped (adder_n_qubits bits)
              (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  rw [applyNat_commute_update_above_dim (adder_n_qubits bits) _ h_wt _ _ _ hflagIdx]
  have h_carry_neq_read : ∀ j, j < bits → carry_idx i ≠ read_idx j := by
    intro j _; unfold carry_idx read_idx; omega
  rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ (carry_idx i)
        h_carry_neq_read]
  have h_carry_ne_flag : carry_idx i ≠ flagIdx := (h_disj_c i hi).symm
  rw [update_neq _ _ _ _ h_carry_ne_flag]
  obtain ⟨_, _, h_carry⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                            bits (if flag then N else 0) x hbits h_c_lt hx
  exact h_carry i hi

/-- **Deliverable C — flag preserved.**  The flag bit at `flagIdx`
survives the full conditional add-back unchanged.  Follows from the
adder commuting past the flag update (by `WellTyped` framing) and
both preps preserving positions outside the read range. -/
theorem conditionalAddConstGate_flag_preserved
    (bits N x flagIdx : Nat) (flag : Bool)
    (hbits : 2 ≤ bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx)
      (update (adder_input_F bits 0 x) flagIdx flag) flagIdx = flag := by
  have h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j := by
    intro j hj
    unfold adder_n_qubits read_idx at *; omega
  unfold conditionalAddConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareMaskedConstRead_yields_input_F bits N flagIdx x flag h_disj]
  have h_wt : Gate.WellTyped (adder_n_qubits bits)
              (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  rw [applyNat_commute_update_above_dim (adder_n_qubits bits) _ h_wt _ _ _ hflagIdx]
  rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ flagIdx h_disj]
  rw [update_eq]

/-- **Deliverable D — `WellTyped` at `flagIdx + 1`.**  The whole
conditional add-back gate is `WellTyped` in the enlarged dimension
that includes the out-of-band flag bit. -/
theorem conditionalAddConstGate_wellTyped
    (bits N flagIdx : Nat) (hbits : 2 ≤ bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    Gate.WellTyped (flagIdx + 1) (conditionalAddConstGate bits N flagIdx) := by
  unfold conditionalAddConstGate
  have h_prep : Gate.WellTyped (flagIdx + 1)
                  (prepareMaskedConstRead bits N flagIdx) :=
    prepareMaskedConstRead_wellTyped bits N flagIdx hflagIdx
  have h_adder_base : Gate.WellTyped (adder_n_qubits bits)
                  (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  have h_adder : Gate.WellTyped (flagIdx + 1)
                  (gidney_adder_full_faithful_no_measurement_patched bits) :=
    Gate.WellTyped.mono h_adder_base (by omega)
  exact ⟨h_prep, ⟨h_adder, h_prep⟩⟩

/-- **Deliverable E — bundled clean primitive.**  The headline
characterisation of `conditionalAddConstGate`: WellTyped, correct
target decode, read register restored, carries cleared, flag
preserved.  This is the one theorem downstream consumers should call. -/
theorem conditionalAddConstGate_clean
    (bits N x flagIdx : Nat) (flag : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    Gate.WellTyped (flagIdx + 1) (conditionalAddConstGate bits N flagIdx)
    ∧ gidney_target_val bits
        (Gate.applyNat (conditionalAddConstGate bits N flagIdx)
          (update (adder_input_F bits 0 x) flagIdx flag))
      = (x + (if flag then N else 0)) % 2^bits
    ∧ (∀ i, i < bits →
        Gate.applyNat (conditionalAddConstGate bits N flagIdx)
          (update (adder_input_F bits 0 x) flagIdx flag) (read_idx i) = false)
    ∧ (∀ i, i < bits →
        Gate.applyNat (conditionalAddConstGate bits N flagIdx)
          (update (adder_input_F bits 0 x) flagIdx flag) (carry_idx i) = false)
    ∧ Gate.applyNat (conditionalAddConstGate bits N flagIdx)
        (update (adder_input_F bits 0 x) flagIdx flag) flagIdx = flag := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact conditionalAddConstGate_wellTyped bits N flagIdx hbits hflagIdx
  · exact conditionalAddConstGate_target_decode bits N flagIdx x flag hbits hN hx hflagIdx
  · exact conditionalAddConstGate_read_restored bits N x flagIdx flag hbits hN hx hflagIdx
  · exact conditionalAddConstGate_carries_cleared bits N x flagIdx flag hbits hN hx hflagIdx
  · exact conditionalAddConstGate_flag_preserved bits N x flagIdx flag hbits hflagIdx

/-- Outside the read register's `[0, bits)` window, `prepareConstRead`
is the identity (so target, carry, and any extra ancillas are
preserved). -/
theorem prepareConstRead_preserves_outside
    (bits c : Nat) (f : Nat → Bool) (p : Nat)
    (h : ∀ i, i < bits → p ≠ read_idx i) :
    Gate.applyNat (prepareConstRead bits c) f p = f p := by
  induction bits with
  | zero => rfl
  | succ k ih =>
      have ih_inst : Gate.applyNat (prepareConstRead k c) f p = f p := by
        apply ih; intro i hi; exact h i (by omega)
      have h_p_rk : p ≠ read_idx k := h k (by omega)
      show Gate.applyNat (if c.testBit k = true then Gate.X (read_idx k) else Gate.I)
            (Gate.applyNat (prepareConstRead k c) f) p = f p
      split
      · simp only [Gate.applyNat_X]
        rw [update_neq _ _ _ _ h_p_rk]
        exact ih_inst
      · exact ih_inst

/-- At `read_idx j` (for `j < bits`), `prepareConstRead` XORs the value
with `c.testBit j`. -/
theorem prepareConstRead_at_read_idx
    (bits c : Nat) (f : Nat → Bool) (j : Nat) (hj : j < bits) :
    Gate.applyNat (prepareConstRead bits c) f (read_idx j) =
    xor (f (read_idx j)) (c.testBit j) := by
  induction bits with
  | zero => omega
  | succ k ih =>
      show Gate.applyNat (if c.testBit k = true then Gate.X (read_idx k) else Gate.I)
            (Gate.applyNat (prepareConstRead k c) f) (read_idx j) = _
      by_cases hjk : j < k
      · have h_rk_neq_rj : read_idx j ≠ read_idx k := by unfold read_idx; omega
        split
        · simp only [Gate.applyNat_X]
          rw [update_neq _ _ _ _ h_rk_neq_rj]
          exact ih hjk
        · exact ih hjk
      · have hjeq : j = k := by omega
        rw [hjeq]
        have h_frame_rk : Gate.applyNat (prepareConstRead k c) f (read_idx k) = f (read_idx k) := by
          apply prepareConstRead_preserves_outside
          intro i hi; unfold read_idx; omega
        split
        next h_test =>
          simp only [Gate.applyNat_X]
          rw [update_eq, h_frame_rk, h_test]
          simp [Bool.xor_comm]
        next h_test =>
          have h_test_false : c.testBit k = false := by
            cases hN_t : c.testBit k
            · rfl
            · exact absurd hN_t h_test
          show Gate.applyNat (prepareConstRead k c) f (read_idx k) = _
          rw [h_frame_rk, h_test_false]
          simp

/-- `prepareConstRead bits c` applied to `adder_input_F bits 0 x`
produces exactly `adder_input_F bits c x` — i.e., the read register
has been loaded with the bits of `c`. -/
theorem prepareConstRead_yields_input_F
    (bits c x : Nat) :
    Gate.applyNat (prepareConstRead bits c) (adder_input_F bits 0 x)
    = adder_input_F bits c x := by
  funext k
  by_cases h_k_read : ∃ j, j < bits ∧ k = read_idx j
  · obtain ⟨j, hj, h_kj⟩ := h_k_read
    rw [h_kj]
    rw [prepareConstRead_at_read_idx bits c _ j hj]
    rw [adder_input_F_at_read_idx_eq bits 0 x j hj]
    rw [Nat.zero_testBit, Bool.false_xor]
    rw [adder_input_F_at_read_idx_eq bits c x j hj]
  · have h_k_read' : ∀ j, j < bits → k ≠ read_idx j := by
      intro j hj h_eq; exact h_k_read ⟨j, hj, h_eq⟩
    rw [prepareConstRead_preserves_outside bits c _ k h_k_read']
    rw [adder_input_F_eq_outside_read_in_range bits 0 x k h_k_read',
        ← adder_input_F_eq_outside_read_in_range bits c x k h_k_read']

/-- `prepareConstRead bits c` is WellTyped at the adder's natural
dimension `adder_n_qubits bits = 3*bits + 2`. -/
theorem prepareConstRead_wellTyped
    (bits c : Nat) :
    Gate.WellTyped (adder_n_qubits bits) (prepareConstRead bits c) := by
  induction bits with
  | zero =>
      show 0 < adder_n_qubits 0
      unfold adder_n_qubits; omega
  | succ k ih =>
      show Gate.WellTyped (adder_n_qubits (k + 1)) _
      have h_extend : Gate.WellTyped (adder_n_qubits (k + 1)) (prepareConstRead k c) := by
        apply Gate.WellTyped.mono ih
        unfold adder_n_qubits; omega
      refine ⟨h_extend, ?_⟩
      by_cases h_test : c.testBit k
      · simp [h_test]
        show read_idx k < adder_n_qubits (k + 1)
        unfold adder_n_qubits read_idx; omega
      · simp [h_test]
        show 0 < adder_n_qubits (k + 1)
        unfold adder_n_qubits; omega

/-- **Bundled clean primitive** for `addConstGate`.  Takes a clean
`adder_input_F bits 0 x` and produces:
* WellTyped at the natural dimension `adder_n_qubits bits`;
* target decodes to `(x + c) mod 2^bits`;
* read register restored to zero;
* carries cleared. -/
theorem addConstGate_clean
    (bits c x : Nat) (hbits : 2 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits) :
    Gate.WellTyped (adder_n_qubits bits) (addConstGate bits c)
    ∧ gidney_target_val bits
        (Gate.applyNat (addConstGate bits c) (adder_input_F bits 0 x))
      = (x + c) % 2^bits
    ∧ (∀ i, i < bits →
        Gate.applyNat (addConstGate bits c) (adder_input_F bits 0 x) (read_idx i) = false)
    ∧ (∀ i, i < bits →
        Gate.applyNat (addConstGate bits c) (adder_input_F bits 0 x) (carry_idx i) = false) := by
  have h_prep_wt : Gate.WellTyped (adder_n_qubits bits) (prepareConstRead bits c) :=
    prepareConstRead_wellTyped bits c
  have h_adder_wt : Gate.WellTyped (adder_n_qubits bits)
                    (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  have h_wt : Gate.WellTyped (adder_n_qubits bits) (addConstGate bits c) :=
    ⟨h_prep_wt, ⟨h_adder_wt, h_prep_wt⟩⟩
  obtain ⟨h_read, h_target, h_carry⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                                          bits c x hbits hc hx
  refine ⟨h_wt, ?_, ?_, ?_⟩
  · apply gidney_target_val_eq_sum_when_bits_match bits (x + c)
    intro i hi
    show Gate.applyNat (addConstGate bits c) (adder_input_F bits 0 x) (target_idx i)
       = (x + c).testBit i
    unfold addConstGate
    rw [Gate.applyNat_seq, Gate.applyNat_seq]
    rw [prepareConstRead_yields_input_F bits c x]
    have h_t_neq_read : ∀ j, j < bits → target_idx i ≠ read_idx j := by
      intro j _; unfold target_idx read_idx; omega
    rw [prepareConstRead_preserves_outside bits c _ (target_idx i) h_t_neq_read]
    rw [h_target i hi, Nat.add_comm]
  · intro i hi
    unfold addConstGate
    rw [Gate.applyNat_seq, Gate.applyNat_seq]
    rw [prepareConstRead_yields_input_F bits c x]
    rw [prepareConstRead_at_read_idx bits c _ i hi]
    rw [h_read i hi]
    cases h_test : c.testBit i
    all_goals simp
  · intro i hi
    unfold addConstGate
    rw [Gate.applyNat_seq, Gate.applyNat_seq]
    rw [prepareConstRead_yields_input_F bits c x]
    have h_c_neq_read : ∀ j, j < bits → carry_idx i ≠ read_idx j := by
      intro j _; unfold carry_idx read_idx; omega
    rw [prepareConstRead_preserves_outside bits c _ (carry_idx i) h_c_neq_read]
    exact h_carry i hi

/-- **Bundled clean primitive** for `subConstGate`.  Follows directly
from `addConstGate_clean` with `c = 2^bits - N`. -/
theorem subConstGate_clean
    (bits N x : Nat) (hbits : 2 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.WellTyped (adder_n_qubits bits) (subConstGate bits N)
    ∧ gidney_target_val bits
        (Gate.applyNat (subConstGate bits N) (adder_input_F bits 0 x))
      = subConstPow2Spec bits N x
    ∧ (∀ i, i < bits →
        Gate.applyNat (subConstGate bits N) (adder_input_F bits 0 x) (read_idx i) = false)
    ∧ (∀ i, i < bits →
        Gate.applyNat (subConstGate bits N) (adder_input_F bits 0 x) (carry_idx i) = false) := by
  have h_c_lt : 2^bits - N < 2^bits := by
    have : 0 < 2^bits := Nat.two_pow_pos bits; omega
  unfold subConstGate
  obtain ⟨h_wt, h_target, h_read, h_carry⟩ := addConstGate_clean bits (2^bits - N) x hbits h_c_lt hx
  refine ⟨h_wt, ?_, h_read, h_carry⟩
  rw [h_target]
  rfl

/-! ### Generalized widened underflow / comparison flag for sums `s < 2*N`

After the first add-step of a modular adder, the intermediate sum
`s = x + c` may exceed `2^bits` (it satisfies `s < 2N` only, where
`N ≤ 2^bits`).  We need a generalisation of the existing widened
underflow theorem (`subConstPow2WideSpec_high_bit`) that drops the
`s < 2^bits` assumption in favour of the weaker `s < 2*N`. -/

/-- Generalized no-underflow high-bit lemma.  When `N ≤ s` and
`s < 2*N`, the widened result equals `s - N`, which fits in `bits`
bits, so bit `bits` is `false`.  Drops the `s < 2^bits` assumption
of `subConstPow2WideSpec_high_bit_of_le`. -/
theorem subConstPow2WideSpec_high_bit_bounded_sum_of_le
    (bits N s : Nat) (hN : N ≤ 2^bits) (hle : N ≤ s) (hs : s < 2 * N) :
    (subConstPow2WideSpec bits N s).testBit bits = false := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_eq : subConstPow2WideSpec bits N s = s - N := by
    unfold subConstPow2WideSpec
    have h_eq2 : s + (2^(bits + 1) - N) = (s - N) + 2^(bits + 1) := by omega
    rw [h_eq2, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h_eq]
  exact Nat.testBit_lt_two_pow (by omega)

/-- Generalized underflow high-bit lemma for `s < N` and `N ≤ 2^bits`.
Identical to `subConstPow2WideSpec_high_bit_of_lt`, restated here as a
named entry point for the post-add-step comparison flag. -/
theorem subConstPow2WideSpec_high_bit_bounded_sum_of_lt
    (bits N s : Nat) (hN : N ≤ 2^bits) (hlt : s < N) :
    (subConstPow2WideSpec bits N s).testBit bits = true :=
  subConstPow2WideSpec_high_bit_of_lt bits N s hN hlt

/-- **Generalized main high-bit theorem** for the widened subtraction
under `s < 2*N`.  After the first add-step of the modular-adder
pipeline, the intermediate sum is bounded by `2*N` (not `2^bits`),
yet the widened subtraction's high bit still equals `decide (s < N)`. -/
theorem subConstPow2WideSpec_high_bit_bounded_sum
    (bits N s : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hs : s < 2 * N) :
    (subConstPow2WideSpec bits N s).testBit bits = decide (s < N) := by
  by_cases h : s < N
  · rw [decide_eq_true h]
    exact subConstPow2WideSpec_high_bit_bounded_sum_of_lt bits N s hN h
  · rw [decide_eq_false (by omega)]
    exact subConstPow2WideSpec_high_bit_bounded_sum_of_le bits N s hN (by omega) hs

/-- **Generalized gate-level underflow flag.**  After the first
add-step of a modular adder, the intermediate sum `s` may have
`s ≥ 2^bits` but always satisfies `s < 2*N`.  The widened patched
Gidney adder's target bit at position `bits` is exactly
`decide (s < N)` under this weaker bound. -/
theorem patched_adder_sub_const_underflow_flag_bounded_sum
    (bits N s : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hs : s < 2 * N) :
    Gate.applyNat
      (gidney_adder_full_faithful_no_measurement_patched (bits + 1))
      (adder_input_F (bits + 1) (2^(bits + 1) - N) s)
      (target_idx bits)
    = decide (s < N) := by
  have h_hb : 2 ≤ bits + 1 := by omega
  have h_2pos : 0 < 2^(bits + 1) := Nat.two_pow_pos (bits + 1)
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_a : 2^(bits + 1) - N < 2^(bits + 1) := by omega
  have h_b : s < 2^(bits + 1) := by omega
  obtain ⟨_, ht, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                          (bits + 1) (2^(bits + 1) - N) s h_hb h_a h_b
  have h := ht bits (by omega)
  rw [h]
  have h_mod_eq : (((2^(bits+1) - N) + s) % 2^(bits+1)).testBit bits
                  = ((2^(bits+1) - N) + s).testBit bits := by
    rw [Nat.testBit_mod_two_pow]
    simp [show bits < bits + 1 from by omega]
  rw [← h_mod_eq]
  rw [show (((2^(bits+1) - N) + s) % 2^(bits+1))
        = subConstPow2WideSpec bits N s from by
        unfold subConstPow2WideSpec; congr 1; omega]
  exact subConstPow2WideSpec_high_bit_bounded_sum bits N s hN_pos hN hs

/-! ## Widened modular-addition arithmetic pipeline (width `bits + 1`)

To compute `(x + c) mod N` reversibly when `x, c < N ≤ 2^bits`, we
*cannot* work at width `bits` — the intermediate sum `s = x + c` may
exceed `2^bits`, losing the overflow bit.  The standard widened
pipeline operates at width `bits + 1`:

1. **add** `c`:                    `s = x + c`,  `s < 2N ≤ 2^(bits+1)`.
2. **subtract** `N`:                `y = subConstPow2WideSpec bits N s`.
   Bit `bits` of `y` is the comparison flag `decide (s < N)`.
3. **conditionally add back** `N`:  `z = (y + (if flag then N else 0)) % 2^(bits+1)`.

The arithmetic correctness is `z % 2^bits = (x + c) % N`.  This
section proves that identity at the Nat level, then begins the
gate-level chain via per-step idealized-input theorems. -/

/-! ### Deliverable A — sum bounds -/

/-- After widened add, the sum fits in `bits + 1` bits. -/
theorem modAdd_sum_bound
    (bits N x c : Nat) (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N) :
    x + c < 2^(bits + 1) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  omega

/-- After widened add, the sum is bounded by `2N` (the tighter bound
needed by the generalized underflow theorem). -/
theorem modAdd_sum_lt_twoN
    (N x c : Nat) (hx : x < N) (hc : c < N) :
    x + c < 2 * N := by omega

/-- **Widened modular-add pipeline correctness** (arithmetic level).
For `0 < N ≤ 2^bits` and `x, c < N`, the low `bits` bits of the
widened pipeline result equal `(x + c) mod N`. -/
theorem modAddConstArithmeticSpec_correct
    (bits N c x : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    modAddConstArithmeticSpec bits N c x % 2^bits = (x + c) % N := by
  unfold modAddConstArithmeticSpec
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_2pos : 0 < 2^(bits + 1) := Nat.two_pow_pos (bits + 1)
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_xc_lt_pow : x + c < 2^(bits + 1) := by omega
  by_cases h_flag : x + c < N
  · -- flag = true: subtract underflows, add-back restores `x + c`
    have h_y : subConstPow2WideSpec bits N (x + c) = (x + c) + 2^(bits+1) - N := by
      unfold subConstPow2WideSpec
      have h_lt : (x + c) + (2^(bits+1) - N) < 2^(bits+1) := by omega
      rw [Nat.mod_eq_of_lt h_lt]; omega
    rw [h_y, decide_eq_true h_flag]
    show ((x + c) + 2^(bits+1) - N + N) % 2^(bits+1) % 2^bits = (x + c) % N
    have h_eq : ((x + c) + 2^(bits+1) - N) + N = (x + c) + 2^(bits+1) := by omega
    rw [h_eq, Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (show x + c < 2^(bits+1) by omega)]
    rw [Nat.mod_eq_of_lt (show x + c < 2^bits by omega)]
    exact (Nat.mod_eq_of_lt h_flag).symm
  · -- flag = false: subtract gives `x + c - N`, add-back is zero
    have h_le : N ≤ x + c := by omega
    have h_y : subConstPow2WideSpec bits N (x + c) = (x + c) - N := by
      unfold subConstPow2WideSpec
      have h_eq2 : (x + c) + (2^(bits + 1) - N) = ((x + c) - N) + 2^(bits + 1) := by omega
      rw [h_eq2, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_y, decide_eq_false (by omega)]
    show ((x + c) - N + 0) % 2^(bits+1) % 2^bits = (x + c) % N
    rw [Nat.add_zero]
    have h_sN_lt : (x + c) - N < 2^bits := by omega
    have h_sN_lt' : (x + c) - N < 2^(bits+1) := by omega
    have h_sN_lt_N : (x + c) - N < N := by omega
    rw [Nat.mod_eq_of_lt h_sN_lt', Nat.mod_eq_of_lt h_sN_lt]
    have h_s_mod : (x + c) % N = (x + c) - N := by
      have h_split : x + c = ((x + c) - N) + N := by omega
      conv_lhs => rw [h_split]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt h_sN_lt_N]
    rw [h_s_mod]

/-! ### Deliverable C — low-bit version of the arithmetic correctness -/

/-- Bit-level form of `modAddConstArithmeticSpec_correct`: bit `i` of
the pipeline result (for `i < bits`) equals bit `i` of `(x + c) % N`. -/
theorem modAddConstArithmeticSpec_low_bit_correct
    (bits N c x i : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) (hi : i < bits) :
    (modAddConstArithmeticSpec bits N c x).testBit i
    = ((x + c) % N).testBit i := by
  have h_main : modAddConstArithmeticSpec bits N c x % 2^bits = (x + c) % N :=
    modAddConstArithmeticSpec_correct bits N c x hN_pos hN hx hc
  have h_bit : (modAddConstArithmeticSpec bits N c x % 2^bits).testBit i
              = (modAddConstArithmeticSpec bits N c x).testBit i := by
    rw [Nat.testBit_mod_two_pow]; simp [hi]
  rw [← h_bit, h_main]

/-! ### Deliverable D — per-step gate-level theorems (idealized inputs)

Each gate step in the pipeline is decoded into target-register
semantics, taking the *idealized* `adder_input_F` form as input.
Composition of these into a single gate-level theorem requires
intermediate-state preservation (the gate output of step `k` must be
extensionally equal to the `adder_input_F` form for step `k+1`),
which is the next tick's task and is NOT claimed here. -/

/-- **Step 1 — first add**.  Applied to a clean `adder_input_F (bits+1)
0 x`, `addConstGate (bits+1) c` decodes its target register to
`x + c` (no overflow, since `x + c < 2^(bits+1)`). -/
theorem modAdd_step1_target_decode
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    gidney_target_val (bits+1)
      (Gate.applyNat (addConstGate (bits+1) c) (adder_input_F (bits+1) 0 x))
    = x + c := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have hbits' : 2 ≤ bits + 1 := by omega
  have hc' : c < 2^(bits+1) := by omega
  have hx' : x < 2^(bits+1) := by omega
  obtain ⟨_, h_target, _, _⟩ := addConstGate_clean (bits+1) c x hbits' hc' hx'
  rw [h_target]
  exact Nat.mod_eq_of_lt (by omega)

/-- **Step 2 — subtract `N`, observe comparison flag at `target_idx bits`**.
Applied to an *idealized* `adder_input_F (bits+1) 0 s` (i.e., target
holds `s` and read/carry are zero), `addConstGate (bits+1) (2^(bits+1) - N)`
makes the bit at `target_idx bits` equal `decide (s < N)`. -/
theorem modAdd_step2_flag_at_target_idx_bits
    (bits N s : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hs : s < 2 * N) :
    Gate.applyNat (addConstGate (bits+1) (2^(bits+1) - N))
      (adder_input_F (bits+1) 0 s) (target_idx bits)
    = decide (s < N) := by
  unfold addConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareConstRead_yields_input_F (bits+1) (2^(bits+1)-N) s]
  have h_t_neq_read : ∀ j, j < bits+1 → target_idx bits ≠ read_idx j := by
    intro j _; unfold target_idx read_idx; omega
  rw [prepareConstRead_preserves_outside (bits+1) (2^(bits+1)-N) _
        (target_idx bits) h_t_neq_read]
  exact patched_adder_sub_const_underflow_flag_bounded_sum bits N s hbits hN_pos hN hs

/-- **Step 3 — conditional add-back**.  Applied to the idealized
`update (adder_input_F (bits+1) 0 y) flagIdx flag` (target holds `y`,
read/carry zero, flag bit at out-of-band `flagIdx`), the
`conditionalAddConstGate (bits+1) N flagIdx` decodes target to
`(y + (if flag then N else 0)) mod 2^(bits+1)` — which is exactly the
`modAddConstArithmeticSpec` value when `y = subConstPow2WideSpec bits N s`
and `flag = decide (s < N)`. -/
theorem modAdd_step3_target_decode
    (bits N flagIdx y : Nat) (flag : Bool)
    (hbits : 1 ≤ bits) (hN : N < 2^(bits+1)) (hy : y < 2^(bits+1))
    (hflagIdx : adder_n_qubits (bits+1) ≤ flagIdx) :
    gidney_target_val (bits+1)
      (Gate.applyNat (conditionalAddConstGate (bits+1) N flagIdx)
        (update (adder_input_F (bits+1) 0 y) flagIdx flag))
    = (y + (if flag then N else 0)) % 2^(bits+1) := by
  have hbits' : 2 ≤ bits + 1 := by omega
  exact conditionalAddConstGate_target_decode (bits+1) N flagIdx y flag hbits' hN hy hflagIdx

/-! ## State-normalization for composing the full modular-add gate

The per-step theorems above take *idealised* `adder_input_F` inputs.
For full gate-level composition, we need per-bit / per-position
"normal-form" facts about the output of each step, plus a flag-copy
gate that promotes the comparison flag from the in-band
`target_idx bits` to an out-of-band `flagIdx`.

This section delivers:
* per-bit target correctness for `addConstGate` (Deliverable A);
* weak normal-form (working positions only) for step 1
  (Deliverable B);
* weak normal-form (working positions + flag bit) for step 2
  (Deliverable C);
* flag-copy gate + correctness + frame + WellTyped (Deliverable D).

Full gate-level chain composition (Deliverable E) is *blocked* by the
need to prove the patched Gidney adder is `WellTyped` at the tight
dimension `3 * n` (or equivalent: that the cascade preserves the gap
positions `read_idx n` and `target_idx n` for an `n`-bit adder).  The
existing WellTyped is at `adder_n_qubits n = 3*n + 2`, two positions
too loose to bridge intermediate gate states; see the closing comments
of this section for the precise blocker statement. -/

/-! ### Deliverable A — per-bit target correctness for `addConstGate` -/

/-- Bit-level form of `addConstGate_clean`'s target-decode line:
applied to `adder_input_F bits 0 x`, the gate's value at `target_idx i`
(for `i < bits`) equals bit `i` of `(x + c) % 2^bits`. -/
theorem addConstGate_target_bit
    (bits c x i : Nat) (hbits : 2 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits)
    (hi : i < bits) :
    Gate.applyNat (addConstGate bits c) (adder_input_F bits 0 x) (target_idx i)
    = ((x + c) % 2^bits).testBit i := by
  unfold addConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareConstRead_yields_input_F bits c x]
  have h_t_neq_read : ∀ j, j < bits → target_idx i ≠ read_idx j := by
    intro j _; unfold target_idx read_idx; omega
  rw [prepareConstRead_preserves_outside bits c _ (target_idx i) h_t_neq_read]
  obtain ⟨_, h_target, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                              bits c x hbits hc hx
  rw [h_target i hi]
  rw [Nat.add_comm c x]
  rw [Nat.testBit_mod_two_pow]; simp [hi]

/-- No-overflow corollary for widened addition.  When `x, c < N ≤ 2^bits`,
the widened sum `x + c` fits in `bits + 1` bits, so bit `i` of the
target is `(x + c).testBit i` (no mod needed). -/
theorem addConstGate_target_bit_no_overflow
    (bits N c x i : Nat) (hbits : 1 ≤ bits) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) (hi : i < bits + 1) :
    Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x) (target_idx i)
    = (x + c).testBit i := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_2N_le : 2 * N ≤ 2 * 2^bits := by omega
  have h_xc_lt : x + c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_c_lt : c < 2^(bits+1) := by
    have : c < 2^bits := by omega
    rw [h_pow_succ]; omega
  have h_x_lt : x < 2^(bits+1) := by
    have : x < 2^bits := by omega
    rw [h_pow_succ]; omega
  rw [addConstGate_target_bit (bits+1) c x i hbits' h_c_lt h_x_lt hi]
  rw [Nat.mod_eq_of_lt h_xc_lt]

/-! ### Deliverable B — weak normal-form for step 1 (`addConstGate`)

Working-position state characterization for `addConstGate (bits + 1) c`
applied to a clean `adder_input_F (bits + 1) 0 x`. -/

/-- After step 1, the read register is zero, carries are cleared, and
target bits 0..bits encode `(x + c)` (no overflow under `x, c < N`).
This is the WEAK normal-form: it does NOT claim function equality at
positions outside the working range. -/
theorem addConstGate_modAdd_step1_state_normal
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    (∀ i, i < bits + 1 →
      Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x) (target_idx i)
      = (x + c).testBit i)
    ∧ (∀ i, i < bits + 1 →
      Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x) (read_idx i)
      = false)
    ∧ (∀ i, i < bits + 1 →
      Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x) (carry_idx i)
      = false) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have h_c_lt : c < 2^(bits+1) := by
    have : c < 2^bits := by omega
    rw [h_pow_succ]; omega
  have h_x_lt : x < 2^(bits+1) := by
    have : x < 2^bits := by omega
    rw [h_pow_succ]; omega
  obtain ⟨_, _, h_read, h_carry⟩ := addConstGate_clean (bits+1) c x hbits' h_c_lt h_x_lt
  refine ⟨?_, h_read, h_carry⟩
  intro i hi
  exact addConstGate_target_bit_no_overflow bits N c x i hbits hN hx hc hi

/-! ### Deliverable C — weak normal-form for step 2 (`subConstGate`)

Applied to a clean `adder_input_F (bits + 1) 0 s` (idealised input —
NOT the actual post-step-1 state, but the structurally-clean version),
`subConstGate (bits + 1) N` writes the widened-subtraction bits and
places the comparison flag at `target_idx bits`. -/

/-- Weak normal-form for step 2.  Same caveat as step 1: working
positions only. -/
theorem subConstGate_modAdd_step2_state_normal
    (bits N s : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hs : s < 2 * N) :
    (∀ i, i < bits + 1 →
      Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s) (target_idx i)
      = (subConstPow2WideSpec bits N s).testBit i)
    ∧ Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s) (target_idx bits)
      = decide (s < N)
    ∧ (∀ i, i < bits + 1 →
      Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s) (read_idx i)
      = false)
    ∧ (∀ i, i < bits + 1 →
      Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s) (carry_idx i)
      = false) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have h_s_lt : s < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_c : 2^(bits+1) - N < 2^(bits+1) := by
    have h_pow_pos2 : 0 < 2^(bits+1) := by rw [h_pow_succ]; omega
    omega
  unfold subConstGate
  obtain ⟨_, _, h_read, h_carry⟩ :=
    addConstGate_clean (bits+1) (2^(bits+1) - N) s hbits' h_c h_s_lt
  have h_target_bit : ∀ i, i < bits + 1 →
      Gate.applyNat (addConstGate (bits + 1) (2^(bits+1) - N)) (adder_input_F (bits + 1) 0 s)
        (target_idx i) = (subConstPow2WideSpec bits N s).testBit i := by
    intro i hi
    rw [addConstGate_target_bit (bits+1) (2^(bits+1) - N) s i hbits' h_c h_s_lt hi]
    rfl
  have h_flag :
      Gate.applyNat (addConstGate (bits + 1) (2^(bits+1) - N)) (adder_input_F (bits + 1) 0 s)
        (target_idx bits) = decide (s < N) := by
    rw [h_target_bit bits (by omega)]
    exact subConstPow2WideSpec_high_bit_bounded_sum bits N s hN_pos hN hs
  exact ⟨h_target_bit, h_flag, h_read, h_carry⟩

/-- Correctness: when the flag bit is initially `false`, the gate
sets it to the value of `target_idx bits`. -/
theorem copyTargetHighBitToFlag_correct
    (bits flagIdx : Nat) (f : Nat → Bool) (h_init : f flagIdx = false) :
    Gate.applyNat (copyTargetHighBitToFlag bits flagIdx) f flagIdx
    = f (target_idx bits) := by
  unfold copyTargetHighBitToFlag
  simp only [Gate.applyNat_CX]
  rw [update_eq, h_init]
  simp

/-- Frame: when `flagIdx` is out-of-band (`flagIdx ≥ adder_n_qubits (bits+1)`),
the flag-copy gate preserves all positions strictly inside the
working dimension. -/
theorem copyTargetHighBitToFlag_preserves_working
    (bits flagIdx : Nat) (f : Nat → Bool) (p : Nat)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx)
    (h_p_lt : p < adder_n_qubits (bits + 1)) :
    Gate.applyNat (copyTargetHighBitToFlag bits flagIdx) f p = f p := by
  unfold copyTargetHighBitToFlag
  simp only [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ (by unfold adder_n_qubits at *; omega : p ≠ flagIdx)]

/-- WellTyped at the enlarged dimension `flagIdx + 1`. -/
theorem copyTargetHighBitToFlag_wellTyped
    (bits flagIdx : Nat)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    Gate.WellTyped (flagIdx + 1) (copyTargetHighBitToFlag bits flagIdx) := by
  unfold copyTargetHighBitToFlag
  unfold adder_n_qubits target_idx at *
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ### Deliverable E — STATUS

Composing `addConstGate (bits+1) c → subConstGate (bits+1) N →
copyTargetHighBitToFlag bits flagIdx → conditionalAddConstGate (bits+1) N flagIdx`
into a single `modAddConstGate_dirtyFlag` gate, with the target-decode
theorem `gidney_target_val bits (...) = (x + c) % N`, is BLOCKED on
the following gate-level intermediate-state preservation gap.

**Specific blocker.**  To chain the per-step theorems via the
existing primitive infrastructure, we need the state after step 1 to
be *extensionally equal* to `adder_input_F (bits+1) 0 (x+c)` (so that
the step-2 primitive `subConstGate_clean` / `addConstGate_target_bit`
can be applied).  The WEAK normal-form (Deliverable B) gives equality
at the working positions `read_idx i, target_idx i, carry_idx i` for
`i < bits + 1` — these are positions `0..3*bits + 2`.  But the
ambient dimension `adder_n_qubits (bits + 1) = 3*bits + 5` includes
two *gap* positions `read_idx (bits + 1) = 3*bits + 3` and
`target_idx (bits + 1) = 3*bits + 4` that are touched by neither the
prep cascade nor the (`bits + 1`)-wide patched Gidney adder cascade
(whose maximum touched position is `carry_idx bits = 3*bits + 2`),
but for which we lack a Lean frame lemma.

To close this gap, the next tick needs ONE of:
(a) a frame lemma showing the patched Gidney adder of width `n`
    preserves positions `≥ 3 * n` (which would give the strong
    normal-form `Gate.applyNat (addConstGate (bits+1) c) (adder_input_F
    (bits+1) 0 x) = adder_input_F (bits+1) 0 (x + c)` extensionally);
(b) a re-proof of the patched adder's `WellTyped` at the tight
    dimension `3 * n` (which would yield the same frame via the
    existing `applyNat_commute_update_above_dim`);
(c) a `Gate.applyNat` congruence lemma at a custom dimension matching
    the cascade's actual max-touched position, plus a per-gate
    "doesn't-touch" infrastructure.

The weak normal-forms (Deliverables B and C) together with
`conditionalAddConstGate_clean` are SUFFICIENT to prove Deliverable
E's headline once any of (a)/(b)/(c) closes; the proof skeleton is
the chain `addConstGate_modAdd_step1_state_normal →
(intermediate-state bridge) → subConstGate_modAdd_step2_state_normal →
(intermediate-state bridge) → copyTargetHighBitToFlag_correct →
(intermediate-state bridge) → modAdd_step3_target_decode →
modAddConstArithmeticSpec_low_bit_correct`.

The dirty-flag composite gate is NOT defined or proved in this
commit, to avoid making any unproven claim. -/

/-! ## Tick 1 — Gap-position frame lemmas and strengthened normalization

This section closes the gap blocker by proving:

* Per-step frame lemmas: `bit_step_*_preserves_above` for the first /
  interior / last / *_reverse / *_reverse_patched gates, each with a
  tight position bound derived from the bit index.
* Cascade frame lemmas: `forward_with_propagation`,
  `forward_faithful_full`, `forward_with_propagation_reverse_patched`,
  `forward_faithful_full_reverse_patched`, `final_cx_cascade` — each
  preserves positions above its actual support.
* Full patched-adder frame: positions `≥ 3 * w` preserved.
* `prepareConstRead`, `addConstGate`, `subConstGate` frame lemmas with
  the uniform bound `3 * bits ≤ p`.
* **Strengthened state normalization** lifting the weak normal-form
  theorems to full extensional `Gate.applyNat ... = adder_input_F ...`
  equalities.

These frame lemmas close the gap-position blocker identified in the
previous section. -/

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
