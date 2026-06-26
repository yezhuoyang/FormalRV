/- PowerOfTwoCase — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.RippleCarryAdder
import Mathlib.Data.Nat.Bitwise
import FormalRV.Arithmetic.ModularAdder.Gidney.Def

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


end FormalRV.BQAlgo
