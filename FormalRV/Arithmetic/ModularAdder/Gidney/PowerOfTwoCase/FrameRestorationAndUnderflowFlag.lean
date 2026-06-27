/- PowerOfTwoCase — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModularAdder.Gidney.PowerOfTwoCase.PowerOfTwoAdderAndSplitCases

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

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


end FormalRV.BQAlgo
