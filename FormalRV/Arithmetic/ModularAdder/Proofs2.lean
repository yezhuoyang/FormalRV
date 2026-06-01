import FormalRV.Arithmetic.RippleCarryAdder
import Mathlib.Data.Nat.Bitwise
import FormalRV.Arithmetic.ModularAdder.Defs
import FormalRV.Arithmetic.ModularAdder.Proofs1

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-- `forward_faithful_full w` preserves positions `≥ 3 * w`. -/
theorem gidney_adder_forward_faithful_full_preserves_above
    (w : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * w ≤ p) :
    Gate.applyNat (gidney_adder_forward_faithful_full w) f p = f p := by
  match w with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
      show Gate.applyNat (Gate.seq (gidney_adder_forward_with_propagation (n+1))
                                   (gidney_adder_bit_step_faithful_last (n+1))) f p = f p
      rw [Gate.applyNat_seq]
      rw [gidney_adder_bit_step_faithful_last_preserves_above (n+1) _ p (by omega)]
      exact gidney_adder_forward_with_propagation_preserves_above (n+1) f p (by omega)

/-- `forward_faithful_full_reverse_patched w` preserves positions `≥ 3 * w`. -/
theorem gidney_adder_forward_faithful_full_reverse_patched_preserves_above
    (w : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * w ≤ p) :
    Gate.applyNat (gidney_adder_forward_faithful_full_reverse_patched w) f p = f p := by
  match w with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
      show Gate.applyNat (Gate.seq (gidney_adder_bit_step_faithful_last_reverse_patched (n+1))
                                   (gidney_adder_forward_with_propagation_reverse_patched (n+1)))
              f p = f p
      rw [Gate.applyNat_seq]
      rw [gidney_adder_forward_with_propagation_reverse_patched_preserves_above
            (n+1) _ p (by omega)]
      exact gidney_adder_bit_step_faithful_last_reverse_patched_preserves_above
              (n+1) f p (by omega)

/-- `final_cx_cascade w` preserves positions `≥ 3 * w`. -/
theorem gidney_final_cx_cascade_preserves_above
    (w : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * w ≤ p) :
    Gate.applyNat (gidney_final_cx_cascade w) f p = f p := by
  induction w generalizing f with
  | zero => rfl
  | succ k ih =>
      show Gate.applyNat (Gate.seq (gidney_final_cx_cascade k)
                                   (Gate.CX (read_idx k) (target_idx k))) f p = f p
      have h_p_rk : p ≠ read_idx k := by unfold read_idx; omega
      have h_p_tk : p ≠ target_idx k := by unfold target_idx; omega
      rw [Gate.applyNat_seq, Gate.applyNat_CX]
      rw [update_neq _ _ _ _ h_p_tk]
      exact ih _ (by omega)

/-! ### Full patched adder frame -/

/-- **Headline frame lemma**: the full patched Gidney adder of width
`w` preserves positions `p ≥ 3 * w`.  This is the tight bound: the
cascade touches positions up to `carry_idx (w-1) = 3w - 1` for `w ≥ 2`. -/
theorem gidney_adder_full_faithful_no_measurement_patched_preserves_above
    (w : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * w ≤ p) :
    Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched w) f p = f p := by
  match w with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
      show Gate.applyNat (Gate.seq
              (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                        (gidney_final_cx_cascade (n + 2)))
              (gidney_adder_forward_faithful_full_reverse_patched (n + 2))) f p = f p
      rw [Gate.applyNat_seq, Gate.applyNat_seq]
      rw [gidney_adder_forward_faithful_full_reverse_patched_preserves_above (n+2) _ p hp]
      rw [gidney_final_cx_cascade_preserves_above (n+2) _ p hp]
      exact gidney_adder_forward_faithful_full_preserves_above (n+2) f p hp

/-! ### `prepareConstRead`, `addConstGate`, `subConstGate` frames -/

/-- `prepareConstRead bits c` preserves positions `≥ 3 * bits`. -/
theorem prepareConstRead_preserves_above
    (bits c : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * bits ≤ p) :
    Gate.applyNat (prepareConstRead bits c) f p = f p := by
  apply prepareConstRead_preserves_outside
  intro i hi; unfold read_idx; omega

/-- **Composable frame**: `addConstGate bits c` preserves positions `≥ 3 * bits`. -/
theorem addConstGate_preserves_above_actual
    (bits c : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * bits ≤ p) :
    Gate.applyNat (addConstGate bits c) f p = f p := by
  unfold addConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareConstRead_preserves_above bits c _ p hp]
  rw [gidney_adder_full_faithful_no_measurement_patched_preserves_above bits _ p hp]
  exact prepareConstRead_preserves_above bits c f p hp

/-- **Composable frame**: `subConstGate bits N` preserves positions `≥ 3 * bits`. -/
theorem subConstGate_preserves_above_actual
    (bits N : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * bits ≤ p) :
    Gate.applyNat (subConstGate bits N) f p = f p :=
  addConstGate_preserves_above_actual bits (2^bits - N) f p hp

/-! ### Gap-position corollaries

For `width = bits + 1`, the two gap positions `read_idx (bits + 1)` and
`target_idx (bits + 1)` are at `3 * (bits + 1)` and `3 * (bits + 1) + 1`
respectively — both `≥ 3 * (bits + 1)`, so both preserved. -/

theorem addConstGate_preserves_gap_read
    (bits c : Nat) (f : Nat → Bool) :
    Gate.applyNat (addConstGate (bits + 1) c) f (read_idx (bits + 1))
      = f (read_idx (bits + 1)) := by
  apply addConstGate_preserves_above_actual
  unfold read_idx; omega

theorem addConstGate_preserves_gap_target
    (bits c : Nat) (f : Nat → Bool) :
    Gate.applyNat (addConstGate (bits + 1) c) f (target_idx (bits + 1))
      = f (target_idx (bits + 1)) := by
  apply addConstGate_preserves_above_actual
  unfold target_idx; omega

theorem subConstGate_preserves_gap_read
    (bits N : Nat) (f : Nat → Bool) :
    Gate.applyNat (subConstGate (bits + 1) N) f (read_idx (bits + 1))
      = f (read_idx (bits + 1)) := by
  apply subConstGate_preserves_above_actual
  unfold read_idx; omega

theorem subConstGate_preserves_gap_target
    (bits N : Nat) (f : Nat → Bool) :
    Gate.applyNat (subConstGate (bits + 1) N) f (target_idx (bits + 1))
      = f (target_idx (bits + 1)) := by
  apply subConstGate_preserves_above_actual
  unfold target_idx; omega

/-! ### Strengthened state normalization (Tick 1 Deliverable C)

With the gap-position frame closed, the per-position state assertions
now extend to FULL extensional equality between the post-gate state
and the canonical `adder_input_F` form of the new value.  This is the
strong normal-form required to chain into the next gate. -/

/-- **Strong normal-form for step 1**: `addConstGate (bits + 1) c`
applied to the clean input `adder_input_F (bits + 1) 0 x` produces a
function extensionally equal to `adder_input_F (bits + 1) 0 (x + c)`.
This supersedes the WEAK `_state_normal` form above. -/
theorem addConstGate_modAdd_step1_state_eq
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x)
    = adder_input_F (bits + 1) 0 (x + c) := by
  funext p
  by_cases hp_high : 3 * (bits + 1) ≤ p
  · rw [addConstGate_preserves_above_actual (bits + 1) c _ p hp_high]
    unfold adder_input_F
    rcases h_mod : p % 3 with _ | _ | _
    · simp [Nat.zero_testBit]
    · have h_div_ge : p / 3 ≥ bits + 1 := by omega
      simp [show ¬ (p / 3 < bits + 1) from by omega]
    · rfl
  · push_neg at hp_high
    obtain ⟨h_target, h_read, h_carry⟩ :=
      addConstGate_modAdd_step1_state_normal bits N c x hbits hN hx hc
    have h_p_div_lt : p / 3 < bits + 1 := by omega
    rcases h_mod : p % 3 with _ | _ | _
    · have h_p_eq : p = read_idx (p / 3) := by unfold read_idx; omega
      rw [h_p_eq, h_read (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (read_idx (p/3)) % 3 = 0 from by unfold read_idx; omega,
          show (read_idx (p/3)) / 3 = p/3 from by unfold read_idx; omega]
      simp [Nat.zero_testBit]
    · have h_p_eq : p = target_idx (p / 3) := by unfold target_idx; omega
      rw [h_p_eq, h_target (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (target_idx (p/3)) % 3 = 1 from by unfold target_idx; omega,
          show (target_idx (p/3)) / 3 = p/3 from by unfold target_idx; omega]
      simp [h_p_div_lt]
    · have h_p_eq : p = carry_idx (p / 3) := by unfold carry_idx; omega
      rw [h_p_eq, h_carry (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (carry_idx (p/3)) % 3 = 2 from by unfold carry_idx; omega]

/-- **Strong normal-form for step 2**: `subConstGate (bits + 1) N`
applied to the clean input `adder_input_F (bits + 1) 0 s` produces a
function extensionally equal to `adder_input_F (bits + 1) 0 y` where
`y := subConstPow2WideSpec bits N s`. -/
theorem subConstGate_modAdd_step2_state_eq
    (bits N s : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hs : s < 2 * N) :
    Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s)
    = adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N s) := by
  funext p
  by_cases hp_high : 3 * (bits + 1) ≤ p
  · rw [subConstGate_preserves_above_actual (bits + 1) N _ p hp_high]
    unfold adder_input_F
    rcases h_mod : p % 3 with _ | _ | _
    · simp [Nat.zero_testBit]
    · have h_div_ge : p / 3 ≥ bits + 1 := by omega
      simp [show ¬ (p / 3 < bits + 1) from by omega]
    · rfl
  · push_neg at hp_high
    obtain ⟨h_target, _, h_read, h_carry⟩ :=
      subConstGate_modAdd_step2_state_normal bits N s hbits hN_pos hN hs
    have h_p_div_lt : p / 3 < bits + 1 := by omega
    rcases h_mod : p % 3 with _ | _ | _
    · have h_p_eq : p = read_idx (p / 3) := by unfold read_idx; omega
      rw [h_p_eq, h_read (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (read_idx (p/3)) % 3 = 0 from by unfold read_idx; omega,
          show (read_idx (p/3)) / 3 = p/3 from by unfold read_idx; omega]
      simp [Nat.zero_testBit]
    · have h_p_eq : p = target_idx (p / 3) := by unfold target_idx; omega
      rw [h_p_eq, h_target (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (target_idx (p/3)) % 3 = 1 from by unfold target_idx; omega,
          show (target_idx (p/3)) / 3 = p/3 from by unfold target_idx; omega]
      simp [h_p_div_lt]
    · have h_p_eq : p = carry_idx (p / 3) := by unfold carry_idx; omega
      rw [h_p_eq, h_carry (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (carry_idx (p/3)) % 3 = 2 from by unfold carry_idx; omega]

/-! ## Tick 2 — Dirty-flag modular add-constant target theorem

With the strong normal-forms `addConstGate_modAdd_step1_state_eq` and
`subConstGate_modAdd_step2_state_eq` in hand, we can now chain the
four-step pipeline and prove decoded target correctness.

Pipeline: `addConstGate (bits+1) c  ;  subConstGate (bits+1) N  ;
copyTargetHighBitToFlag bits flagIdx  ;  conditionalAddConstGate (bits+1) N flagIdx`.

The OUT-OF-BAND flag bit at `flagIdx` is left DIRTY at the value
`decide ((x + c) < N)` — flag uncomputation is the next tick's task. -/

/-- Helper: `adder_input_F w a b` is `false` at any position `≥ 3 * w`
(all working positions are below `3 * w`, and out-of-range bits of `a`
and `b` are zero by the `decide(k/3 < w)` guard). -/
theorem adder_input_F_at_high
    (w a b k : Nat) (hk : 3 * w ≤ k) :
    adder_input_F w a b k = false := by
  unfold adder_input_F
  rcases h_mod : k % 3 with _ | _ | _
  · have h_div_ge : k / 3 ≥ w := by omega
    simp [show ¬(k/3 < w) from by omega]
  · have h_div_ge : k / 3 ≥ w := by omega
    simp [show ¬(k/3 < w) from by omega]
  · rfl

/-- Bit-level conditional add-back: applied to an
`update (adder_input_F bits 0 y) flagIdx flag` input (target holds `y`,
read/carry zero, flag at `flagIdx ≥ adder_n_qubits bits`), the gate
writes `(y + (if flag then N else 0)).testBit i` at `target_idx i`
for `i < bits`. -/
theorem conditionalAddConstGate_target_bit
    (bits N flagIdx y i : Nat) (flag : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hy : y < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) (hi : i < bits) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx)
      (update (adder_input_F bits 0 y) flagIdx flag) (target_idx i)
    = (y + (if flag then N else 0)).testBit i := by
  have h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j := by
    intro j hj
    unfold adder_n_qubits read_idx at *
    omega
  have h_c_lt : (if flag then N else 0) < 2^bits := by
    cases flag with
    | true => exact hN
    | false => exact Nat.two_pow_pos bits
  unfold conditionalAddConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareMaskedConstRead_yields_input_F bits N flagIdx y flag h_disj]
  have h_wt : Gate.WellTyped (adder_n_qubits bits)
              (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  rw [applyNat_commute_update_above_dim (adder_n_qubits bits) _ h_wt _ _ _ hflagIdx]
  have h_t_neq_read : ∀ j, j < bits → target_idx i ≠ read_idx j := by
    intro j _; unfold target_idx read_idx; omega
  rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ (target_idx i) h_t_neq_read]
  have h_target_ne_flag : target_idx i ≠ flagIdx := by
    intro h_eq
    have h_flag_eq : flagIdx = target_idx i := h_eq.symm
    unfold adder_n_qubits target_idx at *
    omega
  rw [update_neq _ _ _ _ h_target_ne_flag]
  obtain ⟨_, h_target, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                              bits (if flag then N else 0) y hbits h_c_lt hy
  rw [h_target i hi, Nat.add_comm]

/-- **Tick 2 HEADLINE**: the dirty-flag modular add-constant gate
decodes its target register (low `bits` bits) to `(x + c) mod N`. -/
theorem modAddConstGate_dirtyFlag_target_decode
    (bits N c x flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    gidney_target_val bits
      (Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
        (adder_input_F (bits + 1) 0 x))
    = (x + c) % N := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_xc_lt_pow : x + c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hbits' : 2 ≤ bits + 1 := by omega
  have hN_lt : N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_y_lt : subConstPow2WideSpec bits N (x + c) < 2^(bits+1) := by
    unfold subConstPow2WideSpec
    have : 0 < 2^(bits+1) := Nat.two_pow_pos _
    exact Nat.mod_lt _ this
  have h_y_high_bit :
      (subConstPow2WideSpec bits N (x + c)).testBit bits = decide ((x + c) < N) :=
    subConstPow2WideSpec_high_bit_bounded_sum bits N (x+c) hN_pos hN h_xc_lt_2N
  have h_input_at_flag :
      adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)) flagIdx = false := by
    apply adder_input_F_at_high
    unfold adder_n_qubits at hflagIdx; omega
  have h_input_at_tbits :
      adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)) (target_idx bits)
      = (subConstPow2WideSpec bits N (x + c)).testBit bits := by
    unfold adder_input_F
    have h_mod : (target_idx bits) % 3 = 1 := by unfold target_idx; omega
    have h_div : (target_idx bits) / 3 = bits := by unfold target_idx; omega
    rw [h_mod, h_div]
    simp [show bits < bits + 1 from by omega]
  have h_xcN_mod : (x + c) % N % 2^bits = (x + c) % N := by
    have : (x + c) % N < N := Nat.mod_lt _ hN_pos
    exact Nat.mod_eq_of_lt (by omega)
  unfold modAddConstGate_dirtyFlag
  rw [Gate.applyNat_seq, Gate.applyNat_seq, Gate.applyNat_seq]
  rw [addConstGate_modAdd_step1_state_eq bits N c x hbits hN hx hc]
  rw [subConstGate_modAdd_step2_state_eq bits N (x+c) hbits hN_pos hN h_xc_lt_2N]
  show gidney_target_val bits
    (Gate.applyNat (conditionalAddConstGate (bits + 1) N flagIdx)
      (Gate.applyNat (copyTargetHighBitToFlag bits flagIdx)
        (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c))))) = (x + c) % N
  unfold copyTargetHighBitToFlag
  rw [Gate.applyNat_CX]
  rw [h_input_at_flag, h_input_at_tbits, h_y_high_bit, Bool.false_xor]
  rw [← h_xcN_mod]
  apply gidney_target_val_eq_sum_when_bits_match bits ((x + c) % N)
  intro i hi
  rw [conditionalAddConstGate_target_bit (bits + 1) N flagIdx
        (subConstPow2WideSpec bits N (x + c)) i (decide ((x + c) < N))
        hbits' hN_lt h_y_lt hflagIdx (by omega)]
  have h_bridge :
      (subConstPow2WideSpec bits N (x + c) +
        (if (decide ((x + c) < N) = true) then N else 0)).testBit i
      = (modAddConstArithmeticSpec bits N c x).testBit i := by
    unfold modAddConstArithmeticSpec
    rw [Nat.testBit_mod_two_pow]
    simp [show i < bits + 1 from by omega]
  rw [h_bridge]
  exact modAddConstArithmeticSpec_low_bit_correct bits N c x i hN_pos hN hx hc hi

/-! ## Tick 3 — Dirty-flag workspace theorem

Prove workspace properties for `modAddConstGate_dirtyFlag`: WellTyped,
read register restored to zero, carry register cleared, and flag bit
exactly `decide ((x + c) < N)`.  Flag-bit restoration is NOT claimed
here; that is the next tick's task. -/

/-- Intermediate: the state after the first three steps (add ; sub ;
copy-flag) of `modAddConstGate_dirtyFlag` is extensionally equal to
`update (adder_input_F (bits+1) 0 y) flagIdx (decide ((x+c)<N))`,
where `y := subConstPow2WideSpec bits N (x+c)`. -/
theorem modAddConstGate_dirtyFlag_after_three_steps_eq
    (bits N c x flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
      (Gate.seq (subConstGate (bits + 1) N)
        (copyTargetHighBitToFlag bits flagIdx)))
      (adder_input_F (bits + 1) 0 x)
    = update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c))) flagIdx
        (decide ((x + c) < N)) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_y_high_bit :
      (subConstPow2WideSpec bits N (x + c)).testBit bits = decide ((x + c) < N) :=
    subConstPow2WideSpec_high_bit_bounded_sum bits N (x+c) hN_pos hN h_xc_lt_2N
  have h_input_at_flag :
      adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)) flagIdx = false := by
    apply adder_input_F_at_high
    unfold adder_n_qubits at hflagIdx; omega
  have h_input_at_tbits :
      adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)) (target_idx bits)
      = (subConstPow2WideSpec bits N (x + c)).testBit bits := by
    unfold adder_input_F
    have h_mod : (target_idx bits) % 3 = 1 := by unfold target_idx; omega
    have h_div : (target_idx bits) / 3 = bits := by unfold target_idx; omega
    rw [h_mod, h_div]
    simp [show bits < bits + 1 from by omega]
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [addConstGate_modAdd_step1_state_eq bits N c x hbits hN hx hc]
  rw [subConstGate_modAdd_step2_state_eq bits N (x+c) hbits hN_pos hN h_xc_lt_2N]
  unfold copyTargetHighBitToFlag
  rw [Gate.applyNat_CX]
  rw [h_input_at_flag, h_input_at_tbits, h_y_high_bit, Bool.false_xor]

/-- **Tick 3 HEADLINE — dirty-flag workspace theorem**.  The
`modAddConstGate_dirtyFlag` is WellTyped at the enlarged dimension
`flagIdx + 1`, restores the read register to zero, clears the carry
register, and places the comparison flag `decide ((x + c) < N)` at
`flagIdx`.  The flag bit is DIRTY — not restored to false. -/
theorem modAddConstGate_dirtyFlag_workspace
    (bits N c x flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    Gate.WellTyped (flagIdx + 1) (modAddConstGate_dirtyFlag bits N c flagIdx)
    ∧ (∀ i, i < bits + 1 →
        Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
          (adder_input_F (bits + 1) 0 x) (read_idx i) = false)
    ∧ (∀ i, i < bits + 1 →
        Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
          (adder_input_F (bits + 1) 0 x) (carry_idx i) = false)
    ∧ Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
        (adder_input_F (bits + 1) 0 x) flagIdx = decide ((x + c) < N) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have hbits' : 2 ≤ bits + 1 := by omega
  have hN_lt : N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hN_le_succ : N ≤ 2^(bits+1) := by omega
  have h_y_lt : subConstPow2WideSpec bits N (x + c) < 2^(bits+1) := by
    unfold subConstPow2WideSpec
    have : 0 < 2^(bits+1) := Nat.two_pow_pos _
    exact Nat.mod_lt _ this
  have h_c_lt : c < 2^(bits+1) := by
    have : c < 2^bits := by omega
    rw [h_pow_succ]; omega
  have h_x_lt : x < 2^(bits+1) := by
    have : x < 2^bits := by omega
    rw [h_pow_succ]; omega
  have h_flag_succ : adder_n_qubits (bits + 1) ≤ flagIdx + 1 := by omega
  have h_3 := modAddConstGate_dirtyFlag_after_three_steps_eq
                bits N c x flagIdx hbits hN_pos hN hx hc hflagIdx
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- WellTyped at flagIdx + 1
    unfold modAddConstGate_dirtyFlag
    obtain ⟨h_add_wt, _, _, _⟩ := addConstGate_clean (bits+1) c x hbits' h_c_lt h_x_lt
    have h_add_wt' : Gate.WellTyped (flagIdx + 1) (addConstGate (bits + 1) c) :=
      Gate.WellTyped.mono h_add_wt h_flag_succ
    obtain ⟨h_sub_wt, _, _, _⟩ := subConstGate_clean (bits+1) N x hbits' hN_pos hN_le_succ h_x_lt
    have h_sub_wt' : Gate.WellTyped (flagIdx + 1) (subConstGate (bits + 1) N) :=
      Gate.WellTyped.mono h_sub_wt h_flag_succ
    have h_copy_wt : Gate.WellTyped (flagIdx + 1) (copyTargetHighBitToFlag bits flagIdx) :=
      copyTargetHighBitToFlag_wellTyped bits flagIdx hflagIdx
    have h_cond_wt : Gate.WellTyped (flagIdx + 1) (conditionalAddConstGate (bits+1) N flagIdx) :=
      conditionalAddConstGate_wellTyped (bits+1) N flagIdx hbits' hflagIdx
    exact ⟨h_add_wt', h_sub_wt', h_copy_wt, h_cond_wt⟩
  · -- read register restored
    intro i hi
    show Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
          (adder_input_F (bits + 1) 0 x) (read_idx i) = false
    unfold modAddConstGate_dirtyFlag
    rw [show Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
            (Gate.seq (subConstGate (bits + 1) N)
              (Gate.seq (copyTargetHighBitToFlag bits flagIdx)
                (conditionalAddConstGate (bits + 1) N flagIdx))))
            (adder_input_F (bits + 1) 0 x)
          = Gate.applyNat (conditionalAddConstGate (bits + 1) N flagIdx)
              (Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
                  (Gate.seq (subConstGate (bits + 1) N)
                    (copyTargetHighBitToFlag bits flagIdx)))
                (adder_input_F (bits + 1) 0 x)) from rfl]
    rw [h_3]
    exact conditionalAddConstGate_read_restored (bits+1) N
            (subConstPow2WideSpec bits N (x+c)) flagIdx (decide ((x+c)<N))
            hbits' hN_lt h_y_lt hflagIdx i hi
  · -- carry register cleared
    intro i hi
    show Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
          (adder_input_F (bits + 1) 0 x) (carry_idx i) = false
    unfold modAddConstGate_dirtyFlag
    rw [show Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
            (Gate.seq (subConstGate (bits + 1) N)
              (Gate.seq (copyTargetHighBitToFlag bits flagIdx)
                (conditionalAddConstGate (bits + 1) N flagIdx))))
            (adder_input_F (bits + 1) 0 x)
          = Gate.applyNat (conditionalAddConstGate (bits + 1) N flagIdx)
              (Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
                  (Gate.seq (subConstGate (bits + 1) N)
                    (copyTargetHighBitToFlag bits flagIdx)))
                (adder_input_F (bits + 1) 0 x)) from rfl]
    rw [h_3]
    exact conditionalAddConstGate_carries_cleared (bits+1) N
            (subConstPow2WideSpec bits N (x+c)) flagIdx (decide ((x+c)<N))
            hbits' hN_lt h_y_lt hflagIdx i hi
  · -- flag bit value
    show Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
          (adder_input_F (bits + 1) 0 x) flagIdx = decide ((x + c) < N)
    unfold modAddConstGate_dirtyFlag
    rw [show Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
            (Gate.seq (subConstGate (bits + 1) N)
              (Gate.seq (copyTargetHighBitToFlag bits flagIdx)
                (conditionalAddConstGate (bits + 1) N flagIdx))))
            (adder_input_F (bits + 1) 0 x)
          = Gate.applyNat (conditionalAddConstGate (bits + 1) N flagIdx)
              (Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
                  (Gate.seq (subConstGate (bits + 1) N)
                    (copyTargetHighBitToFlag bits flagIdx)))
                (adder_input_F (bits + 1) 0 x)) from rfl]
    rw [h_3]
    exact conditionalAddConstGate_flag_preserved (bits+1) N
            (subConstPow2WideSpec bits N (x+c)) flagIdx (decide ((x+c)<N))
            hbits' hflagIdx

/-! ## Tick 4 — Flag uncomputation design + proof

**Design.**  After `modAddConstGate_dirtyFlag`, target = `m := (x+c) mod N`
and flag = `decide ((x+c) < N)`.  We use the identity
`flag = decide (m ≥ c)` (proved by case analysis on `(x+c)<N`):
* if `(x+c) < N`: `m = x+c`, so `m ≥ c` (since `x ≥ 0`);
* if `(x+c) ≥ N`: `m = x+c-N`, so `m < c` (since `x < N`).

The reversible uncompute is a four-step gate:
1. `subConstGate (bits+1) c` — target → `subConstPow2Spec (bits+1) c m`.
   By `subConstPow2WideSpec_high_bit`, `target_idx bits = decide (m < c)`.
2. `CX (target_idx bits) flagIdx` — XOR-in: flag becomes
   `decide (m ≥ c) XOR decide (m < c) = true`.
3. `X flagIdx` — flag becomes `false`.
4. `addConstGate (bits+1) c` — target restored to `m`.

Read/carry are restored automatically by the add/sub workspace.  This
implementation uses ONLY existing Gate IR primitives (no controlled-CCX). -/

/-! ### Generalized state-eq for add/sub at width `n`

For the uncompute proof we need state-eq under just `c < 2^n, x < 2^n`,
without the modular `x < N, c < N` hypothesis.  Both forms work via the
same per-position case analysis. -/

/-- General state-eq: `addConstGate bits c` applied to a clean input
`adder_input_F bits 0 x` produces `adder_input_F bits 0 ((x + c) % 2^bits)`,
under just `c < 2^bits` and `x < 2^bits`. -/
theorem addConstGate_state_eq_general
    (bits c x : Nat) (hbits : 2 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits) :
    Gate.applyNat (addConstGate bits c) (adder_input_F bits 0 x)
    = adder_input_F bits 0 ((x + c) % 2^bits) := by
  funext p
  by_cases hp_high : 3 * bits ≤ p
  · rw [addConstGate_preserves_above_actual bits c _ p hp_high]
    unfold adder_input_F
    rcases h_mod : p % 3 with _ | _ | _
    · simp [Nat.zero_testBit]
    · have h_div_ge : p / 3 ≥ bits := by omega
      simp [show ¬ (p / 3 < bits) from by omega]
    · rfl
  · push_neg at hp_high
    obtain ⟨_, _, h_read, h_carry⟩ := addConstGate_clean bits c x hbits hc hx
    have h_p_div_lt : p / 3 < bits := by omega
    rcases h_mod : p % 3 with _ | _ | _
    · have h_p_eq : p = read_idx (p / 3) := by unfold read_idx; omega
      rw [h_p_eq, h_read (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (read_idx (p/3)) % 3 = 0 from by unfold read_idx; omega,
          show (read_idx (p/3)) / 3 = p/3 from by unfold read_idx; omega]
      simp [Nat.zero_testBit]
    · have h_p_eq : p = target_idx (p / 3) := by unfold target_idx; omega
      rw [h_p_eq, addConstGate_target_bit bits c x (p/3) hbits hc hx h_p_div_lt]
      unfold adder_input_F
      rw [show (target_idx (p/3)) % 3 = 1 from by unfold target_idx; omega,
          show (target_idx (p/3)) / 3 = p/3 from by unfold target_idx; omega]
      simp [h_p_div_lt]
    · have h_p_eq : p = carry_idx (p / 3) := by unfold carry_idx; omega
      rw [h_p_eq, h_carry (p/3) h_p_div_lt]
      unfold adder_input_F
      rw [show (carry_idx (p/3)) % 3 = 2 from by unfold carry_idx; omega]

/-- General state-eq for subConstGate.  Follows from
`addConstGate_state_eq_general` via the definition `subConstGate = addConstGate (2^bits - N)`. -/
theorem subConstGate_state_eq_general
    (bits N x : Nat) (hbits : 2 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.applyNat (subConstGate bits N) (adder_input_F bits 0 x)
    = adder_input_F bits 0 (subConstPow2Spec bits N x) := by
  unfold subConstGate
  have hc : 2^bits - N < 2^bits := by
    have : 0 < 2^bits := Nat.two_pow_pos bits
    omega
  rw [addConstGate_state_eq_general bits (2^bits - N) x hbits hc hx]
  rfl

/-- **Tick 4 HEADLINE — flag uncomputation correctness**.  Given a state
of the form `update (adder_input_F (bits+1) 0 m) flagIdx (decide (m ≥ c))`
(target encoding `m < 2^bits`, flag stored at out-of-band `flagIdx`),
the flag-uncompute gate restores the state to a clean
`adder_input_F (bits+1) 0 m` — i.e., flag becomes false, target / read /
carry unchanged. -/
theorem flagUncomputeGate_correct
    (bits c flagIdx m : Nat) (hbits : 1 ≤ bits) (hc_pos : 0 < c)
    (hc : c < 2^bits) (hm : m < 2^bits)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    Gate.applyNat (flagUncomputeGate bits c flagIdx)
      (update (adder_input_F (bits + 1) 0 m) flagIdx (decide (m ≥ c)))
    = adder_input_F (bits + 1) 0 m := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have hc_succ : c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hc_le_succ : c ≤ 2^(bits+1) := by omega
  have hm_succ : m < 2^(bits+1) := by rw [h_pow_succ]; omega
  obtain ⟨h_sub_wt, _, _, _⟩ := subConstGate_clean (bits+1) c c hbits' hc_pos hc_le_succ hc_succ
  have h_flag_eq : decide (m ≥ c) = !decide (m < c) := by
    rcases Nat.lt_or_ge m c with h | h
    · rw [decide_eq_true h, decide_eq_false (Nat.not_le.mpr h)]; rfl
    · rw [decide_eq_false (Nat.not_lt.mpr h), decide_eq_true h]; rfl
  unfold flagUncomputeGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq, Gate.applyNat_seq]
  rw [applyNat_commute_update_above_dim (adder_n_qubits (bits+1))
        (subConstGate (bits+1) c) h_sub_wt _ _ _ hflagIdx]
  rw [subConstGate_state_eq_general (bits+1) c m hbits' hc_pos hc_le_succ hm_succ]
  have h_mp_high :
      (subConstPow2Spec (bits+1) c m).testBit bits = decide (m < c) := by
    show ((m + (2^(bits+1) - c)) % 2^(bits+1)).testBit bits = decide (m < c)
    rw [show ((m + (2^(bits+1) - c)) % 2^(bits+1)) = subConstPow2WideSpec bits c m from by
          unfold subConstPow2WideSpec; rfl]
    exact subConstPow2WideSpec_high_bit bits c m (by omega) hm
  have h_ainput_tbits :
      adder_input_F (bits+1) 0 (subConstPow2Spec (bits+1) c m) (target_idx bits)
      = (subConstPow2Spec (bits+1) c m).testBit bits := by
    unfold adder_input_F
    rw [show (target_idx bits) % 3 = 1 from by unfold target_idx; omega,
        show (target_idx bits) / 3 = bits from by unfold target_idx; omega]
    simp [show bits < bits+1 from by omega]
  have h_flagIdx_ne_tbits : flagIdx ≠ target_idx bits := by
    unfold adder_n_qubits target_idx at *; omega
  have h_tbits_ne_flag : target_idx bits ≠ flagIdx := fun h => h_flagIdx_ne_tbits h.symm
  rw [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ h_tbits_ne_flag, update_eq, h_ainput_tbits, h_mp_high, h_flag_eq]
  have h_xor : ((!decide (m < c) ^^ decide (m < c)) : Bool) = true := by
    generalize decide (m < c) = b
    cases b <;> rfl
  rw [h_xor]
  rw [Gate.applyNat_X, update_eq]
  have h_collapse :
      ∀ (g : Nat → Bool) (v1 v2 v3 : Bool),
        update (update (update g flagIdx v1) flagIdx v2) flagIdx v3 = update g flagIdx v3 := by
    intros g v1 v2 v3
    funext k
    by_cases hk : k = flagIdx
    · subst hk; rw [update_eq, update_eq]
    · rw [update_neq _ _ _ _ hk, update_neq _ _ _ _ hk, update_neq _ _ _ _ hk,
          update_neq _ _ _ _ hk]
  rw [h_collapse]
  have h_input_flag :
      adder_input_F (bits+1) 0 (subConstPow2Spec (bits+1) c m) flagIdx = false := by
    apply adder_input_F_at_high
    unfold adder_n_qubits at hflagIdx; omega
  have h_update_eq :
      update (adder_input_F (bits+1) 0 (subConstPow2Spec (bits+1) c m)) flagIdx false
      = adder_input_F (bits+1) 0 (subConstPow2Spec (bits+1) c m) := by
    funext k
    by_cases hk : k = flagIdx
    · subst hk; rw [update_eq, h_input_flag]
    · rw [update_neq _ _ _ _ hk]
  show Gate.applyNat (addConstGate (bits + 1) c)
        (update (adder_input_F (bits+1) 0 (subConstPow2Spec (bits+1) c m)) flagIdx (!true))
      = adder_input_F (bits+1) 0 m
  rw [Bool.not_true, h_update_eq]
  rw [addConstGate_state_eq_general (bits+1) c (subConstPow2Spec (bits+1) c m) hbits' hc_succ
        (by show subConstPow2Spec (bits+1) c m < 2^(bits+1)
            unfold subConstPow2Spec; exact Nat.mod_lt _ (by rw [h_pow_succ]; omega))]
  congr 1
  show (subConstPow2Spec (bits+1) c m + c) % 2^(bits+1) = m
  unfold subConstPow2Spec
  rw [Nat.mod_add_mod]
  have h_eq : m + (2^(bits+1) - c) + c = m + 2^(bits+1) := by omega
  rw [h_eq, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hm_succ

/-- WellTyped at `flagIdx + 1`.  All four sub-gates are WellTyped at
`adder_n_qubits (bits + 1) ≤ flagIdx + 1`; the CX and X explicitly touch
`flagIdx`. -/
theorem flagUncomputeGate_wellTyped
    (bits c flagIdx : Nat) (hbits : 1 ≤ bits) (hc_pos : 0 < c) (hc : c < 2^bits)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    Gate.WellTyped (flagIdx + 1) (flagUncomputeGate bits c flagIdx) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have hc_succ : c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hc_le_succ : c ≤ 2^(bits+1) := by omega
  have h_flag_succ : adder_n_qubits (bits + 1) ≤ flagIdx + 1 := by omega
  unfold flagUncomputeGate
  obtain ⟨h_sub_wt, _, _, _⟩ := subConstGate_clean (bits+1) c c hbits' hc_pos hc_le_succ hc_succ
  have h_sub_wt' : Gate.WellTyped (flagIdx + 1) (subConstGate (bits + 1) c) :=
    Gate.WellTyped.mono h_sub_wt h_flag_succ
  obtain ⟨h_add_wt, _, _, _⟩ := addConstGate_clean (bits+1) c c hbits' hc_succ hc_succ
  have h_add_wt' : Gate.WellTyped (flagIdx + 1) (addConstGate (bits + 1) c) :=
    Gate.WellTyped.mono h_add_wt h_flag_succ
  have h_cx_wt : Gate.WellTyped (flagIdx + 1) (Gate.CX (target_idx bits) flagIdx) := by
    unfold adder_n_qubits target_idx at *
    refine ⟨?_, ?_, ?_⟩ <;> omega
  have h_x_wt : Gate.WellTyped (flagIdx + 1) (Gate.X flagIdx) := by
    show flagIdx < flagIdx + 1; omega
  exact ⟨h_sub_wt', h_cx_wt, h_x_wt, h_add_wt'⟩

/-! ## Tick 5 — Clean modular add-constant gate

Compose `modAddConstGate_dirtyFlag` with `flagUncomputeGate` to obtain
the *clean* modular add-constant gate `modAddConstGate`, whose output
is extensionally `adder_input_F (bits + 1) 0 ((x + c) mod N)` — i.e.,
target encodes `(x + c) mod N`, ALL workspace restored including the
flag bit.

The internal `flagIdx` is fixed at `adder_n_qubits (bits + 1)` (the
smallest valid out-of-band position).

Restriction: this clean gate requires `0 < c` (since `flagUncomputeGate`
uses `subConstGate (bits + 1) c` which requires `c > 0`).  The `c = 0`
case is degenerate (modular add by 0 = identity) and not handled here. -/

/-- Auxiliary: `modAddConstArithmeticSpec bits N c x < 2^bits` under
modular hypotheses.  Both flag cases produce a value in `[0, N - 1]`,
hence `< 2^bits`. -/
theorem modAddConstArithmeticSpec_lt_pow_bits
    (bits N c x : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N) :
    modAddConstArithmeticSpec bits N c x < 2^bits := by
  unfold modAddConstArithmeticSpec
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_pow_pos2 : 0 < 2^(bits+1) := by rw [h_pow_succ]; omega
  by_cases h_flag : x + c < N
  · have h_y : subConstPow2WideSpec bits N (x + c) = (x + c) + 2^(bits+1) - N := by
      unfold subConstPow2WideSpec
      have h_lt : (x + c) + (2^(bits+1) - N) < 2^(bits+1) := by omega
      rw [Nat.mod_eq_of_lt h_lt]; omega
    rw [h_y, decide_eq_true h_flag]
    show ((x + c) + 2^(bits+1) - N + N) % 2^(bits+1) < 2^bits
    have h_eq : ((x + c) + 2^(bits+1) - N) + N = (x + c) + 2^(bits+1) := by omega
    rw [h_eq, Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (show x + c < 2^(bits+1) by omega)]
    omega
  · have h_le : N ≤ x + c := by omega
    have h_y : subConstPow2WideSpec bits N (x + c) = (x + c) - N := by
      unfold subConstPow2WideSpec
      have h_eq2 : (x + c) + (2^(bits + 1) - N) = ((x + c) - N) + 2^(bits + 1) := by omega
      rw [h_eq2, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_y, decide_eq_false (by omega)]
    show ((x + c) - N + 0) % 2^(bits+1) < 2^bits
    rw [Nat.add_zero]
    have h_sN_lt : (x + c) - N < 2^bits := by omega
    have h_sN_lt' : (x + c) - N < 2^(bits+1) := by omega
    rw [Nat.mod_eq_of_lt h_sN_lt']
    exact h_sN_lt

/-- `modAddConstArithmeticSpec` equals `(x + c) mod N` (the high bit is
zero, so the mod-`2^(bits+1)` mask is the value itself). -/
theorem modAddConstArithmeticSpec_eq_mod
    (bits N c x : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N) :
    modAddConstArithmeticSpec bits N c x = (x + c) % N := by
  have h1 := modAddConstArithmeticSpec_correct bits N c x hN_pos hN hx hc
  have h2 := modAddConstArithmeticSpec_lt_pow_bits bits N c x hN_pos hN hx hc
  rw [Nat.mod_eq_of_lt h2] at h1
  exact h1

/-! ### Frame lemmas for `conditionalAddConstGate` and `modAddConstGate_dirtyFlag` -/

/-- `conditionalAddConstGate bits N flagIdx` preserves positions `≥ 3 * bits`. -/
theorem conditionalAddConstGate_preserves_above_not_flag
    (bits N flagIdx : Nat) (f : Nat → Bool) (p : Nat) (hp : 3 * bits ≤ p) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx) f p = f p := by
  unfold conditionalAddConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  have h_p_ne_read : ∀ i, i < bits → p ≠ read_idx i := by
    intro i hi; unfold read_idx; omega
  rw [prepareMaskedConstRead_preserves_outside bits N flagIdx _ p h_p_ne_read]
  rw [gidney_adder_full_faithful_no_measurement_patched_preserves_above bits _ p hp]
  exact prepareMaskedConstRead_preserves_outside bits N flagIdx f p h_p_ne_read

/-- `modAddConstGate_dirtyFlag bits N c flagIdx` preserves positions `≥ 3*(bits + 1)`
that are not `flagIdx`. -/
theorem modAddConstGate_dirtyFlag_preserves_above_not_flag
    (bits N c flagIdx : Nat) (f : Nat → Bool) (p : Nat)
    (hp : 3 * (bits + 1) ≤ p) (h_p_ne_flag : p ≠ flagIdx) :
    Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx) f p = f p := by
  unfold modAddConstGate_dirtyFlag
  rw [Gate.applyNat_seq, Gate.applyNat_seq, Gate.applyNat_seq]
  rw [conditionalAddConstGate_preserves_above_not_flag (bits+1) N flagIdx _ p hp]
  unfold copyTargetHighBitToFlag
  rw [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ h_p_ne_flag]
  rw [subConstGate_preserves_above_actual (bits+1) N _ p hp]
  exact addConstGate_preserves_above_actual (bits+1) c f p hp

/-- **Strong state-eq for `modAddConstGate_dirtyFlag`**.  The output is
extensionally equal to the canonical "input form" with target encoding
`(x + c) mod N` and the flag bit at `flagIdx` holding `decide ((x+c)<N)`. -/
theorem modAddConstGate_dirtyFlag_state_eq
    (bits N c x flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
      (adder_input_F (bits + 1) 0 x)
    = update (adder_input_F (bits + 1) 0 ((x + c) % N)) flagIdx (decide ((x + c) < N)) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have hbits' : 2 ≤ bits + 1 := by omega
  have hN_lt : N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_y_lt : subConstPow2WideSpec bits N (x + c) < 2^(bits+1) := by
    unfold subConstPow2WideSpec; exact Nat.mod_lt _ (by rw [h_pow_succ]; omega)
  obtain ⟨_, h_read, h_carry, h_flag⟩ :=
    modAddConstGate_dirtyFlag_workspace bits N c x flagIdx hbits hN_pos hN hx hc hflagIdx
  have h_apply_unfold :
      ∀ (g : Nat → Bool) (p : Nat),
        Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx) g p
        = Gate.applyNat (conditionalAddConstGate (bits + 1) N flagIdx)
            (Gate.applyNat (Gate.seq (addConstGate (bits + 1) c)
              (Gate.seq (subConstGate (bits + 1) N)
                (copyTargetHighBitToFlag bits flagIdx))) g) p := by
    intros g p; rfl
  have h_target : ∀ i, i < bits + 1 →
      Gate.applyNat (modAddConstGate_dirtyFlag bits N c flagIdx)
        (adder_input_F (bits + 1) 0 x) (target_idx i)
      = ((x + c) % N).testBit i := by
    intro i hi
    rw [h_apply_unfold]
    rw [modAddConstGate_dirtyFlag_after_three_steps_eq
          bits N c x flagIdx hbits hN_pos hN hx hc hflagIdx]
    rw [conditionalAddConstGate_target_bit (bits + 1) N flagIdx
          (subConstPow2WideSpec bits N (x + c)) i (decide ((x + c) < N))
          hbits' hN_lt h_y_lt hflagIdx hi]
    have h_bridge :
        (subConstPow2WideSpec bits N (x + c)
          + (if decide ((x + c) < N) = true then N else 0)).testBit i
        = (modAddConstArithmeticSpec bits N c x).testBit i := by
      unfold modAddConstArithmeticSpec
      rw [Nat.testBit_mod_two_pow]; simp [hi]
    rw [h_bridge]
    rw [modAddConstArithmeticSpec_eq_mod bits N c x hN_pos hN hx hc]
  funext p
  by_cases h_p_flag : p = flagIdx
  · subst h_p_flag; rw [h_flag, update_eq]
  · by_cases h_p_high : 3 * (bits + 1) ≤ p
    · rw [modAddConstGate_dirtyFlag_preserves_above_not_flag
            bits N c flagIdx _ p h_p_high h_p_flag]
      rw [update_neq _ _ _ _ h_p_flag]
      unfold adder_input_F
      rcases h_mod : p % 3 with _ | _ | _
      · simp [show ¬(p/3 < bits+1) from by omega]
      · simp [show ¬(p/3 < bits+1) from by omega]
      · rfl
    · push_neg at h_p_high
      have h_p_div_lt : p / 3 < bits + 1 := by omega
      rcases h_mod : p % 3 with _ | _ | _
      · have h_p_eq : p = read_idx (p / 3) := by unfold read_idx; omega
        rw [h_p_eq, h_read (p/3) h_p_div_lt]
        rw [update_neq _ _ _ _ (by rw [← h_p_eq]; exact h_p_flag)]
        unfold adder_input_F
        rw [show (read_idx (p/3)) % 3 = 0 from by unfold read_idx; omega,
            show (read_idx (p/3)) / 3 = p/3 from by unfold read_idx; omega]
        simp [Nat.zero_testBit]
      · have h_p_eq : p = target_idx (p / 3) := by unfold target_idx; omega
        rw [h_p_eq, h_target (p/3) h_p_div_lt]
        rw [update_neq _ _ _ _ (by rw [← h_p_eq]; exact h_p_flag)]
        unfold adder_input_F
        rw [show (target_idx (p/3)) % 3 = 1 from by unfold target_idx; omega,
            show (target_idx (p/3)) / 3 = p/3 from by unfold target_idx; omega]
        simp [h_p_div_lt]
      · have h_p_eq : p = carry_idx (p / 3) := by unfold carry_idx; omega
        rw [h_p_eq, h_carry (p/3) h_p_div_lt]
        rw [update_neq _ _ _ _ (by rw [← h_p_eq]; exact h_p_flag)]
        unfold adder_input_F
        rw [show (carry_idx (p/3)) % 3 = 2 from by unfold carry_idx; omega]

/-- **Tick 5 HEADLINE — clean modular add-constant**.  Applied to
`adder_input_F (bits + 1) 0 x`, the clean modular adder produces
`adder_input_F (bits + 1) 0 ((x + c) mod N)` — full state-eq with
target encoding the modular sum and ALL workspace (read, carry,
internal flag) restored. -/
theorem modAddConstGate_state_eq
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc_pos : 0 < c) (hc : c < N) :
    Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x)
    = adder_input_F (bits + 1) 0 ((x + c) % N) := by
  unfold modAddConstGate
  rw [Gate.applyNat_seq]
  rw [modAddConstGate_dirtyFlag_state_eq bits N c x (adder_n_qubits (bits + 1))
        hbits hN_pos hN hx hc (le_refl _)]
  have h_decide_eq : decide ((x + c) < N) = decide ((x + c) % N ≥ c) := by
    by_cases h : x + c < N
    · have h_mod : (x + c) % N = x + c := Nat.mod_eq_of_lt h
      rw [decide_eq_true h, h_mod]
      rw [decide_eq_true (by omega : x + c ≥ c)]
    · have h_le : N ≤ x + c := by omega
      have h_lt : x + c < 2 * N := by omega
      have h_mod : (x + c) % N = x + c - N := by
        have h_eq : x + c = (x + c - N) + N := by omega
        conv_lhs => rw [h_eq]
        rw [Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [decide_eq_false (by omega), h_mod]
      rw [decide_eq_false (by omega : ¬ x + c - N ≥ c)]
  rw [h_decide_eq]
  have h_xcN_lt_2bits : (x + c) % N < 2^bits := by
    have : (x + c) % N < N := Nat.mod_lt _ hN_pos
    omega
  exact flagUncomputeGate_correct bits c (adder_n_qubits (bits + 1)) ((x + c) % N)
          hbits hc_pos (by omega) h_xcN_lt_2bits (le_refl _)

/-- **Bundled clean theorem** — WellTyped, decoded target, read /
carry / flag all restored.  Derives from `modAddConstGate_state_eq`. -/
theorem modAddConstGate_clean
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc_pos : 0 < c) (hc : c < N) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + 1) (modAddConstGate bits N c)
    ∧ gidney_target_val bits
        (Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x))
      = (x + c) % N
    ∧ (∀ i, i < bits + 1 →
        Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x)
          (read_idx i) = false)
    ∧ (∀ i, i < bits + 1 →
        Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x)
          (carry_idx i) = false)
    ∧ Gate.applyNat (modAddConstGate bits N c) (adder_input_F (bits + 1) 0 x)
        (adder_n_qubits (bits + 1)) = false := by
  have h_state := modAddConstGate_state_eq bits N c x hbits hN_pos hN hx hc_pos hc
  have h_xcN_lt_N : (x + c) % N < N := Nat.mod_lt _ hN_pos
  have h_xcN_lt_2bits : (x + c) % N < 2^bits := by omega
  have h_xcN_mod_2bits : (x + c) % N % 2^bits = (x + c) % N :=
    Nat.mod_eq_of_lt h_xcN_lt_2bits
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- WellTyped: composition
    unfold modAddConstGate
    have h_flag_succ : adder_n_qubits (bits + 1) ≤ adder_n_qubits (bits + 1) := le_refl _
    have h_dirty_wt :
        Gate.WellTyped (adder_n_qubits (bits + 1) + 1)
          (modAddConstGate_dirtyFlag bits N c (adder_n_qubits (bits + 1))) := by
      have := (modAddConstGate_dirtyFlag_workspace bits N c x (adder_n_qubits (bits + 1))
                hbits hN_pos hN hx hc h_flag_succ).1
      exact this
    have h_unc_wt :
        Gate.WellTyped (adder_n_qubits (bits + 1) + 1)
          (flagUncomputeGate bits c (adder_n_qubits (bits + 1))) :=
      flagUncomputeGate_wellTyped bits c (adder_n_qubits (bits + 1)) hbits hc_pos
        (by omega) h_flag_succ
    exact ⟨h_dirty_wt, h_unc_wt⟩
  · -- target decode
    rw [h_state]
    rw [← h_xcN_mod_2bits]
    apply gidney_target_val_eq_sum_when_bits_match bits ((x + c) % N)
    intro i hi
    unfold adder_input_F
    rw [show (target_idx i) % 3 = 1 from by unfold target_idx; omega,
        show (target_idx i) / 3 = i from by unfold target_idx; omega]
    simp only [show decide (i < bits + 1) = true from decide_eq_true (by omega),
               Bool.true_and]
    rw [h_xcN_mod_2bits]
  · -- read restored
    intro i hi
    rw [h_state]
    unfold adder_input_F
    rw [show (read_idx i) % 3 = 0 from by unfold read_idx; omega,
        show (read_idx i) / 3 = i from by unfold read_idx; omega]
    simp [Nat.zero_testBit]
  · -- carries cleared
    intro i hi
    rw [h_state]
    unfold adder_input_F
    rw [show (carry_idx i) % 3 = 2 from by unfold carry_idx; omega]
  · -- flag restored to false
    rw [h_state]
    apply adder_input_F_at_high
    unfold adder_n_qubits; omega

/-- `controlledModAddConstGate` is `WellTyped` at `flagIdx + 1` when
`controlIdx` and `flagIdx` are both out-of-band, with `controlIdx < flagIdx`. -/
theorem controlledModAddConstGate_wellTyped
    (bits N c controlIdx flagIdx : Nat) (hbits : 1 ≤ bits)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.WellTyped (flagIdx + 1) (controlledModAddConstGate bits N c controlIdx flagIdx) := by
  have hbits' : 2 ≤ bits + 1 := by omega
  have hcontrol_above : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  -- Each conditionalAddConstGate is WellTyped at `(its-flag) + 1`, then mono'd to `flagIdx + 1`.
  have h_cond_c_ctrl :
      Gate.WellTyped (flagIdx + 1) (conditionalAddConstGate (bits + 1) c controlIdx) :=
    Gate.WellTyped.mono
      (conditionalAddConstGate_wellTyped (bits+1) c controlIdx hbits' hcontrolIdx)
      (by omega)
  have h_cond_subN_ctrl :
      Gate.WellTyped (flagIdx + 1)
        (conditionalAddConstGate (bits + 1) (2^(bits+1) - N) controlIdx) :=
    Gate.WellTyped.mono
      (conditionalAddConstGate_wellTyped (bits+1) (2^(bits+1) - N) controlIdx hbits' hcontrolIdx)
      (by omega)
  have h_cond_N_flag :
      Gate.WellTyped (flagIdx + 1) (conditionalAddConstGate (bits + 1) N flagIdx) :=
    conditionalAddConstGate_wellTyped (bits+1) N flagIdx hbits' hcontrol_above
  have h_cond_subc_ctrl :
      Gate.WellTyped (flagIdx + 1)
        (conditionalAddConstGate (bits + 1) (2^(bits+1) - c) controlIdx) :=
    Gate.WellTyped.mono
      (conditionalAddConstGate_wellTyped (bits+1) (2^(bits+1) - c) controlIdx hbits' hcontrolIdx)
      (by omega)
  have h_ccx :
      Gate.WellTyped (flagIdx + 1) (Gate.CCX controlIdx (target_idx bits) flagIdx) := by
    unfold adder_n_qubits target_idx at *
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  have h_cx : Gate.WellTyped (flagIdx + 1) (Gate.CX controlIdx flagIdx) := by
    refine ⟨?_, ?_, ?_⟩
    · omega
    · omega
    · omega
  unfold controlledModAddConstGate
  exact ⟨h_cond_c_ctrl, h_cond_subN_ctrl, h_ccx, h_cond_N_flag, h_cond_subc_ctrl, h_ccx,
         h_cx, h_cond_c_ctrl⟩

/-! ### Tick 6b — `conditionalAddConstGate` full state-eq

The key reusable building block for `controlledModAddConstGate`
correctness: a STRONG (extensional) state-eq for `conditionalAddConstGate`
covering BOTH branches of the flag uniformly.  When `flag = false` the
gate is identity on the canonical input form; when `flag = true` it
adds `N` mod `2^bits`. -/

/-- **`conditionalAddConstGate` full state-eq.**  Applied to
`update (adder_input_F bits 0 x) flagIdx flag`, the gate produces
`update (adder_input_F bits 0 ((x + (if flag then N else 0)) % 2^bits))
flagIdx flag` — i.e. flag preserved, target = `(x + flag·N) mod 2^bits`,
read / carry restored. -/
theorem conditionalAddConstGate_state_eq
    (bits N flagIdx x : Nat) (flag : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx)
      (update (adder_input_F bits 0 x) flagIdx flag)
    = update (adder_input_F bits 0 ((x + (if flag then N else 0)) % 2^bits)) flagIdx flag := by
  have h_disj : ∀ j, j < bits → flagIdx ≠ read_idx j := by
    intro j hj
    unfold adder_n_qubits read_idx at *; omega
  obtain ⟨_, _, h_read, h_carry, h_flag⟩ :=
    conditionalAddConstGate_clean bits N x flagIdx flag hbits hN hx hflagIdx
  have h_frame := conditionalAddConstGate_preserves_above_not_flag bits N flagIdx
  funext p
  by_cases h_p_flag : p = flagIdx
  · subst h_p_flag
    rw [h_flag, update_eq]
  · by_cases h_p_high : 3 * bits ≤ p
    · rw [h_frame _ p h_p_high]
      rw [update_neq _ _ _ _ h_p_flag, update_neq _ _ _ _ h_p_flag]
      unfold adder_input_F
      rcases h_mod : p % 3 with _ | _ | _
      · simp [show ¬(p/3 < bits) from by omega]
      · simp [show ¬(p/3 < bits) from by omega]
      · rfl
    · push_neg at h_p_high
      have h_p_div_lt : p / 3 < bits := by omega
      rcases h_mod : p % 3 with _ | _ | _
      · have h_p_eq : p = read_idx (p / 3) := by unfold read_idx; omega
        rw [h_p_eq, h_read (p/3) h_p_div_lt]
        rw [update_neq _ _ _ _ (by rw [← h_p_eq]; exact h_p_flag)]
        unfold adder_input_F
        rw [show (read_idx (p/3)) % 3 = 0 from by unfold read_idx; omega,
            show (read_idx (p/3)) / 3 = p/3 from by unfold read_idx; omega]
        simp [Nat.zero_testBit]
      · have h_p_eq : p = target_idx (p / 3) := by unfold target_idx; omega
        rw [h_p_eq]
        rw [conditionalAddConstGate_target_bit bits N flagIdx x (p/3) flag hbits hN hx hflagIdx
              h_p_div_lt]
        rw [update_neq _ _ _ _ (by rw [← h_p_eq]; exact h_p_flag)]
        unfold adder_input_F
        rw [show (target_idx (p/3)) % 3 = 1 from by unfold target_idx; omega,
            show (target_idx (p/3)) / 3 = p/3 from by unfold target_idx; omega]
        simp only [show decide (p/3 < bits) = true from decide_eq_true h_p_div_lt, Bool.true_and]
        rw [Nat.testBit_mod_two_pow]
        simp [h_p_div_lt]
      · have h_p_eq : p = carry_idx (p / 3) := by unfold carry_idx; omega
        rw [h_p_eq, h_carry (p/3) h_p_div_lt]
        rw [update_neq _ _ _ _ (by rw [← h_p_eq]; exact h_p_flag)]
        unfold adder_input_F
        rw [show (carry_idx (p/3)) % 3 = 2 from by unfold carry_idx; omega]

/-! ### Tick 6c — Commute lemmas for chaining `controlledModAddConstGate`

To prove `controlledModAddConstGate_correct` we need to chain step-eq's
across 8 sub-gates where each step's natural input is a *multi-update*
form (e.g., `update (update (adder_input_F …) flagIdx flag) controlIdx
controlBit`).  This requires showing each sub-gate commutes with the
"outer" update — i.e. doesn't read from or write to that position.

The first piece is a commute lemma for `prepareMaskedConstRead` past an
outer update at a position outside its read/write set. -/

/-- `prepareMaskedConstRead bits N flagIdx` commutes with `update _ p v`
when `p` is outside the gate's read/write set: `p ≠ flagIdx` (not read
as control) and `p ≠ read_idx k` for any `k < bits` (not written). -/
theorem prepareMaskedConstRead_commute_update_outer
    (bits N flagIdx p : Nat) (v : Bool)
    (h_p_ne_flag : p ≠ flagIdx)
    (h_p_ne_read : ∀ i, i < bits → p ≠ read_idx i) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (prepareMaskedConstRead bits N flagIdx) (update f p v)
      = update (Gate.applyNat (prepareMaskedConstRead bits N flagIdx) f) p v := by
  induction bits with
  | zero => intro f; rfl
  | succ k ih =>
      have h_p_ne_read_lt_k : ∀ i, i < k → p ≠ read_idx i :=
        fun i hi => h_p_ne_read i (by omega)
      have h_p_ne_read_k : p ≠ read_idx k := h_p_ne_read k (by omega)
      have ih' := ih h_p_ne_read_lt_k
      intro f
      show Gate.applyNat (Gate.seq (prepareMaskedConstRead k N flagIdx)
              (if N.testBit k then Gate.CX flagIdx (read_idx k) else Gate.I))
            (update f p v)
          = update (Gate.applyNat (Gate.seq (prepareMaskedConstRead k N flagIdx)
              (if N.testBit k then Gate.CX flagIdx (read_idx k) else Gate.I)) f) p v
      apply applyNat_seq_commute_update
      · intro f'; exact ih' f'
      · intro f'
        by_cases h_test : N.testBit k
        · simp [h_test]
          exact applyNat_CX_commute_update_disjoint flagIdx (read_idx k) f' p v
            h_p_ne_flag h_p_ne_read_k
        · simp [h_test]

/-- `conditionalAddConstGate bits N flagIdx` commutes with `update _ p v`
when `p` is outside the gate's actual support: `p ≥ adder_n_qubits bits`
and `p ≠ flagIdx`.  Composes prep + adder + prep commute lemmas. -/
theorem conditionalAddConstGate_commute_update_outer
    (bits N flagIdx p : Nat) (v : Bool)
    (hbits : 2 ≤ bits)
    (hp_dim : adder_n_qubits bits ≤ p)
    (h_p_ne_flag : p ≠ flagIdx) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (conditionalAddConstGate bits N flagIdx) (update f p v)
      = update (Gate.applyNat (conditionalAddConstGate bits N flagIdx) f) p v := by
  intro f
  unfold conditionalAddConstGate
  have h_p_ne_read : ∀ i, i < bits → p ≠ read_idx i := by
    intro i hi; unfold adder_n_qubits read_idx at *; omega
  have h_adder_wt : Gate.WellTyped (adder_n_qubits bits)
                      (gidney_adder_full_faithful_no_measurement_patched bits) :=
    gidney_adder_full_faithful_no_measurement_patched_wellTyped bits hbits
  apply applyNat_seq_commute_update
  · intro f'
    exact prepareMaskedConstRead_commute_update_outer bits N flagIdx p v
      h_p_ne_flag h_p_ne_read f'
  · intro f'
    apply applyNat_seq_commute_update
    · intro f''
      exact applyNat_commute_update_above_dim (adder_n_qubits bits)
        (gidney_adder_full_faithful_no_measurement_patched bits) h_adder_wt f'' p v hp_dim
    · intro f''
      exact prepareMaskedConstRead_commute_update_outer bits N flagIdx p v
        h_p_ne_flag h_p_ne_read f''

/-- State-eq for `conditionalAddConstGate` lifted past an outer update
at `outerIdx`.  This is the form that lets us chain through
`controlledModAddConstGate`'s 8 steps where each sub-state has both
`flagIdx` and `controlIdx` updates active simultaneously. -/
theorem conditionalAddConstGate_state_eq_with_outer
    (bits N flagIdx outerIdx x : Nat) (flag outerVal : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx)
    (hOuter : adder_n_qubits bits ≤ outerIdx) (hOuter_ne_flag : outerIdx ≠ flagIdx) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx)
      (update (update (adder_input_F bits 0 x) flagIdx flag) outerIdx outerVal)
    = update
        (update (adder_input_F bits 0 ((x + (if flag then N else 0)) % 2^bits))
          flagIdx flag) outerIdx outerVal := by
  rw [conditionalAddConstGate_commute_update_outer bits N flagIdx outerIdx outerVal
        hbits hOuter hOuter_ne_flag]
  rw [conditionalAddConstGate_state_eq bits N flagIdx x flag hbits hN hx hflagIdx]

/-- Helper: an `update` at a high `flagIdx` to `false` is idempotent
relative to `adder_input_F n 0 x` (since `adder_input_F` is already
`false` at any position `≥ 3 * n`).  Used in the `controlBit = false`
chain proof to insert/remove redundant flagIdx updates so state forms
match `conditionalAddConstGate_state_eq_with_outer`'s expected shape. -/
theorem collapse_flag_false_update_at_high
    (n flagIdx outerIdx x : Nat) (outerVal : Bool)
    (hflag_high : 3 * n ≤ flagIdx) :
    update (update (adder_input_F n 0 x) flagIdx false) outerIdx outerVal
    = update (adder_input_F n 0 x) outerIdx outerVal := by
  have h_adder_input_at_flag : adder_input_F n 0 x flagIdx = false := by
    unfold adder_input_F
    rcases h_mod : flagIdx % 3 with _ | _ | _
    · have : flagIdx / 3 ≥ n := by omega
      simp [show ¬(flagIdx/3 < n) from by omega]
    · have : flagIdx / 3 ≥ n := by omega
      simp [show ¬(flagIdx/3 < n) from by omega]
    · rfl
  funext q
  by_cases h_q_outer : q = outerIdx
  · rw [h_q_outer, update_eq, update_eq]
  · rw [update_neq _ _ _ _ h_q_outer, update_neq _ _ _ _ h_q_outer]
    by_cases h_q_flag : q = flagIdx
    · rw [h_q_flag, update_eq, h_adder_input_at_flag]
    · rw [update_neq _ _ _ _ h_q_flag]

/-- Corollary of `conditionalAddConstGate_state_eq` for `flag = false`:
the gate is identity on the canonical input form. -/
theorem conditionalAddConstGate_identity_when_flag_false
    (bits N flagIdx x : Nat) (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx)
      (update (adder_input_F bits 0 x) flagIdx false)
    = update (adder_input_F bits 0 x) flagIdx false := by
  rw [conditionalAddConstGate_state_eq bits N flagIdx x false hbits hN hx hflagIdx]
  congr 2
  show (x + 0) % 2^bits = x
  rw [Nat.add_zero, Nat.mod_eq_of_lt hx]

/-- Corollary of `conditionalAddConstGate_state_eq_with_outer` for
`flag = false`: the gate is identity on the *double-update* form, useful
when chaining through `controlledModAddConstGate`'s steps. -/
theorem conditionalAddConstGate_identity_when_flag_false_with_outer
    (bits N flagIdx outerIdx x : Nat) (outerVal : Bool)
    (hbits : 2 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (hflagIdx : adder_n_qubits bits ≤ flagIdx)
    (hOuter : adder_n_qubits bits ≤ outerIdx) (hOuter_ne_flag : outerIdx ≠ flagIdx) :
    Gate.applyNat (conditionalAddConstGate bits N flagIdx)
      (update (update (adder_input_F bits 0 x) flagIdx false) outerIdx outerVal)
    = update (update (adder_input_F bits 0 x) flagIdx false) outerIdx outerVal := by
  rw [conditionalAddConstGate_state_eq_with_outer bits N flagIdx outerIdx x false outerVal
        hbits hN hx hflagIdx hOuter hOuter_ne_flag]
  congr 3
  show (x + 0) % 2^bits = x
  rw [Nat.add_zero, Nat.mod_eq_of_lt hx]

/-- **Tick 6g HEADLINE — `controlBit = false` branch of `controlledModAddConstGate_correct`**.
When the control bit is `false`, the entire 8-step controlled
modular-add pipeline is identity: target / read / carry / flag all
unchanged.  Proved by chaining 8 identity rewrites. -/
theorem controlledModAddConstGate_correct_false
    (bits N c x : Nat) (controlIdx flagIdx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx)
      (update (adder_input_F (bits + 1) 0 x) controlIdx false)
    = update (adder_input_F (bits + 1) 0 x) controlIdx false := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have hc_succ : c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hx_succ : x < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hN_succ : N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_pow_succ_pos : 0 < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hN_2sub : 2^(bits+1) - N < 2^(bits+1) := by omega
  have hc_2sub : 2^(bits+1) - c < 2^(bits+1) := by omega
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_3_succ_flag : 3 * (bits + 1) ≤ flagIdx := by
    unfold adder_n_qubits at h_flag_ge; omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := by omega
  have h_ctrl_ne_flag : controlIdx ≠ flagIdx := h_flag_ne_ctrl.symm
  have h_state_ctrl : (update (adder_input_F (bits + 1) 0 x) controlIdx false) controlIdx = false :=
    update_eq _ _ _
  have h_state_flag : (update (adder_input_F (bits + 1) 0 x) controlIdx false) flagIdx = false := by
    rw [update_neq _ _ _ _ h_flag_ne_ctrl]
    unfold adder_input_F
    rcases h_mod : flagIdx % 3 with _ | _ | _
    · have : flagIdx / 3 ≥ bits + 1 := by omega
      simp [show ¬(flagIdx/3 < bits + 1) from by omega]
    · have : flagIdx / 3 ≥ bits + 1 := by omega
      simp [show ¬(flagIdx/3 < bits + 1) from by omega]
    · rfl
  have h_update_self : update (update (adder_input_F (bits + 1) 0 x) controlIdx false) flagIdx false
                     = update (adder_input_F (bits + 1) 0 x) controlIdx false := by
    funext q
    by_cases h_q_flag : q = flagIdx
    · rw [h_q_flag, update_eq, update_neq _ _ _ _ h_flag_ne_ctrl]
      unfold adder_input_F
      rcases h_mod : flagIdx % 3 with _ | _ | _
      · have : flagIdx / 3 ≥ bits + 1 := by omega
        simp [show ¬(flagIdx/3 < bits + 1) from by omega]
      · have : flagIdx / 3 ≥ bits + 1 := by omega
        simp [show ¬(flagIdx/3 < bits + 1) from by omega]
      · rfl
    · rw [update_neq _ _ _ _ h_q_flag]
  unfold controlledModAddConstGate
  rw [Gate.applyNat_seq]
  rw [conditionalAddConstGate_identity_when_flag_false (bits+1) c controlIdx x
        hbits' hc_succ hx_succ hcontrolIdx]
  rw [Gate.applyNat_seq]
  rw [conditionalAddConstGate_identity_when_flag_false (bits+1) (2^(bits+1) - N) controlIdx x
        hbits' hN_2sub hx_succ hcontrolIdx]
  rw [Gate.applyNat_seq, Gate.applyNat_CCX]
  rw [h_state_ctrl, h_state_flag]
  simp only [Bool.false_and, Bool.false_xor]
  rw [h_update_self]
  rw [Gate.applyNat_seq]
  rw [(collapse_flag_false_update_at_high (bits+1) flagIdx controlIdx x false h_3_succ_flag).symm]
  rw [conditionalAddConstGate_identity_when_flag_false_with_outer (bits+1) N flagIdx controlIdx x
        false hbits' hN_succ hx_succ h_flag_ge hcontrolIdx h_ctrl_ne_flag]
  rw [collapse_flag_false_update_at_high (bits+1) flagIdx controlIdx x false h_3_succ_flag]
  rw [Gate.applyNat_seq]
  rw [conditionalAddConstGate_identity_when_flag_false (bits+1) (2^(bits+1) - c) controlIdx x
        hbits' hc_2sub hx_succ hcontrolIdx]
  rw [Gate.applyNat_seq, Gate.applyNat_CCX]
  rw [h_state_ctrl, h_state_flag]
  simp only [Bool.false_and, Bool.false_xor]
  rw [h_update_self]
  rw [Gate.applyNat_seq, Gate.applyNat_CX]
  rw [h_state_ctrl, h_state_flag]
  simp only [Bool.false_xor]
  rw [h_update_self]
  rw [conditionalAddConstGate_identity_when_flag_false (bits+1) c controlIdx x
        hbits' hc_succ hx_succ hcontrolIdx]

/-- Intermediate: applying step 1 of controlled pipeline (controlled
add c) with controlBit = true gives target = `x + c`. -/
theorem controlled_step1_true
    (bits c x controlIdx : Nat) (hbits : 1 ≤ bits)
    (hc_succ : c < 2^(bits+1)) (hxc_lt : x + c < 2^(bits+1))
    (hx_succ : x < 2^(bits+1))
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx) :
    Gate.applyNat (conditionalAddConstGate (bits + 1) c controlIdx)
      (update (adder_input_F (bits + 1) 0 x) controlIdx true)
    = update (adder_input_F (bits + 1) 0 (x + c)) controlIdx true := by
  have hbits' : 2 ≤ bits + 1 := by omega
  rw [conditionalAddConstGate_state_eq (bits+1) c controlIdx x true hbits' hc_succ hx_succ hcontrolIdx]
  congr 2
  show (x + c) % 2^(bits+1) = x + c
  exact Nat.mod_eq_of_lt hxc_lt

/-- Intermediate: applying step 2 of controlled pipeline (controlled
sub N) with controlBit = true takes target from `x + c` to
`subConstPow2WideSpec bits N (x+c)`. -/
theorem controlled_step2_true
    (bits N c x controlIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx) :
    Gate.applyNat (conditionalAddConstGate (bits + 1) (2^(bits+1) - N) controlIdx)
      (update (adder_input_F (bits + 1) 0 (x + c)) controlIdx true)
    = update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c))) controlIdx true := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have h_pow_succ_pos : 0 < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hN_2sub_lt : 2^(bits+1) - N < 2^(bits+1) := by omega
  have h_xc_lt_pow : x + c < 2^(bits+1) := by rw [h_pow_succ]; omega
  rw [conditionalAddConstGate_state_eq (bits+1) (2^(bits+1) - N) controlIdx (x+c) true
        hbits' hN_2sub_lt h_xc_lt_pow hcontrolIdx]
  rfl

/-- Intermediate: applying step 3 of controlled pipeline (CCX flag-copy)
with controlBit = true puts `decide ((x+c) < N)` into `flagIdx`. -/
theorem controlled_step3_true
    (bits N c x controlIdx flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (Gate.CCX controlIdx (target_idx bits) flagIdx)
      (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c))) controlIdx true)
    = update (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)))
                controlIdx true) flagIdx (decide ((x + c) < N)) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_3_succ_flag : 3 * (bits + 1) ≤ flagIdx := by
    unfold adder_n_qubits at h_flag_ge; omega
  have h_target_bits_ne_ctrl : target_idx bits ≠ controlIdx := by
    unfold adder_n_qubits at hcontrolIdx; unfold target_idx; omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := by omega
  -- Compute state values at controlIdx, target_idx bits, flagIdx
  have h_state_ctrl : (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)))
                        controlIdx true) controlIdx = true := update_eq _ _ _
  have h_y_high : (subConstPow2WideSpec bits N (x + c)).testBit bits = decide ((x + c) < N) :=
    subConstPow2WideSpec_high_bit_bounded_sum bits N (x+c) hN_pos hN h_xc_lt_2N
  have h_state_tbits :
      (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c))) controlIdx true)
        (target_idx bits) = decide ((x + c) < N) := by
    rw [update_neq _ _ _ _ h_target_bits_ne_ctrl]
    unfold adder_input_F
    rw [show (target_idx bits) % 3 = 1 from by unfold target_idx; omega,
        show (target_idx bits) / 3 = bits from by unfold target_idx; omega]
    simp only [show decide (bits < bits + 1) = true from decide_eq_true (by omega), Bool.true_and]
    exact h_y_high
  have h_state_flag :
      (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c))) controlIdx true)
        flagIdx = false := by
    rw [update_neq _ _ _ _ h_flag_ne_ctrl]
    unfold adder_input_F
    rcases h_mod : flagIdx % 3 with _ | _ | _
    · have : flagIdx / 3 ≥ bits + 1 := by omega
      simp [show ¬(flagIdx/3 < bits + 1) from by omega]
    · have : flagIdx / 3 ≥ bits + 1 := by omega
      simp [show ¬(flagIdx/3 < bits + 1) from by omega]
    · rfl
  -- Apply CCX
  rw [Gate.applyNat_CCX]
  rw [h_state_ctrl, h_state_tbits, h_state_flag]
  simp only [Bool.true_and, Bool.false_xor]

/-- Intermediate: applying step 4 of controlled pipeline (flag-controlled
add-back of N) takes target from `subConstPow2WideSpec bits N (x+c)` to
`(x + c) % N` when flag holds `decide ((x+c) < N)`. -/
theorem controlled_step4_true
    (bits N c x controlIdx flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (conditionalAddConstGate (bits + 1) N flagIdx)
      (update (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits N (x + c)))
                  controlIdx true) flagIdx (decide ((x + c) < N)))
    = update (update (adder_input_F (bits + 1) 0 ((x + c) % N))
                controlIdx true) flagIdx (decide ((x + c) < N)) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have hN_succ : N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_y_lt : subConstPow2WideSpec bits N (x + c) < 2^(bits+1) := by
    unfold subConstPow2WideSpec; exact Nat.mod_lt _ (by rw [h_pow_succ]; omega)
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_ctrl_ne_flag : controlIdx ≠ flagIdx := by omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := h_ctrl_ne_flag.symm
  -- Swap update order: flagIdx OUTER, controlIdx INNER → controlIdx OUTER, flagIdx INNER
  rw [update_update_comm _ controlIdx flagIdx true (decide ((x + c) < N)) h_ctrl_ne_flag]
  -- Now: update (update ad-inp-F flagIdx flag) controlIdx true. flagIdx INNER, controlIdx OUTER.
  rw [conditionalAddConstGate_state_eq_with_outer (bits + 1) N flagIdx controlIdx
        (subConstPow2WideSpec bits N (x + c)) (decide ((x + c) < N)) true
        hbits' hN_succ h_y_lt h_flag_ge hcontrolIdx h_ctrl_ne_flag]
  -- Bridge to modAddConstArithmeticSpec
  have h_bridge : (subConstPow2WideSpec bits N (x + c)
                  + (if decide ((x + c) < N) = true then N else 0)) % 2 ^ (bits + 1)
                  = (x + c) % N := by
    have h_arith_eq := modAddConstArithmeticSpec_eq_mod bits N c x hN_pos hN hx hc
    unfold modAddConstArithmeticSpec at h_arith_eq
    exact h_arith_eq
  rw [h_bridge]
  -- Swap back: controlIdx OUTER, flagIdx INNER → flagIdx OUTER, controlIdx INNER
  rw [update_update_comm _ flagIdx controlIdx (decide ((x + c) < N)) true h_flag_ne_ctrl]

end FormalRV.BQAlgo
