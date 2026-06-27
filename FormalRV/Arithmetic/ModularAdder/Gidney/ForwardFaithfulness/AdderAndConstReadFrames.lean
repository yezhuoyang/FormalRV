/- ForwardFaithfulness — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.RippleCarryAdder
import Mathlib.Data.Nat.Bitwise
import FormalRV.Arithmetic.ModularAdder.Gidney.Def
import FormalRV.Arithmetic.ModularAdder.Gidney.PowerOfTwoCase

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


end FormalRV.BQAlgo
