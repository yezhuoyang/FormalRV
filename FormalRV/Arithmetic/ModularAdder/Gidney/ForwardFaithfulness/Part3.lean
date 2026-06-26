/- ForwardFaithfulness — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModularAdder.Gidney.ForwardFaithfulness.Part2

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

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


end FormalRV.BQAlgo
