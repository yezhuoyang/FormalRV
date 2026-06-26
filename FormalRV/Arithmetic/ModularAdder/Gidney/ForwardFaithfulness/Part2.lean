/- ForwardFaithfulness — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModularAdder.Gidney.ForwardFaithfulness.Part1

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

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


end FormalRV.BQAlgo
