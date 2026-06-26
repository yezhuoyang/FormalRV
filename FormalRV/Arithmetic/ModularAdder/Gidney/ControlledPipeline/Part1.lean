/- ControlledPipeline — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.RippleCarryAdder
import Mathlib.Data.Nat.Bitwise
import FormalRV.Arithmetic.ModularAdder.Gidney.Def
import FormalRV.Arithmetic.ModularAdder.Gidney.ForwardFaithfulness

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-- Intermediate: applying step 5 of controlled pipeline (controlled
sub c) with controlBit = true takes target from `(x+c) % N` to
`subConstPow2WideSpec bits c ((x+c) % N)`. -/
theorem controlled_step5_true
    (bits N c x controlIdx flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (conditionalAddConstGate (bits + 1) (2^(bits+1) - c) controlIdx)
      (update (update (adder_input_F (bits + 1) 0 ((x + c) % N)) controlIdx true)
              flagIdx (decide ((x + c) < N)))
    = update (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits c ((x + c) % N)))
                controlIdx true) flagIdx (decide ((x + c) < N)) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have h_pow_succ_pos : 0 < 2^(bits + 1) := by rw [h_pow_succ]; omega
  have hc_2sub_lt : 2^(bits+1) - c < 2^(bits+1) := by omega
  have h_mod_lt_N : (x + c) % N < N := Nat.mod_lt _ hN_pos
  have h_mod_lt_pow : (x + c) % N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := by omega
  rw [conditionalAddConstGate_state_eq_with_outer (bits + 1) (2^(bits+1) - c) controlIdx flagIdx
        ((x + c) % N) true (decide ((x + c) < N))
        hbits' hc_2sub_lt h_mod_lt_pow hcontrolIdx h_flag_ge h_flag_ne_ctrl]
  rfl

/-- Intermediate: applying step 6 of controlled pipeline (second CCX
flag-copy) with controlBit = true sets flagIdx to `TRUE` (the XOR of
the comparison flag and its complement). -/
theorem controlled_step6_true
    (bits N c x controlIdx flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (Gate.CCX controlIdx (target_idx bits) flagIdx)
      (update (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits c ((x + c) % N)))
                  controlIdx true) flagIdx (decide ((x + c) < N)))
    = update (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits c ((x + c) % N)))
                controlIdx true) flagIdx true := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_mod_lt_N : (x + c) % N < N := Nat.mod_lt _ hN_pos
  have h_mod_lt_2bits : (x + c) % N < 2^bits := by omega
  have h_c_lt_2bits : c < 2^bits := by omega
  have h_c_le_2bits : c ≤ 2^bits := by omega
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_ctrl_ne_flag : controlIdx ≠ flagIdx := by omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := h_ctrl_ne_flag.symm
  have h_target_bits_ne_ctrl : target_idx bits ≠ controlIdx := by
    unfold adder_n_qubits at hcontrolIdx; unfold target_idx; omega
  have h_target_bits_ne_flag : target_idx bits ≠ flagIdx := by
    unfold adder_n_qubits at h_flag_ge; unfold target_idx; omega
  -- Compute state values
  have h_state_ctrl : (update (update (adder_input_F (bits + 1) 0
                          (subConstPow2WideSpec bits c ((x + c) % N))) controlIdx true) flagIdx
                          (decide ((x + c) < N))) controlIdx = true := by
    rw [update_neq _ _ _ _ h_ctrl_ne_flag, update_eq]
  have h_target_bits_val : (subConstPow2WideSpec bits c ((x + c) % N)).testBit bits
                          = decide ((x + c) % N < c) :=
    subConstPow2WideSpec_high_bit bits c ((x + c) % N) h_c_le_2bits h_mod_lt_2bits
  have h_state_tbits : (update (update (adder_input_F (bits + 1) 0
                          (subConstPow2WideSpec bits c ((x + c) % N))) controlIdx true) flagIdx
                          (decide ((x + c) < N))) (target_idx bits) = decide ((x + c) % N < c) := by
    rw [update_neq _ _ _ _ h_target_bits_ne_flag, update_neq _ _ _ _ h_target_bits_ne_ctrl]
    unfold adder_input_F
    rw [show (target_idx bits) % 3 = 1 from by unfold target_idx; omega,
        show (target_idx bits) / 3 = bits from by unfold target_idx; omega]
    simp only [show decide (bits < bits + 1) = true from decide_eq_true (by omega), Bool.true_and]
    exact h_target_bits_val
  have h_state_flag : (update (update (adder_input_F (bits + 1) 0
                          (subConstPow2WideSpec bits c ((x + c) % N))) controlIdx true) flagIdx
                          (decide ((x + c) < N))) flagIdx = decide ((x + c) < N) := update_eq _ _ _
  -- Complementarity: decide ((x+c) < N) = !decide ((x+c)%N < c)
  have h_compl : decide ((x + c) < N) = !decide ((x + c) % N < c) := by
    by_cases h : x + c < N
    · rw [decide_eq_true h]
      have h_mod_eq : (x + c) % N = x + c := Nat.mod_eq_of_lt h
      rw [h_mod_eq, decide_eq_false (by omega : ¬ x + c < c)]
      rfl
    · rw [decide_eq_false h]
      have h_le : N ≤ x + c := by omega
      have h_lt : x + c < 2 * N := by omega
      have h_mod_eq : (x + c) % N = x + c - N := by
        have h_eq : x + c = (x + c - N) + N := by omega
        conv_lhs => rw [h_eq]
        rw [Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [h_mod_eq, decide_eq_true (by omega : x + c - N < c)]
      rfl
  -- Apply CCX
  rw [Gate.applyNat_CCX]
  rw [h_state_ctrl, h_state_tbits, h_state_flag]
  -- new flagIdx = decide((x+c)<N) XOR (true AND decide((x+c)%N<c)) = TRUE
  rw [h_compl]
  simp only [Bool.true_and]
  -- !b XOR b = true
  have h_xor : ∀ (b : Bool), ((!b) ^^ b) = true := fun b => by cases b <;> rfl
  rw [h_xor]
  -- Collapse double update at flagIdx (outer wins)
  have h_collapse : ∀ (f : Nat → Bool) (u v : Bool),
      update (update f flagIdx u) flagIdx v = update f flagIdx v := by
    intros f u v
    funext q
    by_cases hq : q = flagIdx
    · rw [hq, update_eq, update_eq]
    · rw [update_neq _ _ _ _ hq, update_neq _ _ _ _ hq, update_neq _ _ _ _ hq]
  rw [h_collapse]

/-- Intermediate: applying step 7 of controlled pipeline (controlled X
flipping flagIdx) takes flagIdx from `TRUE` to `FALSE`. -/
theorem controlled_step7_true
    (bits c x controlIdx flagIdx : Nat) (y : Nat)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (Gate.CX controlIdx flagIdx)
      (update (update (adder_input_F (bits + 1) 0 y) controlIdx true) flagIdx true)
    = update (update (adder_input_F (bits + 1) 0 y) controlIdx true) flagIdx false := by
  have h_ctrl_ne_flag : controlIdx ≠ flagIdx := by omega
  -- Compute state values
  have h_state_ctrl : (update (update (adder_input_F (bits + 1) 0 y) controlIdx true) flagIdx true)
                        controlIdx = true := by
    rw [update_neq _ _ _ _ h_ctrl_ne_flag, update_eq]
  have h_state_flag : (update (update (adder_input_F (bits + 1) 0 y) controlIdx true) flagIdx true)
                        flagIdx = true := update_eq _ _ _
  -- Apply CX
  rw [Gate.applyNat_CX]
  rw [h_state_ctrl, h_state_flag]
  -- new flagIdx = true XOR true = false
  show update (update (update (adder_input_F (bits + 1) 0 y) controlIdx true) flagIdx true)
        flagIdx (true ^^ true)
      = update (update (adder_input_F (bits + 1) 0 y) controlIdx true) flagIdx false
  rw [show (true ^^ true : Bool) = false from rfl]
  -- Collapse double update at flagIdx
  funext q
  by_cases hq : q = flagIdx
  · rw [hq, update_eq, update_eq]
  · rw [update_neq _ _ _ _ hq, update_neq _ _ _ _ hq, update_neq _ _ _ _ hq]

/-- Intermediate: applying step 8 of controlled pipeline (final
controlled add c) takes target from `subConstPow2WideSpec bits c
((x + c) % N)` to `(x + c) % N` via algebraic cancellation. -/
theorem controlled_step8_true
    (bits N c x controlIdx flagIdx : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (conditionalAddConstGate (bits + 1) c controlIdx)
      (update (update (adder_input_F (bits + 1) 0 (subConstPow2WideSpec bits c ((x + c) % N)))
                  controlIdx true) flagIdx false)
    = update (update (adder_input_F (bits + 1) 0 ((x + c) % N)) controlIdx true) flagIdx false := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have h_pow_succ_pos : 0 < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hbits' : 2 ≤ bits + 1 := by omega
  have hc_succ : c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_mod_lt_N : (x + c) % N < N := Nat.mod_lt _ hN_pos
  have h_mod_lt_2bits : (x + c) % N < 2^bits := by omega
  have h_mod_lt_pow : (x + c) % N < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_y_lt : subConstPow2WideSpec bits c ((x + c) % N) < 2^(bits+1) := by
    unfold subConstPow2WideSpec; exact Nat.mod_lt _ (by rw [h_pow_succ]; omega)
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := by omega
  -- Apply state_eq_with_outer
  rw [conditionalAddConstGate_state_eq_with_outer (bits + 1) c controlIdx flagIdx
        (subConstPow2WideSpec bits c ((x + c) % N)) true false
        hbits' hc_succ h_y_lt hcontrolIdx h_flag_ge h_flag_ne_ctrl]
  -- Now simplify: (subConstPow2WideSpec bits c ((x+c)%N) + c) % 2^(bits+1) = (x+c) % N
  congr 3
  show (subConstPow2WideSpec bits c ((x + c) % N) + c) % 2^(bits+1) = (x + c) % N
  unfold subConstPow2WideSpec
  rw [Nat.mod_add_mod]
  have h_eq : (x + c) % N + (2^(bits + 1) - c) + c = (x + c) % N + 2^(bits + 1) := by omega
  rw [h_eq, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt h_mod_lt_pow

/-- **Tick 6p HEADLINE — `controlBit = true` branch**.  When the
control bit is `true`, the full 8-step pipeline produces target =
`(x + c) % N` with all workspace restored. -/
theorem controlledModAddConstGate_correct_true
    (bits N c x : Nat) (controlIdx flagIdx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx)
      (update (adder_input_F (bits + 1) 0 x) controlIdx true)
    = update (adder_input_F (bits + 1) 0 ((x + c) % N)) controlIdx true := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have hc_succ : c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have hx_succ : x < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_xc_lt_pow : x + c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_flag_ge : adder_n_qubits (bits + 1) ≤ flagIdx := by omega
  have h_3_succ_flag : 3 * (bits + 1) ≤ flagIdx := by
    unfold adder_n_qubits at h_flag_ge; omega
  have h_ctrl_ne_flag : controlIdx ≠ flagIdx := by omega
  have h_flag_ne_ctrl : flagIdx ≠ controlIdx := h_ctrl_ne_flag.symm
  unfold controlledModAddConstGate
  rw [Gate.applyNat_seq]
  rw [controlled_step1_true bits c x controlIdx hbits hc_succ h_xc_lt_pow hx_succ hcontrolIdx]
  rw [Gate.applyNat_seq]
  rw [controlled_step2_true bits N c x controlIdx hbits hN_pos hN hx hc hcontrolIdx]
  rw [Gate.applyNat_seq]
  rw [controlled_step3_true bits N c x controlIdx flagIdx hbits hN_pos hN hx hc hcontrolIdx hflagIdx]
  rw [Gate.applyNat_seq]
  rw [controlled_step4_true bits N c x controlIdx flagIdx hbits hN_pos hN hx hc hcontrolIdx hflagIdx]
  rw [Gate.applyNat_seq]
  rw [controlled_step5_true bits N c x controlIdx flagIdx hbits hN_pos hN hx hc_pos hc
        hcontrolIdx hflagIdx]
  rw [Gate.applyNat_seq]
  rw [controlled_step6_true bits N c x controlIdx flagIdx hbits hN_pos hN hx hc_pos hc
        hcontrolIdx hflagIdx]
  rw [Gate.applyNat_seq]
  rw [controlled_step7_true bits c x controlIdx flagIdx
        (subConstPow2WideSpec bits c ((x + c) % N)) hcontrolIdx hflagIdx]
  rw [controlled_step8_true bits N c x controlIdx flagIdx hbits hN_pos hN hx hc_pos hc
        hcontrolIdx hflagIdx]
  -- Final state: update (update (ad-inp-F 0 ((x+c)%N)) controlIdx true) flagIdx false
  -- Need to simplify to: update (ad-inp-F 0 ((x+c)%N)) controlIdx true
  -- Swap order, then collapse the flagIdx-to-false update.
  rw [update_update_comm _ controlIdx flagIdx true false h_ctrl_ne_flag]
  rw [collapse_flag_false_update_at_high (bits + 1) flagIdx controlIdx ((x + c) % N) true
        h_3_succ_flag]

/-- **Tick 6 HEADLINE — full `controlledModAddConstGate_correct`**.
For any `controlBit`, the 8-step pipeline produces target =
`if controlBit then (x + c) % N else x` with all workspace restored. -/
theorem controlledModAddConstGate_correct
    (bits N c x : Nat) (controlBit : Bool) (controlIdx flagIdx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N)
    (hcontrolIdx : adder_n_qubits (bits + 1) ≤ controlIdx)
    (hflagIdx : controlIdx < flagIdx) :
    Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx)
      (update (adder_input_F (bits + 1) 0 x) controlIdx controlBit)
    = update (adder_input_F (bits + 1) 0 (if controlBit then (x + c) % N else x))
        controlIdx controlBit := by
  cases controlBit with
  | false =>
      show Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx)
            (update (adder_input_F (bits + 1) 0 x) controlIdx false)
          = update (adder_input_F (bits + 1) 0 x) controlIdx false
      exact controlledModAddConstGate_correct_false bits N c x controlIdx flagIdx
              hbits hN_pos hN hx hc_pos hc hcontrolIdx hflagIdx
  | true =>
      show Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx)
            (update (adder_input_F (bits + 1) 0 x) controlIdx true)
          = update (adder_input_F (bits + 1) 0 ((x + c) % N)) controlIdx true
      exact controlledModAddConstGate_correct_true bits N c x controlIdx flagIdx
              hbits hN_pos hN hx hc_pos hc hcontrolIdx hflagIdx

/-- `modMultConstGateAux ... 0 = Gate.I` by definition. -/
theorem modMultConstGateAux_zero (bits N a multBits : Nat) :
    modMultConstGateAux bits N a multBits 0 = Gate.I := rfl

/-- `modMultConstGate ... 0 = Gate.I` (zero-bit multiplier is the identity). -/
theorem modMultConstGate_zero (bits N a : Nat) :
    modMultConstGate bits N a 0 = Gate.I := rfl

/-- Recursive unfolding: `modMultConstGateAux ... (k+1)` is the seq of
the `k`-step and the controlled add at bit `k`. -/
theorem modMultConstGateAux_succ (bits N a multBits k : Nat) :
    modMultConstGateAux bits N a multBits (k + 1)
    = Gate.seq
        (modMultConstGateAux bits N a multBits k)
        (controlledModAddConstGate bits N ((a * 2^k) % N)
          (adder_n_qubits (bits + 1) + k)
          (adder_n_qubits (bits + 1) + multBits)) := rfl

/-- Well-typedness of the auxiliary gate at width
`adder_n_qubits (bits+1) + multBits + 1` for any `k ≤ multBits`. -/
theorem modMultConstGateAux_wellTyped
    (bits N a multBits k : Nat) (hbits : 1 ≤ bits) (hk : k ≤ multBits) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (modMultConstGateAux bits N a multBits k) := by
  induction k with
  | zero =>
      -- `modMultConstGateAux ... 0 = Gate.I`; WellTyped reduces to `0 < dim`.
      show Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1) Gate.I
      show 0 < adder_n_qubits (bits + 1) + multBits + 1
      omega
  | succ k ih =>
      have hk' : k ≤ multBits := by omega
      have ih' := ih hk'
      -- Step gate: controlledModAddConstGate at control = adder_n_qubits (bits+1) + k,
      -- flag = adder_n_qubits (bits+1) + multBits.
      have hctrl : adder_n_qubits (bits + 1) ≤ adder_n_qubits (bits + 1) + k := by omega
      have hflag : adder_n_qubits (bits + 1) + k < adder_n_qubits (bits + 1) + multBits := by
        have : k < multBits := by omega
        omega
      have h_step :
          Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
            (controlledModAddConstGate bits N ((a * 2^k) % N)
              (adder_n_qubits (bits + 1) + k)
              (adder_n_qubits (bits + 1) + multBits)) :=
        controlledModAddConstGate_wellTyped bits N ((a * 2^k) % N)
          (adder_n_qubits (bits + 1) + k)
          (adder_n_qubits (bits + 1) + multBits)
          hbits hctrl hflag
      show Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
        (Gate.seq (modMultConstGateAux bits N a multBits k) _)
      exact ⟨ih', h_step⟩

/-- **Well-typedness of `modMultConstGate`.** The full multiplier gate
is well-typed at width `adder_n_qubits (bits+1) + multBits + 1`
(adder block + `multBits` multiplier qubits + 1 flag qubit). -/
theorem modMultConstGate_wellTyped
    (bits N a multBits : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (modMultConstGate bits N a multBits) := by
  unfold modMultConstGate
  exact modMultConstGateAux_wellTyped bits N a multBits multBits hbits (le_refl _)

/-! #### Tick 7a — base cases and a commute lemma for the multiplier step. -/

/-- Base case: the zero-step multiplier auxiliary gate is identity. -/
theorem modMultConstGateAux_correct_zero
    (bits N a multBits : Nat) (f : Nat → Bool) :
    Gate.applyNat (modMultConstGateAux bits N a multBits 0) f = f := by
  show Gate.applyNat Gate.I f = f
  exact Gate.applyNat_I f

/-- Special case at `multBits = 0`: the full multiplier gate is identity
(no multiplier bits to control). -/
theorem modMultConstGate_correct_zero
    (bits N a : Nat) (f : Nat → Bool) :
    Gate.applyNat (modMultConstGate bits N a 0) f = f := by
  unfold modMultConstGate
  exact modMultConstGateAux_correct_zero bits N a 0 f

/-- State-level unfolding for the recursive step. -/
theorem modMultConstGateAux_apply_succ
    (bits N a multBits k : Nat) (f : Nat → Bool) :
    Gate.applyNat (modMultConstGateAux bits N a multBits (k + 1)) f
    = Gate.applyNat
        (controlledModAddConstGate bits N ((a * 2^k) % N)
          (adder_n_qubits (bits + 1) + k)
          (adder_n_qubits (bits + 1) + multBits))
        (Gate.applyNat (modMultConstGateAux bits N a multBits k) f) := by
  show Gate.applyNat (Gate.seq _ _) f = _
  exact Gate.applyNat_seq _ _ _

/-- **Commute lemma for `controlledModAddConstGate`.**  The gate commutes
with an `update _ p v` when `p` is outside the gate's read/write set:
`p ≥ adder_n_qubits (bits+1)` (above the adder block), `p ≠ controlIdx`,
and `p ≠ flagIdx`.  This is the key infrastructure for the inductive
multiplier correctness proof, where each iteration's gate must commute
past updates at OTHER multiplier-bit positions. -/
theorem controlledModAddConstGate_commute_update_outer
    (bits N c controlIdx flagIdx p : Nat) (v : Bool) (hbits : 1 ≤ bits)
    (hp_dim : adder_n_qubits (bits + 1) ≤ p)
    (h_p_ne_ctrl : p ≠ controlIdx) (h_p_ne_flag : p ≠ flagIdx) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx)
          (update f p v)
      = update (Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx) f)
          p v := by
  intro f
  have h2bits : 2 ≤ bits + 1 := by omega
  have h_p_ne_target : p ≠ target_idx bits := by
    unfold adder_n_qubits at hp_dim
    unfold target_idx
    omega
  -- Each sub-gate commutes with `update _ p v` because `p` is outside its support.
  have h_cond_ctrl : ∀ (cst : Nat) (f' : Nat → Bool),
      Gate.applyNat (conditionalAddConstGate (bits + 1) cst controlIdx) (update f' p v)
      = update (Gate.applyNat (conditionalAddConstGate (bits + 1) cst controlIdx) f') p v :=
    fun cst f' => conditionalAddConstGate_commute_update_outer (bits+1) cst controlIdx p v
      h2bits hp_dim h_p_ne_ctrl f'
  have h_cond_flag : ∀ (cst : Nat) (f' : Nat → Bool),
      Gate.applyNat (conditionalAddConstGate (bits + 1) cst flagIdx) (update f' p v)
      = update (Gate.applyNat (conditionalAddConstGate (bits + 1) cst flagIdx) f') p v :=
    fun cst f' => conditionalAddConstGate_commute_update_outer (bits+1) cst flagIdx p v
      h2bits hp_dim h_p_ne_flag f'
  have h_ccx : ∀ (f' : Nat → Bool),
      Gate.applyNat (Gate.CCX controlIdx (target_idx bits) flagIdx) (update f' p v)
      = update (Gate.applyNat (Gate.CCX controlIdx (target_idx bits) flagIdx) f') p v :=
    fun f' => applyNat_CCX_commute_update_disjoint controlIdx (target_idx bits) flagIdx f' p v
      h_p_ne_ctrl h_p_ne_target h_p_ne_flag
  have h_cx : ∀ (f' : Nat → Bool),
      Gate.applyNat (Gate.CX controlIdx flagIdx) (update f' p v)
      = update (Gate.applyNat (Gate.CX controlIdx flagIdx) f') p v :=
    fun f' => applyNat_CX_commute_update_disjoint controlIdx flagIdx f' p v
      h_p_ne_ctrl h_p_ne_flag
  show Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx) (update f p v)
      = update (Gate.applyNat (controlledModAddConstGate bits N c controlIdx flagIdx) f) p v
  -- Term-mode chain via applyNat_seq_commute_update across the 8-step composition.
  unfold controlledModAddConstGate
  exact applyNat_seq_commute_update _ _ _ _ _ (h_cond_ctrl c)
    (fun f1 => applyNat_seq_commute_update _ _ _ _ _ (h_cond_ctrl _)
      (fun f2 => applyNat_seq_commute_update _ _ _ _ _ h_ccx
        (fun f3 => applyNat_seq_commute_update _ _ _ _ _ (h_cond_flag N)
          (fun f4 => applyNat_seq_commute_update _ _ _ _ _ (h_cond_ctrl _)
            (fun f5 => applyNat_seq_commute_update _ _ _ _ _ h_ccx
              (fun f6 => applyNat_seq_commute_update _ _ _ _ _ h_cx
                (fun f7 => h_cond_ctrl c f7)))))))


end FormalRV.BQAlgo
