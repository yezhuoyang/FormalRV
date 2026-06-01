import FormalRV.Arithmetic.RippleCarryAdder
import Mathlib.Data.Nat.Bitwise
import FormalRV.Arithmetic.ModularAdder.Defs
import FormalRV.Arithmetic.ModularAdder.Proofs2

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

/-! #### Tick 7b — multiplier-level commute lemma. -/

/-- **Commute lemma for `modMultConstGateAux`.**  At positions strictly
above the multiplier circuit's flag (i.e., `p > adder_n_qubits (bits+1)
+ multBits`), an `update _ p v` commutes through the full multiplier
auxiliary gate.  Proven directly via `applyNat_commute_update_above_dim`
applied to `modMultConstGateAux_wellTyped`. -/
theorem modMultConstGateAux_commute_update_outer
    (bits N a multBits k p : Nat) (v : Bool) (hbits : 1 ≤ bits)
    (hk : k ≤ multBits) (hp : adder_n_qubits (bits + 1) + multBits < p) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (modMultConstGateAux bits N a multBits k) (update f p v)
      = update (Gate.applyNat (modMultConstGateAux bits N a multBits k) f) p v := by
  intro f
  have h_wt := modMultConstGateAux_wellTyped bits N a multBits k hbits hk
  exact applyNat_commute_update_above_dim
    (adder_n_qubits (bits + 1) + multBits + 1)
    (modMultConstGateAux bits N a multBits k) h_wt f p v (by omega)

/-- **Commute lemma for `modMultConstGate`.**  Specialization of the
aux-level commute lemma at `k = multBits`. -/
theorem modMultConstGate_commute_update_outer
    (bits N a multBits p : Nat) (v : Bool) (hbits : 1 ≤ bits)
    (hp : adder_n_qubits (bits + 1) + multBits < p) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (modMultConstGate bits N a multBits) (update f p v)
      = update (Gate.applyNat (modMultConstGate bits N a multBits) f) p v := by
  intro f
  unfold modMultConstGate
  exact modMultConstGateAux_commute_update_outer bits N a multBits multBits p v
    hbits (le_refl _) hp f

/-- **`modMultConstGateAux` commute lemma at a multiplier-bit position.**
For positions in the multiplier-bit range
`p = adder_n_qubits (bits+1) + j` with `j < multBits` AND `j ≥ k`
(i.e., a multiplier bit that has NOT yet been touched by iterations
`0, 1, ..., k-1`), `update _ p v` commutes through
`modMultConstGateAux bits N a multBits k`.  Proven by induction on `k`,
using `controlledModAddConstGate_commute_update_outer` for the step. -/
theorem modMultConstGateAux_commute_update_mult_pos_above
    (bits N a multBits k j : Nat) (v : Bool) (hbits : 1 ≤ bits)
    (hk : k ≤ multBits) (hjk : k ≤ j) (hj : j < multBits) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (modMultConstGateAux bits N a multBits k)
          (update f (adder_n_qubits (bits + 1) + j) v)
      = update (Gate.applyNat (modMultConstGateAux bits N a multBits k) f)
          (adder_n_qubits (bits + 1) + j) v := by
  induction k with
  | zero =>
      intro f
      show Gate.applyNat Gate.I _ = update (Gate.applyNat Gate.I f) _ v
      rfl
  | succ k ih =>
      intro f
      have hk' : k ≤ multBits := by omega
      have hjk' : k ≤ j := by omega
      have h_step_ne_ctrl :
          adder_n_qubits (bits + 1) + j ≠ adder_n_qubits (bits + 1) + k := by omega
      have h_step_ne_flag :
          adder_n_qubits (bits + 1) + j ≠ adder_n_qubits (bits + 1) + multBits := by omega
      have h_p_dim :
          adder_n_qubits (bits + 1) ≤ adder_n_qubits (bits + 1) + j := by omega
      -- Unfold modMultConstGateAux at (k+1) on BOTH sides.
      simp only [modMultConstGateAux_apply_succ]
      -- Apply IH to the inner update on the LHS.
      rw [ih hk' hjk' f]
      -- Apply step commute to push update past the outer controlled-mod-add.
      exact controlledModAddConstGate_commute_update_outer bits N ((a * 2^k) % N)
              (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits)
              (adder_n_qubits (bits + 1) + j) v hbits h_p_dim h_step_ne_ctrl h_step_ne_flag
              (Gate.applyNat (modMultConstGateAux bits N a multBits k) f)

/-- Recursion unfolding for the aux at `i+1`. -/
theorem mult_input_F_aux_succ (bits multBits m i : Nat) (f : Nat → Bool) :
    mult_input_F_aux bits multBits m (i + 1) f
    = update (mult_input_F_aux bits multBits m i f)
             (adder_n_qubits (bits + 1) + i) (Nat.testBit m i) := rfl

/-- Decoder at multiplier-bit positions: `mult_input_F_aux ... i f` at
position `adder_n_qubits (bits+1) + j` returns `Nat.testBit m j`, when
`j < i` (i.e., bit `j` has been written by some iteration ≤ i-1). -/
theorem mult_input_F_aux_at_mult_pos
    (bits multBits m i j : Nat) (hj : j < i) (f : Nat → Bool) :
    mult_input_F_aux bits multBits m i f (adder_n_qubits (bits + 1) + j)
    = Nat.testBit m j := by
  induction i with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ i ih =>
      rw [mult_input_F_aux_succ]
      by_cases h_j_eq_i : j = i
      · subst h_j_eq_i
        exact update_eq _ _ _
      · have h_j_lt_i : j < i := by omega
        have h_ne : adder_n_qubits (bits + 1) + j ≠ adder_n_qubits (bits + 1) + i := by
          omega
        rw [update_neq _ _ _ _ h_ne]
        exact ih h_j_lt_i

/-- Decoder at non-multiplier positions: `mult_input_F_aux ... i f` at
position `p` outside the multiplier-bit range
`[adder_n_qubits (bits+1), adder_n_qubits (bits+1) + i)` equals `f p`. -/
theorem mult_input_F_aux_at_non_mult_pos
    (bits multBits m i p : Nat)
    (h_outside : p < adder_n_qubits (bits + 1) ∨ adder_n_qubits (bits + 1) + i ≤ p)
    (f : Nat → Bool) :
    mult_input_F_aux bits multBits m i f p = f p := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [mult_input_F_aux_succ]
      have h_outside_i : p < adder_n_qubits (bits + 1) ∨ adder_n_qubits (bits + 1) + i ≤ p := by
        rcases h_outside with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      have h_p_ne : p ≠ adder_n_qubits (bits + 1) + i := by
        rcases h_outside with h | h
        · omega
        · omega
      rw [update_neq _ _ _ _ h_p_ne]
      exact ih h_outside_i

/-- Top-level decoder at multiplier-bit position. -/
theorem mult_input_F_at_mult_pos
    (bits multBits x m j : Nat) (hj : j < multBits) :
    mult_input_F bits multBits x m (adder_n_qubits (bits + 1) + j)
    = Nat.testBit m j := by
  unfold mult_input_F
  exact mult_input_F_aux_at_mult_pos bits multBits m multBits j hj _

/-- Top-level decoder at non-multiplier positions: equal to
`adder_input_F (bits+1) 0 x`. -/
theorem mult_input_F_at_non_mult_pos
    (bits multBits x m p : Nat)
    (h_outside : p < adder_n_qubits (bits + 1)
                 ∨ adder_n_qubits (bits + 1) + multBits ≤ p) :
    mult_input_F bits multBits x m p = adder_input_F (bits + 1) 0 x p := by
  unfold mult_input_F
  exact mult_input_F_aux_at_non_mult_pos bits multBits m multBits p h_outside _

/-! #### Tick 7d — `mult_input_F` reordering (pulling out the k-th
multiplier update). -/

/-- `mult_input_F_aux` commutes with an `update _ (adder_n_qubits (bits+1) + j) v`
when `j ≥ i` (i.e., the iteration hasn't touched position `pos j` yet). -/
theorem mult_input_F_aux_commute_update_above
    (bits multBits m i j : Nat) (hj : i ≤ j) (v : Bool) (f : Nat → Bool) :
    mult_input_F_aux bits multBits m i (update f (adder_n_qubits (bits + 1) + j) v)
    = update (mult_input_F_aux bits multBits m i f)
             (adder_n_qubits (bits + 1) + j) v := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hj_succ : i ≤ j := by omega
      have h_ne_succ : adder_n_qubits (bits + 1) + i ≠ adder_n_qubits (bits + 1) + j := by
        have : i < j := by omega
        omega
      have h_ne_succ' : adder_n_qubits (bits + 1) + j ≠ adder_n_qubits (bits + 1) + i :=
        Ne.symm h_ne_succ
      rw [mult_input_F_aux_succ, ih hj_succ]
      rw [update_update_comm _ _ _ _ _ h_ne_succ']
      rw [← mult_input_F_aux_succ]

/-- **`mult_input_F` isolation at position `k`.**  For `k < multBits`,
the full multiplier-encoded input is equal to `mult_input_F_aux` at
iteration `multBits` applied to a base that already carries the k-th
multiplier update on `adder_input_F`.  The k-th iteration of the aux
overwrites position `adder_n_qubits (bits+1) + k` to the same value
(`Nat.testBit m k`), so the additional update is absorbed; outside the
multiplier range the update at `pos k` is transparent. -/
theorem mult_input_F_isolate_k
    (bits multBits x m k : Nat) (hk : k < multBits) :
    mult_input_F bits multBits x m
    = mult_input_F_aux bits multBits m multBits
        (update (adder_input_F (bits + 1) 0 x)
                (adder_n_qubits (bits + 1) + k) (Nat.testBit m k)) := by
  funext q
  unfold mult_input_F
  by_cases h_q_in : adder_n_qubits (bits + 1) ≤ q
                    ∧ q < adder_n_qubits (bits + 1) + multBits
  · -- q in the multiplier range: q = pos j for some j < multBits.
    obtain ⟨h_q_lo, h_q_hi⟩ := h_q_in
    obtain ⟨j, hj_eq⟩ : ∃ j, q = adder_n_qubits (bits + 1) + j :=
      ⟨q - adder_n_qubits (bits + 1), by omega⟩
    have hj : j < multBits := by omega
    rw [hj_eq]
    rw [mult_input_F_aux_at_mult_pos bits multBits m multBits j hj
         (adder_input_F (bits + 1) 0 x)]
    rw [mult_input_F_aux_at_mult_pos bits multBits m multBits j hj
         (update (adder_input_F (bits + 1) 0 x)
                 (adder_n_qubits (bits + 1) + k) (Nat.testBit m k))]
  · -- q outside the multiplier range: both sides reduce to the base function at q.
    have h_outside : q < adder_n_qubits (bits + 1)
                   ∨ adder_n_qubits (bits + 1) + multBits ≤ q := by
      by_cases h_lo : q < adder_n_qubits (bits + 1)
      · exact Or.inl h_lo
      · push_neg at h_lo
        exact Or.inr (by
          rcases Nat.lt_or_ge q (adder_n_qubits (bits + 1) + multBits) with h | h
          · exact absurd ⟨h_lo, h⟩ h_q_in
          · exact h)
    rw [mult_input_F_aux_at_non_mult_pos bits multBits m multBits q h_outside
         (adder_input_F (bits + 1) 0 x)]
    rw [mult_input_F_aux_at_non_mult_pos bits multBits m multBits q h_outside
         (update (adder_input_F (bits + 1) 0 x)
                 (adder_n_qubits (bits + 1) + k) (Nat.testBit m k))]
    -- Goal: adder_input_F ... q = (update (adder_input_F) (pos k) (testBit m k)) q.
    have h_q_ne_k : q ≠ adder_n_qubits (bits + 1) + k := by
      rcases h_outside with h | h
      · omega
      · omega
    rw [update_neq _ _ _ _ h_q_ne_k]

/-! #### Tick 7e — full single-step correctness on `mult_input_F`. -/

/-- Absorption lemma: when an outer `update` at the k-th multiplier
position rewrites a value that the inner aux-at-iteration-k already
carries (because the inner has `update f (pos k) (testBit m k)` as base
and aux at k doesn't touch pos k), the outer update is a no-op. -/
theorem mult_input_F_aux_absorb_at_k_position
    (bits multBits m k : Nat) (f : Nat → Bool) :
    mult_input_F_aux bits multBits m (k + 1)
        (update f (adder_n_qubits (bits + 1) + k) (Nat.testBit m k))
    = mult_input_F_aux bits multBits m k
        (update f (adder_n_qubits (bits + 1) + k) (Nat.testBit m k)) := by
  rw [mult_input_F_aux_succ]
  funext q
  by_cases hq : q = adder_n_qubits (bits + 1) + k
  · subst hq
    rw [update_eq]
    rw [mult_input_F_aux_at_non_mult_pos bits multBits m k
          (adder_n_qubits (bits + 1) + k) (Or.inr (le_refl _)) _]
    rw [update_eq]
  · rw [update_neq _ _ _ _ hq]

/-- Inductive helper for the single-step correctness on `mult_input_F`. -/
theorem CMAcg_on_mult_input_F_aux_iso
    (bits N c x m multBits k : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N) (hk : k < multBits) :
    ∀ i, i ≤ multBits →
    Gate.applyNat
      (controlledModAddConstGate bits N c
        (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits))
      (mult_input_F_aux bits multBits m i
        (update (adder_input_F (bits + 1) 0 x)
                (adder_n_qubits (bits + 1) + k) (Nat.testBit m k)))
    = mult_input_F_aux bits multBits m i
        (update (adder_input_F (bits + 1) 0
                  (if Nat.testBit m k then (x + c) % N else x))
                (adder_n_qubits (bits + 1) + k) (Nat.testBit m k)) := by
  intro i hi
  induction i with
  | zero =>
      have h_ctrl_ge_adder :
          adder_n_qubits (bits + 1) ≤ adder_n_qubits (bits + 1) + k := by omega
      have h_flag_ge_ctrl :
          adder_n_qubits (bits + 1) + k + 1 ≤ adder_n_qubits (bits + 1) + multBits := by omega
      show Gate.applyNat _ (update _ _ _) = update _ _ _
      exact controlledModAddConstGate_correct bits N c x
              (Nat.testBit m k)
              (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits)
              hbits hN_pos hN hx hc_pos hc h_ctrl_ge_adder (by omega)
  | succ i ih =>
      have hi' : i ≤ multBits := by omega
      have ih' := ih hi'
      by_cases hi_eq_k : i = k
      · -- Outer update at pos i = pos k is absorbed via the absorption lemma.
        subst hi_eq_k
        rw [mult_input_F_aux_absorb_at_k_position bits multBits m i
              (adder_input_F (bits + 1) 0 x)]
        rw [mult_input_F_aux_absorb_at_k_position bits multBits m i
              (adder_input_F (bits + 1) 0 (if Nat.testBit m i then (x + c) % N else x))]
        exact ih'
      · -- Pos i ≠ controlIdx and ≠ flagIdx. Commute CMAcg past the outer update.
        rw [mult_input_F_aux_succ]
        rw [mult_input_F_aux_succ]
        have h_pos_i_above_adder :
            adder_n_qubits (bits + 1) ≤ adder_n_qubits (bits + 1) + i := by omega
        have h_pos_i_ne_ctrl :
            adder_n_qubits (bits + 1) + i ≠ adder_n_qubits (bits + 1) + k := by
          intro h_eq; apply hi_eq_k; omega
        have h_pos_i_ne_flag :
            adder_n_qubits (bits + 1) + i ≠ adder_n_qubits (bits + 1) + multBits := by
          have : i < multBits := by omega
          omega
        rw [controlledModAddConstGate_commute_update_outer bits N c
              (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits)
              (adder_n_qubits (bits + 1) + i) (Nat.testBit m i) hbits
              h_pos_i_above_adder h_pos_i_ne_ctrl h_pos_i_ne_flag _]
        rw [ih']

/-- **Single-step correctness for `controlledModAddConstGate` on
`mult_input_F`.**  Applied to the multiplier-encoded input
`mult_input_F bits multBits x m`, the controlled modular-add gate
(controlled by the `k`-th multiplier qubit, with shared flag at
position `adder_n_qubits (bits+1) + multBits`) advances the adder's
target register from `x` to `(x + c) % N` when bit `k` of `m` is set,
or leaves it unchanged otherwise. -/
theorem controlledModAddConstGate_on_mult_input_F
    (bits N c x m multBits k : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N) (hk : k < multBits) :
    Gate.applyNat
      (controlledModAddConstGate bits N c
        (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits))
      (mult_input_F bits multBits x m)
    = mult_input_F bits multBits
        (if Nat.testBit m k then (x + c) % N else x) m := by
  rw [mult_input_F_isolate_k bits multBits x m k hk]
  rw [mult_input_F_isolate_k bits multBits
        (if Nat.testBit m k then (x + c) % N else x) m k hk]
  exact CMAcg_on_mult_input_F_aux_iso bits N c x m multBits k
          hbits hN_pos hN hx hc_pos hc hk multBits (le_refl _)

/-! #### Tick 7f — full multiplier correctness. -/

/-- **Bit decomposition for the next power of two.**
`m mod 2^(k+1) = m mod 2^k + (testBit m k as Nat) * 2^k`. -/
lemma m_mod_two_pow_succ_eq (m k : Nat) :
    m % 2^(k+1) = m % 2^k + (m / 2^k % 2) * 2^k := by
  have h_pow : 2^(k+1) = 2^k * 2 := by ring
  have h_pos : 0 < 2^k := Nat.two_pow_pos k
  have h_div_div : m / 2^(k+1) = m / 2^k / 2 := by
    rw [h_pow]; exact (Nat.div_div_eq_div_mul m (2^k) 2).symm
  have h1 : 2^k * (m / 2^k) + m % 2^k = m := Nat.div_add_mod m (2^k)
  have h2 : 2^(k+1) * (m / 2^(k+1)) + m % 2^(k+1) = m := Nat.div_add_mod m (2^(k+1))
  have h3 : 2 * (m / 2^k / 2) + m / 2^k % 2 = m / 2^k := Nat.div_add_mod (m / 2^k) 2
  have h2' : 2^k * 2 * (m / 2^k / 2) + m % 2^(k+1) = m := by
    rw [← h_pow, ← h_div_div]; exact h2
  nlinarith [h1, h2', h3, h_pos]

/-- **Inductive correctness for `modMultConstGateAux`.**  At iteration
`k ≤ multBits`, the aux gate has advanced the adder's target from `x`
to `(x + a * (m mod 2^k)) mod N`, given that each per-bit constant
`(a * 2^j) % N` is non-zero for `j < multBits`. -/
theorem modMultConstGateAux_correct
    (bits N a multBits x m : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N)
    (h_const_pos : ∀ j, j < multBits → 0 < (a * 2^j) % N) :
    ∀ k, k ≤ multBits →
    Gate.applyNat (modMultConstGateAux bits N a multBits k)
                  (mult_input_F bits multBits x m)
    = mult_input_F bits multBits ((x + a * (m % 2^k)) % N) m := by
  intro k hk
  induction k with
  | zero =>
      show Gate.applyNat Gate.I _ = _
      rw [Gate.applyNat_I]
      have h_mod : m % 2^0 = 0 := by rw [pow_zero]; exact Nat.mod_one m
      rw [h_mod, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hx]
  | succ k ih =>
      have hk' : k ≤ multBits := by omega
      have ih' := ih hk'
      rw [modMultConstGateAux_apply_succ, ih']
      have h_step_c_pos : 0 < (a * 2^k) % N := h_const_pos k (by omega)
      have h_step_c_lt : (a * 2^k) % N < N := Nat.mod_lt _ hN_pos
      have h_T_k_lt_N : (x + a * (m % 2^k)) % N < N := Nat.mod_lt _ hN_pos
      have hk_lt : k < multBits := by omega
      rw [controlledModAddConstGate_on_mult_input_F bits N ((a * 2^k) % N)
            ((x + a * (m % 2^k)) % N) m multBits k
            hbits hN_pos hN h_T_k_lt_N h_step_c_pos h_step_c_lt hk_lt]
      congr 1
      have h_decomp : m % 2^(k+1) = m % 2^k + (m / 2^k % 2) * 2^k :=
        m_mod_two_pow_succ_eq m k
      cases h_bit : Nat.testBit m k with
      | true =>
          have h_tb : (m / 2^k) % 2 = 1 := by
            rw [Nat.testBit_eq_decide_div_mod_eq] at h_bit
            exact of_decide_eq_true h_bit
          simp only [if_true]
          rw [h_decomp, h_tb, Nat.one_mul, Nat.mul_add]
          rw [show x + (a * (m % 2 ^ k) + a * 2 ^ k)
                = (x + a * (m % 2 ^ k)) + a * 2 ^ k from by ring]
          rw [← Nat.add_mod]
      | false =>
          have h_tb : (m / 2^k) % 2 = 0 := by
            rw [Nat.testBit_eq_decide_div_mod_eq] at h_bit
            have h := of_decide_eq_false h_bit
            omega
          rw [if_neg (by decide : ¬((false : Bool) = true))]
          rw [h_decomp, h_tb, Nat.zero_mul, Nat.add_zero]

/-- **Modular multiplier correctness.**  When `m < 2^multBits`, the
modular multiplier gate sends the adder's target from `x` to
`(x + a * m) mod N`, while preserving the multiplier register `m` and
the flag.  Equivalent form: each multiplier-bit `i` contributes
`(a * 2^i) mod N` to the target when set. -/
theorem modMultConstGate_correct
    (bits N a multBits x m : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N)
    (hm : m < 2^multBits)
    (h_const_pos : ∀ j, j < multBits → 0 < (a * 2^j) % N) :
    Gate.applyNat (modMultConstGate bits N a multBits)
                  (mult_input_F bits multBits x m)
    = mult_input_F bits multBits ((x + a * m) % N) m := by
  unfold modMultConstGate
  rw [modMultConstGateAux_correct bits N a multBits x m
        hbits hN_pos hN hx h_const_pos multBits (le_refl _)]
  rw [Nat.mod_eq_of_lt hm]

/-- Decoder at multiplier-bit positions. -/
theorem mult_state_init_at_mult_pos
    (bits multBits x j : Nat) (hj : j < multBits) :
    mult_state_init bits multBits x (adder_n_qubits (bits + 1) + j)
    = Nat.testBit x j := by
  unfold mult_state_init
  exact mult_input_F_at_mult_pos bits multBits 0 x j hj

/-- Decoder at non-multiplier positions: zero. -/
theorem mult_state_init_at_non_mult_pos
    (bits multBits x p : Nat)
    (h_outside : p < adder_n_qubits (bits + 1)
                 ∨ adder_n_qubits (bits + 1) + multBits ≤ p) :
    mult_state_init bits multBits x p = adder_input_F (bits + 1) 0 0 p := by
  unfold mult_state_init
  exact mult_input_F_at_non_mult_pos bits multBits 0 x p h_outside

/-- **Modular multiplier on the initial input state.**  When applied to
`mult_state_init bits multBits x` (multiplier register holds `x`,
adder zeroed), the gate produces a state whose adder-target register
encodes `(a * x) mod N` while the multiplier register `x` is
preserved.  Hypotheses ensure each per-bit constant `(a * 2^j) % N`
is positive (Shor's coprimality condition) and `x < 2^multBits`. -/
theorem modMultConstGate_on_init_correct
    (bits N a multBits x : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < 2^multBits)
    (h_const_pos : ∀ j, j < multBits → 0 < (a * 2^j) % N) :
    Gate.applyNat (modMultConstGate bits N a multBits)
                  (mult_state_init bits multBits x)
    = mult_input_F bits multBits ((a * x) % N) x := by
  unfold mult_state_init
  have h_0_lt_N : 0 < N := hN_pos
  rw [modMultConstGate_correct bits N a multBits 0 x
        hbits hN_pos hN (by omega) hx h_const_pos]
  congr 1
  rw [Nat.zero_add]

/-- **WellTyped corollary at the Shor-compatible dimension.**  Setting
`n := multBits` (the data register size) and `anc := adder_n_qubits
(bits+1) + 1` (the workspace including the flag), the modular
multiplier gate is well-typed at dimension `n + anc`, matching the
shape required by `encodeDataZeroAnc n anc` and
`MultiplyCircuitProperty a N n anc`. -/
theorem modMultConstGate_wellTyped_at_shor_dim
    (bits N a multBits : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
      (modMultConstGate bits N a multBits) := by
  have h := modMultConstGate_wellTyped bits N a multBits hbits
  -- adder_n_qubits (bits+1) + multBits + 1 = multBits + (adder_n_qubits (bits+1) + 1)
  have h_eq : adder_n_qubits (bits + 1) + multBits + 1
             = multBits + (adder_n_qubits (bits + 1) + 1) := by ring
  rw [← h_eq]
  exact h

/-- **WellTyped** for the step gate at the Shor-compatible dimension. -/
theorem f_modmult_step_gate_wellTyped
    (bits N a multBits i : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
      (f_modmult_step_gate bits N a multBits i) := by
  unfold f_modmult_step_gate
  exact modMultConstGate_wellTyped_at_shor_dim bits N (a^(2^i) % N) multBits hbits

/-- **WellTyped** at the original aux dimension. -/
theorem f_modmult_step_gate_wellTyped_aux
    (bits N a multBits i : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (f_modmult_step_gate bits N a multBits i) := by
  unfold f_modmult_step_gate
  exact modMultConstGate_wellTyped bits N (a^(2^i) % N) multBits hbits

/-- **Step correctness on the initial state.**  Applied to
`mult_state_init bits multBits x`, the step gate at iterate `i`
produces a state whose adder-target register holds `(a^(2^i) * x) % N`
while the multiplier register `x` is preserved.  Hypotheses ensure
each per-bit constant `((a^(2^i)) * 2^j) % N` is positive (the
analogue of Shor's coprimality condition for the squared base). -/
theorem f_modmult_step_gate_on_init_correct
    (bits N a multBits i x : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < 2^multBits)
    (h_const_pos :
      ∀ j, j < multBits → 0 < ((a^(2^i) % N) * 2^j) % N) :
    Gate.applyNat (f_modmult_step_gate bits N a multBits i)
                  (mult_state_init bits multBits x)
    = mult_input_F bits multBits ((a^(2^i) * x) % N) x := by
  unfold f_modmult_step_gate
  rw [modMultConstGate_on_init_correct bits N (a^(2^i) % N) multBits x
        hbits hN_pos hN hx h_const_pos]
  -- Goal: mult_input_F bits multBits ((a^(2^i) % N) * x % N) x
  --     = mult_input_F bits multBits ((a^(2^i) * x) % N) x
  congr 1
  -- ((a^(2^i) % N) * x) % N = (a^(2^i) * x) % N
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- **Family-level WellTyped.**  For every iterate `i`, the gate
`f_modmult_gate_family bits N a multBits i` is `Gate.WellTyped` at
the Shor-compatible dimension `n + anc = multBits +
(adder_n_qubits (bits+1) + 1)`. -/
theorem f_modmult_gate_family_wellTyped
    (bits N a multBits : Nat) (hbits : 1 ≤ bits) :
    ∀ i, Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
            (f_modmult_gate_family bits N a multBits i) := by
  intro i
  unfold f_modmult_gate_family
  exact f_modmult_step_gate_wellTyped bits N a multBits i hbits

/-- **Family-level out-of-place correctness on the initial state.**
For each iterate `i`, applied to `mult_state_init bits multBits x`,
the family member produces a state with adder-target register holding
`(a^(2^i) * x) mod N` and multiplier register `x` preserved. -/
theorem f_modmult_gate_family_on_init_correct
    (bits N a multBits : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (h_const_pos :
      ∀ i, ∀ j, j < multBits → 0 < ((a^(2^i) % N) * 2^j) % N) :
    ∀ i x, x < 2^multBits →
      Gate.applyNat (f_modmult_gate_family bits N a multBits i)
                    (mult_state_init bits multBits x)
      = mult_input_F bits multBits ((a^(2^i) * x) % N) x := by
  intro i x hx
  unfold f_modmult_gate_family
  exact f_modmult_step_gate_on_init_correct bits N a multBits i x
          hbits hN_pos hN hx (h_const_pos i)

/-- Well-typedness for `qubit_swap`. -/
theorem qubit_swap_wellTyped (dim a b : Nat)
    (ha : a < dim) (hb : b < dim) (hab : a ≠ b) :
    Gate.WellTyped dim (qubit_swap a b) := by
  refine ⟨⟨ha, hb, hab⟩, ⟨hb, ha, ?_⟩, ⟨ha, hb, hab⟩⟩
  exact fun h => hab h.symm

/-- **Boolean-state correctness for SWAP.**  Applied to `f`, the swap
gate produces a state with values at positions `a` and `b` exchanged. -/
theorem qubit_swap_correct (a b : Nat) (f : Nat → Bool) (hab : a ≠ b) :
    Gate.applyNat (qubit_swap a b) f
    = update (update f a (f b)) b (f a) := by
  unfold qubit_swap
  simp only [Gate.applyNat_seq, Gate.applyNat_CX]
  -- After unfolding, LHS is three nested updates with CX semantics:
  --   update (update (update f b (f b ⊕ f a)) a (...)) b (...)
  -- Evaluate the intermediate values that the inner CXs read.
  have hba : b ≠ a := Ne.symm hab
  -- After 1st CX(a,b): at position a still f a, at position b is f b ⊕ f a.
  have h_g1_a : update f b (xor (f b) (f a)) a = f a := update_neq _ _ _ _ hab
  have h_g1_b : update f b (xor (f b) (f a)) b = xor (f b) (f a) := update_eq _ _ _
  rw [h_g1_a, h_g1_b]
  -- After 2nd CX(b,a): writes (f a) ⊕ (f b ⊕ f a) = f b at position a.
  -- After 3rd CX(a,b): writes (intermediate at b) ⊕ (intermediate at a) at position b.
  have h_g2_a : update (update f b (xor (f b) (f a))) a (xor (f a) (xor (f b) (f a))) a
                = xor (f a) (xor (f b) (f a)) := update_eq _ _ _
  have h_g2_b : update (update f b (xor (f b) (f a))) a (xor (f a) (xor (f b) (f a))) b
                = xor (f b) (f a) := by
    rw [update_neq _ _ _ _ hba]; exact update_eq _ _ _
  rw [h_g2_b, h_g2_a]
  -- Now the LHS is fully expanded. Funext + case split on the queried position.
  funext q
  by_cases hqa : q = a
  · -- q = a: outer update at b (different), middle update at a (returns the xor expression).
    rw [hqa]
    rw [update_neq _ _ _ _ hab]
    rw [update_eq]
    -- RHS at a: update (update f a (f b)) b (f a) a = (update f a (f b)) a = f b.
    rw [update_neq _ _ _ _ hab]
    rw [update_eq]
    -- Goal: f a ⊕ (f b ⊕ f a) = f b. Boolean fact.
    cases h_fa : f a <;> cases h_fb : f b <;> rfl
  · by_cases hqb : q = b
    · -- q = b: outer update at b returns the xor expression.
      rw [hqb]
      rw [update_eq]
      -- RHS at b: f a.
      rw [update_eq]
      -- Goal: (f b ⊕ f a) ⊕ (f a ⊕ (f b ⊕ f a)) = f a. Boolean fact.
      cases h_fa : f a <;> cases h_fb : f b <;> rfl
    · -- q ≠ a, q ≠ b: all updates skip, both sides equal f q.
      rw [update_neq _ _ _ _ hqb]
      rw [update_neq _ _ _ _ hqa]
      rw [update_neq _ _ _ _ hqb]
      rw [update_neq _ _ _ _ hqb]
      rw [update_neq _ _ _ _ hqa]

/-- Recursion unfolding for `register_swap_aux`. -/
theorem register_swap_aux_succ
    (offsetA offsetB k : Nat) :
    register_swap_aux offsetA offsetB (k + 1)
    = Gate.seq (register_swap_aux offsetA offsetB k)
               (qubit_swap (offsetA + k) (offsetB + k)) := rfl

/-- **WellTyped for `register_swap_aux`.**  Requires non-empty
`dim`, both offset ranges fitting inside `dim`, and the two ranges
being disjoint. -/
theorem register_swap_aux_wellTyped
    (dim offsetA offsetB k : Nat) (hdim : 0 < dim)
    (hA : offsetA + k ≤ dim) (hB : offsetB + k ≤ dim)
    (h_disjoint : offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA) :
    Gate.WellTyped dim (register_swap_aux offsetA offsetB k) := by
  induction k with
  | zero =>
      show 0 < dim
      exact hdim
  | succ k ih =>
      have hA' : offsetA + k ≤ dim := by omega
      have hB' : offsetB + k ≤ dim := by omega
      have h_disjoint' :
          offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA := by
        rcases h_disjoint with h | h
        · left; omega
        · right; omega
      have h_ih := ih hA' hB' h_disjoint'
      have h_swap : Gate.WellTyped dim
          (qubit_swap (offsetA + k) (offsetB + k)) := by
        have hAk : offsetA + k < dim := by omega
        have hBk : offsetB + k < dim := by omega
        have hAk_ne_Bk : offsetA + k ≠ offsetB + k := by
          rcases h_disjoint with h | h
          · omega
          · omega
        exact qubit_swap_wellTyped dim (offsetA + k) (offsetB + k) hAk hBk hAk_ne_Bk
      show Gate.WellTyped dim
        (Gate.seq (register_swap_aux offsetA offsetB k) _)
      exact ⟨h_ih, h_swap⟩

/-- **WellTyped for `register_swap`.** -/
theorem register_swap_wellTyped
    (dim multBits offsetA offsetB : Nat) (hdim : 0 < dim)
    (hA : offsetA + multBits ≤ dim) (hB : offsetB + multBits ≤ dim)
    (h_disjoint : offsetA + multBits ≤ offsetB ∨ offsetB + multBits ≤ offsetA) :
    Gate.WellTyped dim (register_swap multBits offsetA offsetB) :=
  register_swap_aux_wellTyped dim offsetA offsetB multBits hdim hA hB h_disjoint

/-- **Correctness at "other" positions** of `register_swap_aux`.  At
any position outside both `[offsetA, offsetA + n)` and `[offsetB,
offsetB + n)`, the gate is identity. -/
theorem register_swap_aux_at_other
    (offsetA offsetB n : Nat) (f : Nat → Bool) (q : Nat)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA)
    (h_outside_A : q < offsetA ∨ offsetA + n ≤ q)
    (h_outside_B : q < offsetB ∨ offsetB + n ≤ q) :
    Gate.applyNat (register_swap_aux offsetA offsetB n) f q = f q := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have h_disjoint_k : offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA := by
        rcases h_disjoint with h | h
        · left; omega
        · right; omega
      have h_outside_A' : q < offsetA ∨ offsetA + k ≤ q := by
        rcases h_outside_A with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      have h_outside_B' : q < offsetB ∨ offsetB + k ≤ q := by
        rcases h_outside_B with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      have h_q_ne_Ak : q ≠ offsetA + k := by
        rcases h_outside_A with h | h
        · omega
        · omega
      have h_q_ne_Bk : q ≠ offsetB + k := by
        rcases h_outside_B with h | h
        · omega
        · omega
      have hAk_ne_Bk : offsetA + k ≠ offsetB + k := by
        rcases h_disjoint with h | h
        · omega
        · omega
      rw [register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      rw [update_neq _ _ _ _ h_q_ne_Bk]
      rw [update_neq _ _ _ _ h_q_ne_Ak]
      exact ih h_disjoint_k h_outside_A' h_outside_B'

/-- **Correctness at A positions**: at `offsetA + j` for `j < n`, the
gate returns `f (offsetB + j)`. -/
theorem register_swap_aux_at_A
    (offsetA offsetB n : Nat) (f : Nat → Bool) (j : Nat) (hj : j < n)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA) :
    Gate.applyNat (register_swap_aux offsetA offsetB n) f (offsetA + j)
    = f (offsetB + j) := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have h_disjoint_k : offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA := by
        rcases h_disjoint with h | h
        · left; omega
        · right; omega
      have hAk_ne_Bk : offsetA + k ≠ offsetB + k := by
        rcases h_disjoint with h | h
        · omega
        · omega
      rw [register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_neq _ _ _ _ (by omega : offsetA + k ≠ offsetB + k)]
        rw [update_eq]
        have h_outside_A_q : offsetB + k < offsetA ∨ offsetA + k ≤ offsetB + k := by
          rcases h_disjoint with h | h
          · right; omega
          · left; omega
        have h_outside_B_q : offsetB + k < offsetB ∨ offsetB + k ≤ offsetB + k := by
          right; omega
        exact register_swap_aux_at_other offsetA offsetB k f (offsetB + k)
                h_disjoint_k h_outside_A_q h_outside_B_q
      · have hj' : j < k := by omega
        have h_pos_A_ne_Bk : offsetA + j ≠ offsetB + k := by
          rcases h_disjoint with h | h
          · omega
          · omega
        have h_pos_A_ne_Ak : offsetA + j ≠ offsetA + k := by omega
        rw [update_neq _ _ _ _ h_pos_A_ne_Bk]
        rw [update_neq _ _ _ _ h_pos_A_ne_Ak]
        exact ih hj' h_disjoint_k

/-- **Correctness at B positions**: at `offsetB + j` for `j < n`, the
gate returns `f (offsetA + j)`. -/
theorem register_swap_aux_at_B
    (offsetA offsetB n : Nat) (f : Nat → Bool) (j : Nat) (hj : j < n)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA) :
    Gate.applyNat (register_swap_aux offsetA offsetB n) f (offsetB + j)
    = f (offsetA + j) := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have h_disjoint_k : offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA := by
        rcases h_disjoint with h | h
        · left; omega
        · right; omega
      have hAk_ne_Bk : offsetA + k ≠ offsetB + k := by
        rcases h_disjoint with h | h
        · omega
        · omega
      rw [register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_eq]
        have h_outside_A_q : offsetA + k < offsetA ∨ offsetA + k ≤ offsetA + k := by
          right; omega
        have h_outside_B_q : offsetA + k < offsetB ∨ offsetB + k ≤ offsetA + k := by
          rcases h_disjoint with h | h
          · left; omega
          · right; omega
        exact register_swap_aux_at_other offsetA offsetB k f (offsetA + k)
                h_disjoint_k h_outside_A_q h_outside_B_q
      · have hj' : j < k := by omega
        have h_pos_B_ne_Bk : offsetB + j ≠ offsetB + k := by omega
        have h_pos_B_ne_Ak : offsetB + j ≠ offsetA + k := by
          rcases h_disjoint with h | h
          · omega
          · omega
        rw [update_neq _ _ _ _ h_pos_B_ne_Bk]
        rw [update_neq _ _ _ _ h_pos_B_ne_Ak]
        exact ih hj' h_disjoint_k

/-! ### Tick 15 — Modular-inverse algebraic identities.

Two arithmetic facts about modular inverses that justify the third
stage of the in-place wrapper `OOPmul(a) ; SWAP ; OOPmul(N - a⁻¹)`:

(1) `ainv * (a*x mod N) mod N = x` — the modular inverse undoes the
    forward multiplication when `x < N` and `a * ainv ≡ 1 (mod N)`.

(2) `(x + (N - ainv) * (a*x mod N)) mod N = 0` — adding `(N - ainv) *
    (a*x mod N)` to `x` modular-cancels (where `N - ainv` plays the
    role of the additive inverse of `ainv` mod `N`).

Both are purely Nat arithmetic. -/

/-- **Modular-inverse "undo" identity.**  If `a * ainv ≡ 1 (mod N)`,
`x < N`, and `ainv < N`, then `ainv * (a*x mod N) mod N = x`. -/
theorem inv_mul_mod_eq_self (a ainv N x : Nat) (hN : 0 < N)
    (hx : x < N) (hainv : ainv < N) (h_inv : a * ainv % N = 1) :
    ainv * (a * x % N) % N = x := by
  -- Step 1: pull the inner `% N` out via Nat.mul_mod.
  have step : ainv * (a * x % N) % N = ainv * (a * x) % N := by
    conv_rhs => rw [Nat.mul_mod ainv (a * x) N]
    conv_lhs => rw [Nat.mul_mod ainv (a * x % N) N]
    rw [Nat.mod_mod]
  rw [step]
  -- Step 2: regroup and apply h_inv.
  rw [show ainv * (a * x) = (ainv * a) * x from by ring]
  rw [Nat.mul_mod (ainv * a) x N]
  rw [show ainv * a = a * ainv from Nat.mul_comm _ _]
  rw [h_inv, Nat.one_mul, Nat.mod_mod]
  exact Nat.mod_eq_of_lt hx

/-- **Modular cancellation by the additive-inverse-mod-N coefficient.**
If `a * ainv ≡ 1 (mod N)`, `x < N`, `ainv < N`, then
`(x + (N - ainv) * (a*x mod N)) mod N = 0`.  This is the algebraic
identity that justifies the third stage of the in-place modular
multiplier wrapper. -/
theorem mod_inv_cancel_identity (a ainv N x : Nat) (hN : 0 < N)
    (hx : x < N) (hainv : ainv < N) (h_inv : a * ainv % N = 1) :
    (x + (N - ainv) * (a * x % N)) % N = 0 := by
  have h1 := inv_mul_mod_eq_self a ainv N x hN hx hainv h_inv
  have hainv_le : ainv ≤ N := Nat.le_of_lt hainv
  set y := a * x % N with hy_def
  have h_sub : (N - ainv) * y = N * y - ainv * y := by rw [Nat.sub_mul]
  rw [h_sub]
  have h_le : ainv * y ≤ N * y := Nat.mul_le_mul_right _ hainv_le
  have h_add_sub : x + (N * y - ainv * y) = (x + N * y) - ainv * y := by omega
  rw [h_add_sub]
  -- ainv * y = N * (ainv * y / N) + (ainv * y % N) = N * (ainv * y / N) + x  (by h1)
  have h_ainv_y_decomp : ainv * y = N * (ainv * y / N) + x := by
    have := Nat.div_add_mod (ainv * y) N
    rw [h1] at this
    omega
  rw [h_ainv_y_decomp]
  have h_div_le : ainv * y / N ≤ y := by
    have h := Nat.div_le_div_right (c := N) h_le
    rw [Nat.mul_div_cancel_left _ hN] at h
    exact h
  have h_y_ge : N * (ainv * y / N) ≤ N * y := Nat.mul_le_mul_left N h_div_le
  -- (x + N*y - (N * (ainv*y / N) + x)) = N * y - N * (ainv*y / N) = N * (y - ainv*y/N).
  have h_collapse :
      (x + N * y - (N * (ainv * y / N) + x)) % N
      = (N * (y - ainv * y / N)) % N := by
    congr 1
    rw [Nat.mul_sub]
    omega
  rw [h_collapse]
  exact Nat.mul_mod_right _ _

/-- Recursion unfolding for `mult_target_swap_aux`. -/
theorem mult_target_swap_aux_succ (bits k : Nat) :
    mult_target_swap_aux bits (k + 1)
    = Gate.seq (mult_target_swap_aux bits k)
               (qubit_swap (adder_n_qubits (bits + 1) + k) (target_idx k)) := rfl

/-- **WellTyped for `mult_target_swap_aux`.**  At dimension
`adder_n_qubits (bits + 1) + multBits + 1` (Shor-compatible), each
constituent `qubit_swap (adder_n_qubits + k) (target_idx k)` is
well-typed when `k ≤ multBits ≤ bits + 1`. -/
theorem mult_target_swap_aux_wellTyped
    (bits multBits k : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) (hk : k ≤ multBits) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (mult_target_swap_aux bits k) := by
  induction k with
  | zero =>
      show 0 < adder_n_qubits (bits + 1) + multBits + 1
      unfold adder_n_qubits
      omega
  | succ k ih =>
      have hk' : k ≤ multBits := by omega
      have h_ih := ih hk'
      have hk_lt_multBits : k < multBits := by omega
      have h_swap : Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
          (qubit_swap (adder_n_qubits (bits + 1) + k) (target_idx k)) := by
        apply qubit_swap_wellTyped
        · -- adder_n_qubits + k < dim = adder_n_qubits + multBits + 1
          omega
        · -- target_idx k = 3*k + 1 < dim.  k ≤ multBits ≤ bits + 1, so
          -- 3*k + 1 ≤ 3*(bits + 1) + 1 < 3*(bits + 1) + 2 = adder_n_qubits.
          unfold target_idx adder_n_qubits
          omega
        · -- adder_n_qubits + k ≠ target_idx k:  RHS ≤ 3*bits + 1 < adder_n_qubits + 0 ≤ LHS.
          unfold target_idx adder_n_qubits
          omega
      show Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
        (Gate.seq (mult_target_swap_aux bits k) _)
      exact ⟨h_ih, h_swap⟩

/-- **WellTyped for `mult_target_swap`.** -/
theorem mult_target_swap_wellTyped
    (bits multBits : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (mult_target_swap bits multBits) :=
  mult_target_swap_aux_wellTyped bits multBits multBits hbits h_multBits_le
    (le_refl _)

/-- **WellTyped for `modMultInPlace`.** -/
theorem modMultInPlace_wellTyped
    (bits N a ainv multBits : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (modMultInPlace bits N a ainv multBits) := by
  unfold modMultInPlace
  refine ⟨?_, ?_, ?_⟩
  · exact modMultConstGate_wellTyped bits N a multBits hbits
  · exact mult_target_swap_wellTyped bits multBits hbits h_multBits_le
  · exact modMultConstGate_wellTyped bits N ((N - ainv) % N) multBits hbits

/-- **In-place WellTyped at the Shor-compatible dimension.** -/
theorem modMultInPlace_wellTyped_at_shor_dim
    (bits N a ainv multBits : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) :
    Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
      (modMultInPlace bits N a ainv multBits) := by
  have h := modMultInPlace_wellTyped bits N a ainv multBits hbits h_multBits_le
  have h_eq : adder_n_qubits (bits + 1) + multBits + 1
             = multBits + (adder_n_qubits (bits + 1) + 1) := by ring
  rw [← h_eq]
  exact h

/-! ### Tick 17 — Position-level correctness for `mult_target_swap_aux`. -/

/-- **At-other for `mult_target_swap_aux`.**  If `q` is not equal to
any swap-paired position (multiplier-side or target-side) up to
iteration `n`, then the gate is identity at `q`.  Requires
`n ≤ bits + 1` to ensure each swap-pair has distinct positions. -/
theorem mult_target_swap_aux_at_other
    (bits n : Nat) (f : Nat → Bool) (q : Nat)
    (h_n_le : n ≤ bits + 1)
    (h_outside : ∀ k, k < n →
      q ≠ adder_n_qubits (bits + 1) + k ∧ q ≠ target_idx k) :
    Gate.applyNat (mult_target_swap_aux bits n) f q = f q := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have h_n_le' : k ≤ bits + 1 := by omega
      have h_outside_k : ∀ j, j < k →
          q ≠ adder_n_qubits (bits + 1) + j ∧ q ≠ target_idx j := by
        intro j hj; exact h_outside j (by omega)
      have h_q_ne_Ak : q ≠ adder_n_qubits (bits + 1) + k :=
        (h_outside k (by omega)).1
      have h_q_ne_Tk : q ≠ target_idx k :=
        (h_outside k (by omega)).2
      have hk_le_bits : k ≤ bits := by omega
      have h_Ak_ne_Tk : adder_n_qubits (bits + 1) + k ≠ target_idx k := by
        show 3 * (bits + 1) + 2 + k ≠ 3 * k + 1
        omega
      rw [mult_target_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ h_Ak_ne_Tk]
      rw [update_neq _ _ _ _ h_q_ne_Tk]
      rw [update_neq _ _ _ _ h_q_ne_Ak]
      exact ih h_n_le' h_outside_k

/-- **At multiplier-side position**: at `adder_n_qubits + j` for
`j < n`, the gate returns `f (target_idx j)`.  Requires
`n ≤ bits + 1`. -/
theorem mult_target_swap_aux_at_mult
    (bits n : Nat) (f : Nat → Bool) (j : Nat) (hj : j < n)
    (h_n_le : n ≤ bits + 1) :
    Gate.applyNat (mult_target_swap_aux bits n) f
      (adder_n_qubits (bits + 1) + j)
    = f (target_idx j) := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have h_n_le' : k ≤ bits + 1 := by omega
      have hk_le_bits : k ≤ bits := by omega
      have h_Ak_ne_Tk : adder_n_qubits (bits + 1) + k ≠ target_idx k := by
        show 3 * (bits + 1) + 2 + k ≠ 3 * k + 1
        omega
      rw [mult_target_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ h_Ak_ne_Tk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_neq _ _ _ _ h_Ak_ne_Tk]
        rw [update_eq]
        apply mult_target_swap_aux_at_other bits k f (target_idx k) h_n_le'
        intro k' hk'
        have hk'_le_bits : k' ≤ bits := by omega
        refine ⟨?_, ?_⟩
        · show target_idx k ≠ adder_n_qubits (bits + 1) + k'
          show 3 * k + 1 ≠ 3 * (bits + 1) + 2 + k'
          omega
        · show target_idx k ≠ target_idx k'
          show 3 * k + 1 ≠ 3 * k' + 1
          omega
      · have hj' : j < k := by omega
        have hj_le_bits : j ≤ bits := by omega
        have h_pos_Aj_ne_Tk : adder_n_qubits (bits + 1) + j ≠ target_idx k := by
          show 3 * (bits + 1) + 2 + j ≠ 3 * k + 1
          omega
        have h_pos_Aj_ne_Ak : adder_n_qubits (bits + 1) + j
                             ≠ adder_n_qubits (bits + 1) + k := by omega
        rw [update_neq _ _ _ _ h_pos_Aj_ne_Tk]
        rw [update_neq _ _ _ _ h_pos_Aj_ne_Ak]
        exact ih hj' h_n_le'

/-- **At target-side position**: at `target_idx j` for `j < n`, the
gate returns `f (adder_n_qubits + j)`.  Requires `n ≤ bits + 1`. -/
theorem mult_target_swap_aux_at_target
    (bits n : Nat) (f : Nat → Bool) (j : Nat) (hj : j < n)
    (h_n_le : n ≤ bits + 1) :
    Gate.applyNat (mult_target_swap_aux bits n) f (target_idx j)
    = f (adder_n_qubits (bits + 1) + j) := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have h_n_le' : k ≤ bits + 1 := by omega
      have hk_le_bits : k ≤ bits := by omega
      have h_Ak_ne_Tk : adder_n_qubits (bits + 1) + k ≠ target_idx k := by
        show 3 * (bits + 1) + 2 + k ≠ 3 * k + 1
        omega
      rw [mult_target_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ h_Ak_ne_Tk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_eq]
        apply mult_target_swap_aux_at_other bits k f
          (adder_n_qubits (bits + 1) + k) h_n_le'
        intro k' hk'
        have hk'_le_bits : k' ≤ bits := by omega
        refine ⟨?_, ?_⟩
        · show adder_n_qubits (bits + 1) + k ≠ adder_n_qubits (bits + 1) + k'
          omega
        · show adder_n_qubits (bits + 1) + k ≠ target_idx k'
          show 3 * (bits + 1) + 2 + k ≠ 3 * k' + 1
          omega
      · have hj' : j < k := by omega
        have hj_le_bits : j ≤ bits := by omega
        have h_pos_Tj_ne_Tk : target_idx j ≠ target_idx k := by
          show 3 * j + 1 ≠ 3 * k + 1
          omega
        have h_pos_Tj_ne_Ak : target_idx j ≠ adder_n_qubits (bits + 1) + k := by
          show 3 * j + 1 ≠ 3 * (bits + 1) + 2 + k
          omega
        rw [update_neq _ _ _ _ h_pos_Tj_ne_Tk]
        rw [update_neq _ _ _ _ h_pos_Tj_ne_Ak]
        exact ih hj' h_n_le'

end FormalRV.BQAlgo
