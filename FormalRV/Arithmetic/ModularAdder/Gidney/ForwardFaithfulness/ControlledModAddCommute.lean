/- ForwardFaithfulness — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModularAdder.Gidney.ForwardFaithfulness.ConditionalAddStateEq

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

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
