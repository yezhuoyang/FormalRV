/- CuccaroCleanModularAddCorrectness — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroCleanModularAddCorrectness.ControlledModAddRouteAndDesign

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Tick 68 — Stage helpers on `cuccaro_input_F` directly (with bridging). -/

/-- **Helper — `cuccaro_input_F` at `controlIdx` outside workspace is `false`.** -/
theorem cuccaro_input_F_at_controlIdx_outside_eq_false
    (bits x controlIdx : Nat) (hx : x < 2^bits)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx) :
    cuccaro_input_F 2 false 0 x controlIdx = false :=
  cuccaro_input_F_at_outside_eq_false 2 bits x controlIdx hcontrol_out hx

/-- **Helper — `update F controlIdx false = F` when F at controlIdx is false.** -/
theorem update_input_F_controlIdx_false_eq_F
    (bits x controlIdx : Nat) (hx : x < 2^bits)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx) :
    update (cuccaro_input_F 2 false 0 x) controlIdx false
      = cuccaro_input_F 2 false 0 x := by
  funext q
  by_cases hq : q = controlIdx
  · rw [hq, update_eq]
    exact (cuccaro_input_F_at_controlIdx_outside_eq_false bits x controlIdx hx hcontrol_out).symm
  · rw [update_neq _ _ _ _ hq]

/-! ## Tick 68 — Deliverable C: control=false candidate state_eq. -/

/-- **HEADLINE Deliverable C — control = false state equality for the
controlled mod-N add candidate.** -/
theorem sqir_style_controlledModAddConst_candidate_control_false_state_eq
    (bits N c x controlIdx : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
        (update (cuccaro_input_F 2 false 0 x) controlIdx false)
      = update (cuccaro_input_F 2 false 0 x) controlIdx false := by
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have h_F_at_ctrl : cuccaro_input_F 2 false 0 x controlIdx = false :=
    cuccaro_input_F_at_controlIdx_outside_eq_false bits x controlIdx h_x_lt hcontrol_out
  have h_input_eq : update (cuccaro_input_F 2 false 0 x) controlIdx false
                  = cuccaro_input_F 2 false 0 x :=
    update_input_F_controlIdx_false_eq_F bits x controlIdx h_x_lt hcontrol_out
  rw [h_input_eq]
  -- Now: applyNat candidate F = F.
  show Gate.applyNat
      (seq (sqir_conditionalAddConstGate bits 2 c controlIdx)
            (seq (sqir_style_compareConst_candidate bits 2 N 1)
                 (seq (sqir_conditionalSubConstGate bits 2 N 1)
                      (seq (sqir_controlledCompareConst bits 2 c controlIdx 1)
                           (Gate.CX controlIdx 1)))))
      (cuccaro_input_F 2 false 0 x) = _
  simp only [Gate.applyNat_seq]
  -- Hypothesis on controlIdx not being a read position.
  have h_control_distinct : ∀ i, i < bits → controlIdx ≠ 2 + 2 * i + 2 := by
    intros i _ heq
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  -- Stage 1: condAdd with input[controlIdx]=false → full_adder → identity on F.
  have h_stage1 : Gate.applyNat (sqir_conditionalAddConstGate bits 2 c controlIdx)
        (cuccaro_input_F 2 false 0 x) = cuccaro_input_F 2 false 0 x := by
    rw [sqir_conditionalAddConstGate_apply_false_fun bits 2 c controlIdx
          (cuccaro_input_F 2 false 0 x) h_control_distinct h_F_at_ctrl hcontrol_out]
    rw [← cuccaro_addConstGate_zero_eq_full_adder_fun]
    have h_pos : 0 < (2 : Nat)^bits := Nat.two_pow_pos bits
    rw [cuccaro_addConstGate_output_eq_cuccaro_input_F bits 2 0 x hbits h_pos h_x_lt
          (by omega : x + 0 < 2^bits)]
    simp [Nat.add_zero]
  rw [h_stage1]
  -- Stage 2: compareConst F = F (for x < N).
  rw [sqir_style_compareConst_candidate_on_input_F_x_lt_N_eq_id_fun bits N x hbits hN_pos hN hx]
  -- Stage 3: condSub with input[1]=false → full_adder → identity on F.
  have h_F_at_1 : cuccaro_input_F 2 false 0 x 1 = false := by
    unfold cuccaro_input_F; rw [if_pos (by omega : (1 : Nat) < 2)]
  have h_flag_distinct : ∀ i, i < bits → (1 : Nat) ≠ 2 + 2 * i + 2 := fun i _ => by omega
  have h_flag_out : (1 : Nat) < 2 ∨ 2 + 2 * bits + 1 ≤ 1 := Or.inl (by omega)
  have h_stage3 : Gate.applyNat (sqir_conditionalSubConstGate bits 2 N 1)
        (cuccaro_input_F 2 false 0 x) = cuccaro_input_F 2 false 0 x := by
    unfold sqir_conditionalSubConstGate
    rw [sqir_conditionalAddConstGate_apply_false_fun bits 2 (2^bits - N) 1
          (cuccaro_input_F 2 false 0 x) h_flag_distinct h_F_at_1 h_flag_out]
    rw [← cuccaro_addConstGate_zero_eq_full_adder_fun]
    have h_pos : 0 < (2 : Nat)^bits := Nat.two_pow_pos bits
    rw [cuccaro_addConstGate_output_eq_cuccaro_input_F bits 2 0 x hbits h_pos h_x_lt
          (by omega : x + 0 < 2^bits)]
    simp [Nat.add_zero]
  rw [h_stage3]
  -- Stage 4: ctrlCompare with input[controlIdx]=false → identity on F.
  -- Use Tick 67's theorem, bridging F ↔ update F controlIdx false.
  have h_stage4 : Gate.applyNat (sqir_controlledCompareConst bits 2 c controlIdx 1)
        (cuccaro_input_F 2 false 0 x) = cuccaro_input_F 2 false 0 x := by
    rw [show cuccaro_input_F 2 false 0 x
        = update (cuccaro_input_F 2 false 0 x) controlIdx false from h_input_eq.symm]
    exact sqir_controlledCompareConst_at_control_false_on_input_F_eq_id_fun
      bits 2 c controlIdx 1 x hbits h_x_lt h_control_distinct hcontrol_out
      (fun h => hcontrol_ne_flag h)
  rw [h_stage4]
  -- Stage 5: CX(controlIdx, 1) with state[controlIdx]=false → identity.
  exact Gate.applyNat_CX_at_control_false_eq_id_fun controlIdx 1
    (cuccaro_input_F 2 false 0 x) h_F_at_ctrl

/-! ## Tick 68 — Control = false target / workspace consequences. -/

/-- **Control=false target decode = x.** -/
theorem sqir_style_controlledModAddConst_candidate_target_decode_control_false
    (bits N c x controlIdx : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    cuccaro_target_val bits 2
        (Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx false))
      = x := by
  rw [sqir_style_controlledModAddConst_candidate_control_false_state_eq
        bits N c x controlIdx hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag]
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have h_eq : cuccaro_target_val bits 2
        (update (cuccaro_input_F 2 false 0 x) controlIdx false) = x % 2 ^ bits := by
    apply cuccaro_target_val_eq_sum_when_bits_match
    intro i hi
    have h_ne : (2 + 2 * i + 1 : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    exact cuccaro_input_F_at_b 2 i false 0 x
  rw [h_eq]
  exact Nat.mod_eq_of_lt h_x_lt


end FormalRV.BQAlgo
