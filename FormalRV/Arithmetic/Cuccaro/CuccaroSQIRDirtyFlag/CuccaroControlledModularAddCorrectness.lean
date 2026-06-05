import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRCondAdd
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroModularAddDefinitions
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroCleanModularAddCorrectness

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Tick 69 — Control preservation helpers + control=true work. -/

/-- **Deliverable A — addConstGate preserves any outside-workspace position.** -/
theorem cuccaro_addConstGate_preserves_outside_workspace_at
    (bits q_start c controlIdx : Nat) (g : Nat → Bool)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    Gate.applyNat (cuccaro_addConstGate bits q_start c) g controlIdx = g controlIdx := by
  have h_self : update g controlIdx (g controlIdx) = g := update_self g controlIdx
  conv_lhs => rw [← h_self]
  exact cuccaro_addConstGate_preserves_outside_workspace bits q_start c controlIdx
    (g controlIdx) g h_control_out

/-- **Deliverable C — conditionalAddConstGate preserves outside-workspace
position (when distinct from read positions and flag position).** -/
theorem sqir_conditionalAddConstGate_preserves_outside
    (bits q_start c flagPos controlIdx : Nat) (g : Nat → Bool)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    Gate.applyNat (sqir_conditionalAddConstGate bits q_start c flagPos) g controlIdx
      = g controlIdx := by
  show Gate.applyNat
      (seq (sqir_prepareMaskedConstRead bits q_start c flagPos)
            (seq (cuccaro_n_bit_adder_full bits q_start)
                 (sqir_prepareMaskedConstRead bits q_start c flagPos))) g controlIdx = _
  simp only [Gate.applyNat_seq]
  rw [sqir_prepareMaskedConstRead_at_other bits q_start c flagPos controlIdx
        h_control_distinct]
  rcases h_control_out with h_below | h_above
  · rw [cuccaro_n_bit_adder_full_frame_below bits q_start _ controlIdx h_below]
    exact sqir_prepareMaskedConstRead_at_other bits q_start c flagPos controlIdx
      h_control_distinct g
  · rw [cuccaro_n_bit_adder_full_frame_above bits q_start _ controlIdx h_above]
    exact sqir_prepareMaskedConstRead_at_other bits q_start c flagPos controlIdx
      h_control_distinct g

/-- **conditionalSubConstGate preserves outside-workspace position.** -/
theorem sqir_conditionalSubConstGate_preserves_outside
    (bits q_start N flagPos controlIdx : Nat) (g : Nat → Bool)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) g controlIdx
      = g controlIdx := by
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_preserves_outside bits q_start (2^bits - N)
    flagPos controlIdx g h_control_distinct h_control_out

/-- **`sqir_controlledCompareConst` preserves outside-workspace position
(when distinct from read positions and flagPos).** -/
theorem sqir_controlledCompareConst_preserves_control_outside
    (bits q_start c controlIdx flagPos : Nat) (g : Nat → Bool)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (h_control_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos) g controlIdx
      = g controlIdx := by
  show Gate.applyNat
      (seq (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)))))
      g controlIdx = _
  simp only [Gate.applyNat_seq]
  rw [sqir_prepareMaskedConstRead_at_other bits q_start (2^bits - c) controlIdx
        controlIdx h_control_distinct]
  rcases h_control_out with h_below | h_above
  · rw [cuccaro_maj_chain_inv_frame_below bits q_start _ controlIdx h_below]
    rw [Gate.applyNat_CX, update_neq _ _ _ _ h_control_ne_flag]
    rw [cuccaro_maj_chain_frame_below bits q_start _ controlIdx h_below]
    exact sqir_prepareMaskedConstRead_at_other bits q_start (2^bits - c) controlIdx
      controlIdx h_control_distinct g
  · rw [cuccaro_maj_chain_inv_frame_above bits q_start _ controlIdx h_above]
    rw [Gate.applyNat_CX, update_neq _ _ _ _ h_control_ne_flag]
    rw [cuccaro_maj_chain_frame_above bits q_start _ controlIdx h_above]
    exact sqir_prepareMaskedConstRead_at_other bits q_start (2^bits - c) controlIdx
      controlIdx h_control_distinct g

/-- **Partial Deliverable D — control bit is preserved through the controlled
mod-N add candidate.** -/
theorem sqir_style_controlledModAddConst_candidate_preserves_control
    (bits N c x controlIdx : Nat) (control : Bool)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
        (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx
      = control := by
  have h_control_distinct : ∀ i, i < bits → controlIdx ≠ 2 + 2 * i + 2 := by
    intros i _ heq
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  show Gate.applyNat
      (seq (sqir_conditionalAddConstGate bits 2 c controlIdx)
            (seq (sqir_style_compareConst_candidate bits 2 N 1)
                 (seq (sqir_conditionalSubConstGate bits 2 N 1)
                      (seq (sqir_controlledCompareConst bits 2 c controlIdx 1)
                           (Gate.CX controlIdx 1)))))
      _ controlIdx = _
  simp only [Gate.applyNat_seq]
  -- Stage 5 (CX controlIdx 1): controlIdx ≠ 1 → CX doesn't modify controlIdx.
  rw [Gate.applyNat_CX, update_neq _ _ _ _ hcontrol_ne_flag]
  -- Stage 4 (ctrlCompare): preserves controlIdx.
  rw [sqir_controlledCompareConst_preserves_control_outside bits 2 c controlIdx 1
        _ h_control_distinct hcontrol_out hcontrol_ne_flag]
  -- Stage 3 (condSub): preserves controlIdx.
  rw [sqir_conditionalSubConstGate_preserves_outside bits 2 N 1 controlIdx
        _ h_control_distinct hcontrol_out]
  -- Stage 2 (compareConst N): preserves controlIdx via frame_outside.
  rw [sqir_style_compareConst_candidate_frame_outside bits 2 N 1 _ controlIdx
        hcontrol_ne_flag hcontrol_out]
  -- Stage 1 (condAdd c controlIdx): the controlled add preserves its own flagPos = controlIdx.
  exact sqir_conditionalAddConstGate_flag_preserved bits 2 c x controlIdx control
    h_control_distinct hcontrol_out

/-! ## Tick 70 — X/CX commute helpers for locality (Deliverable A precursors).

The full clean_candidate locality requires per-stage commute lemmas
(addConst, compareConst, condSub, compareConst, X).  This tick lands
the easy two (X, CX); the compareConst and conditionalAdd commutes
plus the full clean_candidate locality + state_eq for control=true
are deferred to Tick 71. -/

/-- **X commute with update at outside position.** -/
theorem Gate.applyNat_X_commute_update_outside_fun
    (target controlIdx : Nat) (v : Bool) (f : Nat → Bool) (h : controlIdx ≠ target) :
    Gate.applyNat (Gate.X target) (update f controlIdx v)
      = update (Gate.applyNat (Gate.X target) f) controlIdx v := by
  simp only [Gate.applyNat_X]
  rw [update_neq _ _ _ _ (fun heq => h heq.symm)]
  exact (update_comm f target controlIdx (! f target) v (fun heq => h heq.symm)).symm

/-- **CX commute with update at outside position (≠ control and ≠ target).** -/
theorem Gate.applyNat_CX_commute_update_outside_fun
    (control target controlIdx : Nat) (v : Bool) (f : Nat → Bool)
    (h_ne_control : controlIdx ≠ control) (h_ne_target : controlIdx ≠ target) :
    Gate.applyNat (Gate.CX control target) (update f controlIdx v)
      = update (Gate.applyNat (Gate.CX control target) f) controlIdx v := by
  simp only [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ (fun heq => h_ne_target heq.symm)]
  rw [update_neq _ _ _ _ (fun heq => h_ne_control heq.symm)]
  exact (update_comm f target controlIdx _ v (fun heq => h_ne_target heq.symm)).symm

/-! ## Tick 71 — Locality stack for controlled mod-N add. -/

/-- **Deliverable A — masked prepare commutes with `update` at outside position.** -/
theorem sqir_prepareMaskedConstRead_commute_update_outside_workspace
    (bits q_start N flagPos controlIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) (update f controlIdx v)
      = update (Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f)
              controlIdx v := by
  induction bits generalizing f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat
        (seq (sqir_prepareMaskedConstRead k q_start N flagPos)
              (cond (N.testBit k) (Gate.CX flagPos (q_start + 2 * k + 2)) Gate.I))
        (update f controlIdx v)
      = update (Gate.applyNat
                  (seq (sqir_prepareMaskedConstRead k q_start N flagPos)
                        (cond (N.testBit k) (Gate.CX flagPos (q_start + 2 * k + 2)) Gate.I))
                  f) controlIdx v
    simp only [Gate.applyNat_seq]
    have h_ctrl_out_k : controlIdx < q_start ∨ q_start + 2 * k + 1 ≤ controlIdx := by
      rcases hcontrol_out with hl | hr
      · left; exact hl
      · right; omega
    rw [ih f h_ctrl_out_k]
    cases h_c : N.testBit k with
    | false =>
      simp only [cond_false, Gate.applyNat_I]
    | true =>
      simp only [cond_true]
      have h_ctrl_ne_read : controlIdx ≠ q_start + 2 * k + 2 := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      exact Gate.applyNat_CX_commute_update_outside_fun flagPos (q_start + 2 * k + 2)
        controlIdx v _ hcontrol_ne_flag h_ctrl_ne_read

/-- **Function-level commute for `cuccaro_maj_chain_inv`.**  Lifts the
existing position-level theorem to a function equality. -/
theorem cuccaro_maj_chain_inv_commute_update_outside_workspace_fun
    (bits q_start flagPos : Nat) (v : Bool) (f : Nat → Bool)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (cuccaro_maj_chain_inv bits q_start) (update f flagPos v)
      = update (Gate.applyNat (cuccaro_maj_chain_inv bits q_start) f) flagPos v := by
  funext p
  by_cases hp_in_workspace : q_start ≤ p ∧ p < q_start + 2 * bits + 1
  · have h := cuccaro_maj_chain_inv_commute_update_outside_workspace bits q_start flagPos v f
      hflag_out p hp_in_workspace.1 hp_in_workspace.2
    rw [h]
    have hp_ne_flag : p ≠ flagPos := by
      rcases hflag_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ hp_ne_flag]
  · push_neg at hp_in_workspace
    have hp_outside : p < q_start ∨ q_start + 2 * bits + 1 ≤ p := by
      by_cases h : p < q_start
      · left; exact h
      · push_neg at h; right; exact hp_in_workspace h
    rcases hp_outside with hp_below | hp_above
    · rw [cuccaro_maj_chain_inv_frame_below bits q_start (update f flagPos v) p hp_below]
      by_cases hp_flag : p = flagPos
      · rw [hp_flag, update_eq, update_eq]
      · rw [update_neq _ _ _ _ hp_flag, update_neq _ _ _ _ hp_flag]
        exact (cuccaro_maj_chain_inv_frame_below bits q_start f p hp_below).symm
    · rw [cuccaro_maj_chain_inv_frame_above bits q_start (update f flagPos v) p hp_above]
      by_cases hp_flag : p = flagPos
      · rw [hp_flag, update_eq, update_eq]
      · rw [update_neq _ _ _ _ hp_flag, update_neq _ _ _ _ hp_flag]
        exact (cuccaro_maj_chain_inv_frame_above bits q_start f p hp_above).symm

/-- **Deliverable B — comparator commutes with `update` at outside position.** -/
theorem sqir_style_compareConst_candidate_commute_update_outside_fun
    (bits q_start N flagPos controlIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (update f controlIdx v)
      = update (Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos) f)
              controlIdx v := by
  unfold sqir_style_compareConst_candidate
  simp only [Gate.applyNat_seq]
  have h_ctrl_ne_top : controlIdx ≠ q_start + 2 * bits := by
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  rw [cuccaro_prepareConstRead_commute_update_outside_workspace bits q_start (2^bits - N)
        controlIdx v f hcontrol_out]
  rw [cuccaro_maj_chain_commute_update_outside_workspace bits q_start controlIdx v _ hcontrol_out]
  rw [Gate.applyNat_CX_commute_update_outside_fun (q_start + 2 * bits) flagPos controlIdx v _
        h_ctrl_ne_top hcontrol_ne_flag]
  rw [cuccaro_maj_chain_inv_commute_update_outside_workspace_fun bits q_start controlIdx v _
        hcontrol_out]
  rw [cuccaro_prepareConstRead_commute_update_outside_workspace bits q_start (2^bits - N)
        controlIdx v _ hcontrol_out]

/-- **Deliverable C — conditionalAdd commutes with `update` at outside position.** -/
theorem sqir_conditionalAddConstGate_commute_update_outside_fun
    (bits q_start N flagPos controlIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos) (update f controlIdx v)
      = update (Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos) f)
              controlIdx v := by
  unfold sqir_conditionalAddConstGate
  simp only [Gate.applyNat_seq]
  rw [sqir_prepareMaskedConstRead_commute_update_outside_workspace bits q_start N flagPos
        controlIdx v f hcontrol_out hcontrol_ne_flag]
  rw [cuccaro_n_bit_adder_full_commute_update_outside_workspace bits q_start controlIdx v _
        hcontrol_out]
  rw [sqir_prepareMaskedConstRead_commute_update_outside_workspace bits q_start N flagPos
        controlIdx v _ hcontrol_out hcontrol_ne_flag]

/-- **Deliverable C — conditionalSub commutes with `update` at outside position.** -/
theorem sqir_conditionalSubConstGate_commute_update_outside_fun
    (bits q_start N flagPos controlIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) (update f controlIdx v)
      = update (Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f)
              controlIdx v := by
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_commute_update_outside_fun bits q_start (2^bits - N)
    flagPos controlIdx v f hcontrol_out hcontrol_ne_flag

/-- **R7d^xxix-L-3.10′ helper: q_start-parametric clean modadd
candidate commutes with `update` at controlIdx outside workspace ∪
{flagPos}.**

q_start-parametric port of
`sqir_style_modAddConst_clean_candidate_commute_update_control_outside`.
All sub-deps already q_start-parametric:
- `cuccaro_addConstGate_commute_update_outside_workspace` (CuccaroSQIRCondAdd.lean:685);
- `sqir_style_compareConst_candidate_commute_update_outside_fun` (CuccaroSQIRDirtyFlag.lean:3132);
- `sqir_conditionalSubConstGate_commute_update_outside_fun` (:3174);
- `Gate.applyNat_X_commute_update_outside_fun` (:3039, generic). -/
theorem sqir_style_modAddConst_clean_candidate_commute_update_control_outside_qstart
    (bits q_start N c controlIdx flagPos : Nat) (v : Bool) (f : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_style_modAddConst_clean_candidate bits q_start N c flagPos)
        (update f controlIdx v)
      = update (Gate.applyNat (sqir_style_modAddConst_clean_candidate bits q_start N c flagPos) f)
              controlIdx v := by
  unfold sqir_style_modAddConst_clean_candidate sqir_style_modAddConst_dirtyFlag_candidate
  simp only [Gate.applyNat_seq]
  rw [cuccaro_addConstGate_commute_update_outside_workspace bits q_start c controlIdx v f
        hcontrol_out]
  rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits q_start N flagPos
        controlIdx v _ hcontrol_out hcontrol_ne_flag]
  rw [sqir_conditionalSubConstGate_commute_update_outside_fun bits q_start N flagPos
        controlIdx v _ hcontrol_out hcontrol_ne_flag]
  rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits q_start c flagPos
        controlIdx v _ hcontrol_out hcontrol_ne_flag]
  rw [Gate.applyNat_X_commute_update_outside_fun flagPos controlIdx v _ hcontrol_ne_flag]

/-- **R7d^xxix-L-3.10′ HEADLINE: q_start-parametric control=true
state equality for the controlled mod-N add candidate.**

q_start-parametric port of
`sqir_style_controlledModAddConst_candidate_control_true_state_eq`.
The 5-stage rewrite chain is mirrored with `2 → q_start`, `1 →
flagPos`, free `controlIdx`, with the standard outside-workspace
hypotheses on both `controlIdx` and `flagPos`, plus distinctness.

The state-equality lifts the controlled candidate's action (under
external control = true) to the uncontrolled clean candidate
applied to `cuccaro_input_F q_start false 0 x`, with the
`controlIdx` slot pinned to `true` on both sides.

Dependencies (all already q_start-parametric or just landed):
- `sqir_style_modAddConst_clean_candidate_commute_update_control_outside_qstart`
  (above, this tick);
- `sqir_conditionalAddConstGate_apply_true_fun` (CuccaroSQIRCondAdd.lean:379);
- `sqir_conditionalSubConstGate_preserves_outside` (:2951);
- `sqir_style_compareConst_candidate_frame_outside` (:175);
- `cuccaro_addConstGate_preserves_outside_workspace_at` (:2918);
- `sqir_controlledCompareConst_at_control_true_eq_unmasked_fun` (:2091);
- `Gate.applyNat_CX_at_control_true_eq_X_fun` (generic CX). -/
theorem sqir_style_controlledModAddConst_candidate_control_true_state_eq_qstart
    (bits q_start N c x controlIdx flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
        (update (cuccaro_input_F q_start false 0 x) controlIdx true)
      = update (Gate.applyNat
                  (sqir_style_modAddConst_clean_candidate bits q_start N c flagPos)
                  (update (cuccaro_input_F q_start false 0 x) flagPos false))
              controlIdx true := by
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have h_F_at_flag : cuccaro_input_F q_start false 0 x flagPos = false :=
    cuccaro_input_F_at_outside_eq_false q_start bits x flagPos hflag_out h_x_lt
  have h_F_flag_eq : update (cuccaro_input_F q_start false 0 x) flagPos false
                  = cuccaro_input_F q_start false 0 x := by
    funext q
    by_cases hq : q = flagPos
    · rw [hq, update_eq]; exact h_F_at_flag.symm
    · rw [update_neq _ _ _ _ hq]
  rw [h_F_flag_eq]
  rw [← sqir_style_modAddConst_clean_candidate_commute_update_control_outside_qstart bits q_start
        N c controlIdx flagPos true (cuccaro_input_F q_start false 0 x) hcontrol_out
        hcontrol_ne_flag]
  unfold sqir_style_controlledModAddConst_candidate sqir_style_modAddConst_clean_candidate
    sqir_style_modAddConst_dirtyFlag_candidate
  simp only [Gate.applyNat_seq]
  have h_input_ctrl :
      (update (cuccaro_input_F q_start false 0 x) controlIdx true) controlIdx = true :=
    update_eq _ _ _
  have h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2 := by
    intros i _ heq
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  rw [sqir_conditionalAddConstGate_apply_true_fun bits q_start c controlIdx
        (update (cuccaro_input_F q_start false 0 x) controlIdx true) h_control_distinct
        h_input_ctrl hcontrol_out]
  have h_state3_ctrl :
      Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos)
        (Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
          (Gate.applyNat (cuccaro_addConstGate bits q_start c)
            (update (cuccaro_input_F q_start false 0 x) controlIdx true))) controlIdx = true := by
    rw [sqir_conditionalSubConstGate_preserves_outside bits q_start N flagPos controlIdx _
          h_control_distinct hcontrol_out]
    rw [sqir_style_compareConst_candidate_frame_outside bits q_start N flagPos _ controlIdx
          hcontrol_ne_flag hcontrol_out]
    rw [cuccaro_addConstGate_preserves_outside_workspace_at bits q_start c controlIdx _
          hcontrol_out]
    exact h_input_ctrl
  rw [sqir_controlledCompareConst_at_control_true_eq_unmasked_fun bits q_start c controlIdx
        flagPos _ h_control_distinct hcontrol_out hcontrol_ne_flag h_state3_ctrl]
  have h_state4_ctrl :
      Gate.applyNat (sqir_style_compareConst_candidate bits q_start c flagPos)
        (Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos)
          (Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
            (Gate.applyNat (cuccaro_addConstGate bits q_start c)
              (update (cuccaro_input_F q_start false 0 x) controlIdx true)))) controlIdx = true := by
    rw [sqir_style_compareConst_candidate_frame_outside bits q_start c flagPos _ controlIdx
          hcontrol_ne_flag hcontrol_out]
    exact h_state3_ctrl
  rw [Gate.applyNat_CX_at_control_true_eq_X_fun controlIdx flagPos _ h_state4_ctrl]

/-- **HEADLINE Deliverable D — clean modadd candidate commutes with `update` at
controlIdx outside workspace ∪ {flagPos = 1}.** -/
theorem sqir_style_modAddConst_clean_candidate_commute_update_control_outside
    (bits N c controlIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.applyNat (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
        (update f controlIdx v)
      = update (Gate.applyNat (sqir_style_modAddConst_clean_candidate bits 2 N c 1) f)
              controlIdx v := by
  unfold sqir_style_modAddConst_clean_candidate sqir_style_modAddConst_dirtyFlag_candidate
  simp only [Gate.applyNat_seq]
  rw [cuccaro_addConstGate_commute_update_outside_workspace bits 2 c controlIdx v f hcontrol_out]
  rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits 2 N 1 controlIdx v _
        hcontrol_out hcontrol_ne_flag]
  rw [sqir_conditionalSubConstGate_commute_update_outside_fun bits 2 N 1 controlIdx v _
        hcontrol_out hcontrol_ne_flag]
  rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits 2 c 1 controlIdx v _
        hcontrol_out hcontrol_ne_flag]
  rw [Gate.applyNat_X_commute_update_outside_fun 1 controlIdx v _ hcontrol_ne_flag]

/-! ## Tick 72 — Control=true branch + combined theorems. -/

/-- **Helper — `cuccaro_target_val` is invariant under `update` at outside controlIdx.** -/
theorem cuccaro_target_val_update_outside_workspace
    (bits q_start controlIdx : Nat) (v : Bool) (Y : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    cuccaro_target_val bits q_start (update Y controlIdx v)
      = cuccaro_target_val bits q_start Y := by
  induction bits with
  | zero => rfl
  | succ k ih =>
    unfold cuccaro_target_val
    have h_ne : (q_start + 2 * k + 1 : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    have h_ih : controlIdx < q_start ∨ q_start + 2 * k + 1 ≤ controlIdx := by
      rcases hcontrol_out with hl | hr
      · left; exact hl
      · right; omega
    rw [ih h_ih]

/-- **Helper — `cuccaro_read_val` is invariant under `update` at outside controlIdx.** -/
theorem cuccaro_read_val_update_outside_workspace
    (bits q_start controlIdx : Nat) (v : Bool) (Y : Nat → Bool)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    cuccaro_read_val bits q_start (update Y controlIdx v)
      = cuccaro_read_val bits q_start Y := by
  induction bits with
  | zero => rfl
  | succ k ih =>
    unfold cuccaro_read_val
    have h_ne : (q_start + 2 * k + 2 : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    have h_ih : controlIdx < q_start ∨ q_start + 2 * k + 1 ≤ controlIdx := by
      rcases hcontrol_out with hl | hr
      · left; exact hl
      · right; omega
    rw [ih h_ih]

/-- **HEADLINE Deliverable A — control=true state equality for the controlled
mod-N add candidate.** -/
theorem sqir_style_controlledModAddConst_candidate_control_true_state_eq
    (bits N c x controlIdx : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
        (update (cuccaro_input_F 2 false 0 x) controlIdx true)
      = update (Gate.applyNat (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
                  (update (cuccaro_input_F 2 false 0 x) 1 false)) controlIdx true := by
  have h_F_at_1 : cuccaro_input_F 2 false 0 x 1 = false := by
    unfold cuccaro_input_F; rw [if_pos (by omega : (1 : Nat) < 2)]
  have h_F_1_eq : update (cuccaro_input_F 2 false 0 x) 1 false
                = cuccaro_input_F 2 false 0 x := by
    funext q
    by_cases hq : q = 1
    · rw [hq, update_eq]; exact h_F_at_1.symm
    · rw [update_neq _ _ _ _ hq]
  rw [h_F_1_eq]
  rw [← sqir_style_modAddConst_clean_candidate_commute_update_control_outside bits N c
        controlIdx true (cuccaro_input_F 2 false 0 x) hcontrol_out hcontrol_ne_flag]
  unfold sqir_style_controlledModAddConst_candidate sqir_style_modAddConst_clean_candidate
    sqir_style_modAddConst_dirtyFlag_candidate
  simp only [Gate.applyNat_seq]
  have h_input_ctrl : (update (cuccaro_input_F 2 false 0 x) controlIdx true) controlIdx = true :=
    update_eq _ _ _
  have h_control_distinct : ∀ i, i < bits → controlIdx ≠ 2 + 2 * i + 2 := by
    intros i _ heq
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  rw [sqir_conditionalAddConstGate_apply_true_fun bits 2 c controlIdx
        (update (cuccaro_input_F 2 false 0 x) controlIdx true) h_control_distinct
        h_input_ctrl hcontrol_out]
  have h_state3_ctrl :
      Gate.applyNat (sqir_conditionalSubConstGate bits 2 N 1)
        (Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
          (Gate.applyNat (cuccaro_addConstGate bits 2 c)
            (update (cuccaro_input_F 2 false 0 x) controlIdx true))) controlIdx = true := by
    rw [sqir_conditionalSubConstGate_preserves_outside bits 2 N 1 controlIdx _
          h_control_distinct hcontrol_out]
    rw [sqir_style_compareConst_candidate_frame_outside bits 2 N 1 _ controlIdx
          hcontrol_ne_flag hcontrol_out]
    rw [cuccaro_addConstGate_preserves_outside_workspace_at bits 2 c controlIdx _ hcontrol_out]
    exact h_input_ctrl
  rw [sqir_controlledCompareConst_at_control_true_eq_unmasked_fun bits 2 c controlIdx 1 _
        h_control_distinct hcontrol_out hcontrol_ne_flag h_state3_ctrl]
  have h_state4_ctrl :
      Gate.applyNat (sqir_style_compareConst_candidate bits 2 c 1)
        (Gate.applyNat (sqir_conditionalSubConstGate bits 2 N 1)
          (Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
            (Gate.applyNat (cuccaro_addConstGate bits 2 c)
              (update (cuccaro_input_F 2 false 0 x) controlIdx true)))) controlIdx = true := by
    rw [sqir_style_compareConst_candidate_frame_outside bits 2 c 1 _ controlIdx
          hcontrol_ne_flag hcontrol_out]
    exact h_state3_ctrl
  rw [Gate.applyNat_CX_at_control_true_eq_X_fun controlIdx 1 _ h_state4_ctrl]

/-- **R7d^xxix-L-3.11′ DELIVERABLE: q_start-parametric control=true
target decode.**

q_start-parametric port of
`sqir_style_controlledModAddConst_candidate_target_decode_control_true`.
Three-step thin consequence of the L-3.10′ state equality:
1. rewrite via `_control_true_state_eq_qstart` to expose the
   uncontrolled clean candidate applied to `cuccaro_input_F q_start`
   with the `controlIdx` slot wrapped in `update _ controlIdx true`;
2. strip the outer `update controlIdx true` via
   `cuccaro_target_val_update_outside_workspace` (controlIdx lies
   outside the workspace by hypothesis);
3. close with `_modAddConst_clean_candidate_target_decode_qstart`
   (L-3.9′). -/
theorem sqir_style_controlledModAddConst_candidate_target_decode_control_true_qstart
    (bits q_start N c x controlIdx flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx true))
      = (x + c) % N := by
  rw [sqir_style_controlledModAddConst_candidate_control_true_state_eq_qstart
        bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag]
  rw [cuccaro_target_val_update_outside_workspace bits q_start controlIdx true _ hcontrol_out]
  exact sqir_style_modAddConst_clean_candidate_target_decode_qstart
    bits q_start N c x flagPos hbits hN_pos hN hN2 hc_pos hc hx hflag_out

/-- **Deliverable B — control=true target decode.** -/
theorem sqir_style_controlledModAddConst_candidate_target_decode_control_true
    (bits N c x controlIdx : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx true))
      = (x + c) % N := by
  rw [sqir_style_controlledModAddConst_candidate_control_true_state_eq bits N c x controlIdx
        hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag]
  rw [cuccaro_target_val_update_outside_workspace bits 2 controlIdx true _ hcontrol_out]
  exact sqir_style_modAddConst_clean_candidate_target_decode bits N c x hbits hN_pos hN hN2
    hc_pos hc hx

/-- **R7d^xxix-L-3.12′ helper: q_start-parametric clean-candidate
flag restoration.**  At `flagPos`, the uncontrolled clean candidate
restores the flag to `false`.  Direct q_start port of
`sqir_style_modAddConst_clean_candidate_flag_restored` (line 1462). -/
theorem sqir_style_modAddConst_clean_candidate_flag_restored_qstart
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat
        (sqir_style_modAddConst_clean_candidate bits q_start N c flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos
      = false := by
  show Gate.applyNat
      (seq (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
            (seq (sqir_style_compareConst_candidate bits q_start c flagPos)
                 (Gate.X flagPos)))
      _ _ = _
  simp only [Gate.applyNat_seq]
  have h_flag_distinct : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2 := by
    intros j _ heq
    rcases hflag_out with hl | hr
    · omega
    · omega
  rw [sqir_style_modAddConst_dirtyFlag_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  have h_xc_mod_N_lt : (x + c) % N < 2 ^ bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  rw [Gate.applyNat_X]
  rw [update_eq]
  rw [sqir_style_compareConst_candidate_flag_xor bits q_start c ((x + c) % N) flagPos
        (decide (N ≤ x + c)) hc_pos (by omega : c ≤ 2 ^ bits) h_xc_mod_N_lt hflag_out]
  rw [decide_c_le_xc_mod_N_eq_not_decide_N_le_xc N x c hN_pos hc_pos hx hc]
  cases decide (N ≤ x + c) <;> rfl

/-- **R7d^xxix-L-3.12′ DELIVERABLE: q_start-parametric control=true
workspace bundle.**

4-conjunct workspace bundle when the external control bit is
`true`.  After applying the controlled mod-N add candidate to
`(update (cuccaro_input_F q_start false 0 x) controlIdx true)`:

1. `cuccaro_read_val` (read register) = 0;
2. position `q_start + 2 * bits` (top carry) = false;
3. position `flagPos` = false;
4. position `controlIdx` = true (preserved external control).

Proof strategy mirrors the hard-coded version (line 3481+) but uses
the L-3.10′ state-eq + inline read/top-carry computation +
`_flag_restored_qstart` (helper above). -/
theorem sqir_style_controlledModAddConst_candidate_workspace_control_true_qstart
    (bits q_start N c x controlIdx flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx true))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx true) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx true) flagPos
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx true) controlIdx
        = true := by
  rw [sqir_style_controlledModAddConst_candidate_control_true_state_eq_qstart
        bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag]
  have h_flag_distinct : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2 := by
    intros j _ heq
    rcases hflag_out with hl | hr
    · omega
    · omega
  have h_xc_mod_N_lt : (x + c) % N < 2 ^ bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- read = 0.
    rw [cuccaro_read_val_update_outside_workspace bits q_start controlIdx true _ hcontrol_out]
    show cuccaro_read_val bits q_start
        (Gate.applyNat
          (seq (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
                (seq (sqir_style_compareConst_candidate bits q_start c flagPos)
                     (Gate.X flagPos))) _) = 0
    simp only [Gate.applyNat_seq]
    rw [sqir_style_modAddConst_dirtyFlag_state_eq bits q_start N c x flagPos
          hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
    have h_eq : cuccaro_read_val bits q_start
        (Gate.applyNat (Gate.X flagPos)
          (Gate.applyNat (sqir_style_compareConst_candidate bits q_start c flagPos)
            (update (cuccaro_input_F q_start false 0 ((x + c) % N)) flagPos
              (decide (N ≤ x + c)))))
      = 0 % 2 ^ bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      have h_pos_ne_flag : (q_start + 2 * i + 2 : Nat) ≠ flagPos := by
        rcases hflag_out with hl | hr
        · omega
        · omega
      rw [Gate.applyNat_X]
      rw [update_neq _ _ _ _ h_pos_ne_flag]
      rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits q_start c flagPos _
            hflag_out (q_start + 2 * i + 2) (by omega) (by omega)]
      rw [update_neq _ _ _ _ h_pos_ne_flag]
      rw [cuccaro_input_F_at_a q_start i false 0 ((x + c) % N)]
    rw [h_eq]; simp
  · -- top carry at q_start + 2 * bits = false.
    have h_top_ne_ctrl : (q_start + 2 * bits : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_top_ne_ctrl]
    show Gate.applyNat
        (seq (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
              (seq (sqir_style_compareConst_candidate bits q_start c flagPos)
                   (Gate.X flagPos))) _ _ = _
    simp only [Gate.applyNat_seq]
    rw [sqir_style_modAddConst_dirtyFlag_state_eq bits q_start N c x flagPos
          hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
    have h_top_ne_flag : (q_start + 2 * bits : Nat) ≠ flagPos := by
      rcases hflag_out with hl | hr
      · omega
      · omega
    rw [Gate.applyNat_X]
    rw [update_neq _ _ _ _ h_top_ne_flag]
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits q_start c flagPos _
          hflag_out (q_start + 2 * bits) (by omega) (by omega)]
    rw [update_neq _ _ _ _ h_top_ne_flag]
    have h_eq : q_start + 2 * bits = q_start + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a q_start (bits - 1) false 0 ((x + c) % N)]
    simp [Nat.zero_testBit]
  · -- flag = false.
    rw [update_neq _ _ _ _ hcontrol_ne_flag.symm]
    exact sqir_style_modAddConst_clean_candidate_flag_restored_qstart bits q_start N c x flagPos
      hbits hN_pos hN hN2 hc_pos hc hx hflag_out
  · -- controlIdx = true.
    exact update_eq _ _ _

/-- **Deliverable C — control=true workspace bundle (4-conjunct).** -/
theorem sqir_style_controlledModAddConst_candidate_workspace_control_true
    (bits N c x controlIdx : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx true))
        = 0
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx true) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx true) 1
        = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx true) controlIdx
        = true := by
  rw [sqir_style_controlledModAddConst_candidate_control_true_state_eq bits N c x controlIdx
        hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag]
  obtain ⟨_, _, h_rd, h_tc, h_fl⟩ :=
    sqir_style_modAddConst_clean_candidate_clean bits N c x hbits hN_pos hN hN2 hc_pos hc hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cuccaro_read_val_update_outside_workspace bits 2 controlIdx true _ hcontrol_out]
    exact h_rd
  · have h_ne : (2 + 2 * bits : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    exact h_tc
  · rw [update_neq _ _ _ _ hcontrol_ne_flag.symm]
    exact h_fl
  · exact update_eq _ _ _

/-! ## Tick 72 — Combined theorems (case-split on control). -/

/-- **HEADLINE Deliverable D — combined controlled target decode.** -/
theorem sqir_style_controlledModAddConst_candidate_target_decode
    (bits N c x controlIdx : Nat) (control : Bool) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control))
      = if control then (x + c) % N else x := by
  cases control
  · simp only [Bool.false_eq_true, if_false]
    exact sqir_style_controlledModAddConst_candidate_target_decode_control_false bits N c x
      controlIdx hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag
  · simp only [if_true]
    exact sqir_style_controlledModAddConst_candidate_target_decode_control_true bits N c x
      controlIdx hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag

/-- **Deliverable E — combined workspace bundle.** -/
theorem sqir_style_controlledModAddConst_candidate_workspace
    (bits N c x controlIdx : Nat) (control : Bool) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = 0
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) 1
        = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx
        = control := by
  cases control
  · exact sqir_style_controlledModAddConst_candidate_workspace_control_false bits N c x
      controlIdx hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag
  · exact sqir_style_controlledModAddConst_candidate_workspace_control_true bits N c x
      controlIdx hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag

/-! ## Tick 72 — Candidate clean bundle and total wrapper. -/

/-- **R7d^xxix-L-3.13′ DELIVERABLE: q_start-parametric controlled
candidate clean bundle (combined over both control branches).**

6-conjunct bundle parametric in `q_start`, `flagPos`, `controlIdx`,
`dim`, and `control : Bool`:

1. `Gate.WellTyped dim` of the candidate gate;
2. target decode = `if control then (x + c) % N else x`;
3. read register = 0;
4. position `q_start + 2 * bits` (top carry) = false;
5. position `flagPos` = false;
6. position `controlIdx` = `control` (preserved external control).

Mechanical case-split on `control`: false branch fully delegated to
`_clean_control_false_qstart` (L-3.8′); true branch reuses
`_clean_control_false_qstart` only to extract the
control-independent `Gate.WellTyped`, then assembles the remaining
five conjuncts from `_target_decode_control_true_qstart` (L-3.11′)
and `_workspace_control_true_qstart` (L-3.12′).  No new
arithmetic. -/
theorem sqir_style_controlledModAddConst_candidate_clean_qstart
    (bits q_start N c x dim controlIdx flagPos : Nat) (control : Bool)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_control_lt_dim : controlIdx < dim)
    (h_flag_lt_dim : flagPos < dim) :
    Gate.WellTyped dim
        (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx control))
        = (if control then (x + c) % N else x)
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx control)) = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) flagPos
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) controlIdx
        = control := by
  cases control with
  | false =>
    obtain ⟨h_wt, h_tgt, h_rd, h_tc, h_fl, h_ctrl⟩ :=
      sqir_style_controlledModAddConst_candidate_clean_control_false_qstart
        bits q_start N c x dim controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag h_workspace h_control_lt_dim h_flag_lt_dim
    refine ⟨h_wt, ?_, h_rd, h_tc, h_fl, h_ctrl⟩
    show _ = x
    exact h_tgt
  | true =>
    obtain ⟨h_wt, _, _, _, _, _⟩ :=
      sqir_style_controlledModAddConst_candidate_clean_control_false_qstart
        bits q_start N c x dim controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag h_workspace h_control_lt_dim h_flag_lt_dim
    have h_tgt :=
      sqir_style_controlledModAddConst_candidate_target_decode_control_true_qstart
        bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag
    obtain ⟨h_rd, h_tc, h_fl, h_ctrl⟩ :=
      sqir_style_controlledModAddConst_candidate_workspace_control_true_qstart
        bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag
    refine ⟨h_wt, ?_, h_rd, h_tc, h_fl, h_ctrl⟩
    show _ = (x + c) % N
    exact h_tgt

/-- **Deliverable F — controlled candidate clean bundle for c > 0.** -/
theorem sqir_style_controlledModAddConst_candidate_clean
    (bits N c x controlIdx : Nat) (control : Bool) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1)
    (h_control_workspace_lt : controlIdx < sqir_modmult_rev_anc bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = (if control then (x + c) % N else x)
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control)) = 0
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) (2 + 2 * bits) = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) 1 = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx = control := by
  obtain ⟨h_rd, h_tc, h_fl, h_ctrl⟩ :=
    sqir_style_controlledModAddConst_candidate_workspace bits N c x controlIdx control hbits
      hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag
  refine ⟨?_, ?_, h_rd, h_tc, h_fl, h_ctrl⟩
  · -- WellTyped.
    show Gate.WellTyped (sqir_modmult_rev_anc bits)
        (seq (sqir_conditionalAddConstGate bits 2 c controlIdx)
              (seq (sqir_style_compareConst_candidate bits 2 N 1)
                   (seq (sqir_conditionalSubConstGate bits 2 N 1)
                        (seq (sqir_controlledCompareConst bits 2 c controlIdx 1)
                             (Gate.CX controlIdx 1)))))
    have h_control_distinct : ∀ i, i < bits → controlIdx ≠ 2 + 2 * i + 2 := by
      intros i _ heq
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    have h_flag_distinct : ∀ i, i < bits → (1 : Nat) ≠ 2 + 2 * i + 2 := fun i _ => by omega
    have h_workspace : (2 + 2 * bits + 1 : Nat) ≤ sqir_modmult_rev_anc bits := by
      unfold sqir_modmult_rev_anc; omega
    have h_flag_lt : (1 : Nat) < sqir_modmult_rev_anc bits := by
      unfold sqir_modmult_rev_anc; omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact sqir_conditionalAddConstGate_wellTyped bits 2 c controlIdx (sqir_modmult_rev_anc bits)
        h_workspace h_control_workspace_lt h_control_distinct
    · apply sqir_style_compareConst_candidate_wellTyped bits 2 N 1 (sqir_modmult_rev_anc bits)
        h_workspace h_flag_lt
      omega
    · exact sqir_conditionalSubConstGate_wellTyped bits 2 N 1 (sqir_modmult_rev_anc bits)
        h_workspace h_flag_lt h_flag_distinct
    · -- WellTyped for sqir_controlledCompareConst: same structure as compareConst.
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- prepare(c, controlIdx) wellTyped.
        exact sqir_prepareMaskedConstRead_wellTyped bits 2 (2^bits - c) controlIdx
          (sqir_modmult_rev_anc bits) h_workspace h_control_workspace_lt h_control_distinct
      · -- maj_chain wellTyped.
        exact cuccaro_maj_chain_wellTyped bits 2 (sqir_modmult_rev_anc bits) h_workspace
      · -- CX (q_start + 2 * bits) 1 wellTyped.
        refine ⟨?_, ?_, ?_⟩
        · unfold sqir_modmult_rev_anc; omega
        · exact h_flag_lt
        · omega
      · -- maj_chain_inv wellTyped.
        exact cuccaro_maj_chain_inv_wellTyped bits 2 (sqir_modmult_rev_anc bits) h_workspace
      · -- prepare wellTyped.
        exact sqir_prepareMaskedConstRead_wellTyped bits 2 (2^bits - c) controlIdx
          (sqir_modmult_rev_anc bits) h_workspace h_control_workspace_lt h_control_distinct
    · -- CX controlIdx 1 wellTyped.
      refine ⟨?_, ?_, ?_⟩
      · exact h_control_workspace_lt
      · exact h_flag_lt
      · exact hcontrol_ne_flag
  · exact sqir_style_controlledModAddConst_candidate_target_decode bits N c x controlIdx control
      hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag

/-- **R7d^xxix-L-3.14′ helper: q_start-parametric `c = 0` reduction.**
The total wrapper at `c = 0` is the identity gate, regardless of
`q_start`/`flagPos`/`controlIdx`. -/
theorem sqir_style_controlledModAddConst_gate_zero_eq_qstart
    (bits q_start N controlIdx flagPos : Nat) :
    sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos = Gate.I := by
  unfold sqir_style_controlledModAddConst_gate; simp

/-- **R7d^xxix-L-3.14′ helper: q_start-parametric `c = 0` clean
bundle.**  When `c = 0` the total wrapper is `Gate.I`, so all six
conjuncts reduce to facts about the input state.

Mirrors `sqir_style_controlledModAddConst_gate_zero_clean` (line
2150) with general `q_start`, `flagPos`, and free `dim`.  Uses
`cuccaro_input_F_at_outside_eq_false` for the flag conjunct
instead of the hard-coded `unfold + if_pos`. -/
theorem sqir_style_controlledModAddConst_gate_zero_clean_qstart
    (bits q_start N x dim controlIdx flagPos : Nat) (control : Bool)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim) :
    Gate.WellTyped dim
        (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx control))
        = x
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx control))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) flagPos
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) controlIdx
        = control := by
  rw [sqir_style_controlledModAddConst_gate_zero_eq_qstart]
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- WellTyped: Gate.I requires 0 < dim.
    show 0 < dim
    omega
  · -- target_val = x.
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_target_val bits q_start
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) = x % 2 ^ bits := by
      apply cuccaro_target_val_eq_sum_when_bits_match
      intro i hi
      have h_ne : (q_start + 2 * i + 1 : Nat) ≠ controlIdx := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      rw [update_neq _ _ _ _ h_ne]
      exact cuccaro_input_F_at_b q_start i false 0 x
    rw [h_eq]
    exact Nat.mod_eq_of_lt h_x_lt
  · -- read_val = 0.
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_read_val bits q_start
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) = 0 % 2 ^ bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      have h_ne : (q_start + 2 * i + 2 : Nat) ≠ controlIdx := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      rw [update_neq _ _ _ _ h_ne]
      rw [cuccaro_input_F_at_a q_start i false 0 x]
    rw [h_eq]
    simp
  · -- top carry at q_start + 2 * bits.
    rw [Gate.applyNat_I]
    have h_ne : (q_start + 2 * bits : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    have h_eq : q_start + 2 * bits = q_start + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a q_start (bits - 1) false 0 x]
    exact Nat.zero_testBit _
  · -- flagPos = false.
    rw [Gate.applyNat_I]
    rw [update_neq _ _ _ _ hcontrol_ne_flag.symm]
    exact cuccaro_input_F_at_outside_eq_false q_start bits x flagPos hflag_out h_x_lt
  · -- controlIdx = control.
    rw [Gate.applyNat_I]
    exact update_eq _ _ _

/-- **R7d^xxix-L-3.14′ DELIVERABLE: q_start-parametric total wrapper
clean theorem.**

Combines the `c = 0` case (delegated to
`_gate_zero_clean_qstart` above, with the target conjunct
re-massaged to match the headline's `if control then (x+c)%N else x`
shape at `c = 0`) and the `c > 0` case (delegated to the L-3.13′
`_candidate_clean_qstart`).

Mirrors `sqir_style_controlledModAddConst_gate_clean` (line 3871)
with general `q_start`, `flagPos`, `controlIdx`, and free `dim`. -/
theorem sqir_style_controlledModAddConst_gate_clean_qstart
    (bits q_start N c x dim controlIdx flagPos : Nat) (control : Bool)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_control_lt_dim : controlIdx < dim)
    (h_flag_lt_dim : flagPos < dim) :
    Gate.WellTyped dim
        (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx control))
        = (if control then (x + c) % N else x)
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx control)) = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) flagPos
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control) controlIdx
        = control := by
  by_cases hc0 : c = 0
  · subst hc0
    obtain ⟨h_wt, h_tgt, h_rd, h_tc, h_fl, h_ctrl⟩ :=
      sqir_style_controlledModAddConst_gate_zero_clean_qstart bits q_start N x dim
        controlIdx flagPos control hbits hN_pos hN hx hcontrol_out hflag_out hcontrol_ne_flag
        h_workspace
    refine ⟨h_wt, ?_, h_rd, h_tc, h_fl, h_ctrl⟩
    rw [h_tgt]
    cases control
    · simp
    · simp; exact (Nat.mod_eq_of_lt hx).symm
  · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc0
    have h_unfold :
        sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos
          = sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos := by
      unfold sqir_style_controlledModAddConst_gate
      simp [hc0]
    rw [h_unfold]
    exact sqir_style_controlledModAddConst_candidate_clean_qstart bits q_start N c x dim
      controlIdx flagPos control hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hflag_out
      hcontrol_ne_flag h_workspace h_control_lt_dim h_flag_lt_dim

/-- **HEADLINE Deliverable G — total wrapper clean theorem.** -/
theorem sqir_style_controlledModAddConst_gate_clean
    (bits N c x controlIdx : Nat) (control : Bool) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1)
    (h_control_workspace_lt : controlIdx < sqir_modmult_rev_anc bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = (if control then (x + c) % N else x)
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control)) = 0
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) (2 + 2 * bits) = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) 1 = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx = control := by
  by_cases hc0 : c = 0
  · subst hc0
    obtain ⟨h_wt, h_tgt, h_rd, h_tc, h_fl, h_ctrl⟩ :=
      sqir_style_controlledModAddConst_gate_zero_clean bits N x controlIdx control hbits hN_pos
        hN hx hcontrol_out hcontrol_ne_flag
    refine ⟨h_wt, ?_, h_rd, h_tc, h_fl, h_ctrl⟩
    rw [h_tgt]
    cases control
    · simp
    · simp; exact (Nat.mod_eq_of_lt hx).symm
  · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc0
    have h_unfold : sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1
        = sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1 := by
      unfold sqir_style_controlledModAddConst_gate
      simp [hc0]
    rw [h_unfold]
    exact sqir_style_controlledModAddConst_candidate_clean bits N c x controlIdx control hbits
      hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag h_control_workspace_lt

/-- **HEADLINE Deliverable H — BasicSetting-derived total wrapper clean theorem.** -/
theorem sqir_style_controlledModAddConst_gate_clean_from_BasicSetting
    (a r N m n c x controlIdx : Nat) (control : Bool)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * (n + 1) + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1)
    (h_control_workspace_lt : controlIdx < sqir_modmult_rev_anc (n + 1)) :
    Gate.WellTyped (sqir_modmult_rev_anc (n + 1))
        (sqir_style_controlledModAddConst_gate (n + 1) 2 N c controlIdx 1)
    ∧ cuccaro_target_val (n + 1) 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate (n + 1) 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = (if control then (x + c) % N else x)
    ∧ cuccaro_read_val (n + 1) 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate (n + 1) 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control)) = 0
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate (n + 1) 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) (2 + 2 * (n + 1)) = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate (n + 1) 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) 1 = false
    ∧ Gate.applyNat (sqir_style_controlledModAddConst_gate (n + 1) 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx = control := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have hN_le : N ≤ 2 ^ (n + 1) := by omega
  exact sqir_style_controlledModAddConst_gate_clean (n + 1) N c x controlIdx control
    (by omega : 1 ≤ n + 1) hN_pos hN_le hN2 hc hx hcontrol_out hcontrol_ne_flag
    h_control_workspace_lt

end FormalRV.BQAlgo
