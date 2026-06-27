/- CuccaroDirtyFlagStageCorrectness — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroDirtyFlagStageCorrectness.DirtyFlagArithmeticAndPostState

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Tick 60 — Deliverable D: SQIR-layout WellTyped specialization.

The SQIR-exact layout uses `q_start = 2`, `flagPos = 1`, and the
SQIR-faithful dimension `sqir_modmult_rev_anc bits = 3 * bits + 11`.
This layout places the flag BELOW the workspace.  We can prove
WellTyped at this layout directly — but the semantic theorems
(target_decode, workspace) currently require `h_flag_above`, since
the SQIR-style comparator's flag theorem was set up with flag above
workspace.  Extending the semantic theorems to handle below-workspace
flag is deferred to a later tick (it requires adapting
`sqir_style_compareConst_candidate_flag` and the corresponding
workspace_restored / frame_outside lemmas).  See the "Honesty
disclosures" section below. -/

/-- **Deliverable D (partial) — WellTyped at the exact SQIR layout
`q_start = 2, flagPos = 1, dim = sqir_modmult_rev_anc bits`.** -/
theorem sqir_style_modAddConst_dirtyFlag_candidate_wellTyped_sqir_layout
    (bits N c : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1) := by
  apply sqir_style_modAddConst_dirtyFlag_candidate_wellTyped bits 2 N c 1
    (sqir_modmult_rev_anc bits)
  · unfold sqir_modmult_rev_anc; omega
  · unfold sqir_modmult_rev_anc; omega
  · intros i _; omega
  · omega

/-! ## Tick 60 — Deliverable E: sizing relation from `BasicSetting`.

`BasicSetting` (Shor.lean §3) provides `N < 2^n ≤ 2 * N`.  The dirty-
flag mod-N add requires `2 * N ≤ 2^bits`.  Choosing `bits := n + 1`
yields `2 * N ≤ 2^(n + 1)` directly from `N < 2^n`.  Trying to use
`bits = n` does NOT work, since `2^n ≤ 2 * N` runs the wrong way. -/

/-- **HEADLINE Deliverable E — sizing relation: `BasicSetting a r N m n`
implies `2 * N ≤ 2^(n + 1)`.**

Reading: Shor's data register width is `n` bits; the dirty-flag
modular adder must be instantiated at `bits := n + 1` (one extra
bit) so that intermediate `x + c` cannot overflow before the
comparator sees the top carry.  This matches SQIR's `n + 1`-bit
workspace per modular addition. -/
theorem BasicSetting_twoN_le_pow_succ
    (a r N m n : Nat)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n) :
    2 * N ≤ 2 ^ (n + 1) := by
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨_, _, _, hN_lt, _⟩ := h_basic
  have h2 : 2 * N < 2 ^ (n + 1) := by
    calc 2 * N < 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]; ring
  omega

/-! ## Tick 61 — Below-workspace flag generalizations + SQIR-exact layout.

The semantic theorems landed in Ticks 59–60 require
`h_flag_above : q_start + 2*bits + 1 ≤ flagPos`.  The SQIR-exact
layout has `q_start = 2, flagPos = 1`, putting the flag BELOW
workspace.  We provide `_general` variants that accept the
disjunction, then `_sqir_layout` corollaries. -/

/-- Helper: `cuccaro_input_F q_start false 0 x` evaluates to `false`
at any position outside the workspace `[q_start, q_start + 2*bits]`. -/
theorem cuccaro_input_F_at_outside_eq_false
    (q_start bits x flagPos : Nat)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hx : x < 2^bits) :
    cuccaro_input_F q_start false 0 x flagPos = false := by
  rcases hflag_out with h | h
  · unfold cuccaro_input_F
    rw [if_pos h]
  · exact cuccaro_input_F_above_eq_false q_start bits x flagPos h hx

/-- **Generalized flag-copy theorem.**  For any `flagPos` outside the
workspace (below OR above), the SQIR-style comparator candidate outputs
`decide (N ≤ x)` at `flagPos`. -/
theorem sqir_style_compareConst_candidate_flag_general
    (bits q_start N x flagPos : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (cuccaro_input_F q_start false 0 x) flagPos
      = decide (N ≤ x) := by
  rcases hflag_out with h_below | h_above
  · -- Below-workspace flag.  Mirror the existing above-case proof with `_below` frames.
    show Gate.applyNat
        (seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
              (seq (cuccaro_maj_chain bits q_start)
                   (seq (Gate.CX (q_start + 2 * bits) flagPos)
                        (seq (cuccaro_maj_chain_inv bits q_start)
                             (cuccaro_prepareConstRead bits q_start (2^bits - N))))))
        (cuccaro_input_F q_start false 0 x) flagPos = _
    simp only [Gate.applyNat_seq]
    have h_flagPos_not_read : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2 := by
      intros j _ heq; omega
    rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) flagPos h_flagPos_not_read]
    rw [cuccaro_maj_chain_inv_frame_below bits q_start _ flagPos h_below]
    simp only [Gate.applyNat_CX, update_eq]
    have h_flag_state : Gate.applyNat (cuccaro_maj_chain bits q_start)
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N))
          (cuccaro_input_F q_start false 0 x)) flagPos = false := by
      rw [cuccaro_maj_chain_frame_below bits q_start _ flagPos h_below]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) flagPos h_flagPos_not_read]
      unfold cuccaro_input_F
      rw [if_pos h_below]
    rw [h_flag_state]
    simp only [Bool.false_xor]
    have h_carry := cuccaro_compareConstForward_top_carry bits q_start N x hN_pos hN hx
    unfold cuccaro_compareConstForwardGate at h_carry
    simp only [Gate.applyNat_seq] at h_carry
    exact h_carry
  · exact sqir_style_compareConst_candidate_flag bits q_start N x flagPos
      hN_pos hN hx h_above

/-- **Generalized workspace restoration (at-position).**  At any
workspace position, the SQIR-style comparator candidate restores
the input value, for any `flagPos` outside workspace. -/
theorem sqir_style_compareConst_candidate_workspace_restored_at_general
    (bits q_start N flagPos : Nat) (f : Nat → Bool)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (q : Nat) (hq_lower : q_start ≤ q) (hq_upper : q < q_start + 2 * bits + 1) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos) f q
      = f q := by
  show Gate.applyNat
      (seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (cuccaro_prepareConstRead bits q_start (2^bits - N))))))
      f q = _
  simp only [Gate.applyNat_seq, Gate.applyNat_CX]
  by_cases hq_read : ∃ i, i < bits ∧ q = q_start + 2 * i + 2
  · obtain ⟨i, hi, hq_eq⟩ := hq_read
    rw [hq_eq]
    rw [cuccaro_prepareConstRead_at_read bits q_start (2^bits - N) i hi]
    rw [cuccaro_maj_chain_inv_commute_update_outside_workspace
          bits q_start flagPos _ _ hflag_out
          (q_start + 2 * i + 2) (by omega) (by omega)]
    rw [show Gate.applyNat (cuccaro_maj_chain_inv bits q_start)
          (Gate.applyNat (cuccaro_maj_chain bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f))
          (q_start + 2 * i + 2)
          = Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f
              (q_start + 2 * i + 2) from ?_]
    · rw [cuccaro_prepareConstRead_at_read bits q_start (2^bits - N) i hi]
      cases f (q_start + 2 * i + 2) <;> cases (2^bits - N).testBit i <;> rfl
    · rw [cuccaro_maj_chain_inv_after_chain_eq_id bits q_start
          (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f)]
  · push_neg at hq_read
    have h_not_read : ∀ i, i < bits → q ≠ q_start + 2 * i + 2 := by
      intros i hi h_eq
      exact hq_read i hi h_eq
    rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) q h_not_read]
    rw [cuccaro_maj_chain_inv_commute_update_outside_workspace
          bits q_start flagPos _ _ hflag_out q hq_lower hq_upper]
    rw [show Gate.applyNat (cuccaro_maj_chain_inv bits q_start)
          (Gate.applyNat (cuccaro_maj_chain bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f)) q
          = Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f q from ?_]
    · rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) q h_not_read]
    · rw [cuccaro_maj_chain_inv_after_chain_eq_id bits q_start
          (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N)) f)]

/-- **Generalized compare-state equality** (Tick 59 Deliverable B,
relaxed to `hflag_out`). -/
theorem sqir_dirty_modadd_after_compare_state_eq_general
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (update (cuccaro_input_F q_start false 0 (x + c)) flagPos false)
      = update (cuccaro_input_F q_start false 0 (x + c))
              flagPos (decide (N ≤ x + c)) := by
  have h_input_at_flagPos : cuccaro_input_F q_start false 0 (x + c) flagPos = false :=
    cuccaro_input_F_at_outside_eq_false q_start bits (x + c) flagPos hflag_out (by omega)
  have h_input_eq : update (cuccaro_input_F q_start false 0 (x + c)) flagPos false
                  = cuccaro_input_F q_start false 0 (x + c) := by
    funext q
    by_cases hq : q = flagPos
    · rw [hq, update_eq]; exact h_input_at_flagPos.symm
    · rw [update_neq _ _ _ _ hq]
  rw [h_input_eq]
  funext q
  by_cases hq : q = flagPos
  · rw [hq, update_eq]
    exact sqir_style_compareConst_candidate_flag_general bits q_start N (x + c) flagPos
      hN_pos hN (by omega) hflag_out
  · rw [update_neq _ _ _ _ hq]
    by_cases h_q_workspace : q_start ≤ q ∧ q < q_start + 2 * bits + 1
    · exact sqir_style_compareConst_candidate_workspace_restored_at_general bits q_start N
        flagPos _ hflag_out q h_q_workspace.1 h_q_workspace.2
    · push_neg at h_q_workspace
      have h_q_outside : q < q_start ∨ q_start + 2 * bits + 1 ≤ q := by
        by_cases h : q < q_start
        · left; exact h
        · push_neg at h
          right; exact h_q_workspace h
      exact sqir_style_compareConst_candidate_frame_outside bits q_start N flagPos
        _ q hq h_q_outside

/-- **Generalized dirty-flag mod-N add target decode** (Tick 59 D,
relaxed to `hflag_out`). -/
theorem sqir_style_modAddConst_dirtyFlag_target_decode_general
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false))
      = (x + c) % N := by
  show cuccaro_target_val bits q_start
      (Gate.applyNat
        (seq (cuccaro_addConstGate bits q_start c)
              (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                   (sqir_conditionalSubConstGate bits q_start N flagPos)))
        (update (cuccaro_input_F q_start false 0 x) flagPos false)) = _
  simp only [Gate.applyNat_seq]
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq_general bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  rw [sqir_conditionalSubConstGate_target_decode bits q_start N (x + c) flagPos
        (decide (N ≤ x + c)) hbits hN_pos hN (by omega : x + c < 2^bits)
        h_flag_distinct hflag_out]
  exact sqir_dirty_modadd_arith bits N x c hN_pos hN hN2 hx hc

/-- **Generalized workspace conjuncts** (Tick 60 A, relaxed to `hflag_out`). -/
theorem sqir_style_modAddConst_dirtyFlag_read_decode_general
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_read_val bits q_start
        (Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false))
      = 0 := by
  show cuccaro_read_val bits q_start
      (Gate.applyNat
        (seq (cuccaro_addConstGate bits q_start c)
              (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                   (sqir_conditionalSubConstGate bits q_start N flagPos)))
        (update (cuccaro_input_F q_start false 0 x) flagPos false)) = _
  simp only [Gate.applyNat_seq]
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq_general bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_read_decode bits q_start (2^bits - N) (x + c) flagPos
      (decide (N ≤ x + c)) hbits (by omega) (by omega) h_flag_distinct hflag_out

theorem sqir_style_modAddConst_dirtyFlag_carry_in_restored_general
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos false) q_start
      = false := by
  show Gate.applyNat
      (seq (cuccaro_addConstGate bits q_start c)
            (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                 (sqir_conditionalSubConstGate bits q_start N flagPos)))
      (update (cuccaro_input_F q_start false 0 x) flagPos false) q_start = _
  simp only [Gate.applyNat_seq]
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq_general bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_carry_in_restored bits q_start (2^bits - N) (x + c) flagPos
      (decide (N ≤ x + c)) hbits (by omega) (by omega) h_flag_distinct hflag_out

theorem sqir_style_modAddConst_dirtyFlag_flag_value_general
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos
      = decide (N ≤ x + c) := by
  show Gate.applyNat
      (seq (cuccaro_addConstGate bits q_start c)
            (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                 (sqir_conditionalSubConstGate bits q_start N flagPos)))
      (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos = _
  simp only [Gate.applyNat_seq]
  rw [sqir_dirty_modadd_after_add_state_eq bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc hflag_out]
  rw [sqir_dirty_modadd_after_compare_state_eq_general bits q_start N c x flagPos
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_flag_preserved bits q_start (2^bits - N) (x + c) flagPos
      (decide (N ≤ x + c)) h_flag_distinct hflag_out

/-- **Generalized clean-except-flag bundle** (Tick 60 C, relaxed to
`hflag_out`).  Supports both above- AND below-workspace flag. -/
theorem sqir_style_modAddConst_dirtyFlag_clean_except_flag_general
    (bits q_start N c x flagPos dim : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.WellTyped dim
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
            (update (cuccaro_input_F q_start false 0 x) flagPos false))
        = (x + c) % N
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
            (update (cuccaro_input_F q_start false 0 x) flagPos false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false) q_start
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos
        = decide (N ≤ x + c) := by
  have h_flag_distinct_top : flagPos ≠ q_start + 2 * bits := by
    rcases hflag_out with hl | hr
    · omega
    · omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact sqir_style_modAddConst_dirtyFlag_candidate_wellTyped bits q_start N c flagPos dim
      h_workspace h_flag h_flag_distinct h_flag_distinct_top
  · exact sqir_style_modAddConst_dirtyFlag_target_decode_general bits q_start N c x flagPos
      hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out
  · exact sqir_style_modAddConst_dirtyFlag_read_decode_general bits q_start N c x flagPos
      hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out
  · exact sqir_style_modAddConst_dirtyFlag_carry_in_restored_general bits q_start N c x flagPos
      hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out
  · exact sqir_style_modAddConst_dirtyFlag_flag_value_general bits q_start N c x flagPos
      hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out


end FormalRV.BQAlgo
