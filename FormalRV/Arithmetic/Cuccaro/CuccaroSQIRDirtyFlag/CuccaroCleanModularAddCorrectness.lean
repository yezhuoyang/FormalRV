import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRCondAdd
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroModularAddDefinitions
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroDirtyFlagStageCorrectness

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-- **HEADLINE Deliverable D — clean-candidate flag restoration.**  At
`flagPos`, the clean candidate restores the input flag value `false`. -/
theorem sqir_style_modAddConst_clean_candidate_flag_restored
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N) :
    Gate.applyNat
        (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
        (update (cuccaro_input_F 2 false 0 x) 1 false) 1
      = false := by
  show Gate.applyNat
      (seq (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
            (seq (sqir_style_compareConst_candidate bits 2 c 1)
                 (Gate.X 1)))
      _ _ = _
  simp only [Gate.applyNat_seq]
  have hflag_out : (1 : Nat) < 2 ∨ 2 + 2 * bits + 1 ≤ 1 := Or.inl (by omega)
  have h_flag_distinct : ∀ j, j < bits → (1 : Nat) ≠ 2 + 2 * j + 2 := by
    intros j _; omega
  -- Use state equality to substitute the post-dirty-flag state.
  rw [sqir_style_modAddConst_dirtyFlag_state_eq bits 2 N c x 1
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  have h_xc_mod_N_lt : (x + c) % N < 2 ^ bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  -- Strip the outermost X(1) gate at position 1.
  rw [Gate.applyNat_X]
  rw [update_eq]
  -- Goal: ! (applyNat compareConst(c) (update _ 1 (decide (N ≤ x+c))) 1) = false.
  -- Apply XOR theorem.
  rw [sqir_style_compareConst_candidate_flag_xor bits 2 c ((x + c) % N) 1
        (decide (N ≤ x + c)) hc_pos (by omega : c ≤ 2 ^ bits) h_xc_mod_N_lt hflag_out]
  -- Goal: ! (xor (decide (N ≤ x+c)) (decide (c ≤ (x+c) % N))) = false.
  rw [decide_c_le_xc_mod_N_eq_not_decide_N_le_xc N x c hN_pos hc_pos hx hc]
  -- Goal: ! (xor (decide (N ≤ x+c)) (! decide (N ≤ x+c))) = false.
  cases decide (N ≤ x + c) <;> rfl

/-- **R7d^xxix-L-3.9′ DELIVERABLE: q_start-parametric clean candidate
target preservation.**

q_start-parametric port of
`sqir_style_modAddConst_clean_candidate_target_decode`.  Replaces the
hard-coded layout `q_start = 2`, `flagPos = 1` with free parameters
and the standard outside-workspace hypotheses.

The decoded target after the clean candidate equals `(x + c) % N`,
regardless of where the workspace and flag sit.

Dependencies (all already q_start-parametric):
- `sqir_style_modAddConst_dirtyFlag_state_eq` (CuccaroSQIRDirtyFlag.lean:1378);
- `cuccaro_target_val_eq_sum_when_bits_match` (CuccaroDecoded.lean:102);
- `sqir_style_compareConst_candidate_workspace_restored_at_general`
  (CuccaroSQIRDirtyFlag.lean:568);
- `cuccaro_input_F_at_b` (CuccaroCorrectness.lean:240). -/
theorem sqir_style_modAddConst_clean_candidate_target_decode_qstart
    (bits q_start N c x flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_style_modAddConst_clean_candidate bits q_start N c flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos false))
      = (x + c) % N := by
  show cuccaro_target_val bits q_start
      (Gate.applyNat
        (seq (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
              (seq (sqir_style_compareConst_candidate bits q_start c flagPos)
                   (Gate.X flagPos))) _) = _
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
  have h_eq : cuccaro_target_val bits q_start
      (Gate.applyNat (Gate.X flagPos)
        (Gate.applyNat (sqir_style_compareConst_candidate bits q_start c flagPos)
          (update (cuccaro_input_F q_start false 0 ((x + c) % N)) flagPos
            (decide (N ≤ x + c)))))
    = (x + c) % N % 2^bits := by
    apply cuccaro_target_val_eq_sum_when_bits_match
    intro i hi
    -- Decoder reads target register at odd offsets (q_start + 2*i + 1).
    -- X(flagPos) at q_start + 2*i + 1 ≠ flagPos because flagPos is outside
    -- workspace while q_start + 2*i + 1 ∈ [q_start, q_start + 2*bits + 1).
    have h_target_ne_flag : (q_start + 2 * i + 1 : Nat) ≠ flagPos := by
      rcases hflag_out with hl | hr
      · omega
      · omega
    rw [Gate.applyNat_X]
    rw [update_neq _ _ _ _ h_target_ne_flag]
    -- compareConst at workspace position = identity (workspace_restored).
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits q_start c flagPos _
          hflag_out (q_start + 2 * i + 1) (by omega) (by omega)]
    rw [update_neq _ _ _ _ h_target_ne_flag]
    exact cuccaro_input_F_at_b q_start i false 0 ((x + c) % N)
  rw [h_eq]
  exact Nat.mod_eq_of_lt h_xc_mod_N_lt

/-- **HEADLINE Deliverable E — clean candidate target preservation.**
The clean candidate's decoded target equals `(x + c) % N`. -/
theorem sqir_style_modAddConst_clean_candidate_target_decode
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N) :
    cuccaro_target_val bits 2
        (Gate.applyNat
          (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false))
      = (x + c) % N := by
  show cuccaro_target_val bits 2
      (Gate.applyNat
        (seq (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
              (seq (sqir_style_compareConst_candidate bits 2 c 1)
                   (Gate.X 1))) _) = _
  simp only [Gate.applyNat_seq]
  have hflag_out : (1 : Nat) < 2 ∨ 2 + 2 * bits + 1 ≤ 1 := Or.inl (by omega)
  have h_flag_distinct : ∀ j, j < bits → (1 : Nat) ≠ 2 + 2 * j + 2 := fun j _ => by omega
  rw [sqir_style_modAddConst_dirtyFlag_state_eq bits 2 N c x 1
        hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
  -- Goal: target_val of (applyNat (X 1) (applyNat compareConst(c) (update (cuccaro_input_F ((x+c)%N)) 1 (decide)))) = (x+c) % N.
  have h_xc_mod_N_lt : (x + c) % N < 2 ^ bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  have h_eq : cuccaro_target_val bits 2
      (Gate.applyNat (Gate.X 1)
        (Gate.applyNat (sqir_style_compareConst_candidate bits 2 c 1)
          (update (cuccaro_input_F 2 false 0 ((x + c) % N)) 1 (decide (N ≤ x + c)))))
    = (x + c) % N % 2^bits := by
    apply cuccaro_target_val_eq_sum_when_bits_match
    intro i hi
    -- X(1) at q_start + 2*i + 1 = 2 + 2*i + 1 ≥ 3 ≠ 1 → no-op.
    rw [Gate.applyNat_X]
    rw [update_neq _ _ _ _ (by omega : (2 + 2 * i + 1 : Nat) ≠ 1)]
    -- compareConst at workspace position = identity (workspace_restored).
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 c 1 _
          hflag_out (2 + 2 * i + 1) (by omega) (by omega)]
    -- update at 1 ≠ 2 + 2*i + 1.
    rw [update_neq _ _ _ _ (by omega : (2 + 2 * i + 1 : Nat) ≠ 1)]
    exact cuccaro_input_F_at_b 2 i false 0 ((x + c) % N)
  rw [h_eq]
  exact Nat.mod_eq_of_lt h_xc_mod_N_lt

/-- **HEADLINE Deliverable F — clean candidate full bundle.**
WellTyped + target = (x+c)%N + read restored + top-carry restored + flag restored. -/
theorem sqir_style_modAddConst_clean_candidate_clean
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = (x + c) % N
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 1
        = false := by
  have hflag_out : (1 : Nat) < 2 ∨ 2 + 2 * bits + 1 ≤ 1 := Or.inl (by omega)
  have h_flag_distinct : ∀ j, j < bits → (1 : Nat) ≠ 2 + 2 * j + 2 := fun j _ => by omega
  have h_xc_mod_N_lt : (x + c) % N < 2 ^ bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- WellTyped: clean candidate = seq dirtyFlag (seq compareConst (X 1)).
    show Gate.WellTyped (sqir_modmult_rev_anc bits)
        (seq (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
              (seq (sqir_style_compareConst_candidate bits 2 c 1)
                   (Gate.X 1)))
    refine ⟨?_, ?_, ?_⟩
    · exact sqir_style_modAddConst_dirtyFlag_candidate_wellTyped_sqir_layout bits N c hbits
    · apply sqir_style_compareConst_candidate_wellTyped bits 2 c 1
        (sqir_modmult_rev_anc bits)
      · unfold sqir_modmult_rev_anc; omega
      · unfold sqir_modmult_rev_anc; omega
      · omega
    · show 1 < sqir_modmult_rev_anc bits
      unfold sqir_modmult_rev_anc; omega
  · exact sqir_style_modAddConst_clean_candidate_target_decode bits N c x
      hbits hN_pos hN hN2 hc_pos hc hx
  · -- read = 0.  Same structure as target_decode, but at read positions.
    show cuccaro_read_val bits 2
        (Gate.applyNat
          (seq (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
                (seq (sqir_style_compareConst_candidate bits 2 c 1)
                     (Gate.X 1))) _) = _
    simp only [Gate.applyNat_seq]
    rw [sqir_style_modAddConst_dirtyFlag_state_eq bits 2 N c x 1
          hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
    have h_eq : cuccaro_read_val bits 2
        (Gate.applyNat (Gate.X 1)
          (Gate.applyNat (sqir_style_compareConst_candidate bits 2 c 1)
            (update (cuccaro_input_F 2 false 0 ((x + c) % N)) 1 (decide (N ≤ x + c)))))
      = 0 % 2^bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      rw [Gate.applyNat_X]
      rw [update_neq _ _ _ _ (by omega : (2 + 2 * i + 2 : Nat) ≠ 1)]
      rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 c 1 _
            hflag_out (2 + 2 * i + 2) (by omega) (by omega)]
      rw [update_neq _ _ _ _ (by omega : (2 + 2 * i + 2 : Nat) ≠ 1)]
      rw [cuccaro_input_F_at_a 2 i false 0 ((x + c) % N)]
    rw [h_eq]
    simp
  · -- top carry at 2 + 2*bits = false.  Use workspace_restored.
    show Gate.applyNat
        (seq (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
              (seq (sqir_style_compareConst_candidate bits 2 c 1)
                   (Gate.X 1))) _ _ = _
    simp only [Gate.applyNat_seq]
    rw [sqir_style_modAddConst_dirtyFlag_state_eq bits 2 N c x 1
          hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out]
    rw [Gate.applyNat_X]
    rw [update_neq _ _ _ _ (by omega : (2 + 2 * bits : Nat) ≠ 1)]
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 c 1 _
          hflag_out (2 + 2 * bits) (by omega) (by omega)]
    rw [update_neq _ _ _ _ (by omega : (2 + 2 * bits : Nat) ≠ 1)]
    -- cuccaro_input_F at 2 + 2*bits = 2 + 2*(bits-1) + 2 = a.testBit (bits-1) with a = 0 = false.
    have h_eq : (2 : Nat) + 2 * bits = 2 + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 ((x + c) % N)]
    simp [Nat.zero_testBit]
  · exact sqir_style_modAddConst_clean_candidate_flag_restored bits N c x
      hbits hN_pos hN hN2 hc_pos hc hx

/-! ## Tick 64 — c = 0 identity case. -/

/-- The wrapper at `c = 0` reduces to `Gate.I`. -/
theorem sqir_style_modAddConst_clean_gate_zero_eq
    (bits N : Nat) :
    sqir_style_modAddConst_clean_gate bits N 0 = Gate.I := by
  unfold sqir_style_modAddConst_clean_gate; simp

/-- **Deliverable B — c = 0 bundle.**  At `c = 0` the gate is the
identity, so all 5 conjuncts (WellTyped + target = x + read = 0 +
top carry = false + flag = false) reduce to facts about the input
encoding. -/
theorem sqir_style_modAddConst_clean_gate_zero_clean
    (bits N x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_modAddConst_clean_gate bits N 0)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_gate bits N 0)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = x
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_gate bits N 0)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_gate bits N 0)
          (update (cuccaro_input_F 2 false 0 x) 1 false) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_gate bits N 0)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 1
        = false := by
  rw [sqir_style_modAddConst_clean_gate_zero_eq]
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Gate.WellTyped at I = 0 < dim.
    show Gate.WellTyped (sqir_modmult_rev_anc bits) Gate.I
    show 0 < sqir_modmult_rev_anc bits
    unfold sqir_modmult_rev_anc; omega
  · -- target_val = x.
    show cuccaro_target_val bits 2
        (Gate.applyNat Gate.I (update (cuccaro_input_F 2 false 0 x) 1 false)) = x
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_target_val bits 2
          (update (cuccaro_input_F 2 false 0 x) 1 false) = x % 2 ^ bits := by
      apply cuccaro_target_val_eq_sum_when_bits_match
      intro i hi
      rw [update_neq _ _ _ _ (by omega : (2 + 2 * i + 1 : Nat) ≠ 1)]
      exact cuccaro_input_F_at_b 2 i false 0 x
    rw [h_eq]
    exact Nat.mod_eq_of_lt h_x_lt
  · -- read_val = 0.
    show cuccaro_read_val bits 2
        (Gate.applyNat Gate.I (update (cuccaro_input_F 2 false 0 x) 1 false)) = 0
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_read_val bits 2
          (update (cuccaro_input_F 2 false 0 x) 1 false) = 0 % 2 ^ bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      rw [update_neq _ _ _ _ (by omega : (2 + 2 * i + 2 : Nat) ≠ 1)]
      rw [cuccaro_input_F_at_a 2 i false 0 x]
    rw [h_eq]
    simp
  · -- top carry at 2 + 2*bits = false.
    rw [Gate.applyNat_I]
    rw [update_neq _ _ _ _ (by omega : (2 + 2 * bits : Nat) ≠ 1)]
    have h_eq : (2 : Nat) + 2 * bits = 2 + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 x]
    exact Nat.zero_testBit _
  · -- flag at 1 = false (update_eq).
    rw [Gate.applyNat_I]
    exact update_eq _ _ _

/-! ## Tick 64 — Deliverable C: total clean theorem. -/

/-- **HEADLINE Deliverable C — total clean modular add-constant theorem.**

For all `c < N` (including `c = 0`), the wrapper's output satisfies:
WellTyped + target = `(x+c) % N` + read = 0 + top carry = false +
flag = false. -/
theorem sqir_style_modAddConst_clean_gate_clean
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_modAddConst_clean_gate bits N c)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_gate bits N c)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = (x + c) % N
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_gate bits N c)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_gate bits N c)
          (update (cuccaro_input_F 2 false 0 x) 1 false) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_gate bits N c)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 1
        = false := by
  by_cases hc0 : c = 0
  · -- c = 0 case: target = x = (x + 0) % N.
    subst hc0
    have ⟨h_wt, h_tgt, h_rd, h_tc, h_fl⟩ :=
      sqir_style_modAddConst_clean_gate_zero_clean bits N x hbits hN_pos hN hx
    refine ⟨h_wt, ?_, h_rd, h_tc, h_fl⟩
    rw [h_tgt]
    -- x = (x + 0) % N
    rw [Nat.add_zero]
    exact (Nat.mod_eq_of_lt hx).symm
  · -- 0 < c case: dispatch to the clean candidate's bundle.
    have hc_pos : 0 < c := Nat.pos_of_ne_zero hc0
    have h_unfold : sqir_style_modAddConst_clean_gate bits N c
        = sqir_style_modAddConst_clean_candidate bits 2 N c 1 := by
      unfold sqir_style_modAddConst_clean_gate
      simp [hc0]
    rw [h_unfold]
    exact sqir_style_modAddConst_clean_candidate_clean bits N c x
      hbits hN_pos hN hN2 hc_pos hc hx

/-! ## Tick 64 — Deliverable D: `BasicSetting`-derived wrapper. -/

/-- **HEADLINE Deliverable D — BasicSetting-derived total clean
mod-add-constant theorem.**  At `bits := n + 1`, the SQIR-faithful
sizing `2*N ≤ 2^(n+1)` follows from `BasicSetting`, removing the
explicit `hN`, `hN2`, `hN_pos` preconditions. -/
theorem sqir_style_modAddConst_clean_gate_clean_from_BasicSetting
    (a r N m n c x : Nat)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (hc : c < N) (hx : x < N) :
    Gate.WellTyped (sqir_modmult_rev_anc (n + 1))
        (sqir_style_modAddConst_clean_gate (n + 1) N c)
    ∧ cuccaro_target_val (n + 1) 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_gate (n + 1) N c)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = (x + c) % N
    ∧ cuccaro_read_val (n + 1) 2
          (Gate.applyNat
            (sqir_style_modAddConst_clean_gate (n + 1) N c)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_gate (n + 1) N c)
          (update (cuccaro_input_F 2 false 0 x) 1 false) (2 + 2 * (n + 1))
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_clean_gate (n + 1) N c)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 1
        = false := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have hN_le : N ≤ 2 ^ (n + 1) := by omega
  exact sqir_style_modAddConst_clean_gate_clean (n + 1) N c x
    (by omega : 1 ≤ n + 1) hN_pos hN_le hN2 hc hx

/-! ## Tick 64 — Deliverable E: controlled-modadd route analysis.

The clean modular add-constant gate (Deliverables A–D) is now total
over `c ∈ [0, N)` at the SQIR-faithful layout.  Phase 3 of the
modarith-to-modexp plan is **controlled modular addition** — needed
by the modular multiplier, which iterates over bits of the
multiplicand.

**Important warning (per Tick 64 directive):** do not assume
"control the whole clean modadd gate" works mechanically.  Two
routes to consider:

**Route 1 — Port SQIR's `bygatectrl` infrastructure.**

In Coq SQIR, `bygatectrl 1 g` builds a controlled version of `g`
gate-by-gate.  Each CX becomes CCX, each X becomes CX, etc.  Our
`Gate` IR (`I`, `X`, `CX`, `CCX`, `seq`) does not have a 4-qubit
gate, so any `CCX` inside the inner gate cannot be controlled
directly.  Inside the clean candidate, `CCX` appears (e.g., inside
`cuccaro_MAJ`).  Naive `bygatectrl` would require a 4-input gate
or an additional ancilla qubit.

**Route 2 — Build controlled mod-add-constant by masking the
constant.**

The clean candidate's first stage is `addConstGate(c)`, which adds
the constant `c` to the target.  If we replace this with a *masked*
add-constant — where the prepared `c` is XORed with the control bit
— then:
  - control = false ⇒ the masked-prepared read register is `0`, so
    addConstGate has no effect on the target (just runs the
    cuccaro adder with `a = 0`, which is identity at the target).
  - control = true ⇒ the masked-prepared read register is `c`, so
    addConstGate adds `c`.

The subsequent compareConst, conditionalSub, and flag-uncomputation
stages must also be control-aware.  Naively running them
unconditionally would give:
  - control = false: target unchanged = `x`.  Then compareConst
    computes `decide(N ≤ x) = false` (since `x < N`), so the flag
    XOR is no-op.  conditionalSub with flag = false is identity.
    Then the cleanup compareConst(c) computes `decide(c ≤ x)`,
    which is `false` iff `x < c`.  The `X(1)` flip then negates a
    bit that may or may not have been changed.  This DOES NOT
    cleanly handle the `control = false` case.

The cleanest path is therefore:

**Route 3 (selected for Tick 65) — Wrap the entire clean modadd
gate with a `bygatectrl`-style construction that controls every
gate operation by `control`.**  Since our IR has `CCX` but no
4-input gate, the strategy is:
  - `I` controlled by `ctrl` → `I`.
  - `X(q)` controlled by `ctrl` → `CX(ctrl, q)`.
  - `CX(c, t)` controlled by `ctrl` → `CCX(ctrl, c, t)`.
  - `CCX(a, b, c)` controlled by `ctrl` → would need 4-input; this
    is the structural problem.

The CCX gates inside the cuccaro_MAJ chain are the blocker.  Two
sub-options:
  (a) Use one ancilla `aux` qubit to decompose `controlled-CCX`:
      `CCX(ctrl, c, t)` becomes a Toffoli cascade through `aux`.
  (b) Replace the entire clean modular adder with a structurally
      different design (e.g., port SQIR's `modadder21` directly
      with control wired in at the masked-prepare level).

We will pursue option (b) for Tick 65 — masking the constant
via CX from `control` is structurally simpler and avoids the
auxiliary qubit.  The `compareConst` and conditional sub stages
must then be examined for whether their CCX content survives the
masking.

**Pending Tick 65 questions** (will be added to QUESTIONS.md):
  - Does masking `c` to `0` when `control = false` make the
    cleanup XOR + `X(1)` correctly identity?
  - Or must we ALSO mask `N` (in the comparator) by `control`?
    The cleanup uses `compareConst(c) ; X(1)`; if `c` is masked,
    `c = 0` would fire the broken `compareConst(0)` case (the
    `K = 2^bits` overflow).  We may need an additional guard. -/

/-! ## Tick 65 — Controlled SQIR modular add-constant: design + Task 3 + definitions.

**Route selected (per Python simulation, `scripts/check_sqir_controlled_modadd.py`):**
Route B — control-aware masked constants.  Candidate B (full-control)
passes all `bits ∈ {1..4}, 0 < N ≤ 2^bits / 2, 0 < c < N, x < N,
control ∈ {false, true}` test cases.  Candidate A (naive — control only
stage 1) FAILS for `control = false, c > 0` because the unconditional
cleanup `compareConst(c) ; X(1)` dirties the flag.  Candidate C
(Candidate B with `c = 0` wrapper) also passes, extending to `c = 0`.

**Controlled construction** (5 stages):
  1. `sqir_conditionalAddConstGate(bits, q_start, c, controlIdx)` — adds
     `c` to target iff `controlIdx`.
  2. `sqir_style_compareConst_candidate(bits, q_start, N, flagPos)` —
     UNCONDITIONAL: flag XOR `decide(N ≤ target)`.
  3. `sqir_conditionalSubConstGate(bits, q_start, N, flagPos)` —
     conditional on flag.
  4. `sqir_controlledCompareConst(bits, q_start, c, controlIdx, flagPos)` —
     masked cleanup; control-aware.
  5. `Gate.CX controlIdx flagPos` — control-aware flag flip.

When `control = false`:
- Stage 1 is identity (masked prepare ↔ K=0, full adder on `read = 0` =
  identity at target).
- Stage 2 sets flag := decide(N ≤ x) = false (since `x < N`).
- Stage 3 is identity (flag = false).
- Stage 4 is identity (masked prepare ↔ K=0; compareConst on read=0
  gives top_carry = decide(target ≥ 2^bits) = false; no flag change).
- Stage 5 (CX with control=false) is identity.
- Net: target = x, flag = false, controlIdx preserved. ✓

When `control = true`:
- Stage 1 = `addConstGate(c)` (via `apply_true_fun`).
- Stages 2-3 = unconditional dirtyFlag's compareConst(N) and conditionalSub(N).
- Stage 4 = `compareConst(c)` (masked prepare with control=true = unmasked).
- Stage 5 (CX with control=true) = `X(flagPos)`.
- Net = Tick 63 `clean_candidate`'s chain: target = (x+c) % N, flag = false. ✓
-/

/-! ## Tick 65 Task 3 — controlled add-mod-2^bits theorem (alias).

The existing `sqir_conditionalAddConstGate_target_decode` already
provides this; we re-expose it under the controlled-add semantic
name. -/

/-- **HEADLINE Task 3 — controlled add-mod-2^bits target decode.** -/
theorem sqir_controlledAddConstPow2_target_decode
    (bits q_start c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_conditionalAddConstGate bits q_start c controlIdx)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control))
      = (x + (if control then c else 0)) % 2^bits :=
  sqir_conditionalAddConstGate_target_decode bits q_start c x controlIdx control
    hbits hc hx h_control_distinct h_control_out

/-! ## Status note (Tick 65 part 1).

Landed (kernel-clean):
- Definition of `sqir_controlledCompareConst`.
- Definition of `sqir_style_controlledModAddConst_candidate`.
- Definition of `sqir_style_controlledModAddConst_gate` (total wrapper).
- Task 3 alias `sqir_controlledAddConstPow2_target_decode`.

**Not landed this tick** (Tick 66 work — explicitly deferred):
- `sqir_style_controlledModAddConst_*_target_decode` for the candidate
  (the per-control target value theorem).
- Full clean bundle (WellTyped + target + workspace + flag + control).
- BasicSetting-derived specialization.

Reason for deferral: the semantic theorems require chain-reduction
through 5 controlled stages with case-split on `control`.  Tick 65's
deliverable focus per directive is "first semantic theorem" — and
Task 3 provides one (the controlled add-mod-2^bits target decode),
empirically validating the controlled add primitive that drives
stage 1.  Simulation (Task 2) provides empirical validation of the
full controlled candidate; Tick 66 will land the formal semantic
theorems following the design now confirmed.

**Simulation result** (`scripts/check_sqir_controlled_modadd.py`):
- Candidate B (controlled stages 1, 4, 5): PASSES 380/380 for
  `bits ∈ {1..4}, 0 < N ≤ 2^bits/2, 0 < c < N, x < N`.
- Candidate C (B + c=0 wrapper): PASSES 480/480 over the same range
  with `c ∈ [0, N)`.
- Candidate A (naive — control only stage 1): FAILS (95 fails for
  `control = false` due to spurious flag from the unconditional
  cleanup). -/

/-! ## Tick 66 — Controlled SQIR mod-N add semantic correctness.

This tick proves the target_decode theorem (Deliverable C) for the
controlled mod-N add candidate by case-splitting on `control`, plus
the total wrapper target_decode (Deliverable F) and a BasicSetting-
derived specialization (Deliverable G).

The full clean bundle (Deliverables A, B, D, E with workspace/flag
conjuncts) is deferred to Tick 67 — the position-level chain
analysis through all 5 controlled stages for read/carry/flag
positions is substantial enough to merit its own tick. -/

/-- **Helper — `ctrlCompare` reduces to `compareConst(c)` when
`state[controlIdx] = true`.**  Function-level equality. -/
theorem sqir_controlledCompareConst_at_control_true_eq_unmasked_fun
    (bits q_start c controlIdx flagPos : Nat) (g : Nat → Bool)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (h_control_ne_flag : controlIdx ≠ flagPos)
    (h_control_true : g controlIdx = true) :
    Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos) g
      = Gate.applyNat (sqir_style_compareConst_candidate bits q_start c flagPos) g := by
  show Gate.applyNat
      (seq (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx))))) g
    = Gate.applyNat
        (seq (cuccaro_prepareConstRead bits q_start (2^bits - c))
              (seq (cuccaro_maj_chain bits q_start)
                   (seq (Gate.CX (q_start + 2 * bits) flagPos)
                        (seq (cuccaro_maj_chain_inv bits q_start)
                             (cuccaro_prepareConstRead bits q_start (2^bits - c)))))) g
  simp only [Gate.applyNat_seq]
  -- Inner-most masked prepare → unmasked (state at controlIdx = true).
  rw [sqir_prepareMaskedConstRead_eq_unmasked_fun bits q_start (2^bits - c) controlIdx g
        h_control_distinct h_control_true]
  -- Outer masked prepare → unmasked.  Need state at controlIdx after the
  -- inner stages = true.  The inner stages (prepare, maj_chain, CX, maj_chain_inv)
  -- all preserve controlIdx because it's outside workspace and ≠ flagPos.
  have h_inner_ctrl_preserved :
      Gate.applyNat (cuccaro_maj_chain_inv bits q_start)
        (Gate.applyNat (Gate.CX (q_start + 2 * bits) flagPos)
          (Gate.applyNat (cuccaro_maj_chain bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - c)) g))) controlIdx
        = true := by
    rcases h_control_out with h_below | h_above
    · rw [cuccaro_maj_chain_inv_frame_below bits q_start _ controlIdx h_below]
      rw [Gate.applyNat_CX, update_neq _ _ _ _ h_control_ne_flag]
      rw [cuccaro_maj_chain_frame_below bits q_start _ controlIdx h_below]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - c) controlIdx
            h_control_distinct]
      exact h_control_true
    · rw [cuccaro_maj_chain_inv_frame_above bits q_start _ controlIdx h_above]
      rw [Gate.applyNat_CX, update_neq _ _ _ _ h_control_ne_flag]
      rw [cuccaro_maj_chain_frame_above bits q_start _ controlIdx h_above]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - c) controlIdx
            h_control_distinct]
      exact h_control_true
  rw [sqir_prepareMaskedConstRead_eq_unmasked_fun bits q_start (2^bits - c) controlIdx _
        h_control_distinct h_inner_ctrl_preserved]

/-! ## Tick 66 — Total wrapper c = 0 case (partial Deliverable F). -/

/-- **Total wrapper at c = 0 reduces to `Gate.I`.** -/
theorem sqir_style_controlledModAddConst_gate_zero_eq
    (bits N controlIdx : Nat) :
    sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1 = Gate.I := by
  unfold sqir_style_controlledModAddConst_gate; simp

/-- **HEADLINE partial Deliverable F — c = 0 bundle for the controlled
modular add-constant wrapper.** -/
theorem sqir_style_controlledModAddConst_gate_zero_clean
    (bits N x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = x
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) 1
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx
        = control := by
  rw [sqir_style_controlledModAddConst_gate_zero_eq]
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Gate.WellTyped (sqir_modmult_rev_anc bits) Gate.I
    show 0 < sqir_modmult_rev_anc bits
    unfold sqir_modmult_rev_anc; omega
  · -- target_val = x.
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_target_val bits 2
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) = x % 2 ^ bits := by
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
  · -- read_val = 0.
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_read_val bits 2
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) = 0 % 2 ^ bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      have h_ne : (2 + 2 * i + 2 : Nat) ≠ controlIdx := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      rw [update_neq _ _ _ _ h_ne]
      rw [cuccaro_input_F_at_a 2 i false 0 x]
    rw [h_eq]
    simp
  · -- top carry at 2 + 2*bits.
    rw [Gate.applyNat_I]
    have h_ne : (2 + 2 * bits : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    have h_eq : (2 : Nat) + 2 * bits = 2 + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 x]
    exact Nat.zero_testBit _
  · -- flag at 1.
    rw [Gate.applyNat_I]
    rw [update_neq _ _ _ _ hcontrol_ne_flag.symm]
    -- cuccaro_input_F at 1 = false (since 1 < q_start = 2).
    unfold cuccaro_input_F
    rw [if_pos (by omega : (1 : Nat) < 2)]
  · -- controlIdx = control.
    rw [Gate.applyNat_I]
    exact update_eq _ _ _

/-! ## Tick 67 — Closing the controlled mod-N add chain.

Stage helpers to compose into the full controlled candidate's
semantic theorem. -/

/-- **Deliverable B — CX with control = false is identity.** -/
theorem Gate.applyNat_CX_at_control_false_eq_id_fun
    (control target : Nat) (f : Nat → Bool) (h : f control = false) :
    Gate.applyNat (Gate.CX control target) f = f := by
  funext q
  rw [Gate.applyNat_CX, h, Bool.xor_false]
  by_cases hq : q = target
  · rw [hq, update_eq]
  · rw [update_neq _ _ _ _ hq]

/-- **Deliverable B — CX with control = true equals X(target).** -/
theorem Gate.applyNat_CX_at_control_true_eq_X_fun
    (control target : Nat) (f : Nat → Bool) (h : f control = true) :
    Gate.applyNat (Gate.CX control target) f = Gate.applyNat (Gate.X target) f := by
  rw [Gate.applyNat_CX, Gate.applyNat_X, h]
  congr 1
  cases f target <;> rfl

/-- **Helper — maj_chain on `cuccaro_input_F` with `a = 0` has top carry = false.**
Derived from `cuccaro_compareConstForward_top_carry` with `N = 2^bits`
(reducing the prepare to identity). -/
theorem cuccaro_maj_chain_top_carry_on_input_F_zero_a
    (bits q_start x : Nat) (hbits : 1 ≤ bits) (hx : x < 2^bits) :
    Gate.applyNat (cuccaro_maj_chain bits q_start)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * bits) = false := by
  have h_pos : 0 < (2 : Nat)^bits := Nat.two_pow_pos bits
  have h := cuccaro_compareConstForward_top_carry bits q_start (2^bits) x h_pos
              (le_refl _) hx
  unfold cuccaro_compareConstForwardGate at h
  simp only [Gate.applyNat_seq] at h
  have h_K : (2 : Nat)^bits - 2^bits = 0 := by omega
  rw [h_K] at h
  rw [cuccaro_prepareConstRead_zero_eq_id_fun] at h
  simp [Nat.not_le.mpr hx] at h
  exact h

/-- **Deliverable A — controlled comparator at control = false is identity
on `cuccaro_input_F`-shaped input.** -/
theorem sqir_controlledCompareConst_at_control_false_on_input_F_eq_id_fun
    (bits q_start c controlIdx flagPos x : Nat)
    (hbits : 1 ≤ bits) (hx : x < 2^bits)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (h_control_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
        (update (cuccaro_input_F q_start false 0 x) controlIdx false)
      = update (cuccaro_input_F q_start false 0 x) controlIdx false := by
  set F := cuccaro_input_F q_start false 0 x with hF_def
  show Gate.applyNat
      (seq (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)))))
      (update F controlIdx false)
    = update F controlIdx false
  simp only [Gate.applyNat_seq]
  -- Stage 1: masked prepare with ctrl=false → identity.
  have h_input_ctrl : (update F controlIdx false) controlIdx = false := update_eq _ _ _
  rw [sqir_prepareMaskedConstRead_eq_id_fun bits q_start (2^bits - c) controlIdx
        (update F controlIdx false) h_control_distinct h_input_ctrl]
  -- Stage 3 (CX): need state at top = false.
  -- State entering CX = applyNat maj_chain (update F controlIdx false).
  have h_top_state : Gate.applyNat (cuccaro_maj_chain bits q_start)
        (update F controlIdx false) (q_start + 2 * bits) = false := by
    rw [cuccaro_maj_chain_commute_update_outside_workspace bits q_start controlIdx false F
          h_control_out]
    have h_ne : q_start + 2 * bits ≠ controlIdx := by
      rcases h_control_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    exact cuccaro_maj_chain_top_carry_on_input_F_zero_a bits q_start x hbits hx
  -- CX is identity (xor with false → no change).
  rw [Gate.applyNat_CX_at_control_false_eq_id_fun (q_start + 2 * bits) flagPos _ h_top_state]
  -- Stage 4: maj_chain_inv ∘ maj_chain = id.
  rw [cuccaro_maj_chain_inv_after_chain_eq_id bits q_start (update F controlIdx false)]
  -- Stage 5: masked prepare with state[ctrl] = false (still true after the no-op chain).
  rw [sqir_prepareMaskedConstRead_eq_id_fun bits q_start (2^bits - c) controlIdx
        (update F controlIdx false) h_control_distinct h_input_ctrl]

/-! ## Tick 68 — Compose controlled mod-N add chain. -/

/-- **Deliverable A — uncontrolled comparator identity on `cuccaro_input_F`
when `x < N`.**  Since `decide(N ≤ x) = false`, the comparator XORs false
into flagPos (no change), and workspace + outside positions are preserved. -/
theorem sqir_style_compareConst_candidate_on_input_F_x_lt_N_eq_id_fun
    (bits N x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N) :
    Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
        (cuccaro_input_F 2 false 0 x)
      = cuccaro_input_F 2 false 0 x := by
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have hflag_out : (1 : Nat) < 2 ∨ 2 + 2 * bits + 1 ≤ 1 := Or.inl (by omega)
  funext q
  by_cases hq_flag : q = 1
  · rw [hq_flag]
    rw [sqir_style_compareConst_candidate_flag_general bits 2 N x 1
          hN_pos hN h_x_lt hflag_out]
    have h_F1 : cuccaro_input_F 2 false 0 x 1 = false := by
      unfold cuccaro_input_F; rw [if_pos (by omega : (1 : Nat) < 2)]
    rw [h_F1]
    exact decide_eq_false (Nat.not_le.mpr hx)
  · by_cases hq_ws : 2 ≤ q ∧ q < 2 + 2 * bits + 1
    · exact sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 N 1
        _ hflag_out q hq_ws.1 hq_ws.2
    · push_neg at hq_ws
      have h_q_outside : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := by
        by_cases h : q < 2
        · left; exact h
        · push_neg at h; right; exact hq_ws h
      exact sqir_style_compareConst_candidate_frame_outside bits 2 N 1
        _ q hq_flag h_q_outside

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

/-! ## Phase R7d^xxix-L-3.6′ — q_start-parametric ports

The five q_start-parametric ports below mirror the corresponding
q_start = 2 / flagPos = 1 helpers above. They unlock the
Architecture D selected-add no-op proofs by providing the
control = false target-decode at the shifted layout.

The proofs are mechanical parameter-substituted copies; all
subordinate lemmas were already q_start-parametric (we verified
this during R7d^xxix-L-3.6′ planning). -/

/-- **q_start-parametric variant** of
`cuccaro_input_F_at_controlIdx_outside_eq_false`. Same fact, fully
parametric. -/
theorem cuccaro_input_F_at_controlIdx_outside_eq_false_qstart
    (q_start bits x controlIdx : Nat) (hx : x < 2^bits)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    cuccaro_input_F q_start false 0 x controlIdx = false :=
  cuccaro_input_F_at_outside_eq_false q_start bits x controlIdx hcontrol_out hx

/-- **q_start-parametric variant** of `update_input_F_controlIdx_false_eq_F`. -/
theorem update_input_F_controlIdx_false_eq_F_qstart
    (q_start bits x controlIdx : Nat) (hx : x < 2^bits)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    update (cuccaro_input_F q_start false 0 x) controlIdx false
      = cuccaro_input_F q_start false 0 x := by
  funext q
  by_cases hq : q = controlIdx
  · rw [hq, update_eq]
    exact (cuccaro_input_F_at_controlIdx_outside_eq_false_qstart q_start bits x controlIdx hx
      hcontrol_out).symm
  · rw [update_neq _ _ _ _ hq]

/-- **q_start-parametric variant** of
`sqir_style_compareConst_candidate_on_input_F_x_lt_N_eq_id_fun`.
Adds an explicit `hflag_out` hypothesis so `flagPos` can be at any
outside-workspace position. -/
theorem sqir_style_compareConst_candidate_on_input_F_x_lt_N_eq_id_fun_qstart
    (bits q_start N flagPos x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (cuccaro_input_F q_start false 0 x)
      = cuccaro_input_F q_start false 0 x := by
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  funext q
  by_cases hq_flag : q = flagPos
  · rw [hq_flag]
    rw [sqir_style_compareConst_candidate_flag_general bits q_start N x flagPos
          hN_pos hN h_x_lt hflag_out]
    have h_F_at_flag : cuccaro_input_F q_start false 0 x flagPos = false :=
      cuccaro_input_F_at_controlIdx_outside_eq_false_qstart q_start bits x flagPos h_x_lt
        hflag_out
    rw [h_F_at_flag]
    exact decide_eq_false (Nat.not_le.mpr hx)
  · by_cases hq_ws : q_start ≤ q ∧ q < q_start + 2 * bits + 1
    · exact sqir_style_compareConst_candidate_workspace_restored_at_general bits q_start N flagPos
        _ hflag_out q hq_ws.1 hq_ws.2
    · push_neg at hq_ws
      have h_q_outside : q < q_start ∨ q_start + 2 * bits + 1 ≤ q := by
        by_cases h : q < q_start
        · left; exact h
        · push_neg at h; right; exact hq_ws h
      exact sqir_style_compareConst_candidate_frame_outside bits q_start N flagPos
        _ q hq_flag h_q_outside

/-- **q_start-parametric variant** of
`sqir_style_controlledModAddConst_candidate_control_false_state_eq`.
When the control is false, the controlled mod-add candidate is the
identity on the appropriate base state. Parametric in both
`q_start` and `flagPos`. -/
theorem sqir_style_controlledModAddConst_candidate_control_false_state_eq_qstart
    (bits q_start N c x controlIdx flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
        (update (cuccaro_input_F q_start false 0 x) controlIdx false)
      = update (cuccaro_input_F q_start false 0 x) controlIdx false := by
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have h_F_at_ctrl : cuccaro_input_F q_start false 0 x controlIdx = false :=
    cuccaro_input_F_at_controlIdx_outside_eq_false_qstart q_start bits x controlIdx h_x_lt
      hcontrol_out
  have h_input_eq : update (cuccaro_input_F q_start false 0 x) controlIdx false
                  = cuccaro_input_F q_start false 0 x :=
    update_input_F_controlIdx_false_eq_F_qstart q_start bits x controlIdx h_x_lt hcontrol_out
  rw [h_input_eq]
  show Gate.applyNat
      (seq (sqir_conditionalAddConstGate bits q_start c controlIdx)
            (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                 (seq (sqir_conditionalSubConstGate bits q_start N flagPos)
                      (seq (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
                           (Gate.CX controlIdx flagPos)))))
      (cuccaro_input_F q_start false 0 x) = _
  simp only [Gate.applyNat_seq]
  have h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2 := by
    intros i _ heq
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  -- Stage 1: condAdd with control=false → full_adder → identity on F.
  have h_stage1 : Gate.applyNat (sqir_conditionalAddConstGate bits q_start c controlIdx)
        (cuccaro_input_F q_start false 0 x) = cuccaro_input_F q_start false 0 x := by
    rw [sqir_conditionalAddConstGate_apply_false_fun bits q_start c controlIdx
          (cuccaro_input_F q_start false 0 x) h_control_distinct h_F_at_ctrl hcontrol_out]
    rw [← cuccaro_addConstGate_zero_eq_full_adder_fun]
    have h_pos : 0 < (2 : Nat)^bits := Nat.two_pow_pos bits
    rw [cuccaro_addConstGate_output_eq_cuccaro_input_F bits q_start 0 x hbits h_pos h_x_lt
          (by omega : x + 0 < 2^bits)]
    simp [Nat.add_zero]
  rw [h_stage1]
  -- Stage 2: compareConst F = F (for x < N).
  rw [sqir_style_compareConst_candidate_on_input_F_x_lt_N_eq_id_fun_qstart bits q_start N flagPos
        x hbits hN_pos hN hx hflag_out]
  -- Stage 3: condSub with flag input = false → identity on F.
  have h_F_at_flag : cuccaro_input_F q_start false 0 x flagPos = false :=
    cuccaro_input_F_at_controlIdx_outside_eq_false_qstart q_start bits x flagPos h_x_lt hflag_out
  have h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2 := by
    intros i _ heq
    rcases hflag_out with hl | hr
    · omega
    · omega
  have h_stage3 : Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos)
        (cuccaro_input_F q_start false 0 x) = cuccaro_input_F q_start false 0 x := by
    unfold sqir_conditionalSubConstGate
    rw [sqir_conditionalAddConstGate_apply_false_fun bits q_start (2^bits - N) flagPos
          (cuccaro_input_F q_start false 0 x) h_flag_distinct h_F_at_flag hflag_out]
    rw [← cuccaro_addConstGate_zero_eq_full_adder_fun]
    have h_pos : 0 < (2 : Nat)^bits := Nat.two_pow_pos bits
    rw [cuccaro_addConstGate_output_eq_cuccaro_input_F bits q_start 0 x hbits h_pos h_x_lt
          (by omega : x + 0 < 2^bits)]
    simp [Nat.add_zero]
  rw [h_stage3]
  -- Stage 4: ctrlCompare with state[controlIdx]=false → identity on F.
  have h_stage4 : Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
        (cuccaro_input_F q_start false 0 x) = cuccaro_input_F q_start false 0 x := by
    rw [show cuccaro_input_F q_start false 0 x
        = update (cuccaro_input_F q_start false 0 x) controlIdx false from h_input_eq.symm]
    exact sqir_controlledCompareConst_at_control_false_on_input_F_eq_id_fun
      bits q_start c controlIdx flagPos x hbits h_x_lt h_control_distinct hcontrol_out
      hcontrol_ne_flag
  rw [h_stage4]
  -- Stage 5: CX(controlIdx, flagPos) with state[controlIdx]=false → identity.
  exact Gate.applyNat_CX_at_control_false_eq_id_fun controlIdx flagPos
    (cuccaro_input_F q_start false 0 x) h_F_at_ctrl

/-- **PRIMARY L-3.6′ DELIVERABLE: q_start-parametric control = false
target-decode.** The candidate controlled mod-add gate, applied to the
zero-accumulator Cuccaro base with the control bit set to false,
decodes to `x` at the target. Parametric in both `q_start` and
`flagPos`. -/
theorem sqir_style_controlledModAddConst_candidate_target_decode_control_false_qstart
    (bits q_start N c x controlIdx flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false))
      = x := by
  rw [sqir_style_controlledModAddConst_candidate_control_false_state_eq_qstart
        bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag]
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have h_eq : cuccaro_target_val bits q_start
        (update (cuccaro_input_F q_start false 0 x) controlIdx false) = x % 2 ^ bits := by
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

/-- **R7d^xxix-L-3.7′ DELIVERABLE: q_start-parametric control=false
workspace bundle (4-conjunct).**

Mirrors `sqir_style_controlledModAddConst_candidate_workspace_control_false`
but parametric in `q_start` and `flagPos`.  Both `controlIdx` and
`flagPos` must lie OUTSIDE the Cuccaro workspace
`[q_start, q_start + 2 * bits + 1)` and be distinct.

After the candidate gate applied to `(update F controlIdx false)`:
1. `cuccaro_read_val bits q_start` of the output = 0;
2. position `q_start + 2 * bits` (top carry) = false;
3. position `flagPos` = false;
4. position `controlIdx` = false.

Closes via the already-landed
`sqir_style_controlledModAddConst_candidate_control_false_state_eq_qstart`. -/
theorem sqir_style_controlledModAddConst_candidate_workspace_control_false_qstart
    (bits q_start N c x controlIdx flagPos : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) flagPos
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) controlIdx
        = false := by
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  rw [sqir_style_controlledModAddConst_candidate_control_false_state_eq_qstart
        bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
        hcontrol_out hflag_out hcontrol_ne_flag]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- read = 0.
    have h_eq : cuccaro_read_val bits q_start
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) = 0 % 2 ^ bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      have h_ne : (q_start + 2 * i + 2 : Nat) ≠ controlIdx := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      rw [update_neq _ _ _ _ h_ne]
      rw [cuccaro_input_F_at_a q_start i false 0 x]
    rw [h_eq]; simp
  · -- top carry = false.
    have h_ne : (q_start + 2 * bits : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    have h_eq : q_start + 2 * bits = q_start + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a q_start (bits - 1) false 0 x]
    exact Nat.zero_testBit _
  · -- flag = false.
    rw [update_neq _ _ _ _ hcontrol_ne_flag.symm]
    exact cuccaro_input_F_at_outside_eq_false q_start bits x flagPos hflag_out h_x_lt
  · -- controlIdx = false.
    exact update_eq _ _ _

/-- **R7d^xxix-L-3.8′ DELIVERABLE: q_start-parametric control=false
clean bundle.**

Bundles the already-proved q_start-parametric facts for
`sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx
flagPos` applied to `(update F controlIdx false)`:

1. `Gate.WellTyped dim` of the candidate gate.
2. target decoded value = `x` (no-op on the target).
3. read register = 0.
4. top carry position (`q_start + 2 * bits`) = false.
5. `flagPos` = false.
6. `controlIdx` = false.

Parametric in `q_start`, `flagPos`, `controlIdx`, AND the ambient
dimension `dim`.  Wrapper over:
- `sqir_style_controlledModAddConst_candidate_target_decode_control_false_qstart`,
- `sqir_style_controlledModAddConst_candidate_workspace_control_false_qstart`,
- the five existing q_start-parametric WellTyped sub-lemmas
  (`sqir_conditionalAddConstGate_wellTyped`,
  `sqir_style_compareConst_candidate_wellTyped`,
  `sqir_conditionalSubConstGate_wellTyped`,
  `cuccaro_maj_chain_wellTyped`,
  `cuccaro_maj_chain_inv_wellTyped`,
  `sqir_prepareMaskedConstRead_wellTyped`).

No new infrastructure introduced; control=true direction NOT touched. -/
theorem sqir_style_controlledModAddConst_candidate_clean_control_false_qstart
    (bits q_start N c x dim controlIdx flagPos : Nat)
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
            (update (cuccaro_input_F q_start false 0 x) controlIdx false))
        = x
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
            (update (cuccaro_input_F q_start false 0 x) controlIdx false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) flagPos
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
          (update (cuccaro_input_F q_start false 0 x) controlIdx false) controlIdx
        = false := by
  have h_target :=
    sqir_style_controlledModAddConst_candidate_target_decode_control_false_qstart
      bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
      hcontrol_out hflag_out hcontrol_ne_flag
  obtain ⟨h_rd, h_tc, h_fl, h_ctrl⟩ :=
    sqir_style_controlledModAddConst_candidate_workspace_control_false_qstart
      bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
      hcontrol_out hflag_out hcontrol_ne_flag
  refine ⟨?_, h_target, h_rd, h_tc, h_fl, h_ctrl⟩
  -- WellTyped: 5-stage proof mirroring the hard-coded `_candidate_clean`
  -- but with q_start and flagPos free.
  show Gate.WellTyped dim
      (seq (sqir_conditionalAddConstGate bits q_start c controlIdx)
            (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                 (seq (sqir_conditionalSubConstGate bits q_start N flagPos)
                      (seq (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
                           (Gate.CX controlIdx flagPos)))))
  have h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2 := by
    intros i _ heq
    rcases hcontrol_out with hl | hr
    · omega
    · omega
  have h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2 := by
    intros i _ heq
    rcases hflag_out with hl | hr
    · omega
    · omega
  have h_top_lt_dim : q_start + 2 * bits < dim := by omega
  have h_top_ne_flag : (q_start + 2 * bits : Nat) ≠ flagPos := by
    rcases hflag_out with hl | hr
    · omega
    · omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact sqir_conditionalAddConstGate_wellTyped bits q_start c controlIdx dim
      h_workspace h_control_lt_dim h_control_distinct
  · exact sqir_style_compareConst_candidate_wellTyped bits q_start N flagPos dim
      h_workspace h_flag_lt_dim (Ne.symm h_top_ne_flag)
  · exact sqir_conditionalSubConstGate_wellTyped bits q_start N flagPos dim
      h_workspace h_flag_lt_dim h_flag_distinct
  · -- WellTyped for `sqir_controlledCompareConst` (5-stage subseq).
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact sqir_prepareMaskedConstRead_wellTyped bits q_start (2^bits - c) controlIdx
        dim h_workspace h_control_lt_dim h_control_distinct
    · exact cuccaro_maj_chain_wellTyped bits q_start dim h_workspace
    · -- CX (q_start + 2 * bits) flagPos wellTyped.
      exact ⟨h_top_lt_dim, h_flag_lt_dim, h_top_ne_flag⟩
    · exact cuccaro_maj_chain_inv_wellTyped bits q_start dim h_workspace
    · exact sqir_prepareMaskedConstRead_wellTyped bits q_start (2^bits - c) controlIdx
        dim h_workspace h_control_lt_dim h_control_distinct
  · -- CX controlIdx flagPos wellTyped.
    exact ⟨h_control_lt_dim, h_flag_lt_dim, hcontrol_ne_flag⟩

/-- **Control=false bundle (4-conjunct):** read = 0, top carry = false,
flag = false, controlIdx = false. -/
theorem sqir_style_controlledModAddConst_candidate_workspace_control_false
    (bits N c x controlIdx : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    cuccaro_read_val bits 2
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx false) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx false) 1
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx false) controlIdx
        = false := by
  rw [sqir_style_controlledModAddConst_candidate_control_false_state_eq
        bits N c x controlIdx hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- read = 0.
    have h_eq : cuccaro_read_val bits 2
          (update (cuccaro_input_F 2 false 0 x) controlIdx false) = 0 % 2 ^ bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      have h_ne : (2 + 2 * i + 2 : Nat) ≠ controlIdx := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      rw [update_neq _ _ _ _ h_ne]
      rw [cuccaro_input_F_at_a 2 i false 0 x]
    rw [h_eq]; simp
  · -- top carry = false.
    have h_ne : (2 + 2 * bits : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    have h_eq : (2 : Nat) + 2 * bits = 2 + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 x]
    exact Nat.zero_testBit _
  · -- flag at 1 = false.
    rw [update_neq _ _ _ _ hcontrol_ne_flag.symm]
    unfold cuccaro_input_F
    rw [if_pos (by omega : (1 : Nat) < 2)]
  · -- controlIdx = false.
    exact update_eq _ _ _

end FormalRV.BQAlgo
