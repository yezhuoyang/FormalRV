/- CuccaroCleanModularAddCorrectness — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
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


end FormalRV.BQAlgo
