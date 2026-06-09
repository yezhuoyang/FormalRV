import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultEncoding
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSpec
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultQStart
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultFamily
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSizing
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultBitPositioning
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultPrefixInvariantStepPositions

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
/-! ## Tick 76 — Deliverable D: One-step state equality. -/

/-- **Deliverable D — One-step state equality (function-level).**

After applying the step gate to `sqir_mult_input_F bits m acc`, the
state is exactly `sqir_mult_input_F bits m acc'` where
`acc' = if m.testBit j then (acc + (a*2^j)%N) % N else acc`. -/
theorem sqir_modmult_step_state_eq
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j) (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc) := by
  funext q
  set acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc with hacc'_def
  have hacc'_lt_N : acc' < N := by
    rw [hacc'_def]
    by_cases h : m.testBit j
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact hacc
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  -- Case split on q.
  by_cases hq_above : q ≥ 2 + 2 * bits + 1 + bits
  · -- Above-layout case.
    rw [sqir_modmult_step_above_layout_false bits N a j m acc q hbits hj hq_above]
    -- RHS: sqir_mult_input_F bits m acc' q = false (above layout).
    unfold sqir_mult_input_F
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]
  · push_neg at hq_above
    by_cases hq_in_mult : q ≥ 2 + 2 * bits + 1
    · -- Multiplier register.  q = sqir_mult_control_idx bits k where k = q - (2 + 2*bits + 1).
      set k := q - (2 + 2 * bits + 1) with hk_def
      have hk_lt : k < bits := by omega
      have hq_eq : q = sqir_mult_control_idx bits k := by
        unfold sqir_mult_control_idx; omega
      rw [hq_eq]
      rw [sqir_modmult_step_preserves_all_control_bits bits N a m acc j k
            hbits hN_pos hN hN2 hacc hj hk_lt]
      exact (sqir_mult_input_control_bit bits m acc' k hk_lt).symm
    · push_neg at hq_in_mult
      -- Workspace: q < 2 + 2*bits + 1.
      -- Sub-cases on q.
      by_cases hq_0 : q = 0
      · subst hq_0
        rw [sqir_modmult_step_flag0_false bits N a j m acc hbits hj]
        exact (sqir_mult_input_flag_0_false bits m acc').symm
      by_cases hq_1 : q = 1
      · subst hq_1
        have ⟨_, _, h_fl, _⟩ :=
          sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc
        rw [h_fl]
        exact (sqir_mult_input_flag_1_false bits m acc').symm
      by_cases hq_2 : q = 2
      · subst hq_2
        rw [sqir_modmult_step_carry_in_restored bits N a j m acc hbits hN_pos hN hN2 hj hacc]
        -- RHS: sqir_mult_input_F bits m acc' 2 = cuccaro_input_F at q_start = false.
        unfold sqir_mult_input_F
        rw [if_pos (by omega : (2 : Nat) < 2 + 2 * bits + 1)]
        exact (cuccaro_input_F_at_c_in 2 false 0 acc').symm
      -- q ≥ 3, q ≤ 2 + 2*bits.
      -- Determine parity of (q - 2): if (q - 2) is odd, target bit; if even, read bit.
      -- q - 2 ∈ [1, 2*bits].
      by_cases hq_top : q = 2 + 2 * bits
      · subst hq_top
        have ⟨_, h_tc, _, _⟩ :=
          sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc
        rw [h_tc]
        -- RHS: sqir_mult_input_F bits m acc' (2 + 2*bits)
        --    = cuccaro_input_F 2 false 0 acc' (2 + 2*bits).
        -- Using cuccaro_input_F_at_a with i = bits - 1: position 2 + 2*(bits-1) + 2 = 2 + 2*bits.
        -- Value = 0.testBit (bits - 1) = false.
        have h_eq : (2 + 2 * bits : Nat) = 2 + 2 * (bits - 1) + 2 := by omega
        unfold sqir_mult_input_F
        rw [if_pos (by omega : (2 + 2 * bits : Nat) < 2 + 2 * bits + 1)]
        rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 acc']
        exact (Nat.zero_testBit _).symm
      -- q ∈ [3, 2*bits + 1].  Parity dispatch.
      by_cases h_q_odd : q % 2 = 1
      · -- q odd: q = 2 + 2*i + 1 for i = (q-3)/2 < bits.
        have hi_lt : (q - 3) / 2 < bits := by omega
        have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
        rw [hq_eq]
        rw [sqir_modmult_step_target_bit bits N a j m acc ((q - 3) / 2)
              hbits hN_pos hN hN2 hj hacc hi_lt]
        unfold sqir_mult_input_F
        rw [if_pos (by omega : 2 + 2 * ((q - 3) / 2) + 1 < 2 + 2 * bits + 1)]
        exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc').symm
      · -- q even: q = 2 + 2*i + 2 for i = (q-4)/2 < bits.
        have h_q_even : q % 2 = 0 := by omega
        have hi_lt : (q - 4) / 2 < bits := by omega
        have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
        rw [hq_eq]
        rw [sqir_modmult_step_read_bit bits N a j m acc ((q - 4) / 2)
              hbits hN_pos hN hN2 hj hacc hi_lt]
        unfold sqir_mult_input_F
        rw [if_pos (by omega : 2 + 2 * ((q - 4) / 2) + 2 < 2 + 2 * bits + 1)]
        rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc']
        exact (Nat.zero_testBit _).symm

/-! ## R7d^xxix-L-3.15e.4 — q_start-parametric one-step state
       equality.

`funext q` case split mirrors the hard-coded `sqir_modmult_step_state_eq`
(line 2182) but generalised to free `q_start`, `flagPos`, and `dim`.

Case structure (after `funext q`):
- `q ≥ q_start + 2 * bits + 1 + bits` → above layout (`_step_above_layout_false_qstart`).
- `q_start + 2 * bits + 1 ≤ q` → multiplier register, indexed by
  `k = q - (q_start + 2 * bits + 1)` (`_step_preserves_all_control_bits_qstart`).
- `q < q_start` → workspace-below; split into `q = flagPos`
  (`_step_workspace_qstart` flag conjunct) and `q ≠ flagPos`
  (`_step_at_untouched_pos_qstart`).
- `q_start ≤ q < q_start + 2 * bits + 1` (Cuccaro workspace) → split into
  carry-in, top carry, target-bit (odd offset), read-bit (even offset). -/
theorem sqir_modmult_step_state_eq_qstart
    (bits q_start N a j flagPos m acc dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc)
      = sqir_mult_input_F_qstart bits q_start m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc) := by
  funext q
  set acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc with hacc'_def
  have hacc'_lt_N : acc' < N := by
    rw [hacc'_def]
    by_cases h : m.testBit j
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact hacc
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  by_cases hq_above : q ≥ q_start + 2 * bits + 1 + bits
  · -- Above layout.
    rw [sqir_modmult_step_above_layout_false_qstart bits q_start N a j flagPos m acc q
          hbits hj hq_above h_flag_lt_qstart]
    unfold sqir_mult_input_F_qstart
    rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1)]
    rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1 + bits)]
  · push_neg at hq_above
    by_cases hq_in_mult : q ≥ q_start + 2 * bits + 1
    · -- Multiplier register.
      set k := q - (q_start + 2 * bits + 1) with hk_def
      have hk_lt : k < bits := by omega
      have hq_eq : q = sqir_mult_control_idx_qstart bits q_start k := by
        unfold sqir_mult_control_idx_qstart; omega
      rw [hq_eq]
      rw [sqir_modmult_step_preserves_all_control_bits_qstart bits q_start N a m acc j k flagPos
            hbits hN_pos hN hN2 hacc hj hk_lt h_flag_lt_qstart dim h_workspace h_dim_covers_mult]
      exact (sqir_mult_input_control_bit_qstart bits q_start m acc' k hk_lt).symm
    · push_neg at hq_in_mult
      -- Workspace branch: q < q_start + 2 * bits + 1.
      by_cases hq_below : q < q_start
      · -- Below the Cuccaro workspace.
        by_cases hq_flag : q = flagPos
        · -- q = flagPos: use workspace_qstart flag conjunct.
          rw [hq_flag]
          have ⟨_, _, h_fl, _⟩ :=
            sqir_modmult_step_workspace_qstart bits q_start N a j m acc dim flagPos
              hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart h_workspace h_dim_covers_mult
          rw [h_fl]
          -- RHS: sqir_mult_input_F_qstart at flagPos = false (workspace branch, q < q_start).
          unfold sqir_mult_input_F_qstart
          rw [if_pos (by omega : flagPos < q_start + 2 * bits + 1)]
          unfold cuccaro_input_F
          rw [if_pos h_flag_lt_qstart]
        · -- q ≠ flagPos and q < q_start: use untouched_pos.
          have h_q_out : q < q_start ∨ q_start + 2 * bits + 1 ≤ q := Or.inl hq_below
          have h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx_qstart bits q_start j := by
            unfold sqir_mult_control_idx_qstart; omega
          have h_input_false : sqir_mult_input_F_qstart bits q_start m acc q = false := by
            unfold sqir_mult_input_F_qstart
            rw [if_pos (by omega : q < q_start + 2 * bits + 1)]
            unfold cuccaro_input_F
            rw [if_pos hq_below]
          rw [sqir_modmult_step_at_untouched_pos_qstart bits q_start N a j flagPos m acc q
                hj h_input_false h_q_out hq_flag h_q_ne_ctrl_j]
          -- RHS: sqir_mult_input_F_qstart at q (with acc') = false.
          unfold sqir_mult_input_F_qstart
          rw [if_pos (by omega : q < q_start + 2 * bits + 1)]
          unfold cuccaro_input_F
          rw [if_pos hq_below]
      · -- q ≥ q_start, q < q_start + 2 * bits + 1.  Cuccaro workspace.
        push_neg at hq_below
        by_cases hq_qs : q = q_start
        · -- carry-in.
          rw [hq_qs]
          rw [sqir_modmult_step_carry_in_restored_qstart bits q_start N a j flagPos m acc
                hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart]
          unfold sqir_mult_input_F_qstart
          rw [if_pos (by omega : q_start < q_start + 2 * bits + 1)]
          exact (cuccaro_input_F_at_c_in q_start false 0 acc').symm
        · by_cases hq_top : q = q_start + 2 * bits
          · -- top carry.
            rw [hq_top]
            have ⟨_, h_tc, _, _⟩ :=
              sqir_modmult_step_workspace_qstart bits q_start N a j m acc dim flagPos
                hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart h_workspace h_dim_covers_mult
            rw [h_tc]
            have h_eq : (q_start + 2 * bits : Nat) = q_start + 2 * (bits - 1) + 2 := by omega
            unfold sqir_mult_input_F_qstart
            rw [if_pos (by omega : (q_start + 2 * bits : Nat) < q_start + 2 * bits + 1)]
            rw [h_eq, cuccaro_input_F_at_a q_start (bits - 1) false 0 acc']
            exact (Nat.zero_testBit _).symm
          · -- q ∈ (q_start, q_start + 2*bits).  Parity dispatch on (q - q_start).
            by_cases h_q_odd : (q - q_start) % 2 = 1
            · -- Odd offset: q = q_start + 2*i + 1 with i = (q - q_start - 1) / 2.
              have hi_lt : (q - q_start - 1) / 2 < bits := by omega
              have hq_eq : q = q_start + 2 * ((q - q_start - 1) / 2) + 1 := by omega
              rw [hq_eq]
              rw [sqir_modmult_step_target_bit_qstart bits q_start N a j flagPos m acc
                    ((q - q_start - 1) / 2) hbits hN_pos hN hN2 hj hacc hi_lt
                    h_flag_lt_qstart dim h_workspace h_dim_covers_mult]
              unfold sqir_mult_input_F_qstart
              rw [if_pos (by omega : q_start + 2 * ((q - q_start - 1) / 2) + 1
                                      < q_start + 2 * bits + 1)]
              exact (cuccaro_input_F_at_b q_start ((q - q_start - 1) / 2) false 0 acc').symm
            · -- Even offset: q = q_start + 2*i + 2 with i = (q - q_start - 2) / 2.
              have h_q_even : (q - q_start) % 2 = 0 := by omega
              have hi_lt : (q - q_start - 2) / 2 < bits := by omega
              have hq_eq : q = q_start + 2 * ((q - q_start - 2) / 2) + 2 := by omega
              rw [hq_eq]
              rw [sqir_modmult_step_read_bit_qstart bits q_start N a j flagPos m acc
                    ((q - q_start - 2) / 2) hbits hN_pos hN hN2 hj hacc hi_lt
                    h_flag_lt_qstart dim h_workspace h_dim_covers_mult]
              unfold sqir_mult_input_F_qstart
              rw [if_pos (by omega : q_start + 2 * ((q - q_start - 2) / 2) + 2
                                      < q_start + 2 * bits + 1)]
              rw [cuccaro_input_F_at_a q_start ((q - q_start - 2) / 2) false 0 acc']
              exact (Nat.zero_testBit _).symm

/-! ## Tick 76 — Deliverables E/F: Prefix invariant + target decode. -/

/-- **Deliverable E — Prefix state equality.**

By induction on `k`, the prefix gate's output on `sqir_mult_input_F bits m 0`
equals `sqir_mult_input_F bits m (acc_spec ... k)`.  Uses
`sqir_modmult_step_state_eq` at each step + the accumulator recurrence. -/
theorem sqir_modmult_prefix_state_eq
    (bits N a m k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hk : k ≤ bits) :
    Gate.applyNat (sqir_modmult_prefix_gate bits N a k) (sqir_mult_input_F bits m 0)
      = sqir_mult_input_F bits m (sqir_modmult_acc_spec N a m k) := by
  induction k with
  | zero =>
    rw [sqir_modmult_prefix_gate, Gate.applyNat_I, sqir_modmult_acc_spec_zero]
  | succ n ih =>
    have hn_le : n ≤ bits := by omega
    have hn_lt : n < bits := by omega
    rw [sqir_modmult_prefix_gate_succ_eq, Gate.applyNat_seq]
    rw [ih hn_le]
    -- Now: applyNat (step n) (sqir_mult_input_F bits m (acc_spec n))
    --    = sqir_mult_input_F bits m (acc_spec (n+1))
    have hacc_lt_N : sqir_modmult_acc_spec N a m n < N :=
      sqir_modmult_acc_spec_lt N a m n hN_pos
    rw [sqir_modmult_step_state_eq bits N a n m (sqir_modmult_acc_spec N a m n)
          hbits hN_pos hN hN2 hn_lt hacc_lt_N]
    -- Both sides are def-eq via the `acc_spec` recurrence.
    rfl

/-- **Deliverable F — Prefix target decode (corollary of E).**

The decoded target after applying the prefix gate equals the
accumulator spec at `k`. -/
theorem sqir_modmult_prefix_target_decode
    (bits N a m k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hk : k ≤ bits) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_prefix_gate bits N a k) (sqir_mult_input_F bits m 0))
      = sqir_modmult_acc_spec N a m k := by
  rw [sqir_modmult_prefix_state_eq bits N a m k hbits hN_pos hN hN2 hk]
  have h_lt : sqir_modmult_acc_spec N a m k < 2 ^ bits :=
    Nat.lt_of_lt_of_le (sqir_modmult_acc_spec_lt N a m k hN_pos) hN
  exact sqir_mult_input_target_decode bits m (sqir_modmult_acc_spec N a m k) h_lt

/-! ## Tick 76 — Deliverable G: Full modular multiplier target theorem. -/

/-- **Deliverable G — Full modular multiplier target theorem.**

After applying `sqir_modmult_const_gate bits N a` to
`sqir_mult_input_F bits m 0`, the target register decodes to `(a*m) % N`. -/
theorem sqir_modmult_const_gate_target_decode
    (bits N a m : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hm : m < 2^bits) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0))
      = (a * m) % N := by
  unfold sqir_modmult_const_gate
  rw [sqir_modmult_prefix_target_decode bits N a m bits hbits hN_pos hN hN2 (le_refl _)]
  exact sqir_modmult_acc_spec_eq_mul_mod bits N a m hN_pos hm

/-! ## R7d^xxix-L-3.15e.5 — q_start-parametric multi-step
       constant-multiplier target decode (headline).

Final sub-tick of L-3.15e.  Composes:
- a one-line q_start port of `sqir_mult_input_target_decode` (line
  115) to read the initial accumulator from the encoded input state;
- a prefix state-equality (`_prefix_state_eq_qstart`) by induction on
  `k`, consuming the L-3.15e.4 `_step_state_eq_qstart` + the existing
  q_start-INDEPENDENT `sqir_modmult_acc_spec` recurrence;
- a prefix target-decode corollary (`_prefix_target_decode_qstart`);
- the headline `_const_gate_target_decode_qstart`, closed via the
  pre-existing q_start-independent `_acc_spec_eq_mul_mod`. -/

/-- q_start-parametric: decoded target of the initial input state
equals the accumulator value (assuming `acc < 2^bits`).  Port of
`sqir_mult_input_target_decode` (line 115). -/
theorem sqir_mult_input_target_decode_qstart
    (bits q_start m acc : Nat) (hacc : acc < 2 ^ bits) :
    cuccaro_target_val bits q_start (sqir_mult_input_F_qstart bits q_start m acc) = acc := by
  have h_eq : cuccaro_target_val bits q_start (sqir_mult_input_F_qstart bits q_start m acc)
                = acc % 2 ^ bits := by
    apply cuccaro_target_val_eq_sum_when_bits_match
    intro i hi
    unfold sqir_mult_input_F_qstart
    have h1 : q_start + 2 * i + 1 < q_start + 2 * bits + 1 := by omega
    rw [if_pos h1]
    exact cuccaro_input_F_at_b q_start i false 0 acc
  rw [h_eq]
  exact Nat.mod_eq_of_lt hacc

/-- q_start-parametric prefix state equality.  Port of
`sqir_modmult_prefix_state_eq` (line 2416). -/
theorem sqir_modmult_prefix_state_eq_qstart
    (bits q_start N a m k flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hk : k ≤ bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_prefix_gate_qstart bits q_start N a flagPos k)
        (sqir_mult_input_F_qstart bits q_start m 0)
      = sqir_mult_input_F_qstart bits q_start m (sqir_modmult_acc_spec N a m k) := by
  induction k with
  | zero =>
    rw [sqir_modmult_prefix_gate_qstart, Gate.applyNat_I, sqir_modmult_acc_spec_zero]
  | succ n ih =>
    have hn_le : n ≤ bits := by omega
    have hn_lt : n < bits := by omega
    rw [sqir_modmult_prefix_gate_qstart_succ_eq, Gate.applyNat_seq]
    rw [ih hn_le]
    have hacc_lt_N : sqir_modmult_acc_spec N a m n < N :=
      sqir_modmult_acc_spec_lt N a m n hN_pos
    rw [sqir_modmult_step_state_eq_qstart bits q_start N a n flagPos m
          (sqir_modmult_acc_spec N a m n) dim
          hbits hN_pos hN hN2 hn_lt hacc_lt_N h_flag_lt_qstart h_workspace h_dim_covers_mult]
    rfl

/-- q_start-parametric prefix target decode (corollary of prefix
state equality).  Port of `sqir_modmult_prefix_target_decode`
(line 2443). -/
theorem sqir_modmult_prefix_target_decode_qstart
    (bits q_start N a m k flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hk : k ≤ bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_modmult_prefix_gate_qstart bits q_start N a flagPos k)
          (sqir_mult_input_F_qstart bits q_start m 0))
      = sqir_modmult_acc_spec N a m k := by
  rw [sqir_modmult_prefix_state_eq_qstart bits q_start N a m k flagPos dim
        hbits hN_pos hN hN2 hk h_flag_lt_qstart h_workspace h_dim_covers_mult]
  have h_lt : sqir_modmult_acc_spec N a m k < 2 ^ bits :=
    Nat.lt_of_lt_of_le (sqir_modmult_acc_spec_lt N a m k hN_pos) hN
  exact sqir_mult_input_target_decode_qstart bits q_start m
    (sqir_modmult_acc_spec N a m k) h_lt

/-- **R7d^xxix-L-3.15e.5 HEADLINE: q_start-parametric full modular
multiplier target decode.**

After applying `sqir_modmult_const_gate_qstart bits q_start N a
flagPos` to `sqir_mult_input_F_qstart bits q_start m 0`, the target
register decodes to `(a * m) % N`.  Port of
`sqir_modmult_const_gate_target_decode` (line 2461). -/
theorem sqir_modmult_const_gate_target_decode_qstart
    (bits q_start N a m flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hm : m < 2^bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
          (sqir_mult_input_F_qstart bits q_start m 0))
      = (a * m) % N := by
  unfold sqir_modmult_const_gate_qstart
  rw [sqir_modmult_prefix_target_decode_qstart bits q_start N a m bits flagPos dim
        hbits hN_pos hN hN2 (le_refl _) h_flag_lt_qstart h_workspace h_dim_covers_mult]
  exact sqir_modmult_acc_spec_eq_mul_mod bits N a m hN_pos hm

end FormalRV.BQAlgo
