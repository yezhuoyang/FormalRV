import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultEncoding
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSpec
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultQStart
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultFamily
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSizing
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultBitPositioning
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultPrefixInvariantStateEq

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
/-! ## R7d^xxix-L-3.15f — q_start-parametric constant-multiplier
       workspace bundle.

After applying the q_start constant multiplier `sqir_modmult_const_gate_qstart`
to the initial input `sqir_mult_input_F_qstart bits q_start m 0`, the
non-target workspace positions are clean and the multiplier control
bits are preserved.  Mirrors the workspace conjuncts of the hard-coded
`sqir_modmult_const_gate_clean` (line 2629).

Strategy: instead of porting an explicit prefix-workspace induction
(the hard-coded version doesn't have one), reuse the just-landed
`sqir_modmult_prefix_state_eq_qstart` (L-3.15e.5) to reshape the
post-gate state into `sqir_mult_input_F_qstart bits q_start m
((a * m) % N)`, then read off each conjunct from the input-state
shape via small q_start ports of the existing input-state facts. -/

/-- q_start-parametric: `sqir_mult_input_F_qstart` at any position
strictly below `q_start` is `false`.  Generalises the hard-coded
`sqir_mult_input_flag_0_false` / `_flag_1_false` to any
flagPos < q_start. -/
theorem sqir_mult_input_at_below_qstart_eq_false_qstart
    (bits q_start m acc q : Nat) (hq : q < q_start) :
    sqir_mult_input_F_qstart bits q_start m acc q = false := by
  unfold sqir_mult_input_F_qstart
  rw [if_pos (by omega : q < q_start + 2 * bits + 1)]
  unfold cuccaro_input_F
  rw [if_pos hq]

/-- q_start-parametric: the read register of `sqir_mult_input_F_qstart`
is 0.  Port of `sqir_mult_input_read_decode` (line 129). -/
theorem sqir_mult_input_read_decode_qstart
    (bits q_start m acc : Nat) :
    cuccaro_read_val bits q_start (sqir_mult_input_F_qstart bits q_start m acc) = 0 := by
  have h_eq : cuccaro_read_val bits q_start (sqir_mult_input_F_qstart bits q_start m acc)
              = 0 % 2 ^ bits := by
    apply cuccaro_read_val_eq_sum_when_bits_match
    intro i hi
    unfold sqir_mult_input_F_qstart
    have h1 : q_start + 2 * i + 2 < q_start + 2 * bits + 1 := by omega
    rw [if_pos h1]
    rw [cuccaro_input_F_at_a q_start i false 0 acc]
  rw [h_eq]; simp

/-- q_start-parametric: the top-carry position `q_start + 2 * bits`
of `sqir_mult_input_F_qstart` is `false`.  Port of
`sqir_mult_input_top_carry_false` (line 162). -/
theorem sqir_mult_input_top_carry_false_qstart
    (bits q_start m acc : Nat) (hbits : 1 ≤ bits) :
    sqir_mult_input_F_qstart bits q_start m acc (q_start + 2 * bits) = false := by
  unfold sqir_mult_input_F_qstart
  rw [if_pos (by omega : (q_start + 2 * bits : Nat) < q_start + 2 * bits + 1)]
  have h_eq : (q_start + 2 * bits : Nat) = q_start + 2 * (bits - 1) + 2 := by omega
  rw [h_eq, cuccaro_input_F_at_a q_start (bits - 1) false 0 acc]
  exact Nat.zero_testBit _

/-- **R7d^xxix-L-3.15f HEADLINE: q_start-parametric constant-multiplier
workspace bundle.**

For the full multiplier `sqir_modmult_const_gate_qstart bits q_start N a
flagPos` applied to `sqir_mult_input_F_qstart bits q_start m 0`:
1. the read register decodes to 0;
2. the top carry position `q_start + 2 * bits` is `false`;
3. the dirty-flag position `flagPos` is `false`;
4. every multiplier control bit `k < bits` is preserved as `m.testBit k`.

Proof routes through `sqir_modmult_prefix_state_eq_qstart` (L-3.15e.5)
at `k = bits` + `sqir_modmult_acc_spec_eq_mul_mod` (q_start-independent)
to reshape the post-gate state, then reads each conjunct off the input
state shape.  Port of the workspace conjuncts of
`sqir_modmult_const_gate_clean` (line 2629). -/
theorem sqir_modmult_const_gate_workspace_qstart
    (bits q_start N a m flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hm : m < 2^bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_read_val bits q_start
          (Gate.applyNat (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
            (sqir_mult_input_F_qstart bits q_start m 0))
        = 0
    ∧ Gate.applyNat (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
          (sqir_mult_input_F_qstart bits q_start m 0) (q_start + 2 * bits)
        = false
    ∧ Gate.applyNat (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
          (sqir_mult_input_F_qstart bits q_start m 0) flagPos
        = false
    ∧ ∀ k, k < bits →
        Gate.applyNat (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
          (sqir_mult_input_F_qstart bits q_start m 0)
          (sqir_mult_control_idx_qstart bits q_start k) = m.testBit k := by
  unfold sqir_modmult_const_gate_qstart
  rw [sqir_modmult_prefix_state_eq_qstart bits q_start N a m bits flagPos dim
        hbits hN_pos hN hN2 (le_refl _) h_flag_lt_qstart h_workspace h_dim_covers_mult]
  rw [sqir_modmult_acc_spec_eq_mul_mod bits N a m hN_pos hm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sqir_mult_input_read_decode_qstart bits q_start m ((a * m) % N)
  · exact sqir_mult_input_top_carry_false_qstart bits q_start m ((a * m) % N) hbits
  · exact sqir_mult_input_at_below_qstart_eq_false_qstart bits q_start m
      ((a * m) % N) flagPos h_flag_lt_qstart
  · intro k hk
    exact sqir_mult_input_control_bit_qstart bits q_start m ((a * m) % N) k hk

/-- **Deliverable G corollary — Full multiplier state equality.**

After the full multiplier, the state is `sqir_mult_input_F bits m ((a*m)%N)`. -/
theorem sqir_modmult_const_gate_state_eq
    (bits N a m : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hm : m < 2^bits) :
    Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0)
      = sqir_mult_input_F bits m ((a * m) % N) := by
  unfold sqir_modmult_const_gate
  rw [sqir_modmult_prefix_state_eq bits N a m bits hbits hN_pos hN hN2 (le_refl _)]
  rw [sqir_modmult_acc_spec_eq_mul_mod bits N a m hN_pos hm]

/-! ## Tick 76 — Deliverable H: Clean multiplier bundle. -/

/-- **Step gate is WellTyped at `sqir_modmult_rev_anc bits`.** -/
theorem sqir_modmult_step_gate_wellTyped
    (bits N a j : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (hj : j < bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits) (sqir_modmult_step_gate bits N a j) := by
  unfold sqir_modmult_step_gate
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  -- For acc = 0 (any value in [0, N)), use the WellTyped conjunct.
  have ⟨h_wt, _, _, _, _, _⟩ :=
    sqir_style_controlledModAddConst_gate_clean bits N ((a * 2^j) % N) 0
      (sqir_mult_control_idx bits j) false hbits hN_pos hN hN2 hc_pos hN_pos
      (sqir_mult_control_idx_outside_modadd_workspace_form bits j)
      (sqir_mult_control_idx_ne_flag bits j)
      (sqir_mult_control_idx_lt_sqir_dim bits j hj)
  exact h_wt

/-- **Prefix gate is WellTyped at `sqir_modmult_rev_anc bits`.** -/
theorem sqir_modmult_prefix_gate_wellTyped
    (bits N a k : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (hk : k ≤ bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits) (sqir_modmult_prefix_gate bits N a k) := by
  induction k with
  | zero =>
    rw [sqir_modmult_prefix_gate]
    show 0 < sqir_modmult_rev_anc bits
    unfold sqir_modmult_rev_anc; omega
  | succ n ih =>
    rw [sqir_modmult_prefix_gate_succ_eq]
    refine ⟨?_, ?_⟩
    · exact ih (by omega)
    · exact sqir_modmult_step_gate_wellTyped bits N a n hbits hN_pos hN hN2 (by omega)

/-- **Deliverable H — Clean modular-multiplier bundle.**

For the full multiplier gate `sqir_modmult_const_gate bits N a`:
- WellTyped at `sqir_modmult_rev_anc bits`.
- Target decoded to `(a * m) % N`.
- Read = 0.
- Flag bits 0, 1 = false.
- Top carry (position `2 + 2*bits`) = false.
- All multiplier control bits preserved as `m.testBit k`. -/
theorem sqir_modmult_const_gate_clean
    (bits N a m : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hm : m < 2^bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits) (sqir_modmult_const_gate bits N a)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0))
        = (a * m) % N
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0))
        = 0
    ∧ Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0) 0
        = false
    ∧ Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0) 1
        = false
    ∧ Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0)
          (2 + 2 * bits) = false
    ∧ ∀ k, k < bits →
        Gate.applyNat (sqir_modmult_const_gate bits N a)
          (sqir_mult_input_F bits m 0) (sqir_mult_control_idx bits k) = m.testBit k := by
  have h_state := sqir_modmult_const_gate_state_eq bits N a m hbits hN_pos hN hN2 hm
  have ham_lt : (a * m) % N < 2 ^ bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sqir_modmult_prefix_gate_wellTyped bits N a bits hbits hN_pos hN hN2 (le_refl _)
  · rw [h_state]; exact sqir_mult_input_target_decode bits m ((a * m) % N) ham_lt
  · rw [h_state]; exact sqir_mult_input_read_decode bits m ((a * m) % N)
  · rw [h_state]; exact sqir_mult_input_flag_0_false bits m ((a * m) % N)
  · rw [h_state]; exact sqir_mult_input_flag_1_false bits m ((a * m) % N)
  · rw [h_state]; exact sqir_mult_input_top_carry_false bits m ((a * m) % N) hbits
  · intro k hk
    rw [h_state]
    exact sqir_mult_input_control_bit bits m ((a * m) % N) k hk

/-! ## Tick 76 — Deliverable I: BasicSetting specialization. -/

/-- **Deliverable I — BasicSetting specialization of the full
multiplier clean bundle.**

For BasicSetting parameters (which give `N ≤ 2^(n+1)` and `2*N ≤ 2^(n+1)`),
the clean bundle holds at `bits = n + 1`. -/
theorem sqir_modmult_const_gate_clean_from_BasicSetting
    (a r N m n x_mult : Nat)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (hm : x_mult < 2^(n + 1)) :
    Gate.WellTyped (sqir_modmult_rev_anc (n + 1))
        (sqir_modmult_const_gate (n + 1) N a)
    ∧ cuccaro_target_val (n + 1) 2
          (Gate.applyNat (sqir_modmult_const_gate (n + 1) N a)
            (sqir_mult_input_F (n + 1) x_mult 0)) = (a * x_mult) % N
    ∧ cuccaro_read_val (n + 1) 2
          (Gate.applyNat (sqir_modmult_const_gate (n + 1) N a)
            (sqir_mult_input_F (n + 1) x_mult 0)) = 0
    ∧ Gate.applyNat (sqir_modmult_const_gate (n + 1) N a)
          (sqir_mult_input_F (n + 1) x_mult 0) 0 = false
    ∧ Gate.applyNat (sqir_modmult_const_gate (n + 1) N a)
          (sqir_mult_input_F (n + 1) x_mult 0) 1 = false
    ∧ Gate.applyNat (sqir_modmult_const_gate (n + 1) N a)
          (sqir_mult_input_F (n + 1) x_mult 0) (2 + 2 * (n + 1)) = false
    ∧ ∀ k, k < (n + 1) →
        Gate.applyNat (sqir_modmult_const_gate (n + 1) N a)
          (sqir_mult_input_F (n + 1) x_mult 0)
          (sqir_mult_control_idx (n + 1) k) = x_mult.testBit k := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have hN_le : N ≤ 2 ^ (n + 1) := by omega
  exact sqir_modmult_const_gate_clean (n + 1) N a x_mult
    (by omega : 1 ≤ n + 1) hN_pos hN_le hN2 hm

theorem sqir_modmult_acc_spec_from_zero (N a m acc : Nat) :
    sqir_modmult_acc_spec_from N a m acc 0 = acc := rfl

theorem sqir_modmult_acc_spec_from_succ_true
    (N a m acc k : Nat) (h : m.testBit k = true) :
    sqir_modmult_acc_spec_from N a m acc (k + 1)
      = (sqir_modmult_acc_spec_from N a m acc k + (a * 2 ^ k) % N) % N := by
  show (if m.testBit k then _ else _) = _; simp [h]

theorem sqir_modmult_acc_spec_from_succ_false
    (N a m acc k : Nat) (h : m.testBit k = false) :
    sqir_modmult_acc_spec_from N a m acc (k + 1)
      = sqir_modmult_acc_spec_from N a m acc k := by
  show (if m.testBit k then _ else _) = _; simp [h]

/-- For `0 < N`, the accumulator-from-start stays in `[0, N)` if `acc < N`. -/
theorem sqir_modmult_acc_spec_from_lt
    (N a m acc k : Nat) (hN_pos : 0 < N) (hacc : acc < N) :
    sqir_modmult_acc_spec_from N a m acc k < N := by
  induction k with
  | zero => exact hacc
  | succ n ih =>
    unfold sqir_modmult_acc_spec_from
    by_cases h : m.testBit n
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact ih

/-- **Closed form for `acc_spec_from`**: equals `(acc + a * (m % 2^k)) % N`
for `acc < N`. -/
theorem sqir_modmult_acc_spec_from_eq_mod_pow
    (N a m acc k : Nat) (hN_pos : 0 < N) (hacc : acc < N) :
    sqir_modmult_acc_spec_from N a m acc k = (acc + a * (m % 2^k)) % N := by
  induction k with
  | zero =>
    rw [sqir_modmult_acc_spec_from_zero, pow_zero, Nat.mod_one,
        Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hacc]
  | succ n ih =>
    rw [nat_mod_two_pow_succ_eq m n]
    by_cases h_bit : m.testBit n = true
    · rw [sqir_modmult_acc_spec_from_succ_true N a m acc n h_bit]
      simp only [h_bit, if_true]
      rw [ih, Nat.mul_add, ← Nat.add_mod, Nat.add_assoc]
    · have h_bit_false : m.testBit n = false := by
        cases hh : m.testBit n
        · rfl
        · exact absurd hh h_bit
      rw [sqir_modmult_acc_spec_from_succ_false N a m acc n h_bit_false]
      rw [h_bit_false]; simp only [Bool.false_eq_true, if_false, Nat.add_zero]
      exact ih

/-- For `m < 2^bits` and `acc < N`, the final accumulator equals
`(acc + a*m) % N`. -/
theorem sqir_modmult_acc_spec_from_eq_add_mul_mod
    (bits N a m acc : Nat) (hN_pos : 0 < N) (hacc : acc < N) (hm : m < 2^bits) :
    sqir_modmult_acc_spec_from N a m acc bits = (acc + a * m) % N := by
  rw [sqir_modmult_acc_spec_from_eq_mod_pow N a m acc bits hN_pos hacc]
  rw [Nat.mod_eq_of_lt hm]

/-- **Generalized prefix state equality** for arbitrary starting accumulator. -/
theorem sqir_modmult_prefix_state_eq_from
    (bits N a m acc k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hk : k ≤ bits) :
    Gate.applyNat (sqir_modmult_prefix_gate bits N a k) (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m (sqir_modmult_acc_spec_from N a m acc k) := by
  induction k with
  | zero =>
    rw [sqir_modmult_prefix_gate, Gate.applyNat_I, sqir_modmult_acc_spec_from_zero]
  | succ n ih =>
    have hn_le : n ≤ bits := by omega
    have hn_lt : n < bits := by omega
    rw [sqir_modmult_prefix_gate_succ_eq, Gate.applyNat_seq]
    rw [ih hn_le]
    have hacc_lt_N : sqir_modmult_acc_spec_from N a m acc n < N :=
      sqir_modmult_acc_spec_from_lt N a m acc n hN_pos hacc
    rw [sqir_modmult_step_state_eq bits N a n m (sqir_modmult_acc_spec_from N a m acc n)
          hbits hN_pos hN hN2 hn_lt hacc_lt_N]
    rfl

/-- **Generalized full multiplier state equality** for arbitrary
starting accumulator. -/
theorem sqir_modmult_const_gate_state_eq_from
    (bits N a m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hm : m < 2^bits) :
    Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m ((acc + a * m) % N) := by
  unfold sqir_modmult_const_gate
  rw [sqir_modmult_prefix_state_eq_from bits N a m acc bits hbits hN_pos hN hN2 hacc (le_refl _)]
  rw [sqir_modmult_acc_spec_from_eq_add_mul_mod bits N a m acc hN_pos hacc hm]

/-! ## R7d^xxix-L-3.15g — q_start-parametric in-place modular
       multiplier infrastructure (fallback Option 2).

The full in-place state-equality
`sqir_modmult_inplace_candidate_state_eq_qstart` requires porting
~7 swap-position helpers plus a ~100-line
`sqir_swap_acc_mult_apply_qstart`.  Total ~300 lines is too large
for a single tick.

This sub-tick lands the *prerequisite layer*:
- forward-compute generalised state-equality lifted to arbitrary
  starting accumulator (`sqir_modmult_const_gate_state_eq_from_qstart`
  and its prefix ancestor);
- q_start swap-register definitions
  (`sqir_target_idx_qstart`, `sqir_swap_acc_mult_aux_qstart`,
  `sqir_swap_acc_mult_qstart`) plus the trivial index-distinctness
  and recursion-unfold lemmas;
- the q_start in-place candidate definition
  (`sqir_modmult_inplace_candidate_qstart`).

The `acc_spec_from` arithmetic chain
(`sqir_modmult_acc_spec_from`, `_from_lt`, `_from_eq_add_mul_mod`)
is q_start-INDEPENDENT and reused as-is.

Deferred to L-3.15g.2:
- 5 swap-position case helpers
  (`_at_mult_out_range`, `_at_target_out_range`, `_at_target_in_range`,
  `_at_mult_in_range`, `_at_other`) ported to qstart;
- `sqir_swap_acc_mult_apply_qstart` (~100-line `funext q` case split);
- the headline `sqir_modmult_inplace_candidate_state_eq_qstart`. -/

/-- q_start-parametric: prefix state-eq generalised to an arbitrary
starting accumulator.  Port of `sqir_modmult_prefix_state_eq_from`.
Uses the q_start-INDEPENDENT `sqir_modmult_acc_spec_from` chain
plus the L-3.15e.4 `sqir_modmult_step_state_eq_qstart`. -/
theorem sqir_modmult_prefix_state_eq_from_qstart
    (bits q_start N a m acc k flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hk : k ≤ bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_prefix_gate_qstart bits q_start N a flagPos k)
        (sqir_mult_input_F_qstart bits q_start m acc)
      = sqir_mult_input_F_qstart bits q_start m
          (sqir_modmult_acc_spec_from N a m acc k) := by
  induction k with
  | zero =>
    rw [sqir_modmult_prefix_gate_qstart, Gate.applyNat_I,
        sqir_modmult_acc_spec_from_zero]
  | succ n ih =>
    have hn_le : n ≤ bits := by omega
    have hn_lt : n < bits := by omega
    rw [sqir_modmult_prefix_gate_qstart_succ_eq, Gate.applyNat_seq]
    rw [ih hn_le]
    have hacc_lt_N : sqir_modmult_acc_spec_from N a m acc n < N :=
      sqir_modmult_acc_spec_from_lt N a m acc n hN_pos hacc
    rw [sqir_modmult_step_state_eq_qstart bits q_start N a n flagPos m
          (sqir_modmult_acc_spec_from N a m acc n) dim
          hbits hN_pos hN hN2 hn_lt hacc_lt_N h_flag_lt_qstart h_workspace
          h_dim_covers_mult]
    rfl

/-- q_start-parametric: full multiplier state-eq generalised to an
arbitrary starting accumulator.  Port of
`sqir_modmult_const_gate_state_eq_from`. -/
theorem sqir_modmult_const_gate_state_eq_from_qstart
    (bits q_start N a m acc flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hm : m < 2^bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc)
      = sqir_mult_input_F_qstart bits q_start m ((acc + a * m) % N) := by
  unfold sqir_modmult_const_gate_qstart
  rw [sqir_modmult_prefix_state_eq_from_qstart bits q_start N a m acc bits flagPos dim
        hbits hN_pos hN hN2 hacc (le_refl _) h_flag_lt_qstart h_workspace
        h_dim_covers_mult]
  rw [sqir_modmult_acc_spec_from_eq_add_mul_mod bits N a m acc hN_pos hacc hm]

/-- Target index disjoint from multiplier control index. -/
theorem sqir_target_idx_ne_mult_control_idx_qstart
    (bits q_start i j : Nat) (hi : i < bits) :
    sqir_target_idx_qstart q_start i
      ≠ sqir_mult_control_idx_qstart bits q_start j := by
  unfold sqir_target_idx_qstart sqir_mult_control_idx_qstart
  omega

/-- Unfold lemma for `sqir_swap_acc_mult_aux_qstart`. -/
theorem sqir_swap_acc_mult_aux_qstart_succ_eq (bits q_start k : Nat) :
    sqir_swap_acc_mult_aux_qstart bits q_start (k + 1)
      = Gate.seq (sqir_swap_acc_mult_aux_qstart bits q_start k)
          (qubit_swap (sqir_target_idx_qstart q_start k)
                      (sqir_mult_control_idx_qstart bits q_start k)) := rfl

/-- Sanity helper: `sqir_target_idx_qstart` value. -/
theorem sqir_target_idx_qstart_value (q_start i : Nat) :
    sqir_target_idx_qstart q_start i = q_start + 2 * i + 1 := rfl

/-! ### Per-position behavior of `sqir_swap_acc_mult_aux_qstart` (L-3.15g.2). -/

/-- q_start port of `sqir_swap_acc_mult_aux_at_mult_out_range` (line 3097).
At a multiplier bit `i ≥ k`, swap output = input. -/
theorem sqir_swap_acc_mult_at_mult_out_range_qstart
    (bits q_start k i : Nat) (hk : k ≤ bits) (hi_ge : k ≤ i) (hi_bits : i < bits)
    (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux_qstart bits q_start k) f
        (sqir_mult_control_idx_qstart bits q_start i)
      = f (sqir_mult_control_idx_qstart bits q_start i) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [sqir_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    have h_i_ne_n : i ≠ n := by omega
    have h_ne_mult_n :
        sqir_mult_control_idx_qstart bits q_start i
          ≠ sqir_mult_control_idx_qstart bits q_start n := by
      intro heq
      exact h_i_ne_n (sqir_mult_control_idx_injective_qstart bits q_start i n heq)
    have h_ne_target_n :
        sqir_mult_control_idx_qstart bits q_start i
          ≠ sqir_target_idx_qstart q_start n :=
      (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n i hn_lt).symm
    rw [update_neq _ _ _ _ h_ne_mult_n]
    rw [update_neq _ _ _ _ h_ne_target_n]
    exact ih (by omega) (by omega)

end FormalRV.BQAlgo
