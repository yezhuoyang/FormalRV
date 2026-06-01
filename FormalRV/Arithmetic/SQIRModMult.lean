/-
  FormalRV.BQAlgo.SQIRModMult — SQIR-style modular multiplier
  built by iterating the controlled modular add-constant from Phase 3.

  This file begins Phase 4 of the modarith-to-modexp plan:
  Phase 3 (controlled mod-add) → Phase 4 (modular multiplier) →
  Phase 5 (modular exponentiation) → Phase 6 (close SQIR axioms).

  Tick 73 (initial layout):
    - Layout for the multiplier control register.
    - Input encoding `sqir_mult_input_F` with sanity lemmas.
    - One-step gate `sqir_modmult_step_gate`.
    - Prefix gate skeleton `sqir_modmult_prefix_gate`.
    - Accumulator specification `sqir_modmult_acc_spec`.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Tick 73 — Multiplier control register layout.

Reuses the SQIR-faithful Cuccaro mod-add layout (q_start = 2,
flagPos = 1, top carry = 2 + 2*bits).  The multiplier control
register starts at `2 + 2*bits + 1` (immediately after the top
carry), so the `j`-th multiplier bit sits at position
`2 + 2*bits + 1 + j`. -/

/-- Multiplier bit `j` lives at this position in the layout. -/
def sqir_mult_control_idx (bits j : Nat) : Nat :=
  2 + (2 * bits + 1) + j

theorem sqir_mult_control_idx_outside_modadd_workspace
    (bits j : Nat) :
    sqir_mult_control_idx bits j < 2
      ∨ 2 + (2 * bits + 1) ≤ sqir_mult_control_idx bits j := by
  right
  unfold sqir_mult_control_idx
  omega

theorem sqir_mult_control_idx_ne_flag
    (bits j : Nat) :
    sqir_mult_control_idx bits j ≠ 1 := by
  unfold sqir_mult_control_idx
  omega

theorem sqir_mult_control_idx_ne_top_carry
    (bits j : Nat) :
    sqir_mult_control_idx bits j ≠ 2 + 2 * bits := by
  unfold sqir_mult_control_idx
  omega

theorem sqir_mult_control_idx_lt_sqir_dim
    (bits j : Nat) (hj : j < bits) :
    sqir_mult_control_idx bits j < sqir_modmult_rev_anc bits := by
  unfold sqir_mult_control_idx sqir_modmult_rev_anc
  omega

theorem sqir_mult_control_idx_outside_modadd_workspace_form
    (bits j : Nat) :
    sqir_mult_control_idx bits j < 2
      ∨ 2 + 2 * bits + 1 ≤ sqir_mult_control_idx bits j := by
  right
  unfold sqir_mult_control_idx
  omega

/-- Distinct multiplier bits map to distinct positions. -/
theorem sqir_mult_control_idx_injective
    (bits j j' : Nat) (h : sqir_mult_control_idx bits j = sqir_mult_control_idx bits j') :
    j = j' := by
  unfold sqir_mult_control_idx at h
  omega

/-! ## Tick 73 — Input encoding for the multiplier.

Combines the Cuccaro accumulator encoding (carry-in = false,
read-register = 0, target = `acc`) with multiplier bits installed
in the control register. -/

/-- Input state for the modular multiplier.

Layout:
- Positions 0 and 1 are flag bits (both false).
- Positions 2..2+2*bits-1 encode the Cuccaro state for the
  accumulator (carry-in = false, read register = 0, target = `acc`).
- Position 2 + 2*bits is the top carry (false, since accumulator
  is in `[0, 2^bits)`).
- Position 2 + 2*bits + 1 + j is the j-th multiplier bit
  (`m.testBit j`).
- Positions above the multiplier register are false. -/
def sqir_mult_input_F (bits m acc : Nat) : Nat → Bool := fun q =>
  if q < 2 + 2 * bits + 1 then
    cuccaro_input_F 2 false 0 acc q
  else if q < 2 + 2 * bits + 1 + bits then
    m.testBit (q - (2 + 2 * bits + 1))
  else false

/-- **Multiplier bit at `sqir_mult_control_idx bits j` is `m.testBit j`.** -/
theorem sqir_mult_input_control_bit
    (bits m acc j : Nat) (hj : j < bits) :
    sqir_mult_input_F bits m acc (sqir_mult_control_idx bits j) = m.testBit j := by
  unfold sqir_mult_input_F sqir_mult_control_idx
  have h1 : ¬ (2 + (2 * bits + 1) + j < 2 + 2 * bits + 1) := by omega
  rw [if_neg h1]
  have h2 : 2 + (2 * bits + 1) + j < 2 + 2 * bits + 1 + bits := by omega
  rw [if_pos h2]
  congr 1
  omega

/-- **Decoded target register equals `acc` (for `acc < 2^bits`).** -/
theorem sqir_mult_input_target_decode
    (bits m acc : Nat) (hacc : acc < 2 ^ bits) :
    cuccaro_target_val bits 2 (sqir_mult_input_F bits m acc) = acc := by
  have h_eq : cuccaro_target_val bits 2 (sqir_mult_input_F bits m acc) = acc % 2 ^ bits := by
    apply cuccaro_target_val_eq_sum_when_bits_match
    intro i hi
    unfold sqir_mult_input_F
    have h1 : 2 + 2 * i + 1 < 2 + 2 * bits + 1 := by omega
    rw [if_pos h1]
    exact cuccaro_input_F_at_b 2 i false 0 acc
  rw [h_eq]
  exact Nat.mod_eq_of_lt hacc

/-- **Decoded read register is 0.** -/
theorem sqir_mult_input_read_decode
    (bits m acc : Nat) :
    cuccaro_read_val bits 2 (sqir_mult_input_F bits m acc) = 0 := by
  have h_eq : cuccaro_read_val bits 2 (sqir_mult_input_F bits m acc) = 0 % 2 ^ bits := by
    apply cuccaro_read_val_eq_sum_when_bits_match
    intro i hi
    unfold sqir_mult_input_F
    have h1 : 2 + 2 * i + 2 < 2 + 2 * bits + 1 := by omega
    rw [if_pos h1]
    rw [cuccaro_input_F_at_a 2 i false 0 acc]
  rw [h_eq]
  simp

/-- **Flag bits are false.** -/
theorem sqir_mult_input_flag_0_false
    (bits m acc : Nat) :
    sqir_mult_input_F bits m acc 0 = false := by
  unfold sqir_mult_input_F
  rw [if_pos (by omega : (0 : Nat) < 2 + 2 * bits + 1)]
  unfold cuccaro_input_F
  rw [if_pos (by omega : (0 : Nat) < 2)]

theorem sqir_mult_input_flag_1_false
    (bits m acc : Nat) :
    sqir_mult_input_F bits m acc 1 = false := by
  unfold sqir_mult_input_F
  rw [if_pos (by omega : (1 : Nat) < 2 + 2 * bits + 1)]
  unfold cuccaro_input_F
  rw [if_pos (by omega : (1 : Nat) < 2)]

/-- **Top carry is false (when bits ≥ 1).**  The top carry position
`2 + 2*bits = 2 + 2*(bits-1) + 2` is the highest read register bit
in the Cuccaro encoding with `a = 0`. -/
theorem sqir_mult_input_top_carry_false
    (bits m acc : Nat) (hbits : 1 ≤ bits) :
    sqir_mult_input_F bits m acc (2 + 2 * bits) = false := by
  unfold sqir_mult_input_F
  rw [if_pos (by omega : (2 + 2 * bits : Nat) < 2 + 2 * bits + 1)]
  have h_eq : (2 + 2 * bits : Nat) = 2 + 2 * (bits - 1) + 2 := by omega
  rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 acc]
  exact Nat.zero_testBit _

/-! ## Tick 73 — One-step controlled mod-add gate.

For constant `a` and multiplier bit `j`, the step gate conditionally
adds `(a * 2^j) % N` to the accumulator, controlled by multiplier
bit `j`. -/

/-- **One-step modular multiplier gate (controlled add of `(a * 2^j) % N`).** -/
def sqir_modmult_step_gate (bits N a j : Nat) : Gate :=
  sqir_style_controlledModAddConst_gate bits 2 N ((a * 2 ^ j) % N)
    (sqir_mult_control_idx bits j) 1

/-! ## Tick 73 — Accumulator specification. -/

/-- Recursive specification of the accumulator after processing the
first `k` multiplier bits.  Models the classical
shift-and-accumulate loop. -/
def sqir_modmult_acc_spec (N a m : Nat) : Nat → Nat
  | 0       => 0
  | k + 1   =>
    if m.testBit k then
      (sqir_modmult_acc_spec N a m k + (a * 2 ^ k) % N) % N
    else
      sqir_modmult_acc_spec N a m k

theorem sqir_modmult_acc_spec_zero (N a m : Nat) :
    sqir_modmult_acc_spec N a m 0 = 0 := rfl

theorem sqir_modmult_acc_spec_succ_false
    (N a m k : Nat) (h : m.testBit k = false) :
    sqir_modmult_acc_spec N a m (k + 1) = sqir_modmult_acc_spec N a m k := by
  show (if m.testBit k then _ else sqir_modmult_acc_spec N a m k) = _
  simp [h]

theorem sqir_modmult_acc_spec_succ_true
    (N a m k : Nat) (h : m.testBit k = true) :
    sqir_modmult_acc_spec N a m (k + 1)
      = (sqir_modmult_acc_spec N a m k + (a * 2 ^ k) % N) % N := by
  show (if m.testBit k then (sqir_modmult_acc_spec N a m k + (a * 2 ^ k) % N) % N else _) = _
  simp [h]

/-- For `0 < N`, the accumulator after any prefix is in `[0, N)`. -/
theorem sqir_modmult_acc_spec_lt (N a m k : Nat) (hN_pos : 0 < N) :
    sqir_modmult_acc_spec N a m k < N := by
  induction k with
  | zero => exact hN_pos
  | succ n ih =>
    unfold sqir_modmult_acc_spec
    by_cases h : m.testBit n
    · rw [if_pos h]
      exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]
      exact ih

/-! ## Tick 73 — Prefix multiplier gate (skeleton). -/

/-- Multiplier prefix gate: applies `sqir_modmult_step_gate` for
`j = 0, 1, ..., k-1` in order. -/
def sqir_modmult_prefix_gate (bits N a : Nat) : Nat → Gate
  | 0       => Gate.I
  | k + 1   => seq (sqir_modmult_prefix_gate bits N a k) (sqir_modmult_step_gate bits N a k)

theorem sqir_modmult_prefix_gate_zero_eq_I
    (bits N a : Nat) :
    sqir_modmult_prefix_gate bits N a 0 = Gate.I := rfl

theorem sqir_modmult_prefix_gate_succ_eq
    (bits N a k : Nat) :
    sqir_modmult_prefix_gate bits N a (k + 1)
      = seq (sqir_modmult_prefix_gate bits N a k) (sqir_modmult_step_gate bits N a k) := rfl

/-- The full multiplier gate (process all `bits` multiplier bits). -/
def sqir_modmult_const_gate (bits N a : Nat) : Gate :=
  sqir_modmult_prefix_gate bits N a bits

/-! ## Tick 74 — Wrapper-level commute helpers. -/

/-- **Controlled compareConst commutes with update at outside position
distinct from the inner controlIdx and flagPos.** -/
theorem sqir_controlledCompareConst_commute_update_outside_fun
    (bits q_start c controlIdx flagPos updateIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hupdate_out : updateIdx < q_start ∨ q_start + 2 * bits + 1 ≤ updateIdx)
    (hupdate_ne_flag : updateIdx ≠ flagPos)
    (hupdate_ne_ctrl : updateIdx ≠ controlIdx) :
    Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
        (update f updateIdx v)
      = update (Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos) f)
              updateIdx v := by
  unfold sqir_controlledCompareConst
  simp only [Gate.applyNat_seq]
  have h_ctrl_ne_top : updateIdx ≠ q_start + 2 * bits := by
    rcases hupdate_out with hl | hr
    · omega
    · omega
  rw [sqir_prepareMaskedConstRead_commute_update_outside_workspace bits q_start (2^bits - c)
        controlIdx updateIdx v f hupdate_out hupdate_ne_ctrl]
  rw [cuccaro_maj_chain_commute_update_outside_workspace bits q_start updateIdx v _ hupdate_out]
  rw [Gate.applyNat_CX_commute_update_outside_fun (q_start + 2 * bits) flagPos updateIdx v _
        h_ctrl_ne_top hupdate_ne_flag]
  rw [cuccaro_maj_chain_inv_commute_update_outside_workspace_fun bits q_start updateIdx v _
        hupdate_out]
  rw [sqir_prepareMaskedConstRead_commute_update_outside_workspace bits q_start (2^bits - c)
        controlIdx updateIdx v _ hupdate_out hupdate_ne_ctrl]

/-- **Deliverable A — controlled modular add-constant gate commutes
with `update` at outside positions (distinct from flag and controlIdx).** -/
theorem sqir_style_controlledModAddConst_gate_commute_update_outside_fun
    (bits N c controlIdx updateIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hupdate_out : updateIdx < 2 ∨ 2 + (2 * bits + 1) ≤ updateIdx)
    (hupdate_ne_flag : updateIdx ≠ 1)
    (hupdate_ne_control : updateIdx ≠ controlIdx) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
        (update f updateIdx v)
      = update (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1) f)
              updateIdx v := by
  unfold sqir_style_controlledModAddConst_gate
  by_cases hc : c = 0
  · simp [hc, Gate.applyNat_I]
  · simp only [hc, if_false]
    unfold sqir_style_controlledModAddConst_candidate
    simp only [Gate.applyNat_seq]
    rw [sqir_conditionalAddConstGate_commute_update_outside_fun bits 2 c controlIdx updateIdx v f
          hupdate_out hupdate_ne_control]
    rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits 2 N 1 updateIdx v _
          hupdate_out hupdate_ne_flag]
    rw [sqir_conditionalSubConstGate_commute_update_outside_fun bits 2 N 1 updateIdx v _
          hupdate_out hupdate_ne_flag]
    rw [sqir_controlledCompareConst_commute_update_outside_fun bits 2 c controlIdx 1 updateIdx v _
          hupdate_out hupdate_ne_flag hupdate_ne_control]
    rw [Gate.applyNat_CX_commute_update_outside_fun controlIdx 1 updateIdx v _
          hupdate_ne_control hupdate_ne_flag]

/-! ## R7d^xxix-L-3.15a — q_start-parametric infrastructure for the
       modular-multiplier step.

q_start-parametric counterparts of the basic Pipeline-B multiplier
objects: control index, input state, step gate, and a commute helper
for the controlled mod-add gate.  This layer mirrors the hard-coded
`q_start = 2`, `flagPos = 1` versions and consumes the previously-
closed `sqir_style_controlledModAddConst_gate_clean_qstart` (L-3.14′)
through its already-q_start-parametric sub-helpers.

This sub-tick does NOT yet add the `install_mult_bits_skip_j_qstart`
chain (L-3.15b) or the target-through-install bridge + headline
target_decode (L-3.15c). -/

/-- q_start-parametric multiplier-bit position.  Generalises
`sqir_mult_control_idx bits j = 2 + (2 * bits + 1) + j` to free
`q_start`. -/
def sqir_mult_control_idx_qstart (bits q_start j : Nat) : Nat :=
  q_start + (2 * bits + 1) + j

/-- The j-th multiplier bit lies above the shifted Cuccaro workspace
`[q_start, q_start + 2 * bits + 1)`.  Port of
`sqir_mult_control_idx_outside_modadd_workspace_form` (line 63). -/
theorem sqir_mult_control_idx_outside_modadd_workspace_form_qstart
    (bits q_start j : Nat) :
    sqir_mult_control_idx_qstart bits q_start j < q_start
      ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start j := by
  right
  unfold sqir_mult_control_idx_qstart
  omega

/-- The j-th multiplier bit is distinct from any chosen `flagPos`
strictly below the shifted workspace.  Port of
`sqir_mult_control_idx_ne_flag` (line 45). -/
theorem sqir_mult_control_idx_ne_flag_qstart
    (bits q_start j flagPos : Nat) (h_flag_lt : flagPos < q_start) :
    sqir_mult_control_idx_qstart bits q_start j ≠ flagPos := by
  unfold sqir_mult_control_idx_qstart
  omega

/-- The j-th multiplier bit fits in a dimension that covers the
workspace plus the multiplier register.  Port of
`sqir_mult_control_idx_lt_sqir_dim` (line 57) generalised to a free
`dim` parameter. -/
theorem sqir_mult_control_idx_lt_dim_qstart
    (bits q_start j dim : Nat) (hj : j < bits)
    (h_dim : q_start + (2 * bits + 1) + bits ≤ dim) :
    sqir_mult_control_idx_qstart bits q_start j < dim := by
  unfold sqir_mult_control_idx_qstart
  omega

/-- Distinct multiplier bits map to distinct positions.  Port of
`sqir_mult_control_idx_injective` (line 72). -/
theorem sqir_mult_control_idx_injective_qstart
    (bits q_start j j' : Nat)
    (h : sqir_mult_control_idx_qstart bits q_start j
          = sqir_mult_control_idx_qstart bits q_start j') :
    j = j' := by
  unfold sqir_mult_control_idx_qstart at h
  omega

/-- q_start-parametric input state for the modular multiplier.

Layout (free `q_start`):
- Positions `q < q_start + 2 * bits + 1`: Cuccaro state
  (`cuccaro_input_F q_start false 0 acc`).
- Positions `q_start + 2 * bits + 1 + j` for `j < bits`: multiplier
  bit `m.testBit j`.
- Positions above the multiplier register: `false`.

Port of `sqir_mult_input_F` (line 95). -/
def sqir_mult_input_F_qstart (bits q_start m acc : Nat) : Nat → Bool := fun q =>
  if q < q_start + 2 * bits + 1 then
    cuccaro_input_F q_start false 0 acc q
  else if q < q_start + 2 * bits + 1 + bits then
    m.testBit (q - (q_start + 2 * bits + 1))
  else false

/-- The multiplier bit at `sqir_mult_control_idx_qstart bits q_start j`
is `m.testBit j`.  Port of `sqir_mult_input_control_bit` (line 103). -/
theorem sqir_mult_input_control_bit_qstart
    (bits q_start m acc j : Nat) (hj : j < bits) :
    sqir_mult_input_F_qstart bits q_start m acc
        (sqir_mult_control_idx_qstart bits q_start j) = m.testBit j := by
  unfold sqir_mult_input_F_qstart sqir_mult_control_idx_qstart
  have h1 : ¬ (q_start + (2 * bits + 1) + j < q_start + 2 * bits + 1) := by omega
  rw [if_neg h1]
  have h2 : q_start + (2 * bits + 1) + j < q_start + 2 * bits + 1 + bits := by omega
  rw [if_pos h2]
  congr 1
  omega

/-- q_start-parametric one-step modular-multiplier gate.  Conditionally
adds `(a * 2^j) % N` to the accumulator at workspace q_start = `q_start`,
controlled by the multiplier bit at
`sqir_mult_control_idx_qstart bits q_start j`, with dirty flag at
`flagPos`.  Port of `sqir_modmult_step_gate` (line 178). -/
def sqir_modmult_step_gate_qstart (bits q_start N a j flagPos : Nat) : Gate :=
  sqir_style_controlledModAddConst_gate bits q_start N ((a * 2 ^ j) % N)
    (sqir_mult_control_idx_qstart bits q_start j) flagPos

/-- q_start-parametric commute helper for the controlled mod-add gate.

Port of `sqir_style_controlledModAddConst_gate_commute_update_outside_fun`
(line 276): the gate commutes with an `update` at any position outside
its workspace and distinct from both `controlIdx` and `flagPos`.

All sub-helpers are already q_start-parametric:
- `sqir_conditionalAddConstGate_commute_update_outside_fun`
  (CuccaroSQIRDirtyFlag.lean:3157);
- `sqir_style_compareConst_candidate_commute_update_outside_fun` (:3132);
- `sqir_conditionalSubConstGate_commute_update_outside_fun` (:3174);
- `sqir_controlledCompareConst_commute_update_outside_fun` (this file:249);
- `Gate.applyNat_CX_commute_update_outside_fun` (CuccaroSQIRDirtyFlag.lean:3039). -/
theorem sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart
    (bits q_start N c controlIdx flagPos updateIdx : Nat) (v : Bool) (f : Nat → Bool)
    (hupdate_out : updateIdx < q_start ∨ q_start + 2 * bits + 1 ≤ updateIdx)
    (hupdate_ne_flag : updateIdx ≠ flagPos)
    (hupdate_ne_control : updateIdx ≠ controlIdx) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
        (update f updateIdx v)
      = update (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
                                  controlIdx flagPos) f)
              updateIdx v := by
  unfold sqir_style_controlledModAddConst_gate
  by_cases hc : c = 0
  · simp [hc, Gate.applyNat_I]
  · simp only [hc, if_false]
    unfold sqir_style_controlledModAddConst_candidate
    simp only [Gate.applyNat_seq]
    rw [sqir_conditionalAddConstGate_commute_update_outside_fun bits q_start c controlIdx
          updateIdx v f hupdate_out hupdate_ne_control]
    rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits q_start N flagPos
          updateIdx v _ hupdate_out hupdate_ne_flag]
    rw [sqir_conditionalSubConstGate_commute_update_outside_fun bits q_start N flagPos
          updateIdx v _ hupdate_out hupdate_ne_flag]
    rw [sqir_controlledCompareConst_commute_update_outside_fun bits q_start c controlIdx flagPos
          updateIdx v _ hupdate_out hupdate_ne_flag hupdate_ne_control]
    rw [Gate.applyNat_CX_commute_update_outside_fun controlIdx flagPos updateIdx v _
          hupdate_ne_control hupdate_ne_flag]

/-! ## Tick 74 — Multiplier-bit install helper for bridging. -/

/-- Recursively install multiplier bits `k = 0, ..., num_bits - 1` from `m`,
**skipping** bit `j`. -/
def install_mult_bits_skip_j (bits m j : Nat) : Nat → (Nat → Bool) → (Nat → Bool)
  | 0,     f => f
  | n + 1, f =>
    if n = j then install_mult_bits_skip_j bits m j n f
    else update (install_mult_bits_skip_j bits m j n f) (sqir_mult_control_idx bits n) (m.testBit n)

/-- **`install_mult_bits_skip_j` at outside workspace.**  At any position
`q < 2 + 2 * bits + 1`, the installs don't touch `q` (they update only at
multiplier positions). -/
theorem install_mult_bits_skip_j_at_workspace_eq
    (bits m j num_bits : Nat) (f : Nat → Bool) (q : Nat)
    (hq : q < 2 + 2 * bits + 1) :
    install_mult_bits_skip_j bits m j num_bits f q = f q := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_eq : k = j
    · rw [if_pos h_eq]; exact ih
    · rw [if_neg h_eq]
      have h_ne : q ≠ sqir_mult_control_idx bits k := by
        have h_ctrl_ge : sqir_mult_control_idx bits k ≥ 2 + 2 * bits + 1 := by
          unfold sqir_mult_control_idx; omega
        omega
      rw [update_neq _ _ _ _ h_ne]
      exact ih

/-- **`install_mult_bits_skip_j` at multiplier position `k`** (`k < num_bits`,
`k ≠ j`): installs `m.testBit k`. -/
theorem install_mult_bits_skip_j_at_mult_k_eq
    (bits m j num_bits k : Nat) (f : Nat → Bool)
    (h_k_lt : k < num_bits) (h_k_ne_j : k ≠ j) :
    install_mult_bits_skip_j bits m j num_bits f (sqir_mult_control_idx bits k)
      = m.testBit k := by
  induction num_bits with
  | zero => omega
  | succ n ih =>
    unfold install_mult_bits_skip_j
    by_cases h_eq : n = j
    · rw [if_pos h_eq]
      -- After skip, recurse with smaller num_bits.  Need k < n.
      apply ih
      omega
    · rw [if_neg h_eq]
      by_cases h_kn : k = n
      · rw [h_kn, update_eq]
      · have h_ne : sqir_mult_control_idx bits k ≠ sqir_mult_control_idx bits n := by
          intro heq
          exact h_kn (sqir_mult_control_idx_injective bits k n heq)
        rw [update_neq _ _ _ _ h_ne]
        apply ih
        omega

/-- **`install_mult_bits_skip_j` at the skipped position `j`.**  Installs
never touch position `controlIdx_j` (always skipped), so the install
returns `f (controlIdx_j)`. -/
theorem install_mult_bits_skip_j_at_j_eq
    (bits m j num_bits : Nat) (f : Nat → Bool) :
    install_mult_bits_skip_j bits m j num_bits f (sqir_mult_control_idx bits j)
      = f (sqir_mult_control_idx bits j) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_ne : sqir_mult_control_idx bits j ≠ sqir_mult_control_idx bits k :=
        fun heq => h_kj (sqir_mult_control_idx_injective bits j k heq).symm
      rw [update_neq _ _ _ _ h_ne]
      exact ih

/-- **`install_mult_bits_skip_j` at outside-multiplier upper positions.**
For `q ≥ 2 + 2 * bits + 1 + bits` (above the multiplier register), installs
don't touch `q`. -/
theorem install_mult_bits_skip_j_at_above_eq
    (bits m j num_bits : Nat) (h_num_le : num_bits ≤ bits) (f : Nat → Bool) (q : Nat)
    (hq : q ≥ 2 + 2 * bits + 1 + bits) :
    install_mult_bits_skip_j bits m j num_bits f q = f q := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_eq : k = j
    · rw [if_pos h_eq]; exact ih (by omega)
    · rw [if_neg h_eq]
      have h_ne : q ≠ sqir_mult_control_idx bits k := by
        have h_ctrl_lt : sqir_mult_control_idx bits k < 2 + 2 * bits + 1 + bits := by
          unfold sqir_mult_control_idx; omega
        omega
      rw [update_neq _ _ _ _ h_ne]
      exact ih (by omega)

/-! ## Deliverable B — Bridge: `sqir_mult_input_F` as install over `F_j`. -/

/-- **`sqir_mult_input_F` decomposes as `install_mult_bits_skip_j` applied
to `update (cuccaro_input_F) controlIdx_j (m.testBit j)`.** -/
theorem sqir_mult_input_F_eq_install_with_j
    (bits m acc j : Nat) (hj : j < bits) (hacc : acc < 2 ^ bits) :
    sqir_mult_input_F bits m acc
      = install_mult_bits_skip_j bits m j bits
          (update (cuccaro_input_F 2 false 0 acc) (sqir_mult_control_idx bits j) (m.testBit j)) := by
  funext q
  by_cases hq_ws : q < 2 + 2 * bits + 1
  · -- q < workspace upper bound: both sides = cuccaro_input_F at q.
    rw [install_mult_bits_skip_j_at_workspace_eq bits m j bits _ q hq_ws]
    -- LHS: sqir_mult_input_F q = cuccaro_input_F at q.
    have h_lhs : sqir_mult_input_F bits m acc q = cuccaro_input_F 2 false 0 acc q := by
      unfold sqir_mult_input_F; rw [if_pos hq_ws]
    -- RHS: update F controlIdx_j _ at q = F at q (since q < controlIdx_j).
    have h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx bits j := by
      have : sqir_mult_control_idx bits j ≥ 2 + 2 * bits + 1 := by
        unfold sqir_mult_control_idx; omega
      omega
    rw [h_lhs, update_neq _ _ _ _ h_q_ne_ctrl_j]
  · push_neg at hq_ws
    -- q ≥ 2 + 2*bits + 1.
    by_cases hq_in_mult : q < 2 + 2 * bits + 1 + bits
    · -- q is in multiplier register.
      set k := q - (2 + 2 * bits + 1) with hk_def
      have hk_lt : k < bits := by omega
      have h_q_eq : q = sqir_mult_control_idx bits k := by
        unfold sqir_mult_control_idx; omega
      rw [h_q_eq]
      have h_lhs : sqir_mult_input_F bits m acc (sqir_mult_control_idx bits k)
                 = m.testBit k :=
        sqir_mult_input_control_bit bits m acc k hk_lt
      rw [h_lhs]
      by_cases h_kj : k = j
      · -- k = j: install skips, but F_j has the j-th update directly.
        rw [h_kj]
        rw [install_mult_bits_skip_j_at_j_eq bits m j bits _]
        rw [update_eq]
      · -- k ≠ j: install puts m.testBit k at controlIdx_k.
        rw [install_mult_bits_skip_j_at_mult_k_eq bits m j bits k _ hk_lt h_kj]
    · push_neg at hq_in_mult
      -- q ≥ 2 + 2*bits + 1 + bits.
      rw [install_mult_bits_skip_j_at_above_eq bits m j bits (le_refl _) _ q hq_in_mult]
      have h_lhs : sqir_mult_input_F bits m acc q = false := by
        unfold sqir_mult_input_F
        rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
        rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]
      have h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx bits j := by
        have : sqir_mult_control_idx bits j < 2 + 2 * bits + 1 + bits := by
          unfold sqir_mult_control_idx; omega
        omega
      rw [h_lhs, update_neq _ _ _ _ h_q_ne_ctrl_j]
      -- cuccaro_input_F at q (≥ 2 + 2*bits + 1) = false (q ≥ q_start + 2*bits + 1).
      exact (cuccaro_input_F_above_eq_false 2 bits acc q (by omega) hacc).symm

/-! ## R7d^xxix-L-3.15b — q_start-parametric install infrastructure.

q_start-parametric counterparts of `install_mult_bits_skip_j` and its
four position lemmas, plus the bridge `_eq_install_with_j_qstart`.
This sub-tick depends only on the L-3.15a infrastructure
(`sqir_mult_control_idx_qstart`, `_injective_qstart`,
`sqir_mult_input_F_qstart`, `_input_control_bit_qstart`) and the
already-q_start-parametric `cuccaro_input_F_above_eq_false`.

After this sub-tick, the next step (L-3.15c) is to add
`cuccaro_target_val_through_install_mult_qstart` and the headline
`sqir_modmult_step_target_decode_qstart`. -/

/-- q_start-parametric: recursively install multiplier bits
`k = 0, ..., num_bits - 1` from `m`, **skipping** bit `j`.  Port of
`install_mult_bits_skip_j` (line 447). -/
def install_mult_bits_skip_j_qstart (bits q_start m j : Nat) :
    Nat → (Nat → Bool) → (Nat → Bool)
  | 0,     f => f
  | n + 1, f =>
    if n = j then install_mult_bits_skip_j_qstart bits q_start m j n f
    else update (install_mult_bits_skip_j_qstart bits q_start m j n f)
                (sqir_mult_control_idx_qstart bits q_start n) (m.testBit n)

/-- q_start-parametric: install chain does not modify positions strictly
below `q_start + 2 * bits + 1`.  Port of
`install_mult_bits_skip_j_at_workspace_eq` (line 456). -/
theorem install_mult_bits_skip_j_at_workspace_eq_qstart
    (bits q_start m j num_bits : Nat) (f : Nat → Bool) (q : Nat)
    (hq : q < q_start + 2 * bits + 1) :
    install_mult_bits_skip_j_qstart bits q_start m j num_bits f q = f q := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_eq : k = j
    · rw [if_pos h_eq]; exact ih
    · rw [if_neg h_eq]
      have h_ne : q ≠ sqir_mult_control_idx_qstart bits q_start k := by
        have h_ctrl_ge :
            sqir_mult_control_idx_qstart bits q_start k ≥ q_start + 2 * bits + 1 := by
          unfold sqir_mult_control_idx_qstart; omega
        omega
      rw [update_neq _ _ _ _ h_ne]
      exact ih

/-- q_start-parametric: install chain at multiplier position `k`
(`k < num_bits`, `k ≠ j`) installs `m.testBit k`.  Port of
`install_mult_bits_skip_j_at_mult_k_eq` (line 476). -/
theorem install_mult_bits_skip_j_at_mult_k_eq_qstart
    (bits q_start m j num_bits k : Nat) (f : Nat → Bool)
    (h_k_lt : k < num_bits) (h_k_ne_j : k ≠ j) :
    install_mult_bits_skip_j_qstart bits q_start m j num_bits f
        (sqir_mult_control_idx_qstart bits q_start k) = m.testBit k := by
  induction num_bits with
  | zero => omega
  | succ n ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_eq : n = j
    · rw [if_pos h_eq]
      apply ih
      omega
    · rw [if_neg h_eq]
      by_cases h_kn : k = n
      · rw [h_kn, update_eq]
      · have h_ne :
            sqir_mult_control_idx_qstart bits q_start k
              ≠ sqir_mult_control_idx_qstart bits q_start n := by
          intro heq
          exact h_kn (sqir_mult_control_idx_injective_qstart bits q_start k n heq)
        rw [update_neq _ _ _ _ h_ne]
        apply ih
        omega

/-- q_start-parametric: install chain at the skipped position `j` is
preserved from the base state.  Port of
`install_mult_bits_skip_j_at_j_eq` (line 503). -/
theorem install_mult_bits_skip_j_at_j_eq_qstart
    (bits q_start m j num_bits : Nat) (f : Nat → Bool) :
    install_mult_bits_skip_j_qstart bits q_start m j num_bits f
        (sqir_mult_control_idx_qstart bits q_start j)
      = f (sqir_mult_control_idx_qstart bits q_start j) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_ne :
          sqir_mult_control_idx_qstart bits q_start j
            ≠ sqir_mult_control_idx_qstart bits q_start k :=
        fun heq => h_kj
          (sqir_mult_control_idx_injective_qstart bits q_start j k heq).symm
      rw [update_neq _ _ _ _ h_ne]
      exact ih

/-- q_start-parametric: install chain identity above the multiplier
register.  Port of `install_mult_bits_skip_j_at_above_eq` (line 522). -/
theorem install_mult_bits_skip_j_at_above_eq_qstart
    (bits q_start m j num_bits : Nat) (h_num_le : num_bits ≤ bits)
    (f : Nat → Bool) (q : Nat)
    (hq : q ≥ q_start + 2 * bits + 1 + bits) :
    install_mult_bits_skip_j_qstart bits q_start m j num_bits f q = f q := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_eq : k = j
    · rw [if_pos h_eq]; exact ih (by omega)
    · rw [if_neg h_eq]
      have h_ne : q ≠ sqir_mult_control_idx_qstart bits q_start k := by
        have h_ctrl_lt :
            sqir_mult_control_idx_qstart bits q_start k < q_start + 2 * bits + 1 + bits := by
          unfold sqir_mult_control_idx_qstart; omega
        omega
      rw [update_neq _ _ _ _ h_ne]
      exact ih (by omega)

/-- q_start-parametric bridge: `sqir_mult_input_F_qstart bits q_start m
acc` decomposes as `install_mult_bits_skip_j_qstart` applied to
`update (cuccaro_input_F q_start false 0 acc) (sqir_mult_control_idx_qstart
bits q_start j) (m.testBit j)`.  Port of
`sqir_mult_input_F_eq_install_with_j` (line 544). -/
theorem sqir_mult_input_F_eq_install_with_j_qstart
    (bits q_start m acc j : Nat) (hj : j < bits) (hacc : acc < 2 ^ bits) :
    sqir_mult_input_F_qstart bits q_start m acc
      = install_mult_bits_skip_j_qstart bits q_start m j bits
          (update (cuccaro_input_F q_start false 0 acc)
            (sqir_mult_control_idx_qstart bits q_start j) (m.testBit j)) := by
  funext q
  by_cases hq_ws : q < q_start + 2 * bits + 1
  · -- q below workspace upper bound: both sides equal `cuccaro_input_F` at q.
    rw [install_mult_bits_skip_j_at_workspace_eq_qstart bits q_start m j bits _ q hq_ws]
    have h_lhs : sqir_mult_input_F_qstart bits q_start m acc q
                = cuccaro_input_F q_start false 0 acc q := by
      unfold sqir_mult_input_F_qstart; rw [if_pos hq_ws]
    have h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx_qstart bits q_start j := by
      have : sqir_mult_control_idx_qstart bits q_start j ≥ q_start + 2 * bits + 1 := by
        unfold sqir_mult_control_idx_qstart; omega
      omega
    rw [h_lhs, update_neq _ _ _ _ h_q_ne_ctrl_j]
  · push_neg at hq_ws
    by_cases hq_in_mult : q < q_start + 2 * bits + 1 + bits
    · -- q is in multiplier register.
      set k := q - (q_start + 2 * bits + 1) with hk_def
      have hk_lt : k < bits := by omega
      have h_q_eq : q = sqir_mult_control_idx_qstart bits q_start k := by
        unfold sqir_mult_control_idx_qstart; omega
      rw [h_q_eq]
      have h_lhs : sqir_mult_input_F_qstart bits q_start m acc
                      (sqir_mult_control_idx_qstart bits q_start k)
                 = m.testBit k :=
        sqir_mult_input_control_bit_qstart bits q_start m acc k hk_lt
      rw [h_lhs]
      by_cases h_kj : k = j
      · -- k = j: install skips, but the base state has the j-th update.
        rw [h_kj]
        rw [install_mult_bits_skip_j_at_j_eq_qstart bits q_start m j bits _]
        rw [update_eq]
      · -- k ≠ j: install puts m.testBit k at controlIdx_k.
        rw [install_mult_bits_skip_j_at_mult_k_eq_qstart bits q_start m j bits k _
              hk_lt h_kj]
    · push_neg at hq_in_mult
      -- q ≥ q_start + 2*bits + 1 + bits.
      rw [install_mult_bits_skip_j_at_above_eq_qstart bits q_start m j bits (le_refl _) _ q
            hq_in_mult]
      have h_lhs : sqir_mult_input_F_qstart bits q_start m acc q = false := by
        unfold sqir_mult_input_F_qstart
        rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1)]
        rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1 + bits)]
      have h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx_qstart bits q_start j := by
        have : sqir_mult_control_idx_qstart bits q_start j < q_start + 2 * bits + 1 + bits := by
          unfold sqir_mult_control_idx_qstart; omega
        omega
      rw [h_lhs, update_neq _ _ _ _ h_q_ne_ctrl_j]
      exact (cuccaro_input_F_above_eq_false q_start bits acc q (by omega) hacc).symm

/-! ## Tick 74 — Deliverable C: One-step target decode. -/

/-- **`cuccaro_target_val` is invariant under installing multiplier bits
on the gate-applied state.**  Each installed update is at position
`controlIdx_k` (outside workspace), so by Deliverable A (commute with
update) + `cuccaro_target_val_update_outside_workspace`, the target
register's decoded value is unchanged. -/
theorem cuccaro_target_val_through_install_mult
    (bits m j N c : Nat) (num_bits : Nat) (f : Nat → Bool) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1)
          (install_mult_bits_skip_j bits m j num_bits f))
      = cuccaro_target_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1) f) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_kj : k = j
    · rw [if_pos h_kj]
      exact ih
    · rw [if_neg h_kj]
      -- Apply Deliverable A to commute the gate with the update at controlIdx_k.
      have h_out : sqir_mult_control_idx bits k < 2
            ∨ 2 + (2 * bits + 1) ≤ sqir_mult_control_idx bits k := by
        right; unfold sqir_mult_control_idx; omega
      have h_ne_flag : sqir_mult_control_idx bits k ≠ 1 := by
        unfold sqir_mult_control_idx; omega
      have h_ne_ctrl_j :
          sqir_mult_control_idx bits k ≠ sqir_mult_control_idx bits j :=
        fun heq => h_kj (sqir_mult_control_idx_injective bits k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N c
            (sqir_mult_control_idx bits j) (sqir_mult_control_idx bits k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [cuccaro_target_val_update_outside_workspace bits 2
            (sqir_mult_control_idx bits k) (m.testBit k) _ h_out]
      exact ih

/-- **Deliverable C — One-step modular-multiplier target decode.**

After applying `sqir_modmult_step_gate bits N a j` to
`sqir_mult_input_F bits m acc`, the decoded target register equals
`if m.testBit j then (acc + (a * 2^j) % N) % N else acc`. -/
theorem sqir_modmult_step_target_decode
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc))
      = if m.testBit j then (acc + (a * 2 ^ j) % N) % N else acc := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  -- Bridge sqir_mult_input_F to install over F_j (Deliverable B).
  rw [sqir_mult_input_F_eq_install_with_j bits m acc j hj hacc_lt]
  unfold sqir_modmult_step_gate
  -- Push gate through install (target_val invariant).
  rw [cuccaro_target_val_through_install_mult bits m j N ((a * 2^j) % N) bits]
  -- Apply gate_clean target_decode on F_j.
  have h_ctrl_out :
      sqir_mult_control_idx bits j < 2
        ∨ 2 + 2 * bits + 1 ≤ sqir_mult_control_idx bits j :=
    sqir_mult_control_idx_outside_modadd_workspace_form bits j
  have h_ctrl_ne_flag : sqir_mult_control_idx bits j ≠ 1 :=
    sqir_mult_control_idx_ne_flag bits j
  have h_ctrl_lt : sqir_mult_control_idx bits j < sqir_modmult_rev_anc bits :=
    sqir_mult_control_idx_lt_sqir_dim bits j hj
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  have ⟨_, h_tgt, _⟩ :=
    sqir_style_controlledModAddConst_gate_clean bits N ((a * 2^j) % N) acc
      (sqir_mult_control_idx bits j) (m.testBit j)
      hbits hN_pos hN hN2 hc_pos hacc h_ctrl_out h_ctrl_ne_flag h_ctrl_lt
  exact h_tgt

/-! ## R7d^xxix-L-3.15c — q_start-parametric target-through-install
       bridge + step target-decode headline.

q_start-parametric counterparts of `cuccaro_target_val_through_install_mult`
and the headline `sqir_modmult_step_target_decode`.  Uses the L-3.15a
infrastructure (control-index facts, commute helper) and the L-3.15b
install chain + bridge, plus the L-3.14′
`sqir_style_controlledModAddConst_gate_clean_qstart`.

This sub-tick closes the q_start chain at the modular-multiplier-step
target-decode layer.  Workspace preservation
(`sqir_modmult_step_workspace_qstart`) is intentionally deferred. -/

/-- q_start-parametric: installing multiplier bits (other than the
j-th) outside the Cuccaro workspace does not change the gate's decoded
target value.  Port of `cuccaro_target_val_through_install_mult`
(line 782). -/
theorem cuccaro_target_val_through_install_mult_qstart
    (bits q_start m j N c flagPos : Nat) (num_bits : Nat) (f : Nat → Bool)
    (h_flag_lt_qstart : flagPos < q_start) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos)
          (install_mult_bits_skip_j_qstart bits q_start m j num_bits f))
      = cuccaro_target_val bits q_start
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos) f) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_kj : k = j
    · rw [if_pos h_kj]
      exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx_qstart bits q_start k < q_start
            ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start k :=
        sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start k
      have h_ne_flag : sqir_mult_control_idx_qstart bits q_start k ≠ flagPos :=
        sqir_mult_control_idx_ne_flag_qstart bits q_start k flagPos h_flag_lt_qstart
      have h_ne_ctrl_j :
          sqir_mult_control_idx_qstart bits q_start k
            ≠ sqir_mult_control_idx_qstart bits q_start j :=
        fun heq => h_kj (sqir_mult_control_idx_injective_qstart bits q_start k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos
            (sqir_mult_control_idx_qstart bits q_start k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [cuccaro_target_val_update_outside_workspace bits q_start
            (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k) _ h_out]
      exact ih

/-- **R7d^xxix-L-3.15c HEADLINE: q_start-parametric one-step modular-
multiplier target decode.**

After applying `sqir_modmult_step_gate_qstart bits q_start N a j flagPos`
to `sqir_mult_input_F_qstart bits q_start m acc`, the decoded target
register equals `if m.testBit j then (acc + (a * 2^j) % N) % N else acc`.

Port of `sqir_modmult_step_target_decode` (line 820).  Uses the L-3.14′
`sqir_style_controlledModAddConst_gate_clean_qstart`, the L-3.15a
control-index facts, and the L-3.15b install bridge + this tick's
`_through_install_mult_qstart`.

The `flagPos < q_start` hypothesis matches the hard-coded `flagPos = 1
< 2 = q_start` case and ensures `flagPos` is distinct from every
multiplier-bit position. -/
theorem sqir_modmult_step_target_decode_qstart
    (bits q_start N a j m acc dim flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
          (sqir_mult_input_F_qstart bits q_start m acc))
      = if m.testBit j then (acc + (a * 2 ^ j) % N) % N else acc := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  -- Bridge sqir_mult_input_F_qstart to install over F_j (L-3.15b).
  rw [sqir_mult_input_F_eq_install_with_j_qstart bits q_start m acc j hj hacc_lt]
  unfold sqir_modmult_step_gate_qstart
  -- Push gate through install (this tick's bridge).
  rw [cuccaro_target_val_through_install_mult_qstart bits q_start m j N ((a * 2^j) % N)
        flagPos bits _ h_flag_lt_qstart]
  -- Apply L-3.14′ gate_clean_qstart on the j-th-installed F.
  have h_ctrl_out :
      sqir_mult_control_idx_qstart bits q_start j < q_start
        ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start j :=
    sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start j
  have h_flag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos :=
    Or.inl h_flag_lt_qstart
  have h_ctrl_ne_flag : sqir_mult_control_idx_qstart bits q_start j ≠ flagPos :=
    sqir_mult_control_idx_ne_flag_qstart bits q_start j flagPos h_flag_lt_qstart
  have h_ctrl_lt_dim : sqir_mult_control_idx_qstart bits q_start j < dim :=
    sqir_mult_control_idx_lt_dim_qstart bits q_start j dim hj h_dim_covers_mult
  have h_flag_lt_dim : flagPos < dim := by omega
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  have ⟨_, h_tgt, _⟩ :=
    sqir_style_controlledModAddConst_gate_clean_qstart bits q_start N ((a * 2^j) % N) acc dim
      (sqir_mult_control_idx_qstart bits q_start j) flagPos (m.testBit j)
      hbits hN_pos hN hN2 hc_pos hacc h_ctrl_out h_flag_out h_ctrl_ne_flag
      h_workspace h_ctrl_lt_dim h_flag_lt_dim
  exact h_tgt

/-! ## Tick 74 — Deliverable D: One-step workspace preservation. -/

/-- **Read register invariant through install.** -/
theorem cuccaro_read_val_through_install_mult
    (bits m j N c : Nat) (num_bits : Nat) (f : Nat → Bool) :
    cuccaro_read_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1)
          (install_mult_bits_skip_j bits m j num_bits f))
      = cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1) f) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx bits k < 2
            ∨ 2 + (2 * bits + 1) ≤ sqir_mult_control_idx bits k := by
        right; unfold sqir_mult_control_idx; omega
      have h_ne_flag : sqir_mult_control_idx bits k ≠ 1 := by
        unfold sqir_mult_control_idx; omega
      have h_ne_ctrl_j :
          sqir_mult_control_idx bits k ≠ sqir_mult_control_idx bits j :=
        fun heq => h_kj (sqir_mult_control_idx_injective bits k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N c
            (sqir_mult_control_idx bits j) (sqir_mult_control_idx bits k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [cuccaro_read_val_update_outside_workspace bits 2
            (sqir_mult_control_idx bits k) (m.testBit k) _ h_out]
      exact ih

/-- **Position-wise invariance through install at workspace positions.** -/
theorem applyNat_modmult_through_install_at_workspace
    (bits m j N c : Nat) (num_bits q : Nat) (f : Nat → Bool)
    (hq_ws : q < 2 + 2 * bits + 1) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1)
      (install_mult_bits_skip_j bits m j num_bits f) q
      = Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1) f q := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx bits k < 2
            ∨ 2 + (2 * bits + 1) ≤ sqir_mult_control_idx bits k := by
        right; unfold sqir_mult_control_idx; omega
      have h_ne_flag : sqir_mult_control_idx bits k ≠ 1 := by
        unfold sqir_mult_control_idx; omega
      have h_ne_ctrl_j :
          sqir_mult_control_idx bits k ≠ sqir_mult_control_idx bits j :=
        fun heq => h_kj (sqir_mult_control_idx_injective bits k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N c
            (sqir_mult_control_idx bits j) (sqir_mult_control_idx bits k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      have h_q_ne_ctrl_k : q ≠ sqir_mult_control_idx bits k := by
        unfold sqir_mult_control_idx; omega
      rw [update_neq _ _ _ _ h_q_ne_ctrl_k]
      exact ih

/-- **Position-wise invariance through install at the controlIdx_j position.** -/
theorem applyNat_modmult_through_install_at_j
    (bits m j N c : Nat) (num_bits : Nat) (f : Nat → Bool) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1)
      (install_mult_bits_skip_j bits m j num_bits f) (sqir_mult_control_idx bits j)
      = Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1) f (sqir_mult_control_idx bits j) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx bits k < 2
            ∨ 2 + (2 * bits + 1) ≤ sqir_mult_control_idx bits k := by
        right; unfold sqir_mult_control_idx; omega
      have h_ne_flag : sqir_mult_control_idx bits k ≠ 1 := by
        unfold sqir_mult_control_idx; omega
      have h_ne_ctrl_j :
          sqir_mult_control_idx bits k ≠ sqir_mult_control_idx bits j :=
        fun heq => h_kj (sqir_mult_control_idx_injective bits k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N c
            (sqir_mult_control_idx bits j) (sqir_mult_control_idx bits k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [update_neq _ _ _ _ (Ne.symm h_ne_ctrl_j)]
      exact ih

/-- **Deliverable D — One-step workspace preservation.**

After applying the step gate, the read register is 0, the top carry is
false, the flag bit is false, and the multiplier control bit `j` is
preserved as `m.testBit j`. -/
theorem sqir_modmult_step_workspace
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    cuccaro_read_val bits 2
        (Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc)) = 0
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) (2 + 2 * bits) = false
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) 1 = false
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) (sqir_mult_control_idx bits j) = m.testBit j := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  rw [sqir_mult_input_F_eq_install_with_j bits m acc j hj hacc_lt]
  unfold sqir_modmult_step_gate
  -- gate_clean facts on F_j.
  have h_ctrl_out :
      sqir_mult_control_idx bits j < 2
        ∨ 2 + 2 * bits + 1 ≤ sqir_mult_control_idx bits j :=
    sqir_mult_control_idx_outside_modadd_workspace_form bits j
  have h_ctrl_ne_flag : sqir_mult_control_idx bits j ≠ 1 :=
    sqir_mult_control_idx_ne_flag bits j
  have h_ctrl_lt : sqir_mult_control_idx bits j < sqir_modmult_rev_anc bits :=
    sqir_mult_control_idx_lt_sqir_dim bits j hj
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  have ⟨_, _, h_rd, h_tc, h_fl, h_ctrl⟩ :=
    sqir_style_controlledModAddConst_gate_clean bits N ((a * 2^j) % N) acc
      (sqir_mult_control_idx bits j) (m.testBit j)
      hbits hN_pos hN hN2 hc_pos hacc h_ctrl_out h_ctrl_ne_flag h_ctrl_lt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cuccaro_read_val_through_install_mult bits m j N ((a * 2^j) % N) bits]
    exact h_rd
  · rw [applyNat_modmult_through_install_at_workspace bits m j N ((a * 2^j) % N) bits
          (2 + 2 * bits) _ (by omega)]
    exact h_tc
  · rw [applyNat_modmult_through_install_at_workspace bits m j N ((a * 2^j) % N) bits
          1 _ (by omega)]
    exact h_fl
  · rw [applyNat_modmult_through_install_at_j bits m j N ((a * 2^j) % N) bits]
    exact h_ctrl

/-! ## R7d^xxix-L-3.15d — q_start-parametric step workspace
       preservation.

q_start-parametric counterparts of the three install-bridge helpers
(`cuccaro_read_val_through_install_mult`, `applyNat_modmult_through_install_at_workspace`,
`applyNat_modmult_through_install_at_j`) and the headline
`sqir_modmult_step_workspace`.  Mirrors the L-3.15c structure but on
workspace conjuncts (read register, top carry, flag, control-bit
preservation). -/

/-- q_start-parametric: installing multiplier bits (other than the
j-th) outside the Cuccaro workspace preserves the decoded read/workspace
value.  Port of `cuccaro_read_val_through_install_mult` (line 958). -/
theorem cuccaro_read_val_through_install_mult_qstart
    (bits q_start m j N c flagPos : Nat) (num_bits : Nat) (f : Nat → Bool)
    (h_flag_lt_qstart : flagPos < q_start) :
    cuccaro_read_val bits q_start
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos)
          (install_mult_bits_skip_j_qstart bits q_start m j num_bits f))
      = cuccaro_read_val bits q_start
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos) f) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx_qstart bits q_start k < q_start
            ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start k :=
        sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start k
      have h_ne_flag : sqir_mult_control_idx_qstart bits q_start k ≠ flagPos :=
        sqir_mult_control_idx_ne_flag_qstart bits q_start k flagPos h_flag_lt_qstart
      have h_ne_ctrl_j :
          sqir_mult_control_idx_qstart bits q_start k
            ≠ sqir_mult_control_idx_qstart bits q_start j :=
        fun heq => h_kj (sqir_mult_control_idx_injective_qstart bits q_start k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos
            (sqir_mult_control_idx_qstart bits q_start k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [cuccaro_read_val_update_outside_workspace bits q_start
            (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k) _ h_out]
      exact ih

/-- q_start-parametric: install chain commutes with the step gate at
any single workspace position `q < q_start + 2 * bits + 1`.  Port of
`applyNat_modmult_through_install_at_workspace` (line 990). -/
theorem applyNat_modmult_through_install_at_workspace_qstart
    (bits q_start m j N c flagPos : Nat) (num_bits q : Nat) (f : Nat → Bool)
    (h_flag_lt_qstart : flagPos < q_start)
    (hq_ws : q < q_start + 2 * bits + 1) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
        (sqir_mult_control_idx_qstart bits q_start j) flagPos)
      (install_mult_bits_skip_j_qstart bits q_start m j num_bits f) q
      = Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
        (sqir_mult_control_idx_qstart bits q_start j) flagPos) f q := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx_qstart bits q_start k < q_start
            ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start k :=
        sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start k
      have h_ne_flag : sqir_mult_control_idx_qstart bits q_start k ≠ flagPos :=
        sqir_mult_control_idx_ne_flag_qstart bits q_start k flagPos h_flag_lt_qstart
      have h_ne_ctrl_j :
          sqir_mult_control_idx_qstart bits q_start k
            ≠ sqir_mult_control_idx_qstart bits q_start j :=
        fun heq => h_kj (sqir_mult_control_idx_injective_qstart bits q_start k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos
            (sqir_mult_control_idx_qstart bits q_start k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      have h_q_ne_ctrl_k : q ≠ sqir_mult_control_idx_qstart bits q_start k := by
        unfold sqir_mult_control_idx_qstart; omega
      rw [update_neq _ _ _ _ h_q_ne_ctrl_k]
      exact ih

/-- q_start-parametric: install chain commutes with the step gate at
the j-th multiplier control position.  Port of
`applyNat_modmult_through_install_at_j` (line 1022). -/
theorem applyNat_modmult_through_install_at_j_qstart
    (bits q_start m j N c flagPos : Nat) (num_bits : Nat) (f : Nat → Bool)
    (h_flag_lt_qstart : flagPos < q_start) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
        (sqir_mult_control_idx_qstart bits q_start j) flagPos)
      (install_mult_bits_skip_j_qstart bits q_start m j num_bits f)
        (sqir_mult_control_idx_qstart bits q_start j)
      = Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
        (sqir_mult_control_idx_qstart bits q_start j) flagPos) f
          (sqir_mult_control_idx_qstart bits q_start j) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    unfold install_mult_bits_skip_j_qstart
    by_cases h_kj : k = j
    · rw [if_pos h_kj]; exact ih
    · rw [if_neg h_kj]
      have h_out : sqir_mult_control_idx_qstart bits q_start k < q_start
            ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start k :=
        sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start k
      have h_ne_flag : sqir_mult_control_idx_qstart bits q_start k ≠ flagPos :=
        sqir_mult_control_idx_ne_flag_qstart bits q_start k flagPos h_flag_lt_qstart
      have h_ne_ctrl_j :
          sqir_mult_control_idx_qstart bits q_start k
            ≠ sqir_mult_control_idx_qstart bits q_start j :=
        fun heq => h_kj (sqir_mult_control_idx_injective_qstart bits q_start k j heq)
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos
            (sqir_mult_control_idx_qstart bits q_start k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [update_neq _ _ _ _ (Ne.symm h_ne_ctrl_j)]
      exact ih

/-- **R7d^xxix-L-3.15d HEADLINE: q_start-parametric one-step
modular-multiplier workspace preservation.**

After applying `sqir_modmult_step_gate_qstart` to
`sqir_mult_input_F_qstart`:
1. the read register decodes to 0;
2. the top carry position (`q_start + 2 * bits`) is `false`;
3. `flagPos` is `false`;
4. the j-th multiplier control position holds `m.testBit j`.

Port of `sqir_modmult_step_workspace` (line 1055). -/
theorem sqir_modmult_step_workspace_qstart
    (bits q_start N a j m acc dim flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_read_val bits q_start
        (Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
          (sqir_mult_input_F_qstart bits q_start m acc)) = 0
    ∧ Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
          (sqir_mult_input_F_qstart bits q_start m acc) (q_start + 2 * bits) = false
    ∧ Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
          (sqir_mult_input_F_qstart bits q_start m acc) flagPos = false
    ∧ Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
          (sqir_mult_input_F_qstart bits q_start m acc)
          (sqir_mult_control_idx_qstart bits q_start j) = m.testBit j := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  rw [sqir_mult_input_F_eq_install_with_j_qstart bits q_start m acc j hj hacc_lt]
  unfold sqir_modmult_step_gate_qstart
  have h_ctrl_out :
      sqir_mult_control_idx_qstart bits q_start j < q_start
        ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start j :=
    sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start j
  have h_flag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos :=
    Or.inl h_flag_lt_qstart
  have h_ctrl_ne_flag : sqir_mult_control_idx_qstart bits q_start j ≠ flagPos :=
    sqir_mult_control_idx_ne_flag_qstart bits q_start j flagPos h_flag_lt_qstart
  have h_ctrl_lt_dim : sqir_mult_control_idx_qstart bits q_start j < dim :=
    sqir_mult_control_idx_lt_dim_qstart bits q_start j dim hj h_dim_covers_mult
  have h_flag_lt_dim : flagPos < dim := by omega
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  have ⟨_, _, h_rd, h_tc, h_fl, h_ctrl⟩ :=
    sqir_style_controlledModAddConst_gate_clean_qstart bits q_start N ((a * 2^j) % N) acc dim
      (sqir_mult_control_idx_qstart bits q_start j) flagPos (m.testBit j)
      hbits hN_pos hN hN2 hc_pos hacc h_ctrl_out h_flag_out h_ctrl_ne_flag
      h_workspace h_ctrl_lt_dim h_flag_lt_dim
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cuccaro_read_val_through_install_mult_qstart bits q_start m j N ((a * 2^j) % N) flagPos
          bits _ h_flag_lt_qstart]
    exact h_rd
  · rw [applyNat_modmult_through_install_at_workspace_qstart bits q_start m j N ((a * 2^j) % N)
          flagPos bits (q_start + 2 * bits) _ h_flag_lt_qstart (by omega)]
    exact h_tc
  · rw [applyNat_modmult_through_install_at_workspace_qstart bits q_start m j N ((a * 2^j) % N)
          flagPos bits flagPos _ h_flag_lt_qstart (by omega)]
    exact h_fl
  · rw [applyNat_modmult_through_install_at_j_qstart bits q_start m j N ((a * 2^j) % N) flagPos
          bits _ h_flag_lt_qstart]
    exact h_ctrl

/-! ## R7d^xxix-L-3.15e.1 — q_start-parametric prefix/const-gate
       definitions + sub-q_start input-state mini-helpers.

Smallest piece of the L-3.15e decomposition: provides the recursive
`sqir_modmult_prefix_gate_qstart` and the `bits`-fold
`sqir_modmult_const_gate_qstart` (plus zero/succ unfold lemmas), and
ports the trivial input-state flag-position helpers
`sqir_mult_input_flag_0_false` / `_flag_1_false` to the q_start
input.  No new arithmetic; consumed by subsequent L-3.15e.* sub-ticks. -/

/-- q_start-parametric input flag-0 mini-helper.  At position 0 of
`sqir_mult_input_F_qstart`, the bit is `false`, provided position 0
is below the Cuccaro workspace start.  Port of
`sqir_mult_input_flag_0_false` (line 143). -/
theorem sqir_mult_input_flag_0_false_qstart
    (bits q_start m acc : Nat) (h_lt : 0 < q_start) :
    sqir_mult_input_F_qstart bits q_start m acc 0 = false := by
  unfold sqir_mult_input_F_qstart
  rw [if_pos (by omega : (0 : Nat) < q_start + 2 * bits + 1)]
  unfold cuccaro_input_F
  rw [if_pos h_lt]

/-- q_start-parametric input flag-1 mini-helper.  At position 1 of
`sqir_mult_input_F_qstart`, the bit is `false`, provided position 1
is below the Cuccaro workspace start.  Port of
`sqir_mult_input_flag_1_false` (line 151). -/
theorem sqir_mult_input_flag_1_false_qstart
    (bits q_start m acc : Nat) (h_lt : 1 < q_start) :
    sqir_mult_input_F_qstart bits q_start m acc 1 = false := by
  unfold sqir_mult_input_F_qstart
  rw [if_pos (by omega : (1 : Nat) < q_start + 2 * bits + 1)]
  unfold cuccaro_input_F
  rw [if_pos h_lt]

/-- q_start-parametric prefix gate.  Applies
`sqir_modmult_step_gate_qstart` for `j = 0, 1, ..., k - 1` in order.
Port of `sqir_modmult_prefix_gate` (line 228). -/
def sqir_modmult_prefix_gate_qstart
    (bits q_start N a flagPos : Nat) : Nat → Gate
  | 0       => Gate.I
  | k + 1   => seq (sqir_modmult_prefix_gate_qstart bits q_start N a flagPos k)
                   (sqir_modmult_step_gate_qstart bits q_start N a k flagPos)

/-- q_start-parametric prefix gate at 0 windows is the identity. -/
theorem sqir_modmult_prefix_gate_qstart_zero_eq_I
    (bits q_start N a flagPos : Nat) :
    sqir_modmult_prefix_gate_qstart bits q_start N a flagPos 0 = Gate.I := rfl

/-- q_start-parametric prefix gate at `k + 1` windows. -/
theorem sqir_modmult_prefix_gate_qstart_succ_eq
    (bits q_start N a flagPos k : Nat) :
    sqir_modmult_prefix_gate_qstart bits q_start N a flagPos (k + 1)
      = seq (sqir_modmult_prefix_gate_qstart bits q_start N a flagPos k)
            (sqir_modmult_step_gate_qstart bits q_start N a k flagPos) := rfl

/-- q_start-parametric full multiplier gate.  Process all `bits`
multiplier bits.  Port of `sqir_modmult_const_gate` (line 242). -/
def sqir_modmult_const_gate_qstart (bits q_start N a flagPos : Nat) : Gate :=
  sqir_modmult_prefix_gate_qstart bits q_start N a flagPos bits

/-! ## R7d^xxix-L-3.15e.2 — q_start-parametric step-gate position
       helpers (above-layout / flag0 / carry-in restored).

Three position-level helpers needed by the eventual
`sqir_modmult_step_state_eq_qstart` proof.  The above-layout and
flag0 cases route through a shared `_step_at_untouched_pos_qstart`
helper; the carry-in case routes through the
`sqir_style_controlledModAddConst_gate` carry-in chain. -/

/-- q_start-parametric: step gate doesn't touch positions outside
its support.  At any `q` outside the workspace, distinct from
`flagPos` and the j-th multiplier control position, the gate's
output equals the input's value.  Port of
`sqir_modmult_step_at_untouched_pos` (line 1712). -/
private theorem sqir_modmult_step_at_untouched_pos_qstart
    (bits q_start N a j flagPos m acc q : Nat) (hj : j < bits)
    (h_input : sqir_mult_input_F_qstart bits q_start m acc q = false)
    (h_q_out : q < q_start ∨ q_start + 2 * bits + 1 ≤ q)
    (h_q_ne_flag : q ≠ flagPos)
    (h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx_qstart bits q_start j) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc) q = false := by
  have h_in_eq : update (sqir_mult_input_F_qstart bits q_start m acc) q false
                = sqir_mult_input_F_qstart bits q_start m acc := by
    rw [show (false : Bool) = sqir_mult_input_F_qstart bits q_start m acc q from h_input.symm]
    exact update_self _ q
  unfold sqir_modmult_step_gate_qstart
  have h_commute := sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart
    bits q_start N ((a * 2^j) % N)
    (sqir_mult_control_idx_qstart bits q_start j) flagPos q false
    (sqir_mult_input_F_qstart bits q_start m acc)
    h_q_out h_q_ne_flag h_q_ne_ctrl_j
  rw [h_in_eq] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [update_eq] at h_at_q
  exact h_at_q

/-- q_start-parametric: step gate's output at flag-0 position is
`false`.  Port of `sqir_modmult_step_flag0_false` (line 1734). -/
theorem sqir_modmult_step_flag0_false_qstart
    (bits q_start N a j flagPos m acc : Nat) (hbits : 1 ≤ bits) (hj : j < bits)
    (h_qstart_ge_2 : 2 ≤ q_start)
    (h_flag_ne_0 : (0 : Nat) ≠ flagPos) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc) 0 = false := by
  apply sqir_modmult_step_at_untouched_pos_qstart bits q_start N a j flagPos m acc 0 hj
  · exact sqir_mult_input_flag_0_false_qstart bits q_start m acc (by omega)
  · exact Or.inl (by omega)
  · exact h_flag_ne_0
  · have h := sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start j
    intro h_eq; unfold sqir_mult_control_idx_qstart at h_eq; omega

/-- q_start-parametric: step gate's output above the multiplier
register (for `q ≥ q_start + 2 * bits + 1 + bits`) is `false`.  Port
of `sqir_modmult_step_above_layout_false` (line 1747). -/
theorem sqir_modmult_step_above_layout_false_qstart
    (bits q_start N a j flagPos m acc q : Nat) (hbits : 1 ≤ bits) (hj : j < bits)
    (hq : q ≥ q_start + 2 * bits + 1 + bits)
    (h_flag_lt_qstart : flagPos < q_start) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc) q = false := by
  apply sqir_modmult_step_at_untouched_pos_qstart bits q_start N a j flagPos m acc q hj
  · unfold sqir_mult_input_F_qstart
    rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1)]
    rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1 + bits)]
  · exact Or.inr (by omega)
  · intro heq; omega
  · intro h_eq
    have h := sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start j
    unfold sqir_mult_control_idx_qstart at h_eq
    omega

/-! ### Carry-in restored chain (port of CuccaroSQIRDirtyFlag.lean
clean-candidate carry-in + this file's controlled wrapper). -/

/-- q_start-parametric: the uncontrolled clean modular-add candidate
restores the carry-in to `false`.  Port of
`sqir_style_modAddConst_clean_candidate_carry_in_restored`
(line 1637). -/
theorem sqir_style_modAddConst_clean_candidate_carry_in_restored_qstart
    (bits q_start N c x flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_modAddConst_clean_candidate bits q_start N c flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos false) q_start = false := by
  show Gate.applyNat
      (seq (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
        (seq (sqir_style_compareConst_candidate bits q_start c flagPos) (Gate.X flagPos)))
      (update (cuccaro_input_F q_start false 0 x) flagPos false) q_start = false
  simp only [Gate.applyNat_seq, Gate.applyNat_X]
  have h_qs_ne_flag : (q_start : Nat) ≠ flagPos := by
    rcases hflag_out with hl | hr
    · omega
    · omega
  rw [update_neq _ _ _ _ h_qs_ne_flag]
  have h_qs_in_ws_lo : q_start ≤ q_start := le_refl _
  have h_qs_in_ws_hi : q_start < q_start + 2 * bits + 1 := by omega
  rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits q_start c flagPos
        _ hflag_out q_start h_qs_in_ws_lo h_qs_in_ws_hi]
  have h_flag_distinct : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2 := by
    intros j _ heq
    rcases hflag_out with hl | hr
    · omega
    · omega
  exact sqir_style_modAddConst_dirtyFlag_carry_in_restored_general bits q_start N c x flagPos
    hbits hN_pos hN hN2 hx hc h_flag_distinct hflag_out

/-- q_start-parametric: controlled candidate carry-in restored.
Dispatches on `control`.  Port of
`sqir_style_controlledModAddConst_candidate_carry_in_restored`
(line 1657). -/
theorem sqir_style_controlledModAddConst_candidate_carry_in_restored_qstart
    (bits q_start N c x controlIdx flagPos : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
        (update (cuccaro_input_F q_start false 0 x) controlIdx control) q_start = false := by
  have h_ctrl_ne_qs : controlIdx ≠ q_start := by
    rcases hcontrol_out with h | h
    · omega
    · omega
  cases control with
  | false =>
    rw [sqir_style_controlledModAddConst_candidate_control_false_state_eq_qstart
          bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
          hcontrol_out hflag_out hcontrol_ne_flag]
    rw [update_neq _ _ _ _ (Ne.symm h_ctrl_ne_qs)]
    exact cuccaro_input_F_at_c_in q_start false 0 x
  | true =>
    rw [sqir_style_controlledModAddConst_candidate_control_true_state_eq_qstart
          bits q_start N c x controlIdx flagPos hbits hN_pos hN hN2 hc_pos hc hx
          hcontrol_out hflag_out hcontrol_ne_flag]
    rw [update_neq _ _ _ _ (Ne.symm h_ctrl_ne_qs)]
    exact sqir_style_modAddConst_clean_candidate_carry_in_restored_qstart bits q_start N c x
      flagPos hbits hN_pos hN hN2 hc hx hflag_out

/-- q_start-parametric: wrapper-level controlled mod-add carry-in
restored.  Adds the `c = 0` identity case.  Port of
`sqir_style_controlledModAddConst_gate_carry_in_restored` (line 1684). -/
theorem sqir_style_controlledModAddConst_gate_carry_in_restored_qstart
    (bits q_start N c x controlIdx flagPos : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hcontrol_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
        (update (cuccaro_input_F q_start false 0 x) controlIdx control) q_start = false := by
  unfold sqir_style_controlledModAddConst_gate
  have h_ctrl_ne_qs : controlIdx ≠ q_start := by
    rcases hcontrol_out with h | h
    · omega
    · omega
  by_cases hc0 : c = 0
  · simp only [hc0, if_true, Gate.applyNat_I]
    rw [update_neq _ _ _ _ (Ne.symm h_ctrl_ne_qs)]
    exact cuccaro_input_F_at_c_in q_start false 0 x
  · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc0
    simp only [hc0, if_false]
    exact sqir_style_controlledModAddConst_candidate_carry_in_restored_qstart bits q_start N c x
      controlIdx flagPos control hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hflag_out
      hcontrol_ne_flag

/-! ### Function-level commute of step gate with install (q_start). -/

/-- q_start-parametric: the controlled mod-add wrapper gate commutes
with the entire install stack.  Port of
`sqir_style_controlledModAddConst_gate_commute_install` (line 1362). -/
theorem sqir_style_controlledModAddConst_gate_commute_install_qstart
    (bits q_start m j N c flagPos num_bits : Nat) (f : Nat → Bool)
    (h_flag_lt_qstart : flagPos < q_start) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
        (sqir_mult_control_idx_qstart bits q_start j) flagPos)
      (install_mult_bits_skip_j_qstart bits q_start m j num_bits f)
      = install_mult_bits_skip_j_qstart bits q_start m j num_bits
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos) f) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    by_cases h_kj : k = j
    · have h_lhs_eq : install_mult_bits_skip_j_qstart bits q_start m j (k+1) f
                    = install_mult_bits_skip_j_qstart bits q_start m j k f := by
        show (if k = j then install_mult_bits_skip_j_qstart bits q_start m j k f
              else update (install_mult_bits_skip_j_qstart bits q_start m j k f)
                          (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k))
            = install_mult_bits_skip_j_qstart bits q_start m j k f
        rw [if_pos h_kj]
      have h_rhs_eq : install_mult_bits_skip_j_qstart bits q_start m j (k+1)
                      (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
                        (sqir_mult_control_idx_qstart bits q_start j) flagPos) f)
                    = install_mult_bits_skip_j_qstart bits q_start m j k
                      (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
                        (sqir_mult_control_idx_qstart bits q_start j) flagPos) f) := by
        show (if k = j
              then install_mult_bits_skip_j_qstart bits q_start m j k
                    (Gate.applyNat _ f)
              else update (install_mult_bits_skip_j_qstart bits q_start m j k
                            (Gate.applyNat _ f))
                          (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k))
            = install_mult_bits_skip_j_qstart bits q_start m j k
              (Gate.applyNat _ f)
        rw [if_pos h_kj]
      rw [h_lhs_eq, h_rhs_eq]
      exact ih
    · have h_out : sqir_mult_control_idx_qstart bits q_start k < q_start
            ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start k :=
        sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start k
      have h_ne_flag : sqir_mult_control_idx_qstart bits q_start k ≠ flagPos :=
        sqir_mult_control_idx_ne_flag_qstart bits q_start k flagPos h_flag_lt_qstart
      have h_ne_ctrl_j :
          sqir_mult_control_idx_qstart bits q_start k
            ≠ sqir_mult_control_idx_qstart bits q_start j :=
        fun heq => h_kj (sqir_mult_control_idx_injective_qstart bits q_start k j heq)
      have h_lhs_eq : install_mult_bits_skip_j_qstart bits q_start m j (k+1) f
                    = update (install_mult_bits_skip_j_qstart bits q_start m j k f)
                        (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k) := by
        show (if k = j then install_mult_bits_skip_j_qstart bits q_start m j k f
              else update (install_mult_bits_skip_j_qstart bits q_start m j k f)
                          (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k))
            = update (install_mult_bits_skip_j_qstart bits q_start m j k f)
                (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k)
        rw [if_neg h_kj]
      have h_rhs_eq : install_mult_bits_skip_j_qstart bits q_start m j (k+1)
                      (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
                        (sqir_mult_control_idx_qstart bits q_start j) flagPos) f)
                    = update (install_mult_bits_skip_j_qstart bits q_start m j k
                        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits q_start N c
                          (sqir_mult_control_idx_qstart bits q_start j) flagPos) f))
                        (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k) := by
        show (if k = j
              then install_mult_bits_skip_j_qstart bits q_start m j k (Gate.applyNat _ f)
              else update (install_mult_bits_skip_j_qstart bits q_start m j k (Gate.applyNat _ f))
                          (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k))
            = update (install_mult_bits_skip_j_qstart bits q_start m j k (Gate.applyNat _ f))
                (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k)
        rw [if_neg h_kj]
      rw [h_lhs_eq, h_rhs_eq]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun_qstart bits q_start N c
            (sqir_mult_control_idx_qstart bits q_start j) flagPos
            (sqir_mult_control_idx_qstart bits q_start k) (m.testBit k)
            (install_mult_bits_skip_j_qstart bits q_start m j k f)
            h_out h_ne_flag h_ne_ctrl_j]
      rw [ih]

/-- q_start-parametric: step gate's output at the carry-in position
(`q_start`) is `false`.  Port of `sqir_modmult_step_carry_in_restored`
(line 1764). -/
theorem sqir_modmult_step_carry_in_restored_qstart
    (bits q_start N a j flagPos m acc : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N)
    (h_flag_lt_qstart : flagPos < q_start) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc) q_start = false := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  rw [sqir_mult_input_F_eq_install_with_j_qstart bits q_start m acc j hj hacc_lt]
  unfold sqir_modmult_step_gate_qstart
  rw [sqir_style_controlledModAddConst_gate_commute_install_qstart bits q_start m j N
        ((a * 2^j) % N) flagPos bits _ h_flag_lt_qstart]
  rw [install_mult_bits_skip_j_at_workspace_eq_qstart bits q_start m j bits _ q_start (by omega)]
  have h_ctrl_out :
      sqir_mult_control_idx_qstart bits q_start j < q_start
        ∨ q_start + 2 * bits + 1 ≤ sqir_mult_control_idx_qstart bits q_start j :=
    sqir_mult_control_idx_outside_modadd_workspace_form_qstart bits q_start j
  have h_flag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos :=
    Or.inl h_flag_lt_qstart
  have h_ctrl_ne_flag : sqir_mult_control_idx_qstart bits q_start j ≠ flagPos :=
    sqir_mult_control_idx_ne_flag_qstart bits q_start j flagPos h_flag_lt_qstart
  exact sqir_style_controlledModAddConst_gate_carry_in_restored_qstart bits q_start N
    ((a * 2^j) % N) acc (sqir_mult_control_idx_qstart bits q_start j) flagPos (m.testBit j)
    hbits hN_pos hN hN2 (Nat.mod_lt _ hN_pos) hacc h_ctrl_out h_flag_out h_ctrl_ne_flag

/-! ## Tick 74 — Deliverable F: Prefix invariant starter. -/

/-- **Prefix invariant — base case (`k = 0`).**

The 0-step prefix gate is identity, so the target register is just the
encoded `acc = 0`. -/
theorem sqir_modmult_prefix_target_decode_zero
    (bits N a m : Nat) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_prefix_gate bits N a 0) (sqir_mult_input_F bits m 0))
      = sqir_modmult_acc_spec N a m 0 := by
  rw [sqir_modmult_acc_spec_zero, sqir_modmult_prefix_gate]
  rw [Gate.applyNat_I]
  exact sqir_mult_input_target_decode bits m 0 (Nat.two_pow_pos bits)

/-! ## Tick 75 — Deliverable A: All control bits preserved by one step. -/

/-- **Function-level commute of step gate with install.**

The controlled mod-add wrapper gate commutes with the entire install
stack, because each install update is at `controlIdx_k` for `k ≠ j`
(by construction of `install_mult_bits_skip_j`), which is outside the
gate's support. -/
theorem sqir_style_controlledModAddConst_gate_commute_install
    (bits m j N c num_bits : Nat) (f : Nat → Bool) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1)
      (install_mult_bits_skip_j bits m j num_bits f)
      = install_mult_bits_skip_j bits m j num_bits
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1) f) := by
  induction num_bits with
  | zero => rfl
  | succ k ih =>
    by_cases h_kj : k = j
    · have h_lhs_eq : install_mult_bits_skip_j bits m j (k+1) f
                    = install_mult_bits_skip_j bits m j k f := by
        show (if k = j then install_mult_bits_skip_j bits m j k f
              else update (install_mult_bits_skip_j bits m j k f)
                          (sqir_mult_control_idx bits k) (m.testBit k))
            = install_mult_bits_skip_j bits m j k f
        rw [if_pos h_kj]
      have h_rhs_eq : install_mult_bits_skip_j bits m j (k+1)
                      (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
                        (sqir_mult_control_idx bits j) 1) f)
                    = install_mult_bits_skip_j bits m j k
                      (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
                        (sqir_mult_control_idx bits j) 1) f) := by
        show (if k = j
              then install_mult_bits_skip_j bits m j k
                    (Gate.applyNat _ f)
              else update (install_mult_bits_skip_j bits m j k
                            (Gate.applyNat _ f))
                          (sqir_mult_control_idx bits k) (m.testBit k))
            = install_mult_bits_skip_j bits m j k
              (Gate.applyNat _ f)
        rw [if_pos h_kj]
      rw [h_lhs_eq, h_rhs_eq]
      exact ih
    · have h_out : sqir_mult_control_idx bits k < 2
            ∨ 2 + (2 * bits + 1) ≤ sqir_mult_control_idx bits k := by
        right; unfold sqir_mult_control_idx; omega
      have h_ne_flag : sqir_mult_control_idx bits k ≠ 1 := by
        unfold sqir_mult_control_idx; omega
      have h_ne_ctrl_j :
          sqir_mult_control_idx bits k ≠ sqir_mult_control_idx bits j :=
        fun heq => h_kj (sqir_mult_control_idx_injective bits k j heq)
      have h_lhs_eq : install_mult_bits_skip_j bits m j (k+1) f
                    = update (install_mult_bits_skip_j bits m j k f)
                        (sqir_mult_control_idx bits k) (m.testBit k) := by
        show (if k = j then install_mult_bits_skip_j bits m j k f
              else update (install_mult_bits_skip_j bits m j k f)
                          (sqir_mult_control_idx bits k) (m.testBit k))
            = update (install_mult_bits_skip_j bits m j k f)
                (sqir_mult_control_idx bits k) (m.testBit k)
        rw [if_neg h_kj]
      have h_rhs_eq : install_mult_bits_skip_j bits m j (k+1)
                      (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
                        (sqir_mult_control_idx bits j) 1) f)
                    = update (install_mult_bits_skip_j bits m j k
                        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
                          (sqir_mult_control_idx bits j) 1) f))
                        (sqir_mult_control_idx bits k) (m.testBit k) := by
        show (if k = j
              then install_mult_bits_skip_j bits m j k (Gate.applyNat _ f)
              else update (install_mult_bits_skip_j bits m j k (Gate.applyNat _ f))
                          (sqir_mult_control_idx bits k) (m.testBit k))
            = update (install_mult_bits_skip_j bits m j k (Gate.applyNat _ f))
                (sqir_mult_control_idx bits k) (m.testBit k)
        rw [if_neg h_kj]
      rw [h_lhs_eq, h_rhs_eq]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N c
            (sqir_mult_control_idx bits j) (sqir_mult_control_idx bits k)
            (m.testBit k) _ h_out h_ne_flag h_ne_ctrl_j]
      rw [ih]

/-- **Deliverable A — All control bits preserved by one step.**

The one-step gate `sqir_modmult_step_gate bits N a j` preserves every
multiplier control bit `k < bits` as `m.testBit k`.  This generalizes
Tick 74's Deliverable D from `k = j` to all `k < bits`. -/
theorem sqir_modmult_step_preserves_all_control_bits
    (bits N a m acc j k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hj : j < bits) (hk : k < bits) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) (sqir_mult_control_idx bits k)
      = m.testBit k := by
  by_cases h_kj : k = j
  · rw [h_kj]
    have ⟨_, _, _, h_ctrl⟩ :=
      sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc
    exact h_ctrl
  · have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
    rw [sqir_mult_input_F_eq_install_with_j bits m acc j hj hacc_lt]
    unfold sqir_modmult_step_gate
    rw [sqir_style_controlledModAddConst_gate_commute_install bits m j N
          ((a * 2^j) % N) bits _]
    exact install_mult_bits_skip_j_at_mult_k_eq bits m j bits k _ hk h_kj

/-! ## Tick 75 — Converse target/read-value extraction (utility). -/

/-- **Converse to `cuccaro_target_val_eq_sum_when_bits_match`.**

For `S < 2^bits`, if `cuccaro_target_val bits q_start f = S`, then each
target bit `i < bits` matches `S.testBit i`.  By uniqueness of binary
representation.  Useful for deducing per-bit info from a target_val
equality.

This is a forward-looking utility lemma; in Tick 75 it is not yet
consumed by `sqir_modmult_step_state_eq` (deferred to Tick 76). -/
theorem cuccaro_target_val_eq_implies_bits_match
    (bits q_start S : Nat) (f : Nat → Bool)
    (hS : S < 2^bits) (h : cuccaro_target_val bits q_start f = S) :
    ∀ i, i < bits → f (q_start + 2 * i + 1) = S.testBit i := by
  induction bits generalizing S with
  | zero => intros i hi; omega
  | succ n ih =>
    intro i hi
    have hTn_lt : cuccaro_target_val n q_start f < 2^n :=
      cuccaro_target_val_lt n q_start f
    have h_unfold : cuccaro_target_val n q_start f
                  + (if f (q_start + 2 * n + 1) then 2^n else 0) = S := h
    by_cases hi_eq : i = n
    · subst hi_eq
      by_cases hvn : f (q_start + 2 * i + 1) = true
      · rw [if_pos hvn] at h_unfold
        rw [hvn]
        have hS_eq : S = 2^i + cuccaro_target_val i q_start f := by omega
        rw [hS_eq, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hTn_lt]
        rfl
      · have hvn_f : f (q_start + 2 * i + 1) = false := by
          cases hh : f (q_start + 2 * i + 1)
          · rfl
          · exact absurd hh hvn
        rw [if_neg hvn] at h_unfold
        rw [hvn_f]
        have h_eq : S = cuccaro_target_val i q_start f := by omega
        rw [h_eq]
        exact (Nat.testBit_lt_two_pow hTn_lt).symm
    · have hi_lt_n : i < n := by omega
      have h_ih : f (q_start + 2 * i + 1) = (cuccaro_target_val n q_start f).testBit i :=
        ih (cuccaro_target_val n q_start f) hTn_lt rfl i hi_lt_n
      rw [h_ih]
      by_cases hvn : f (q_start + 2 * n + 1) = true
      · rw [if_pos hvn] at h_unfold
        have hS_eq : S = 2^n + cuccaro_target_val n q_start f := by omega
        rw [hS_eq, Nat.testBit_two_pow_add_gt hi_lt_n]
      · rw [if_neg hvn] at h_unfold
        have h_eq : S = cuccaro_target_val n q_start f := by omega
        rw [h_eq]

/-- **Converse to `cuccaro_read_val_eq_sum_when_bits_match`.** -/
theorem cuccaro_read_val_eq_implies_bits_match
    (bits q_start S : Nat) (f : Nat → Bool)
    (hS : S < 2^bits) (h : cuccaro_read_val bits q_start f = S) :
    ∀ i, i < bits → f (q_start + 2 * i + 2) = S.testBit i := by
  induction bits generalizing S with
  | zero => intros i hi; omega
  | succ n ih =>
    intro i hi
    have hTn_lt : cuccaro_read_val n q_start f < 2^n :=
      cuccaro_read_val_lt n q_start f
    have h_unfold : cuccaro_read_val n q_start f
                  + (if f (q_start + 2 * n + 2) then 2^n else 0) = S := h
    by_cases hi_eq : i = n
    · subst hi_eq
      by_cases hvn : f (q_start + 2 * i + 2) = true
      · rw [if_pos hvn] at h_unfold
        rw [hvn]
        have hS_eq : S = 2^i + cuccaro_read_val i q_start f := by omega
        rw [hS_eq, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hTn_lt]
        rfl
      · have hvn_f : f (q_start + 2 * i + 2) = false := by
          cases hh : f (q_start + 2 * i + 2)
          · rfl
          · exact absurd hh hvn
        rw [if_neg hvn] at h_unfold
        rw [hvn_f]
        have h_eq : S = cuccaro_read_val i q_start f := by omega
        rw [h_eq]
        exact (Nat.testBit_lt_two_pow hTn_lt).symm
    · have hi_lt_n : i < n := by omega
      have h_ih : f (q_start + 2 * i + 2) = (cuccaro_read_val n q_start f).testBit i :=
        ih (cuccaro_read_val n q_start f) hTn_lt rfl i hi_lt_n
      rw [h_ih]
      by_cases hvn : f (q_start + 2 * n + 2) = true
      · rw [if_pos hvn] at h_unfold
        have hS_eq : S = 2^n + cuccaro_read_val n q_start f := by omega
        rw [hS_eq, Nat.testBit_two_pow_add_gt hi_lt_n]
      · rw [if_neg hvn] at h_unfold
        have h_eq : S = cuccaro_read_val n q_start f := by omega
        rw [h_eq]

/-! ## Tick 75 — Deliverable B: One-step state-normal theorem. -/

/-- **Deliverable B — One-step state-normal theorem.**

Combines Tick 74's target decode + Tick 74 workspace preservation +
Deliverable A's all-control-bits preservation into a unified finite-
state characterization of the step gate's output. -/
theorem sqir_modmult_step_state_normal
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    let acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc)) = acc'
    ∧ cuccaro_read_val bits 2
        (Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc)) = 0
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) 1 = false
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) (2 + 2 * bits) = false
    ∧ ∀ k, k < bits →
        Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) (sqir_mult_control_idx bits k)
          = m.testBit k := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact sqir_modmult_step_target_decode bits N a j m acc hbits hN_pos hN hN2 hj hacc
  · have ⟨h_rd, _, _, _⟩ :=
      sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc
    exact h_rd
  · have ⟨_, _, h_fl, _⟩ :=
      sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc
    exact h_fl
  · have ⟨_, h_tc, _, _⟩ :=
      sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc
    exact h_tc
  · intro k hk
    exact sqir_modmult_step_preserves_all_control_bits bits N a m acc j k
      hbits hN_pos hN hN2 hacc hj hk

/-! ## Tick 75 — Deliverable E: Accumulator-spec equals modular product. -/

/-- **Strong recurrence form.** -/
private theorem sqir_modmult_acc_spec_eq_mul_mod_pow
    (N a m k : Nat) (hN_pos : 0 < N) :
    sqir_modmult_acc_spec N a m k = (a * (m % 2^k)) % N := by
  induction k with
  | zero =>
    rw [sqir_modmult_acc_spec_zero]
    rw [pow_zero, Nat.mod_one, Nat.mul_zero, Nat.zero_mod]
  | succ n ih =>
    rw [nat_mod_two_pow_succ_eq m n]
    by_cases h_bit : m.testBit n = true
    · rw [sqir_modmult_acc_spec_succ_true N a m n h_bit]
      simp only [h_bit, if_true]
      rw [ih, Nat.mul_add, ← Nat.add_mod]
    · have h_bit_false : m.testBit n = false := by
        cases hh : m.testBit n
        · rfl
        · exact absurd hh h_bit
      rw [sqir_modmult_acc_spec_succ_false N a m n h_bit_false]
      rw [h_bit_false]
      simp only [Bool.false_eq_true, if_false, Nat.add_zero]
      exact ih

/-- **Deliverable E — Accumulator-spec equals modular product.**

For `m < 2^bits`, the bit-by-bit accumulator equals `(a * m) % N`. -/
theorem sqir_modmult_acc_spec_eq_mul_mod
    (bits N a m : Nat) (hN_pos : 0 < N) (hm : m < 2^bits) :
    sqir_modmult_acc_spec N a m bits = (a * m) % N := by
  rw [sqir_modmult_acc_spec_eq_mul_mod_pow N a m bits hN_pos]
  rw [Nat.mod_eq_of_lt hm]

/-! ## Tick 76 — Carry-in restoration chain. -/

/-- **Clean candidate carry-in (`q_start = 2`) restored to `false`.**

Chains through `dirtyFlag → compareConst c → X(1)`:
- `dirtyFlag` restores carry-in via `dirtyFlag_carry_in_restored_general`.
- `compareConst c` preserves all workspace positions via
  `compareConst_candidate_workspace_restored_at_general`.
- `X(1)` doesn't touch position 2 (since 2 ≠ 1). -/
theorem sqir_style_modAddConst_clean_candidate_carry_in_restored
    (bits N c x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N) :
    Gate.applyNat (sqir_style_modAddConst_clean_candidate bits 2 N c 1)
        (update (cuccaro_input_F 2 false 0 x) 1 false) 2 = false := by
  show Gate.applyNat
      (seq (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
        (seq (sqir_style_compareConst_candidate bits 2 c 1) (Gate.X 1)))
      (update (cuccaro_input_F 2 false 0 x) 1 false) 2 = false
  simp only [Gate.applyNat_seq, Gate.applyNat_X]
  rw [update_neq _ _ _ _ (by decide : (2 : Nat) ≠ 1)]
  rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 c 1
        _ (Or.inl (by omega)) 2 (by omega) (by omega)]
  exact sqir_style_modAddConst_dirtyFlag_carry_in_restored_general bits 2 N c x 1
    hbits hN_pos hN hN2 hx hc (fun j _ => by omega) (Or.inl (by omega))

/-- **Controlled candidate carry-in restored.** Dispatches on `control`:
- `control = false`: identity (via `control_false_state_eq`).
- `control = true`: chains through `clean_candidate_carry_in_restored`. -/
theorem sqir_style_controlledModAddConst_candidate_carry_in_restored
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.applyNat (sqir_style_controlledModAddConst_candidate bits 2 N c controlIdx 1)
        (update (cuccaro_input_F 2 false 0 x) controlIdx control) 2 = false := by
  have h_ctrl_ne_2 : controlIdx ≠ 2 := by
    rcases hcontrol_out with h | h
    · omega
    · omega
  cases control with
  | false =>
    rw [sqir_style_controlledModAddConst_candidate_control_false_state_eq bits N c x controlIdx
          hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag]
    rw [update_neq _ _ _ _ (Ne.symm h_ctrl_ne_2)]
    exact cuccaro_input_F_at_c_in 2 false 0 x
  | true =>
    rw [sqir_style_controlledModAddConst_candidate_control_true_state_eq bits N c x controlIdx
          hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag]
    rw [update_neq _ _ _ _ (Ne.symm h_ctrl_ne_2)]
    exact sqir_style_modAddConst_clean_candidate_carry_in_restored bits N c x
      hbits hN_pos hN hN2 hc hx

/-- **Wrapper-level controlled mod-add carry-in restored.** Adds the
`c = 0` identity case to the candidate version. -/
theorem sqir_style_controlledModAddConst_gate_carry_in_restored
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
        (update (cuccaro_input_F 2 false 0 x) controlIdx control) 2 = false := by
  unfold sqir_style_controlledModAddConst_gate
  by_cases hc0 : c = 0
  · simp only [hc0, if_true, Gate.applyNat_I]
    have h_ctrl_ne_2 : controlIdx ≠ 2 := by
      rcases hcontrol_out with h | h
      · omega
      · omega
    rw [update_neq _ _ _ _ (Ne.symm h_ctrl_ne_2)]
    exact cuccaro_input_F_at_c_in 2 false 0 x
  · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc0
    simp only [hc0, if_false]
    exact sqir_style_controlledModAddConst_candidate_carry_in_restored bits N c x controlIdx control
      hbits hN_pos hN hN2 hc_pos hc hx hcontrol_out hcontrol_ne_flag

/-! ## Tick 76 — Step gate position-wise facts. -/

/-- **Generic helper — step gate doesn't touch positions outside its
support.**  At any `q` outside workspace, distinct from flag and
controlIdx_j, the gate's output equals the input's value (via
commute + update_self). -/
private theorem sqir_modmult_step_at_untouched_pos
    (bits N a j m acc q : Nat) (hj : j < bits)
    (h_input : sqir_mult_input_F bits m acc q = false)
    (h_q_out : q < 2 ∨ 2 + (2 * bits + 1) ≤ q)
    (h_q_ne_flag : q ≠ 1)
    (h_q_ne_ctrl_j : q ≠ sqir_mult_control_idx bits j) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) q = false := by
  have h_in_eq : update (sqir_mult_input_F bits m acc) q false
                = sqir_mult_input_F bits m acc := by
    rw [show (false : Bool) = sqir_mult_input_F bits m acc q from h_input.symm]
    exact update_self _ q
  have h_commute := sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
    ((a * 2^j) % N) (sqir_mult_control_idx bits j) q false (sqir_mult_input_F bits m acc)
    h_q_out h_q_ne_flag h_q_ne_ctrl_j
  -- h_commute : applyNat (controlled gate) (update input q false) = update (applyNat (controlled gate) input) q false
  rw [h_in_eq] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [update_eq] at h_at_q
  exact h_at_q

/-- **Step gate's output at flag bit 0 is `false`.** -/
theorem sqir_modmult_step_flag0_false
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits) (hj : j < bits) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) 0 = false := by
  apply sqir_modmult_step_at_untouched_pos bits N a j m acc 0 hj
  · exact sqir_mult_input_flag_0_false bits m acc
  · exact Or.inl (by omega)
  · omega
  · have h := sqir_mult_control_idx_outside_modadd_workspace_form bits j
    intro h_eq; unfold sqir_mult_control_idx at h_eq; omega

/-- **Step gate's output above the multiplier register is `false`.**
For `q ≥ 2 + 2 * bits + 1 + bits`. -/
theorem sqir_modmult_step_above_layout_false
    (bits N a j m acc q : Nat) (hbits : 1 ≤ bits) (hj : j < bits)
    (hq : q ≥ 2 + 2 * bits + 1 + bits) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) q = false := by
  apply sqir_modmult_step_at_untouched_pos bits N a j m acc q hj
  · unfold sqir_mult_input_F
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]
  · exact Or.inr (by omega)
  · omega
  · intro h_eq
    have h := sqir_mult_control_idx_outside_modadd_workspace_form bits j
    unfold sqir_mult_control_idx at h_eq
    omega

/-- **Step gate's output at carry-in (position 2) is `false`.** -/
theorem sqir_modmult_step_carry_in_restored
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) 2 = false := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  rw [sqir_mult_input_F_eq_install_with_j bits m acc j hj hacc_lt]
  unfold sqir_modmult_step_gate
  rw [sqir_style_controlledModAddConst_gate_commute_install bits m j N
        ((a * 2^j) % N) bits _]
  rw [install_mult_bits_skip_j_at_workspace_eq bits m j bits _ 2 (by omega)]
  exact sqir_style_controlledModAddConst_gate_carry_in_restored bits N
    ((a * 2^j) % N) acc (sqir_mult_control_idx bits j) (m.testBit j)
    hbits hN_pos hN hN2 (Nat.mod_lt _ hN_pos) hacc
    (sqir_mult_control_idx_outside_modadd_workspace_form bits j)
    (sqir_mult_control_idx_ne_flag bits j)

/-- **Step gate's output at target bit `i` equals `acc'.testBit i`.**

Uses the per-bit converse `cuccaro_target_val_eq_implies_bits_match`
plus the Tick 74 `sqir_modmult_step_target_decode`. -/
theorem sqir_modmult_step_target_bit
    (bits N a j m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) (2 + 2 * i + 1)
      = (if m.testBit j then (acc + (a * 2^j) % N) % N else acc).testBit i := by
  set acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc with hacc'_def
  have hacc'_lt_N : acc' < N := by
    rw [hacc'_def]
    by_cases h : m.testBit j
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact hacc
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  have h_tgt := sqir_modmult_step_target_decode bits N a j m acc hbits hN_pos hN hN2 hj hacc
  exact cuccaro_target_val_eq_implies_bits_match bits 2 acc' _ hacc'_lt h_tgt i hi

/-- **Step gate's output at read bit `i` is `false`.** -/
theorem sqir_modmult_step_read_bit
    (bits N a j m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) (2 + 2 * i + 2) = false := by
  have h_rd := (sqir_modmult_step_workspace bits N a j m acc hbits hN_pos hN hN2 hj hacc).1
  have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
  have := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd i hi
  rw [this, Nat.zero_testBit]

/-! ## R7d^xxix-L-3.15e.3 — q_start-parametric step-gate position
       helpers (target-bit / read-bit / all-control-bits preserved).

The three remaining per-position helpers needed by the eventual
`sqir_modmult_step_state_eq_qstart` proof.  Each is a thin port of
its hard-coded counterpart, consuming previously-closed L-3.15c/d/e
infrastructure plus the q_start-parametric decoders
`cuccaro_target_val_eq_implies_bits_match` and
`cuccaro_read_val_eq_implies_bits_match` (already q_start-parametric
above in this file). -/

/-- q_start-parametric: step gate's output at target/b-register
position `q_start + 2 * i + 1` decodes the i-th bit of the advanced
accumulator.  Port of `sqir_modmult_step_target_bit` (line 2063). -/
theorem sqir_modmult_step_target_bit_qstart
    (bits q_start N a j flagPos m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc) (q_start + 2 * i + 1)
      = (if m.testBit j then (acc + (a * 2^j) % N) % N else acc).testBit i := by
  set acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc with hacc'_def
  have hacc'_lt_N : acc' < N := by
    rw [hacc'_def]
    by_cases h : m.testBit j
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact hacc
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  have h_tgt := sqir_modmult_step_target_decode_qstart bits q_start N a j m acc dim flagPos
    hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart h_workspace h_dim_covers_mult
  exact cuccaro_target_val_eq_implies_bits_match bits q_start acc' _ hacc'_lt h_tgt i hi

/-- q_start-parametric: step gate's output at read/a-register
position `q_start + 2 * i + 2` is `false`.  Port of
`sqir_modmult_step_read_bit` (line 2161). -/
theorem sqir_modmult_step_read_bit_qstart
    (bits q_start N a j flagPos m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc) (q_start + 2 * i + 2) = false := by
  have h_rd := (sqir_modmult_step_workspace_qstart bits q_start N a j m acc dim flagPos
    hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart h_workspace h_dim_covers_mult).1
  have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
  have := cuccaro_read_val_eq_implies_bits_match bits q_start 0 _ h_zero_lt h_rd i hi
  rw [this, Nat.zero_testBit]

/-- q_start-parametric: step gate preserves every multiplier control
bit `k < bits` as `m.testBit k`.  Port of
`sqir_modmult_step_preserves_all_control_bits` (line 1717). -/
theorem sqir_modmult_step_preserves_all_control_bits_qstart
    (bits q_start N a m acc j k flagPos : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hj : j < bits) (hk : k < bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat (sqir_modmult_step_gate_qstart bits q_start N a j flagPos)
        (sqir_mult_input_F_qstart bits q_start m acc)
          (sqir_mult_control_idx_qstart bits q_start k)
      = m.testBit k := by
  by_cases h_kj : k = j
  · rw [h_kj]
    have ⟨_, _, _, h_ctrl⟩ :=
      sqir_modmult_step_workspace_qstart bits q_start N a j m acc dim flagPos
        hbits hN_pos hN hN2 hj hacc h_flag_lt_qstart h_workspace h_dim_covers_mult
    exact h_ctrl
  · have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
    rw [sqir_mult_input_F_eq_install_with_j_qstart bits q_start m acc j hj hacc_lt]
    unfold sqir_modmult_step_gate_qstart
    rw [sqir_style_controlledModAddConst_gate_commute_install_qstart bits q_start m j N
          ((a * 2^j) % N) flagPos bits _ h_flag_lt_qstart]
    exact install_mult_bits_skip_j_at_mult_k_eq_qstart bits q_start m j bits k _ hk h_kj

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

/-! ## Tick 77 — Task 1: Generalized accumulator multiplier. -/

/-- **Accumulator spec from a starting value.**  Like
`sqir_modmult_acc_spec` but starts at `acc` instead of `0`.
Used by the in-place modular multiplier uncompute step. -/
def sqir_modmult_acc_spec_from (N a m acc : Nat) : Nat → Nat
  | 0     => acc
  | k + 1 =>
    if m.testBit k then
      (sqir_modmult_acc_spec_from N a m acc k + (a * 2 ^ k) % N) % N
    else
      sqir_modmult_acc_spec_from N a m acc k

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
private theorem sqir_modmult_acc_spec_from_eq_mod_pow
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

/-! ### q_start swap-register definitions. -/

/-- q_start-parametric: index of the accumulator (target) bit `i` in
the Cuccaro layout.  Port of `sqir_target_idx`. -/
def sqir_target_idx_qstart (q_start i : Nat) : Nat := q_start + 2 * i + 1

/-- Target index disjoint from multiplier control index. -/
theorem sqir_target_idx_ne_mult_control_idx_qstart
    (bits q_start i j : Nat) (hi : i < bits) :
    sqir_target_idx_qstart q_start i
      ≠ sqir_mult_control_idx_qstart bits q_start j := by
  unfold sqir_target_idx_qstart sqir_mult_control_idx_qstart
  omega

/-- q_start-parametric recursive swap of accumulator bits `[0, k)`
with multiplier bits `[0, k)`.  Port of `sqir_swap_acc_mult_aux`. -/
def sqir_swap_acc_mult_aux_qstart (bits q_start : Nat) : Nat → Gate
  | 0     => Gate.I
  | k + 1 => Gate.seq (sqir_swap_acc_mult_aux_qstart bits q_start k)
                      (qubit_swap (sqir_target_idx_qstart q_start k)
                                  (sqir_mult_control_idx_qstart bits q_start k))

/-- q_start-parametric full SWAP of accumulator with multiplier
register.  Port of `sqir_swap_acc_mult`. -/
def sqir_swap_acc_mult_qstart (bits q_start : Nat) : Gate :=
  sqir_swap_acc_mult_aux_qstart bits q_start bits

/-- Unfold lemma for `sqir_swap_acc_mult_aux_qstart`. -/
theorem sqir_swap_acc_mult_aux_qstart_succ_eq (bits q_start k : Nat) :
    sqir_swap_acc_mult_aux_qstart bits q_start (k + 1)
      = Gate.seq (sqir_swap_acc_mult_aux_qstart bits q_start k)
          (qubit_swap (sqir_target_idx_qstart q_start k)
                      (sqir_mult_control_idx_qstart bits q_start k)) := rfl

/-- Sanity helper: `sqir_target_idx_qstart` value. -/
theorem sqir_target_idx_qstart_value (q_start i : Nat) :
    sqir_target_idx_qstart q_start i = q_start + 2 * i + 1 := rfl

/-! ### q_start in-place modular multiplier candidate. -/

/-- q_start-parametric in-place modular multiplier wrapper.

Implements `x ↦ (a * x) % N` in the multiplier register using:
1. `const_gate_qstart(a)`: compute `(a * x) % N` into accumulator.
2. `swap_acc_mult_qstart`: swap accumulator and multiplier registers.
3. `const_gate_qstart((N - ainv) % N)`: uncompute the old `x` by
   accumulating `(N - ainv) * (a*x) % N ≡ -x (mod N)`, leaving the
   accumulator = 0.

Correctness (sub-tick L-3.15g.2) will require `(a * ainv) % N = 1`.
Port of `sqir_modmult_inplace_candidate`. -/
def sqir_modmult_inplace_candidate_qstart
    (bits q_start N a ainv flagPos : Nat) : Gate :=
  Gate.seq (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
    (Gate.seq (sqir_swap_acc_mult_qstart bits q_start)
              (sqir_modmult_const_gate_qstart bits q_start N
                ((N - ainv) % N) flagPos))

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

/-- q_start port of `sqir_swap_acc_mult_aux_at_target_out_range` (line 3118).
At an accumulator bit `i ≥ k`, swap output = input. -/
theorem sqir_swap_acc_mult_at_target_out_range_qstart
    (bits q_start k i : Nat) (hk : k ≤ bits) (hi_ge : k ≤ i) (hi_bits : i < bits)
    (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux_qstart bits q_start k) f
        (sqir_target_idx_qstart q_start i)
      = f (sqir_target_idx_qstart q_start i) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [sqir_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    have h_i_ne_n : i ≠ n := by omega
    have h_ne_mult_n :
        sqir_target_idx_qstart q_start i
          ≠ sqir_mult_control_idx_qstart bits q_start n :=
      sqir_target_idx_ne_mult_control_idx_qstart bits q_start i n hi_bits
    have h_ne_target_n :
        sqir_target_idx_qstart q_start i ≠ sqir_target_idx_qstart q_start n := by
      unfold sqir_target_idx_qstart; omega
    rw [update_neq _ _ _ _ h_ne_mult_n]
    rw [update_neq _ _ _ _ h_ne_target_n]
    exact ih (by omega) (by omega)

/-- q_start port of `sqir_swap_acc_mult_aux_at_target_in_range` (line 3139).
At an accumulator bit `i < k`, swap output = input at the matched
multiplier position. -/
theorem sqir_swap_acc_mult_at_target_in_range_qstart
    (bits q_start k i : Nat) (hk : k ≤ bits) (hi_k : i < k) (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux_qstart bits q_start k) f
        (sqir_target_idx_qstart q_start i)
      = f (sqir_mult_control_idx_qstart bits q_start i) := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hn_lt : n < bits := by omega
    have hi_bits : i < bits := by omega
    rw [sqir_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    by_cases hi_eq : i = n
    · subst hi_eq
      rw [update_neq _ _ _ _
            (sqir_target_idx_ne_mult_control_idx_qstart bits q_start i i hi_bits)]
      rw [update_eq]
      exact sqir_swap_acc_mult_at_mult_out_range_qstart bits q_start i i
              (by omega) (le_refl _) hi_bits f
    · have h_ne_mult_n :
          sqir_target_idx_qstart q_start i
            ≠ sqir_mult_control_idx_qstart bits q_start n :=
        sqir_target_idx_ne_mult_control_idx_qstart bits q_start i n hi_bits
      have h_ne_target_n :
          sqir_target_idx_qstart q_start i ≠ sqir_target_idx_qstart q_start n := by
        unfold sqir_target_idx_qstart; omega
      rw [update_neq _ _ _ _ h_ne_mult_n]
      rw [update_neq _ _ _ _ h_ne_target_n]
      exact ih (by omega) (by omega)

/-- q_start port of `sqir_swap_acc_mult_aux_at_mult_in_range` (line 3164).
At a multiplier bit `i < k`, swap output = input at matched target. -/
theorem sqir_swap_acc_mult_at_mult_in_range_qstart
    (bits q_start k i : Nat) (hk : k ≤ bits) (hi_k : i < k) (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux_qstart bits q_start k) f
        (sqir_mult_control_idx_qstart bits q_start i)
      = f (sqir_target_idx_qstart q_start i) := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hn_lt : n < bits := by omega
    have hi_bits : i < bits := by omega
    rw [sqir_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    by_cases hi_eq : i = n
    · subst hi_eq
      rw [update_eq]
      exact sqir_swap_acc_mult_at_target_out_range_qstart bits q_start i i
              (by omega) (le_refl _) hi_bits f
    · have h_ne_mult_n :
          sqir_mult_control_idx_qstart bits q_start i
            ≠ sqir_mult_control_idx_qstart bits q_start n := by
        intro heq
        exact hi_eq (sqir_mult_control_idx_injective_qstart bits q_start i n heq)
      have h_ne_target_n :
          sqir_mult_control_idx_qstart bits q_start i
            ≠ sqir_target_idx_qstart q_start n :=
        (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n i hn_lt).symm
      rw [update_neq _ _ _ _ h_ne_mult_n]
      rw [update_neq _ _ _ _ h_ne_target_n]
      exact ih (by omega) (by omega)

/-- q_start port of `sqir_swap_acc_mult_aux_at_other` (line 3189).
At any position outside the swap range, output = input. -/
theorem sqir_swap_acc_mult_at_other_qstart
    (bits q_start k q : Nat) (hk : k ≤ bits) (f : Nat → Bool)
    (h_q_not_target : ∀ i, i < k → q ≠ sqir_target_idx_qstart q_start i)
    (h_q_not_mult : ∀ i, i < k → q ≠ sqir_mult_control_idx_qstart bits q_start i) :
    Gate.applyNat (sqir_swap_acc_mult_aux_qstart bits q_start k) f q = f q := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [sqir_swap_acc_mult_aux_qstart_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _
          (sqir_target_idx_ne_mult_control_idx_qstart bits q_start n n hn_lt)]
    have h_q_ne_target_n : q ≠ sqir_target_idx_qstart q_start n :=
      h_q_not_target n (by omega)
    have h_q_ne_mult_n : q ≠ sqir_mult_control_idx_qstart bits q_start n :=
      h_q_not_mult n (by omega)
    rw [update_neq _ _ _ _ h_q_ne_mult_n]
    rw [update_neq _ _ _ _ h_q_ne_target_n]
    exact ih (by omega)
            (fun i hi => h_q_not_target i (by omega))
            (fun i hi => h_q_not_mult i (by omega))

/-! ### Full swap correctness on `sqir_mult_input_F_qstart`. -/

/-- q_start port of `sqir_swap_acc_mult_apply` (line 3215).  Full SWAP
correctness on `sqir_mult_input_F_qstart`. -/
theorem sqir_swap_acc_mult_apply_qstart
    (bits q_start m acc : Nat) (hbits : 1 ≤ bits)
    (hm : m < 2^bits) (hacc : acc < 2^bits) :
    Gate.applyNat (sqir_swap_acc_mult_qstart bits q_start)
        (sqir_mult_input_F_qstart bits q_start m acc)
      = sqir_mult_input_F_qstart bits q_start acc m := by
  unfold sqir_swap_acc_mult_qstart
  funext q
  by_cases h_target : ∃ i, i < bits ∧ q = sqir_target_idx_qstart q_start i
  · obtain ⟨i, hi, hq_eq⟩ := h_target
    rw [hq_eq]
    rw [sqir_swap_acc_mult_at_target_in_range_qstart bits q_start bits i (le_refl _) hi]
    rw [sqir_mult_input_control_bit_qstart bits q_start m acc i hi]
    show m.testBit i = sqir_mult_input_F_qstart bits q_start acc m
                          (sqir_target_idx_qstart q_start i)
    unfold sqir_mult_input_F_qstart
    rw [sqir_target_idx_qstart_value]
    rw [if_pos (by omega : q_start + 2 * i + 1 < q_start + 2 * bits + 1)]
    exact (cuccaro_input_F_at_b q_start i false 0 m).symm
  · by_cases h_mult : ∃ i, i < bits ∧ q = sqir_mult_control_idx_qstart bits q_start i
    · obtain ⟨i, hi, hq_eq⟩ := h_mult
      rw [hq_eq]
      rw [sqir_swap_acc_mult_at_mult_in_range_qstart bits q_start bits i (le_refl _) hi]
      have h_lhs : sqir_mult_input_F_qstart bits q_start m acc
                     (sqir_target_idx_qstart q_start i) = acc.testBit i := by
        unfold sqir_mult_input_F_qstart sqir_target_idx_qstart
        rw [if_pos (by omega : q_start + 2 * i + 1 < q_start + 2 * bits + 1)]
        exact cuccaro_input_F_at_b q_start i false 0 acc
      rw [h_lhs]
      exact (sqir_mult_input_control_bit_qstart bits q_start acc m i hi).symm
    · have h_not_target : ∀ i, i < bits → q ≠ sqir_target_idx_qstart q_start i := by
        intros i hi heq
        exact h_target ⟨i, hi, heq⟩
      have h_not_mult :
          ∀ i, i < bits → q ≠ sqir_mult_control_idx_qstart bits q_start i := by
        intros i hi heq
        exact h_mult ⟨i, hi, heq⟩
      rw [sqir_swap_acc_mult_at_other_qstart bits q_start bits q (le_refl _) _
            h_not_target h_not_mult]
      by_cases hq_ws : q < q_start + 2 * bits + 1
      · unfold sqir_mult_input_F_qstart
        rw [if_pos hq_ws, if_pos hq_ws]
        unfold cuccaro_input_F
        by_cases hq_below : q < q_start
        · rw [if_pos hq_below, if_pos hq_below]
        · push_neg at hq_below
          rw [if_neg (by omega : ¬ q < q_start),
              if_neg (by omega : ¬ q < q_start)]
          by_cases hq_q_start : q - q_start = 0
          · rw [if_pos hq_q_start, if_pos hq_q_start]
          · rw [if_neg hq_q_start, if_neg hq_q_start]
            by_cases hq_odd : (q - q_start) % 2 = 1
            · rw [if_pos hq_odd, if_pos hq_odd]
              exfalso
              have hi_bound : (q - q_start - 1) / 2 < bits := by omega
              have h_eq : q = sqir_target_idx_qstart q_start
                                ((q - q_start - 1) / 2) := by
                unfold sqir_target_idx_qstart; omega
              exact h_not_target ((q - q_start - 1) / 2) hi_bound h_eq
            · rw [if_neg hq_odd, if_neg hq_odd]
      · push_neg at hq_ws
        unfold sqir_mult_input_F_qstart
        rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1)]
        rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1)]
        by_cases hq_in_mult : q < q_start + 2 * bits + 1 + bits
        · rw [if_pos hq_in_mult, if_pos hq_in_mult]
          exfalso
          set k := q - (q_start + 2 * bits + 1)
          have hk_lt : k < bits := by omega
          have hq_eq : q = sqir_mult_control_idx_qstart bits q_start k := by
            unfold sqir_mult_control_idx_qstart; omega
          exact h_not_mult k hk_lt hq_eq
        · rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1 + bits)]
          rw [if_neg (by omega : ¬ q < q_start + 2 * bits + 1 + bits)]

/-! ## Tick 77 — Task 2: Accumulator↔Multiplier register swap. -/

/-- Index of the accumulator (target) bit `i` in the SQIR layout. -/
def sqir_target_idx (i : Nat) : Nat := 2 + 2 * i + 1

theorem sqir_target_idx_ne_mult_control_idx
    (bits i j : Nat) (hi : i < bits) :
    sqir_target_idx i ≠ sqir_mult_control_idx bits j := by
  unfold sqir_target_idx sqir_mult_control_idx
  omega

/-- Recursive swap of accumulator bits `[0, k)` with multiplier bits `[0, k)`. -/
def sqir_swap_acc_mult_aux (bits : Nat) : Nat → Gate
  | 0     => Gate.I
  | k + 1 => Gate.seq (sqir_swap_acc_mult_aux bits k)
                      (qubit_swap (sqir_target_idx k) (sqir_mult_control_idx bits k))

/-- Full SWAP of accumulator (target) register with multiplier register. -/
def sqir_swap_acc_mult (bits : Nat) : Gate :=
  sqir_swap_acc_mult_aux bits bits

theorem sqir_swap_acc_mult_aux_succ_eq (bits k : Nat) :
    sqir_swap_acc_mult_aux bits (k + 1)
      = Gate.seq (sqir_swap_acc_mult_aux bits k)
          (qubit_swap (sqir_target_idx k) (sqir_mult_control_idx bits k)) := rfl

/-- **WellTyped for `sqir_swap_acc_mult_aux`.** -/
theorem sqir_swap_acc_mult_aux_wellTyped
    (bits k : Nat) (hbits : 1 ≤ bits) (hk : k ≤ bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits) (sqir_swap_acc_mult_aux bits k) := by
  induction k with
  | zero =>
    show 0 < sqir_modmult_rev_anc bits
    unfold sqir_modmult_rev_anc; omega
  | succ n ih =>
    rw [sqir_swap_acc_mult_aux_succ_eq]
    refine ⟨ih (by omega), ?_⟩
    apply qubit_swap_wellTyped
    · unfold sqir_target_idx sqir_modmult_rev_anc; omega
    · exact sqir_mult_control_idx_lt_sqir_dim bits n (by omega)
    · exact sqir_target_idx_ne_mult_control_idx bits n n (by omega)

theorem sqir_swap_acc_mult_wellTyped
    (bits : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits) (sqir_swap_acc_mult bits) :=
  sqir_swap_acc_mult_aux_wellTyped bits bits hbits (le_refl _)

/-! ## Per-position behavior of `sqir_swap_acc_mult_aux`. -/

/-- **At a multiplier bit `i ≥ k`, swap output = input.** -/
theorem sqir_swap_acc_mult_aux_at_mult_out_range
    (bits k i : Nat) (hk : k ≤ bits) (hi_ge : k ≤ i) (hi_bits : i < bits) (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux bits k) f (sqir_mult_control_idx bits i)
      = f (sqir_mult_control_idx bits i) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [sqir_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (sqir_target_idx_ne_mult_control_idx bits n n hn_lt)]
    have h_i_ne_n : i ≠ n := by omega
    have h_ne_mult_n : sqir_mult_control_idx bits i ≠ sqir_mult_control_idx bits n := by
      intro heq
      exact h_i_ne_n (sqir_mult_control_idx_injective bits i n heq)
    have h_ne_target_n : sqir_mult_control_idx bits i ≠ sqir_target_idx n :=
      (sqir_target_idx_ne_mult_control_idx bits n i hn_lt).symm
    rw [update_neq _ _ _ _ h_ne_mult_n]
    rw [update_neq _ _ _ _ h_ne_target_n]
    exact ih (by omega) (by omega)

/-- **At an accumulator bit `i ≥ k`, swap output = input.** -/
theorem sqir_swap_acc_mult_aux_at_target_out_range
    (bits k i : Nat) (hk : k ≤ bits) (hi_ge : k ≤ i) (hi_bits : i < bits) (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux bits k) f (sqir_target_idx i)
      = f (sqir_target_idx i) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [sqir_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (sqir_target_idx_ne_mult_control_idx bits n n hn_lt)]
    have h_i_ne_n : i ≠ n := by omega
    have h_ne_mult_n : sqir_target_idx i ≠ sqir_mult_control_idx bits n :=
      sqir_target_idx_ne_mult_control_idx bits i n hi_bits
    have h_ne_target_n : sqir_target_idx i ≠ sqir_target_idx n := by
      unfold sqir_target_idx; omega
    rw [update_neq _ _ _ _ h_ne_mult_n]
    rw [update_neq _ _ _ _ h_ne_target_n]
    exact ih (by omega) (by omega)

/-- **At an accumulator bit `i < k`, swap output = input at the matched
multiplier position.** -/
theorem sqir_swap_acc_mult_aux_at_target_in_range
    (bits k i : Nat) (hk : k ≤ bits) (hi_k : i < k) (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux bits k) f (sqir_target_idx i)
      = f (sqir_mult_control_idx bits i) := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hn_lt : n < bits := by omega
    have hi_bits : i < bits := by omega
    rw [sqir_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (sqir_target_idx_ne_mult_control_idx bits n n hn_lt)]
    by_cases hi_eq : i = n
    · subst hi_eq
      rw [update_neq _ _ _ _ (sqir_target_idx_ne_mult_control_idx bits i i hi_bits)]
      rw [update_eq]
      exact sqir_swap_acc_mult_aux_at_mult_out_range bits i i (by omega) (le_refl _) hi_bits f
    · have h_ne_mult_n : sqir_target_idx i ≠ sqir_mult_control_idx bits n :=
        sqir_target_idx_ne_mult_control_idx bits i n hi_bits
      have h_ne_target_n : sqir_target_idx i ≠ sqir_target_idx n := by
        unfold sqir_target_idx; omega
      rw [update_neq _ _ _ _ h_ne_mult_n]
      rw [update_neq _ _ _ _ h_ne_target_n]
      exact ih (by omega) (by omega)

/-- **At a multiplier bit `i < k`, swap output = input at matched target.** -/
theorem sqir_swap_acc_mult_aux_at_mult_in_range
    (bits k i : Nat) (hk : k ≤ bits) (hi_k : i < k) (f : Nat → Bool) :
    Gate.applyNat (sqir_swap_acc_mult_aux bits k) f (sqir_mult_control_idx bits i)
      = f (sqir_target_idx i) := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hn_lt : n < bits := by omega
    have hi_bits : i < bits := by omega
    rw [sqir_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (sqir_target_idx_ne_mult_control_idx bits n n hn_lt)]
    by_cases hi_eq : i = n
    · subst hi_eq
      rw [update_eq]
      exact sqir_swap_acc_mult_aux_at_target_out_range bits i i (by omega) (le_refl _) hi_bits f
    · have h_ne_mult_n : sqir_mult_control_idx bits i ≠ sqir_mult_control_idx bits n := by
        intro heq
        exact hi_eq (sqir_mult_control_idx_injective bits i n heq)
      have h_ne_target_n : sqir_mult_control_idx bits i ≠ sqir_target_idx n :=
        (sqir_target_idx_ne_mult_control_idx bits n i hn_lt).symm
      rw [update_neq _ _ _ _ h_ne_mult_n]
      rw [update_neq _ _ _ _ h_ne_target_n]
      exact ih (by omega) (by omega)

/-- **At any position outside the swap range, output = input.** -/
theorem sqir_swap_acc_mult_aux_at_other
    (bits k q : Nat) (hk : k ≤ bits) (f : Nat → Bool)
    (h_q_not_target : ∀ i, i < k → q ≠ sqir_target_idx i)
    (h_q_not_mult : ∀ i, i < k → q ≠ sqir_mult_control_idx bits i) :
    Gate.applyNat (sqir_swap_acc_mult_aux bits k) f q = f q := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn_lt : n < bits := by omega
    rw [sqir_swap_acc_mult_aux_succ_eq, Gate.applyNat_seq]
    rw [qubit_swap_correct _ _ _ (sqir_target_idx_ne_mult_control_idx bits n n hn_lt)]
    have h_q_ne_target_n : q ≠ sqir_target_idx n := h_q_not_target n (by omega)
    have h_q_ne_mult_n : q ≠ sqir_mult_control_idx bits n := h_q_not_mult n (by omega)
    rw [update_neq _ _ _ _ h_q_ne_mult_n]
    rw [update_neq _ _ _ _ h_q_ne_target_n]
    exact ih (by omega)
            (fun i hi => h_q_not_target i (by omega))
            (fun i hi => h_q_not_mult i (by omega))

/-! ## Full swap correctness on `sqir_mult_input_F`. -/

/-- **Sanity helper:** `sqir_target_idx i = 2 + 2*i + 1`. -/
theorem sqir_target_idx_value (i : Nat) :
    sqir_target_idx i = 2 + 2 * i + 1 := rfl

/-- **Full SWAP correctness on `sqir_mult_input_F`.** -/
theorem sqir_swap_acc_mult_apply
    (bits m acc : Nat) (hbits : 1 ≤ bits)
    (hm : m < 2^bits) (hacc : acc < 2^bits) :
    Gate.applyNat (sqir_swap_acc_mult bits) (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits acc m := by
  unfold sqir_swap_acc_mult
  funext q
  -- Case split on q's role.
  by_cases h_target : ∃ i, i < bits ∧ q = sqir_target_idx i
  · obtain ⟨i, hi, hq_eq⟩ := h_target
    rw [hq_eq]
    rw [sqir_swap_acc_mult_aux_at_target_in_range bits bits i (le_refl _) hi]
    rw [sqir_mult_input_control_bit bits m acc i hi]
    -- RHS: sqir_mult_input_F bits acc m at sqir_target_idx i = m.testBit i.
    -- sqir_target_idx i = 2 + 2*i + 1 — workspace.
    show m.testBit i = sqir_mult_input_F bits acc m (sqir_target_idx i)
    unfold sqir_mult_input_F
    rw [sqir_target_idx_value]
    rw [if_pos (by omega : 2 + 2 * i + 1 < 2 + 2 * bits + 1)]
    exact (cuccaro_input_F_at_b 2 i false 0 m).symm
  · by_cases h_mult : ∃ i, i < bits ∧ q = sqir_mult_control_idx bits i
    · obtain ⟨i, hi, hq_eq⟩ := h_mult
      rw [hq_eq]
      rw [sqir_swap_acc_mult_aux_at_mult_in_range bits bits i (le_refl _) hi]
      -- LHS: input (target_idx i) = acc.testBit i.
      have h_lhs : sqir_mult_input_F bits m acc (sqir_target_idx i) = acc.testBit i := by
        unfold sqir_mult_input_F sqir_target_idx
        rw [if_pos (by omega : 2 + 2 * i + 1 < 2 + 2 * bits + 1)]
        exact cuccaro_input_F_at_b 2 i false 0 acc
      rw [h_lhs]
      -- RHS: sqir_mult_input_F bits acc m at sqir_mult_control_idx bits i = acc.testBit i.
      exact (sqir_mult_input_control_bit bits acc m i hi).symm
    · -- Other positions: unchanged by swap, AND sqir_mult_input_F at q with swapped args
      --   equals sqir_mult_input_F at q with original args (since both depend only on
      --   workspace structure, not m or acc, at these positions).
      have h_not_target : ∀ i, i < bits → q ≠ sqir_target_idx i := by
        intros i hi heq
        exact h_target ⟨i, hi, heq⟩
      have h_not_mult : ∀ i, i < bits → q ≠ sqir_mult_control_idx bits i := by
        intros i hi heq
        exact h_mult ⟨i, hi, heq⟩
      rw [sqir_swap_acc_mult_aux_at_other bits bits q (le_refl _) _ h_not_target h_not_mult]
      -- Now: sqir_mult_input_F bits m acc q = sqir_mult_input_F bits acc m q.
      -- For workspace q (not target bit): depends only on q's position class.
      -- For mult register q (not mult_i for any i): impossible — q outside layout.
      -- For above-layout q: both = false.
      by_cases hq_ws : q < 2 + 2 * bits + 1
      · -- Workspace q.  q is not a target bit (h_not_target).
        unfold sqir_mult_input_F
        rw [if_pos hq_ws, if_pos hq_ws]
        -- cuccaro_input_F at q for both sides: depends only on q since a = 0, c_in = false.
        -- Only the "b" (target) bits depend on acc/m.  We need to show q isn't a target bit.
        unfold cuccaro_input_F
        by_cases hq_below : q < 2
        · rw [if_pos hq_below, if_pos hq_below]
        · push_neg at hq_below
          rw [if_neg (by omega : ¬ q < 2), if_neg (by omega : ¬ q < 2)]
          by_cases hq_q_start : q - 2 = 0
          · rw [if_pos hq_q_start, if_pos hq_q_start]
          · rw [if_neg hq_q_start, if_neg hq_q_start]
            by_cases hq_odd : (q - 2) % 2 = 1
            · -- Odd: would be target bit.  But q is not a target bit by h_not_target.
              rw [if_pos hq_odd, if_pos hq_odd]
              -- Goal: acc.testBit ((q - 2 - 1) / 2) = m.testBit ((q - 2 - 1) / 2)
              -- Wait, both functions return b.testBit ... where b is the second
              -- argument (target value).  In our case b = acc on LHS, b = m on RHS.
              -- But we said q is not a target bit; in cuccaro_input_F, the
              -- "b position" is q_start + 2*i + 1 for some i.  We have q ≥ 2, q - 2 = 2*i + 1
              -- for some i ≥ 0.  Need i < bits for it to be a "target bit" in our layout.
              -- Since q < 2 + 2*bits + 1, q - 2 < 2*bits + 1, so 2*i + 1 < 2*bits + 1, i.e., i < bits.
              -- So q IS a target bit (sqir_target_idx i = 2 + 2*i + 1 = q).
              -- Contradiction with h_not_target.
              exfalso
              have hi_bound : (q - 2 - 1) / 2 < bits := by omega
              have h_eq : q = sqir_target_idx ((q - 2 - 1) / 2) := by
                unfold sqir_target_idx; omega
              exact h_not_target ((q - 2 - 1) / 2) hi_bound h_eq
            · rw [if_neg hq_odd, if_neg hq_odd]
      · -- q ≥ 2 + 2*bits + 1.  Could be a multiplier bit (but excluded) or above-layout.
        push_neg at hq_ws
        unfold sqir_mult_input_F
        rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
        rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
        by_cases hq_in_mult : q < 2 + 2 * bits + 1 + bits
        · -- q in multiplier register.
          rw [if_pos hq_in_mult, if_pos hq_in_mult]
          -- The mult value depends on the first arg.  LHS = m.testBit ..., RHS = acc.testBit ...
          -- But h_not_mult says q ≠ sqir_mult_control_idx bits i for any i < bits.
          -- For q in [2 + 2*bits + 1, 2 + 2*bits + 1 + bits), q = 2 + 2*bits + 1 + k
          --   where k = q - (2 + 2*bits + 1) < bits.  So q = sqir_mult_control_idx bits k.
          -- Contradiction with h_not_mult.
          exfalso
          set k := q - (2 + 2 * bits + 1)
          have hk_lt : k < bits := by omega
          have hq_eq : q = sqir_mult_control_idx bits k := by
            unfold sqir_mult_control_idx; omega
          exact h_not_mult k hk_lt hq_eq
        · -- q ≥ 2 + 2*bits + 1 + bits: above layout.  Both = false.
          rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]
          rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]

/-! ## Tick 77 — Task 3: In-place modular multiplier candidate. -/

/-- **In-place modular multiplier wrapper.**

Implements `x ↦ (a*x) % N` in the multiplier register using:
1. `const_gate(a)`: compute `(a*x) % N` into accumulator.
2. `swap_acc_mult`: swap the accumulator and multiplier registers.
3. `const_gate((N - ainv) % N)`: uncompute the old `x` by accumulating
   `(N - ainv) * (a*x) % N ≡ -x (mod N)`, leaving accumulator = 0.

Requires `(a * ainv) % N = 1` (i.e., `ainv` is the modular inverse of `a`). -/
def sqir_modmult_inplace_candidate (bits N a ainv : Nat) : Gate :=
  Gate.seq (sqir_modmult_const_gate bits N a)
    (Gate.seq (sqir_swap_acc_mult bits)
              (sqir_modmult_const_gate bits N ((N - ainv) % N)))

/-! ## Tick 77 — Task 4: Modular inverse arithmetic. -/

/-- **Modular inverse clear arithmetic.**

If `(a * ainv) % N = 1`, then
`(x + ((N - ainv) % N) * ((a * x) % N)) % N = 0`. -/
theorem sqir_modmult_inverse_clear_arith
    (N a ainv x : Nat) (hN_pos : 0 < N) (hx : x < N) (h_ainv_le : ainv ≤ N)
    (h_inv : (a * ainv) % N = 1) :
    (x + ((N - ainv) % N) * ((a * x) % N)) % N = 0 := by
  -- Step 0: combine the inner mods.
  have h_combined :
      (x + ((N - ainv) % N) * ((a * x) % N)) % N
        = (x + (N - ainv) * (a * x)) % N := by
    rw [Nat.add_mod x (((N - ainv) % N) * ((a * x) % N)) N]
    rw [← Nat.mul_mod]
    rw [← Nat.add_mod]
  rw [h_combined]
  -- Step 1: (N - ainv) * (a * x) = N*(a*x) - ainv*(a*x).
  have h_sub : (N - ainv) * (a * x) = N * (a * x) - ainv * (a * x) :=
    Nat.sub_mul N ainv (a * x)
  rw [h_sub]
  -- Step 2: x + (N * (a*x) - ainv * (a*x)).
  -- Since ainv * (a*x) ≤ N * (a*x) (because ainv ≤ N), and N*(a*x) ≤ x + N*(a*x):
  have h_le1 : ainv * (a * x) ≤ N * (a * x) := Nat.mul_le_mul_right _ h_ainv_le
  have h_le2 : ainv * (a * x) ≤ x + N * (a * x) := by omega
  -- Rewrite: x + (N * (a*x) - ainv * (a*x)) = (x + N * (a*x)) - ainv * (a*x).
  have h_assoc : x + (N * (a * x) - ainv * (a * x))
                = (x + N * (a * x)) - ainv * (a * x) := by omega
  rw [h_assoc]
  -- Now: ((x + N*(a*x)) - ainv*(a*x)) % N = 0.
  -- Let A = x + N*(a*x), B = ainv*(a*x).  Then A ≥ B and we want (A - B) % N = 0.
  set A := x + N * (a * x) with hA_def
  set B := ainv * (a * x) with hB_def
  have hB_le_A : B ≤ A := h_le2
  -- A % N = x.
  have hA_mod : A % N = x := by
    rw [hA_def, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hx
  -- B % N = x.
  have hB_mod : B % N = x := by
    rw [hB_def]
    rw [show ainv * (a * x) = (a * ainv) * x by ring]
    rw [Nat.mul_mod, h_inv, Nat.one_mul, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hx
  -- ((A - B) % N + B % N) % N = A % N (by sub_add_cancel + add_mod).
  have h_sub_add : (A - B) + B = A := Nat.sub_add_cancel hB_le_A
  have h_eq : ((A - B) + B) % N = A % N := by rw [h_sub_add]
  have h_eq_split : ((A - B) % N + B % N) % N = A % N := by
    rw [← Nat.add_mod]; exact h_eq
  rw [hA_mod, hB_mod] at h_eq_split
  -- h_eq_split : ((A - B) % N + x) % N = x.  Let R = (A - B) % N.
  set R := (A - B) % N with hR_def
  have hR_lt : R < N := Nat.mod_lt _ hN_pos
  -- (R + x) % N = x, R < N, x < N → R = 0.
  by_contra h_R_ne
  have h_R_pos : R > 0 := Nat.pos_of_ne_zero h_R_ne
  rcases Nat.lt_or_ge (R + x) N with h_lt | h_ge
  · rw [Nat.mod_eq_of_lt h_lt] at h_eq_split
    omega
  · have h_RpX_eq : (R + x) % N = R + x - N := by
      rw [Nat.mod_eq_sub_mod h_ge]
      exact Nat.mod_eq_of_lt (by omega : R + x - N < N)
    rw [h_RpX_eq] at h_eq_split
    omega

/-! ## Tick 77 — Task 5: In-place target theorem. -/

/-- **In-place modular multiplier candidate target theorem.**

After applying the in-place wrapper to `(x, 0)`, the resulting state is
`((a*x) % N, 0)` — i.e., the original "multiplier" register now holds
the product, and the accumulator is cleared. -/
theorem sqir_modmult_inplace_candidate_state_eq
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv) (sqir_mult_input_F bits x 0)
      = sqir_mult_input_F bits ((a * x) % N) 0 := by
  unfold sqir_modmult_inplace_candidate
  simp only [Gate.applyNat_seq]
  -- Step 1: Compute (x, 0) → (x, (a*x) % N).
  have hx_lt_pow : x < 2^bits := Nat.lt_of_lt_of_le hx hN
  rw [sqir_modmult_const_gate_state_eq_from bits N a x 0 hbits hN_pos hN hN2 hN_pos hx_lt_pow]
  simp only [Nat.zero_add]
  -- Step 2: Swap → ((a*x) % N, x).
  have hax_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have hax_lt_pow : (a * x) % N < 2^bits := Nat.lt_of_lt_of_le hax_lt_N hN
  rw [sqir_swap_acc_mult_apply bits x ((a * x) % N) hbits hx_lt_pow hax_lt_pow]
  -- Step 3: Uncompute with c = (N - ainv) % N.
  -- Now input is sqir_mult_input_F bits ((a*x) % N) x.
  rw [sqir_modmult_const_gate_state_eq_from bits N ((N - ainv) % N) ((a * x) % N) x
        hbits hN_pos hN hN2 hx hax_lt_pow]
  -- Result: sqir_mult_input_F bits ((a*x) % N) ((x + ((N - ainv) % N) * ((a*x) % N)) % N).
  -- By inverse arithmetic, the accumulator = 0.
  congr 1
  exact sqir_modmult_inverse_clear_arith N a ainv x hN_pos hx h_ainv_le h_inv

/-! ## R7d^xxix-L-3.15g.2 — Headline: q_start in-place modular
       multiplier state equality.

Built on:
- `sqir_modmult_const_gate_state_eq_from_qstart` (this file, L-3.15g).
- `sqir_swap_acc_mult_apply_qstart` (this file, L-3.15g.2 above).
- `sqir_modmult_inverse_clear_arith` (q_start-INDEPENDENT, above). -/

/-- q_start port of `sqir_modmult_inplace_candidate_state_eq`.

After applying the q_start in-place wrapper to `(x, 0)`, the resulting
state is `((a*x) % N, 0)` — the original "multiplier" register now
holds the product, and the accumulator is cleared. -/
theorem sqir_modmult_inplace_candidate_state_eq_qstart
    (bits q_start N a ainv x flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat
        (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
        (sqir_mult_input_F_qstart bits q_start x 0)
      = sqir_mult_input_F_qstart bits q_start ((a * x) % N) 0 := by
  unfold sqir_modmult_inplace_candidate_qstart
  simp only [Gate.applyNat_seq]
  -- Step 1: compute (x, 0) → (x, (a*x) % N).
  have hx_lt_pow : x < 2^bits := Nat.lt_of_lt_of_le hx hN
  rw [sqir_modmult_const_gate_state_eq_from_qstart bits q_start N a x 0 flagPos dim
        hbits hN_pos hN hN2 hN_pos hx_lt_pow h_flag_lt_qstart h_workspace
        h_dim_covers_mult]
  simp only [Nat.zero_add]
  -- Step 2: swap → ((a*x) % N, x).
  have hax_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have hax_lt_pow : (a * x) % N < 2^bits := Nat.lt_of_lt_of_le hax_lt_N hN
  rw [sqir_swap_acc_mult_apply_qstart bits q_start x ((a * x) % N) hbits
        hx_lt_pow hax_lt_pow]
  -- Step 3: uncompute with c = (N - ainv) % N.
  rw [sqir_modmult_const_gate_state_eq_from_qstart bits q_start N ((N - ainv) % N)
        ((a * x) % N) x flagPos dim
        hbits hN_pos hN hN2 hx hax_lt_pow h_flag_lt_qstart h_workspace
        h_dim_covers_mult]
  congr 1
  exact sqir_modmult_inverse_clear_arith N a ainv x hN_pos hx h_ainv_le h_inv

/-! ## R7d^xxix-L-3.15h — q_start in-place-clean bundle (the MCP
       prerequisite immediately below the MCP layer).

The hard-coded MCP headline at line 4218 wraps the in-place candidate
inside a `Gate.shift bits ∘ reverse_register_swap` adapter (which
re-encodes between the external `encodeDataZeroAnc` layout and the
internal SQIR layout).  That outer adapter is built on the fixed
`q_start = 2` constants in `sqir_mult_control_idx bits 0 = 2*bits + 1`
and would need a parallel q_start-parametric reverse-register adapter
plus its disjointness / well-typed / correctness chain to lift.

Per the L-3.15h fallback policy, this sub-tick lands the **clean
bundle immediately below the MCP layer** (the q_start port of
`sqir_modmult_inplace_candidate_clean`, line 3733).  The bundle
restates the in-place state-eq pointwise via the existing q_start
decoded-helper layer (lines 2488–2640), and is the input that an
adapter-bridge MCP port would consume verbatim.

Concretely the bundle yields:
- decoded target = 0;
- decoded read = 0;
- every position below `q_start` is `false` (the q_start generalisation
  of the old `flag_0`/`flag_1` conjuncts);
- top-carry = `false`;
- multiplier register decodes to `((a*x) % N).testBit k`.

Deferred to L-3.15h.2 (full MCP port):
- `sqir_modmult_rev_anc_qstart`, `sqir_total_dim_qstart`;
- `sqir_mult_input_F_shifted_qstart` (shift by `bits`);
- `sqir_encode_to_mult_adapter_qstart` + disjointness/WellTyped/
  correctness/involution/reverse chain;
- `sqir_modmult_inplace_shifted_qstart` + `_correct` + `_wellTyped`;
- `sqir_modmult_MCP_gate_qstart` + `_apply_encode` + `_wellTyped`;
- `sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty_qstart`. -/

/-- q_start port of `sqir_modmult_inplace_candidate_target_decode`
(line 3708): after the in-place wrapper, the decoded target value is `0`. -/
theorem sqir_modmult_inplace_candidate_target_decode_qstart
    (bits q_start N a ainv x flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0))
      = 0 := by
  rw [sqir_modmult_inplace_candidate_state_eq_qstart bits q_start N a ainv x
        flagPos dim hbits hN_pos hN hN2 h_ainv_le hx h_inv
        h_flag_lt_qstart h_workspace h_dim_covers_mult]
  exact sqir_mult_input_target_decode_qstart bits q_start ((a * x) % N) 0
          (Nat.two_pow_pos bits)

/-- q_start port of `sqir_modmult_inplace_candidate_mult_bit` (line 3721):
the multiplier register decodes bit-by-bit to `((a*x) % N).testBit k`. -/
theorem sqir_modmult_inplace_candidate_mult_bit_qstart
    (bits q_start N a ainv x k flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) (hk : k < bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat
        (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
        (sqir_mult_input_F_qstart bits q_start x 0)
        (sqir_mult_control_idx_qstart bits q_start k)
      = ((a * x) % N).testBit k := by
  rw [sqir_modmult_inplace_candidate_state_eq_qstart bits q_start N a ainv x
        flagPos dim hbits hN_pos hN hN2 h_ainv_le hx h_inv
        h_flag_lt_qstart h_workspace h_dim_covers_mult]
  exact sqir_mult_input_control_bit_qstart bits q_start ((a * x) % N) 0 k hk

/-- q_start port of `sqir_modmult_inplace_candidate_clean` (line 3733).

The clean bundle restating the in-place state-eq pointwise:
* `cuccaro_target_val = 0`;
* `cuccaro_read_val = 0`;
* every position below `q_start` is `false` (q_start generalisation of
  the old `flag_0`/`flag_1` conjuncts at positions 0 and 1);
* top-carry position `q_start + 2*bits` is `false`;
* multiplier-bit decoding at every `sqir_mult_control_idx_qstart bits q_start k`
  equals `((a*x) % N).testBit k`. -/
theorem sqir_modmult_inplace_candidate_clean_qstart
    (bits q_start N a ainv x flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0)) = 0
    ∧ cuccaro_read_val bits q_start
        (Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0)) = 0
    ∧ (∀ q, q < q_start →
        Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0) q = false)
    ∧ Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0) (q_start + 2 * bits) = false
    ∧ ∀ k, k < bits →
        Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0)
          (sqir_mult_control_idx_qstart bits q_start k)
          = ((a * x) % N).testBit k := by
  have h_state := sqir_modmult_inplace_candidate_state_eq_qstart bits q_start N a ainv x
    flagPos dim hbits hN_pos hN hN2 h_ainv_le hx h_inv
    h_flag_lt_qstart h_workspace h_dim_covers_mult
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h_state]
    exact sqir_mult_input_target_decode_qstart bits q_start ((a * x) % N) 0
            (Nat.two_pow_pos bits)
  · rw [h_state]; exact sqir_mult_input_read_decode_qstart bits q_start ((a * x) % N) 0
  · intro q hq
    rw [h_state]
    exact sqir_mult_input_at_below_qstart_eq_false_qstart bits q_start
            ((a * x) % N) 0 q hq
  · rw [h_state]
    exact sqir_mult_input_top_carry_false_qstart bits q_start ((a * x) % N) 0 hbits
  · intro k hk
    rw [h_state]
    exact sqir_mult_input_control_bit_qstart bits q_start ((a * x) % N) 0 k hk

/-! ## Tick 77 — Task 6: Clean workspace bundle for in-place wrapper. -/

/-- **In-place modular multiplier candidate, target decoded.** -/
theorem sqir_modmult_inplace_candidate_target_decode
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv) (sqir_mult_input_F bits x 0))
      = 0 := by
  rw [sqir_modmult_inplace_candidate_state_eq bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv]
  exact sqir_mult_input_target_decode bits ((a * x) % N) 0 (Nat.two_pow_pos bits)

/-- **In-place modular multiplier candidate, multiplier register decoded
to `(a*x) % N`.** -/
theorem sqir_modmult_inplace_candidate_mult_bit
    (bits N a ainv x k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) (hk : k < bits) :
    Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
        (sqir_mult_input_F bits x 0) (sqir_mult_control_idx bits k)
      = ((a * x) % N).testBit k := by
  rw [sqir_modmult_inplace_candidate_state_eq bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv]
  exact sqir_mult_input_control_bit bits ((a * x) % N) 0 k hk

/-- **In-place modular multiplier — clean bundle.** -/
theorem sqir_modmult_inplace_candidate_clean
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
          (sqir_mult_input_F bits x 0)) = 0
    ∧ cuccaro_read_val bits 2
        (Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
          (sqir_mult_input_F bits x 0)) = 0
    ∧ Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
          (sqir_mult_input_F bits x 0) 0 = false
    ∧ Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
          (sqir_mult_input_F bits x 0) 1 = false
    ∧ Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
          (sqir_mult_input_F bits x 0) (2 + 2 * bits) = false
    ∧ ∀ k, k < bits →
        Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
          (sqir_mult_input_F bits x 0) (sqir_mult_control_idx bits k)
          = ((a * x) % N).testBit k := by
  have h_state := sqir_modmult_inplace_candidate_state_eq bits N a ainv x
    hbits hN_pos hN hN2 h_ainv_le hx h_inv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_state]; exact sqir_mult_input_target_decode bits ((a * x) % N) 0 (Nat.two_pow_pos bits)
  · rw [h_state]; exact sqir_mult_input_read_decode bits ((a * x) % N) 0
  · rw [h_state]; exact sqir_mult_input_flag_0_false bits ((a * x) % N) 0
  · rw [h_state]; exact sqir_mult_input_flag_1_false bits ((a * x) % N) 0
  · rw [h_state]; exact sqir_mult_input_top_carry_false bits ((a * x) % N) 0 hbits
  · intro k hk
    rw [h_state]
    exact sqir_mult_input_control_bit bits ((a * x) % N) 0 k hk

/-! ## Tick 78 — Layout adapter bridge to MultiplyCircuitProperty. -/

/-- **Total dimension for the MCP-layout SQIR multiplier.**

`bits` for the external data register + `sqir_modmult_rev_anc bits`
for the SQIR ancilla/workspace block. -/
def sqir_total_dim (bits : Nat) : Nat := bits + sqir_modmult_rev_anc bits

/-- **Shifted SQIR input function.**

The internal SQIR layout shifted up by `bits` so positions `[0, bits)`
are reserved for the external data register and positions
`[bits, bits + sqir_modmult_rev_anc bits)` for the SQIR block. -/
def sqir_mult_input_F_shifted (bits x acc : Nat) : Nat → Bool :=
  fun q => if q < bits then false else sqir_mult_input_F bits x acc (q - bits)

theorem sqir_mult_input_F_shifted_below_bits
    (bits x acc q : Nat) (hq : q < bits) :
    sqir_mult_input_F_shifted bits x acc q = false := by
  unfold sqir_mult_input_F_shifted; rw [if_pos hq]

theorem sqir_mult_input_F_shifted_above_bits
    (bits x acc q : Nat) (hq : bits ≤ q) :
    sqir_mult_input_F_shifted bits x acc q
      = sqir_mult_input_F bits x acc (q - bits) := by
  unfold sqir_mult_input_F_shifted; rw [if_neg (Nat.not_lt.mpr hq)]

theorem sqir_mult_input_F_shifted_at_shifted_control_bit
    (bits x acc k : Nat) (hk : k < bits) :
    sqir_mult_input_F_shifted bits x acc (bits + sqir_mult_control_idx bits k)
      = x.testBit k := by
  rw [sqir_mult_input_F_shifted_above_bits bits x acc _ (by omega)]
  rw [show bits + sqir_mult_control_idx bits k - bits = sqir_mult_control_idx bits k from by omega]
  exact sqir_mult_input_control_bit bits x acc k hk

/-! ## Tick 78 — Task 2: Gate.shift. -/

/-- Shift all gate positions up by `off`. -/
def Gate.shift (off : Nat) : Gate → Gate
  | Gate.I        => Gate.I
  | Gate.X q      => Gate.X (off + q)
  | Gate.CX a b   => Gate.CX (off + a) (off + b)
  | Gate.CCX a b c => Gate.CCX (off + a) (off + b) (off + c)
  | Gate.seq g h  => Gate.seq (Gate.shift off g) (Gate.shift off h)

theorem Gate.shift_seq (off : Nat) (g h : Gate) :
    Gate.shift off (Gate.seq g h)
      = Gate.seq (Gate.shift off g) (Gate.shift off h) := rfl

/-- **At positions below `off`, a shifted gate acts as identity.** -/
theorem Gate.applyNat_shift_at_lo
    (off : Nat) (g : Gate) (f : Nat → Bool) (q : Nat) (hq : q < off) :
    Gate.applyNat (Gate.shift off g) f q = f q := by
  induction g generalizing f with
  | I => rfl
  | X p =>
    show update f (off + p) (! f (off + p)) q = f q
    rw [update_neq _ _ _ _ (by omega : q ≠ off + p)]
  | CX a b =>
    show update f (off + b) (xor (f (off + b)) (f (off + a))) q = f q
    rw [update_neq _ _ _ _ (by omega : q ≠ off + b)]
  | CCX a b c =>
    show update f (off + c) (xor (f (off + c)) (f (off + a) && f (off + b))) q = f q
    rw [update_neq _ _ _ _ (by omega : q ≠ off + c)]
  | seq g₁ g₂ ih₁ ih₂ =>
    show Gate.applyNat (Gate.shift off g₂) (Gate.applyNat (Gate.shift off g₁) f) q = f q
    rw [ih₂]
    exact ih₁ f

/-- **At positions ≥ `off`, a shifted gate acts as the original gate
on the function `r ↦ f (off + r)`.** -/
theorem Gate.applyNat_shift_at_hi
    (off : Nat) (g : Gate) (f : Nat → Bool) (q : Nat) (hq : off ≤ q) :
    Gate.applyNat (Gate.shift off g) f q
      = Gate.applyNat g (fun r => f (off + r)) (q - off) := by
  induction g generalizing f q with
  | I =>
    show f q = f (off + (q - off))
    congr 1; omega
  | X p =>
    show update f (off + p) (! f (off + p)) q
        = update (fun r => f (off + r)) p (! (fun r => f (off + r)) p) (q - off)
    by_cases h_eq : q = off + p
    · subst h_eq
      rw [update_eq, show off + p - off = p from by omega, update_eq]
    · rw [update_neq _ _ _ _ h_eq]
      have h_ne : q - off ≠ p := fun h => h_eq (by omega)
      rw [update_neq _ _ _ _ h_ne]
      show f q = f (off + (q - off))
      congr 1; omega
  | CX a b =>
    show update f (off + b) (xor (f (off + b)) (f (off + a))) q
        = update (fun r => f (off + r)) b
            (xor ((fun r => f (off + r)) b) ((fun r => f (off + r)) a)) (q - off)
    by_cases h_eq : q = off + b
    · subst h_eq
      rw [update_eq, show off + b - off = b from by omega, update_eq]
    · rw [update_neq _ _ _ _ h_eq]
      have h_ne : q - off ≠ b := fun h => h_eq (by omega)
      rw [update_neq _ _ _ _ h_ne]
      show f q = f (off + (q - off))
      congr 1; omega
  | CCX a b c =>
    show update f (off + c) (xor (f (off + c)) (f (off + a) && f (off + b))) q
        = update (fun r => f (off + r)) c
            (xor ((fun r => f (off + r)) c)
              ((fun r => f (off + r)) a && (fun r => f (off + r)) b))
            (q - off)
    by_cases h_eq : q = off + c
    · subst h_eq
      rw [update_eq, show off + c - off = c from by omega, update_eq]
    · rw [update_neq _ _ _ _ h_eq]
      have h_ne : q - off ≠ c := fun h => h_eq (by omega)
      rw [update_neq _ _ _ _ h_ne]
      show f q = f (off + (q - off))
      congr 1; omega
  | seq g₁ g₂ ih₁ ih₂ =>
    show Gate.applyNat (Gate.shift off g₂) (Gate.applyNat (Gate.shift off g₁) f) q
        = Gate.applyNat g₂ (Gate.applyNat g₁ (fun r => f (off + r))) (q - off)
    rw [ih₂ (Gate.applyNat (Gate.shift off g₁) f) q hq]
    congr 1
    funext r
    by_cases hr : off ≤ off + r
    · rw [ih₁ f (off + r) hr]
      congr 1; omega
    · exfalso; omega

/-- **Gate.shift is WellTyped at the larger dimension.** -/
theorem Gate.shift_wellTyped
    {off dim : Nat} {g : Gate} (h : Gate.WellTyped dim g) :
    Gate.WellTyped (off + dim) (Gate.shift off g) := by
  induction g with
  | I =>
    show 0 < off + dim
    exact Nat.lt_of_lt_of_le h (Nat.le_add_left dim off)
  | X q =>
    show off + q < off + dim
    have : q < dim := h
    omega
  | CX a b =>
    obtain ⟨ha, hb, hab⟩ := h
    show off + a < off + dim ∧ off + b < off + dim ∧ off + a ≠ off + b
    refine ⟨by omega, by omega, ?_⟩
    intro heq; exact hab (by omega)
  | CCX a b c =>
    obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := h
    show off + a < off + dim ∧ off + b < off + dim ∧ off + c < off + dim
        ∧ off + a ≠ off + b ∧ off + a ≠ off + c ∧ off + b ≠ off + c
    refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
    · intro heq; exact hab (by omega)
    · intro heq; exact hac (by omega)
    · intro heq; exact hbc (by omega)
  | seq g₁ g₂ ih₁ ih₂ =>
    refine ⟨ih₁ h.1, ih₂ h.2⟩

/-! ## Tick 78 — Task 3: Data-layout adapter. -/

/-- Position of `x.testBit j` in the big-endian `encodeDataZeroAnc`
encoding (for `j < bits`). -/
def encode_data_pos (bits j : Nat) : Nat := bits - 1 - j

/-- Shifted SQIR position of multiplier control bit `j`. -/
def shifted_sqir_control_idx (bits j : Nat) : Nat :=
  bits + sqir_mult_control_idx bits j

/-- **Layout adapter from `encodeDataZeroAnc` to shifted SQIR layout.**

Reuses the existing `reverse_register_swap` primitive: position `i` of
the encoded data register (`[0, bits)`) is swapped with position
`(3*bits + 3) + (bits - 1 - i)` of the shifted SQIR multiplier register. -/
def sqir_encode_to_mult_adapter (bits : Nat) : Gate :=
  reverse_register_swap bits 0 (bits + sqir_mult_control_idx bits 0)

/-- Disjointness of swap ranges (used in `reverse_register_swap` lemmas). -/
private theorem sqir_encode_to_mult_adapter_disjoint (bits : Nat) :
    0 + bits ≤ bits + sqir_mult_control_idx bits 0
      ∨ bits + sqir_mult_control_idx bits 0 + bits ≤ 0 := by
  left; unfold sqir_mult_control_idx; omega

theorem sqir_encode_to_mult_adapter_wellTyped
    (bits : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (sqir_total_dim bits) (sqir_encode_to_mult_adapter bits) := by
  unfold sqir_encode_to_mult_adapter sqir_total_dim
  apply reverse_register_swap_wellTyped
  · unfold sqir_modmult_rev_anc; omega
  · unfold sqir_modmult_rev_anc; omega
  · unfold sqir_mult_control_idx sqir_modmult_rev_anc; omega
  · exact sqir_encode_to_mult_adapter_disjoint bits

/-- Helper: workspace value of `cuccaro_input_F 2 false 0 0` is always false. -/
private theorem cuccaro_input_F_zero_at_workspace
    (q : Nat) (hq : q < 2 + 2 * (0 : Nat) + 1 ∨ True) :
    cuccaro_input_F 2 false 0 0 q = false := by
  unfold cuccaro_input_F
  by_cases h_lt : q < 2
  · rw [if_pos h_lt]
  · rw [if_neg h_lt]
    set i := q - 2
    by_cases hi_0 : i = 0
    · rw [if_pos hi_0]
    · rw [if_neg hi_0]
      by_cases hi_odd : i % 2 = 1
      · rw [if_pos hi_odd]; exact Nat.zero_testBit _
      · rw [if_neg hi_odd]; exact Nat.zero_testBit _

/-- **Adapter correctness: `encodeDataZeroAnc → sqir_mult_input_F_shifted`.** -/
theorem sqir_encode_to_mult_adapter_correct
    (bits x : Nat) (hbits : 1 ≤ bits) (hx : x < 2^bits) :
    Gate.applyNat (sqir_encode_to_mult_adapter bits)
        (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
      = sqir_mult_input_F_shifted bits x 0 := by
  funext q
  unfold sqir_encode_to_mult_adapter
  set offB := bits + sqir_mult_control_idx bits 0 with h_offB_def
  have h_offB_val : offB = 2 + 2 * bits + 1 + bits := by
    rw [h_offB_def]; unfold sqir_mult_control_idx; omega
  have h_disjoint : 0 + bits ≤ offB ∨ offB + bits ≤ 0 :=
    sqir_encode_to_mult_adapter_disjoint bits
  have h_anc_pos : 0 < sqir_modmult_rev_anc bits := by unfold sqir_modmult_rev_anc; omega
  by_cases hq_lo : q < bits
  · -- Encoded data position: at_A with j = q.
    rw [sqir_mult_input_F_shifted_below_bits bits x 0 q hq_lo]
    conv_lhs => rw [show q = 0 + q from by omega]
    unfold reverse_register_swap
    rw [reverse_register_swap_aux_at_A bits 0 offB bits _ q hq_lo h_disjoint (le_refl _)]
    have h_anc_idx_lt : offB + (bits - 1 - q) - bits < sqir_modmult_rev_anc bits := by
      rw [h_offB_val]; unfold sqir_modmult_rev_anc; omega
    have h_anc_eq : offB + (bits - 1 - q) = bits + (offB + (bits - 1 - q) - bits) := by
      rw [h_offB_val]; omega
    rw [h_anc_eq, encodeDataZeroAnc_anc hx h_anc_idx_lt]
  · push_neg at hq_lo
    by_cases hq_in_mult : offB ≤ q ∧ q < offB + bits
    · obtain ⟨h_q_ge, h_q_lt⟩ := hq_in_mult
      have h_j'_lt : bits - 1 - (q - offB) < bits := by omega
      -- RHS first: convert to shifted_control_bit form.
      have h_q_minus_bits : q - bits = sqir_mult_control_idx bits (q - offB) := by
        rw [h_offB_val] at h_q_ge h_q_lt; unfold sqir_mult_control_idx; omega
      rw [sqir_mult_input_F_shifted_above_bits bits x 0 q (by omega)]
      rw [h_q_minus_bits]
      rw [sqir_mult_input_control_bit bits x 0 (q - offB) (by omega)]
      -- LHS:
      have h_q_eq : q = offB + (bits - 1 - (bits - 1 - (q - offB))) := by omega
      conv_lhs => rw [h_q_eq]
      unfold reverse_register_swap
      rw [reverse_register_swap_aux_at_B bits 0 offB bits _ (bits - 1 - (q - offB))
            h_j'_lt h_disjoint (le_refl _)]
      simp only [Nat.zero_add]
      rw [encodeDataZeroAnc_data hx h_j'_lt]
      unfold FormalRV.Framework.nat_to_funbool
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have h_exp_eq : bits - 1 - (bits - 1 - (q - offB)) = q - offB := by omega
      rw [h_exp_eq]
    · -- Other positions: identity.
      have h_not_in_swap_range : ¬ (offB ≤ q ∧ q < offB + bits) := hq_in_mult
      have h_lhs_id : Gate.applyNat (reverse_register_swap_aux bits 0 offB bits)
                          (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x) q
                        = encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x q := by
        apply reverse_register_swap_aux_at_other bits 0 offB bits _ q h_disjoint (le_refl _)
        intro i hi
        refine ⟨by omega, ?_⟩
        intro heq
        exact h_not_in_swap_range ⟨by omega, by omega⟩
      unfold reverse_register_swap
      rw [h_lhs_id]
      rw [sqir_mult_input_F_shifted_above_bits bits x 0 q hq_lo]
      by_cases hq_below_offB : q < offB
      · -- q ∈ [bits, offB).  Both false.
        have h_anc_idx_lt : q - bits < sqir_modmult_rev_anc bits := by
          rw [h_offB_val] at hq_below_offB; unfold sqir_modmult_rev_anc; omega
        have h_eq : q = bits + (q - bits) := by omega
        rw [h_eq, encodeDataZeroAnc_anc hx h_anc_idx_lt]
        -- RHS: q - bits ∈ [0, 2*bits + 3).  In workspace.
        unfold sqir_mult_input_F
        rw [if_pos (by rw [h_offB_val] at hq_below_offB; omega
                      : bits + (q - bits) - bits < 2 + 2 * bits + 1)]
        rw [show bits + (q - bits) - bits = q - bits from by omega]
        exact (cuccaro_input_F_zero_at_workspace (q - bits) (Or.inr trivial)).symm
      · push_neg at hq_below_offB
        -- q ≥ offB + bits.  Encoded false, RHS false.
        have h_q_minus_eq : bits + (q - bits) - bits = q - bits := by omega
        have h_RHS_false : sqir_mult_input_F bits x 0 (q - bits) = false := by
          unfold sqir_mult_input_F
          rw [if_neg (by rw [h_offB_val] at hq_below_offB; omega
                        : ¬ q - bits < 2 + 2 * bits + 1)]
          rw [if_neg (by rw [h_offB_val] at hq_below_offB; omega
                        : ¬ q - bits < 2 + 2 * bits + 1 + bits)]
        rw [h_RHS_false]
        rw [show q = bits + (q - bits) from by omega]
        by_cases h_q_minus_lt_anc : q - bits < sqir_modmult_rev_anc bits
        · exact encodeDataZeroAnc_anc hx h_q_minus_lt_anc
        · push_neg at h_q_minus_lt_anc
          exact encodeDataZeroAnc_oob h_anc_pos
                (by omega : bits + sqir_modmult_rev_anc bits ≤ bits + (q - bits))

/-! ## Tick 78 — Adapter involution + reverse direction. -/

/-- **General reverse-register-swap involution.**  Applying
`reverse_register_swap n offsetA offsetB` twice yields identity, given
disjoint ranges. -/
theorem reverse_register_swap_involution_general
    (n offsetA offsetB : Nat)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA)
    (f : Nat → Bool) :
    Gate.applyNat (reverse_register_swap n offsetA offsetB)
      (Gate.applyNat (reverse_register_swap n offsetA offsetB) f)
    = f := by
  unfold reverse_register_swap
  funext q
  by_cases h_in_A : offsetA ≤ q ∧ q < offsetA + n
  · obtain ⟨h_q_lo, h_q_hi⟩ := h_in_A
    set j := q - offsetA with hj_def
    have hj_lt : j < n := by omega
    have h_q_eq : q = offsetA + j := by omega
    conv_lhs => rw [h_q_eq]
    rw [reverse_register_swap_aux_at_A n offsetA offsetB n _ j hj_lt h_disjoint (le_refl _)]
    rw [reverse_register_swap_aux_at_B n offsetA offsetB n _ j hj_lt h_disjoint (le_refl _)]
    congr 1; omega
  · by_cases h_in_B : offsetB ≤ q ∧ q < offsetB + n
    · obtain ⟨h_q_lo, h_q_hi⟩ := h_in_B
      set j := n - 1 - (q - offsetB) with hj_def
      have hj_lt : j < n := by omega
      have h_q_eq : q = offsetB + (n - 1 - j) := by omega
      conv_lhs => rw [h_q_eq]
      rw [reverse_register_swap_aux_at_B n offsetA offsetB n _ j hj_lt h_disjoint (le_refl _)]
      rw [reverse_register_swap_aux_at_A n offsetA offsetB n _ j hj_lt h_disjoint (le_refl _)]
      congr 1; omega
    · -- q outside both ranges.
      push_neg at h_in_A h_in_B
      have h_outside : ∀ i, i < n →
          q ≠ offsetA + i ∧ q ≠ offsetB + (n - 1 - i) := by
        intro i hi
        refine ⟨?_, ?_⟩
        · by_contra heq; exact absurd (Nat.le_refl q) (by omega)
        · intro heq
          have h_q_ge_B : offsetB ≤ q := by omega
          have h_q_lt_B_n : q < offsetB + n := by omega
          exact absurd (h_in_B h_q_ge_B) (by omega)
      rw [reverse_register_swap_aux_at_other n offsetA offsetB n _ q h_disjoint (le_refl _) h_outside]
      rw [reverse_register_swap_aux_at_other n offsetA offsetB n _ q h_disjoint (le_refl _) h_outside]

/-- **Adapter is self-inverse.** -/
theorem sqir_encode_to_mult_adapter_involution
    (bits : Nat) (f : Nat → Bool) :
    Gate.applyNat (sqir_encode_to_mult_adapter bits)
      (Gate.applyNat (sqir_encode_to_mult_adapter bits) f) = f := by
  unfold sqir_encode_to_mult_adapter
  exact reverse_register_swap_involution_general bits 0 _
    (sqir_encode_to_mult_adapter_disjoint bits) f

/-- **Adapter reverse direction: `sqir_mult_input_F_shifted → encodeDataZeroAnc`.** -/
theorem sqir_encode_to_mult_adapter_reverse
    (bits y : Nat) (hbits : 1 ≤ bits) (hy : y < 2^bits) :
    Gate.applyNat (sqir_encode_to_mult_adapter bits)
        (sqir_mult_input_F_shifted bits y 0)
      = encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) y := by
  have h_forward := sqir_encode_to_mult_adapter_correct bits y hbits hy
  -- applyNat adapter (encoded y) = shifted y.
  -- So applyNat adapter (shifted y) = applyNat adapter (applyNat adapter (encoded y)) = encoded y.
  have h_invol := sqir_encode_to_mult_adapter_involution bits
                    (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) y)
  rw [h_forward] at h_invol
  exact h_invol

/-! ## Tick 78 — Task 4: Shifted in-place multiplier. -/

/-- **Shifted in-place modular multiplier gate.** -/
def sqir_modmult_inplace_shifted (bits N a ainv : Nat) : Gate :=
  Gate.shift bits (sqir_modmult_inplace_candidate bits N a ainv)

/-- **Shifted in-place multiplier correctness.** -/
theorem sqir_modmult_inplace_shifted_correct
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (sqir_modmult_inplace_shifted bits N a ainv)
        (sqir_mult_input_F_shifted bits x 0)
      = sqir_mult_input_F_shifted bits ((a * x) % N) 0 := by
  unfold sqir_modmult_inplace_shifted
  funext q
  by_cases hq_lo : q < bits
  · rw [Gate.applyNat_shift_at_lo bits _ _ q hq_lo]
    rw [sqir_mult_input_F_shifted_below_bits bits x 0 q hq_lo]
    rw [sqir_mult_input_F_shifted_below_bits bits ((a * x) % N) 0 q hq_lo]
  · push_neg at hq_lo
    rw [Gate.applyNat_shift_at_hi bits _ _ q hq_lo]
    rw [sqir_mult_input_F_shifted_above_bits bits ((a * x) % N) 0 q hq_lo]
    have h_inner_eq : (fun r => sqir_mult_input_F_shifted bits x 0 (bits + r))
                    = sqir_mult_input_F bits x 0 := by
      funext r
      rw [sqir_mult_input_F_shifted_above_bits bits x 0 (bits + r) (by omega)]
      congr 1; omega
    rw [h_inner_eq]
    rw [sqir_modmult_inplace_candidate_state_eq bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv]

theorem sqir_modmult_inplace_shifted_wellTyped
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    Gate.WellTyped (sqir_total_dim bits) (sqir_modmult_inplace_shifted bits N a ainv) := by
  unfold sqir_modmult_inplace_shifted sqir_total_dim
  apply Gate.shift_wellTyped
  -- Need: WellTyped (sqir_modmult_rev_anc bits) (sqir_modmult_inplace_candidate bits N a ainv).
  -- The in-place candidate = seq const_gate (seq swap const_gate).
  unfold sqir_modmult_inplace_candidate
  refine ⟨?_, ?_, ?_⟩
  · exact sqir_modmult_prefix_gate_wellTyped bits N a bits hbits hN_pos hN hN2 (le_refl _)
  · exact sqir_swap_acc_mult_wellTyped bits hbits
  · exact sqir_modmult_prefix_gate_wellTyped bits N ((N - ainv) % N) bits
            hbits hN_pos hN hN2 (le_refl _)

/-! ## Tick 78 — Task 5/6: Full MCP-layout gate. -/

/-- **MCP-layout gate.**  Three-stage composition:
adapter → shifted in-place multiplier → adapter. -/
def sqir_modmult_MCP_gate (bits N a ainv : Nat) : Gate :=
  Gate.seq (sqir_encode_to_mult_adapter bits)
    (Gate.seq (sqir_modmult_inplace_shifted bits N a ainv)
              (sqir_encode_to_mult_adapter bits))

/-- **MCP-layout gate apply theorem.**

The composed gate maps `encodeDataZeroAnc bits anc x` to
`encodeDataZeroAnc bits anc ((a*x) % N)`. -/
theorem sqir_modmult_MCP_gate_apply_encode
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (sqir_modmult_MCP_gate bits N a ainv)
        (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
      = encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) ((a * x) % N) := by
  unfold sqir_modmult_MCP_gate
  simp only [Gate.applyNat_seq]
  have hx_lt_pow : x < 2^bits := Nat.lt_of_lt_of_le hx hN
  rw [sqir_encode_to_mult_adapter_correct bits x hbits hx_lt_pow]
  rw [sqir_modmult_inplace_shifted_correct bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv]
  have h_ax_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have h_ax_lt_pow : (a * x) % N < 2^bits := Nat.lt_of_lt_of_le h_ax_lt_N hN
  exact sqir_encode_to_mult_adapter_reverse bits ((a * x) % N) hbits h_ax_lt_pow

/-- **MCP-layout gate WellTyped.** -/
theorem sqir_modmult_MCP_gate_wellTyped
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    Gate.WellTyped (sqir_total_dim bits) (sqir_modmult_MCP_gate bits N a ainv) := by
  unfold sqir_modmult_MCP_gate
  refine ⟨?_, ?_, ?_⟩
  · exact sqir_encode_to_mult_adapter_wellTyped bits hbits
  · exact sqir_modmult_inplace_shifted_wellTyped bits N a ainv hbits hN_pos hN hN2
  · exact sqir_encode_to_mult_adapter_wellTyped bits hbits

/-! ## Tick 78 — Task 7: MultiplyCircuitProperty bridge. -/

/-- **HEADLINE: MCP-layout gate satisfies `MultiplyCircuitProperty`.** -/
theorem sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    FormalRV.SQIRPort.MultiplyCircuitProperty a N bits (sqir_modmult_rev_anc bits)
      (Gate.toUCom (sqir_total_dim bits) (sqir_modmult_MCP_gate bits N a ainv)) := by
  unfold sqir_total_dim
  apply toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc
    (sqir_modmult_MCP_gate_wellTyped bits N a ainv hbits hN_pos hN hN2)
    hN
  intro x hx
  exact sqir_modmult_MCP_gate_apply_encode bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv

/-! ## Tick 79 — Verified ModMulImpl family.

### Layout and sizing decision (documented as Route B)

The original SQIR axiom site (`Shor.lean:4570`) declares:
  axiom f_modmult_circuit : (a ainv N n : Nat) → Nat → BaseUCom (n + modmult_rev_anc n)
where `modmult_rev_anc n = 2 * n + 1`, giving total dim `3 * n + 1`.

Our verified MCP gate has total dim `(n + 1) + sqir_modmult_rev_anc (n + 1) = 4 * n + 15`
because:
1. `BasicSetting` only guarantees `2^n ≤ 2 * N`, NOT `2 * N ≤ 2^n`.  The
   `BasicSetting_twoN_le_pow_succ` lemma gives `2 * N ≤ 2 ^ (n + 1)`, so
   we instantiate at `bits = n + 1`.
2. The SQIR-faithful workspace requires `3 * (n + 1) + 11 = 3 * n + 14`
   ancilla bits, which exceeds the placeholder's `2 * (n+1) + 1`.

**Route B (verified parallel family)**: we land a new family
`f_modmult_circuit_verified` at dimension `(n + 1) + sqir_modmult_rev_anc (n + 1)`,
prove `ModMulImpl` + `uc_well_typed` at that dimension, and document the
exact dimension mismatch with the original placeholder.  The original
axiom names remain untouched; downstream theorems that take
`ModMulImpl ... f` as a hypothesis can be instantiated with our family
at dimension `n + 1` (with appropriate dimension/ancilla bookkeeping). -/

/-- **Per-iterate modular inverse arithmetic.**

If `(a * ainv) % N = 1` and `N ≥ 2`, then for every `i`,
`((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1`. -/
theorem pow_iter_inverse_mod
    (a ainv N i : Nat) (hN_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    ((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1 := by
  rw [← Nat.mul_mod]
  rw [← Nat.mul_pow]
  rw [Nat.pow_mod]
  rw [h_inv]
  rw [one_pow]
  exact Nat.mod_eq_of_lt hN_ge_2

/-- **Verified modular-multiplier oracle family** at SQIR-faithful
dimension `(n + 1) + sqir_modmult_rev_anc (n + 1)`. -/
noncomputable def f_modmult_circuit_verified (a ainv N n : Nat) :
    Nat → FormalRV.Framework.BaseUCom ((n + 1) + sqir_modmult_rev_anc (n + 1)) :=
  fun i =>
    Gate.toUCom ((n + 1) + sqir_modmult_rev_anc (n + 1))
      (sqir_modmult_MCP_gate (n + 1) N ((a^(2^i)) % N) ((ainv^(2^i)) % N))

/-- **MCP up-to-mod lifting.**  If a unitary satisfies
`MultiplyCircuitProperty (c % N)`, then it also satisfies
`MultiplyCircuitProperty c` (since `(c * x) % N = ((c % N) * x) % N`). -/
theorem MultiplyCircuitProperty_of_mod
    {c N n anc : Nat} {U : FormalRV.Framework.BaseUCom (n + anc)}
    (hN_pos : 0 < N) (h_modN : FormalRV.SQIRPort.MultiplyCircuitProperty (c % N) N n anc U) :
    FormalRV.SQIRPort.MultiplyCircuitProperty c N n anc U := by
  unfold FormalRV.SQIRPort.MultiplyCircuitProperty at h_modN ⊢
  intro x hx
  have h_eq : c * x % N = c % N * x % N := by
    conv_lhs => rw [Nat.mul_mod]
    conv_rhs => rw [Nat.mul_mod]
    rw [Nat.mod_mod]
  rw [h_eq]
  exact h_modN x hx

/-- **Per-iterate `MultiplyCircuitProperty` for the verified family.** -/
theorem f_modmult_circuit_verified_per_iterate
    (a ainv N n i : Nat) (hN_ge_2 : 2 ≤ N) (hN : N ≤ 2^(n + 1)) (hN2 : 2 * N ≤ 2^(n + 1))
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.MultiplyCircuitProperty
      (a^(2^i)) N (n + 1) (sqir_modmult_rev_anc (n + 1))
      (f_modmult_circuit_verified a ainv N n i) := by
  unfold f_modmult_circuit_verified
  have hN_pos : 0 < N := by omega
  have h_ainv_lt_N : (ainv^(2^i)) % N < N := Nat.mod_lt _ hN_pos
  have h_ainv_le : (ainv^(2^i)) % N ≤ N := Nat.le_of_lt h_ainv_lt_N
  have h_inv_i : ((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1 :=
    pow_iter_inverse_mod a ainv N i hN_ge_2 h_inv
  -- Reframe via mod-up-to lift.
  apply MultiplyCircuitProperty_of_mod hN_pos
  -- Goal: MultiplyCircuitProperty ((a^(2^i)) % N) N (n+1) anc (Gate.toUCom ... MCP_gate)
  show FormalRV.SQIRPort.MultiplyCircuitProperty
    ((a^(2^i)) % N) N (n + 1) (sqir_modmult_rev_anc (n + 1))
    (Gate.toUCom ((n + 1) + sqir_modmult_rev_anc (n + 1))
      (sqir_modmult_MCP_gate (n + 1) N ((a^(2^i)) % N) ((ainv^(2^i)) % N)))
  have h_mcp := sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty
    (n + 1) N ((a^(2^i)) % N) ((ainv^(2^i)) % N)
    (by omega : 1 ≤ n + 1) hN_pos hN hN2 h_ainv_le h_inv_i
  unfold sqir_total_dim at h_mcp
  exact h_mcp

/-- **`ModMulImpl` for the verified family.** -/
theorem f_modmult_circuit_verified_MMI
    (a ainv N n : Nat) (hN_ge_2 : 2 ≤ N) (hN : N ≤ 2^(n + 1)) (hN2 : 2 * N ≤ 2^(n + 1))
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.ModMulImpl a N (n + 1) (sqir_modmult_rev_anc (n + 1))
      (f_modmult_circuit_verified a ainv N n) := by
  intro i
  exact f_modmult_circuit_verified_per_iterate a ainv N n i hN_ge_2 hN hN2 h_inv

/-- **`uc_well_typed` for every iterate of the verified family.** -/
theorem f_modmult_circuit_verified_uc_well_typed
    (a ainv N n : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^(n + 1)) (hN2 : 2 * N ≤ 2^(n + 1)) :
    ∀ i, FormalRV.SQIRPort.uc_well_typed (f_modmult_circuit_verified a ainv N n i) := by
  intro i
  unfold f_modmult_circuit_verified
  apply uc_well_typed_toUCom_of_Gate_WellTyped
  have h_wt := sqir_modmult_MCP_gate_wellTyped (n + 1) N
    ((a^(2^i)) % N) ((ainv^(2^i)) % N) (by omega : 1 ≤ n + 1) hN_pos hN hN2
  unfold sqir_total_dim at h_wt
  exact h_wt

/-! ### BasicSetting bridge for the verified family. -/

/-- **`ModMulImpl` from `BasicSetting`** (n+1 dimension). -/
theorem f_modmult_circuit_verified_MMI_from_BasicSetting
    (a r N m n ainv : Nat) (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.ModMulImpl a N (n + 1) (sqir_modmult_rev_anc (n + 1))
      (f_modmult_circuit_verified a ainv N n) := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have h_N_ge_2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h_lt | h_ge
    · exfalso
      have hN_eq : N = 1 := by omega
      rw [hN_eq, Nat.mod_one] at h_inv
      exact absurd h_inv (by decide)
    · exact h_ge
  have hN : N ≤ 2 ^ (n + 1) := by
    have h1 : N ≤ 2 * N := by omega
    have h2 : 2 * N ≤ 2 ^ (n + 1) := hN2
    omega
  exact f_modmult_circuit_verified_MMI a ainv N n h_N_ge_2 hN hN2 h_inv

/-- **`uc_well_typed` from `BasicSetting`**. -/
theorem f_modmult_circuit_verified_uc_well_typed_from_BasicSetting
    (a r N m n ainv : Nat) (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n) :
    ∀ i, FormalRV.SQIRPort.uc_well_typed (f_modmult_circuit_verified a ainv N n i) := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have hN : N ≤ 2 ^ (n + 1) := by
    have h1 : N ≤ 2 * N := by omega
    have h2 : 2 * N ≤ 2 ^ (n + 1) := hN2
    omega
  exact f_modmult_circuit_verified_uc_well_typed a ainv N n hN_pos hN hN2

/-! ## Tick 80 — Bits-parameterized verified family + Shor wiring.

### BasicSetting sizing mismatch documentation

The original SQIR `Shor_correct_var` is parametric over `(a r N m n anc)`
and requires `BasicSetting a r N m n` which contains the tight register
bound `N < 2^n ≤ 2 * N`.  Our verified MCP gate requires
`2 * N ≤ 2^bits`.  These two bounds can only coexist when `2^bits = 2 * N`,
i.e., `N` is a power of 2 — a degenerate case.

For general `N`, taking `bits = n + 1` (so `2^bits = 2 * 2^n ≥ 2 * N`)
violates BasicSetting's `2^bits ≤ 2 * N` requirement.  Conversely,
taking `bits = n` (where BasicSetting holds) fails our gate's
`2 * N ≤ 2^bits` requirement (we only get `2^n ≤ 2 * N`, the
opposite direction).

**Conclusion**: Direct instantiation of `Shor_correct_var` with our
verified family at `bits = n + 1` is BLOCKED by the BasicSetting
upper-bound conflict.  A fully verified Shor theorem using our family
would require either:
  (a) a relaxed `BasicSetting'` that drops the `2^n ≤ 2 * N` constraint,
      plus a re-proof of `Shor_correct_var` for the relaxed form, OR
  (b) refactoring the SQIR convention so the data register and the
      Coq-side ancilla budget are separately parameterized.

This is the "Status D" classification per the task spec.  We land the
infrastructure below to make the wiring trivial once the relaxed
`Shor_correct_var` exists. -/

/-- **Bits-parameterized verified modular-multiplier family.** -/
noncomputable def f_modmult_circuit_verified_bits (a ainv N bits : Nat) :
    Nat → FormalRV.Framework.BaseUCom (bits + sqir_modmult_rev_anc bits) :=
  fun i =>
    Gate.toUCom (bits + sqir_modmult_rev_anc bits)
      (sqir_modmult_MCP_gate bits N ((a^(2^i)) % N) ((ainv^(2^i)) % N))

/-- **MMI for the bits-parameterized family.** -/
theorem f_modmult_circuit_verified_bits_MMI
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_ge_2 : 2 ≤ N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.ModMulImpl a N bits (sqir_modmult_rev_anc bits)
      (f_modmult_circuit_verified_bits a ainv N bits) := by
  intro i
  unfold f_modmult_circuit_verified_bits
  have hN_pos : 0 < N := by omega
  have h_ainv_lt_N : (ainv^(2^i)) % N < N := Nat.mod_lt _ hN_pos
  have h_ainv_le : (ainv^(2^i)) % N ≤ N := Nat.le_of_lt h_ainv_lt_N
  have h_inv_i : ((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1 :=
    pow_iter_inverse_mod a ainv N i hN_ge_2 h_inv
  apply MultiplyCircuitProperty_of_mod hN_pos
  have h_mcp := sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty
    bits N ((a^(2^i)) % N) ((ainv^(2^i)) % N) hbits hN_pos hN hN2 h_ainv_le h_inv_i
  unfold sqir_total_dim at h_mcp
  exact h_mcp

/-- **uc_well_typed for the bits-parameterized family.** -/
theorem f_modmult_circuit_verified_bits_uc_well_typed
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    ∀ i, FormalRV.SQIRPort.uc_well_typed (f_modmult_circuit_verified_bits a ainv N bits i) := by
  intro i
  unfold f_modmult_circuit_verified_bits
  apply uc_well_typed_toUCom_of_Gate_WellTyped
  have h_wt := sqir_modmult_MCP_gate_wellTyped bits N
    ((a^(2^i)) % N) ((ainv^(2^i)) % N) hbits hN_pos hN hN2
  unfold sqir_total_dim at h_wt
  exact h_wt

/-- **Verified Shor probability bound — bits-parameterized.**

If the user provides `BasicSetting a r N m bits` (which is generally
INCOMPATIBLE with our sizing requirement `2 * N ≤ 2^bits` — see the
documentation block above), the Shor success-probability bound holds
for the verified family at dimension `bits + sqir_modmult_rev_anc bits`.

In practice, both hypotheses can be simultaneously satisfied ONLY when
`2 * N = 2^bits` (i.e., `N` is a power of 2).  For general `N`, this
theorem is vacuous — see Status D in PROGRESS.md / Tick 80 commit. -/
theorem Shor_correct_with_sqir_verified_modmult_bits
    (a r N m bits ainv : Nat) (hbits : 1 ≤ bits)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m bits)
    (hN2 : 2 * N ≤ 2^bits)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
      (sqir_modmult_rev_anc bits)
      (f_modmult_circuit_verified_bits a ainv N bits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have h_basic_destruct := h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic_destruct
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _h_ord, _, hN_lt, _⟩ := h_basic_destruct
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have h_N_ge_2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h_lt | h_ge
    · exfalso
      have hN_eq : N = 1 := by omega
      rw [hN_eq, Nat.mod_one] at h_inv
      exact absurd h_inv (by decide)
    · exact h_ge
  have hN : N ≤ 2 ^ bits := Nat.le_of_lt hN_lt
  exact FormalRV.SQIRPort.Shor_correct_var a r N m bits
    (sqir_modmult_rev_anc bits) (f_modmult_circuit_verified_bits a ainv N bits)
    h_basic
    (f_modmult_circuit_verified_bits_MMI a ainv N bits hbits h_N_ge_2 hN hN2 h_inv)
    (fun i _ => f_modmult_circuit_verified_bits_uc_well_typed a ainv N bits
                  hbits hN_pos hN hN2 i)

/-! ## Tick 81 — Relaxed BasicSetting + sizing predicate.

### BasicSetting use-site review
After inspecting every theorem in the `Shor_correct_var` proof chain
that consumes `BasicSetting`, we find that **NO sub-lemma actually uses
the upper bound `2^n ≤ 2 * N`** mathematically.  The destructure pattern
in each case is `⟨⟨h_a_pos, h_a_lt⟩, h_ord, ⟨h_Nsq_lt, _⟩, _⟩` (or
similar), discarding the n-bound conjunct with `_`.  Concrete sites:
- `s_closest_ub` (line 956): destructures `_` for n-bound.
- `s_closest_injective` (line 988): same.
- `khinchin_applies_to_s_closest` (line 1236): same.
- `TODO_r_found_1_core_exact_rational` (line 3371): destructures
  `_h_pow_n` (named but unused).
- `TODO_r_found_1_core_generic` (line 3575): destructures `h_pow_n`
  and re-packs for `k_over_r_is_convergent`, which also discards it.

**Conclusion**: the `2^n ≤ 2 * N` conjunct is dead weight in the proof
chain.  A relaxed predicate that drops it admits the same proof. -/

/-- **Relaxed BasicSetting** without the tight upper bound `2^n ≤ 2*N`.
Keeps every conjunct mathematically used by the Shor proof.

**Deprecated 2026-05-29 (Phase R2):** use `VerifiedShor.ShorSetting`
for new code.  This definition is kept as the implementation;
`VerifiedShor.ShorSetting` is an `abbrev` for it. -/
def BasicSettingRelaxed (a r N m n : Nat) : Prop :=
  (0 < a ∧ a < N) ∧
  FormalRV.SQIRPort.Order a r N ∧
  (N^2 < 2^m ∧ 2^m ≤ 2 * N^2) ∧
  N < 2^n

/-- **Sizing predicate** for the verified SQIR modular multiplier.

**Deprecated 2026-05-29 (Phase R2):** use `VerifiedShor.CircuitSizing`
for new code.  This definition is kept as the implementation;
`VerifiedShor.CircuitSizing` is an `abbrev` for it. -/
def VerifiedCircuitSizing (N bits : Nat) : Prop :=
  1 ≤ bits ∧ N ≤ 2^bits ∧ 2*N ≤ 2^bits

/-- `BasicSetting → BasicSettingRelaxed` (drops the upper-bound conjunct). -/
theorem BasicSettingRelaxed_of_BasicSetting
    {a r N m n : Nat} (h : FormalRV.SQIRPort.BasicSetting a r N m n) :
    BasicSettingRelaxed a r N m n := by
  obtain ⟨ha, hord, hm, hn, _⟩ := h
  exact ⟨ha, hord, hm, hn⟩

/-- **Canonical sizing**: `bits = Nat.log2 N + 1` gives `2*N ≤ 2^bits`
when `N` is a power of 2 minus 1 or smaller; we use `Nat.log2 (2*N) + 1`
as a generic choice. -/
theorem VerifiedCircuitSizing_canonical_pow2_succ
    (N : Nat) (hN : 0 < N) :
    VerifiedCircuitSizing N (Nat.log2 (2 * N) + 1) := by
  set bits := Nat.log2 (2 * N) + 1 with h_bits_def
  have h_2N_pos : 0 < 2 * N := by omega
  have h_log2_le : 2 ^ (Nat.log2 (2 * N)) ≤ 2 * N := Nat.log2_self_le (by omega)
  have h_pow_bits_ge : 2 ^ bits = 2 * 2 ^ (Nat.log2 (2 * N)) := by
    rw [h_bits_def, pow_succ]; ring
  refine ⟨?_, ?_, ?_⟩
  · omega
  · have : N ≤ 2 * N := by omega
    have h_2N_le : 2 * N ≤ 2 ^ bits := by
      rw [h_pow_bits_ge]
      have h_strict : 2 * N < 2 ^ (Nat.log2 (2 * N) + 1) := Nat.lt_log2_self
      omega
    omega
  · rw [h_pow_bits_ge]
    have h_strict : 2 * N < 2 ^ (Nat.log2 (2 * N) + 1) := Nat.lt_log2_self
    omega

/-! ## Tick 81 — Relaxed sub-lemmas (copies of original proofs with
relaxed hypothesis). -/

/-- **Relaxed s_closest_ub.** -/
theorem s_closest_ub_relaxed (a r N m n k : Nat)
    (h_basic : BasicSettingRelaxed a r N m n) (h_k_lt : k < r) :
    FormalRV.SQIRPort.s_closest m k r < 2^m := by
  obtain ⟨⟨h_a_pos, h_a_lt_N⟩, h_ord, ⟨h_Nsq_lt, _⟩, _⟩ := h_basic
  have h_r_pos : 0 < r := h_ord.1
  have h_N_pos : 0 < N := by omega
  have h_r_lt_N : r < N := FormalRV.SQIRPort.Order_r_lt_N a r N h_N_pos h_ord
  have h_N_le_Nsq : N ≤ N^2 := by nlinarith
  have h_r_lt_2m : r < 2^m := by omega
  unfold FormalRV.SQIRPort.s_closest
  rw [Nat.div_lt_iff_lt_mul h_r_pos]
  have h_k_succ : k + 1 ≤ r := h_k_lt
  have h_k_mul : (k + 1) * 2^m ≤ r * 2^m := Nat.mul_le_mul_right _ h_k_succ
  have h_r_half : r / 2 < 2^m := by omega
  have h_expand : (k + 1) * 2^m = k * 2^m + 2^m := by ring
  have h_comm : r * 2^m = 2^m * r := Nat.mul_comm _ _
  omega

/-- **Relaxed s_closest_injective** — same proof as the original, just
adjusted for the relaxed hypothesis. -/
theorem s_closest_injective_relaxed
    (a r N m n : Nat) (h_basic : BasicSettingRelaxed a r N m n) :
    ∀ i j : Nat, i < r → j < r →
      FormalRV.SQIRPort.s_closest m i r = FormalRV.SQIRPort.s_closest m j r → i = j := by
  intros i j h_i h_j h_eq
  obtain ⟨⟨h_a_pos, h_a_lt_N⟩, h_ord, ⟨h_Nsq_lt, _⟩, _⟩ := h_basic
  have h_r_pos : 0 < r := h_ord.1
  have h_N_pos : 0 < N := by omega
  have h_r_lt_N : r < N := FormalRV.SQIRPort.Order_r_lt_N a r N h_N_pos h_ord
  have h_N_le_Nsq : N ≤ N^2 := by nlinarith
  have h_r_lt_2m : r < 2^m := by omega
  unfold FormalRV.SQIRPort.s_closest at h_eq
  have h_i_div : r * ((i * 2^m + r/2) / r) + (i * 2^m + r/2) % r = i * 2^m + r/2 :=
    Nat.div_add_mod (i * 2^m + r/2) r
  have h_j_div : r * ((j * 2^m + r/2) / r) + (j * 2^m + r/2) % r = j * 2^m + r/2 :=
    Nat.div_add_mod (j * 2^m + r/2) r
  have h_i_mod_lt : (i * 2^m + r/2) % r < r := Nat.mod_lt _ h_r_pos
  have h_j_mod_lt : (j * 2^m + r/2) % r < r := Nat.mod_lt _ h_r_pos
  rw [h_eq] at h_i_div
  rcases Nat.lt_trichotomy i j with h_lt | h_eq_ij | h_gt
  · exfalso
    have h_ij_step : i * 2^m + 2^m ≤ j * 2^m := by
      have h1 : i + 1 ≤ j := h_lt
      nlinarith
    have h_rearrange : i * 2^m + (j * 2^m + r/2) % r
                       = j * 2^m + (i * 2^m + r/2) % r := by omega
    omega
  · exact h_eq_ij
  · exfalso
    have h_ij_step : j * 2^m + 2^m ≤ i * 2^m := by
      have h1 : j + 1 ≤ i := h_gt
      nlinarith
    have h_rearrange : i * 2^m + (j * 2^m + r/2) % r
                       = j * 2^m + (i * 2^m + r/2) % r := by omega
    omega

/-- **Relaxed r_found_1**: Since the existing `r_found_1` proof chain
discards the n-bound throughout, it lifts to the relaxed setting via a
constructed-BasicSetting argument with a placeholder upper bound.

Pragmatic implementation: the existing `r_found_1` works at `BasicSetting`,
which requires `2^n ≤ 2*N`.  We don't have this, but the proof
doesn't use it.  Rather than re-proving the entire chain, we use the
relaxed-from-BasicSetting bridge in reverse: state the relaxed theorem
with an extra `(h_fake : 2^n ≤ 2*N)` parameter that we discard at call
sites by NOT using this lemma when the bound is unavailable.

For the SQIR `Shor_correct_var` chain, the bound IS available (since
BasicSetting holds), so the relaxed lemma can fall through to the
existing one.  For our verified family with `bits = n + 1`, the bound
is NOT available — but we sidestep this by USING THE EXISTING
`Shor_correct_var` AT `n = bits` where BasicSetting also holds, which
is the route we've taken in Tick 80. -/
theorem r_found_1_relaxed_with_bound
    (a r N m n k : Nat) (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_2n_bound : 2 ^ n ≤ 2 * N) (h_k_lt : k < r) (h_coprime : Nat.gcd k r = 1) :
    FormalRV.SQIRPort.r_found (FormalRV.SQIRPort.s_closest m k r) m r a N = 1 := by
  obtain ⟨ha, hord, hm, hn⟩ := h_basic_r
  exact FormalRV.SQIRPort.r_found_1 a r N m n k
    ⟨ha, hord, hm, hn, h_2n_bound⟩ h_k_lt h_coprime

/-! ## Tick 81 — Relaxed Shor_correct_var_relaxed_with_bound.

The relaxed variant still threads the `2^n ≤ 2*N` upper bound through
because `r_found_1` cannot yet be fully relaxed without re-proving the
continued-fraction chain.  However, the SIGNATURE makes the upper-bound
visible as a SEPARATE hypothesis, which clarifies the obstruction. -/

/-- **Relaxed Shor_correct_var (with bound)**: takes the upper bound
explicitly so that the proof obligations are visible. -/
theorem Shor_correct_var_relaxed_with_bound
    (a r N m n anc : Nat) (u : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_2n_bound : 2 ^ n ≤ 2 * N)
    (h_modmul : FormalRV.SQIRPort.ModMulImpl a N n anc u)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (u i)) :
    FormalRV.SQIRPort.probability_of_success a r N m n anc u
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  obtain ⟨ha, hord, hm, hn⟩ := h_basic_r
  exact FormalRV.SQIRPort.Shor_correct_var a r N m n anc u
    ⟨ha, hord, hm, hn, h_2n_bound⟩ h_modmul h_wt

/-! ## Tick 81 — Final verified Shor theorem with relaxed setup.

The final theorem cleanly SEPARATES:
- `BasicSettingRelaxed a r N m bits`: the Shor mathematical setup at
  data-register size `bits`.
- `VerifiedCircuitSizing N bits`: the verified-circuit sizing
  requirements.
- A residual `2 ^ bits ≤ 2 * N` hypothesis surfaced from the
  un-relaxed-yet `r_found_1` chain.

The residual hypothesis is the EXACT obstruction documented in the
Tick 80 caveat — it forces `2^bits = 2*N` (knife-edge case) when
combined with `VerifiedCircuitSizing`.  Future ticks would relax
`r_found_1` (via continued-fraction proof restructuring) to remove
this last constraint. -/
theorem Shor_correct_with_sqir_verified_modmult_relaxed
    (a r N m bits ainv : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m bits)
    (h_bits : VerifiedCircuitSizing N bits)
    (h_2n_bound : 2 ^ bits ≤ 2 * N)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
      (sqir_modmult_rev_anc bits)
      (f_modmult_circuit_verified_bits a ainv N bits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have hbits : 1 ≤ bits := h_bits.1
  have hN : N ≤ 2^bits := h_bits.2.1
  have hN2 : 2 * N ≤ 2^bits := h_bits.2.2
  have h_a_pos : 0 < a := h_basic_r.1.1
  have h_a_lt : a < N := h_basic_r.1.2
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have h_N_ge_2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h_lt | h_ge
    · exfalso
      have hN_eq : N = 1 := by omega
      rw [hN_eq, Nat.mod_one] at h_inv
      exact absurd h_inv (by decide)
    · exact h_ge
  exact Shor_correct_var_relaxed_with_bound a r N m bits
    (sqir_modmult_rev_anc bits) (f_modmult_circuit_verified_bits a ainv N bits)
    h_basic_r h_2n_bound
    (f_modmult_circuit_verified_bits_MMI a ainv N bits hbits h_N_ge_2 hN hN2 h_inv)
    (fun i _ => f_modmult_circuit_verified_bits_uc_well_typed a ainv N bits
                  hbits hN_pos hN hN2 i)

/-! ## Tick 82 — Canonical-n bridge + relaxed continued-fraction chain.

### Key insight
Lemma conclusions that do NOT mention `n` (e.g., `r_found_1`,
`s_closest_ub`) can be invoked at ANY `n` where `BasicSetting` holds.
From `BasicSettingRelaxed a r N m bits`, we construct
`BasicSetting a r N m (Nat.log2 (2*N))` (the canonical n where the
tight upper bound holds automatically), then invoke the original
theorems. -/

/-- **Canonical-n bridge**: From `BasicSettingRelaxed` at any `bits`, we
can construct `BasicSetting` at `n_canonical = Nat.log2 (2*N)`. -/
theorem BasicSetting_at_canonical_n_of_BasicSettingRelaxed
    (a r N m bits : Nat) (h_basic_r : BasicSettingRelaxed a r N m bits) :
    FormalRV.SQIRPort.BasicSetting a r N m (Nat.log2 (2 * N)) := by
  obtain ⟨⟨h_a_pos, h_a_lt⟩, h_ord, hm, _⟩ := h_basic_r
  have hN_pos : 0 < N := by omega
  refine ⟨⟨h_a_pos, h_a_lt⟩, h_ord, hm, ?_, ?_⟩
  · -- N < 2^log2(2N): from 2*N < 2^(log2(2N)+1) = 2 * 2^log2(2N).
    have h_lt : 2 * N < 2 ^ (Nat.log2 (2 * N) + 1) := Nat.lt_log2_self
    have h_eq : 2 ^ (Nat.log2 (2 * N) + 1) = 2 * 2 ^ Nat.log2 (2 * N) := by
      rw [pow_succ]; ring
    omega
  · exact Nat.log2_self_le (by omega : 2 * N ≠ 0)

/-- **Relaxed `r_found_1`**: same conclusion as the original, but
hypothesis weakened to `BasicSettingRelaxed`.  Uses the canonical-n
bridge since the conclusion `r_found (...) = 1` does not mention `n`. -/
theorem r_found_1_relaxed (a r N m bits k : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m bits)
    (h_k_lt : k < r) (h_coprime : Nat.gcd k r = 1) :
    FormalRV.SQIRPort.r_found (FormalRV.SQIRPort.s_closest m k r) m r a N = 1 :=
  FormalRV.SQIRPort.r_found_1 a r N m (Nat.log2 (2 * N)) k
    (BasicSetting_at_canonical_n_of_BasicSettingRelaxed a r N m bits h_basic_r)
    h_k_lt h_coprime

/-! ### Blocker for full relaxation: QPE_MMI_correct's deep machinery.

The review shows that `qpe_semantics_measurement_eq_from_lsb` (PostQFT.lean:3330),
`QPE_MMI_correct_modulo_qpe_semantics` (Shor.lean:4980), and
`QPE_MMI_correct_assuming_orbit_factorization` all use only
`h_n_bounds.1.le` (= `N ≤ 2^n`) from BasicSetting — never the upper
bound `2^n ≤ 2*N`.  However, relaxing them requires re-stating each
with `BasicSettingRelaxed` and updating callers; this is a 4-6 lemma
copy-modify chain that requires modifying Shor.lean/PostQFT.lean.

The Tick 82 review confirms the mathematical relaxability of the
entire chain.  Implementing it requires either:
- modifying Shor.lean / PostQFT.lean to weaken the BasicSetting
  hypothesis everywhere (invasive);
- or duplicating ~200-300 lines of proof scaffolding in this file.

For Tick 82, we land the canonical-n bridge + `r_found_1_relaxed`
(which removes one of the residual obstructions) but the QPE_MMI
chain remains a future-tick blocker.  Status B per task spec. -/

/-! ## Tick 83 — Relaxed QPE_MMI chain. -/

/-! ### Task 2 — Lower-sizing extraction lemmas from BasicSettingRelaxed. -/

theorem BasicSettingRelaxed_a_pos
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : 0 < a := h.1.1

theorem BasicSettingRelaxed_a_lt
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : a < N := h.1.2

theorem BasicSettingRelaxed_order
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) :
    FormalRV.SQIRPort.Order a r N := h.2.1

theorem BasicSettingRelaxed_Nsq_lt
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : N^2 < 2^m := h.2.2.1.1

theorem BasicSettingRelaxed_pow_le_2Nsq
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : 2^m ≤ 2 * N^2 := h.2.2.1.2

theorem BasicSettingRelaxed_N_lt_pow_n
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : N < 2^n := h.2.2.2

theorem BasicSettingRelaxed_N_le_pow_n
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : N ≤ 2^n :=
  (BasicSettingRelaxed_N_lt_pow_n h).le

theorem BasicSettingRelaxed_N_pos
    {a r N m n : Nat} (h : BasicSettingRelaxed a r N m n) : 0 < N :=
  Nat.lt_of_lt_of_le (BasicSettingRelaxed_a_pos h) (Nat.le_of_lt (BasicSettingRelaxed_a_lt h))

/-! ### Task 3 — Relaxed qpe_semantics_measurement_eq_from_lsb. -/

theorem qpe_semantics_measurement_eq_from_lsb_relaxed
    (a r N m n anc k : Nat)
    (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_modmul : FormalRV.SQIRPort.ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (f i)) :
    FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.Framework.basis_vector (2^m)
          (FormalRV.SQIRPort.s_closest m k r))
        (FormalRV.SQIRPort.Shor_final_state m n anc f)
    = FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.Framework.basis_vector (2^m)
          (FormalRV.SQIRPort.s_closest m k r))
        (FormalRV.SQIRPort.shor_orbit_state a r N m n anc) := by
  obtain ⟨h_r_pos, h_arN, h_min⟩ := BasicSettingRelaxed_order h_basic_r
  have h_N_pos : 0 < N := BasicSettingRelaxed_N_pos h_basic_r
  have h_N_gt_one : 1 < N := by
    have := BasicSettingRelaxed_a_lt h_basic_r
    have := BasicSettingRelaxed_a_pos h_basic_r
    omega
  have h_N_lt_pow : N ≤ 2^n := BasicSettingRelaxed_N_le_pow_n h_basic_r
  have hm : 0 < m := by
    have h_Nsq_lt : N^2 < 2^m := BasicSettingRelaxed_Nsq_lt h_basic_r
    have h_Nsq_pos : 0 < N^2 := by positivity
    by_contra h
    push_neg at h
    interval_cases m
    simp at h_Nsq_lt
    omega
  have hmanc : 0 < m + (n + anc) := by omega
  have h_state_eq : FormalRV.SQIRPort.Shor_final_state m n anc f
      = FormalRV.SQIRPort.QState.cast (by rw [pow_add, pow_add, mul_assoc])
          (FormalRV.SQIRPort.shor_orbit_state a r N m n anc) := by
    show FormalRV.SQIRPort.Shor_final_state_lsb m n anc f = _
    exact FormalRV.SQIRPort.Shor_final_state_lsb_eq_shor_orbit_state
      a r N m n anc hmanc hm h_r_pos h_arN h_min h_N_gt_one h_N_lt_pow h_N_pos
      f h_modmul (fun i hi => h_wt i hi)
  rw [h_state_eq, FormalRV.SQIRPort.prob_partial_meas_cast]

/-! ### Task 5 — Relaxed QPE_MMI_correct_from_Shor_orbit_state. -/

theorem QPE_MMI_correct_from_Shor_orbit_state_relaxed
    (a r N m n anc k : Nat)
    (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (β : Fin r → Matrix (Fin (2^(n + anc))) (Fin 1) ℂ)
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (_h_mmi : FormalRV.SQIRPort.ModMulImpl a N n anc f)
    (_h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_orth : ∀ j j' : Fin r,
       ∑ y : Fin (2^(n + anc)), starRingEnd ℂ ((β j') y 0) * (β j) y 0
       = if j = j' then (1 : ℂ) else 0)
    (actual_state : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ)
    (h_state : actual_state =
      fun i j => (1 / (Real.sqrt r : ℂ)) *
        ((∑ j_idx : Fin r,
           FormalRV.Framework.kron_vec
             (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
             (β j_idx) :
           Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ) i j)) :
    FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.Framework.basis_vector (2^m)
          (FormalRV.SQIRPort.s_closest m k r)) actual_state
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  have h_r_pos : 0 < r := (BasicSettingRelaxed_order h_basic_r).1
  have h_s_lt : FormalRV.SQIRPort.s_closest m k r < 2^m :=
    s_closest_ub_relaxed a r N m n k h_basic_r h_k_lt
  exact FormalRV.SQIRPort.QPE_MMI_correct_from_orbit_state_eq k h_k_lt h_r_pos h_s_lt
    β h_orth actual_state h_state

/-! ### Task 5 (cont.) — Relaxed QPE_MMI_correct_assuming_orbit_factorization. -/

theorem QPE_MMI_correct_assuming_orbit_factorization_relaxed
    (a r N m n anc k : Nat)
    (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_mmi : FormalRV.SQIRPort.ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_orbit_exists :
        ∃ (β : Fin r → Matrix (Fin (2^(n + anc))) (Fin 1) ℂ)
          (actual_state : Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ),
          ((∀ j j' : Fin r,
             ∑ y : Fin (2^(n + anc)),
                  starRingEnd ℂ ((β j') y 0) * (β j) y 0
             = if j = j' then (1 : ℂ) else 0)
          ∧ (actual_state = fun i j => (1 / (Real.sqrt r : ℂ)) *
              ((∑ j_idx : Fin r,
                 FormalRV.Framework.kron_vec
                   (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
                   (β j_idx) :
                 Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ) i j))
          ∧ (FormalRV.SQIRPort.prob_partial_meas
                (FormalRV.Framework.basis_vector (2^m)
                  (FormalRV.SQIRPort.s_closest m k r))
                (FormalRV.SQIRPort.Shor_final_state m n anc f)
              = FormalRV.SQIRPort.prob_partial_meas
                  (FormalRV.Framework.basis_vector (2^m)
                    (FormalRV.SQIRPort.s_closest m k r))
                  actual_state))) :
    FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.Framework.basis_vector (2^m)
          (FormalRV.SQIRPort.s_closest m k r))
        (FormalRV.SQIRPort.Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  obtain ⟨β, actual_state, h_orth, h_state, h_prob_eq⟩ := h_orbit_exists
  rw [h_prob_eq]
  exact QPE_MMI_correct_from_Shor_orbit_state_relaxed a r N m n anc k f β
    h_basic_r h_mmi h_wt h_k_lt h_orth actual_state h_state

/-! ### Task 4 — Relaxed QPE_MMI_correct_modulo_qpe_semantics. -/

theorem QPE_MMI_correct_modulo_qpe_semantics_relaxed
    (a r N m n anc k : Nat)
    (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_mmi : FormalRV.SQIRPort.ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_qpe_semantics :
      FormalRV.SQIRPort.prob_partial_meas
          (FormalRV.Framework.basis_vector (2^m)
            (FormalRV.SQIRPort.s_closest m k r))
          (FormalRV.SQIRPort.Shor_final_state m n anc f)
        = FormalRV.SQIRPort.prob_partial_meas
            (FormalRV.Framework.basis_vector (2^m)
              (FormalRV.SQIRPort.s_closest m k r))
            (FormalRV.SQIRPort.shor_orbit_state a r N m n anc)) :
    FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.Framework.basis_vector (2^m)
          (FormalRV.SQIRPort.s_closest m k r))
        (FormalRV.SQIRPort.Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  apply QPE_MMI_correct_assuming_orbit_factorization_relaxed a r N m n anc k f
    h_basic_r h_mmi h_wt h_k_lt
  obtain ⟨h_r_pos, h_arN, h_min⟩ := BasicSettingRelaxed_order h_basic_r
  have h_N_pos : 0 < N := BasicSettingRelaxed_N_pos h_basic_r
  have h_N_gt_one : 1 < N := by
    have := BasicSettingRelaxed_a_lt h_basic_r
    have := BasicSettingRelaxed_a_pos h_basic_r
    omega
  have h_N_lt_pow : N ≤ 2^n := BasicSettingRelaxed_N_le_pow_n h_basic_r
  refine ⟨FormalRV.SQIRPort.modmult_eigenstate_combined a r N n anc,
          FormalRV.SQIRPort.shor_orbit_state a r N m n anc, ?_, rfl, h_qpe_semantics⟩
  intros j j'
  exact FormalRV.SQIRPort.modmult_eigenstate_combined_orthonormal a r N n anc
    h_r_pos h_arN h_min h_N_gt_one h_N_lt_pow j j'

/-! ### Task 6 — Relaxed QPE_MMI_correct. -/

theorem QPE_MMI_correct_relaxed
    (a r N m n anc k : Nat)
    (f : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_mmi : FormalRV.SQIRPort.ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (f i))
    (h_k_lt : k < r) :
    FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.Framework.basis_vector (2^m)
          (FormalRV.SQIRPort.s_closest m k r))
        (FormalRV.SQIRPort.Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  apply QPE_MMI_correct_modulo_qpe_semantics_relaxed a r N m n anc k f
    h_basic_r h_mmi h_wt h_k_lt
  exact qpe_semantics_measurement_eq_from_lsb_relaxed a r N m n anc k f h_basic_r h_mmi h_wt

/-! ### Task 7 — Fully relaxed parametric Shor theorem.

Re-proves the body of `Shor_correct_var_conditional` with sub-lemma
calls replaced by their `_relaxed` variants. -/

theorem Shor_correct_var_relaxed
    (a r N m n anc : Nat) (u : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic_r : BasicSettingRelaxed a r N m n)
    (h_modmul : FormalRV.SQIRPort.ModMulImpl a N n anc u)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (u i)) :
    FormalRV.SQIRPort.probability_of_success a r N m n anc u
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have h_a_pos : 0 < a := BasicSettingRelaxed_a_pos h_basic_r
  have h_a_lt : a < N := BasicSettingRelaxed_a_lt h_basic_r
  obtain ⟨h_r_pos, h_arN, h_min⟩ := BasicSettingRelaxed_order h_basic_r
  have h_N_pos : 0 < N := BasicSettingRelaxed_N_pos h_basic_r
  have h_r_lt_N : r < N := FormalRV.SQIRPort.Order_r_lt_N a r N h_N_pos
    ⟨h_r_pos, h_arN, h_min⟩
  have h_r_le_N : r ≤ N := Nat.le_of_lt h_r_lt_N
  have h_r_pos_R : (0 : ℝ) < r := by exact_mod_cast h_r_pos
  have h_r_ne_R : (r : ℝ) ≠ 0 := ne_of_gt h_r_pos_R
  -- The integrand
  set f : Nat → ℝ := fun x =>
      FormalRV.SQIRPort.r_found x m r a N *
        FormalRV.SQIRPort.prob_partial_meas
          (FormalRV.Framework.basis_vector (2^m) x)
          (FormalRV.SQIRPort.Shor_final_state m n anc u)
    with hf_def
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    refine mul_nonneg ?_ (FormalRV.SQIRPort.prob_partial_meas_nonneg _ _)
    unfold FormalRV.SQIRPort.r_found
    split_ifs <;> norm_num
  -- Step 1: subset+injectivity using _relaxed versions.
  have h_step1 :
      ∑ i ∈ Finset.range r, f (FormalRV.SQIRPort.s_closest m i r)
        ≤ ∑ x ∈ Finset.range (2^m), f x := by
    rw [show (∑ i ∈ Finset.range r, f (FormalRV.SQIRPort.s_closest m i r))
          = ∑ x ∈ (Finset.range r).image (fun i => FormalRV.SQIRPort.s_closest m i r), f x
            from ?_]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        rw [Finset.mem_range] at hi ⊢
        exact s_closest_ub_relaxed a r N m n i h_basic_r hi
      · intro x _ _; exact hf_nonneg x
    · rw [Finset.sum_image]
      intros i hi j hj heq
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      exact s_closest_injective_relaxed a r N m n h_basic_r i j hi hj heq
  -- Step 2: per-term bound using QPE_MMI_correct_relaxed.
  set g : Nat → ℝ := fun i =>
    (if Nat.gcd i r = 1 then (1 : ℝ) else 0) * (4 / (Real.pi^2 * (r : ℝ)))
    with hg_def
  have h_step2 :
      ∀ i ∈ Finset.range r, g i ≤ f (FormalRV.SQIRPort.s_closest m i r) := by
    intro i hi
    rw [Finset.mem_range] at hi
    show g i ≤ f (FormalRV.SQIRPort.s_closest m i r)
    by_cases hcop : Nat.gcd i r = 1
    · show (if Nat.gcd i r = 1 then (1:ℝ) else 0) * (4 / (Real.pi^2 * (r:ℝ)))
            ≤ FormalRV.SQIRPort.r_found
                (FormalRV.SQIRPort.s_closest m i r) m r a N *
                FormalRV.SQIRPort.prob_partial_meas
                  (FormalRV.Framework.basis_vector (2^m)
                    (FormalRV.SQIRPort.s_closest m i r))
                  (FormalRV.SQIRPort.Shor_final_state m n anc u)
      rw [if_pos hcop, one_mul]
      have h_rf : FormalRV.SQIRPort.r_found
          (FormalRV.SQIRPort.s_closest m i r) m r a N = 1 :=
        r_found_1_relaxed a r N m n i h_basic_r hi hcop
      rw [h_rf, one_mul]
      exact QPE_MMI_correct_relaxed a r N m n anc i u h_basic_r h_modmul h_wt hi
    · show (if Nat.gcd i r = 1 then (1:ℝ) else 0) * (4 / (Real.pi^2 * (r:ℝ)))
            ≤ f (FormalRV.SQIRPort.s_closest m i r)
      rw [if_neg hcop, zero_mul]
      exact hf_nonneg _
  -- Step 3: Σ g over [0, r) = (4/(π²·r)) · ϕ(r)
  have h_step3 :
      ∑ i ∈ Finset.range r, g i
        = (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ) := by
    show (∑ i ∈ Finset.range r,
           (if Nat.gcd i r = 1 then (1:ℝ) else 0) * (4 / (Real.pi^2 * (r:ℝ))))
          = (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ)
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    rw [Nat.totient]
    push_cast
    rw [show ((Finset.range r).filter (Nat.Coprime r)).card
          = ((Finset.range r).filter (fun i => Nat.gcd i r = 1)).card from ?_]
    · rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
          Nat.smul_one_eq_cast, Finset.filter_congr_decidable]
    · congr 1; ext i; simp [Nat.Coprime, Nat.coprime_comm]
  -- Step 4: bound by Euler totient
  have h_step4 :
      (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ)
        ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
    have h_phi : ((Nat.totient r : ℝ) / (r : ℝ))
                  ≥ Real.exp (-2) / (Nat.log2 N : ℝ)^4 :=
      FormalRV.SQIRPort.phi_n_over_n_lowerbound r N h_r_pos h_r_le_N
    have h_pi_sq : (0 : ℝ) < Real.pi^2 := pow_pos Real.pi_pos 2
    have h_rewrite :
        (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ)
          = (4 / Real.pi^2) * ((Nat.totient r : ℝ) / (r : ℝ)) := by
      field_simp
    rw [h_rewrite]
    have h_κ : FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4
              = (4 / Real.pi^2) * (Real.exp (-2) / (Nat.log2 N : ℝ)^4) := by
      unfold FormalRV.SQIRPort.κ; field_simp
    rw [h_κ]
    apply mul_le_mul_of_nonneg_left h_phi
    positivity
  unfold FormalRV.SQIRPort.probability_of_success
  calc FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4
      ≤ (4 / (Real.pi^2 * (r : ℝ))) * (Nat.totient r : ℝ) := h_step4
    _ = ∑ i ∈ Finset.range r, g i := h_step3.symm
    _ ≤ ∑ i ∈ Finset.range r, f (FormalRV.SQIRPort.s_closest m i r) :=
          Finset.sum_le_sum h_step2
    _ ≤ ∑ x ∈ Finset.range (2^m), f x := h_step1

/-! ### Task 8 — Final usable verified SQIR Shor theorem. -/

/-- **Fully usable verified SQIR Shor theorem** — no residual upper
bound on `2^bits` from BasicSetting. -/
theorem Shor_correct_with_sqir_verified_modmult_usable
    (a r N m bits ainv : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m bits)
    (h_sizing : VerifiedCircuitSizing N bits)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
      (sqir_modmult_rev_anc bits)
      (f_modmult_circuit_verified_bits a ainv N bits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have hbits : 1 ≤ bits := h_sizing.1
  have hN : N ≤ 2^bits := h_sizing.2.1
  have hN2 : 2 * N ≤ 2^bits := h_sizing.2.2
  have hN_pos : 0 < N := BasicSettingRelaxed_N_pos h_basic_r
  have h_N_ge_2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h_lt | h_ge
    · exfalso
      have hN_eq : N = 1 := by omega
      rw [hN_eq, Nat.mod_one] at h_inv
      exact absurd h_inv (by decide)
    · exact h_ge
  exact Shor_correct_var_relaxed a r N m bits
    (sqir_modmult_rev_anc bits) (f_modmult_circuit_verified_bits a ainv N bits)
    h_basic_r
    (f_modmult_circuit_verified_bits_MMI a ainv N bits hbits h_N_ge_2 hN hN2 h_inv)
    (fun i _ => f_modmult_circuit_verified_bits_uc_well_typed a ainv N bits
                  hbits hN_pos hN hN2 i)

/-! ### Task 9 — Canonical bits corollary. -/

/-- **Canonical-bits corollary**: bits = `Nat.log2 (2*N) + 1`. -/
theorem Shor_correct_with_sqir_verified_modmult_canonical_bits
    (a r N m ainv : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m (Nat.log2 (2*N) + 1))
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m (Nat.log2 (2*N) + 1)
      (sqir_modmult_rev_anc (Nat.log2 (2*N) + 1))
      (f_modmult_circuit_verified_bits a ainv N (Nat.log2 (2*N) + 1))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have hN_pos : 0 < N := BasicSettingRelaxed_N_pos h_basic_r
  exact Shor_correct_with_sqir_verified_modmult_usable a r N m
    (Nat.log2 (2*N) + 1) ainv h_basic_r
    (VerifiedCircuitSizing_canonical_pow2_succ N hN_pos) h_inv

/-! ## Tick 84 — Final review, alias, and Phase summary.

### Documentation: which Shor theorem to cite

The original SQIR `Shor_correct` and `Shor_correct_var` theorems
(`PostQFT.lean`) depend on the placeholder axioms
`f_modmult_circuit`, `f_modmult_circuit_MMI`, and
`f_modmult_circuit_uc_well_typed` (declared in `Shor.lean:4570-4711`).
Confirmed by `lean_verify Shor_correct` listing these axioms.

The **verified** Shor theorem to cite for the kernel-clean,
axiom-free result is one of:

- `Shor_correct_with_sqir_verified_modmult_usable`: takes
  `BasicSettingRelaxed`, `VerifiedCircuitSizing`, and the modular
  inverse hypothesis.
- `Shor_correct_with_sqir_verified_modmult_canonical_bits`: same but
  the sizing is auto-discharged at `bits = Nat.log2 (2*N) + 1`.

These theorems use the verified SQIR modular multiplier
(`f_modmult_circuit_verified_bits` → `sqir_modmult_MCP_gate`) and
NOT the placeholder `f_modmult_circuit`.  Their axiom dependency is
exactly `[propext, Classical.choice, Quot.sound]` (the standard kernel).

**Do not cite `Shor_correct` or `Shor_correct_var` as the verified
result** — they remain in the codebase for historical compatibility
but rely on placeholder axioms. -/

/-- **Verified Shor's algorithm correctness theorem (no placeholder
axioms).**  Alias for `Shor_correct_with_sqir_verified_modmult_canonical_bits`
under a name that signals its axiom-free status. -/
theorem Shor_correct_verified_no_modmult_axioms
    (a r N m ainv : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m (Nat.log2 (2*N) + 1))
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m (Nat.log2 (2*N) + 1)
      (sqir_modmult_rev_anc (Nat.log2 (2*N) + 1))
      (f_modmult_circuit_verified_bits a ainv N (Nat.log2 (2*N) + 1))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 :=
  Shor_correct_with_sqir_verified_modmult_canonical_bits a r N m ainv h_basic_r h_inv

/-! ## Verified Shor pipeline — Phase summary

This Lean development verifies a full Shor-algorithm
success-probability bound for an SQIR-style modular multiplier
without using the placeholder modular-multiplier axioms.

### Phase 1: Cuccaro/SQIR modular addition
- `sqir_style_modAddConst_clean_candidate_clean`
  (`CuccaroSQIRDirtyFlag.lean`): correctness + clean-workspace
  bundle for the SQIR-faithful clean-flag modular addition.
- Carry-in restoration:
  `sqir_style_modAddConst_clean_candidate_carry_in_restored`
  (this file).

### Phase 2: controlled modular addition
- `sqir_style_controlledModAddConst_gate_clean`
  (`CuccaroSQIRDirtyFlag.lean`): WellTyped + target + read + flags
  + top carry + controlIdx-preservation bundle.
- `sqir_style_controlledModAddConst_gate_carry_in_restored`
  (this file).

### Phase 3: modular multiplier
- `sqir_modmult_const_gate_target_decode` / `_state_eq` /
  `_clean`: target decoded to `(a*m) % N`, state-equality, and
  full clean bundle.
- `sqir_modmult_inplace_candidate_state_eq` /
  `_target_decode` / `_clean`: in-place wrapper
  `x ↦ (a*x) % N`.

### Phase 4: MCP-layout bridge
- `sqir_modmult_MCP_gate_apply_encode` /
  `_satisfies_MultiplyCircuitProperty`: composed via
  `sqir_encode_to_mult_adapter` (a `reverse_register_swap`
  with bit-order reversal) + `Gate.shift`.

### Phase 5: relaxed verified Shor theorem
- `BasicSettingRelaxed`, `VerifiedCircuitSizing` (this file).
- `r_found_1_relaxed`, `QPE_MMI_correct_relaxed`,
  `Shor_correct_var_relaxed`.
- HEADLINE: `Shor_correct_with_sqir_verified_modmult_usable` and
  `_canonical_bits`.
- ALIAS: `Shor_correct_verified_no_modmult_axioms`.

### Axiom independence
All five Phase summaries land kernel-clean
(`axioms ⊆ [propext, Classical.choice, Quot.sound]`).  The original
SQIR placeholder axioms (`f_modmult_circuit`, `f_modmult_circuit_MMI`,
`f_modmult_circuit_uc_well_typed` at `Shor.lean:4570-4711`) remain
declared for historical compatibility but are NOT used by any
theorem in this verified pipeline. -/

/-! ## Tick 75 status note.

Landed in Tick 75:
- Deliverable A — `sqir_modmult_step_preserves_all_control_bits`:
  all multiplier control bits preserved by one step.  Generalizes
  Tick 74's Deliverable D from `k = j` to all `k < bits`.
- Function-level commute helper
  `sqir_style_controlledModAddConst_gate_commute_install`: cleaner
  primitive that subsumes the position-wise install commute helpers.
- Deliverable B — `sqir_modmult_step_state_normal`: combined finite-
  state characterization (target_val, read_val, flag, top carry, all
  control bits) at the workspace + multiplier positions.
- Deliverable E — `sqir_modmult_acc_spec_eq_mul_mod`: arithmetic
  proof that the accumulator spec equals `(a * m) % N` for
  `m < 2^bits`.  Uses `nat_mod_two_pow_succ_eq` (existing in
  `RippleCarryAdder.lean`).

Blockers for Tick 76 (full prefix theorem):
- Deliverable C (prefix invariant by induction) requires
  `sqir_modmult_step_state_eq` (full function equality):
  ```
  Gate.applyNat (sqir_modmult_step_gate bits N a j) (sqir_mult_input_F bits m acc)
    = sqir_mult_input_F bits m acc'
  ```
  This requires:
  1. **Per-bit converse for `cuccaro_target_val`/`read_val`**: a lemma
     of the form "if `target_val f = S < 2^bits`, then for `i < bits`
     `f (q_start + 2*i + 1) = S.testBit i`".  Tractable (uses
     `Nat.testBit_two_pow_add_eq` + `Nat.testBit_two_pow_add_gt`).
  2. **Carry-in restoration**: a theorem
     `applyNat (sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1)
        (update (cuccaro_input_F 2 false 0 x) controlIdx control) 2 = false`.
     For `control = false`, follows from
     `sqir_style_controlledModAddConst_candidate_control_false_state_eq`
     (identity).  For `control = true`, requires tracking carry-in
     restoration through all stages; the Cuccaro `_carry_in_restored`
     theorem is the building block.
  3. **Above-multiplier invariance**: for `q ≥ 2 + 2*bits + 1 + bits`,
     gate output equals input (`false` for `sqir_mult_input_F`).
     Tractable via `commute_update_outside_fun` + `update_self`.
  4. **Position-0 invariance**: same trick as above-multiplier.

Once `sqir_modmult_step_state_eq` lands, prefix induction is trivial
(base = identity on input, step = step_state_eq composed with IH).
Then Deliverables D (corollary), F (D + E), G (clean bundle), and H
(BasicSetting specialization) follow mechanically. -/

/-! ## Status note (Tick 73).

Landed:
- Layout: `sqir_mult_control_idx`, disjointness + dimension lemmas.
- Input encoding: `sqir_mult_input_F` with target/read/flag/top
  carry sanity decoders.
- Step gate: `sqir_modmult_step_gate`.
- Accumulator spec: `sqir_modmult_acc_spec` with recurrence +
  in-bound lemmas.
- Prefix gate skeleton + total wrapper:
  `sqir_modmult_prefix_gate`, `sqir_modmult_const_gate`.

NOT yet landed (Tick 74 work):
- One-step target_decode theorem
  (`sqir_modmult_step_target_decode`): requires a bridge between
  `sqir_mult_input_F` (which carries the full multiplier register)
  and the controlled mod-add's input form
  `update (cuccaro_input_F 2 false 0 acc) controlIdx (m.testBit j)`.
  The simplest bridge uses the controlled gate's commutativity
  with `update` at outside positions (Tick 71 stack extended to
  `sqir_style_controlledModAddConst_gate`).
- Workspace/control preservation through the step.
- Prefix invariant theorem
  (`sqir_modmult_prefix_target_decode`).

This is incremental Phase 4 startup. -/

end FormalRV.BQAlgo
