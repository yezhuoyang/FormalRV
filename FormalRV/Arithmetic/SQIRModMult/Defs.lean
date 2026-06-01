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

/-! ## Tick 73 — Prefix multiplier gate (skeleton). -/

/-- Multiplier prefix gate: applies `sqir_modmult_step_gate` for
`j = 0, 1, ..., k-1` in order. -/
def sqir_modmult_prefix_gate (bits N a : Nat) : Nat → Gate
  | 0       => Gate.I
  | k + 1   => seq (sqir_modmult_prefix_gate bits N a k) (sqir_modmult_step_gate bits N a k)

/-- The full multiplier gate (process all `bits` multiplier bits). -/
def sqir_modmult_const_gate (bits N a : Nat) : Gate :=
  sqir_modmult_prefix_gate bits N a bits

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

/-- q_start-parametric one-step modular-multiplier gate.  Conditionally
adds `(a * 2^j) % N` to the accumulator at workspace q_start = `q_start`,
controlled by the multiplier bit at
`sqir_mult_control_idx_qstart bits q_start j`, with dirty flag at
`flagPos`.  Port of `sqir_modmult_step_gate` (line 178). -/
def sqir_modmult_step_gate_qstart (bits q_start N a j flagPos : Nat) : Gate :=
  sqir_style_controlledModAddConst_gate bits q_start N ((a * 2 ^ j) % N)
    (sqir_mult_control_idx_qstart bits q_start j) flagPos

/-! ## Tick 74 — Multiplier-bit install helper for bridging. -/

/-- Recursively install multiplier bits `k = 0, ..., num_bits - 1` from `m`,
**skipping** bit `j`. -/
def install_mult_bits_skip_j (bits m j : Nat) : Nat → (Nat → Bool) → (Nat → Bool)
  | 0,     f => f
  | n + 1, f =>
    if n = j then install_mult_bits_skip_j bits m j n f
    else update (install_mult_bits_skip_j bits m j n f) (sqir_mult_control_idx bits n) (m.testBit n)

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

/-- q_start-parametric prefix gate.  Applies
`sqir_modmult_step_gate_qstart` for `j = 0, 1, ..., k - 1` in order.
Port of `sqir_modmult_prefix_gate` (line 228). -/
def sqir_modmult_prefix_gate_qstart
    (bits q_start N a flagPos : Nat) : Nat → Gate
  | 0       => Gate.I
  | k + 1   => seq (sqir_modmult_prefix_gate_qstart bits q_start N a flagPos k)
                   (sqir_modmult_step_gate_qstart bits q_start N a k flagPos)

/-- q_start-parametric full multiplier gate.  Process all `bits`
multiplier bits.  Port of `sqir_modmult_const_gate` (line 242). -/
def sqir_modmult_const_gate_qstart (bits q_start N a flagPos : Nat) : Gate :=
  sqir_modmult_prefix_gate_qstart bits q_start N a flagPos bits

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

/-! ### q_start swap-register definitions. -/

/-- q_start-parametric: index of the accumulator (target) bit `i` in
the Cuccaro layout.  Port of `sqir_target_idx`. -/
def sqir_target_idx_qstart (q_start i : Nat) : Nat := q_start + 2 * i + 1

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

/-! ## Tick 77 — Task 2: Accumulator↔Multiplier register swap. -/

/-- Index of the accumulator (target) bit `i` in the SQIR layout. -/
def sqir_target_idx (i : Nat) : Nat := 2 + 2 * i + 1

/-- Recursive swap of accumulator bits `[0, k)` with multiplier bits `[0, k)`. -/
def sqir_swap_acc_mult_aux (bits : Nat) : Nat → Gate
  | 0     => Gate.I
  | k + 1 => Gate.seq (sqir_swap_acc_mult_aux bits k)
                      (qubit_swap (sqir_target_idx k) (sqir_mult_control_idx bits k))

/-- Full SWAP of accumulator (target) register with multiplier register. -/
def sqir_swap_acc_mult (bits : Nat) : Gate :=
  sqir_swap_acc_mult_aux bits bits

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

/-! ## Tick 78 — Task 2: Gate.shift. -/

/-- Shift all gate positions up by `off`. -/
def Gate.shift (off : Nat) : Gate → Gate
  | Gate.I        => Gate.I
  | Gate.X q      => Gate.X (off + q)
  | Gate.CX a b   => Gate.CX (off + a) (off + b)
  | Gate.CCX a b c => Gate.CCX (off + a) (off + b) (off + c)
  | Gate.seq g h  => Gate.seq (Gate.shift off g) (Gate.shift off h)

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

/-! ## Tick 78 — Task 4: Shifted in-place multiplier. -/

/-- **Shifted in-place modular multiplier gate.** -/
def sqir_modmult_inplace_shifted (bits N a ainv : Nat) : Gate :=
  Gate.shift bits (sqir_modmult_inplace_candidate bits N a ainv)

/-! ## Tick 78 — Task 5/6: Full MCP-layout gate. -/

/-- **MCP-layout gate.**  Three-stage composition:
adapter → shifted in-place multiplier → adapter. -/
def sqir_modmult_MCP_gate (bits N a ainv : Nat) : Gate :=
  Gate.seq (sqir_encode_to_mult_adapter bits)
    (Gate.seq (sqir_modmult_inplace_shifted bits N a ainv)
              (sqir_encode_to_mult_adapter bits))

/-- **Verified modular-multiplier oracle family** at SQIR-faithful
dimension `(n + 1) + sqir_modmult_rev_anc (n + 1)`. -/
noncomputable def f_modmult_circuit_verified (a ainv N n : Nat) :
    Nat → FormalRV.Framework.BaseUCom ((n + 1) + sqir_modmult_rev_anc (n + 1)) :=
  fun i =>
    Gate.toUCom ((n + 1) + sqir_modmult_rev_anc (n + 1))
      (sqir_modmult_MCP_gate (n + 1) N ((a^(2^i)) % N) ((ainv^(2^i)) % N))

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
