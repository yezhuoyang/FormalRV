/- WindowedLoaderBitExtraction — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.WindowedLoaderBitExtraction.ParametricSelectedAddFrame

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ### State-builder reconstruction lemma

The data-preservation theorem uses the observation that updating a
state at position `p` and then applying the gate is the same as
applying the gate first and then updating at `p`, provided `p` is
disjoint from the gate's support. This is exactly the L-2′ frame
theorem. The state-builder reconstruction shows we can express
`gidneyComputeInput bits x acc` as the underlying `cuccaro_input_F`
base with successive data-position updates — but we don't actually
need this; the direct evaluation at q for the gate's output state
follows from a single application of L-2′. -/

/-- **PRIMARY L-3′ THEOREM: data-position preservation under the
shifted-workspace selected-add gate.**

At any data position `q < bits` other than the active window
controls `gidneyB0Idx bits k` and `gidneyB1Idx bits k`, the gate
preserves the value of `gidneyComputeInput bits x acc q`.

The proof is a single application of the L-2′ data-position frame
theorem (`toyWindow2SelectedAddGate_qstart_commute_update_data_disjoint`)
applied to the difference between the input state and a "zeroed at
q" state. -/
theorem toyWindow2SelectedAddGate_qstart_preserves_data_at_disjoint
    (bits N a k acc x q : Nat)
    (hwin : 2 * k + 1 < bits)
    (hq : q < bits)
    (hq_ne_b0 : q ≠ gidneyB0Idx bits k)
    (hq_ne_b1 : q ≠ gidneyB1Idx bits k) :
    Gate.applyNat
        (toyWindow2SelectedAddGate_qstart bits bits N a k
          (gidneyFlagPos bits) (gidneyFlagPos bits)
          (gidneyB0Idx bits k) (gidneyB1Idx bits k))
        (gidneyComputeInput bits x acc) q
      = gidneyComputeInput bits x acc q := by
  -- Strategy: express gidneyComputeInput as
  --   update (substateWithQReplaced) q (gidneyComputeInput bits x acc q)
  -- Then apply L-2′ to commute the gate past the outer update, since
  -- q is disjoint from b0Idx, b1Idx, flagPos.
  -- The update commutes through the gate; reading at q gives the
  -- assigned value, which is the original gidneyComputeInput value at q.
  set f := gidneyComputeInput bits x acc with hf_def
  have h_self : update f q (f q) = f := FormalRV.Framework.update_self f q
  have h_qne_flag : q ≠ gidneyFlagPos bits := gidneyFlag_ne_data bits q hq
  have h_commute := toyWindow2SelectedAddGate_qstart_commute_update_data_disjoint
    bits N a k (gidneyFlagPos bits) (gidneyFlagPos bits)
    (gidneyB0Idx bits k) (gidneyB1Idx bits k) q (f q) f
    hq h_qne_flag h_qne_flag hq_ne_b0 hq_ne_b1
  -- h_commute : applyNat gate (update f q (f q)) = update (applyNat gate f) q (f q)
  rw [h_self] at h_commute
  -- h_commute : applyNat gate f = update (applyNat gate f) q (f q)
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

/-- **Corollary: data-position preservation at non-window positions.**
For data positions `q < bits` that fall OUTSIDE the active window
(`q < gidneyB1Idx bits k ∨ q > gidneyB0Idx bits k`), the gate
preserves the value. Useful when iterating over multi-window
products. -/
theorem toyWindow2SelectedAddGate_qstart_preserves_data_outside_window
    (bits N a k acc x q : Nat)
    (hwin : 2 * k + 1 < bits)
    (hq : q < bits)
    (h_outside : q < bits - 1 - (2 * k + 1) ∨ bits - 1 - 2 * k < q) :
    Gate.applyNat
        (toyWindow2SelectedAddGate_qstart bits bits N a k
          (gidneyFlagPos bits) (gidneyFlagPos bits)
          (gidneyB0Idx bits k) (gidneyB1Idx bits k))
        (gidneyComputeInput bits x acc) q
      = gidneyComputeInput bits x acc q := by
  have hq_ne_b0 : q ≠ gidneyB0Idx bits k := by
    unfold gidneyB0Idx
    rcases h_outside with h | h <;> omega
  have hq_ne_b1 : q ≠ gidneyB1Idx bits k := by
    unfold gidneyB1Idx
    rcases h_outside with h | h <;> omega
  exact toyWindow2SelectedAddGate_qstart_preserves_data_at_disjoint
    bits N a k acc x q hwin hq hq_ne_b0 hq_ne_b1

/-! ### Status: R7d^xxix-L-3′ partial deliverable

What landed:
- Architecture D layout primitives:
  `gidneyB0Idx`, `gidneyB1Idx`, `gidneyFlagPos`, `gidneyComputeInput`.
- Readback lemmas: `_data`, `_b0`, `_b1`, `_at_flagPos`.
- Shifted-layout arithmetic helpers (B0_lt_bits, B1_lt_bits,
  B0_ne_B1, flag_above_workspace, flag_ne_data, flagPos_ne_b0/b1).
- Primary deliverable: **data-position preservation theorem**
  `toyWindow2SelectedAddGate_qstart_preserves_data_at_disjoint`
  showing all non-active data positions are preserved.
- Outside-window corollary
  `toyWindow2SelectedAddGate_qstart_preserves_data_outside_window`.

What is deferred to follow-up ticks (full single-window arithmetic
correctness):
- q_start-parametric versions of the Cuccaro internal helpers:
  - `mod_add_state_eq_when_control_false_on_qstart_input`.
  - `mod_add_above_layout_noop_on_F` at q_start.
- q_start-parametric per-case state-eq theorems
  (Case1/2/3 FF/FT/TF/TT no-op or fire branches).
- The composed q_start selected-add state-equation theorem
  `toyWindow2SelectedAddGate_qstart_state_eq_on_gidneyComputeInput`.

Why deferred: the existing q_start = 2 state-eq theorems
(`toyWindow2Case3Gate_state_eq_FF_noop`, etc.) span ~200 lines each
because they unfold the Cuccaro adder internals at the specific
positions of the q_start = 2 layout. A clean port to q_start
requires ~6-8 helper lemmas to be ported first, each ~100-200
lines. This is a multi-tick effort that should follow its own
dedicated planning. -/

/-! ## Phase R7d^xxix-L-3.5′ — q_start controlled-mod-add preservation

This phase closes the q_start-parametric **frame-based**
preservation theorem for the controlled mod-add gate
`sqir_style_controlledModAddConst_gate bits q_start N c controlIdx
flagPos`.

**Scope**: positions OUTSIDE the gate's working set are proven
preserved (a strict subset of "full no-op when control is false",
but the workspace/control/flagPos preservation requires the FULL
clean theorem at q_start which is multi-tick effort).

**Why the FULL state preservation is deferred**:
- The q_start = 2 clean theorem
  (`sqir_style_controlledModAddConst_gate_clean`) bakes in
  q_start = 2 AND flagPos = 1 throughout its multi-stage proof
  (deliverables A through G, each ~50-200 lines, in
  `CuccaroSQIRDirtyFlag.lean`).
- The `ControlledModAdd.clean_*` projections used by
  `mod_add_state_eq_when_control_false_on_Case3Input` extract from
  the q_start = 2 clean bundle; they do NOT generalize to q_start =
  bits without a parallel clean theorem.
- Porting clean to parametric q_start requires touching the entire
  `sqir_style_controlledModAddConst_gate_clean` proof chain,
  redoing each deliverable.

**What L-3.5′ achieves**: the FRAME-based preservation gives us
"the gate preserves any state at positions outside the workspace
and outside control/flag positions". This is a clean, useful
result that survives any future clean-theorem port. -/

/-- **q_start frame preservation: gate preserves state at any single
position disjoint from its working set.** Direct consequence of the
L-2′ `sqir_modAdd_qstart_commute_update_disjoint` via
`update_self`. -/
theorem sqir_modAdd_qstart_preserves_at_outside
    (bits q_start N c controlIdx flagPos q : Nat) (s : Nat → Bool)
    (h_q_outside :
      q < q_start ∨ q_start + 2 * bits + 1 ≤ q)
    (h_q_ne_flag : q ≠ flagPos)
    (h_q_ne_control : q ≠ controlIdx) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos) s q
      = s q := by
  have h_self : update s q (s q) = s := FormalRV.Framework.update_self s q
  have h_commute := sqir_modAdd_qstart_commute_update_disjoint
    bits q_start N c controlIdx flagPos q (s q) s
    h_q_outside h_q_ne_flag h_q_ne_control
  rw [h_self] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

/-- **Above-layout no-op specialization** (matches the prompt's
Step 2 fallback shape). On the zero-accumulator Cuccaro base
`cuccaro_input_F q_start false 0 acc`, at any position above the
workspace + ≠ flagPos, the gate yields `false`. -/
theorem mod_add_above_layout_noop_on_F_qstart
    (bits q_start N c flagPos acc q : Nat)
    (hacc : acc < 2^bits)
    (h_q_above : q_start + 2 * bits + 1 ≤ q)
    (h_q_ne_flag : q ≠ flagPos) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits q_start N c flagPos flagPos)
        (cuccaro_input_F q_start false 0 acc) q
      = false := by
  rw [sqir_modAdd_qstart_preserves_at_outside bits q_start N c
        flagPos flagPos q _ (Or.inr h_q_above) h_q_ne_flag h_q_ne_flag]
  exact cuccaro_input_F_above_eq_false q_start bits acc q h_q_above hacc

/-- **Architecture D mod-add preservation at data positions.** For
any data position `q < bits`, the q_start = bits controlled
mod-add gate (with control = flag = gidneyFlagPos) preserves the
value of `gidneyComputeInput bits x acc` at `q`.

This holds because data positions `q < bits = q_start` are below
the shifted workspace, and `gidneyFlagPos = 3*bits + 1 > bits >
q`. -/
theorem sqir_modAdd_qstart_preserves_data_on_gidneyComputeInput
    (bits N c x acc q : Nat)
    (hq : q < bits) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate
          bits bits N c (gidneyFlagPos bits) (gidneyFlagPos bits))
        (gidneyComputeInput bits x acc) q
      = gidneyComputeInput bits x acc q := by
  have h_q_outside : q < bits ∨ bits + 2 * bits + 1 ≤ q := Or.inl hq
  have h_q_ne_flag : q ≠ gidneyFlagPos bits := gidneyFlag_ne_data bits q hq
  exact sqir_modAdd_qstart_preserves_at_outside bits bits N c
    (gidneyFlagPos bits) (gidneyFlagPos bits) q _ h_q_outside
    h_q_ne_flag h_q_ne_flag

/-- **Architecture D mod-add preservation above the flag.** For
any position `q > gidneyFlagPos bits`, the q_start = bits
controlled mod-add gate preserves the value of `gidneyComputeInput
bits x acc` at `q`. -/
theorem sqir_modAdd_qstart_preserves_above_flag_on_gidneyComputeInput
    (bits N c x acc q : Nat)
    (h_q_above : gidneyFlagPos bits < q) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate
          bits bits N c (gidneyFlagPos bits) (gidneyFlagPos bits))
        (gidneyComputeInput bits x acc) q
      = gidneyComputeInput bits x acc q := by
  have h_q_workspace_above : bits + 2 * bits + 1 ≤ q := by
    have : bits + 2 * bits + 1 = gidneyFlagPos bits := by unfold gidneyFlagPos; rfl
    omega
  have h_q_outside : q < bits ∨ bits + 2 * bits + 1 ≤ q := Or.inr h_q_workspace_above
  have h_q_ne_flag : q ≠ gidneyFlagPos bits := by
    intro h_eq; rw [h_eq] at h_q_above; exact absurd h_q_above (Nat.lt_irrefl _)
  exact sqir_modAdd_qstart_preserves_at_outside bits bits N c
    (gidneyFlagPos bits) (gidneyFlagPos bits) q _ h_q_outside
    h_q_ne_flag h_q_ne_flag

/-- **c = 0 trivial no-op.** When the constant being added is 0,
the controlled mod-add gate is literally `Gate.I`. -/
theorem sqir_style_controlledModAddConst_gate_qstart_zero_noop
    (bits q_start N controlIdx flagPos : Nat) (s : Nat → Bool) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos) s
      = s := by
  unfold sqir_style_controlledModAddConst_gate
  rw [if_pos rfl]
  exact Gate.applyNat_I s

/-! ## Phase R7d^xxix-L-3.6′ — Architecture D control=false target-decode

The L-3.6′ tick ported the control=false target-decode of the
controlled mod-add candidate from q_start = 2 + flagPos = 1 to
parametric q_start + flagPos (see `BQAlgo/CuccaroSQIRDirtyFlag.lean`
for the chain of five ports).

This section specializes the new ported theorem to Architecture D
(q_start = bits, flagPos = gidneyFlagPos bits). The specialization
is the FIRST architectural-correctness theorem for the Gidney-style
layout: it shows that when the control bit is false, the mod-add
gate's target decode equals the original `x`. -/

/-- **Architecture D second ancilla position.** Allocated just above
`gidneyFlagPos bits` so the controlled mod-add can use two distinct
above-workspace positions for its external control and internal
flag. -/
def gidneyFlagPos' (bits : Nat) : Nat := gidneyFlagPos bits + 1

/-- `gidneyFlagPos' bits` is distinct from `gidneyFlagPos bits`. -/
theorem gidneyFlagPos'_ne_gidneyFlagPos (bits : Nat) :
    gidneyFlagPos' bits ≠ gidneyFlagPos bits := by
  unfold gidneyFlagPos' gidneyFlagPos; omega

/-- `gidneyFlagPos' bits` is also above the shifted workspace. -/
theorem gidneyFlagPos'_above_workspace (bits : Nat) :
    bits + 2 * bits + 1 ≤ gidneyFlagPos' bits := by
  unfold gidneyFlagPos' gidneyFlagPos; omega

/-- **Architecture D control=false target-decode.** When the
external control at `gidneyFlagPos' bits` is `false`, the controlled
mod-add candidate (with `q_start = bits`, controlIdx = `gidneyFlagPos'
bits`, internal flagPos = `gidneyFlagPos bits`) preserves the
target's decoded value at `x`. -/
theorem sqir_style_controlledModAddConst_candidate_target_decode_control_false_gidney
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N) :
    cuccaro_target_val bits bits
        (Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false))
      = x := by
  have h_flagPos'_above : bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    gidneyFlagPos'_above_workspace bits
  have h_flagPos_above : bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    gidneyFlag_above_workspace bits
  have h_ctrl_out :
      gidneyFlagPos' bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    Or.inr h_flagPos'_above
  have h_flag_out :
      gidneyFlagPos bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    Or.inr h_flagPos_above
  exact sqir_style_controlledModAddConst_candidate_target_decode_control_false_qstart
    bits bits N c x (gidneyFlagPos' bits) (gidneyFlagPos bits)
    hbits hN_pos hN hN2 hc_pos hc hx h_ctrl_out h_flag_out
    (gidneyFlagPos'_ne_gidneyFlagPos bits)

/-- **R7d^xxix-L-3.7′ Gidney specialization (workspace bundle,
control=false).**  The Architecture-D controlled mod-add (external
control = `gidneyFlagPos' bits`, internal flagPos = `gidneyFlagPos
bits`) preserves the four workspace conjuncts after applying to the
shifted-workspace `cuccaro_input_F` base with control=false. -/
theorem sqir_style_controlledModAddConst_candidate_workspace_control_false_gidney
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N) :
    cuccaro_read_val bits bits
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits bits N c
              (gidneyFlagPos' bits) (gidneyFlagPos bits))
            (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (bits + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (gidneyFlagPos bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (gidneyFlagPos' bits)
        = false := by
  have h_flagPos'_above : bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    gidneyFlagPos'_above_workspace bits
  have h_flagPos_above : bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    gidneyFlag_above_workspace bits
  have h_ctrl_out :
      gidneyFlagPos' bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    Or.inr h_flagPos'_above
  have h_flag_out :
      gidneyFlagPos bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    Or.inr h_flagPos_above
  exact sqir_style_controlledModAddConst_candidate_workspace_control_false_qstart
    bits bits N c x (gidneyFlagPos' bits) (gidneyFlagPos bits)
    hbits hN_pos hN hN2 hc_pos hc hx h_ctrl_out h_flag_out
    (gidneyFlagPos'_ne_gidneyFlagPos bits)

/-- **R7d^xxix-L-3.8′ Gidney specialization (clean bundle,
control=false).**  The Architecture-D controlled mod-add (q_start =
`bits`, internal flagPos = `gidneyFlagPos bits`, external controlIdx =
`gidneyFlagPos' bits`) clean bundle for the control=false branch.

Parametric in `dim` with the three standard dimension hypotheses:
- the shifted Cuccaro workspace fits: `bits + 2 * bits + 1 ≤ dim`;
- `gidneyFlagPos' bits < dim`;
- `gidneyFlagPos bits < dim`.

Trivial wrapper over
`sqir_style_controlledModAddConst_candidate_clean_control_false_qstart`. -/
theorem sqir_style_controlledModAddConst_candidate_clean_control_false_gidney
    (bits N c x dim : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (h_workspace : bits + 2 * bits + 1 ≤ dim)
    (h_flagPos'_lt_dim : gidneyFlagPos' bits < dim)
    (h_flagPos_lt_dim  : gidneyFlagPos bits  < dim) :
    Gate.WellTyped dim
        (sqir_style_controlledModAddConst_candidate bits bits N c
          (gidneyFlagPos' bits) (gidneyFlagPos bits))
    ∧ cuccaro_target_val bits bits
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits bits N c
              (gidneyFlagPos' bits) (gidneyFlagPos bits))
            (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false))
        = x
    ∧ cuccaro_read_val bits bits
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits bits N c
              (gidneyFlagPos' bits) (gidneyFlagPos bits))
            (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (bits + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (gidneyFlagPos bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (gidneyFlagPos' bits)
        = false := by
  have h_flagPos'_above : bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    gidneyFlagPos'_above_workspace bits
  have h_flagPos_above : bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    gidneyFlag_above_workspace bits
  have h_ctrl_out :
      gidneyFlagPos' bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    Or.inr h_flagPos'_above
  have h_flag_out :
      gidneyFlagPos bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    Or.inr h_flagPos_above
  exact sqir_style_controlledModAddConst_candidate_clean_control_false_qstart
    bits bits N c x dim (gidneyFlagPos' bits) (gidneyFlagPos bits)
    hbits hN_pos hN hN2 hc_pos hc hx h_ctrl_out h_flag_out
    (gidneyFlagPos'_ne_gidneyFlagPos bits)
    h_workspace h_flagPos'_lt_dim h_flagPos_lt_dim


end Windowed
end VerifiedShor
