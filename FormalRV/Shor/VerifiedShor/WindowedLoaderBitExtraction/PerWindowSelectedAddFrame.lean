/- WindowedLoaderBitExtraction — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.WindowedLoaderBitExtraction.StateBuilderReconstruction

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ### Status: R7d^xxix-L-3.5′ partial deliverable

**Closed** (kernel-clean):
- `sqir_modAdd_qstart_preserves_at_outside` (generic single-position
  frame preservation).
- `mod_add_above_layout_noop_on_F_qstart` (above-layout no-op on
  cuccaro_input_F base, the prompt's Step 2 fallback shape).
- `sqir_modAdd_qstart_preserves_data_on_gidneyComputeInput`
  (Architecture D specialization at data positions).
- `sqir_modAdd_qstart_preserves_above_flag_on_gidneyComputeInput`
  (Architecture D specialization above flag).
- `sqir_style_controlledModAddConst_gate_qstart_zero_noop` (c = 0
  trivial no-op).

**Deferred** (require q_start clean theorem port, multi-tick):
- `sqir_style_controlledModAddConst_gate_qstart_noop_of_control_false`:
  full-state no-op when the control bit is false. Requires the
  q_start-parametric versions of
  `ControlledModAdd.clean_controlPreserved`,
  `ControlledModAdd.clean_flagFalse`,
  `ControlledModAdd.clean_targetDecode` (with control = false),
  and `ControlledModAdd.clean_readZero`. These all factor through
  `sqir_style_controlledModAddConst_gate_clean` which is q_start
  = 2 hard-coded.
- `sqir_style_controlledModAddConst_gate_qstart_noop_on_gidneyComputeInput`
  (the full Architecture-D specialization).
- `toyWindow2SelectedAddGate_qstart_FF_noop_on_gidneyComputeInput`
  (depends on the above).

The deferred theorems are NOT structural — they're proof-engineering
liabilities. The roadmap for porting them is:
1. Port `sqir_style_controlledModAddConst_gate_clean` to parametric
   q_start AND parametric flagPos (the latter being the harder
   change). ~6 subordinate clean lemmas, each ~50-200 lines.
2. Build q_start-parametric `ControlledModAddImpl` instance for
   q_start = bits and the gidneyFlagPos convention.
3. Extract `clean_*` projections.
4. Port `mod_add_state_eq_when_control_false_on_Case3Input` to
   parametric layout.
5. Use to build FF / FT / TF / TT case state_eq theorems for
   `toyWindow2CaseN_qstart`.
6. Compose into full `toyWindow2SelectedAddGate_qstart_state_eq`. -/

/-! ## Phase R7d^xxiv — per-window selected-add frame helper

The frame helper for the toy windowSize=2 selected-add gate. Says that
the gate commutes with an `update _ p v` whenever `p` is "inactive":
above the Cuccaro workspace, distinct from the gate's active window
positions, and distinct from `flagIdx`.

This is the key bridge for proving the full multi-window correctness
theorem `toyWindow2SelectedAddGate_on_windowed2Input` (see the docstring
of that theorem stub below for the proof strategy). -/

/-- **Frame helper for the selected-add gate.**

`toyWindow2SelectedAddGate` at active window positions `(b0Idx, b1Idx,
flagIdx)` commutes with any `update _ p v` where `p` is disjoint from
the gate's support. Specifically:
- `p` is above the Cuccaro workspace (`p ≥ 2 + 2*bits + 1`),
- `p` is not the active b0 / b1 positions,
- `p` is not `flagIdx`.

The proof composes primitive frame lemmas (`Gate.applyNat_X_commute
_update_outside_fun`, `applyNat_CCX_commute_update_disjoint`,
`style_controlledModAddConst_gate_commute_update_outside_fun`)
through `applyNat_seq_commute_update` per case gate (Case 1, 2, 3), then
chains the three case gates via two more `applyNat_seq_commute_update`. -/
theorem toyWindow2SelectedAddGate_commute_update_inactive
    (bits N a k flagIdx b0Idx b1Idx p : Nat) (v : Bool) (s : Nat → Bool)
    (hp_hi : 2 + 2 * bits + 1 ≤ p)
    (hp_ne_b0 : p ≠ b0Idx)
    (hp_ne_b1 : p ≠ b1Idx)
    (hp_ne_flag : p ≠ flagIdx) :
    Gate.applyNat (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx)
        (update s p v)
      = update
          (Gate.applyNat
            (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx) s)
          p v := by
  have hp_out : p < 2 ∨ 2 + (2 * bits + 1) ≤ p := Or.inr (by omega)
  have hp_ne_one : p ≠ 1 := by omega
  -- Primitive commute proofs (universally quantified over inner state).
  have hX_b0 : ∀ f', Gate.applyNat (Gate.X b0Idx) (update f' p v)
                    = update (Gate.applyNat (Gate.X b0Idx) f') p v :=
    fun f' => Gate.applyNat_X_commute_update_outside_fun b0Idx p v f' hp_ne_b0
  have hX_b1 : ∀ f', Gate.applyNat (Gate.X b1Idx) (update f' p v)
                    = update (Gate.applyNat (Gate.X b1Idx) f') p v :=
    fun f' => Gate.applyNat_X_commute_update_outside_fun b1Idx p v f' hp_ne_b1
  have hCCX : ∀ f', Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
                       (update f' p v)
                  = update (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx) f') p v :=
    fun f' => applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx f' p v
                hp_ne_b0 hp_ne_b1 hp_ne_flag
  have hM1 : ∀ f', Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 1) flagIdx 1) (update f' p v)
                  = update (Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 1) flagIdx 1) f') p v :=
    fun f' => style_controlledModAddConst_gate_commute_update_outside_fun
                bits N (tableValue a N 2 k 1) flagIdx p v f'
                hp_out hp_ne_one hp_ne_flag
  have hM2 : ∀ f', Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 2) flagIdx 1) (update f' p v)
                  = update (Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 2) flagIdx 1) f') p v :=
    fun f' => style_controlledModAddConst_gate_commute_update_outside_fun
                bits N (tableValue a N 2 k 2) flagIdx p v f'
                hp_out hp_ne_one hp_ne_flag
  have hM3 : ∀ f', Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1) (update f' p v)
                  = update (Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1) f') p v :=
    fun f' => style_controlledModAddConst_gate_commute_update_outside_fun
                bits N (tableValue a N 2 k 3) flagIdx p v f'
                hp_out hp_ne_one hp_ne_flag
  -- Case-1 gate commute (5-layer seq X-CCX-M-CCX-X).
  have hCase1 : ∀ f', Gate.applyNat
                        (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
                        (update f' p v)
                    = update (Gate.applyNat
                        (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx) f')
                        p v := by
    intro f'
    show Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update f' p v) = _
    exact applyNat_seq_commute_update _ _ f' p v hX_b1
            (fun f'' => applyNat_seq_commute_update _ _ f'' p v hCCX
              (fun f''' => applyNat_seq_commute_update _ _ f''' p v hM1
                (fun f'''' => applyNat_seq_commute_update _ _ f'''' p v hCCX hX_b1)))
  -- Case-2 gate commute (5-layer seq X-CCX-M-CCX-X).
  have hCase2 : ∀ f', Gate.applyNat
                        (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
                        (update f' p v)
                    = update (Gate.applyNat
                        (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx) f')
                        p v := by
    intro f'
    show Gate.applyNat (Gate.seq (Gate.X b0Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 2) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
          (update f' p v) = _
    exact applyNat_seq_commute_update _ _ f' p v hX_b0
            (fun f'' => applyNat_seq_commute_update _ _ f'' p v hCCX
              (fun f''' => applyNat_seq_commute_update _ _ f''' p v hM2
                (fun f'''' => applyNat_seq_commute_update _ _ f'''' p v hCCX hX_b0)))
  -- Case-3 gate commute (3-layer seq CCX-M-CCX).
  have hCase3 : ∀ f', Gate.applyNat
                        (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
                        (update f' p v)
                    = update (Gate.applyNat
                        (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx) f')
                        p v := by
    intro f'
    show Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 3) flagIdx 1)
              (Gate.CCX b0Idx b1Idx flagIdx))) (update f' p v) = _
    exact applyNat_seq_commute_update _ _ f' p v hCCX
            (fun f'' => applyNat_seq_commute_update _ _ f'' p v hM3 hCCX)
  -- Compose: toyWindow2SelectedAddGate = Case1Gate ; Case2Gate ; Case3Gate.
  show Gate.applyNat (Gate.seq (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
          (Gate.seq (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
                    (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)))
        (update s p v) = _
  exact applyNat_seq_commute_update _ _ s p v hCase1
          (fun f'' => applyNat_seq_commute_update _ _ f'' p v hCase2 hCase3)

/-! ### Documentation: main multi-window theorem strategy

The full main theorem
```
toyWindow2SelectedAddGate_on_windowed2Input : ∀ ... ,
  Gate.applyNat (toyWindow2SelectedAddGate ... k ... (b0Idx k) (b1Idx k))
      (windowed2Input acc b0Idx b1Idx b0 b1 numWin)
    = windowed2Input
        (windowedStepSpec a N 2 k acc (windowBits2_at b0 b1 k))
        b0Idx b1Idx b0 b1 numWin
```
is proved by induction on `numWin`. Two cases per step (`numWin = n + 1`):

**Case B (k < n, inactive newest):** The two outermost updates of
`windowed2Input ... (n+1)` are at the inactive positions
`(b0Idx n, b1Idx n)`. By cross-window distinctness, these positions
satisfy the frame helper's "inactive" predicate
(`p ≠ b0Idx k`, `p ≠ b1Idx k`, `p ≠ flagIdx`, `p ≥ 2 + 2*bits + 1`).
Apply `toyWindow2SelectedAddGate_commute_update_inactive` twice to push
the two outer updates outside the gate, then apply the inductive
hypothesis on the inner `windowed2Input ... n`, then re-apply
`windowed2Input_succ` to reconstruct the result.

**Case A (k = n, active newest):** The outer two updates ARE the
active layer `(b0Idx n, b1Idx n) = (b0Idx k, b1Idx k)`. Inside is
`windowed2Input ... n` containing `n` inactive prefix layers. To apply
`toyWindow2SelectedAddGate_state_eq_spec`, we need the inner state to
be `cuccaro_input_F 2 false 0 acc` (i.e., no inactive prefix).
Strategy: inner induction on `n` (the inactive prefix size).
- Inner base `n = 0`: inner state IS `cuccaro_input_F`. State is a
  literal `toyWindow2Case3Input`. Apply spec directly.
- Inner step `n = j + 1`: the inner state has outer layer `(b0Idx j,
  b1Idx j)`. Use `update_comm` (four times) to swap this layer past
  the active `(b0Idx k, b1Idx k)` updates, bringing the inactive layer
  outermost. Use the frame helper to commute the inactive layer through
  the gate. Use inner IH on the stripped state. Then `update_comm` back.

Hypotheses required: cross-window distinctness `b0Idx i ≠ b0Idx j`,
`b1Idx i ≠ b1Idx j`, `b0Idx i ≠ b1Idx j` (for any i, j with i ≠ j),
plus the existing single-window hypotheses. The four `update_comm`
swaps need each pair (`b0Idx k`, `b1Idx k`) × (`b0Idx j`, `b1Idx j`)
to be distinct — which is exactly the cross-window distinctness.

This proof structure is mechanically clear but verbose (~150–200 lines
total). Deferred to a follow-up tick to keep this commit focused on
the reusable frame infrastructure. -/


end Windowed
end VerifiedShor
