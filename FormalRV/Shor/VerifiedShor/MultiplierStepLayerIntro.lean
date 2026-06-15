import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.ControlledModAddLayer

namespace VerifiedShor
namespace ControlledModAdd
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)




/-! ### Level-1 register layout (Phase R5b)

`ControlledModAddLayout` is the **Level-1** layout abstraction:
the minimal set of layout facts that the `ControlledModAddImpl`
contract (R4b) actually mentions.  It abstracts away the
Cuccaro-specific names (`cuccaro_input_F`, `cuccaro_target_val`,
`cuccaro_read_val`, `flagPos = 1`, `topCarryPos = 2 + 2*bits`, …)
so that `ControlledModAddImpl` can be stated without them.

**Scope (Level 1 only)**: this struct only carries facts needed to
state and prove **controlled-modular-add correctness**.  It does
NOT abstract:
* The multiplier register layout (`mult_control_idx`,
  `modmult_input_F`, install machinery) — that is Level 2
  `MultiplierStepLayout`, reserved for R5c.
* The Shor/MCP adapter layout (`encodeDataZeroAnc`,
  `encode_to_mult_adapter`, `Gate.shift`) — that is Level 3
  `MCPAdapterLayout`, reserved for R5d.

**Fields are functions of `bits`**, not constants, so different
adders may pick layouts that scale differently with width.

**No semantic laws are bundled in the struct** (e.g. "decoder ∘
encoder = identity", "workspaceUpperBound ≤ ancillaWidth").
Such laws are not currently required by the R4b contract, and
adding them now would force every layout-instance to discharge
them up front.  If a future R5b' tick discovers that a particular
projection alias needs a law, we add it then. -/
structure ControlledModAddLayout where
  /-- Ancilla width as a function of data-register width `bits`. -/
  ancillaWidth        : Nat → Nat
  /-- Position of the dirty flag bit in the layout. -/
  flagPos             : Nat → Nat
  /-- Position of the top-carry bit in the layout. -/
  topCarryPos         : Nat → Nat
  /-- Exclusive upper bound of the in-block workspace (`controlIdx`
  must live below or above this). -/
  workspaceUpperBound : Nat → Nat
  /-- Input encoder: given width `bits` and an `acc : Nat`, produces
  the Boolean state-function representing the input register. -/
  inputEncode         : (bits acc : Nat) → Nat → Bool
  /-- Target-register decoder. -/
  targetDecode        : (bits : Nat) → (Nat → Bool) → Nat
  /-- Read/workspace-register decoder. -/
  readDecode          : (bits : Nat) → (Nat → Bool) → Nat
  /-- Predicate stating "the supplied control index is outside the
  in-block workspace" — i.e. it lives in the input-flag region or
  above the workspace cassette. -/
  controlAllowed      : Nat → Nat → Prop

/-- **`ControlledModAddImpl`** — the first reusable contract below
`VerifiedModMulFamily`.

R5b refactor: the layout-specific names (`cuccaro_target_val`,
`cuccaro_read_val`, `cuccaro_input_F`, hard-coded positions 1 and
`2 + 2*bits`, etc.) are now **factored out** into a `layout :
ControlledModAddLayout` field.  Every reference in the `clean`
bundle goes through the layout.

Specifically:

* `layout : ControlledModAddLayout` — the layout abstraction (R5b).
* `gate bits N c controlIdx` is the Lean `Gate` IR term implementing
  `if control bit at controlIdx then x ↦ (x + c) % N else x ↦ x`.
* `clean` is the **6-conjunct cleanliness bundle**, now stated in
  terms of `layout.*` projections:
  1. The gate is well-typed at the declared `layout.ancillaWidth bits`.
  2. `layout.targetDecode bits` of the output equals `(x + c) % N`
     if `control = true` else `x`.
  3. `layout.readDecode bits` of the output equals `0`.
  4. The top-carry bit (position `layout.topCarryPos bits`) is `false`.
  5. The flag bit (position `layout.flagPos bits`) is `false`.
  6. The control bit at `controlIdx` is preserved.

### Side conditions consumed by `clean`
* `1 ≤ bits`, `0 < N`, `N ≤ 2^bits`, `2 * N ≤ 2^bits`: sizing.
* `c < N`, `x < N`: the constant and the live data live in `[0, N)`.
* `layout.controlAllowed bits controlIdx`: the control wire is outside
  the in-block workspace.
* `controlIdx ≠ layout.flagPos bits`: the control wire is not the
  flag bit.
* `controlIdx < layout.ancillaWidth bits`: the control wire is within
  the declared workspace.

### Layout coupling
The R5b layout is still **Level 1 only**.  Multiplier-step layout
(`MultiplierStepLayout`) and Shor/MCP adapter layout
(`MCPAdapterLayout`) are reserved for R5c and R5d respectively. -/
structure ControlledModAddImpl where
  /-- The Level-1 register layout this implementation uses. -/
  layout : ControlledModAddLayout
  /-- The controlled mod-add gate constructor. -/
  gate   : (bits N c controlIdx : Nat) → Gate
  /-- The 6-conjunct cleanliness bundle, stated through the layout. -/
  clean  : ∀ (bits N c x controlIdx : Nat) (control : Bool),
             1 ≤ bits → 0 < N → N ≤ 2^bits → 2 * N ≤ 2^bits →
             c < N → x < N →
             layout.controlAllowed bits controlIdx →
             controlIdx ≠ layout.flagPos bits →
             controlIdx < layout.ancillaWidth bits →
             Gate.WellTyped (layout.ancillaWidth bits)
               (gate bits N c controlIdx)
             ∧ layout.targetDecode bits
                 (Gate.applyNat (gate bits N c controlIdx)
                   (update (layout.inputEncode bits x)
                     controlIdx control))
               = (if control then (x + c) % N else x)
             ∧ layout.readDecode bits
                 (Gate.applyNat (gate bits N c controlIdx)
                   (update (layout.inputEncode bits x)
                     controlIdx control)) = 0
             ∧ Gate.applyNat (gate bits N c controlIdx)
                 (update (layout.inputEncode bits x)
                   controlIdx control)
                 (layout.topCarryPos bits) = false
             ∧ Gate.applyNat (gate bits N c controlIdx)
                 (update (layout.inputEncode bits x)
                   controlIdx control)
                 (layout.flagPos bits) = false
             ∧ Gate.applyNat (gate bits N c controlIdx)
                 (update (layout.inputEncode bits x)
                   controlIdx control) controlIdx = control

/-! ### SQIR/Cuccaro layout instance (Phase R5b)

`sqirCuccaroLayout` packages the **SQIR/Cuccaro layout choices** as
a `ControlledModAddLayout` value:

* `ancillaWidth := sqir_modmult_rev_anc` (= `3*bits + 11`).
* `flagPos := fun _ ↦ 1` (Cuccaro flag at position 1).
* `topCarryPos := fun bits ↦ 2 + 2 * bits` (top carry).
* `workspaceUpperBound := fun bits ↦ 2 + 2 * bits + 1`
  (one above the top carry).
* `inputEncode := fun _ acc ↦ cuccaro_input_F 2 false 0 acc`
  (Cuccaro encoding with q_start = 2, carry_in = false, a = 0,
  b = acc).
* `targetDecode := fun bits ↦ cuccaro_target_val bits 2`.
* `readDecode := fun bits ↦ cuccaro_read_val bits 2`.
* `controlAllowed := fun bits controlIdx ↦
    controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx`.

A future Gidney-AND, QFT-adder, or lookup-table layout would supply
a different `ControlledModAddLayout` value. -/
def sqirCuccaroLayout : ControlledModAddLayout where
  ancillaWidth        := sqir_modmult_rev_anc
  flagPos             := fun _ => 1
  topCarryPos         := fun bits => 2 + 2 * bits
  workspaceUpperBound := fun bits => 2 + 2 * bits + 1
  inputEncode         := fun _ acc => cuccaro_input_F 2 false 0 acc
  targetDecode        := fun bits => cuccaro_target_val bits 2
  readDecode          := fun bits => cuccaro_read_val bits 2
  controlAllowed      := fun bits controlIdx =>
                           controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx

/-! ### SQIR/Cuccaro implementation instance

`sqirCuccaroImpl` is the **first witness** of the
`ControlledModAddImpl` contract (Phase R4b + R5b refactor).

It carries the `sqirCuccaroLayout` defined just above and wraps the
existing SQIR-faithful Cuccaro controlled modular adder
(`sqir_style_controlledModAddConst_gate`) plus its 6-conjunct
clean theorem (`sqir_style_controlledModAddConst_gate_clean`).

Because every layout field of `sqirCuccaroLayout` is a `fun` that
reduces to the corresponding Cuccaro name, the `clean` field below
is propositionally (and definitionally) equal to the source
theorem's conclusion — so the body is a one-line direct call to
`sqir_style_controlledModAddConst_gate_clean`. -/
noncomputable def sqirCuccaroImpl : ControlledModAddImpl where
  layout := sqirCuccaroLayout
  gate   := fun bits N c controlIdx =>
              sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1
  clean  := by
    intro bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
      hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt
    exact sqir_style_controlledModAddConst_gate_clean bits N c x controlIdx control
      hbits hN_pos hN hN2 hc hx hcontrol_allowed hcontrol_ne_flag
      h_control_workspace_lt

/-! ### Projection aliases (R5b: stated through `C.layout`)

The six aliases below extract individual conjuncts from
`ControlledModAddImpl.clean`.  All references to layout-specific
positions and decoders go through `C.layout.*` projections — the
aliases are now layout-parametric.

Signature convention: each alias takes the *full* side-condition
list (bits, N, c, x, controlIdx, control + 10 hypotheses), matching
the shape of the source bundle.  Aliases for conjuncts that don't
depend on `x` / `control` still accept them so the call shape is
uniform. -/

theorem clean_wellTyped (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    Gate.WellTyped (C.layout.ancillaWidth bits)
      (C.gate bits N c controlIdx) :=
  (C.clean bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
    hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt).1

theorem clean_targetDecode (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    C.layout.targetDecode bits
        (Gate.applyNat (C.gate bits N c controlIdx)
          (update (C.layout.inputEncode bits x) controlIdx control))
      = (if control then (x + c) % N else x) :=
  (C.clean bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
    hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt).2.1

theorem clean_readZero (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    C.layout.readDecode bits
        (Gate.applyNat (C.gate bits N c controlIdx)
          (update (C.layout.inputEncode bits x) controlIdx control)) = 0 :=
  (C.clean bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
    hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt).2.2.1

theorem clean_topCarryFalse (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    Gate.applyNat (C.gate bits N c controlIdx)
        (update (C.layout.inputEncode bits x) controlIdx control)
        (C.layout.topCarryPos bits) = false :=
  (C.clean bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
    hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt).2.2.2.1

theorem clean_flagFalse (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    Gate.applyNat (C.gate bits N c controlIdx)
        (update (C.layout.inputEncode bits x) controlIdx control)
        (C.layout.flagPos bits) = false :=
  (C.clean bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
    hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt).2.2.2.2.1

theorem clean_controlPreserved (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    Gate.applyNat (C.gate bits N c controlIdx)
        (update (C.layout.inputEncode bits x) controlIdx control)
        controlIdx
      = control :=
  (C.clean bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
    hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt).2.2.2.2.2

/-! ### Generic smoke theorem (R5b)

A direct restatement of `clean_targetDecode` for any
`ControlledModAddImpl`.  Demonstrates that the layout-parametric
interface can be consumed without naming Cuccaro. -/
theorem ControlledModAddImpl.targetDecode_eq_of_clean
    (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    C.layout.targetDecode bits
        (Gate.applyNat (C.gate bits N c controlIdx)
          (update (C.layout.inputEncode bits x) controlIdx control))
      = (if control then (x + c) % N else x) :=
  clean_targetDecode C bits N c x controlIdx control
    hbits hN_pos hN hN2 hc hx hcontrol_allowed hcontrol_ne_flag
    h_control_workspace_lt

/-! ### SQIR-specific smoke theorem (preserved name)

A usability check: the SQIR/Cuccaro instance, when consumed through
the `clean_targetDecode` projection, produces the expected
`(x + c) % N` decode under `control = true` (and `x` under
`control = false`).  After the R5b refactor the SQIR-flavor decoder
(`cuccaro_target_val bits 2`) and encoder (`cuccaro_input_F 2 false
0 x`) on the conclusion are obtained by definitional reduction
through `sqirCuccaroImpl.layout = sqirCuccaroLayout`. -/
theorem sqirCuccaroImpl_targetDecode_eq
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1)
    (h_control_workspace_lt :
        controlIdx < sqirCuccaroImpl.layout.ancillaWidth bits) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqirCuccaroImpl.gate bits N c controlIdx)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control))
      = (if control then (x + c) % N else x) :=
  clean_targetDecode sqirCuccaroImpl bits N c x controlIdx control
    hbits hN_pos hN hN2 hc hx hcontrol_out hcontrol_ne_flag
    h_control_workspace_lt

end ControlledModAdd
end VerifiedShor
