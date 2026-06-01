import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.Part20

namespace VerifiedShor
namespace Windowed
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




/-! ### Pure arithmetic specs (R7b) -/

/-- The k-th w-bit window of `m`: bits `[k*w, (k+1)*w)` interpreted
as a `Nat` in `[0, 2^w)`. -/
def windowValue (m w k : Nat) : Nat := (m / 2^(k * w)) % 2^w

/-- Number of windows needed to cover `bits` bits with window size `w`.
For `w = 0`, returns `0` (degenerate). -/
def numWindows (bits w : Nat) : Nat :=
  if w = 0 then 0 else (bits + w - 1) / w

/-- Table value for window `k` and value `v`: `(a * 2^(k*w) * v) % N`.
Used as the precomputed lookup entry for the k-th window. -/
def tableValue (a N w k v : Nat) : Nat := (a * 2^(k * w) * v) % N

/-- One windowed-step accumulator update:
`(acc + tableValue a N w k v) % N`. -/
def windowedStepSpec (a N w k acc v : Nat) : Nat :=
  (acc + tableValue a N w k v) % N

/-! ### Arithmetic bound lemmas -/

theorem windowValue_lt (m w k : Nat) (_hw : 0 < w) :
    windowValue m w k < 2^w := by
  unfold windowValue
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem tableValue_lt_N (a N w k v : Nat) (hN_pos : 0 < N) :
    tableValue a N w k v < N := by
  unfold tableValue
  exact Nat.mod_lt _ hN_pos

theorem windowedStepSpec_lt_N (a N w k acc v : Nat) (hN_pos : 0 < N) :
    windowedStepSpec a N w k acc v < N := by
  unfold windowedStepSpec
  exact Nat.mod_lt _ hN_pos

theorem tableValue_zero (a N w k : Nat) :
    tableValue a N w k 0 = 0 := by
  unfold tableValue
  rw [Nat.mul_zero, Nat.zero_mod]

theorem windowedStepSpec_zero (a N w k acc : Nat) :
    windowedStepSpec a N w k acc 0 = acc % N := by
  unfold windowedStepSpec
  rw [tableValue_zero, Nat.add_zero]

/-- Window value at `k = 0` is `m % 2^w`. -/
theorem windowValue_zero (m w : Nat) :
    windowValue m w 0 = m % 2^w := by
  unfold windowValue
  simp

/-- A `0`-sized window decodes to `0`. -/
theorem windowValue_w_zero (m k : Nat) :
    windowValue m 0 k = 0 := by
  unfold windowValue
  simp [Nat.mod_one]

/-! ### Interface structures (R7c) -/

/-- **`WindowLayout`**: layout descriptor for the windowed register
arrangement.  Data-level only.

Future extensions (when circuit construction lands) may add fields
for window-bit positions, ancilla locations, and lookup table
registers. -/
structure WindowLayout where
  /-- Window size (number of multiplier bits per lookup step). -/
  windowSize : Nat
  /-- Number of windows as a function of the multiplier bit width. -/
  numWindows : Nat → Nat

/-- **`LookupTableImpl`**: a precomputed lookup table for windowed
modular multiplication.

`tableValue a N w k v` is the precomputed value `(a * 2^(k*w) * v) % N`.
`lookupCorrect` is the semantic field certifying the implementation
agrees with the arithmetic spec.

For R7c this is a pure data + correctness package; circuit-level
loading is deferred. -/
structure LookupTableImpl where
  /-- The table value function. -/
  tableValue : (a N w k v : Nat) → Nat
  /-- Agreement with the arithmetic spec `(a * 2^(k*w) * v) % N`. -/
  lookupCorrect :
    ∀ a N w k v, 0 < N → tableValue a N w k v = Windowed.tableValue a N w k v

/-- **`WindowedLookupModMulSpec`**: a *spec-level* windowed-lookup
modular-multiplier description.

For R7c we only require:
* `layout`: window descriptor.
* `table`: precomputed values agreeing with `tableValue`.
* `stepSpec`: an arithmetic-only correctness field — given window
  index `k`, current accumulator `acc < N`, and window value
  `v < 2^windowSize`, the next accumulator is `windowedStepSpec
  a N windowSize k acc v`.

This structure does NOT yet carry a circuit family.  R7d/R7e will
extend it (or introduce a `WindowedLookupModMulImpl` subclass) with
a `family` field once toy circuit construction is in place. -/
structure WindowedLookupModMulSpec (a N : Nat) where
  layout : WindowLayout
  table  : LookupTableImpl
  /-- Spec: applying the k-th windowed step with value `v` advances
  the accumulator by `tableValue a N w k v` modulo `N`. -/
  stepSpec :
    ∀ k acc v, 0 < N → acc < N → v < 2^layout.windowSize →
      ∃ acc', acc' = windowedStepSpec a N layout.windowSize k acc v

/-- **Identity `LookupTableImpl`**: uses `Windowed.tableValue` directly.
Demonstrates the structure is non-empty. -/
def identityLookupTable : LookupTableImpl where
  tableValue   := Windowed.tableValue
  lookupCorrect := fun _ _ _ _ _ _ => rfl

/-- **Trivial spec instance** at `windowSize = 1` for `(a, N)`.
Demonstrates the structure is inhabited; `stepSpec` is trivially
witnessed by `windowedStepSpec` itself. -/
def trivialSpec (a N : Nat) : WindowedLookupModMulSpec a N where
  layout := {
    windowSize := 1
    numWindows := fun bits => bits
  }
  table := identityLookupTable
  stepSpec := fun k acc v _ _ _ =>
    ⟨windowedStepSpec a N 1 k acc v, rfl⟩

/-! ### Future work skeleton (R7d/R7e)

A real `WindowedLookupModMulImpl` extending the spec with a circuit
family would look approximately like:

```
structure WindowedLookupModMulImpl (a N bits anc : Nat)
    extends WindowedLookupModMulSpec a N where
  family : Nat → FormalRV.SQIRPort.BaseUCom (bits + anc)
  familyCorrect : ...  -- ties the circuit family to stepSpec
```

The connection to `VerifiedModMulFamily` would be:

```
theorem WindowedLookupModMulImpl.toVerifiedModMulFamily
    {a N bits anc : Nat}
    (W : WindowedLookupModMulImpl a N bits anc) :
    VerifiedModMulFamily a N bits anc :=
  { family := W.family
  , mmi := ...  -- derived from familyCorrect + per-iterate spec
  , wellTyped := ...  -- circuit well-typedness
  }
```

Missing pieces for this connection:
* Toy lookup circuit construction (equality-test on w bits with
  CCX cascade + reversible flag uncomputation; `2^w` controlled
  modular-add applications composed in sequence).
* Proof that the circuit family realizes `MultiplyCircuitProperty`
  for `a^(2^i) mod N` at each QPE iterate (this requires linking
  the per-window step proof to the full per-iterate multiplication).

These are the next R7d/R7e targets. -/

/-! ### R7d: toy windowed-lookup case-3 selected-add (windowSize = 2)

A minimal **Route A** circuit-level demonstration that windowed-lookup
arithmetic fits in the existing `Gate` IR — combined with a
**Route B** interface for the spec-level correctness.

The CONCRETE `Gate` IR construction below shows that the existing
primitives (CCX + the R4b `ControlledModAdd.sqirCuccaroImpl.gate`)
are sufficient to express one case (v=3) of a windowSize=2 lookup
step.  This answers the R7a feasibility question definitively:
**no new primitive is needed**.

Circuit structure (for v=3, the simplest case):
1. `CCX b0Idx b1Idx flagIdx` — compute equality test:
   flag becomes (b0 AND b1), which is true iff v = 3.
2. `ControlledModAdd.sqirCuccaroImpl.gate bits N c_3 flagIdx` — the
   R4b mod-add gate, controlled by the equality flag.  Adds c_3
   (= `tableValue a N 2 k 3`) to target if flag is true; otherwise
   no-op.
3. `CCX b0Idx b1Idx flagIdx` — uncompute the equality flag.  b0 and
   b1 are above the mod-add workspace, so they're unchanged by
   step 2, and the same CCX inverts step 1.

For cases v=1, v=2, the analogous gate inserts X-flips around the
CCX cascade.  Generalizing to all 4 values yields the full
windowSize=2 lookup step.

**Soundness rule honored**: no sorry/admit/axiom.  The `def` lands
as a concrete `Gate` term; the correctness theorem is packaged at
the spec level (Route B) via `Window2LookupCase3Spec`.  A future
tick can land the full Lean proof of `case3Gate` against this spec
— the proof outline (which exists; see docstring on
`Window2LookupCase3Spec.gateCorrect`) requires a few `Framework.update`
commutation lemmas not yet in the public surface. -/

/-- One window step's selected-add gate for the v=3 case.
Concrete `Gate` IR term using only `CCX` + R4b's mod-add. -/
noncomputable def toyWindow2Case3Gate
    (bits N a k : Nat) (flagIdx b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 3
  Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
    (Gate.seq (ControlledModAdd.sqirCuccaroImpl.gate bits N c flagIdx)
              (Gate.CCX b0Idx b1Idx flagIdx))

/-- Input encoding for the toy case-3 gate: SQIR/Cuccaro accumulator
encoding (with empty multiplier-input region) plus the two window
bits at `b0Idx`, `b1Idx`. -/
def toyWindow2Case3Input
    (acc : Nat) (b0Idx b1Idx : Nat) (b0 b1 : Bool) : Nat → Bool :=
  update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1

/-! ### Spec interface for windowSize=2 case 3 (Route B)

`Window2LookupCase3Spec` is the layer-1 contract for a selected-add
component covering the v=3 case of a windowSize=2 lookup step.

Any backend (the toy CCX-based gate above, or a future Gidney-AND,
QFT-adder, or QROM-based variant) can provide this contract by
implementing the gate field and proving the `case3Correct` field.

Once a `Window2LookupCase3Spec` instance lands, composing with the
analogous v=1, v=2 specs gives the full windowSize=2 lookup step.
Composing across windows k = 0 .. numWindows N 2 yields a windowed
multiplier suitable for `VerifiedModMulFamily` (R7e). -/
structure Window2LookupCase3Spec (a N : Nat) where
  /-- The gate constructor, parameterized by width and window index. -/
  gate : (bits k flagIdx b0Idx b1Idx : Nat) → Gate
  /-- Correctness: when the window bits encode v = 3 (both true),
  the target advances by `tableValue a N 2 k 3`; else target
  unchanged.  The hypothesis set matches what the toy CCX-based
  construction would consume. -/
  case3Correct :
    ∀ (bits k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool),
      1 ≤ bits → 0 < N → N ≤ 2^bits → 2 * N ≤ 2^bits →
      acc < N →
      flagIdx < 2 → flagIdx ≠ 1 → flagIdx < sqir_modmult_rev_anc bits →
      2 + 2 * bits + 1 ≤ b0Idx → 2 + 2 * bits + 1 ≤ b1Idx →
      b0Idx ≠ b1Idx → b0Idx ≠ flagIdx → b1Idx ≠ flagIdx →
      cuccaro_target_val bits 2
          (Gate.applyNat (gate bits k flagIdx b0Idx b1Idx)
            (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
        = if b0 && b1 then (acc + tableValue a N 2 k 3) % N else acc

/-- Arithmetic helper: `tableValue` at the v=3 case unfolds to its
defining expression.  Useful for instantiating the spec. -/
theorem tableValue_window2_v3_eq (a N k : Nat) :
    tableValue a N 2 k 3 = (a * 2^(k * 2) * 3) % N := rfl

/-- Arithmetic helper: `windowedStepSpec` for v=3 equals
the target-decode formula. -/
theorem windowedStepSpec_window2_v3
    (a N k acc : Nat) (_hN_pos : 0 < N) :
    windowedStepSpec a N 2 k acc 3 = (acc + tableValue a N 2 k 3) % N := by
  unfold windowedStepSpec
  rfl

/-- **R7d' — toy case-3 selected-add correctness**.

The toy windowSize=2 case-3 gate satisfies the spec: when both
window bits are true (v = 3), the target accumulator advances by
`tableValue a N 2 k 3`; otherwise it is unchanged.

Proof route:
1. The outer CCX only updates `flagIdx` (< 2), which is outside the
   Cuccaro workspace.  By `cuccaro_target_val_update_outside_workspace`,
   the target value is invariant.
2. The inner CCX computes `update F0 flagIdx (b0 AND b1)` since
   `F0 flagIdx = false` (from the cuccaro_input_F at `flagIdx < 2`).
3. Updates at `b0Idx`, `b1Idx` (both above the workspace) commute
   with the mod-add (via `sqir_style_controlledModAddConst_gate_commute_update_outside_fun`)
   and are invisible to `cuccaro_target_val` (via the outside-workspace
   lemma).
4. The remaining `Gate.applyNat (mod-add) (update (cuccaro_input_F ...) flagIdx ctrl)`
   is exactly the input shape `ControlledModAdd.clean_targetDecode`
   handles.

**No direct call to `sqir_style_controlledModAddConst_gate_clean`** —
the mod-add target is extracted through the R4b/R5b projection
`ControlledModAdd.clean_targetDecode`. -/
theorem toyWindow2Case3Gate_correct
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_target_val bits 2
        (Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = if b0 && b1 then (acc + tableValue a N 2 k 3) % N else acc := by
  -- Auxiliary facts.
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  -- Convert the gate to SQIR-form (the mod-add is the only layout-coupled term).
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change cuccaro_target_val bits 2
      (Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = if b0 && b1 then (acc + tableValue a N 2 k 3) % N else acc
  simp only [Gate.applyNat_seq]
  -- Step 1: outer CCX is just an update at flagIdx, outside workspace.
  rw [Gate.applyNat_CCX]
  rw [cuccaro_target_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  -- Step 2: compute the inner CCX result.
  rw [Gate.applyNat_CCX]
  -- Compute F0 reads at b0Idx, b1Idx, flagIdx.
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_eq]
  have h_F0_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F0_b0, h_F0_b1, h_F0_flag]
  -- xor false (b0 && b1) = b0 && b1.
  simp only [Bool.false_xor]
  -- Step 3: reorder updates to bring flagIdx update closest to cuccaro_input_F.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Step 4: push b0Idx, b1Idx updates outside the mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx b1 _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx b0 _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  -- Step 5: drop the outside-workspace updates from cuccaro_target_val.
  rw [cuccaro_target_val_update_outside_workspace bits 2 b1Idx b1 _ h_b1_out]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b0Idx b0 _ h_b0_out]
  -- Step 6: apply R4b/R5b clean_targetDecode (def-eq absorbs the layout-form).
  exact ControlledModAdd.clean_targetDecode ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 3) acc flagIdx (b0 && b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- **R7d' — spec implementation.**  Package
`toyWindow2Case3Gate` as a `Window2LookupCase3Spec` instance.
This demonstrates the case-3 selected-add backend satisfies the
spec contract; chaining with v=1 and v=2 specs (R7d'') produces a
full windowSize=2 lookup step. -/
noncomputable def toyWindow2Case3SpecImpl (a N : Nat) :
    Window2LookupCase3Spec a N where
  gate := fun bits k flagIdx b0Idx b1Idx =>
            toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx
  case3Correct := fun bits k acc flagIdx b0Idx b1Idx b0 b1
                      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
                      h_flag_lt_dim h_b0_hi h_b1_hi h_b0_ne_b1
                      h_b0_ne_flag h_b1_ne_flag =>
    toyWindow2Case3Gate_correct bits N a k acc flagIdx b0Idx b1Idx b0 b1
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag

/-! ### R7d'' — cases v=1 and v=2

For v=1 (binary 01, b0=true b1=false) and v=2 (binary 10, b0=false
b1=true), the equality test requires X-normalization of the
relevant bit before the CCX cascade.

* v=1 gate: `X b1Idx ; CCX b0 b1 flag ; modAdd[flag] ; CCX b0 b1 flag ; X b1Idx`
  After the first X, b1 becomes `!b1` so the CCX computes
  `b0 ∧ !b1`, which is true iff (b0, b1) = (true, false), i.e. v=1.
* v=2 gate: symmetric with X on `b0Idx`.

Correctness proof mirrors v=3 with three extra rewriting steps:
1. Strip the outermost X (outside workspace at b0Idx or b1Idx) via
   `cuccaro_target_val_update_outside_workspace`.
2. Compute the inner X-flip's effect on the relevant bit
   (`F0 b1Idx = b1` so `! F0 b1Idx = !b1`).
3. Merge the double-update at the flipped bit position via
   `Framework.update_idem`. -/

/-- Arithmetic helper: `tableValue` for v=1. -/
theorem tableValue_window2_v1_eq (a N k : Nat) :
    tableValue a N 2 k 1 = (a * 2^(k * 2) * 1) % N := rfl

/-- Arithmetic helper: `tableValue` for v=2. -/
theorem tableValue_window2_v2_eq (a N k : Nat) :
    tableValue a N 2 k 2 = (a * 2^(k * 2) * 2) % N := rfl

/-- Arithmetic helper: `windowedStepSpec` for v=1. -/
theorem windowedStepSpec_window2_v1
    (a N k acc : Nat) (_hN_pos : 0 < N) :
    windowedStepSpec a N 2 k acc 1 = (acc + tableValue a N 2 k 1) % N := by
  unfold windowedStepSpec
  rfl

/-- Arithmetic helper: `windowedStepSpec` for v=2. -/
theorem windowedStepSpec_window2_v2
    (a N k acc : Nat) (_hN_pos : 0 < N) :
    windowedStepSpec a N 2 k acc 2 = (acc + tableValue a N 2 k 2) % N := by
  unfold windowedStepSpec
  rfl

/-- One window step's selected-add gate for the v=1 case
(binary 01).  X-normalizes b1 before/after the CCX cascade. -/
noncomputable def toyWindow2Case1Gate
    (bits N a k : Nat) (flagIdx b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 1
  Gate.seq (Gate.X b1Idx)
    (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
      (Gate.seq (ControlledModAdd.sqirCuccaroImpl.gate bits N c flagIdx)
        (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.X b1Idx))))

/-- One window step's selected-add gate for the v=2 case
(binary 10).  X-normalizes b0 before/after the CCX cascade. -/
noncomputable def toyWindow2Case2Gate
    (bits N a k : Nat) (flagIdx b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 2
  Gate.seq (Gate.X b0Idx)
    (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
      (Gate.seq (ControlledModAdd.sqirCuccaroImpl.gate bits N c flagIdx)
        (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.X b0Idx))))

/-- **R7d'' — toy case-1 selected-add correctness.**

When v=1 (b0=true, b1=false), the target accumulator advances by
`tableValue a N 2 k 1`; otherwise unchanged.  Proof mirrors v=3
with the X-flip handling described above. -/
theorem toyWindow2Case1Gate_correct
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_target_val bits 2
        (Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = if b0 && !b1 then (acc + tableValue a N 2 k 1) % N else acc := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change cuccaro_target_val bits 2
      (Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = if b0 && !b1 then (acc + tableValue a N 2 k 1) % N else acc
  simp only [Gate.applyNat_seq]
  -- Outermost X(b1Idx): outside workspace.
  rw [Gate.applyNat_X]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b1Idx _ _ h_b1_out]
  -- Outer-second CCX: outside workspace (flagIdx).
  rw [Gate.applyNat_CCX]
  rw [cuccaro_target_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  -- Compute the inner CCX result, factoring through the inner X(b1Idx).
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  -- F0 reads.  Here F0 = update (update G b0Idx b0) b1Idx b1; we
  -- compute its values at the three positions, and also at b1Idx
  -- *after* the X-flip — which is just !b1 by update_idem.
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_eq]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F0_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- After the X-flip, the state at b1Idx is !b1; at b0Idx is b0; at flagIdx is false.
  rw [h_F0_b1]
  -- Now reads on (update F0 b1Idx (!b1)):
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b1Idx (!b1) b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b1Idx (!b1) b1Idx
        = !b1 := by
    rw [FormalRV.Framework.update_eq]
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b1Idx (!b1) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.false_xor]
  -- Merge the double-update at b1Idx via update_idem.
  rw [FormalRV.Framework.update_idem]
  -- Now: update (update (update G b0Idx b0) b1Idx (!b1)) flagIdx (b0 && !b1)
  -- Reorder via update_comm to bring flagIdx update closest to G.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Push b0Idx, b1Idx updates outside the mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx (!b1) _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx b0 _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  -- Drop the outside-workspace updates from cuccaro_target_val.
  rw [cuccaro_target_val_update_outside_workspace bits 2 b1Idx (!b1) _ h_b1_out]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b0Idx b0 _ h_b0_out]
  -- Close via R4b clean_targetDecode.
  exact ControlledModAdd.clean_targetDecode ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 1) acc flagIdx (b0 && !b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- **R7d'' — toy case-2 selected-add correctness.**

When v=2 (b0=false, b1=true), the target accumulator advances by
`tableValue a N 2 k 2`; otherwise unchanged.  Symmetric to v=1
with X on b0Idx. -/
theorem toyWindow2Case2Gate_correct
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_target_val bits 2
        (Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = if !b0 && b1 then (acc + tableValue a N 2 k 2) % N else acc := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change cuccaro_target_val bits 2
      (Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = if !b0 && b1 then (acc + tableValue a N 2 k 2) % N else acc
  simp only [Gate.applyNat_seq]
  -- Outermost X(b0Idx): outside workspace.
  rw [Gate.applyNat_X]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b0Idx _ _ h_b0_out]
  -- Outer-second CCX: outside workspace (flagIdx).
  rw [Gate.applyNat_CCX]
  rw [cuccaro_target_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  -- Compute inner CCX result via inner X(b0Idx).
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  rw [h_F0_b0]
  -- Reads on (update F0 b0Idx (!b0)):
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b0Idx (!b0) b0Idx
        = !b0 := by
    rw [FormalRV.Framework.update_eq]
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b0Idx (!b0) b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1),
        FormalRV.Framework.update_eq]
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b0Idx (!b0) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.false_xor]
  -- For the case-2 gate, the b0Idx update sequence is:
  -- update (update G b0Idx b0) b1Idx b1 -> (X) -> update (update (update G b0Idx b0) b1Idx b1) b0Idx (!b0)
  -- Reorder to bring the b0Idx (!b0) update to the right place:
  --   = update (update (update G b1Idx b1) b0Idx b0) b0Idx (!b0)   -- commute b1 and b0
  --   = update (update G b1Idx b1) b0Idx (!b0)                       -- update_idem
  -- Then update flagIdx ctrl on top, then commute.  Let's do it directly:
  -- The current expression after rw is:
  --   update (update (update (update G b0Idx b0) b1Idx b1) b0Idx (!b0)) flagIdx (!b0 && b1)
  -- First commute: swap the outer b0Idx (!b0) with b1Idx b1:
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  -- Now: update (update (update (update G b0Idx b0) b0Idx (!b0)) b1Idx b1) flagIdx ...
  -- Merge the double-update at b0Idx:
  rw [FormalRV.Framework.update_idem]
  -- Now: update (update (update G b1Idx b1) b0Idx (!b0)) flagIdx (!b0 && b1)
  -- Wait — the update_idem merged the b0Idx updates that were at the
  -- innermost (b0Idx b0) and the middle (b0Idx (!b0)) wrapping the
  -- swapped b1Idx update.  So after the swap+idem, the order is:
  --   update (update (update G b1Idx b1) b0Idx (!b0)) flagIdx ctrl
  -- The outermost update under flagIdx is at b0Idx, not b1Idx.
  -- So we must first swap flagIdx past b0Idx, then past b1Idx.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  -- Push b0Idx, b1Idx updates outside the mod-add.  Outermost is b0Idx.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx (!b0) _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx b1 _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  -- Drop the outside-workspace updates.  Outermost is b0Idx.
  rw [cuccaro_target_val_update_outside_workspace bits 2 b0Idx (!b0) _ h_b0_out]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b1Idx b1 _ h_b1_out]
  -- Close via R4b clean_targetDecode.
  exact ControlledModAdd.clean_targetDecode ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 2) acc flagIdx (!b0 && b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-! ### R7d''' — composed windowSize=2 selected-add gate

The composed gate runs all three nonzero-case selected-add gates in
sequence.  For any input window value `v ∈ {0, 1, 2, 3}`, exactly
one case fires (or none, for v=0), advancing the target accumulator
by `tableValue a N 2 k v` modulo `N`. -/

/-- Composed windowSize=2 selected-add gate: case1 ; case2 ; case3. -/
noncomputable def toyWindow2SelectedAddGate
    (bits N a k : Nat) (flagIdx b0Idx b1Idx : Nat) : Gate :=
  Gate.seq (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
    (Gate.seq (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
              (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx))

/-- Arithmetic helper: `windowedStepSpec` for v=0 reduces to `acc`
when `acc < N`. -/
theorem windowedStepSpec_window2_v0
    (a N k acc : Nat) (_hN_pos : 0 < N) (hacc : acc < N) :
    windowedStepSpec a N 2 k acc 0 = acc := by
  unfold windowedStepSpec
  rw [tableValue_zero, Nat.add_zero]
  exact Nat.mod_eq_of_lt hacc

/-! ### R7d^v — case-3 gate window-bit preservation helpers

These per-position helpers prove that `toyWindow2Case3Gate` preserves
the values at the external multiplier register positions `b0Idx`
and `b1Idx`.  They are the cleanest "outside workspace" cases and
the first step toward the full state-equality theorem
`toyWindow2Case3Gate_state_eq` (deferred to a follow-up tick).

Proof pattern (used by both):
1. Unfold the gate's 3-gate seq structure.
2. `change` to convert layout-form mod-add to SQIR-form (def-eq).
3. `simp only [Gate.applyNat_seq]` to expose the nested `Gate.applyNat`s.
4. Peel the outer CCX via `Gate.applyNat_CCX` + `update_neq` (direction:
   `h_bX_ne_flag`, since the pattern is `update _ flagIdx _ bXIdx`).
5. Peel the inner CCX via `Gate.applyNat_CCX`.
6. Substitute input reads at the three positions.
7. Simplify `xor false (true && true) = true`.
8. Reorder updates via `update_comm` (twice) to bring flagIdx innermost.
9. Push b0Idx/b1Idx outside the mod-add via
   `sqir_style_controlledModAddConst_gate_commute_update_outside_fun`.
10. Finish with `update_eq`. -/

/-- The case-3 gate preserves the value `true` at the external
multiplier register position `b0Idx`. -/
theorem toyWindow2Case3Gate_preserves_b0Idx
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) b0Idx = true := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b0Idx
      = true
  simp only [Gate.applyNat_seq]
  -- Peel outer CCX (writes at flagIdx; we read at b0Idx).
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
  -- Peel inner CCX.
  rw [Gate.applyNat_CCX]
  -- Compute input's value at the three positions.
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_input_b0, h_input_b1, h_input_flag]
  -- xor false (true && true) = true.
  simp only [Bool.and_self, Bool.false_xor]
  -- Reorder updates: bring flagIdx update innermost.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- State is now: update (update (update G flagIdx true) b0Idx true) b1Idx true.
  -- Push b1Idx (outermost) outside the mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  -- Read at b0Idx through outer b1Idx update (b0Idx ≠ b1Idx).
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
  -- Push b0Idx outside the mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  -- Read at b0Idx via update_eq.
  rw [FormalRV.Framework.update_eq]

/-- The case-3 gate restores the equality flag at `flagIdx` to its
original value `false` after the full CCX/modadd/CCX cycle.

The proof tracks the state through all three stages:
1. After the inner CCX, flagIdx is set to `xor false (true && true) = true`.
2. After the mod-add, flagIdx is preserved at `true` (via R4b's
   `clean_controlPreserved`).
3. After the outer CCX, flagIdx becomes `xor true (true && true) = false`. -/
theorem toyWindow2Case3Gate_restores_flagIdx
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) flagIdx = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  -- Helper: the input's values at b0Idx, b1Idx, flagIdx.
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- Inner state values (after mod-add ∘ CCX1 applied to input).
  -- We prove (a) MA b0Idx = true, (b) MA b1Idx = true, (c) MA flagIdx = true.
  -- Each follows the same skeleton as in `_preserves_b0Idx`.
  -- Set the inner expression abbreviation isn't ergonomic with simp/rw,
  -- so we inline each subproof.
  have h_MA_b0 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true))
        b0Idx = true := by
    rw [Gate.applyNat_CCX]
    rw [h_input_b0, h_input_b1, h_input_flag]
    simp only [Bool.and_self, Bool.false_xor]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_eq]
  have h_MA_b1 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true))
        b1Idx = true := by
    rw [Gate.applyNat_CCX]
    rw [h_input_b0, h_input_b1, h_input_flag]
    simp only [Bool.and_self, Bool.false_xor]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_eq]
  have h_MA_flag :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true))
        flagIdx = true := by
    rw [Gate.applyNat_CCX]
    rw [h_input_b0, h_input_b1, h_input_flag]
    simp only [Bool.and_self, Bool.false_xor]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    -- Goal: Gate.applyNat (...) (update (cuccaro_input_F 2 false 0 acc) flagIdx true) flagIdx = true
    -- This is R4b clean_controlPreserved on sqirCuccaroImpl.
    exact ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
      bits N (tableValue a N 2 k 3) acc flagIdx true
      hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
  -- Combine.
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) flagIdx
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_eq]
  rw [h_MA_b0, h_MA_b1, h_MA_flag]
  decide

/-- The case-3 gate preserves the value `true` at the external
multiplier register position `b1Idx`.  Symmetric to
`_preserves_b0Idx`. -/
theorem toyWindow2Case3Gate_preserves_b1Idx
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) b1Idx = true := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b1Idx
      = true
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
  rw [Gate.applyNat_CCX]
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_input_b0, h_input_b1, h_input_flag]
  simp only [Bool.and_self, Bool.false_xor]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- State: update (update (update G flagIdx true) b0Idx true) b1Idx true.
  -- Push b1Idx (outermost) outside the mod-add, then read via update_eq.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_eq]

/-! ### R7d^vii — scalar Cuccaro-workspace helpers for case-3 gate

These three per-position helpers prove that the case-3 toy gate
restores the internal Cuccaro-workspace scalar positions:

* Position 1 (Cuccaro dirty flag): `false`.
* Position 2 (Cuccaro carry-in): `false`.
* Position `2 + 2*bits` (top carry): `false`.

Each proof follows the same skeleton as `_preserves_b0Idx` /
`_preserves_b1Idx`, but the finishing rule is:
* `clean_flagFalse` for position 1.
* `sqir_style_controlledModAddConst_gate_carry_in_restored` for
  position 2 (the carry-in restore theorem is not in the R4b
  bundle, so we use the SQIR theorem directly — it's NOT in the
  forbidden list).
* `clean_topCarryFalse` for position `2 + 2*bits`. -/

/-- The case-3 gate restores the internal Cuccaro dirty flag at
position 1 to `false`. -/
theorem toyWindow2Case3Gate_internalFlagFalse
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) 1 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  have h_1_ne_flag : (1 : Nat) ≠ flagIdx := Ne.symm h_flag_ne_1
  have h_1_ne_b0 : (1 : Nat) ≠ b0Idx := by omega
  have h_1_ne_b1 : (1 : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) 1
      = false
  simp only [Gate.applyNat_seq]
  -- Peel outer CCX2 (writes at flagIdx; we read at 1, ≠ flagIdx).
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_flag]
  -- Peel inner CCX1.
  rw [Gate.applyNat_CCX]
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_input_b0, h_input_b1, h_input_flag]
  simp only [Bool.and_self, Bool.false_xor]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Push b1Idx outside mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
  -- Push b0Idx outside mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
  -- Apply clean_flagFalse on sqirCuccaroImpl with control = true.
  exact ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 3) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-3 gate restores the Cuccaro carry-in at position 2 to
`false`. -/
theorem toyWindow2Case3Gate_carryInRestored
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) 2 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  have h_2_ne_flag : (2 : Nat) ≠ flagIdx := by omega
  have h_2_ne_b0 : (2 : Nat) ≠ b0Idx := by omega
  have h_2_ne_b1 : (2 : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) 2
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_flag]
  rw [Gate.applyNat_CCX]
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_input_b0, h_input_b1, h_input_flag]
  simp only [Bool.and_self, Bool.false_xor]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
  -- Apply the SQIR carry_in_restored theorem (NOT in the forbidden list).
  exact sqir_style_controlledModAddConst_gate_carry_in_restored bits N
    (tableValue a N 2 k 3) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1

/-- The case-3 gate restores the Cuccaro top carry at position
`2 + 2*bits` to `false`. -/
theorem toyWindow2Case3Gate_topCarryFalse
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) (2 + 2 * bits) = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  have h_tc_ne_flag : (2 + 2 * bits : Nat) ≠ flagIdx := by omega
  have h_tc_ne_b0 : (2 + 2 * bits : Nat) ≠ b0Idx := by omega
  have h_tc_ne_b1 : (2 + 2 * bits : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) (2 + 2 * bits)
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_tc_ne_flag]
  rw [Gate.applyNat_CCX]
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_input_b0, h_input_b1, h_input_flag]
  simp only [Bool.and_self, Bool.false_xor]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_tc_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_tc_ne_b0]
  -- Apply clean_topCarryFalse on sqirCuccaroImpl with control = true.
  exact ControlledModAdd.clean_topCarryFalse ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 3) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-! ### R7d^viii: target-bit and read-bit extraction for case-3 gate

These per-position helpers extract individual target/read register bits
from the case-3 gate's output, via the converse decoder lemmas
`cuccaro_target_val_eq_implies_bits_match` and
`cuccaro_read_val_eq_implies_bits_match`.

For the target-bit helper we instantiate `toyWindow2Case3Gate_correct`
at `b0 = b1 = true` (case 3 firing condition) to get the
target_val decode equality, then apply the converse.

For the read-bit helper we first prove a `_readVal` companion (mirroring
`toyWindow2Case3Gate_correct` but routing through `clean_readZero`
instead of `clean_targetDecode`), then apply the converse at `S = 0`.

**No direct call to `sqir_style_controlledModAddConst_gate_clean`** —
the mod-add target/read are extracted through the R4b/R5b projections
`ControlledModAdd.clean_targetDecode` and `ControlledModAdd.clean_readZero`. -/

/-- The case-3 gate leaves the Cuccaro read register at `0` after the
full sequence (independent of the window bits `b0`, `b1`).

Proof mirrors `toyWindow2Case3Gate_correct` but uses
`cuccaro_read_val_update_outside_workspace` for the outside-workspace
invariance steps and `ControlledModAdd.clean_readZero` at the finish. -/
theorem toyWindow2Case3Gate_readVal
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_read_val bits 2
        (Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = 0 := by
  -- Auxiliary facts (mirror toyWindow2Case3Gate_correct).
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  -- Convert the gate to SQIR-form.
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change cuccaro_read_val bits 2
      (Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = 0
  simp only [Gate.applyNat_seq]
  -- Step 1: outer CCX is just an update at flagIdx, outside workspace.
  rw [Gate.applyNat_CCX]
  rw [cuccaro_read_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  -- Step 2: compute the inner CCX result.
  rw [Gate.applyNat_CCX]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_eq]
  have h_F0_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F0_b0, h_F0_b1, h_F0_flag]
  -- xor false (b0 && b1) = b0 && b1.
  simp only [Bool.false_xor]
  -- Step 3: reorder updates to bring flagIdx update closest to cuccaro_input_F.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Step 4: push b0Idx, b1Idx updates outside the mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx b1 _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx b0 _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  -- Step 5: drop the outside-workspace updates from cuccaro_read_val.
  rw [cuccaro_read_val_update_outside_workspace bits 2 b1Idx b1 _ h_b1_out]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b0Idx b0 _ h_b0_out]
  -- Step 6: apply R4b/R5b clean_readZero.
  exact ControlledModAdd.clean_readZero ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 3) acc flagIdx (b0 && b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-3 gate's output at target-bit position `2 + 2*i + 1`
(for `i < bits`) equals the `i`-th bit of `(acc + tableValue a N 2 k 3) % N`.

Proof: instantiate `toyWindow2Case3Gate_correct` at `b0 = b1 = true`
(case 3 firing condition) to get the target_val decode equality, then
apply the converse decoder `cuccaro_target_val_eq_implies_bits_match`.

This is the bit-level analog of `sqir_modmult_step_target_bit`. -/
theorem toyWindow2Case3Gate_targetBit
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) (2 + 2 * i + 1)
      = ((acc + tableValue a N 2 k 3) % N).testBit i := by
  have h_correct := toyWindow2Case3Gate_correct bits N a k acc flagIdx b0Idx b1Idx
    true true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  -- h_correct: cuccaro_target_val ... = if true && true then ... else acc
  -- Reduce to: cuccaro_target_val ... = (acc + tableValue) % N.
  have h_target_decode :
      cuccaro_target_val bits 2
          (Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
            (toyWindow2Case3Input acc b0Idx b1Idx true true))
        = (acc + tableValue a N 2 k 3) % N := by
    simpa using h_correct
  -- Bound check for the converse.
  have h_acc'_lt_N : (acc + tableValue a N 2 k 3) % N < N := Nat.mod_lt _ hN_pos
  have h_acc'_lt : (acc + tableValue a N 2 k 3) % N < 2^bits :=
    Nat.lt_of_lt_of_le h_acc'_lt_N hN
  -- Apply the converse decoder.
  exact cuccaro_target_val_eq_implies_bits_match bits 2 _ _ h_acc'_lt
    h_target_decode i hi

/-- The case-3 gate's output at read-bit position `2 + 2*i + 2`
(for `i < bits`) equals `false`.

Proof: use `toyWindow2Case3Gate_readVal` to get the read_val = 0
equality, then apply the converse decoder
`cuccaro_read_val_eq_implies_bits_match` at `S = 0`; finish with
`Nat.zero_testBit`.

This is the bit-level analog of `sqir_modmult_step_read_bit`. -/
theorem toyWindow2Case3Gate_readBit
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) (2 + 2 * i + 2)
      = false := by
  have h_rd := toyWindow2Case3Gate_readVal bits N a k acc flagIdx b0Idx b1Idx
    true true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
  have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd i hi
  rw [h_bit, Nat.zero_testBit]

/-! ### R7d^ix: above-layout helper for case-3 gate

For positions `q ≥ 2 + 2*bits + 1` distinct from `b0Idx`, `b1Idx`,
`flagIdx`, the case-3 gate leaves `q` at `false` (its input value).

Proof strategy mirrors the SQIRModMult `sqir_modmult_step_at_untouched_pos`
trick: at q the input is `false`, so `update input q false = input` (no-op).
By the SQIR commute lemma, the mod-add commutes with this trivial update,
yielding `applyNat mod-add input q = false` directly.

The CCX layers also commute with the q-update (q ∉ {b0Idx, b1Idx, flagIdx}),
so the full gate's output at q equals the input's value at q, which is
false by `cuccaro_input_F_above_eq_false`. -/

/-- The case-3 gate's output is `false` at any position `q` above the
SQIR/Cuccaro layout (`q ≥ 2 + 2*bits + 1`) that is distinct from the
window bits `b0Idx`/`b1Idx` and the lookup equality flag `flagIdx`. -/
theorem toyWindow2Case3Gate_aboveLayoutFalse
    (bits N a k acc flagIdx b0Idx b1Idx q : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (hq_above : 2 + 2 * bits + 1 ≤ q)
    (hq_ne_b0 : q ≠ b0Idx) (hq_ne_b1 : q ≠ b1Idx) (hq_ne_flag : q ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) q = false := by
  -- Auxiliary facts.
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_q_ne_one : q ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  -- Convert the gate to SQIR-form.
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) q
      = false
  simp only [Gate.applyNat_seq]
  -- Step 1: peel the outer CCX (q ≠ flagIdx).
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_flag]
  -- Step 2: peel the inner CCX.
  rw [Gate.applyNat_CCX]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_F0_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F0_b0, h_F0_b1, h_F0_flag]
  simp only [Bool.and_self, Bool.false_xor]
  -- Step 3: reorder updates to bring flagIdx innermost.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Step 4: push b1Idx, b0Idx updates outside the mod-add and read through.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b0]
  -- Goal: Gate.applyNat (mod-add) (update F flagIdx true) q = false.
  -- Use the commute trick: input at q is false, so mod-add output at q is false.
  have h_input_q :
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true) q = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_flag]
    exact cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt
  have h_in_eq :
      update (update (cuccaro_input_F 2 false 0 acc) flagIdx true) q false
        = update (cuccaro_input_F 2 false 0 acc) flagIdx true := by
    -- Cannot use `rw [show false = (...) q from h_input_q.symm]` here because
    -- `cuccaro_input_F 2 false 0 acc` contains a `false` literal that would
    -- be hit by the rewrite.  Use funext instead.
    funext p
    by_cases hpq : p = q
    · subst hpq
      rw [FormalRV.Framework.update_eq]
      exact h_input_q.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hpq]
  have h_commute :=
    sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
      (tableValue a N 2 k 3) flagIdx q false
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true)
      h_q_out h_q_ne_one hq_ne_flag
  rw [h_in_eq] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

end Windowed
end VerifiedShor
