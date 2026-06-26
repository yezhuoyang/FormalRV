/- ToyWindow2Case3StateEquality — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.ReservedExtensionSlot

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
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
   with the mod-add (via `style_controlledModAddConst_gate_commute_update_outside_fun`)
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
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx b1 _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [style_controlledModAddConst_gate_commute_update_outside_fun bits N
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


end Windowed
end VerifiedShor
