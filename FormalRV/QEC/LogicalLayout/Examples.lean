/-
  FormalRV.QEC.LogicalLayout.Examples
  ───────────────────────────────────
  **Worked logical-indexing examples, kernel-checked.**

  Two VERIFIED code blocks (real codes, real user-declared logical bases):

      block 0 : C422  = [[4,2,2]]  (k = 2, basis `code422Logical`, VALID)
      block 1 : BB18  = [[18,2,·]] bivariate-bicycle (k = 2,
                         basis `bbSmallLogicalBasis`)

  Consecutive labeling:  wire 0 ↦ C422.slot 0,  wire 1 ↦ C422.slot 1,
                         wire 2 ↦ BB18.slot 0,  wire 3 ↦ BB18.slot 1
  — the John example in miniature: with blocks `[LP(k=14), BB(k=6)]` the
  first 14 wires are LP's logical qubits and wire 14 is BB's first.
-/
import FormalRV.QEC.LogicalLayout.Labeling
import FormalRV.QEC.LogicalLayout.Notation
import FormalRV.QEC.Instances
import FormalRV.QEC.LogicalFinder
import FormalRV.PPM.Syntax.Notation

namespace FormalRV.QEC.LogicalLayout.Examples

open FormalRV.QEC
open FormalRV.QEC.LogicalLayout
open FormalRV.PPM.Prog

/-! ## §1. The user's block declarations (code + k + logical basis). -/

/-- A [[4,2,2]] block: 2 logical qubits, basis declared and VERIFIED. -/
def blk422 : CodeBlock :=
  ⟨"C422", Instances.code422, 2, Instances.code422Logical⟩

/-- A [[18,2]] bivariate-bicycle (LDPC) block: 2 logical qubits, basis
computed by `LogicalFinder` and verified. -/
def blkBB : CodeBlock :=
  ⟨"BB18", LogicalFinder.bbSmall, 2, LogicalFinder.bbSmallLogicalBasis⟩

-- THE layout declaration — one line per block, order = wire order.
logical_layout demoLayout {
  block blk422;
  block blkBB
}

/-! ## §2. The labeling, kernel-checked. -/

-- wire-by-wire: the first k₀ = 2 wires are C422's logical qubits,
-- wire 2 is BB18's FIRST logical qubit (John's "15th qubit" in miniature)
example : addrOf demoLayout.blocks 0 = ⟨0, 0⟩ := by decide
example : addrOf demoLayout.blocks 1 = ⟨0, 1⟩ := by decide
example : addrOf demoLayout.blocks 2 = ⟨1, 0⟩ := by decide
example : addrOf demoLayout.blocks 3 = ⟨1, 1⟩ := by decide

example : capacityOf demoLayout.blocks = 4 := by decide

-- the layout obligations: structural wf is FREE (generated theorem) …
example : demoLayout.wfStructural = true := demoLayout_wfStructural

-- … and the C422 basis is fully verified at kernel scale
example : Instances.code422Logical.valid = true := by decide

/-! ## §3. Labeling a PPM program. -/

/-- A joint-measurement program across both blocks: a CROSS-BLOCK joint
Pauli measurement (= inter-block surgery once lowered), a frame, a T. -/
def demoProg : PPMProg := ppm! {
  c0 = Measure X[0]Z[2];
  c1 = Measure Z[1]Z[3];
  frame X[2];
  useT[3]
}

example : supports demoLayout.blocks demoProg = true := by decide

-- the joint measurement X[0]Z[2] spans BOTH blocks — surgery datum
example :
    blocksTouched demoLayout.blocks [⟨0, .x⟩, ⟨2, .z⟩] = [0, 1] := by
  decide

-- its footprint inside each block
example :
    slotsInBlock demoLayout.blocks [⟨0, .x⟩, ⟨2, .z⟩] 0 = [(0, .x)] := by
  decide
example :
    slotsInBlock demoLayout.blocks [⟨0, .x⟩, ⟨2, .z⟩] 1 = [(0, .z)] := by
  decide

-- the second measurement Z[1]Z[3] also spans both blocks
example :
    blocksTouched demoLayout.blocks [⟨1, .z⟩, ⟨3, .z⟩] = [0, 1] := by
  decide

/-! ## §4. The labeled rendering. -/

/-- `#eval renderProg demoLayout.blocks demoProg`:

    c0 = Measure X[C422_0.0]·Z[BB18_1.0];
    c1 = Measure Z[C422_0.1]·Z[BB18_1.1];
    frame Z[BB18_1.0];
    useT[BB18_1.1]
-/
example :
    renderStmt demoLayout.blocks (.useT 3) = "useT[BB18_1.1]" := by
  native_decide

/-! ## §5. BLOCK FARMS: `blocks 1024 of …` — John's surface-code fleet.

One declaration line yields 1024 identical blocks; the parser emits the
literal `List.replicate 1024 blk`, and the CLOSED-FORM theorems index any
wire by division — no 1024-step walk anywhere. -/

-- a farm of 1024 identical [[4,2,2]] blocks (stand-in for 1024 surface
-- patches; for surface codes k = 1 and the slot is always 0) + one BB
logical_layout farmLayout {
  blocks 1024 of blk422;
  block blkBB
}

-- the parser recognized the farm as LITERAL replication (machine-readable)
example : farmLayout.blocks = List.replicate 1024 blk422 ++ [blkBB] := rfl

-- capacity by the closed form: 1024·2 + 2 = 2050 — no list walk
example : capacityOf farmLayout.blocks = 2050 := by
  show capacityOf (List.replicate 1024 blk422 ++ [blkBB]) = 2050
  rw [capacityOf_append, capacityOf_replicate]
  rfl

-- wire 2047 = farm block 1023, slot 1 — BY DIVISION (closed form)
example : addrOf farmLayout.blocks 2047 = ⟨1023, 1⟩ := by
  show addrOf (List.replicate 1024 blk422 ++ [blkBB]) 2047 = _
  rw [addrOf_append_left _ _ _ (by
        rw [capacityOf_replicate, show blk422.k = 2 from rfl]
        omega),
      addrOf_replicate 1024 blk422 2047 (by decide) (by
        rw [show blk422.k = 2 from rfl]
        omega),
      show blk422.k = 2 from rfl]

-- wire 2048 = the BB block's FIRST logical qubit (the segment law)
example : addrOf farmLayout.blocks 2048 = ⟨1024, 0⟩ := by
  show addrOf (List.replicate 1024 blk422 ++ [blkBB]) 2048 = _
  rw [addrOf_append_right _ _ _ (by
        rw [capacityOf_replicate, show blk422.k = 2 from rfl]
        omega)]
  show LogicalAddr.mk ((List.replicate 1024 blk422).length
      + (addrOf [blkBB] (2048 - capacityOf (List.replicate 1024 blk422))).block)
      _ = _
  rw [capacityOf_replicate, List.length_replicate]
  rfl

-- the farm layout is structurally well-formed FOR FREE (generated theorem)
example : farmLayout.wfStructural = true := farmLayout_wfStructural

end FormalRV.QEC.LogicalLayout.Examples
