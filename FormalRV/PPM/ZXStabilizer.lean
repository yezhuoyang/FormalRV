/-
  FormalRV.Framework.ZX — ZX calculus as the IR for lattice surgery, grounded in
  PPM.

  Strategic design (John 2026-06-02): use ZX calculus as the intermediate
  representation for lattice surgery, and PROVE it is consistent with our PPM
  layer.  The motivating fact (Tan, Niu & Gidney, "A SAT Scalpel for Lattice
  Surgery", §II-D: *cube = spider, pipe = wire*): a surface-code lattice-surgery
  merge IS a ZX spider, and a ZX spider (in the measurement/Clifford fragment) IS
  a Pauli-product measurement (PPM).  So EVERY lattice-surgery implementation —
  including optimized ones (minimum spacetime volume) — goes through PPM, and is
  verifiable by reducing its ZX IR to a PPM program and checking it in our
  already-verified surgery/PPM layer.

  This module builds the FIRST rung: the phase-free MEASUREMENT FRAGMENT of ZX,
  where each spider is a Pauli-product measurement, translated to our
  `StabProgram` PPM IR, and proven to run as the surgery merge state-map
  `measureChecks`.  So: ZX diagram → PPM program → surgery (the user's
  "all lattice surgery goes through PPM", made into a theorem).

  ## Roadmap (this is the foundation; full ZX is the program)

  * NOW: spiders-as-PPM (Z-spider = ∏Z measurement, X-spider = ∏X), the
    ZX→PPM translation, and ZX-merge ↔ surgery-`measureChecks` consistency.
  * NEXT: spider phases (π/2, π, …) for non-Clifford / Y-basis (Tan's `YCube`);
    spider FUSION and the other ZX rewrite rules, proven to PRESERVE the PPM
    semantics (so ZX-rewriting = optimization that the framework verifies);
    general (non-linear) diagrams via a connectivity graph.

  No Mathlib.  Pure List / the PauliString algebra + the Gottesman update.
  No `sorry`, no `axiom`.
-/

import FormalRV.LatticeSurgery.SurgeryReduction

namespace FormalRV.Framework.ZX

open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.Framework.SurgeryReadout
open FormalRV.Framework.SurgeryReduction
open FormalRV.Framework.StabProgram
open FormalRV.Framework.PPMOp
open FormalRV.Framework.PauliSem

/-! ## (1) The measurement fragment of ZX -/

/-- A spider's colour: `Z` (green) or `X` (red). -/
inductive ZXColor | Z | X
  deriving DecidableEq, Repr

/-- A phase-free stabilizer ZX SPIDER as a Pauli-product MEASUREMENT.  A Z-spider
    over `support` measures `∏_{i∈support} Z_i`; an X-spider measures
    `∏_{i∈support} X_i`.  (The full ZX calculus adds non-zero phases and fusion;
    this is the measurement fragment that realises lattice surgery — Tan §II-D.) -/
structure ZXSpider where
  color   : ZXColor
  support : BoolVec
  deriving Repr

/-- The Pauli operator a spider measures (`Z`-spider ↦ `zRow`, `X`-spider ↦ `xRow`). -/
def ZXSpider.toPauli (sp : ZXSpider) : PauliString :=
  match sp.color with
  | ZXColor.Z => zRow sp.support
  | ZXColor.X => xRow sp.support

/-- The PPM op a spider compiles to: measure its Pauli. -/
def ZXSpider.toStabOp (sp : ZXSpider) : StabOp := StabOp.meas sp.toPauli

/-- Build a spider from its colour and the list of qubit indices in its support
    (over `n` qubits).  Used by the LaSre→PPM importer to emit compact diagrams. -/
def mkSpider (color : ZXColor) (idxs : List Nat) (n : Nat) : ZXSpider :=
  { color := color, support := (List.range n).map (fun i => idxs.contains i) }

/-- A ZX diagram (measurement fragment) — a sequence of spiders. -/
abbrev ZXDiagram := List ZXSpider

/-- **ZX → PPM.**  Translate a ZX diagram to a PPM program (our `StabProgram`
    IR): each spider becomes a Pauli-product measurement.  This is the formal
    statement that lattice surgery (as a ZX diagram) GOES THROUGH PPM. -/
def zxToPPM (d : ZXDiagram) : StabProgram := d.map ZXSpider.toStabOp

/-- The ZX diagram's stabilizer semantics = running its PPM realisation on the
    all-`+1` outcome branch. -/
def zxRun (d : ZXDiagram) (s : StabilizerState) : StabilizerState :=
  runProgram (zxToPPM d) [] s

/-! ## (2) ZX ↔ PPM ↔ surgery consistency

    A surgery merge expressed in the ZX IR runs as the surgery's `measureChecks`
    state-map — so the ZX IR is consistent with the verified surgery/PPM layer. -/

/-- The X-type surgery merge as a ZX diagram: every merged X-check is an X-spider. -/
def mergeToZX_X (g : SurgeryGadget) : ZXDiagram :=
  g.merged_hx.map (fun row => { color := ZXColor.X, support := row })

/-- The Z-type surgery merge as a ZX diagram: every merged Z-check is a Z-spider. -/
def mergeToZX_Z (g : SurgeryGadget) : ZXDiagram :=
  g.merged_hz.map (fun row => { color := ZXColor.Z, support := row })

/-- The X-merge ZX diagram compiles to exactly the surgery X-schedule program. -/
theorem mergeZX_X_eq_schedule (g : SurgeryGadget) :
    zxToPPM (mergeToZX_X g) = (merged_stabilizers_X g).map StabOp.meas := by
  simp only [zxToPPM, mergeToZX_X, merged_stabilizers_X, ZXSpider.toStabOp,
    ZXSpider.toPauli, List.map_map, Function.comp_def]

/-- **ZX ↔ PPM ↔ surgery (X-type).**  Running the surgery merge's ZX diagram
    equals the surgery merge state-map `measureChecks` — the lattice surgery,
    expressed in the ZX IR, reduces to PPM (our verified layer).  Axiom-free. -/
theorem mergeZX_X_runs_as_surgery (g : SurgeryGadget) (s : StabilizerState) :
    zxRun (mergeToZX_X g) s = measureChecks (merged_stabilizers_X g) s := by
  unfold zxRun
  rw [mergeZX_X_eq_schedule]
  exact surgery_schedule_runs_as_merge g s

/-- The Z-merge ZX diagram compiles to exactly the surgery Z-schedule program. -/
theorem mergeZX_Z_eq_schedule (g : SurgeryGadget) :
    zxToPPM (mergeToZX_Z g) = (merged_stabilizers_Z g).map StabOp.meas := by
  simp only [zxToPPM, mergeToZX_Z, merged_stabilizers_Z, ZXSpider.toStabOp,
    ZXSpider.toPauli, List.map_map, Function.comp_def]

/-- **ZX ↔ PPM ↔ surgery (Z-type).** -/
theorem mergeZX_Z_runs_as_surgery (g : SurgeryGadget) (s : StabilizerState) :
    zxRun (mergeToZX_Z g) s = measureChecks (merged_stabilizers_Z g) s := by
  unfold zxRun
  rw [mergeZX_Z_eq_schedule]
  exact surgery_schedule_runs_as_merge_Z g s

/-! ## (3) Smoke: a ZX diagram of two X-spiders runs as the PPM program. -/

example (s : StabilizerState) :
    zxRun [{ color := ZXColor.X, support := [true, false] },
           { color := ZXColor.X, support := [false, true] }] s
      = runProgram [StabOp.meas (xRow [true, false]), StabOp.meas (xRow [false, true])] [] s := by
  rfl

end FormalRV.Framework.ZX
