/-
  FormalRV.QEC.Gidney21.FoldPPMProg
  ─────────────────────────────────
  **★ THE PPMProg → ONE composed LaS diagram DRIVER — the missing central seam. ★**

  The audit's `composition_gap`: `progGadgets`/`productGadgets` route a whole PPM
  program to a LIST of individually-verified gadgets (`progGadgets_each_verified`),
  but no theorem WELDS that list into ONE spacetime diagram carrying a SINGLE
  `LaSCorrectFull` — the two stacks (`Gidney21.progGadgets` per-gadget vs
  `LatticeSurgery.weldChain` composed) were never bridged.

  This file bridges them.  `foldLaSList` DERIVES the diagram list from the PPM
  SYNTAX TREE (via the existing `progGadgets`/`gadgetFor` catalog — the same
  `PPMProg`/`PPMStmt`/`PauliProduct` types `lowerRot` emits), `foldPPMProgLaS`
  welds it into one diagram, and `foldPPMProg_LaSCorrectFull` certifies the whole
  welded program through `weldChain_LaSCorrectFull` — a SINGLE global flow
  obligation on the composed diagram, NOT a per-gadget conjunction.

  HONEST SCOPE (the next brick): the surfaces `ss`, board `conn`, and ports are
  the SCHEDULER/frame-tracker's (untrusted-producer) output; `chainOK` is the
  VERIFIED GATE that certifies them against the syntax-DERIVED diagram list.  So
  this closes the SYNTAX→DIAGRAM→one-cert seam; making the producer automatic and
  ∀-program (idle insertion, width uniformization, frame threading for the
  mixed/Y-dominated catalog) is the heterogeneous-engine brick that follows.
-/
import FormalRV.QEC.Gidney21.GadgetToLaS
import FormalRV.QEC.LatticeSurgery.ChainComposition

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC.LaSre
open FormalRV.PPM.Prog (PPMProg PPMStmt PauliProduct PFactor PKind)

/-! ## §1. Fold a PPM program to its welded lattice-surgery diagram. -/

/-- **The LaSre diagram list a PPM program folds to.**  Route the program to its
verified gadget KINDS (`progGadgets`, the existing PPM→catalog map), then take
each kind's verified diagram (`gadgetFor … |>.L`).  Derived ENTIRELY from the
PPM syntax tree — no hand-assembly. -/
def foldLaSList (prog : PPMProg) : List LaSre :=
  (progGadgets prog).map (fun k => (gadgetFor k).L)

/-- The matching per-gadget surfaces (each gadget's OWN surface; the
frame-threading product maps for a real schedule are supplied as `ss`). -/
def foldSurfList (prog : PPMProg) : List Surf :=
  (progGadgets prog).map (fun k => (gadgetFor k).S)

/-- **The whole-program spacetime diagram** — weld the per-statement gadget
diagrams (derived from the PPM syntax) into ONE diagram across board `conn` at
uniform gadget height `h`. -/
def foldPPMProgLaS (h : Nat) (conn : List (Nat × Nat)) (prog : PPMProg) : LaSre :=
  weldChain h conn (foldLaSList prog)

/-! ## §2. THE SEAM — the whole program is ONE `LaSCorrectFull` diagram. -/

/-- **★ A WHOLE PPM PROGRAM FOLDS TO ONE VERIFIED LATTICE-SURGERY DIAGRAM ★.**
For ANY PPM program `prog`, if the scheduler-supplied surfaces `ss` (and board
`conn`, ports, spec `paulis`) pass the per-gadget+per-interface `chainOK` against
the SYNTAX-DERIVED diagram list `foldLaSList prog`, and the composite ports match,
then the welded whole-program diagram passes the COMPLETE global `LaSCorrectFull`
— a single composed obligation, obtained from per-gadget checks via the chain
corollary (never a `native_decide` on the whole welded grid).

This is the missing PPMProg→one-composed-cert driver: it folds a real `PPMProg`
(the same syntax `lowerRot` emits) into one `weldChain` carrying one
`LaSCorrectFull`, closing the `composition_gap` at the program level. -/
theorem foldPPMProg_LaSCorrectFull
    (h n : Nat) (conn : List (Nat × Nat)) (w wj : Nat) (prog : PPMProg)
    (ss : List Surf) (ports : List Port) (paulis : Nat → Nat → Pauli)
    (hc : chainOK h n conn w wj (foldLaSList prog) ss = true)
    (hPorts : portsOK (weldChainSurf h ss) ports paulis n = true) :
    LaSCorrectFull (foldPPMProgLaS h conn prog) (weldChainSurf h ss) ports paulis n = true :=
  weldChain_LaSCorrectFull h n conn w wj (foldLaSList prog) ss ports paulis hc hPorts

/-! ## §3. A REAL PPM PROGRAM, FOLDED AND CERTIFIED END-TO-END.

  A genuine 2-statement program — measure `Z̄` on logical qubit 0, then measure
  `Z̄` on qubit 0 again — driven entirely through the syntax: `progGadgets`
  routes it to `[mZ1, mZ1]`, `foldLaSList` takes their diagrams `[memoryLaS,
  memoryLaS]`, and `foldPPMProg_LaSCorrectFull` welds + certifies the whole
  two-measurement worldline as ONE diagram realizing `Z̄` (NOT a per-gadget
  conjunction). -/

/-- The program: `c0 = Measure Z[0]` ; `c1 = Measure Z[0]`. -/
def demoZZProg : PPMProg :=
  [PPMStmt.measure 0 [{ qubit := 0, kind := PKind.z }],
   PPMStmt.measure 1 [{ qubit := 0, kind := PKind.z }]]

/-- The syntax routes it to two weight-1 `M_Z` gadgets. -/
theorem demoZZ_gadgets : progGadgets demoZZProg = [GadgetKind.mZ1, GadgetKind.mZ1] := by
  native_decide

/-- ...whose diagrams are two single-patch worldlines (definitional). -/
theorem demoZZ_diagrams : foldLaSList demoZZProg = [memoryLaS, memoryLaS] := rfl

/-- The scheduler-supplied data for this single-qubit worldline: the per-gadget
`M_Z` surfaces, the single-patch board, and the bottom/top `Z̄` ports of the
6-step welded worldline. -/
def demoZZSurfs : List Surf := [mZ1Surf, mZ1Surf]
def demoZZPorts : List Port := [⟨0, 0, 0, 4, 5⟩, ⟨0, 0, 5, 4, 5⟩]
def demoZZPaulis : Nat → Nat → Pauli := fun _ _ => Pauli.Z

/-- Each per-gadget + per-interface check passes (each SMALL — one gadget's own
`valid`+`funcOK`, plus the single weld interface). -/
theorem demoZZ_chainOK :
    chainOK 3 1 [(0, 0)] 1 1 (foldLaSList demoZZProg) demoZZSurfs = true := by
  native_decide

/-- The composite ports match the `Z̄` spec on the welded worldline. -/
theorem demoZZ_ports :
    portsOK (weldChainSurf 3 demoZZSurfs) demoZZPorts demoZZPaulis 1 = true := by
  native_decide

/-- **★ THE WHOLE 2-STATEMENT PROGRAM FOLDS TO ONE VERIFIED LATTICE-SURGERY
DIAGRAM ★** — `foldPPMProg_LaSCorrectFull` welds the syntax-derived gadget
diagrams into one spacetime diagram passing the COMPLETE global `LaSCorrectFull`,
realizing the program's `Z̄` measurement.  Obtained from the per-gadget +
per-interface `chainOK` (never a `native_decide` on the whole welded diagram). -/
theorem demoZZ_correct :
    LaSCorrectFull (foldPPMProgLaS 3 [(0, 0)] demoZZProg)
      (weldChainSurf 3 demoZZSurfs) demoZZPorts demoZZPaulis 1 = true :=
  foldPPMProg_LaSCorrectFull 3 1 [(0, 0)] 1 1 demoZZProg
    demoZZSurfs demoZZPorts demoZZPaulis demoZZ_chainOK demoZZ_ports

end FormalRV.QEC.Gidney21
