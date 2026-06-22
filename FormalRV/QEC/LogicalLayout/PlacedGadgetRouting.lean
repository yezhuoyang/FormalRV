/-
  FormalRV.QEC.LogicalLayout.PlacedGadgetRouting
  ----------------------------------------------
  **THE GADGET → HARDWARE BRIDGE — placing a routed Shor program on the actual
  d=27 surface-code board, deriving the routing, and counting the device qubits,
  scaling to the Gidney-Ekerå 20-million-qubit machine.**

  We have a routed program: a real Shor arithmetic circuit (Cuccaro adder,
  modular multiplier, modexp) lowered to PPM and routed by `progGadgets`/
  `progPlaced` to a list of VERIFIED lattice-surgery gadgets, each carrying the
  logical qubits it acts on (`PlacedGadget`).  This file places that program on
  the hardware:

    * `progMerges` — each gadget's seam pairs (a weight-k join → its `k-1` seams);
    * `progBoard` — the fixed d=27 board (`FixedBoard.place`) sized to the
      program's logical width;
    * the routing is DERIVED from the placement (`Geometry.channelVolume` /
      `routingQubits`), NOT a free oracle — real lattice-surgery routing;
    * `progDeviceQubits` — data + factory + routing via the System `deviceQubits`
      decomposition, with the magic-factory share from the program's CCZ count.

  The SAME definitions, instantiated at `6144` patches / RSA-2048 / d=27,
  reproduce the GE2021 device total `22 071 129` (`progDeviceQubits_eq_rsa2048`)
  — small board for an adder now, 20M-qubit board for 2048-bit Shor, one set of
  formulas.

  SCOPE (honest): this is placement + DERIVED routing + per-gadget verification +
  resource count.  It is NOT (and does not claim) the composed-semantic guarantee
  that the welded channels realize the program's logical map — that is the
  orthogonal, still-open flow-composition layer.  The routing here is a verified
  resource ceiling on the real architecture.
-/
import FormalRV.QEC.LogicalLayout.DerivedRoutingBridge
import FormalRV.QEC.Gidney21.GadgetToLaS
import FormalRV.QEC.Gidney21.CuccaroAdderDemo

namespace FormalRV.QEC.Geometry

open FormalRV.QEC.Gidney21
open FormalRV.PPM.Prog
open FormalRV.System.MagicScheduleComplete
open FormalRV.System.MagicStateReadiness
open FormalRV.System.Architecture
open FormalRV.System.RoutingResourceModel

/-! ## §1. Gadget → seam merge-pairs, and the board. -/

/-- The seam merge-pairs of one placed gadget: a weight-`k` joint measurement is
a chain of `k-1` adjacent seams `[(q₀,q₁),(q₁,q₂),…]`; weight ≤ 1 (readouts) and
single-patch gadgets contribute none.  Driven purely by `g.qubits` (the ordered
factor qubits), matching the chain-of-I-seams `mergeZ3LaS`/`mergeZ4LaS` boxes. -/
def gadgetMerges (g : PlacedGadget) : List (Nat × Nat) :=
  match g.qubits with
  | []        => []
  | [_]       => []
  | q :: rest => (q :: rest).zip rest

/-- All seam merge-pairs of a whole routed program. -/
def progMerges (prog : PPMProg) : List (Nat × Nat) :=
  (progPlaced prog).flatMap gadgetMerges

/-- Logical patches the program needs = its qubit width (an upper bound on the
distinct-qubit count; exact for the dense arithmetic lowerings). -/
def progPatches (prog : PPMProg) : Nat := PPMProg.width prog

/-- The fixed single-row d=27 board sized to the program's logical width, with
the patches placed at `(i, 0)` (`FixedBoard.place`). -/
def progBoard (prog : PPMProg) : Board :=
  { width := PPMProg.width prog, place := place }

/-! ## §2. The magic-factory count (the share `progPlaced` does not carry). -/

/-- CCZ/Toffoli magic count of one statement (`useCCZ`/`useT` produce no merge,
so they are counted here for the factory share). -/
def stmtCCZ : PPMStmt → Nat
  | .useCCZ _ _ _ => 1
  | .useT _       => 1
  | _             => 0

def progCCZ (prog : PPMProg) : Nat := (prog.map stmtCCZ).sum

/-! ## §3. The device-qubit count — data + factory + DERIVED routing. -/

/-- Data qubits = patches × per-patch physical size. -/
def progDataQubits (perPatch : Nat) (prog : PPMProg) : Nat := progPatches prog * perPatch

/-- DERIVED routing fabric (equal-area serial highway, `FixedBoard.routingQubits`). -/
def progRoutingQubits (perPatch : Nat) (prog : PPMProg) : Nat :=
  routingQubits perPatch (progPatches prog)

/-- Magic-factory qubits from the program's CCZ count (8-hour budget, CCZ spec). -/
def progFactoryQubits (prog : PPMProg) : Nat :=
  factoryQubitShare (progCCZ prog) 28800000000 ccz_spec_qianxu

/-- **★ The whole device-qubit count for a routed program — NO free oracle ★** —
data + factory + DERIVED routing, via the System `deviceQubits` decomposition. -/
def progDeviceQubits (perPatch : Nat) (prog : PPMProg) : Nat :=
  deviceQubits (progDataQubits perPatch prog) (progFactoryQubits prog)
               (progRoutingQubits perPatch prog)

/-- The routing SPACE-TIME volume of the program under the board placement
(`Geometry.progRoutingVolume`). -/
def progRoutingVolume' (prog : PPMProg) (d : Nat) : Nat :=
  progRoutingVolume (progBoard prog) (progMerges prog) d

/-! ## §4. THE PLACEMENT THEOREM and the SCALE endpoint. -/

/-- **★ A ROUTED SHOR PROGRAM, PLACED ON THE HARDWARE ★.**  Simultaneously:
(a) every emitted gadget is verified lattice surgery; (b) the serial schedule is
conflict-free BY CONSTRUCTION (distinct clocks never overlap, so the derived
routing fabric is always available); (c) the device-qubit count decomposes
EXACTLY as data + factory + derived-routing.  Real placement, real (derived)
routing, real resource count — no free parameter. -/
theorem placeRoutedProgram (perPatch : Nat) (prog : PPMProg) :
    (∀ g ∈ progPlaced prog, ScheduleImplementsSpec (gadgetFor g.kind) = true)
    ∧ (∀ W i1 j1 i2 j2 c1 c2 : Nat, c1 ≠ c2 →
         conflict (serialSurgeryOp W i1 j1 c1) (serialSurgeryOp W i2 j2 c2) = false)
    ∧ progDeviceQubits perPatch prog
        = progDataQubits perPatch prog + progFactoryQubits prog
          + progRoutingQubits perPatch prog :=
  ⟨progPlaced_verified prog,
   fun W i1 j1 i2 j2 c1 c2 h => serial_no_conflict W i1 j1 i2 j2 c1 c2 h,
   rfl⟩

/-- **★ THE SAME FORMULAS REPRODUCE THE GE2021 20M-QUBIT TOTAL ★.**  Any routed
program at the RSA-2048 logical width (`6144` patches) and magic budget
(`rsa2048_magic_budget` Toffolis), priced at the d=27 per-patch size (`1568`),
has device-qubit count exactly `22 071 129` — the Gidney-Ekerå number — via the
SAME `progDeviceQubits` definition used on a small adder.  The two scale
hypotheses are the interface to the windowed-Shor sizing. -/
theorem progDeviceQubits_eq_rsa2048 (prog : PPMProg)
    (hp : progPatches prog = 6144) (hk : progCCZ prog = rsa2048_magic_budget) :
    progDeviceQubits perPatch27 prog = 22071129 := by
  unfold progDeviceQubits progDataQubits progRoutingQubits progFactoryQubits
  rw [hp, hk]
  native_decide

/-! ## §5. MILESTONE — a real Cuccaro adder, placed on a small board. -/

/-- The Cuccaro adder's seam merge-pairs (derived from its routed gadgets). -/
def adderMerges : List (Nat × Nat) := progMerges adderPPM

/-- **★ THE CUCCARO ADDER, PLACED AND COUNTED ★** — the real lowered adder's
device-qubit count decomposes exactly as data + factory + derived routing on the
fixed d=27 board.  (Per-gadget verified + serial-conflict-free come from
`placeRoutedProgram`.)  Real arithmetic → placed → derived-routed → counted. -/
theorem adderBoard_decomposes :
    progDeviceQubits perPatch27 adderPPM
      = progDataQubits perPatch27 adderPPM + progFactoryQubits adderPPM
        + progRoutingQubits perPatch27 adderPPM := rfl

-- The concrete small-board numbers for the real adder:
#eval progPatches adderPPM                    -- logical patches (board width)
#eval adderMerges.length                      -- routing seams
#eval progDeviceQubits perPatch27 adderPPM    -- device-qubit count on the d=27 board

/-! ## §6. TIGHTENING — the routing is GADGET-GROUNDED, per actual seam. -/

/-- On the fixed single-row board (`place i = ⟨i,0⟩`), the Manhattan separation
of two patches is just `|i − j|`. -/
theorem place_manhattan (i j : Nat) :
    manhattan (place i) (place j) = (max i j - min i j) := by
  unfold manhattan place; simp

/-- **★ THE PROGRAM'S ROUTING SPACE-TIME IS DERIVED PER GADGET-SEAM ★** — it is
exactly the sum, over every gadget's seam `(q,q')`, of the channel volume
`(|q−q'| + 2)·d` between the placed patches.  So the routing is grounded in the
ACTUAL gadget placements (a spread merge pays more, an adjacent one pays `3d`),
not a generic per-patch number. -/
theorem progRouting_per_seam (prog : PPMProg) (d : Nat) :
    progRoutingVolume' prog d
      = ((progMerges prog).map
          (fun p => (manhattan (place p.1) (place p.2) + 2) * d)).sum := by
  unfold progRoutingVolume' progRoutingVolume progBoard
  simp only [channelVolume_eq]

-- The real adder's routing space-time, derived from its actual gadget seams:
#eval progRoutingVolume' adderPPM 27

end FormalRV.QEC.Geometry
