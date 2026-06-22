/-
  FormalRV.QEC.LogicalLayout.FrameTracker
  ---------------------------------------
  **★ THE STABILIZER-FRAME TRACKER — derive the global flow frame + per-layer
  `surfCombine` maps so multi-layer composition is CORRECT for evolving frames. ★**

  Through Z-merges: each qubit's `X̄_q` passes STRAIGHT (no growth), but Z-operators
  are FORCED to join at the seam — a single `Z̄_q` has no closing surface through a
  merge on `q`.  So the consistent global Z-frame is exactly **one joint-`Z` per
  CONNECTED COMPONENT of the merge graph** (qubits linked if ever merged).  Example:
  `Z̄₀Z̄₁ ; Z̄₁Z̄₂` links `{0,1,2}` into one component ⇒ the global Z-flow is
  `Z̄₀Z̄₁Z̄₂`; layer 1 expresses it as `(merge Z̄₀Z̄₁) ⊕ (idle Z̄₂)`, layer 2 as
  `(idle Z̄₀) ⊕ (merge Z̄₁Z̄₂)` — via `surfCombine`.

  DESIGN (modular, review-friendly, extensible): the tracker is an UNTRUSTED
  PRODUCER of the frame + maps; `chainOK` is the VERIFIED GATE.  A wrong map fails
  `chainOK` (the interface check bites), so correctness is guaranteed by the
  checker, not by trusting the tracker.  An advanced optimizing compiler can swap
  the scheduler/placement freely — as long as it re-emits frame+maps, `chainOK`
  re-certifies.  Each step below is a separate, independently-reviewable function.
-/
import FormalRV.QEC.LogicalLayout.Threader

namespace FormalRV.QEC.Threader

open FormalRV.QEC.Gidney21
open FormalRV.QEC.LaSre

/-! ## §1. The merge graph + connected components (union by min-rep fixpoint). -/

/-- The seam edges a gadget contributes: consecutive qubit pairs. -/
def gadgetEdges (g : PlacedGadget) : List (Nat × Nat) :=
  match g.qubits with
  | []      => []
  | q :: rest => (q :: rest).zip rest

/-- All merge edges of a scheduled program (every gadget in every layer). -/
def progEdges (layers : List Layer) : List (Nat × Nat) :=
  (layers.flatMap id).flatMap gadgetEdges

/-- One fixpoint pass: for each edge `(a,b)`, relabel both reps to their min. -/
def closeStep (edges : List (Nat × Nat)) (reps : List Nat) : List Nat :=
  edges.foldl (fun r p =>
    let ra := r.getD p.1 p.1
    let rb := r.getD p.2 p.2
    let m := min ra rb
    r.map (fun x => if x == ra || x == rb then m else x)) reps

/-- Component representatives: iterate `closeStep` `W` times (enough to propagate
the min across any path). -/
def compReps (W : Nat) (edges : List (Nat × Nat)) : List Nat :=
  (List.range W).foldl (fun r _ => closeStep edges r) (List.range W)

/-- The component rep of qubit `q`. -/
def compOf (reps : List Nat) (q : Nat) : Nat := reps.getD q q

/-! ## §2. The global flow frame: one joint-Z per component + one X per qubit. -/

/-- A global flow: the joint `Z̄` over a component, or a single qubit's `X̄`. -/
inductive Flow where
  | zComp (rep : Nat)
  | xQ (q : Nat)
deriving DecidableEq, Repr

/-- The frame = `zComp` per distinct component, then `xQ` per qubit. -/
def frameFlows (W : Nat) (edges : List (Nat × Nat)) : List Flow :=
  ((compReps W edges).dedup.map Flow.zComp) ++ ((List.range W).map Flow.xQ)

/-! ## §3. A layer's LOCAL generators (parts + descriptors), in flow-index order.

  A merge at columns `[c, c+w)` contributes generators `[jointZ [c..c+w), xQ c,
  xQ c+1, …]` (matching `mergeZSurf`'s flow order); an idle column `c` contributes
  `[zQ c, xQ c]` (matching `idSurf`). -/

/-- What a local generator measures. -/
inductive GenDesc where
  | jointZ (col w : Nat)   -- joint Z̄ over columns [col, col+w)
  | zQ (q : Nat)
  | xQ (q : Nat)
deriving DecidableEq, Repr

/-- The leftmost (global) column of a gadget. -/
def gadgetCol (g : PlacedGadget) : Nat := g.qubits.foldl min (g.qubits.headD 0)

/-- Columns a layer's gadgets occupy. -/
def usedCols (layer : Layer) : List Nat :=
  layer.flatMap (fun g => (List.range (gadgetW g)).map (gadgetCol g + ·))

/-- Build a layer's surface parts and generator descriptors TOGETHER (so flow
indices line up): gadgets first (at their global columns), then idle columns. -/
def layerData (W : Nat) (layer : Layer) : List SurfPart × List GenDesc :=
  -- gadgets
  let gAcc := layer.foldl (fun (acc : Nat × List SurfPart × List GenDesc) g =>
      let c := gadgetCol g
      let w := gadgetW g
      let nf := (gadgetFor g.kind).nStab
      let part : SurfPart := (c, acc.1, nf, w, (gadgetFor g.kind).S)
      let descs := GenDesc.jointZ c w :: (List.range w).map (fun i => GenDesc.xQ (c + i))
      (acc.1 + nf, acc.2.1 ++ [part], acc.2.2 ++ descs))
    (0, [], [])
  -- idle columns
  let idle := (List.range W).filter (fun c => !(usedCols layer).contains c)
  let iAcc := idle.foldl (fun (acc : Nat × List SurfPart × List GenDesc) c =>
      let part : SurfPart := (c, acc.1, 2, 1, idSurf)
      (acc.1 + 2, acc.2.1 ++ [part], acc.2.2 ++ [GenDesc.zQ c, GenDesc.xQ c]))
    gAcc
  (iAcc.2.1, iAcc.2.2)

/-! ## §4. The per-layer `surfCombine` map: global flow ↦ local generator indices. -/

/-- For global flow `s`, the local generators that XOR to it:
`xQ q` ↦ the unique `xQ q` generator; `zComp rep` ↦ every `jointZ`/`zQ` generator
whose column lies in component `rep`. -/
def layerMap (W : Nat) (edges : List (Nat × Nat)) (layer : Layer) : Nat → List Nat :=
  let reps := compReps W edges
  let frame := frameFlows W edges
  let descs := (layerData W layer).2
  fun s =>
    match frame.getD s (Flow.xQ 0) with
    | Flow.xQ q =>
        descs.zipIdx.filterMap (fun p =>
          match p.1 with | GenDesc.xQ q' => if q' == q then some p.2 else none | _ => none)
    | Flow.zComp rep =>
        descs.zipIdx.filterMap (fun p =>
          match p.1 with
          | GenDesc.jointZ col _ => if compOf reps col == rep then some p.2 else none
          | GenDesc.zQ q         => if compOf reps q == rep then some p.2 else none
          | _                    => none)

/-! ## §5. The global layer EMITTER (LaSre + surface), at GLOBAL columns. -/

/-- Idle worldlines on the columns NOT used by gadgets (the through-qubits). -/
def idleFillLaS (W : Nat) (layer : Layer) : LaSre :=
  let used := usedCols layer
  { maxI := W, maxJ := 1, maxK := 3
    YCube := fun _ _ _ => false
    ExistI := fun _ _ _ => false, ExistJ := fun _ _ _ => false
    ExistK := fun i j k => decide (i < W) && !used.contains i && j == 0 && k < 2
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

/-- The layer LaSre: each gadget at its GLOBAL column ∪ idle worldlines elsewhere. -/
def emitLayerLaS (W : Nat) (layer : Layer) : LaSre :=
  let active := layer.foldl (fun acc g => unionLaS acc (shiftI (gadgetCol g) (gadgetFor g.kind).L))
    (idleStrip 0)
  unionLaS active (idleFillLaS W layer)

/-- The layer surface: combine the local generators, then `surfCombine` them into
the global frame via the tracker's map. -/
def emitLayerSurf (W : Nat) (edges : List (Nat × Nat)) (layer : Layer) : Surf :=
  surfCombine (combineSurf (layerData W layer).1) (layerMap W edges layer)

/-! ## §6. Ports + paulis for the whole frame (first-layer bottom, last-layer top). -/

/-- Composite ports: every column's in-port (k=0) and out-port (k=`3·#layers−1`). -/
def emitPorts (W nLayers : Nat) : List Port :=
  (List.range W).map (fun c => (⟨c, 0, 0, 4, 5⟩ : Port)) ++
  (List.range W).map (fun c => (⟨c, 0, 3 * nLayers - 1, 4, 5⟩ : Port))

/-- Frame spec: a `zComp rep` flow is `Z̄` on every column of component `rep`; an
`xQ q` flow is `X̄` on column `q`. -/
def emitPaulis (W : Nat) (edges : List (Nat × Nat)) : Nat → Nat → Pauli :=
  let reps := compReps W edges
  let frame := frameFlows W edges
  fun s p =>
    let col := p % W
    match frame.getD s (Flow.xQ 0) with
    | Flow.zComp rep => if compOf reps col == rep then Pauli.Z else Pauli.I
    | Flow.xQ q      => if col == q then Pauli.X else Pauli.I

/-! ## §7. ★ CERTIFIED — an EVOLVING-FRAME program: `Z̄₀Z̄₁ ; Z̄₁Z̄₂`. -/

/-- The overlapping schedule: merge `(0,1)`, then merge `(1,2)` — qubit 1 in both,
so the frame EVOLVES (the hard case last turn could not do). -/
def evoSchedule : List Layer := [[⟨GadgetKind.zMerge, [0, 1]⟩], [⟨GadgetKind.zMerge, [1, 2]⟩]]

def evoEdges : List (Nat × Nat) := progEdges evoSchedule

-- Sanity: one component {0,1,2}; frame = {Z̄₀Z̄₁Z̄₂, X̄₀, X̄₁, X̄₂}; n = 4.
#eval compReps 3 evoEdges                 -- [0,0,0]
#eval (frameFlows 3 evoEdges).length       -- 4
#eval (layerMap 3 evoEdges evoSchedule[0]!) 0   -- Z-flow map, layer 1: [merge-Z, idle-Z]
#eval (layerMap 3 evoEdges evoSchedule[1]!) 0   -- Z-flow map, layer 2

def evoGadgets : List LaSre := evoSchedule.map (emitLayerLaS 3)
def evoSurfs : List Surf := evoSchedule.map (emitLayerSurf 3 evoEdges)

theorem evo_chainOK :
    chainOK 3 4 (threadConn 3) 3 1 evoGadgets evoSurfs = true := by native_decide

theorem evo_ports :
    portsOK (weldChainSurf 3 evoSurfs) (emitPorts 3 2) (emitPaulis 3 evoEdges) 4 = true := by
  native_decide

/-- **★ THE EVOLVING-FRAME MULTI-LAYER PROGRAM IS CERTIFIED ★** — `Z̄₀Z̄₁ ; Z̄₁Z̄₂`,
with the frame TRACKER deriving the component joint-`Z̄₀Z̄₁Z̄₂` and the per-layer
`surfCombine` maps, welds into one diagram passing the complete `LaSCorrectFull`.
The case the hand emitter could NOT do last turn — multi-layer composition with an
evolving stabilizer frame — is now GUARANTEED correct by the tracker + `chainOK`. -/
theorem evo_correct :
    LaSCorrectFull (weldChain 3 (threadConn 3) evoGadgets) (weldChainSurf 3 evoSurfs)
      (emitPorts 3 2) (emitPaulis 3 evoEdges) 4 = true :=
  weldChain_LaSCorrectFull 3 4 (threadConn 3) 3 1 evoGadgets evoSurfs
    (emitPorts 3 2) (emitPaulis 3 evoEdges) evo_chainOK evo_ports

end FormalRV.QEC.Threader
