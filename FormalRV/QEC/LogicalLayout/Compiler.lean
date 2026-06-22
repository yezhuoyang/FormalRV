/-
  FormalRV.QEC.LogicalLayout.Compiler
  -----------------------------------
  **★ THE INTEGRATED COMPILER — schedule → route → frame → emit → chain-certify,
  with LONG-RANGE merges at any distance. ★**

  Brings together every piece: the ASAP scheduler (parallel layers), the
  long-range merge (`lrMergeLaSd d`, non-adjacent merges), and the stabilizer-
  frame tracker (component joint-Z + `surfCombine` maps).  A weight-2 measurement
  `Z̄_a Z̄_b` is emitted UNIFORMLY as `lrMergeLaSd (b−a)` — `d=1` is the adjacent
  merge, `d>1` routes through the free channel columns between data qubits
  (so the channel never collides with data).  The frame tracker runs over the
  DATA columns; `chainOK` is the verified gate.

  This file drives a block with BOTH a long-range merge AND frame evolution
  through the whole pipeline, certified end to end (`block_correct`).
-/
import FormalRV.QEC.LogicalLayout.FrameTracker
import FormalRV.QEC.LatticeSurgery.Routing

namespace FormalRV.QEC.Threader

open FormalRV.QEC.Gidney21
open FormalRV.QEC.LaSre

/-! ## §1. ROUTING a gadget: pure-`Z̄` measurement of ANY weight ↦ `lrMergeMulti`.

  A pure-`Z` joint measurement on qubits `[q₀ < q₁ < …]` (any weight, any spacing)
  is emitted as `lrMergeMulti` over the LOCAL columns `[0, q₁−q₀, …]`, placed at
  `q₀`.  Weight 1 = a worldline; weight 2 adjacent = `mergeZLaS`; weight `k`
  spread = a `Z`-seam through the free channels — all ONE gadget. -/

def routeCol (g : PlacedGadget) : Nat := g.qubits.foldl min (g.qubits.headD 0)
def routeHi (g : PlacedGadget) : Nat := g.qubits.foldl max (g.qubits.headD 0)
def routeSpan (g : PlacedGadget) : Nat := routeHi g - routeCol g + 1
def routeLocalCols (g : PlacedGadget) : List Nat := g.qubits.map (· - routeCol g)
def routeLaS (g : PlacedGadget) : LaSre := lrMergeMulti (routeLocalCols g)
def routeSurf (g : PlacedGadget) : Surf := lrMergeMultiSurf (routeLocalCols g)
def routeNFlows (g : PlacedGadget) : Nat := g.qubits.length + 1

/-! ## §2. The DATA-column frame (channels excluded). -/

/-- The frame over DATA columns only: one `zComp` per distinct data-component,
one `xQ` per data qubit (channel columns carry no logical flow). -/
def frameFlows' (dataCols : List Nat) (reps : List Nat) : List Flow :=
  ((dataCols.map (compOf reps)).dedup.map Flow.zComp) ++ (dataCols.map Flow.xQ)

/-! ## §3. A layer's surface parts + per-generator FLOW TAGS (route-aware). -/

/-- For a layer: the `combineSurf` parts and, in flow-index order, the global
`Flow` each local generator contributes to.  A merge `[a,b]` ↦
`[zComp(comp a), xQ a, xQ b]`; an idle data column `c` ↦ `[zComp(comp c), xQ c]`. -/
def layerData' (reps : List Nat) (dataCols : List Nat) (layer : Layer) :
    List SurfPart × List Flow :=
  let gAcc := layer.foldl (fun (acc : Nat × List SurfPart × List Flow) g =>
      let part : SurfPart := (routeCol g, acc.1, routeNFlows g, routeSpan g, routeSurf g)
      let tags := Flow.zComp (compOf reps (routeCol g)) :: g.qubits.map Flow.xQ
      (acc.1 + routeNFlows g, acc.2.1 ++ [part], acc.2.2 ++ tags))
    (0, [], [])
  let used := layer.flatMap (fun g => (List.range (routeSpan g)).map (routeCol g + ·))
  let idle := dataCols.filter (fun c => !used.contains c)
  let iAcc := idle.foldl (fun (acc : Nat × List SurfPart × List Flow) c =>
      let part : SurfPart := (c, acc.1, 2, 1, idSurf)
      (acc.1 + 2, acc.2.1 ++ [part], acc.2.2 ++ [Flow.zComp (compOf reps c), Flow.xQ c]))
    gAcc
  (iAcc.2.1, iAcc.2.2)

/-! ## §4. The layer EMITTER (LaSre + surface), at GLOBAL data columns. -/

def emitLaS' (W : Nat) (dataCols : List Nat) (layer : Layer) : LaSre :=
  let active := layer.foldl (fun acc g => unionLaS acc (shiftI (routeCol g) (routeLaS g)))
    (idleStrip 0)
  let used := layer.flatMap (fun g => (List.range (routeSpan g)).map (routeCol g + ·))
  let idle := dataCols.filter (fun c => !used.contains c)
  unionLaS active
    { maxI := W, maxJ := 1, maxK := 3
      YCube := fun _ _ _ => false
      ExistI := fun _ _ _ => false, ExistJ := fun _ _ _ => false
      ExistK := fun i j k => idle.contains i && j == 0 && k < 2
      ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

def emitSurf' (W : Nat) (edges : List (Nat × Nat)) (dataCols : List Nat) (layer : Layer) : Surf :=
  let reps := compReps W edges
  let frame := frameFlows' dataCols reps
  let td := layerData' reps dataCols layer
  surfCombine (combineSurf td.1) (fun s =>
    td.2.zipIdx.filterMap (fun p => if p.1 == frame.getD s (Flow.xQ 0) then some p.2 else none))

/-! ## §5. Ports + paulis over the data columns. -/

def emitPorts' (dataCols : List Nat) (nLayers : Nat) : List Port :=
  dataCols.map (fun c => (⟨c, 0, 0, 4, 5⟩ : Port)) ++
  dataCols.map (fun c => (⟨c, 0, 3 * nLayers - 1, 4, 5⟩ : Port))

def emitPaulis' (W : Nat) (edges : List (Nat × Nat)) (dataCols : List Nat) : Nat → Nat → Pauli :=
  let reps := compReps W edges
  let frame := frameFlows' dataCols reps
  fun s p =>
    let col := dataCols.getD (p % dataCols.length) 0
    match frame.getD s (Flow.xQ 0) with
    | Flow.zComp rep => if compOf reps col == rep then Pauli.Z else Pauli.I
    | Flow.xQ q      => if col == q then Pauli.X else Pauli.I

/-! ## §6. ★ A REAL BLOCK — long-range + frame evolution + idle, end to end. -/

/-- Data qubits at spaced columns `0, 2, 4` (channels at `1, 3`).  Measure
`Z̄₀Z̄₂` (long-range through channel 1), then `Z̄₂Z̄₄` (through channel 3) — the
two overlap at column 2, so the frame EVOLVES; both are LONG-RANGE. -/
def blockSchedule : List Layer :=
  [[⟨GadgetKind.zMerge, [0, 2]⟩], [⟨GadgetKind.zMerge, [2, 4]⟩]]
def blockData : List Nat := [0, 2, 4]
def blockEdges : List (Nat × Nat) := progEdges blockSchedule

-- Sanity: one data-component {0,2,4}; frame = {Z̄₀₂₄, X̄₀, X̄₂, X̄₄}; n = 4.
#eval (frameFlows' blockData (compReps 5 blockEdges)).length    -- 4

def blockGadgets : List LaSre := blockSchedule.map (emitLaS' 5 blockData)
def blockSurfs : List Surf := blockSchedule.map (emitSurf' 5 blockEdges blockData)
def blockConn : List (Nat × Nat) := blockData.map (fun c => (c, 0))

theorem block_chainOK :
    chainOK 3 4 blockConn 5 1 blockGadgets blockSurfs = true := by native_decide

theorem block_ports :
    portsOK (weldChainSurf 3 blockSurfs) (emitPorts' blockData 2) (emitPaulis' 5 blockEdges blockData) 4
      = true := by native_decide

/-- **★ A REAL BLOCK COMPILED END TO END ★** — `Z̄₀Z̄₂ ; Z̄₂Z̄₄` (two LONG-RANGE
merges, OVERLAPPING so the stabilizer frame evolves, with an idle data qubit each
layer) is scheduled, routed, frame-tracked, emitted, and welded — passing the
complete `LaSCorrectFull`.  Long-range routing + frame evolution + parall idle,
all integrated, all verified through the chain corollary. -/
theorem block_correct :
    LaSCorrectFull (weldChain 3 blockConn blockGadgets) (weldChainSurf 3 blockSurfs)
      (emitPorts' blockData 2) (emitPaulis' 5 blockEdges blockData) 4 = true :=
  weldChain_LaSCorrectFull 3 4 blockConn 5 1 blockGadgets blockSurfs
    (emitPorts' blockData 2) (emitPaulis' 5 blockEdges blockData) block_chainOK block_ports

/-! ## §7. ★ MIXED WEIGHTS — a weight-3 then a weight-2 measurement. -/

/-- `Z̄₀Z̄₂Z̄₄` (weight-3 long-range) then `Z̄₂Z̄₄` (weight-2), qubit 0 idle in
layer 2 — different weights in one program. -/
def wblockSchedule : List Layer :=
  [[⟨GadgetKind.zMerge, [0, 2, 4]⟩], [⟨GadgetKind.zMerge, [2, 4]⟩]]
def wblockData : List Nat := [0, 2, 4]
def wblockEdges : List (Nat × Nat) := progEdges wblockSchedule
def wblockGadgets : List LaSre := wblockSchedule.map (emitLaS' 5 wblockData)
def wblockSurfs : List Surf := wblockSchedule.map (emitSurf' 5 wblockEdges wblockData)
def wblockConn : List (Nat × Nat) := wblockData.map (fun c => (c, 0))

theorem wblock_chainOK :
    chainOK 3 4 wblockConn 5 1 wblockGadgets wblockSurfs = true := by native_decide

theorem wblock_ports :
    portsOK (weldChainSurf 3 wblockSurfs) (emitPorts' wblockData 2)
      (emitPaulis' 5 wblockEdges wblockData) 4 = true := by native_decide

/-- **★ MIXED-WEIGHT PROGRAM COMPILED END TO END ★** — a weight-3 long-range
measurement and a weight-2, both routed by `lrMergeMulti`, frame-tracked over the
shared component, and welded — `LaSCorrectFull`.  `route*` now handles any pure-`Z`
weight. -/
theorem wblock_correct :
    LaSCorrectFull (weldChain 3 wblockConn wblockGadgets) (weldChainSurf 3 wblockSurfs)
      (emitPorts' wblockData 2) (emitPaulis' 5 wblockEdges wblockData) 4 = true :=
  weldChain_LaSCorrectFull 3 4 wblockConn 5 1 wblockGadgets wblockSurfs
    (emitPorts' wblockData 2) (emitPaulis' 5 wblockEdges wblockData) wblock_chainOK wblock_ports

end FormalRV.QEC.Threader
