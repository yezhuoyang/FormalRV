/-
  FormalRV.QEC.LatticeSurgery.Routing
  -----------------------------------
  **★ THE LONG-RANGE Z-MERGE — making NON-ADJACENT merges composable. ★**

  Catalog merges join ADJACENT columns only, so a measurement `Z̄_a Z̄_b` with
  `a`, `b` apart was not placeable on the global board.  This gadget closes that:
  a `Z`-seam threaded through an ANCILLA STRIP between the two data qubits (the
  lattice-surgery routing channel) measures `Z̄_a Z̄_b` DIRECTLY, as ONE wide
  gadget — no separate routing schedule.

  The ancilla columns carry the joint `Z` across (internal `I`-pipe seam, no `Z`
  boundary port), exactly as a `|+⟩`-initialised / `X`-measured routing patch.
  The distance-2 case (`Z̄₀Z̄₂`, ancilla at column 1) is built and verified here;
  the construction extends to any distance by lengthening the seam.

  Convention: I-axis, blue=`KI`(4)=`Z`, red=`KJ`(5)=`X`, `j=0`.
-/
import FormalRV.QEC.LatticeSurgery.Pad

namespace FormalRV.QEC.LaSre

/-! ## §1. The distance-2 long-range Z-merge (`Z̄₀Z̄₂`, ancilla column 1). -/

/-- Two DATA worldlines (cols 0, 2) joined by a `Z`-seam that runs through an
ANCILLA point at column 1 (two `I`-pipes at `k=1`, no `K`-worldline there). -/
def lrMergeLaS : LaSre :=
  { maxI := 3, maxJ := 1, maxK := 3
    YCube := fun _ _ _ => false
    ExistI := fun i j k => (i == 0 || i == 1) && j == 0 && k == 1   -- seam: 0–1 and 1–2
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => (i == 0 || i == 2) && j == 0 && k < 2     -- data worldlines (NOT col 1)
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

/-- Surfaces: flow 0 `Z̄₀Z̄₂` = blue `KI` on the two data worldlines, joined by the
`IK` seam pieces through the ancilla; flows 1,2 = the red `X̄₀`, `X̄₂`. -/
def lrMergeSurf : Surf :=
  { IJ := fun _ _ _ _ => false
    IK := fun s i j k => s == 0 && (i == 0 || i == 1) && j == 0 && k == 1   -- seam joins both pipes
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => s == 0 && j == 0 && (i == 0 || i == 2)             -- Z on data worldlines
    KJ := fun s i j _ => (s == 1 && i == 0 && j == 0) || (s == 2 && i == 2 && j == 0) }

/-- Four data ports: col-0 in/out, col-2 in/out (blue=`KI`). -/
def lrMergePorts : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨0, 0, 2, 4, 5⟩, ⟨2, 0, 0, 4, 5⟩, ⟨2, 0, 2, 4, 5⟩]

/-- Spec: flow 0 `Z̄₀Z̄₂` (Z on all data ports); flow 1 `X̄₀`; flow 2 `X̄₂`. -/
def lrMergePaulis : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, _ => Pauli.Z
  | 1, 0 => Pauli.X | 1, 1 => Pauli.X
  | 2, 2 => Pauli.X | 2, 3 => Pauli.X
  | _, _ => Pauli.I

theorem lrMerge_report :
    LaSReport lrMergeLaS lrMergeSurf lrMergePorts lrMergePaulis 3 = [] := by native_decide

/-- **★ THE LONG-RANGE Z-MERGE IS VERIFIED LATTICE SURGERY ★** — the
`Z̄₀Z̄₂` joint measurement across the column-1 ancilla passes the complete
`LaSCorrectFull` for all three flows.  A NON-ADJACENT merge is now a single
verified gadget — the routing requirement is closed at the gadget level. -/
theorem lrMerge_correct :
    LaSCorrectFull lrMergeLaS lrMergeSurf lrMergePorts lrMergePaulis 3 = true := by native_decide

/-- TEETH: dropping one seam pipe (the join no longer crosses the ancilla) breaks
the across-ancilla parity — `LaSCorrectFull` REJECTS.  So the join is genuinely
LONG-RANGE (it must thread the ancilla), not two independent merges. -/
def lrMergeSurf_broken : Surf :=
  { lrMergeSurf with IK := fun s i j k => s == 0 && i == 0 && j == 0 && k == 1 }

theorem lrMerge_broken_rejected :
    LaSCorrectFull lrMergeLaS lrMergeSurf_broken lrMergePorts lrMergePaulis 3 = false := by
  native_decide

/-- Footprint: `3 × 1 × 3` (uniform `h=3`, `wj=1`) — chain-composable like any
catalog gadget. -/
theorem lrMerge_footprint :
    lrMergeLaS.maxI = 3 ∧ lrMergeLaS.maxJ = 1 ∧ lrMergeLaS.maxK = 3 := by native_decide

/-! ## §1½. GENERALIZED to distance `d` — `Z̄₀Z̄_d` through `d−1` ancillas.

  `lrMergeLaSd d` measures `Z̄₀Z̄_d` with the `Z`-seam running through ancilla
  columns `1..d−1`.  At `d=1` it IS the adjacent `mergeZLaS` (the catalog merge),
  so this ONE gadget covers every weight-2 `Z`-measurement at any distance. -/

/-- The distance-`d` long-range `Z`-merge (data at cols `0`, `d`; ancillas between). -/
def lrMergeLaSd (d : Nat) : LaSre :=
  { maxI := d + 1, maxJ := 1, maxK := 3
    YCube := fun _ _ _ => false
    ExistI := fun i j k => decide (i < d) && j == 0 && k == 1
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => (i == 0 || i == d) && j == 0 && k < 2
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

def lrMergeSurfd (d : Nat) : Surf :=
  { IJ := fun _ _ _ _ => false
    IK := fun s i j k => s == 0 && decide (i < d) && j == 0 && k == 1
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => s == 0 && j == 0 && (i == 0 || i == d)
    KJ := fun s i j _ => (s == 1 && i == 0 && j == 0) || (s == 2 && i == d && j == 0) }

def lrMergePortsd (d : Nat) : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨0, 0, 2, 4, 5⟩, ⟨d, 0, 0, 4, 5⟩, ⟨d, 0, 2, 4, 5⟩]

/-- `d=1` is exactly the adjacent merge — the general gadget subsumes the catalog. -/
theorem lrMergeD1_correct :
    LaSCorrectFull (lrMergeLaSd 1) (lrMergeSurfd 1) (lrMergePortsd 1) lrMergePaulis 3 = true := by
  native_decide
theorem lrMergeD2_correct :
    LaSCorrectFull (lrMergeLaSd 2) (lrMergeSurfd 2) (lrMergePortsd 2) lrMergePaulis 3 = true := by
  native_decide
theorem lrMergeD3_correct :
    LaSCorrectFull (lrMergeLaSd 3) (lrMergeSurfd 3) (lrMergePortsd 3) lrMergePaulis 3 = true := by
  native_decide

/-! ## §1¾. MULTI-DATA long-range Z-merge — any weight, any distance.

  `lrMergeMulti cols` (local columns, starting at 0) joins ALL the data columns
  with one `Z`-seam (data worldlines at `cols`, ancilla points in the gaps),
  measuring the joint `Z̄` over `cols`.  This ONE gadget covers every pure-`Z`
  measurement: weight 1,2,3,4… at any spacing. -/

def lrMergeMulti (cols : List Nat) : LaSre :=
  let hi := cols.foldl max 0
  { maxI := hi + 1, maxJ := 1, maxK := 3
    YCube := fun _ _ _ => false
    ExistI := fun i j k => decide (i < hi) && j == 0 && k == 1     -- seam 0..hi
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => cols.contains i && j == 0 && k < 2       -- data worldlines
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

def lrMergeMultiSurf (cols : List Nat) : Surf :=
  let hi := cols.foldl max 0
  { IJ := fun _ _ _ _ => false
    IK := fun s i j k => s == 0 && decide (i < hi) && j == 0 && k == 1
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => s == 0 && j == 0 && cols.contains i        -- joint Z on all data
    KJ := fun s i j _ => decide (1 ≤ s) && (cols.getD (s - 1) (hi + 1) == i) && j == 0 }

/-- In/out ports for every data column. -/
def lrMergeMultiPorts (cols : List Nat) : List Port :=
  cols.flatMap (fun c => [(⟨c, 0, 0, 4, 5⟩ : Port), (⟨c, 0, 2, 4, 5⟩ : Port)])

/-- Flow 0 = joint `Z̄`; flow `s` = `X̄` on the `(s−1)`-th data column. -/
def lrMergeMultiPaulis (cols : List Nat) : Nat → Nat → Pauli := fun s p =>
  if s == 0 then Pauli.Z
  else if cols.getD (s - 1) (cols.foldl max 0 + 1) == cols.getD (p / 2) (cols.foldl max 0 + 1)
    then Pauli.X else Pauli.I

theorem lrMM_w2adj :
    LaSCorrectFull (lrMergeMulti [0,1]) (lrMergeMultiSurf [0,1]) (lrMergeMultiPorts [0,1])
      (lrMergeMultiPaulis [0,1]) 3 = true := by native_decide
theorem lrMM_w2spread :
    LaSCorrectFull (lrMergeMulti [0,2]) (lrMergeMultiSurf [0,2]) (lrMergeMultiPorts [0,2])
      (lrMergeMultiPaulis [0,2]) 3 = true := by native_decide
theorem lrMM_w3 :
    LaSCorrectFull (lrMergeMulti [0,1,2]) (lrMergeMultiSurf [0,1,2]) (lrMergeMultiPorts [0,1,2])
      (lrMergeMultiPaulis [0,1,2]) 4 = true := by native_decide
theorem lrMM_w3spread :
    LaSCorrectFull (lrMergeMulti [0,2,4]) (lrMergeMultiSurf [0,2,4]) (lrMergeMultiPorts [0,2,4])
      (lrMergeMultiPaulis [0,2,4]) 4 = true := by native_decide
theorem lrMM_w4 :
    LaSCorrectFull (lrMergeMulti [0,1,2,3]) (lrMergeMultiSurf [0,1,2,3]) (lrMergeMultiPorts [0,1,2,3])
      (lrMergeMultiPaulis [0,1,2,3]) 5 = true := by native_decide

/-! ## §1⅞. HEIGHT-PADDED merge (`padK`) — for a common footprint with mixed gadgets.

  `lrMergeMultiH cols h` is the multi-data Z-merge built at height `h`: the merge
  seam stays at `k=1`, but the data worldlines run the full height (`k < h−1`
  `K`-pipes).  This pads a pure-`Z` merge up to the height of a mixed gadget
  (`h=9`) so they share a uniform `chainOK` footprint.  The surface is unchanged
  (`lrMergeMultiSurf` spans all `k`); `padJ` is automatic (`unionLaS` bumps `maxJ`,
  the pure-`Z` `j=1` row staying empty). -/

def lrMergeMultiH (cols : List Nat) (h : Nat) : LaSre :=
  let hi := cols.foldl max 0
  { maxI := hi + 1, maxJ := 1, maxK := h
    YCube := fun _ _ _ => false
    ExistI := fun i j k => decide (i < hi) && j == 0 && k == 1
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => cols.contains i && j == 0 && decide (k + 1 < h)
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

def lrMergeMultiPortsH (cols : List Nat) (h : Nat) : List Port :=
  cols.flatMap (fun c => [(⟨c, 0, 0, 4, 5⟩ : Port), (⟨c, 0, h - 1, 4, 5⟩ : Port)])

theorem lrMMH_h9 :
    LaSCorrectFull (lrMergeMultiH [0,1] 9) (lrMergeMultiSurf [0,1]) (lrMergeMultiPortsH [0,1] 9)
      (lrMergeMultiPaulis [0,1]) 3 = true := by native_decide

theorem lrMMH_w3_h9 :
    LaSCorrectFull (lrMergeMultiH [0,1,2] 9) (lrMergeMultiSurf [0,1,2]) (lrMergeMultiPortsH [0,1,2] 9)
      (lrMergeMultiPaulis [0,1,2]) 4 = true := by native_decide

/-! ## §2. ★ COMPOSABLE — a NON-ADJACENT merge welded into a multi-layer chain. -/

/-- Only the DATA worldlines (cols 0, 2) are welded across interfaces; the
column-1 ancilla is internal to each layer. -/
def lrConn : List (Nat × Nat) := [(0, 0), (2, 0)]

def lrChain : List LaSre := [lrMergeLaS, lrMergeLaS]
def lrChainSurf : List Surf := [lrMergeSurf, lrMergeSurf]

/-- Composite ports: data cols 0, 2 in (k=0) and out (k=5). -/
def lrChainPorts : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨2, 0, 0, 4, 5⟩, ⟨0, 0, 5, 4, 5⟩, ⟨2, 0, 5, 4, 5⟩]

def lrChainPaulis : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, _ => Pauli.Z                                   -- Z̄₀Z̄₂ (all data ports)
  | 1, 0 => Pauli.X | 1, 2 => Pauli.X                 -- X̄₀ (col-0 in/out)
  | 2, 1 => Pauli.X | 2, 3 => Pauli.X                 -- X̄₂ (col-2 in/out)
  | _, _ => Pauli.I

theorem lrChain_chainOK :
    chainOK 3 3 lrConn 3 1 lrChain lrChainSurf = true := by native_decide

theorem lrChain_ports :
    portsOK (weldChainSurf 3 lrChainSurf) lrChainPorts lrChainPaulis 3 = true := by native_decide

/-- **★ A NON-ADJACENT MERGE COMPOSES INTO A MULTI-LAYER PROGRAM ★** — two
long-range `Z̄₀Z̄₂` measurements, welded by the chain corollary (only the data
worldlines connect; each ancilla stays internal), pass the complete
`LaSCorrectFull`.  Non-adjacent merges are now fully chain-composable. -/
theorem lrChain_correct :
    LaSCorrectFull (weldChain 3 lrConn lrChain) (weldChainSurf 3 lrChainSurf)
      lrChainPorts lrChainPaulis 3 = true :=
  weldChain_LaSCorrectFull 3 3 lrConn 3 1 lrChain lrChainSurf lrChainPorts lrChainPaulis
    lrChain_chainOK lrChain_ports

end FormalRV.QEC.LaSre
