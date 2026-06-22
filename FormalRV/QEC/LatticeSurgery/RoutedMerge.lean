/-
  FormalRV.QEC.LatticeSurgery.RoutedMerge
  ---------------------------------------
  **★ THE ROUTING FIX — realize a merge between NON-ADJACENT qubits as a verified
  long-range (ancilla-highway) merge, instead of the broken contiguous placement. ★**

  THE BUG (found while compiling `modexpPPM`): the FrameTracker places a merge as
  a fixed-width contiguous block at `min(qubits)`, so a real merge between, e.g.,
  logical qubits `{4,7}` is laid down as two patches at columns `4,5` — qubit `7`
  is at column `7`, not `5`.  Distinct merges then collide on a column, breaking
  the diagram.  The blocks were being placed in the wrong spots on the baseplate.

  THE FIX: a merge over columns `cols` (possibly NON-adjacent) is the long-range
  merge `lrMergeMulti cols` — data worldlines only at `cols`, the in-between
  columns are ANCILLA points carrying the `Z`-seam (the "highway"), measuring the
  joint `Z̄` over exactly `cols`.  This `Routing.lrMergeMulti` is already verified
  for any spacing; here we package it as the routing realization, prove the
  highway PRESERVES the observable (∀ cols, flow 0 is the joint `Z̄`), and certify
  the exact distances `modexpPPM` needs (`{4,7}`→dist-3, `{3,8}`→dist-5).
-/
import FormalRV.QEC.LatticeSurgery.Routing

namespace FormalRV.QEC.LaSre

/-! ## §1. The routed realization of a Z-merge over arbitrary columns. -/

/-- A `Z̄`-merge over columns `cols` (possibly non-adjacent), routed as the
long-range ancilla-highway merge. -/
def routedZMerge (cols : List Nat) : LaSre := lrMergeMulti cols
def routedZMergeSurf (cols : List Nat) : Surf := lrMergeMultiSurf cols
def routedZMergePorts (cols : List Nat) : List Port := lrMergeMultiPorts cols
def routedZMergePaulis (cols : List Nat) : Nat → Nat → Pauli := lrMergeMultiPaulis cols

/-! ## §2. ROUTING PRESERVES THE OBSERVABLE — ∀ cols, flow 0 is the joint `Z̄`. -/

/-- **★ THE HIGHWAY DOESN'T CHANGE WHAT IS MEASURED, FOR ANY ROUTING ★** — no
matter how far apart the data columns are (how long the ancilla highway is), the
measured observable (flow 0) is the joint `Z̄` on every data port.  So routing a
merge over a gap is observationally identical to an adjacent merge. -/
theorem routed_flow0_is_jointZ (cols : List Nat) (p : Nat) :
    routedZMergePaulis cols 0 p = Pauli.Z := by
  simp [routedZMergePaulis, lrMergeMultiPaulis]

/-- The ports sit on EXACTLY the data columns — the ancilla highway carries no
data port (it is internal). -/
theorem routed_ports_only_data (cols : List Nat) :
    routedZMergePorts cols = cols.flatMap (fun c => [(⟨c,0,0,4,5⟩ : Port), (⟨c,0,2,4,5⟩ : Port)]) := by
  rfl

/-! ## §3. CERTIFIED at the exact distances `modexpPPM` needs (the failing L1 case). -/

/-- **★ `modexpPPM`'s `zMerge {4,7}` (distance 3) ROUTES CORRECTLY ★** — as local
columns `[0,3]`, the routed long-range merge passes the COMPLETE `LaSCorrectFull`
(where the contiguous placement collided). -/
theorem routed_dist3_correct :
    LaSCorrectFull (routedZMerge [0,3]) (routedZMergeSurf [0,3]) (routedZMergePorts [0,3])
      (routedZMergePaulis [0,3]) 3 = true := by native_decide

/-- ...and `mxzMerge {3,8}` (distance 5) likewise. -/
theorem routed_dist5_correct :
    LaSCorrectFull (routedZMerge [0,5]) (routedZMergeSurf [0,5]) (routedZMergePorts [0,5])
      (routedZMergePaulis [0,5]) 3 = true := by native_decide

/-- ...and a weight-3 spread (the `mxzz3`/`mZ3` joins route the same way). -/
theorem routed_w3spread_correct :
    LaSCorrectFull (routedZMerge [0,2,7]) (routedZMergeSurf [0,2,7]) (routedZMergePorts [0,2,7])
      (routedZMergePaulis [0,2,7]) 4 = true := by native_decide

/-- The routed dist-3 merge measures exactly `Z̄` on its two data columns (0 and 3). -/
theorem routed_dist3_measures_Z03 :
    routedZMergePaulis [0,3] 0 0 = Pauli.Z ∧ routedZMergePaulis [0,3] 0 2 = Pauli.Z :=
  ⟨routed_flow0_is_jointZ [0,3] 0, routed_flow0_is_jointZ [0,3] 2⟩

/-! ## §4. THE CONGESTION CRITERION — when can two highways run in parallel?

  A routed merge occupies the whole COLUMN SPAN `[min cols, max cols]` (its
  highway).  Two merges may share a time-layer only if their spans are DISJOINT;
  if the highways overlap, the merges must be SERIALIZED into different layers.
  This is exactly why the `modexpPPM` layer L1 broke: its two merges `{4,7}` and
  `{3,8}` have OVERLAPPING spans, so they cannot both be routed in one layer —
  the scheduler packed them together (qubit-disjoint) without checking highway
  congestion. -/

/-- The column span of a routed merge = `[min cols, max cols]` (the highway). -/
def colSpan (cols : List Nat) : Nat × Nat := (cols.foldl Nat.min (cols.headD 0), cols.foldl Nat.max 0)

/-- Two highways are parallel-compatible iff their spans don't overlap. -/
def spansDisjoint (a b : List Nat) : Bool :=
  decide ((colSpan a).2 < (colSpan b).1) || decide ((colSpan b).2 < (colSpan a).1)

/-- **★ WHY L1 FAILED — ITS TWO HIGHWAYS COLLIDE ★** — `{4,7}` (span 4–7) and
`{3,8}` (span 3–8) overlap, so they cannot share a time-layer; the scheduler
must serialize them.  (Qubit-disjoint ≠ highway-disjoint.) -/
theorem L1_highways_collide : spansDisjoint [4,7] [3,8] = false := by decide

/-- ...whereas two merges on disjoint spans `{0,3}` and `{5,8}` ARE parallel — the
correct criterion for packing routed merges into one layer. -/
theorem parallel_routing_ok : spansDisjoint [0,3] [5,8] = true := by decide

end FormalRV.QEC.LaSre
