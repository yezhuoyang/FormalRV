/-
  FormalRV.QEC.LogicalLayout.Geometry
  -----------------------------------
  **The 2D surface placement + routing layer — making "correlated surface and
  routing" (Paler) a DERIVED, verified resource.**

  Until now a lattice-surgery merge between two logical patches was priced
  with a fixed, placement-independent ancilla (the routing 2x was ASSERTED).
  Paler's point: the routing cost and the schedule are CORRELATED with the
  surface placement — you cannot price them without a geometry.

  This file adds that geometry and wires it to the ALREADY-VERIFIED congestion
  engine (`System.RoutingResourceModel`, which is layout-agnostic):

    * `Tile`/`Board` — a 2D placement of logical patches on a grid;
    * `manhattan` separation `L` and the `routePath` ancilla channel of length
      `~L` connecting two patches;
    * `channelVolume = path.length * d` — the `(L+c)*d` routing space-time the
      fixed model omitted;
    * `placedSurgeryOp` — a placed merge as a `ResOp`, so the verified
      `litinski_simultaneous_conflict` gives, for FREE, the theorem that **two
      placed merges conflict (must serialize) iff their Manhattan routing paths
      share a tile** — exactly the surface/routing coupling.
-/
import FormalRV.System.DeviceLane.RoutingResourceModel
import Mathlib.Tactic

namespace FormalRV.QEC.Geometry

open FormalRV.System.RoutingResourceModel

/-! ## §1. 2D tiles, boards, and separation. -/

/-- A tile on the surface grid: a logical-patch (or routing) site. -/
structure Tile where
  x : Nat
  y : Nat
deriving DecidableEq, Repr

/-- Flatten a tile to an abstract resource id on a width-`W` grid. -/
def Tile.id (W : Nat) (t : Tile) : Resource := t.y * W + t.x

/-- Manhattan (L1) separation of two tiles — the lattice-surgery routing
distance `L`. -/
def manhattan (a b : Tile) : Nat :=
  (max a.x b.x - min a.x b.x) + (max a.y b.y - min a.y b.y)

/-- A board: a grid width plus a placement of each logical-wire index onto a
tile. -/
structure Board where
  width : Nat
  place : Nat → Tile

/-- A placement is INJECTIVE on the first `n` indices — no two logical patches
share a tile. -/
def Board.injOn (B : Board) (n : Nat) : Prop :=
  ∀ i j, i < n → j < n → B.place i = B.place j → i = j

/-! ## §2. Routing channels (the `(L+c)*d` volume the fixed model omitted). -/

/-- A horizontal run of `len` tiles at row `y` starting at column `lo`. -/
def hRun (y lo len : Nat) : List Tile := (List.range len).map (fun k => ⟨lo + k, y⟩)

/-- A vertical run of `len` tiles at column `x` starting at row `lo`. -/
def vRun (x lo len : Nat) : List Tile := (List.range len).map (fun k => ⟨x, lo + k⟩)

/-- **The L-shaped Manhattan routing channel** from `a` to `b`: a horizontal
run then a vertical run.  The reserved ancilla path connecting the patches. -/
def routePath (a b : Tile) : List Tile :=
  hRun a.y (min a.x b.x) (max a.x b.x - min a.x b.x + 1)
    ++ vRun b.x (min a.y b.y) (max a.y b.y - min a.y b.y + 1)

/-- **The routing channel has length `L + 2`** (`L = manhattan`, the `+2`
counting both segment endpoints) — so routing scales with PLACEMENT, not a
constant. -/
theorem routePath_length (a b : Tile) :
    (routePath a b).length = manhattan a b + 2 := by
  unfold routePath hRun vRun manhattan
  rw [List.length_append, List.length_map, List.length_map,
      List.length_range, List.length_range]
  omega

/-- **The routing SPACE-TIME volume** of a merge between `a` and `b` held for
`d` rounds: `(L+2) * d` qubit-rounds — the `(L+c)*d` channel cost. -/
def channelVolume (a b : Tile) (d : Nat) : Nat := (routePath a b).length * d

/-- The channel volume is `(L+2)*d` — explicitly placement-dependent. -/
theorem channelVolume_eq (a b : Tile) (d : Nat) :
    channelVolume a b d = (manhattan a b + 2) * d := by
  unfold channelVolume; rw [routePath_length]

/-! ## §3. THE BRIDGE: placed merges drive the verified congestion engine. -/

/-- A merge between patches at tiles `a`, `b` (clock `clk`), as a reserved
operation in the verified resource model — operands are the two patch tiles,
the routing region is the Manhattan channel. -/
def placedSurgeryOp (W : Nat) (a b : Tile) (clk : Nat) : ResOp :=
  latticeSurgeryOp [a.id W, b.id W] ((routePath a b).map (Tile.id W)) clk

/-- **CORRELATED SURFACE AND ROUTING, as a theorem.**  Two placed lattice-
surgery merges CONFLICT (cannot run concurrently — they must serialize) IFF
their patch-tiles or Manhattan routing channels SHARE A TILE.  Routing
contention is thus DERIVED from the placement, via the already-verified
`litinski_simultaneous_conflict`. -/
theorem placed_conflict_iff_paths_overlap
    (W : Nat) (a b c e : Tile) (clk : Nat) :
    conflict (placedSurgeryOp W a b clk) (placedSurgeryOp W c e clk)
      = overlap ([a.id W, b.id W] ++ (routePath a b).map (Tile.id W))
                ([c.id W, e.id W] ++ (routePath c e).map (Tile.id W)) :=
  litinski_simultaneous_conflict _ _ _ _ clk

/-- Two placed merges with DISJOINT footprints (non-overlapping patches and
routing channels) do NOT conflict — they run in parallel.  The space side of
the coupling: enough routing separation buys parallelism. -/
theorem placed_parallel_of_disjoint
    (W : Nat) (a b c e : Tile) (clk : Nat)
    (h : overlap ([a.id W, b.id W] ++ (routePath a b).map (Tile.id W))
                 ([c.id W, e.id W] ++ (routePath c e).map (Tile.id W)) = false) :
    conflict (placedSurgeryOp W a b clk) (placedSurgeryOp W c e clk) = false := by
  rw [placed_conflict_iff_paths_overlap]; exact h

/-! ## §4. DERIVED routing cost — placement-dependent, not asserted. -/

/-- **The total routing space-time of a program's merges UNDER A PLACEMENT** —
each merge's channel volume `(L+2)*d`, summed.  Unlike the old fixed
per-merge footprint, this is DERIVED from the board: spread the patches and
it grows, pack them and it shrinks. -/
def progRoutingVolume (B : Board) (merges : List (Nat × Nat)) (d : Nat) : Nat :=
  (merges.map (fun p => channelVolume (B.place p.1) (B.place p.2) d)).sum

/-- A placement is COMPACT for a workload when every merge joins ADJACENT
patches (`manhattan = 1`) — GE2021's deliberately slack-packed board. -/
def CompactFor (B : Board) (merges : List (Nat × Nat)) : Prop :=
  ∀ p ∈ merges, manhattan (B.place p.1) (B.place p.2) = 1

/-- **COMPACT placement ⇒ routing is a DERIVED CONSTANT** `3*d` per merge
(`(1+2)*d`), so total routing `= #merges * 3d`.  This recovers GE2021's
"routing negligible / O(1) per op" as a THEOREM about the compact placement —
NOT an assertion.  Spread the board and `manhattan` (hence the volume) grows,
which is exactly the surface/routing coupling Paler flags. -/
theorem compact_routing_volume (B : Board) (merges : List (Nat × Nat)) (d : Nat)
    (h : CompactFor B merges) :
    progRoutingVolume B merges d = merges.length * (3 * d) := by
  unfold progRoutingVolume
  induction merges with
  | nil => simp
  | cons p rest ih =>
      have hp : manhattan (B.place p.1) (B.place p.2) = 1 :=
        h p (List.mem_cons_self ..)
      have hrest : CompactFor B rest := fun q hq => h q (List.mem_cons_of_mem _ hq)
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [channelVolume_eq, hp, ih hrest]
      ring

/-- **Routing volume is MONOTONE in separation**: a merge between patches at
Manhattan distance `L >= 1` costs `(L+2)*d >= 3*d`, with EQUALITY only for the
compact `L = 1` placement.  So a spread placement pays strictly more routing:
the floorplan and the routing cost are one coupled quantity (Paler). -/
theorem channelVolume_ge_compact (a b : Tile) (d : Nat) (h : 1 ≤ manhattan a b) :
    3 * d ≤ channelVolume a b d := by
  rw [channelVolume_eq]; gcongr; omega

end FormalRV.QEC.Geometry
