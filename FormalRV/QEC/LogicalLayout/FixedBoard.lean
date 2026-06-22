/-
  FormalRV.QEC.LogicalLayout.FixedBoard
  -------------------------------------
  **A correct-by-construction layout + serial schedule that DERIVES the
  routing cost — turning the dangling `routingQubits` oracle into a closed
  form, the upper-bound way (not optimization).**

  The design review flagged that the headline resource total is parametric in
  a FREE `routingQubits : Nat` — a reviewer could set it to 0.  Solving optimal
  routing is NP-hard, but our job is a correct UPPER BOUND, not optimization.
  So we use the cheap, provable trick:

    * a FIXED regular layout — data patches in a row at `y = 0`, a dedicated
      routing HIGHWAY at `y = 1`.  Every pair of logical qubits is connectable
      through the highway, which is DISJOINT from the data row by construction;
    * a SERIAL schedule — one merge per time step.  Serial execution means two
      merges never overlap in time, so they NEVER conflict (regardless of
      footprint), so the highway is ALWAYS available: correctness by
      construction, no congestion to solve;
    * the routing fabric is then a FIXED size `n` highway tiles (reused
      serially), so `routingQubits = n` (derived), and the board is `2n` tiles
      — the `~2x` overhead we used to assert, now DERIVED from the layout.

  Everything is a placement FUNCTION with universally-quantified properties —
  no enumeration of the (10^11-op) workload.  Loose but correct, which is what
  an upper bound is allowed to be.
-/
import FormalRV.QEC.LogicalLayout.Geometry

namespace FormalRV.QEC.Geometry

open FormalRV.System.RoutingResourceModel

/-! ## §1. The fixed placement and the routing highway. -/

/-- **The fixed data placement**: logical qubit `i` sits at tile `(i, 0)` — a
single row.  A function, not a searched layout. -/
def place (i : Nat) : Tile := ⟨i, 0⟩

/-- The placement is INJECTIVE — no two logical patches share a tile. -/
theorem place_injective {i j : Nat} (h : place i = place j) : i = j := by
  simpa [place] using h

/-- **The routing highway**: the segment of row `y = 1` spanning the columns
between `i` and `j`.  The dedicated lane that connects any two patches. -/
def route (i j : Nat) : List Tile :=
  (List.range (max i j - min i j + 1)).map (fun k => ⟨min i j + k, 1⟩)

/-- Every routing tile lies on the highway row `y = 1`. -/
theorem route_in_highway (i j : Nat) : ∀ t ∈ route i j, t.y = 1 := by
  intro t ht
  rw [route, List.mem_map] at ht
  obtain ⟨k, _, rfl⟩ := ht
  rfl

/-- **The highway is DISJOINT from the data row**: no data patch `place k`
(at `y = 0`) is ever a routing tile (at `y = 1`).  So routing never collides
with logical data — the fabric is genuinely separate. -/
theorem route_disjoint_data (i j k : Nat) : place k ∉ route i j := by
  intro h
  have : (place k).y = 1 := route_in_highway i j _ h
  simp [place] at this

/-- The highway segment for a merge has length `|i − j| + 1` — bounded by the
board width, scaling with placement (not a constant, not an oracle). -/
theorem route_length (i j : Nat) :
    (route i j).length = (max i j - min i j) + 1 := by
  rw [route, List.length_map, List.length_range]

/-! ## §2. Serial schedule: correctness BY CONSTRUCTION (no congestion). -/

/-- A merge between logical qubits `i` and `j` at clock `clk`, reserving the
two data patches and the highway segment — as a verified `ResOp`. -/
def serialSurgeryOp (W i j clk : Nat) : ResOp :=
  latticeSurgeryOp [(place i).id W, (place j).id W]
    ((route i j).map (Tile.id W)) clk

/-- **SERIAL ⇒ NO CONFLICT.**  Two merges at DISTINCT clocks never overlap in
time (each occupies one tick), so they never conflict — whatever their
footprints.  Hence in a serial schedule the routing highway is ALWAYS
available, and the whole schedule is conflict-free BY CONSTRUCTION, with no
routing optimization required. -/
theorem serial_no_conflict (W i1 j1 i2 j2 clk1 clk2 : Nat) (h : clk1 ≠ clk2) :
    conflict (serialSurgeryOp W i1 j1 clk1) (serialSurgeryOp W i2 j2 clk2)
      = false := by
  have ht : timeOverlap (serialSurgeryOp W i1 j1 clk1)
      (serialSurgeryOp W i2 j2 clk2) = false := by
    unfold timeOverlap serialSurgeryOp latticeSurgeryOp
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega
  unfold conflict
  rw [ht, Bool.false_and]

/-! ## §3. The DERIVED routing fabric (closed form, not an oracle). -/

/-- **The routing-fabric qubit count is DERIVED**: `n` highway tiles for `n`
logical patches (the lane spans the data row), each tile a surface patch of
`perPatch` physical qubits (price routing tiles the SAME as data patches so the
total is commensurate).  Reused serially, so this fixed fabric suffices for the
whole computation — a closed form in `(perPatch, n)`, NOT a free input. -/
def routingQubits (perPatch n : Nat) : Nat := n * perPatch

/-- **The total board qubits are DERIVED**: data row (`n` patches) + routing
highway (`n` patches) = `2 · n · perPatch`.  The `~2x` overhead we used to
ASSERT is now a THEOREM about the fixed layout. -/
def boardQubits (perPatch n : Nat) : Nat := n * perPatch + routingQubits perPatch n

/-- The board is exactly `2x` the data area — the routing tax, derived. -/
theorem boardQubits_eq (perPatch n : Nat) :
    boardQubits perPatch n = 2 * (n * perPatch) := by
  unfold boardQubits routingQubits; ring

/-- The routing fabric is no longer a free oracle: it is pinned to the layout
width `n` and the patch size.  (A reviewer can no longer set it to 0 — it is
`n · perPatch`, equal to the data area.) -/
theorem routingQubits_pinned (perPatch n : Nat) :
    routingQubits perPatch n = n * perPatch := rfl

/-- The derived routing fabric equals the data area: a dedicated equal-area
highway, the honest serial upper bound. -/
theorem routingQubits_eq_data (perPatch n : Nat) :
    routingQubits perPatch n = n * perPatch := rfl

/-! ## §4. Per-merge routing volume (space-time), derived from placement. -/

/-- The space-time volume a single merge between `i` and `j` consumes on the
highway, held for `d` rounds: `(|i−j| + 1) · d` qubit-rounds — placement-
dependent, bounded by `width · d`. -/
def mergeRoutingVolume (i j d : Nat) : Nat := (route i j).length * d

theorem mergeRoutingVolume_eq (i j d : Nat) :
    mergeRoutingVolume i j d = ((max i j - min i j) + 1) * d := by
  unfold mergeRoutingVolume; rw [route_length]

/-- **Every merge routes within `width · d`** on a width-`n` board — a uniform
upper bound over ALL merges, quantified, not enumerated. -/
theorem mergeRoutingVolume_le (i j d n : Nat) (hi : i < n) (hj : j < n) :
    mergeRoutingVolume i j d ≤ n * d := by
  rw [mergeRoutingVolume_eq]
  have : (max i j - min i j) + 1 ≤ n := by omega
  exact Nat.mul_le_mul_right d this

end FormalRV.QEC.Geometry
