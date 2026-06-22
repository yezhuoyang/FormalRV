/-
  FormalRV.QEC.Gidney21.Accounting
  ────────────────────────────────
  **THE HONEST PHYSICAL-QUBIT BREAKDOWN — data vs syndrome vs surgery.**

  At the QEC level the virtual qubits split into THREE roles, counted
  separately (the System pass later decides which can share hardware):

    1. DATA qubits — FIXED.  The logical surface patches; `width · 729` for
       distance-27 rotated `[[729,1,27]]` patches.  Persistent: the data of
       a logical qubit lives at the same index for the whole computation.

    2. SYNDROME qubits — SSA, system-provided.  Each stabilizer measurement
       in each round gets a FRESH qubit (NO reuse — we cannot yet assume the
       reset time suffices, so we do not collapse rounds).  So measuring `d`
       rounds of a patch's `m` checks needs `d · m` syndrome qubits, and over
       the whole program the syndrome-qubit count EQUALS the syndrome-
       measurement count (one fresh qubit each).

    3. LATTICE-SURGERY (merge/split) ancilla — **NOT FREE.**  Every joint
       logical Pauli measurement (`countMeas` of the PPM program) is realized
       by a merge, and EVERY merge allocates a FRESH, well-prepared ancilla
       PATCH between the data patches — itself syndrome-extracted for `d`
       rounds (SSA).  Code switching / lattice surgery costs real qubits:
       per merge, `729` ancilla-data + `27 · 728` ancilla-syndrome = `20385`
       physical qubits, allocated fresh.  This is counted and added to the
       physical total, never assumed free.

  Counts are read off the real objects (`measCountC` walks, `countMeas`
  walks), proven equal to closed forms — no gadget × asserted multiplier.
-/
import FormalRV.QEC.Gidney21.Resource

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC FormalRV.QEC.Circuit FormalRV.QEC.LogicalLayout
open FormalRV.Resource
open FormalRV.Framework (Gate)

/-! ## §1. DATA qubits (fixed). -/

/-- **DATA qubits of a gadget**: `width · 729` — one persistent
distance-27 patch's data per logical qubit. -/
def gadgetDataQubits (g : Gate) : Nat := Resource.width g * 729

/-- The data qubit count is the board's data — `width · (patch data)`. -/
theorem gadgetDataQubits_eq (g : Gate) :
    gadgetDataQubits g = Resource.width g * (Codes.Surface.rotatedSurface 27).n := by
  unfold gadgetDataQubits
  obtain ⟨hn, _, _⟩ := Codes.Surface.rotatedSurface27_counts
  rw [hn]

/-! ## §2. SYNDROME qubits (SSA — fresh per round). -/

/-- **SYNDROME qubits of a gadget (SSA)**: one FRESH qubit per stabilizer
measurement, so the count equals the syndrome-measurement count of the
monolithic physical circuit (walked by `measCountC`).  `d` rounds of `m`
checks ⇒ `d · m` qubits (NO reuse). -/
def gadgetSyndromeQubits (g : Gate) : Nat :=
  physicalStmtCount (gadgetPPM g) * (27 * (Resource.width g * 728))

/-- The SSA syndrome-qubit count IS the walked syndrome-measurement count of
the generated monolithic circuit — fresh-per-measurement, by definition of
SSA. -/
theorem gadgetSyndromeQubits_eq_measCount (g : Gate) :
    gadgetSyndromeQubits g = measCountC (gadgetPhysical g) :=
  (gadget_measCount g).symm

/-! ## §3. LATTICE-SURGERY merges (the joint measurements). -/

/-- **NUMBER OF LATTICE-SURGERY MERGES**: every PPM measurement statement is
one joint logical Pauli measurement realized by a merge.  Walked by
`countMeas` over the gadget's PPM program. -/
def gadgetMergeCount (g : Gate) : Nat := countMeas (gadgetPPM g)

/-! ## §4. LATTICE-SURGERY ANCILLA — NOT FREE.

  EMPHASIS (per the QEC charter): a code-switching / lattice-surgery merge is
  NOT free.  Each merge allocates a FRESH ancilla patch — a full distance-27
  surface patch (729 data qubits) that must ALSO be syndrome-extracted for
  `d = 27` rounds (SSA, fresh per round) — `729 + 27·728 = 20385` physical
  qubits, allocated fresh, per merge.  These are added to the physical total,
  never neglected. -/

/-- **The fresh ancilla cost of ONE lattice-surgery merge**: a full d=27
surface patch (data) plus its `d`-round SSA syndrome — `729 + 27·728`. -/
def mergeAncillaFootprint : Nat := 729 + 27 * 728

/-- The per-merge ancilla footprint IS a full fresh surface patch's data
plus `d` rounds of its syndrome — verified against `surface27`. -/
theorem mergeAncillaFootprint_eq :
    mergeAncillaFootprint
      = (Codes.Surface.rotatedSurface 27).n
        + 27 * ((Codes.Surface.rotatedSurface 27).hx.length
            + (Codes.Surface.rotatedSurface 27).hz.length) := by
  unfold mergeAncillaFootprint
  obtain ⟨hn, hx, hz⟩ := Codes.Surface.rotatedSurface27_counts
  rw [hn, hx, hz]

/-- **TOTAL LATTICE-SURGERY ANCILLA of a gadget** — NOT FREE: one fresh
ancilla patch per merge. -/
def gadgetMergeAncilla (g : Gate) : Nat :=
  gadgetMergeCount g * mergeAncillaFootprint

/-! ## §5. The packaged honest breakdown + the grand total. -/

/-- **THE FULL PHYSICAL-QUBIT REPORT of a gadget** at distance 27 — every
role counted, lattice surgery NOT free. -/
structure PhysReport where
  dataQubits        : Nat   -- fixed logical-patch data
  syndromeQubits    : Nat   -- SSA syndrome (fresh per round = #measurements)
  surgeryMerges     : Nat   -- # lattice-surgery joint measurements
  mergeAncillaQubits : Nat  -- FRESH ancilla patches for the merges (not free!)
  totalPhysQubits   : Nat   -- data + syndrome + merge ancilla
  deriving Repr

/-- **The grand total physical qubits**: data + SSA syndrome + the fresh
lattice-surgery ancilla — surgery is paid for, not free. -/
def gadgetTotalPhysQubits (g : Gate) : Nat :=
  gadgetDataQubits g + gadgetSyndromeQubits g + gadgetMergeAncilla g

/-- Assemble the report for a gadget (all entries from real walks). -/
def gadgetReport (g : Gate) : PhysReport :=
  ⟨gadgetDataQubits g, gadgetSyndromeQubits g, gadgetMergeCount g,
   gadgetMergeAncilla g, gadgetTotalPhysQubits g⟩

/-- **LATTICE SURGERY IS NOT FREE** (the emphasized invariant): whenever a
gadget performs at least one joint measurement, its physical-qubit total
STRICTLY exceeds the bare data + syndrome — the merge ancilla is real. -/
theorem lattice_surgery_not_free (g : Gate) (h : 0 < gadgetMergeCount g) :
    gadgetDataQubits g + gadgetSyndromeQubits g < gadgetTotalPhysQubits g := by
  unfold gadgetTotalPhysQubits gadgetMergeAncilla mergeAncillaFootprint
  have : 0 < gadgetMergeCount g * (729 + 27 * 728) := by positivity
  omega

end FormalRV.QEC.Gidney21
