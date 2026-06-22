/-
  FormalRV.System.RoutingResourceModel — an ARCHITECTURE-AGNOSTIC model of routing & scheduling
  as physical-resource RESERVATION, and proofs that it is consistent with concrete architectures
  (surface-code lattice surgery à la Litinski 1808.02892, and movement-based neutral-atom/ion).

  ## The general concept (learned from, but not specific to, Litinski)

  We deliberately do NOT introduce `Tile`, patch geometry, or any surface-code-specific type.
  Instead we extract the GENERAL lesson that every fault-tolerant architecture shares:

    * A logical operation RESERVES a footprint of physical RESOURCES — its `operands` plus a
      `routing` region used to connect/mediate them — for a time window.
    * ROUTING IS A RESERVATION, not a free side-effect: the routing region occupies real
      resources for the operation's duration.
    * Two operations CONFLICT iff they overlap in time AND their reserved footprints share a
      resource.  (Surface code: ancilla-tile PATHS overlap.  Neutral atom: transit CORRIDORS
      overlap.  Same rule.)
    * `routingQubits` is a general cost primitive — the SIZE of the reserved routing list, the
      same list the exclusivity check reads (with a duplicates caveat; see §3).

  ## Consistency with the architectures (the point of this file)

  The general `conflict`/`scheduleValid` is shown to be CONSISTENT with:
    * Litinski surface-code lattice surgery: instantiating `routing :=` the ancilla path, the
      general conflict IS "two PPMs conflict iff their ancilla paths overlap"
      (`litinski_simultaneous_conflict`).  No tile type needed — resources are abstract ids and
      the ancilla path is just the list of resources the surgery occupies.
    * Neutral-atom / trapped-ion movement: instantiating `routing :=` a transit corridor, the
      general conflict is corridor exclusivity (`transit_conflict_is_corridor_overlap`).
    * The OLD operand-only exclusivity (`exclusivity_ok` on named operands): the degenerate case
      `routing = []` (`conflict_no_routing`) — so the general model strictly REFINES it.

  Self-contained (Nat/List only).
-/

namespace FormalRV.System.RoutingResourceModel

/-! ## §1. Abstract resources and reserved operations. -/

/-- An abstract physical resource unit: a qubit, a site, a tile-qubit — the granularity is the
    architecture's choice; the laws below are agnostic to it. -/
abbrev Resource := Nat

/-- A scheduled operation reserves a footprint of resources — `operands` (the data resources it
    acts on) plus `routing` (the region reserved to connect/mediate them) — during the window
    `[begin_t, begin_t + dur_t)`. -/
structure ResOp where
  operands : List Resource
  routing  : List Resource
  begin_t  : Nat
  dur_t    : Nat
  deriving Repr

/-- The full reserved footprint: operands together with the routing region. -/
def ResOp.footprint (op : ResOp) : List Resource := op.operands ++ op.routing

/-- **`routingQubits`** — the general routing cost = the length of the routing list (duplicates
    counted; see the limitation noted at `routingQubits_is_reserved`). -/
def ResOp.routingQubits (op : ResOp) : Nat := op.routing.length

/-! ## §2. The general conflict / exclusivity rule. -/

/-- Two operations overlap in time iff their windows intersect. -/
def timeOverlap (a b : ResOp) : Bool :=
  decide (a.begin_t < b.begin_t + b.dur_t) && decide (b.begin_t < a.begin_t + a.dur_t)

/-- Two resource lists share a unit. -/
def overlap (s t : List Resource) : Bool := s.any (fun r => t.contains r)

/-- **General conflict.**  Two operations conflict iff they overlap in time AND their reserved
    footprints (operands + routing) share a resource.  This one rule subsumes surface-code
    ancilla-path overlap and neutral-atom corridor overlap. -/
def conflict (a b : ResOp) : Bool := timeOverlap a b && overlap a.footprint b.footprint

/-- A schedule is VALID iff no two distinct operations conflict (footprint-exclusivity). -/
def scheduleValid (ops : List ResOp) : Bool :=
  let n := ops.length
  (List.range n).all (fun i => (List.range n).all (fun j =>
    if decide (i < j) then
      match ops[i]?, ops[j]? with
      | some a, some b => ! conflict a b
      | _, _ => true
    else true))

/-- Disjoint-in-time operations never conflict — you can always serialize (wait). -/
theorem no_conflict_if_disjoint_time (a b : ResOp) (h : timeOverlap a b = false) :
    conflict a b = false := by
  unfold conflict; rw [h]; rfl

/-- Footprint-disjoint operations never conflict — they run in parallel in different regions. -/
theorem no_conflict_if_disjoint_footprint (a b : ResOp)
    (h : overlap a.footprint b.footprint = false) : conflict a b = false := by
  unfold conflict; rw [h, Bool.and_false]

/-! ## §3. `routingQubits` counts the reserved routing list. -/

/-- Length accounting: `footprint.length = operands.length + routingQubits` (this is just
    `List.length_append`).  LIMITATION: footprints are LISTS with duplicates allowed, so an op can
    inflate `routingQubits` (e.g. one resource id repeated 100 times reports cost 100) while the
    exclusivity check (`overlap`) sees only that single resource.  The count is tied to the
    reserved list, not to the number of DISTINCT resources reserved. -/
theorem routingQubits_is_reserved (op : ResOp) :
    op.footprint.length = op.operands.length + op.routingQubits := by
  unfold ResOp.footprint ResOp.routingQubits; rw [List.length_append]

/-! ## §4. Subsumption of the old operand-only exclusivity. -/

/-- With no routing reservation (`routing = []`), conflict reduces to OPERAND overlap — exactly the
    old `exclusivity_ok`/`syscall_acts_on` behaviour (which named only operands).  So the general
    model agrees with the old one when routing is empty and catches MORE conflicts when routing is
    present.  This is the precise sense in which the general model REFINES the existing one. -/
theorem conflict_no_routing (a b : ResOp) (ha : a.routing = []) (hb : b.routing = []) :
    conflict a b = (timeOverlap a b && overlap a.operands b.operands) := by
  unfold conflict ResOp.footprint
  rw [ha, hb, List.append_nil, List.append_nil]

/-! ## §5. Consistency with Litinski surface-code lattice surgery. -/

/-- A surface-code lattice-surgery Pauli-product measurement, AS AN INSTANCE of the general model:
    `operands` = the operand patch resources, `routing` = the ANCILLA-PATH resources it occupies
    for 1 clock.  No surface-code-specific type — resources are abstract ids; the ancilla path is
    just the list of resources the surgery reserves. -/
def latticeSurgeryOp (patch ancillaPath : List Resource) (clk : Nat) : ResOp :=
  { operands := patch, routing := ancillaPath, begin_t := clk, dur_t := 1 }

/-- **★ Consistency with the paper ★.**  For two simultaneous lattice-surgery PPMs, the general
    `conflict` is EXACTLY "their footprints (operand patches + ancilla paths) overlap" — i.e.
    Litinski's rule that two PPMs conflict iff their ancilla paths overlap (parallelproducts.tex
    §parallel products).  The general model thus faithfully captures surface-code surgery
    scheduling, with NO tile/patch type. -/
theorem litinski_simultaneous_conflict (patch1 path1 patch2 path2 : List Resource) (clk : Nat) :
    conflict (latticeSurgeryOp patch1 path1 clk) (latticeSurgeryOp patch2 path2 clk)
      = overlap (patch1 ++ path1) (patch2 ++ path2) := by
  unfold conflict latticeSurgeryOp timeOverlap ResOp.footprint
  have h : clk < clk + 1 := Nat.lt_succ_self clk
  simp [h]

/-- By construction (`rfl`): `latticeSurgeryOp` stores `ancillaPath` in the `routing` field, so
    its `routingQubits` is the ancilla-path length.  Definitional glue, not a derived fact. -/
theorem litinski_routingQubits (patch ancillaPath : List Resource) (clk : Nat) :
    (latticeSurgeryOp patch ancillaPath clk).routingQubits = ancillaPath.length := rfl

/-! ## §6. Consistency with movement-based (neutral-atom / trapped-ion) routing. -/

/-- A qubit transit, AS AN INSTANCE of the general model: `operands` = source & destination
    resources, `routing` = the transit-corridor resources it occupies while moving. -/
def transitOp (src dst : Resource) (corridor : List Resource) (begin_t dur_t : Nat) : ResOp :=
  { operands := [src, dst], routing := corridor, begin_t := begin_t, dur_t := dur_t }

/-- For movement-based routing, the general conflict captures corridor/endpoint exclusivity: two
    transits conflict iff (overlapping in time and) their corridors or endpoints share a resource.
    The same general rule serves shuttling architectures. -/
theorem transit_conflict_is_corridor_overlap
    (s1 d1 s2 d2 : Resource) (c1 c2 : List Resource) (b dur : Nat) :
    conflict (transitOp s1 d1 c1 b dur) (transitOp s2 d2 c2 b dur)
      = (decide (0 < dur) && overlap ([s1, d1] ++ c1) ([s2, d2] ++ c2)) := by
  unfold conflict transitOp timeOverlap ResOp.footprint
  by_cases hd : 0 < dur
  · rw [decide_eq_true (by omega : b < b + dur), Bool.and_self, decide_eq_true hd, Bool.true_and]
  · have : dur = 0 := by omega
    subst this; simp [overlap]

/-! ## §7. Demonstration: shared ROUTING conflicts even with disjoint OPERANDS. -/

/-- Operation `gA` acts on operands `{0,2}` and routes through resource `1`. -/
def gA : ResOp := { operands := [0, 2], routing := [1], begin_t := 0, dur_t := 1 }
/-- Operation `gC` acts on DISJOINT operands `{10,12}` but routes through the SAME resource `1`. -/
def gC : ResOp := { operands := [10, 12], routing := [1], begin_t := 0, dur_t := 1 }

/-- **The general lesson, demonstrated.**  `gA` and `gC` share NO operand, yet they conflict
    because their routing regions share resource `1` — the conflict the old operand-only model
    (`syscall_acts_on` on named qubits) could not see.  This is architecture-agnostic: `1` could be
    an ancilla tile (surface code) or a corridor site (neutral atom). -/
theorem shared_routing_conflicts : conflict gA gC = true := by native_decide

/-- The same pair is admissible once serialized — `gC` WAITS for `gA` (next window): different
    time windows ⇒ no shared-resource conflict. -/
theorem shared_routing_ok_when_serialized :
    scheduleValid [gA, { gC with begin_t := 1 }] = true := by native_decide

/-- And disjoint-routing operations run in parallel. -/
theorem disjoint_routing_parallel_ok :
    scheduleValid [gA, { gC with routing := [99] }] = true := by native_decide

/-! ## §8. Architecture-agnostic wait law (no operation before its inputs are ready). -/

/-- An operation is READY to start at `t` iff all its input-producing operations have completed by
    `t` (their end times `≤ t`).  This is the general produce-before-consume dependency — magic
    states, ancilla preparation, prior measurement outcomes alike. -/
def readyAt (inputEnds : List Nat) (t : Nat) : Bool := inputEnds.all (fun e => decide (e ≤ t))

/-- **Wait law.**  If any input completes after `t`, the operation is not ready at `t` — it must
    wait.  Architecture-agnostic (subsumes the magic-state readiness law). -/
theorem must_wait_for_inputs (inputEnds : List Nat) (t e : Nat) (he : e ∈ inputEnds) (hlt : t < e) :
    readyAt inputEnds t = false := by
  unfold readyAt
  rw [List.all_eq_false]
  exact ⟨e, he, by simp [Nat.not_le.mpr hlt]⟩

/-! ## §9. What DISTINGUISHES the architectures: physical mobility.

    §1–§8 treat neutral-atom transport and surface-code lattice surgery IDENTICALLY for
    conflict / latency / throughput — correctly, since both reserve a footprint for a duration.
    But they differ PHYSICALLY, and the model must say so:

      * A neutral atom (or trapped ion) PHYSICALLY MOVES through the system, so routing RELOCATES
        the qubit — its hardware slot changes.
      * A superconducting / surface-code device has qubits bolted to the hardware, so "routing a
        logical qubit" is done by LATTICE SURGERY (a measurement through transient ancilla) with
        NO physical qubit ever moving.

    We capture the difference as the PERSISTENT effect on the physical placement: transport
    changes it; surgery leaves it invariant.  Conflict/latency/throughput remain shared (they
    depend only on the reservation, not the kind). -/

/-- Which logical qubit (if any) physically occupies each resource (hardware slot); `none` = free. -/
abbrev Placement := Resource → Option Nat

/-- Point update of a placement. -/
def Placement.set (p : Placement) (r : Resource) (v : Option Nat) : Placement :=
  fun x => if x = r then v else p x

/-- The two routing paradigms, distinguished by their PERSISTENT effect on physical placement.
    `transport q src dst` = a MOBILE architecture (neutral atom / ion) physically relocates the
    qubit holding logical `q` from hardware slot `src` to `dst`.  `surgery` = a STATIC architecture
    (superconducting / surface-code lattice surgery): the operation is measurement-mediated through
    transient ancilla and NO physical qubit moves. -/
inductive RoutingKind where
  | transport (q src dst : Resource)
  | surgery
  deriving DecidableEq, Repr

/-- The persistent placement effect.  Transport frees the source slot and occupies the destination;
    surgery leaves the physical placement unchanged. -/
def RoutingKind.applyPlacement : RoutingKind → Placement → Placement
  | .transport q src dst, p => (p.set src none).set dst (some q)
  | .surgery, p => p

/-- A routed operation pairs a transient RESERVATION (→ latency/conflict/throughput, SHARED across
    architectures) with a routing KIND (→ persistent placement, DIFFERENT across architectures). -/
structure RoutedOp where
  reservation : ResOp
  kind        : RoutingKind

/-- Conflict between routed ops is computed from their RESERVATIONS alone. -/
def routedConflict (a b : RoutedOp) : Bool := conflict a.reservation b.reservation

/-- **Conflict is kind-blind — by construction (`rfl`).**  `routedConflict` reads only the
    reservations, so changing the routing kind (transport ↔ surgery) cannot change it.  This
    records the DESIGN DECISION that scheduling treats neutral-atom and surface-code routing
    identically; it is definitional, not a derived fact. -/
theorem routedConflict_ignores_kind (a b : RoutedOp) (k : RoutingKind) :
    routedConflict { a with kind := k } b = routedConflict a b := rfl

/-- **★ Surgery preserves physical placement ★** — surface-code lattice surgery moves no physical
    qubit (the logical operation is measurement-mediated; the transient ancilla is freed).  This is
    the formal mark of a STATIC (superconducting) architecture. -/
theorem surgery_preserves_placement (p : Placement) :
    RoutingKind.surgery.applyPlacement p = p := rfl

/-- **★ Transport relocates a physical qubit ★** — a neutral atom / ion physically travels, so the
    operand's hardware slot CHANGES (source freed, destination occupied). -/
theorem transport_relocates (q src dst : Resource) (p : Placement) (h : dst ≠ src) :
    (RoutingKind.transport q src dst).applyPlacement p dst = some q
    ∧ (RoutingKind.transport q src dst).applyPlacement p src = none := by
  unfold RoutingKind.applyPlacement Placement.set
  exact ⟨by simp, by simp [Ne.symm h]⟩

/-- **★ The crisp distinction ★.**  When the source held `q` and the destination was free
    (`src ≠ dst`), a TRANSPORT genuinely CHANGES the physical placement, whereas SURGERY leaves it
    fixed.  So the two architecture classes — identical in conflict / latency / throughput — differ
    exactly in their physical mobility: neutral atoms move, surface-code qubits do not. -/
theorem transport_changes_but_surgery_preserves
    (q src dst : Resource) (p : Placement) (h : dst ≠ src) (hq : p src = some q) (hfree : p dst = none) :
    (RoutingKind.transport q src dst).applyPlacement p ≠ p
    ∧ RoutingKind.surgery.applyPlacement p = p := by
  refine ⟨fun heq => ?_, rfl⟩
  have hd : (RoutingKind.transport q src dst).applyPlacement p dst = some q :=
    (transport_relocates q src dst p h).1
  rw [heq, hfree] at hd
  simp at hd

end FormalRV.System.RoutingResourceModel
