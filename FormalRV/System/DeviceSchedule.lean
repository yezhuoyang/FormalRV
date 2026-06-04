/-
  FormalRV.System.DeviceSchedule — an END-TO-END device-schedule execution engine and validity
  checker for fault-tolerant quantum computation, built on the architecture-agnostic
  `RoutingResourceModel` (which is proven consistent with Litinski surface-code lattice surgery
  and with neutral-atom/ion transport).

  This threads the routing/placement model into a RUNNING schedule and checks, together, the five
  concerns a real FT machine must satisfy — the "tricky things":

    1. **T-state preparation & scheduling** — `prepMagic` ops occupy a factory footprint for a
       production duration.
    2. **State teleportation (magic consumption)** — `consumeMagic` ops are surgery PPMs that
       DEPEND on a completed `prepMagic` (the produce-before-consume WAIT), via `deps`.
    3. **Decoder scheduling** — `decode` ops are bounded by the reaction time and limited by the
       decoder count (queue depth).
    4. **Space-time conflict avoidance** — no two time-overlapping ops share a footprint resource.
    5. **Parallelism** — time-overlapping ops with DISJOINT footprints run concurrently (only
       overlapping footprints are rejected).

  Plus the PLACEMENT state-evolution: folding each op's effect over the schedule, with the
  surface-code invariant that a static (surgery-only) schedule never moves a physical qubit.

  Honesty: the full RSA-scale schedule (~10⁹ ops) is not constructed concretely; this engine + the
  generic validity theorems + a representative Shor-fragment demo + the resource-number connection
  (`DeviceScheduleCapstone`) constitute the verified system at the achievable level.
  Self-contained beyond `RoutingResourceModel` (Nat/List only).
-/
import FormalRV.System.RoutingResourceModel

namespace FormalRV.System.DeviceSchedule

open FormalRV.System.RoutingResourceModel

/-! ## §1. Device operations, schedule, and device configuration. -/

/-- The kind of a scheduled device operation. -/
inductive OpKind where
  | prepMagic                     -- T/CCZ-state preparation in a factory
  | consumeMagic                  -- state teleportation: consume a prepared magic via surgery PPM
  | logicalSurgery                -- a Pauli-product measurement between logical qubits
  | decode                        -- a decoder run on a completed syndrome round
  | move (rk : RoutingKind)       -- relocate a logical qubit: transport (mobile) or surgery (static)
  deriving Repr, Inhabited

/-- A scheduled operation: its footprint of reserved resources during `[begin_t, begin_t+dur_t)`,
    and the ids of operations that must COMPLETE before it may begin (`deps` — the wait edges:
    magic readiness, decoder reaction, measurement feed-forward). -/
structure DeviceOp where
  id        : Nat
  kind      : OpKind
  footprint : List Resource
  begin_t   : Nat
  dur_t     : Nat
  deps      : List Nat
  deriving Repr, Inhabited

def DeviceOp.end_t (op : DeviceOp) : Nat := op.begin_t + op.dur_t

abbrev DSchedule := List DeviceOp

/-- Device configuration: total physical resources, decoder count, reaction-time bound, code-cycle
    time, code distance. -/
structure Device where
  totalResources : Nat
  nDecoders      : Nat
  reactionTime   : Nat
  codeCycleUs    : Nat
  d              : Nat
  deriving Repr

def DeviceOp.isDecode (op : DeviceOp) : Bool :=
  match op.kind with | OpKind.decode => true | _ => false

def DeviceOp.activeAt (op : DeviceOp) (t : Nat) : Bool :=
  decide (op.begin_t ≤ t) && decide (t < op.end_t)

/-! ## §2. The five validity checks. -/

/-- Two ops overlap in time. -/
def opsTimeOverlap (a b : DeviceOp) : Bool :=
  decide (a.begin_t < b.end_t) && decide (b.begin_t < a.end_t)

/-- Two ops conflict iff they overlap in time AND share a footprint resource. -/
def DeviceOp.conflictsWith (a b : DeviceOp) : Bool :=
  opsTimeOverlap a b && overlap a.footprint b.footprint

/-- **(4) Space-time conflict-freedom** (recursive pairwise form).  No two distinct ops overlap in
    time AND share a footprint resource.  Parallelism is ALLOWED: time-overlapping ops with disjoint
    footprints pass.  Recursive shape (head vs. all of tail, then recurse) for clean induction. -/
def conflictFree : DSchedule → Bool
  | []        => true
  | op :: rest => rest.all (fun o => ! op.conflictsWith o) && conflictFree rest

def findOp (sched : DSchedule) (oid : Nat) : Option DeviceOp := sched.find? (fun o => o.id == oid)

/-- **(2)+(3) Dependencies respected (the WAIT law).**  Every dependency op exists and COMPLETES
    before the dependent op begins.  This enforces: magic produced+routed before consumed; decode
    finished before a feed-forward-dependent op; ancilla prepared before use. -/
def depsRespected (sched : DSchedule) : Bool :=
  sched.all (fun op => op.deps.all (fun dpid =>
    match findOp sched dpid with
    | some dop => decide (dop.end_t ≤ op.begin_t)
    | none => false))

/-- Schedule boundary times (begin/end of every op, plus 0). -/
def boundaries (sched : DSchedule) : List Nat :=
  sched.foldl (fun acc o => o.begin_t :: o.end_t :: acc) [0]

/-- Total footprint resources reserved by ops active at time `t` (an upper bound on distinct
    occupancy; exact when the schedule is conflict-free, since active footprints are then disjoint). -/
def activeFootprintSize (sched : DSchedule) (t : Nat) : Nat :=
  ((sched.filter (fun o => o.activeAt t)).map (fun o => o.footprint.length)).sum

/-- Active footprint of `o :: rest`: `o`'s footprint if active, plus the rest. -/
theorem activeFootprintSize_cons (o : DeviceOp) (rest : DSchedule) (t : Nat) :
    activeFootprintSize (o :: rest) t
      = (if o.activeAt t then o.footprint.length else 0) + activeFootprintSize rest t := by
  unfold activeFootprintSize
  by_cases h : o.activeAt t = true
  · simp [List.filter_cons, h, List.map_cons, List.sum_cons]
  · simp [List.filter_cons, h]

/-- **(capacity)** At every boundary, the reserved footprint fits the device. -/
def capacityRespected (dev : Device) (sched : DSchedule) : Bool :=
  (boundaries sched).all (fun t => decide (activeFootprintSize sched t ≤ dev.totalResources))

/-- **(3) Decoder queue.**  At every boundary, the number of active `decode` ops ≤ `nDecoders`. -/
def decoderQueueRespected (dev : Device) (sched : DSchedule) : Bool :=
  (boundaries sched).all (fun t =>
    decide ((sched.filter (fun o => o.isDecode && o.activeAt t)).length ≤ dev.nDecoders))

/-- **(3) Reaction bound.**  Every `decode` op completes within the reaction time. -/
def reactionRespected (dev : Device) (sched : DSchedule) : Bool :=
  sched.all (fun o => if o.isDecode then decide (o.dur_t ≤ dev.reactionTime) else true)

/-- **★ END-TO-END device-schedule validity ★** — all five concerns at once. -/
def scheduleValid (dev : Device) (sched : DSchedule) : Bool :=
  conflictFree sched
  && depsRespected sched
  && capacityRespected dev sched
  && decoderQueueRespected dev sched
  && reactionRespected dev sched

/-- Validity projects to each component (so a valid schedule satisfies conflict-freedom, the wait
    law, capacity, the decoder queue, and the reaction bound individually). -/
theorem scheduleValid_components (dev : Device) (sched : DSchedule)
    (h : scheduleValid dev sched = true) :
    conflictFree sched = true ∧ depsRespected sched = true ∧ capacityRespected dev sched = true
    ∧ decoderQueueRespected dev sched = true ∧ reactionRespected dev sched = true := by
  unfold scheduleValid at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-! ## §3. Placement state-evolution over the running schedule. -/

/-- An op's persistent effect on physical placement: a `move` applies its `RoutingKind`'s effect;
    every other op leaves placement unchanged. -/
def DeviceOp.placementEffect (op : DeviceOp) (p : Placement) : Placement :=
  match op.kind with
  | OpKind.move rk => rk.applyPlacement p
  | _ => p

/-- Replay the schedule, evolving the physical placement op by op. -/
def evolvePlacement (sched : DSchedule) (p0 : Placement) : Placement :=
  sched.foldl (fun p op => op.placementEffect p) p0

/-- Replaying `op :: rest` = apply `op`'s effect, then replay `rest`. -/
theorem evolvePlacement_cons (op : DeviceOp) (rest : DSchedule) (p0 : Placement) :
    evolvePlacement (op :: rest) p0 = evolvePlacement rest (op.placementEffect p0) := by
  unfold evolvePlacement; rw [List.foldl_cons]

/-- An op is STATIC (moves no physical qubit) iff it is not a `transport` move. -/
def DeviceOp.isStatic (op : DeviceOp) : Bool :=
  match op.kind with
  | OpKind.move RoutingKind.surgery => true
  | OpKind.move (RoutingKind.transport _ _ _) => false
  | _ => true

/-- A static op leaves physical placement unchanged. -/
theorem placementEffect_static (op : DeviceOp) (p : Placement) (h : op.isStatic = true) :
    op.placementEffect p = p := by
  unfold DeviceOp.isStatic at h
  unfold DeviceOp.placementEffect
  match hk : op.kind with
  | OpKind.move rk =>
      cases rk with
      | surgery => rfl
      | transport q s d => rw [hk] at h; simp at h
  | OpKind.prepMagic => rfl
  | OpKind.consumeMagic => rfl
  | OpKind.logicalSurgery => rfl
  | OpKind.decode => rfl

/-- **★ Surface-code placement invariant ★** — a STATIC schedule (no `transport` moves: pure
    surface-code lattice surgery) never moves a physical qubit: the placement after replaying the
    whole schedule equals the initial placement.  (Contrast a transport/neutral-atom schedule,
    which relocates qubits.) -/
theorem evolvePlacement_static : ∀ (sched : DSchedule) (p0 : Placement),
    sched.all DeviceOp.isStatic = true → evolvePlacement sched p0 = p0
  | [], _, _ => rfl
  | op :: rest, p0, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [evolvePlacement_cons, placementEffect_static op p0 h.1]
      exact evolvePlacement_static rest p0 h.2

end FormalRV.System.DeviceSchedule
