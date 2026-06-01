/-
  FormalRV.Framework.ScheduleInvariantsExplicit — general
  decidable checkers for the four system-level invariants
  exactly as stated in qianxu (Cain–Xu et al. 2026) Sec.
  SysLayer / our `Framework/SysLayer.lean`.

  Each invariant has a corresponding `*_ok` function below.
  Inputs are completely explicit: an architecture zone breakdown,
  a list of `SysCall`s, and a few scalar bounds.  Outputs are
  `Bool` (decidable).  The user can apply them to any concrete
  schedule and discharge via `decide`.

  ## The four invariants (qianxu Sec. SysLayer)

  * **I1 capacity**:
       ∀ t, ∀ zone role ρ, |claimed_t ∩ slots_ρ| ≤ |slots_ρ|
    For every cycle `t` and every zone role ρ, the number of
    physical atoms claimed by active `SysCall`s at `t` whose
    zone has role ρ does not exceed the total atoms of role ρ.

  * **I2 exclusivity**:
       ∀ t, ∀ distinct c₁, c₂ ∈ sched(t), slots(c₁) ∩ slots(c₂) = ∅
    For every cycle `t`, any two distinct `SysCall`s active at
    `t` claim disjoint atoms.

  * **I3 speed-limit / latency**:
       ∀ (route c), duration(c) ≥ distance(c) / v_max
       ∀ (feedback c), latency(c) ≤ t_cycle
    Atom transports respect v_max, feedback completes within
    one stab cycle.

  * **I4 throughput**:
       ∀ t₀, ∀ W, Σ_{t ∈ [t₀, t₀+W)} magicReq(t) ≤ supply(t₀, W)
    Over any window of W cycles, the cumulative magicReq
    demand does not exceed the factory's CCZ-state supply.

  ## Decidability strategy

  The schedule is a FINITE list of `SysCall`s (each with explicit
  `begin_us`, `end_us`, `kind`).  Each invariant reduces to:

  * I1: for every pair (atom claimed by a syscall, zone), check
    atom is in zone OR atom is not in zone.  Linear-in-atoms.
  * I2: pairwise over syscalls (O(n²)) — for each pair, if time
    intervals overlap, check atom-list disjointness.
  * I3: per-syscall check on `feedback`/`route` syscalls.
  * I4: per-window check over the n+1 distinct start-times
    formed by `magicReq` begin times.  Only O(n²) windows to
    enumerate (any window not aligned with a magicReq begin
    has the same count as the nearest aligned one).

  All four are linear-or-quadratic in the schedule length;
  `decide` closes for schedules with ~100s of syscalls.

  No Mathlib dependency.  Pure Bool / Nat.
-/

import FormalRV.System.Architecture
import FormalRV.System.CodedLayout

namespace FormalRV.Framework.ScheduleInv

open FormalRV.Framework.Architecture

/-! ## Zone breakdown (for I1) -/

/-- An architecture zone described as a contiguous atom range
    with a role label.  `[atom_lo, atom_hi)` defines the zone's
    atoms; `capacity = atom_hi − atom_lo`. -/
structure ArchZone where
  name     : String
  atom_lo  : Nat
  atom_hi  : Nat        -- exclusive
  deriving Repr, Inhabited

namespace ArchZone

@[inline] def capacity (z : ArchZone) : Nat := z.atom_hi - z.atom_lo

@[inline] def contains_atom (z : ArchZone) (a : Nat) : Bool :=
  decide (z.atom_lo ≤ a) && decide (a < z.atom_hi)

end ArchZone

/-- A zoned architecture: list of disjoint ArchZones covering
    the atom-id range `[0, total_atoms)` (possibly with gaps). -/
structure ZonedArch where
  zones        : List ArchZone
  total_atoms  : Nat
  t_cycle_us   : Nat
  v_max_um_per_us : Nat
  deriving Repr, Inhabited

namespace ZonedArch

/-- Find the zone containing the given atom (the first match). -/
def zone_of (arch : ZonedArch) (a : Nat) : Option ArchZone :=
  arch.zones.find? (·.contains_atom a)

end ZonedArch

/-! ## I1: capacity check (per-zone, per-syscall-claim) -/

/-- **I1 capacity check.**  Every physical atom claimed by any
    `SysCall` in the schedule lies inside SOME architecture
    zone (i.e., the schedule does not claim atoms outside the
    architecture).

    For sequential schedules — where at most one syscall is
    active at any cycle — this implies the per-cycle per-zone
    capacity holds (each zone's load is at most one syscall's
    claim ≤ zone capacity).  For parallel schedules, we also
    check per-cycle per-zone aggregate below
    (`capacity_per_cycle_ok`). -/
def capacity_in_arch_ok (arch : ZonedArch) (sched : List SysCall) : Bool :=
  sched.all (fun sc =>
    (syscall_acts_on sc).all (fun a => (arch.zone_of a).isSome))

/-- **I1 capacity, per-cycle.**  For every begin-time t of any
    syscall, count the atoms claimed across all simultaneously-
    active syscalls by zone, and require each zone's count to
    not exceed its capacity.

    Decidable: we enumerate the distinct begin-times in the
    schedule.  Any in-between time has the same active set as
    the nearest preceding begin-time, so this is sufficient. -/
def capacity_per_cycle_ok (arch : ZonedArch) (sched : List SysCall) : Bool :=
  let active_at (t : Nat) : List SysCall :=
    sched.filter (fun sc => decide (sc.begin_us ≤ t) && decide (t < sc.end_us))
  let begin_times := sched.map (·.begin_us)
  let zone_load (t : Nat) (z : ArchZone) : Nat :=
    ((active_at t).flatMap syscall_acts_on).filter z.contains_atom |>.length
  begin_times.all (fun t =>
    arch.zones.all (fun z => decide (zone_load t z ≤ z.capacity)))

/-! ## I2: pairwise exclusivity -/

/-- Two intervals `[a_lo, a_hi)` and `[b_lo, b_hi)` overlap iff
    `a_lo < b_hi ∧ b_lo < a_hi` (and they are nonempty,
    which we don't check separately). -/
@[inline] def intervals_overlap (a_lo a_hi b_lo b_hi : Nat) : Bool :=
  decide (a_lo < b_hi) && decide (b_lo < a_hi)

/-- Two atom lists are disjoint iff no atom appears in both. -/
@[inline] def atoms_disjoint (xs ys : List Nat) : Bool :=
  xs.all (fun a => ¬ ys.contains a)

/-- **I2 exclusivity check.**  For every pair `(i, j)` of distinct
    positions in the schedule, if syscalls `i` and `j` overlap in
    time, their claimed atoms are disjoint. -/
def exclusivity_ok (sched : List SysCall) : Bool :=
  let n := sched.length
  (List.range n).all (fun i =>
    (List.range n).all (fun j =>
      if decide (i < j) then
        match sched[i]?, sched[j]? with
        | some s_i, some s_j =>
            if intervals_overlap s_i.begin_us s_i.end_us
                                 s_j.begin_us s_j.end_us then
              atoms_disjoint (syscall_acts_on s_i) (syscall_acts_on s_j)
            else true
        | _, _ => true
      else true))

/-! ## I3: latency (feedback) and speed-limit (route) -/

/-- **I3 feedback-latency check.**  Every `PauliFrameUpdate`
    syscall completes within one stabilizer cycle. -/
def feedback_latency_ok (t_cycle_us : Nat) (sched : List SysCall) : Bool :=
  sched.all (fun sc =>
    match sc.kind with
    | .PauliFrameUpdate _ =>
        decide (sc.end_us - sc.begin_us ≤ t_cycle_us)
    | _ => true)

/-- **I3 speed-limit check.**  Every `TransitQubit` syscall
    satisfies `duration · v_max ≥ distance`.

    Note: the existing `TransitQubit q c` SysCall doesn't carry
    an explicit `distance` field; the caller supplies it via
    `distance_fn` indexed by channel id `c`.  For schedules with
    NO transits (static architectures like our cuccaro CCZ demo),
    this check is vacuously true. -/
def speed_limit_ok (v_max_um_per_us : Nat)
    (distance_fn : Nat → Nat) (sched : List SysCall) : Bool :=
  sched.all (fun sc =>
    match sc.kind with
    | .TransitQubit _ channel_id =>
        decide ((sc.end_us - sc.begin_us) * v_max_um_per_us
                ≥ distance_fn channel_id)
    | _ => true)

/-- **I3 decoder-reaction-time check.**  Every `DecodeSyndrome`
    syscall completes within `t_react_us` µs (the architecture's
    decoder reaction budget).  Without this, the decoder cannot
    catch up with the per-cycle syndrome stream.

    (Previously this check existed only at the non-decidable
    `Architecture.latency_ok : Prop` level; this is the decidable
    counterpart.) -/
def decoder_react_ok (t_react_us : Nat) (sched : List SysCall) : Bool :=
  sched.all (fun sc =>
    match sc.kind with
    | .DecodeSyndrome _ =>
        decide (sc.end_us - sc.begin_us ≤ t_react_us)
    | _ => true)

/-- Combined I3: feedback latency AND transit speed-limit AND
    decoder reaction-time. -/
def latency_speed_ok (t_cycle_us v_max_um_per_us : Nat)
    (distance_fn : Nat → Nat) (sched : List SysCall) : Bool :=
  feedback_latency_ok t_cycle_us sched
  && speed_limit_ok v_max_um_per_us distance_fn sched

/-- Strengthened I3 that ALSO requires the decoder reaction-time
    check.  `t_react_us` is supplied separately because `ZonedArch`
    only carries `t_cycle_us`; the caller passes the architecture's
    `t_react_us` field. -/
def latency_speed_decoder_ok
    (t_cycle_us v_max_um_per_us t_react_us : Nat)
    (distance_fn : Nat → Nat) (sched : List SysCall) : Bool :=
  feedback_latency_ok t_cycle_us sched
  && speed_limit_ok v_max_um_per_us distance_fn sched
  && decoder_react_ok t_react_us sched

/-! ## I4: factory throughput (per-window) -/

/-- Count `magicReq` syscalls whose `begin_us` falls inside
    `[t0, t0 + window)`. -/
def magicReq_count_in_window (sched : List SysCall) (t0 window : Nat) : Nat :=
  sched.foldl (fun acc sc =>
    match sc.kind with
    | .RequestMagicState _ =>
        if decide (t0 ≤ sc.begin_us) && decide (sc.begin_us < t0 + window)
        then acc + 1
        else acc
    | _ => acc) 0

/-- **I4 window-throughput check.**  For every window `[t0, t0 + window_us)`
    aligned with a magicReq's `begin_us`, the number of
    magicReqs inside the window does not exceed
    `max_per_window`.

    Decidable: we enumerate t0 over the magicReq begin times.
    Windows not aligned with a magicReq begin contain a SUBSET
    of magicReqs of some aligned window, so this is sufficient.

    For qianxu's factory (1 CCZ per 12_000 µs distillation
    cycle), set `window_us = 12_000` and `max_per_window = 1`. -/
def window_throughput_ok (sched : List SysCall)
    (window_us max_per_window : Nat) : Bool :=
  let magic_reqs := sched.filter (fun sc =>
    match sc.kind with
    | .RequestMagicState _ => true
    | _                    => false)
  let begin_times := magic_reqs.map (·.begin_us)
  begin_times.all (fun t0 =>
    decide (magicReq_count_in_window sched t0 window_us ≤ max_per_window))

/-! ## Headline -/

/-- The four-invariant headline checker.  Takes everything the
    framework needs:
    * the zoned architecture,
    * the schedule,
    * factory window parameters (window_us, max_per_window),
    * a route distance function (or zero for no-transit). -/
def all_invariants_ok
    (arch : ZonedArch)
    (sched : List SysCall)
    (window_us max_per_window : Nat)
    (distance_fn : Nat → Nat) : Bool :=
  capacity_in_arch_ok arch sched
  && capacity_per_cycle_ok arch sched
  && exclusivity_ok sched
  && latency_speed_ok arch.t_cycle_us arch.v_max_um_per_us distance_fn sched
  && window_throughput_ok sched window_us max_per_window

end FormalRV.Framework.ScheduleInv
