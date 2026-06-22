/-
  FormalRV.System.FTSchedule — SYSTEM-LEVEL FAULT-TOLERANT SCHEDULING.

  The four hardware concerns are syscalls — RequestMagicState (T-factory),
  RequestFreshAncilla (ancilla), TransitQubit (routing), DecodeSyndrome
  (classical decoding) — and the decidable bundle
  `ScheduleInv.all_invariants_ok` (capacity, exclusivity, latency/speed,
  decoder reaction, throughput) guarantees they are schedulable.  `ft_ok`
  combines that bundle with a schedule-level decoder budget and distance
  adequacy (3·τ_s ≥ 2·d).  A passing `FTSchedule` is fault-tolerant:
  schedulable (invariants) + error-suppressed (distance); the syscalls are
  NON-SEMANTIC (we verify the schedule satisfies invariants + FT, not what
  each syscall computes — the logical-action semantics live in
  `QEC/LatticeSurgery/SurgeryCorrect`).  Resource count (magic states,
  ancillas, decode rounds, routing moves, wallclock) follows from the
  schedule.  Merged-code distance d̃ ≥ d is the delimited external input.

  ## How the rungs map to the bundle

  * **capacity** (`capacity_in_arch_ok` ∧ `capacity_per_cycle_ok`) — every
    claimed atom lies in a zone, and no zone is over-subscribed at any
    begin-time.  This is the ANCILLA / qubit-budget concern.
  * **exclusivity** (`exclusivity_ok`) — time-overlapping syscalls claim
    disjoint atoms.  This is the no-double-booking concern.
  * **latency / speed** (`latency_speed_ok`) — feedback (`PauliFrameUpdate`)
    completes within one stabilizer cycle, and every `TransitQubit` respects
    `duration · v_max ≥ distance`.  This is the ROUTING + feedback concern.
  * **decoder reaction** (`decoder_react_ok arch.t_react_us`) — every
    `DecodeSyndrome` completes within the architecture's reaction budget
    (the qianxu within-cycle decoding claim).  This is the
    CLASSICAL-DECODING concern.
  * **throughput** (`window_throughput_ok`) — magic-state demand per window
    ≤ supply.  This is the T-FACTORY concern.
  * **distance adequacy** (`3·τ_s ≥ 2·d`) — the error-suppression rung, the
    cycle-count analogue of `SurgeryCorrect.SurgeryFaultTolerant`'s
    `merged_dist ≥ data_code.d`.  τ_s must be large enough (≥ ⌈2d/3⌉) to
    balance space-like and time-like logical error.

  ## The two decoder budgets

  `all_invariants_ok` checks `decoder_react_ok` against the ARCHITECTURE
  field `arch.t_react_us`; `ft_ok` ALSO checks it against the independent
  SCHEDULE-LEVEL field `FTSchedule.t_react_us`.  The effective decoder
  budget is the minimum of the two.  The second conjunct is not redundant:
  the budgets can differ, `ftSchedule_guarantee` exposes
  `decoder_react_ok f.t_react_us` in its conclusion, and
  `demoFT_slowDecoder` below fails ONLY the schedule-level budget (its
  `arch.t_react_us = 10` check passes).

  No Mathlib.  Pure List / Bool / Nat + `decide`.  No `sorry`, no `axiom`,
  no `admit`.
-/
import FormalRV.System.Invariants.ScheduleInvariantsExplicit
import FormalRV.System.Checkers.SystemChecker
import FormalRV.Resource.SysCallCount

namespace FormalRV.System.FTSchedule

open FormalRV.System.Architecture FormalRV.System.ScheduleInv

/-! ## (1) The FT-schedule bundle -/

/-- A fault-tolerant schedule: a syscall schedule on an architecture, plus the
    distance/τ_s adequacy data. -/
structure FTSchedule where
  arch            : ZonedArch
  sched           : List SysCall
  window_us       : Nat
  max_per_window  : Nat
  distance_fn     : Nat → Nat
  code_distance   : Nat        -- d (processor/data code distance)
  tau_s           : Nat        -- surgery cycle count
  t_react_us      : Nat        -- schedule-level decoder reaction budget; independent
                               -- of arch.t_react_us (qianxu ~1ms/cycle)

/-- Distance adequacy: τ_s ≥ ⌈2d/3⌉, i.e. 3τ_s ≥ 2d (the SurgeryFaultTolerant
    cycle condition that balances space-like and time-like logical error). -/
def FTSchedule.distance_adequate (f : FTSchedule) : Bool :=
  decide (3 * f.tau_s ≥ 2 * f.code_distance)

/-- The full FT-schedule check: the bundle `all_invariants_ok` (capacity =
    ancilla, exclusivity, latency/speed = routing, decoder reaction vs
    `arch.t_react_us`, throughput = T-factory) AND the decoder reaction-time
    bound against the schedule-level budget `f.t_react_us` (independent of
    `arch.t_react_us` — see "The two decoder budgets" in the header) AND
    distance adequacy.  All four hardware concerns — T-factory, ancilla,
    routing, decoding — plus error-suppression are thereby covered. -/
def FTSchedule.ft_ok (f : FTSchedule) : Bool :=
  all_invariants_ok f.arch f.sched f.window_us f.max_per_window f.distance_fn
  && decoder_react_ok f.t_react_us f.sched
  && f.distance_adequate

/-! ## (2) The guarantee theorem -/

/-- A passing FT-schedule satisfies BOTH the system invariants (it is
    schedulable: no resource conflicts, magic demand ≤ supply, latency within
    budget) AND distance adequacy (error suppression governed by the code
    distance). The merged-code distance d̃ ≥ d is the delimited external input
    (cf. SurgeryFaultTolerant); semantic correctness of the surgery operations
    is the already-proven
    SurgeryCorrect.surgery_implements_logical_measurement.  The system syscalls
    themselves are non-semantic — only their invariant satisfaction matters
    here. -/
theorem ftSchedule_guarantee (f : FTSchedule) (h : f.ft_ok = true) :
    all_invariants_ok f.arch f.sched f.window_us f.max_per_window f.distance_fn = true
    ∧ decoder_react_ok f.t_react_us f.sched = true
    ∧ 3 * f.tau_s ≥ 2 * f.code_distance := by
  have := h
  simp only [FTSchedule.ft_ok, FTSchedule.distance_adequate, Bool.and_eq_true,
    decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-! ## (3) Resource budget — the "resource count follows" at system level -/

/-- Count syscalls whose kind satisfies the predicate `p` — an alias for
    THE canonical counter (`Resource/SysCallCount.countWhere`). -/
abbrev countKind : (SysCallKind → Bool) → List SysCall → Nat :=
  FormalRV.Resource.SysCallCount.countWhere

/-- Number of magic-state requests (canonical counter). -/
abbrev magicStateCount : List SysCall → Nat :=
  FormalRV.Resource.SysCallCount.countMagicReq

/-- Number of fresh-ancilla requests (canonical counter). -/
abbrev ancillaCount : List SysCall → Nat :=
  FormalRV.Resource.SysCallCount.countFreshAnc

/-- Number of decoder rounds (canonical counter). -/
abbrev decodeRounds : List SysCall → Nat :=
  FormalRV.Resource.SysCallCount.countDecode

/-- Number of routing moves (canonical counter). -/
abbrev routingMoves : List SysCall → Nat :=
  FormalRV.Resource.SysCallCount.countTransit

/-- Wallclock = latest end timestamp. -/
def wallclock_us (s : List SysCall) : Nat := s.foldl (fun acc c => Nat.max acc c.end_us) 0

/-- The system-level resource budget extracted from a schedule. -/
structure SystemBudget where
  magic_states : Nat
  ancillas     : Nat
  decode_rounds: Nat
  routing_moves: Nat
  wallclock_us : Nat
deriving Repr, DecidableEq

/-- The resource budget of an FT-schedule: counts of each expensive resource
    plus the wallclock.  The "resource count follows" deliverable: every figure
    is read off the schedule, not asserted. -/
def FTSchedule.budget (f : FTSchedule) : SystemBudget :=
  { magic_states := magicStateCount f.sched, ancillas := ancillaCount f.sched,
    decode_rounds := decodeRounds f.sched, routing_moves := routingMoves f.sched,
    wallclock_us := wallclock_us f.sched }

/-! ## (4) Worked instance — a small concrete FT schedule

    A minimal `ZonedArch` with one Data / Workspace / Factory / Routing zone,
    and a schedule exercising all four hardware concerns:
      * `RequestMagicState 2`   — T-factory demand;
      * `RequestFreshAncilla 1` — ancilla request in the Workspace zone;
      * `TransitQubit 30 0`     — a routing move of atom 30 along channel 0,
                                  duration 10 µs, 10·5 = 50 ≥ 30 = distance;
      * `DecodeSyndrome 0`      — a classical decode round;
      * `Measure 5 0`           — a surgery measurement on Data atom 5;
      * `Gate2q 1 2 0`          — a two-qubit gate on Data atoms 1, 2.

    Atoms are pairwise disjoint and all lie in valid zones; timestamps are
    chosen so all five invariants hold (verified by `decide`).  τ_s = 6, d = 9:
    3·6 = 18 ≥ 2·9 = 18, so distance adequacy holds with equality. -/

/-- The worked-instance architecture: Data[0,10) Workspace[10,20)
    Factory[20,30) Routing[30,40), one stabilizer cycle = 100 µs, transport
    speed limit 5 µm/µs. -/
def demoArch : ZonedArch :=
  { zones :=
      [ { name := "Data",      site_lo := 0,  site_hi := 10 }
      , { name := "Workspace", site_lo := 10, site_hi := 20 }
      , { name := "Factory",   site_lo := 20, site_hi := 30 }
      , { name := "Routing",   site_lo := 30, site_hi := 40 } ]
    total_sites := 40
    t_cycle_us  := 100
    v_max_um_per_us := 5
    t_react_us := 10 }

/-- Route distance function: every channel covers 30 µm. -/
def demoDist : Nat → Nat := fun _ => 30

/-- The worked-instance schedule (all four hardware concerns + a surgery
    measurement + a two-qubit gate, on disjoint valid atoms). -/
def demoSched : List SysCall :=
  [ { kind := SysCallKind.RequestMagicState 2,   begin_us := 0,  end_us := 10 }
  , { kind := SysCallKind.RequestFreshAncilla 1, begin_us := 0,  end_us := 10 }
  , { kind := SysCallKind.TransitQubit 30 0,     begin_us := 10, end_us := 20 }
  , { kind := SysCallKind.DecodeSyndrome 0,      begin_us := 20, end_us := 25 }
  , { kind := SysCallKind.Measure 5 0,           begin_us := 30, end_us := 35 }
  , { kind := SysCallKind.Gate2q 1 2 0,          begin_us := 40, end_us := 45 } ]

/-- The worked FT-schedule instance.  τ_s = 6, d = 9 ⇒ 3·6 = 18 ≥ 2·9 = 18. -/
def demoFT : FTSchedule :=
  { arch := demoArch, sched := demoSched, window_us := 1000, max_per_window := 1,
    distance_fn := demoDist, code_distance := 9, tau_s := 6, t_react_us := 10 }

/-- The worked instance IS fault-tolerant: all four system invariants hold and
    distance adequacy holds. -/
example : demoFT.ft_ok = true := by decide

/-- The resource count follows from the schedule: one magic state, one ancilla,
    one decode round, one routing move; wallclock 45 µs. -/
example : demoFT.budget =
    { magic_states := 1, ancillas := 1, decode_rounds := 1, routing_moves := 1,
      wallclock_us := 45 } := by decide

/-- The decomposed guarantee for the worked instance. -/
theorem demoFT_guarantee :
    all_invariants_ok demoFT.arch demoFT.sched demoFT.window_us demoFT.max_per_window
        demoFT.distance_fn = true
    ∧ decoder_react_ok demoFT.t_react_us demoFT.sched = true
    ∧ 3 * demoFT.tau_s ≥ 2 * demoFT.code_distance :=
  ftSchedule_guarantee demoFT (by decide)

/-! ## (5) Negative tests — the FT guard REJECTS violations -/

/-- A schedule identical to `demoSched` except the routing transit is too fast:
    duration 2 µs at v_max = 5 gives 2·5 = 10 < 30 = distance, so the speed
    limit (the routing rung of `latency_speed_ok`) is violated.  This is the
    discriminating "routing/latency too fast" case the bundle catches. -/
def demoSched_slowTransit : List SysCall :=
  [ { kind := SysCallKind.RequestMagicState 2,   begin_us := 0,  end_us := 10 }
  , { kind := SysCallKind.RequestFreshAncilla 1, begin_us := 0,  end_us := 10 }
  , { kind := SysCallKind.TransitQubit 30 0,     begin_us := 10, end_us := 12 }
  , { kind := SysCallKind.DecodeSyndrome 0,      begin_us := 20, end_us := 25 }
  , { kind := SysCallKind.Measure 5 0,           begin_us := 30, end_us := 35 }
  , { kind := SysCallKind.Gate2q 1 2 0,          begin_us := 40, end_us := 45 } ]

/-- Routing speed-limit violation ⇒ `ft_ok = false`. -/
def demoFT_slowTransit : FTSchedule := { demoFT with sched := demoSched_slowTransit }

example : demoFT_slowTransit.ft_ok = false := by decide

/-- Decoder too slow for the SCHEDULE-LEVEL budget: `t_react_us := 2` is below
    the `DecodeSyndrome` latency (25 − 20 = 5), so the
    `decoder_react_ok f.t_react_us` conjunct fails ⇒ `ft_ok = false`.  The
    architecture budget (`arch.t_react_us = 10`) still passes, so this test is
    exactly why the schedule-level conjunct is not redundant. -/
def demoFT_slowDecoder : FTSchedule := { demoFT with t_react_us := 2 }

example : demoFT_slowDecoder.ft_ok = false := by decide

/-- Distance-inadequate: τ_s too small for d ⟹ `ft_ok = false`.
    3·1 = 3 < 2·11 = 22, so distance adequacy fails. -/
def demoFT_lowTauS : FTSchedule := { demoFT with tau_s := 1, code_distance := 11 }

example : demoFT_lowTauS.ft_ok = false := by decide

/-- For completeness: the distance-adequacy conjunct is exactly what fails in
    `demoFT_lowTauS` (the system invariants on the unchanged schedule still
    hold). -/
example : demoFT_lowTauS.distance_adequate = false := by decide

end FormalRV.System.FTSchedule
