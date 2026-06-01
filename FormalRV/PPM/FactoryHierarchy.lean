/-
  FormalRV.Framework.FactoryHierarchy — the user-directed
  abstraction split between *atomic* magic-state factories
  and *implementer-specified* CCZ constructions.

  ## Per John's 2026-05-25 directive

  > "For factory, I think we can set T-factory, such as
  >  Cultivation, a black block that takes some time and
  >  space.  But if we use 8T-CCZ, then user actually need
  >  to specify how they want to implement it.  The only
  >  atomic black box is T-distillation/Cultivation."

  Hence two factory specs:

    1. **Atomic factories** (`AtomicFactorySpec`).  T-state
       distillation, CCZ cultivation, magic-state factories
       whose internal distillation circuit we do NOT
       formalise.  They consume time + space; their output
       is requested via a single `RequestMagicState` SysCall.

    2. **8T-to-CCZ composition** (`EightTToCCZSpec`).  When
       the implementer chooses to BUILD a CCZ state from 8
       T states + Clifford glue (NOT cultivation), they
       must submit:
       (a) The T-factory zone id (an atomic factory).
       (b) The CCZ output zone id.
       (c) The 8 T-request SysCalls within the CCZ window.
       (d) (Future) The Clifford-glue circuit.

  The framework verifies that the composition is *structurally
  honest* — at minimum, the 8 T-state requests exist within
  the CCZ's production window.  Semantic correctness (the
  Clifford circuit actually produces |CCZ⟩) is a deeper
  verification we don't claim here.

  No Mathlib.  Pure Bool / Nat / List.  Decidable.
-/

import FormalRV.System.Architecture

namespace FormalRV.Framework.Factory

open FormalRV.Framework.Architecture

/-! ## What kind of magic state does a factory produce? -/

/-- The two kinds of magic state the framework distinguishes:
    T (the universal atomic resource) and CCZ (which CAN
    be produced atomically by cultivation OR composed from
    8 T states). -/
inductive MagicStateKind
  | T
  | CCZ
  deriving DecidableEq, Repr

instance : Inhabited MagicStateKind := ⟨.T⟩

/-! ## Atomic factory specification

    The level below which we do NOT formalise.  The
    implementer DECLARES the factory's parameters; the
    framework treats it as a black box that consumes its
    declared atom budget and produces one output per
    declared period. -/

/-- One atomic factory — either T or CCZ cultivation.  Internal
    distillation circuit is NOT specified; the framework
    accepts its outputs on trust.  The implementer DECLARES
    these parameters — the framework cannot derive them
    without modelling the underlying distillation circuit
    (which is out of scope per the "atomic black box" rule). -/
structure AtomicFactorySpec where
  /-- Physical zone id. -/
  zone_id                  : Nat
  /-- T or CCZ. -/
  kind                     : MagicStateKind
  /-- Physical-atom budget. -/
  factory_atoms            : Nat
  /-- Steady-state period: one output every this many µs after
      the pipeline is full. -/
  time_per_state_us        : Nat
  /-- Pipeline depth: time from factory start to FIRST output.
      Distinct from steady-state period.  For cultivation
      (single-shot), this equals `time_per_state_us`.  For
      distillation pipelines this is larger. -/
  startup_latency_us       : Nat
  /-- Per-attempt success probability of a distillation cycle,
      in parts per million.  1_000_000 = deterministic;
      950_000 = 95% success (Bravyi-Kitaev 15-to-1 nominal). -/
  success_probability_ppm  : Nat
  /-- Output state fidelity, in parts per million (`1 - error`). -/
  output_fidelity_x1e6     : Nat
  deriving Repr, Inhabited

namespace AtomicFactorySpec

/-- Maximum number of outputs over a window of `window_us`
    microseconds, assuming DETERMINISTIC output and pipeline
    already full.  Used by I4 throughput checking as the
    upper bound on supply. -/
def max_outputs_in_window (f : AtomicFactorySpec) (window_us : Nat) : Nat :=
  window_us / f.time_per_state_us

/-- Expected number of outputs over a window, accounting for
    success probability.  Approximates
    `(window_us / time_per_state_us) × success_prob`.
    Encoded in ppm units to stay in Nat:

      expected_outputs = (window_us / time_per_state_us) × success_probability_ppm
                        / 1_000_000.

    For deterministic factories (`success_probability_ppm = 1_000_000`)
    this equals `max_outputs_in_window`. -/
def expected_outputs_in_window
    (f : AtomicFactorySpec) (window_us : Nat) : Nat :=
  (window_us / f.time_per_state_us) * f.success_probability_ppm / 1_000_000

/-- Throughput in outputs per millisecond × 1000 (fixed point
    integer for Nat).

      throughput_x1000 = 1_000_000_000 × success_probability_ppm
                       / (time_per_state_us × 1_000_000)
                       = 1000 × success_probability_ppm / time_per_state_us. -/
def throughput_per_ms_x1000 (f : AtomicFactorySpec) : Nat :=
  if f.time_per_state_us = 0 then 0
  else 1000 * f.success_probability_ppm / 1_000_000 / f.time_per_state_us

/-- The total latency to deliver `n` outputs.
    `total = startup_latency + (n - 1) × time_per_state`
    (pipeline depth for the first, then steady state). -/
def total_latency_for_n_outputs (f : AtomicFactorySpec) (n : Nat) : Nat :=
  if n = 0 then 0
  else f.startup_latency_us + (n - 1) * f.time_per_state_us

end AtomicFactorySpec

/-! ## 8-T-to-CCZ composition specification

    When the implementer's CCZ output zone is NOT an atomic
    cultivation factory but is composed from 8 T states
    + Clifford glue, they submit `EightTToCCZSpec`. -/

/-- The implementer's declaration of an 8T-to-CCZ build. -/
structure EightTToCCZSpec where
  /-- The composite CCZ zone the SCHEDULE's
      `RequestMagicState` targets. -/
  ccz_output_zone   : Nat
  /-- The atomic T-factory zone we draw the 8 Ts from. -/
  t_factory_zone    : Nat
  /-- Begin time (µs) of the CCZ production window. -/
  build_begin_us    : Nat
  /-- End time (µs) — when the CCZ output is ready. -/
  build_end_us      : Nat
  deriving Repr, Inhabited

namespace EightTToCCZSpec

/-- Count `RequestMagicState` SysCalls targeting `t_factory_zone`
    whose entire `[begin_us, end_us)` lies within the build
    window. -/
def t_requests_in_window (spec : EightTToCCZSpec) (sched : List SysCall) : Nat :=
  (sched.filter (fun sc =>
    match sc.kind with
    | .RequestMagicState zid =>
        decide (zid = spec.t_factory_zone)
        && decide (spec.build_begin_us ≤ sc.begin_us)
        && decide (sc.end_us ≤ spec.build_end_us)
    | _ => false)).length

/-- **Check 1.**  Exactly 8 (or more — the implementer is
    free to over-request, e.g. for distillation post-
    selection) T-state requests target the T-factory zone
    inside the build window. -/
def has_eight_t_requests (spec : EightTToCCZSpec) (sched : List SysCall) : Bool :=
  decide (spec.t_requests_in_window sched ≥ 8)

/-- **Check 2.**  The build window is non-trivial
    (begin < end). -/
def window_well_formed (spec : EightTToCCZSpec) : Bool :=
  decide (spec.build_begin_us < spec.build_end_us)

/-- **Check 3.**  There is exactly one downstream
    `RequestMagicState` to `ccz_output_zone` whose begin
    time equals `build_end_us` (the CCZ becomes available
    at the build's end). -/
def downstream_ccz_request
    (spec : EightTToCCZSpec) (sched : List SysCall) : Bool :=
  sched.any (fun sc =>
    match sc.kind with
    | .RequestMagicState zid =>
        decide (zid = spec.ccz_output_zone)
        && decide (sc.begin_us ≥ spec.build_end_us)
    | _ => false)

/-- Headline: the 8T-to-CCZ build is honestly structural. -/
def verifies (spec : EightTToCCZSpec) (sched : List SysCall) : Bool :=
  has_eight_t_requests spec sched
  && window_well_formed spec
  && downstream_ccz_request spec sched

end EightTToCCZSpec

/-! ## Two-tier factory abstraction

    A `MagicFactory` is either an atomic spec or a
    composite 8T-to-CCZ.  The framework treats the two
    uniformly when checking the schedule's magic-state
    interface. -/

inductive MagicFactory
  | atomic   (spec : AtomicFactorySpec)
  | composite (spec : EightTToCCZSpec)
  deriving Repr, Inhabited

namespace MagicFactory

/-- The zone id `RequestMagicState` SysCalls target. -/
def output_zone : MagicFactory → Nat
  | .atomic    s => s.zone_id
  | .composite s => s.ccz_output_zone

/-- Atomic factories are accepted by structure (no internals
    to check); composite factories must pass
    `EightTToCCZSpec.verifies`. -/
def verifies (f : MagicFactory) (sched : List SysCall) : Bool :=
  match f with
  | .atomic    _ => true
  | .composite s => s.verifies sched

end MagicFactory

/-! ## Worked example: cuccaro N=1 with explicit factory choice

    Two illustrative configurations:

    * `cuccaro_n1_cultivation_factory` — atomic CCZ
      cultivation (qianxu's choice in the paper).
    * `cuccaro_n1_eight_t_factory` — 8T-to-CCZ composed
      from an atomic T-factory.

    Each `RequestMagicState` SysCall in cuccaro N=1's
    schedule corresponds to one CCZ output.  The
    cultivation variant passes trivially; the composite
    variant requires the implementer to ALSO submit 8
    T-requests per CCZ for the verifier to accept it. -/

def cuccaro_n1_cultivation_factory : MagicFactory :=
  .atomic
    { zone_id                 := 2
      kind                    := .CCZ
      factory_atoms           := 200    -- per qianxu demo
      time_per_state_us       := 10_000
      startup_latency_us      := 10_000 -- cultivation: pipeline = period
      success_probability_ppm := 1_000_000  -- cultivation ≈ deterministic
      output_fidelity_x1e6    := 999_000 }

/-- An illustrative 8T-to-CCZ spec for gate-3's CCZ (request
    at t=0, delivery at t=12_000, drawn from T-factory at
    zone 9).  Just the spec — the schedule we'd need to
    submit to verify it must contain 8 T-requests inside
    [0, 12_000). -/
def cuccaro_n1_gate3_eight_t : EightTToCCZSpec :=
  { ccz_output_zone := 2
    t_factory_zone  := 9
    build_begin_us  := 0
    build_end_us    := 12_000 }

end FormalRV.Framework.Factory
