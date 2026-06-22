/-
  FormalRV.Framework.GE2021PPMSysInv — a SMALL, CONCRETE
  PPM-block SysCall schedule whose resource numbers are
  DERIVED FROM the actual list of SysCalls (not typed in).

  ## Motivation — closing the spreadsheet gap

  `Corpus/GidneyEkera2021FullStackE2E.lean`'s
  `per_shot_runtime_us` is a TYPED-IN `Nat` field on
  `GE2021Submission`; its "verified" wallclock theorem
  `ge2021_per_shot_wallclock` reduces to the identity function
  applied to that typed-in value:

      per_shot_wallclock_us := sub.per_shot_runtime_us         -- identity
      ge2021_per_shot_wallclock :=
        (compute_resources concrete_submission).per_shot_wallclock_us
          = 18_360_000_000                                     -- = the typed-in Nat

  This file is the smallest reusable counter-example: a
  16-SysCall PPM block where the wallclock and peak physical
  qubits are COMPUTED from the actual SysCall list (foldl over
  end_us, per-cycle active-atom count), and the four
  system-level invariants (I1 capacity + I2 exclusivity + I3
  feedback latency + I3 decoder reaction + I4 factory
  throughput) are decide-closed on that list.

  ## What the PPM block represents

  One joint Pauli-product measurement M_{ZZ} between two
  logical qubits L0 (data qubit 0) and L1 (data qubit 50), via
  an ancilla qubit (atom 100), over τ_s = 3 syndrome-extraction
  rounds (minimum to verify the joint stabilizer's outcome bit
  via majority vote), plus one PauliFrameUpdate.

  Per round (5 SysCalls):
    1. RequestFreshAncilla — allocate the joint-measurement ancilla
    2. Gate2q 0  → 100   — controlled by L0's data qubit
    3. Gate2q 50 → 100   — controlled by L1's data qubit
    4. Measure 100       — read out the joint stabilizer
    5. DecodeSyndrome r  — classical reaction per round

  After 3 rounds:
    16. PauliFrameUpdate 0 — apply correction based on the
                              majority-vote XOR of the 3 outcomes

  Total: 16 SysCalls; wallclock = 16 µs; peak active qubits = 2
  per cycle (a single Gate2q claims two atoms simultaneously).

  ## Anti-spreadsheet property

  Compare verbatim:

  GE2021FullStackE2E.lean:
      per_shot_wallclock_us := sub.per_shot_runtime_us   -- IDENTITY
      theorem ge2021_per_shot_wallclock :
        compute_resources.per_shot_wallclock_us = 18_360_000_000 := by decide
      -- ↑ proves: the typed-in Nat equals itself.

  This file:
      def ppm_block_wallclock_us :=
        ppm_block_syscalls.foldl (fun acc sc => Nat.max acc sc.end_us) 0
      theorem ppm_block_wallclock_is_derived :
        ppm_block_wallclock_us =
          ppm_block_syscalls.foldl (fun acc sc => Nat.max acc sc.end_us) 0 := rfl
      -- ↑ proves: the wallclock is the foldl, not a typed-in value.

  No Mathlib.  Pure Bool / Nat / List.  Decidable.
-/

import FormalRV.System.Core.Architecture
import FormalRV.System.Invariants.ScheduleInvariantsExplicit
import FormalRV.System.Core.CodedLayout   -- for `syscall_acts_on`
import FormalRV.Resource.SysCallCount

namespace FormalRV.Framework.GE2021PPMSysInv

open FormalRV.Framework
open FormalRV.System.Architecture
open FormalRV.System.ScheduleInv

/-! ## §1. Minimal architecture (Data + Ancilla zones)

    Two contiguous zones covering 200 physical qubits.  Cycle
    time 1 µs matches GE2021 parameters; v_max = 0 reflects
    superconducting transmons with SWAP-based routing (no
    physical motion of qubits). -/

def ge2021_ppm_arch : ZonedArch :=
  { zones :=
      [ { name := "Data",    site_lo := 0,   site_hi := 100 }
      , { name := "Ancilla", site_lo := 100, site_hi := 200 } ]
    total_sites := 200
    t_cycle_us  := 1
    v_max_um_per_us := 0
    t_react_us := 10
  }

theorem ge2021_ppm_arch_zone_count :
    ge2021_ppm_arch.zones.length = 2 := by decide

theorem ge2021_ppm_arch_total :
    ge2021_ppm_arch.total_sites = 200 := by decide

/-! ## §2. One PPM round (5 SysCalls, 5 µs long) -/

/-- One round of the joint M_{ZZ} measurement.  Five SysCalls
    starting at `start_us`, ending at `start_us + 5`. -/
def ppm_round (start_us : Nat) (decoder_id : Nat) : List SysCall :=
  [ { kind     := SysCallKind.RequestFreshAncilla 100
      begin_us := start_us
      end_us   := start_us + 1 }
  , { kind     := SysCallKind.Gate2q 0 100 0
      begin_us := start_us + 1
      end_us   := start_us + 2 }
  , { kind     := SysCallKind.Gate2q 50 100 0
      begin_us := start_us + 2
      end_us   := start_us + 3 }
  , { kind     := SysCallKind.Measure 100 0
      begin_us := start_us + 3
      end_us   := start_us + 4 }
  , { kind     := SysCallKind.DecodeSyndrome decoder_id
      begin_us := start_us + 4
      end_us   := start_us + 5 } ]

theorem ppm_round_count (s d : Nat) : (ppm_round s d).length = 5 := by rfl

/-! ## §3. The full PPM block: 3 rounds + 1 correction (16 SysCalls) -/

/-- The complete PPM block.  Three rounds of the joint
    measurement at t = 0, 5, 10, then a PauliFrameUpdate at
    t = 15. -/
def ppm_block_syscalls : List SysCall :=
  ppm_round 0 0
  ++ ppm_round 5 1
  ++ ppm_round 10 2
  ++ [ { kind     := SysCallKind.PauliFrameUpdate 0
         begin_us := 15
         end_us   := 16 } ]

theorem ppm_block_syscall_count :
    ppm_block_syscalls.length = 16 := by rfl

/-! ## §4. DERIVED metrics (foldl/aggregation over the actual list) -/

/-- Wallclock = max end_us across all SysCalls.  This is the
    KEY anti-spreadsheet definition: nothing typed in, no field
    on a struct — just the fold. -/
def ppm_block_wallclock_us : Nat :=
  ppm_block_syscalls.foldl (fun acc sc => Nat.max acc sc.end_us) 0

/-- Peak simultaneously-active physical qubits.  For each
    distinct begin time `t` in the schedule, count atoms
    claimed by syscalls active at that instant; take the max
    across all such `t`s.

    This is the per-instant load that `capacity_per_cycle_ok`
    bounds against the per-zone capacities. -/
def ppm_block_peak_physical_qubits : Nat :=
  let active_at (t : Nat) : List Nat :=
    (ppm_block_syscalls.filter (fun sc =>
      decide (sc.begin_us ≤ t) && decide (t < sc.end_us))).flatMap syscall_acts_on
  let begin_times := ppm_block_syscalls.map (·.begin_us)
  begin_times.foldl (fun acc t => Nat.max acc (active_at t).length) 0

/-- Total distinct physical qubits TOUCHED by the schedule.
    Sums up the qubits referenced anywhere in any SysCall. -/
def ppm_block_total_distinct_qubits : Nat :=
  ((ppm_block_syscalls.flatMap syscall_acts_on).foldl
    (fun acc q => if acc.contains q then acc else q :: acc)
    ([] : List Nat)).length

/-! ## §5. Anti-spreadsheet property (wallclock IS the foldl) -/

/-- **The key anti-spreadsheet theorem.**  Demonstrates the
    wallclock is computed from the SysCall stream, not copied
    from a submitted Nat field. -/
theorem ppm_block_wallclock_is_derived :
    ppm_block_wallclock_us =
      ppm_block_syscalls.foldl (fun acc sc => Nat.max acc sc.end_us) 0 :=
  rfl

/-! ## §6. Concrete derived values (proven by decide) -/

theorem ppm_block_wallclock_value :
    ppm_block_wallclock_us = 16 := by decide

theorem ppm_block_peak_physical_qubits_value :
    ppm_block_peak_physical_qubits = 2 := by decide
  -- Each Gate2q claims {data, ancilla} = 2 atoms simultaneously.
  -- All other SysCalls (RequestFreshAncilla, Measure, DecodeSyndrome,
  -- PauliFrameUpdate) claim 1 atom or 0.

theorem ppm_block_total_distinct_qubits_value :
    ppm_block_total_distinct_qubits = 3 := by decide
  -- Distinct atoms touched: {0, 50, 100} = 3.

/-! ## §7. System-level invariants (each closed by `decide`) -/

theorem ppm_block_capacity_in_arch_ok :
    capacity_in_arch_ok ge2021_ppm_arch ppm_block_syscalls = true := by decide

theorem ppm_block_capacity_per_cycle_ok :
    capacity_per_cycle_ok ge2021_ppm_arch ppm_block_syscalls = true := by decide

theorem ppm_block_exclusivity_ok :
    exclusivity_ok ppm_block_syscalls = true := by decide

theorem ppm_block_feedback_latency_ok :
    feedback_latency_ok ge2021_ppm_arch.t_cycle_us ppm_block_syscalls = true := by decide
  -- The single PauliFrameUpdate is 1 µs ≤ t_cycle_us = 1.

theorem ppm_block_speed_limit_ok :
    speed_limit_ok ge2021_ppm_arch.v_max_um_per_us (fun _ => 0)
      ppm_block_syscalls = true := by decide
  -- No TransitQubit syscalls; vacuously satisfied.

theorem ppm_block_window_throughput_ok :
    window_throughput_ok ppm_block_syscalls 1000 1000 = true := by decide
  -- No RequestMagicState in this block; vacuous.

/-- The patched decoder-reaction check (added to
    `ScheduleInvariantsExplicit.lean`): every `DecodeSyndrome`
    completes within `t_react_us` µs. -/
theorem ppm_block_decoder_react_ok :
    decoder_react_ok 10 ppm_block_syscalls = true := by decide
  -- Each DecodeSyndrome lasts 1 µs ≤ 10 µs reaction budget.

/-! ## §8. Headline: ALL four invariants hold simultaneously -/

/-- The headline structural-correctness theorem: the
    16-SysCall PPM block satisfies every system-level
    invariant on the GE2021-style architecture. -/
theorem ppm_block_all_invariants_ok :
    all_invariants_ok ge2021_ppm_arch ppm_block_syscalls 1000 1000 (fun _ => 0) = true := by
  decide

/-! ## §9. Bookkeeping: explicit syscall-kind counts — aliases for THE
       canonical counters (`Resource/SysCallCount`); resource claims
       never redefine their own walks. -/

abbrev count_request_fresh_ancilla : List SysCall → Nat :=
  FormalRV.Resource.SysCallCount.countFreshAnc

abbrev count_gate2q : List SysCall → Nat :=
  FormalRV.Resource.SysCallCount.countGate2q

abbrev count_measure : List SysCall → Nat :=
  FormalRV.Resource.SysCallCount.countMeasure

abbrev count_decode_syndrome : List SysCall → Nat :=
  FormalRV.Resource.SysCallCount.countDecode

abbrev count_pauli_frame_update : List SysCall → Nat :=
  FormalRV.Resource.SysCallCount.countFeedback

/-- Three rounds × 1 RequestFreshAncilla each = 3. -/
theorem ppm_block_count_request_fresh_ancilla :
    count_request_fresh_ancilla ppm_block_syscalls = 3 := by decide

/-- Three rounds × 2 Gate2q each = 6. -/
theorem ppm_block_count_gate2q :
    count_gate2q ppm_block_syscalls = 6 := by decide

/-- Three rounds × 1 Measure each = 3. -/
theorem ppm_block_count_measure :
    count_measure ppm_block_syscalls = 3 := by decide

/-- Three rounds × 1 DecodeSyndrome each = 3. -/
theorem ppm_block_count_decode_syndrome :
    count_decode_syndrome ppm_block_syscalls = 3 := by decide

/-- One PauliFrameUpdate at the end of the block. -/
theorem ppm_block_count_pauli_frame_update :
    count_pauli_frame_update ppm_block_syscalls = 1 := by decide

/-! ## §10. What this delivers

  A 16-SysCall PPM block on the GE2021-style architecture with:

    * Wallclock = 16 µs       DERIVED from `foldl Nat.max sc.end_us`,
                              NOT typed in.
    * Peak active qubits = 2  DERIVED from per-cycle active-atom
                              count, NOT typed in.
    * Distinct qubits = 3     DERIVED from `flatMap syscall_acts_on`,
                              NOT typed in.
    * All four system invariants (I1 + I2 + I3 + I4 + decoder
      reaction) `decide`-closed on the actual SysCall list.

  Contrast with `GE2021FullStackE2E.lean`:
    * `per_shot_runtime_us := 18_360_000_000` — typed in.
    * `per_shot_wallclock_us := sub.per_shot_runtime_us` — identity.
    * `ge2021_per_shot_wallclock = 18_360_000_000` — value equals
                                                    typed-in value.
    * No SysCall list, no syndrome extraction, no I1–I4 on a
      concrete schedule.

  ## How this scales

  The same `ppm_round` template lifts to any number of rounds
  by `ppm_round t d` over a list of `(t, d)` start/decoder pairs.
  An N-PPM block would have `5N + 1` SysCalls with wallclock
  `5N + 1` µs.  To extend to the full Gidney–Ekerå pipeline
  (~3.6 × 10¹⁰ PPMs), the construction is mechanical — but
  `decide` will not close at that scale; structural induction
  on `ppm_round` would be required.

  This file delivers the smallest reusable structural bridge:
  a concrete SysCall-stream PPM block with derived wallclock and
  decide-closed invariants.  Future work extends it to the
  full pipeline.
-/

end FormalRV.Framework.GE2021PPMSysInv
