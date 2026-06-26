/-
  FormalRV.System.Examples.SystemInvariantExamples — five worked device programs checked against
  the system-level invariants (I1 capacity, I2 exclusivity, I3 latency/speed + decoder-reaction,
  I4 factory throughput), TWO that PASS and THREE that FAIL.

  Every pass/fail verdict is a `native_decide` theorem, regression-checked by the umbrella
  `lake build` (imported by `FormalRV/System.lean`).  The matching emitted `DEVICE-PROGRAM` text
  is printed by the standalone demo `FormalRV/Codegen/SysCallEmitDemo.lean`.

  Workflow: build a `Schedule` (physical ops + system calls) → CHECK with
  `ScheduleInv.all_invariants_ok` → emit.  `ZonedArch` carries `t_react_us`, so the headline
  `all_invariants_ok` enforces ALL of I3 (feedback + speed + decoder reaction).
-/
import FormalRV.System.Invariants.ScheduleInvariantsExplicit
import FormalRV.System.Params.RSA2048

set_option maxRecDepth 8000

namespace FormalRV.System.SystemInvariantExamples

open FormalRV.System.ScheduleInv
open FormalRV.System.Architecture

/-- A tiny architecture: a Data zone `[0,100)`, an Ancilla zone `[100,200)`, and a Factory zone
    `[200,300)`; 1 µs stabilizer cycle, no transit (`v_max = 0`), 10 µs decoder reaction budget. -/
def demoArch : ZonedArch :=
  { zones :=
      [ { name := "Data",    site_lo := 0,   site_hi := 100 },
        { name := "Ancilla", site_lo := 100, site_hi := 200 },
        { name := "Factory", site_lo := 200, site_hi := 300 } ]
    total_sites := 300
    t_cycle_us  := 1
    v_max_um_per_us := 0
    t_react_us  := 10 }

/-- Factory window: the CCZ factory makes ≤ 1 magic state per window (the canonical
    `RSA2048.cczWindowUs` = 12 000 µs, Cain–Xu 2026 App. C). -/
def winUs : Nat := FormalRV.System.RSA2048.cczWindowUs
def maxPerWin : Nat := 1
def noDist : Nat → Nat := fun _ => 0

/-- One PPM measurement (request ancilla → joint gate → measure → decode), parametric in start
    time, data qubit, ancilla qubit, decoder id.  The decode takes 1 µs (≤ the 10 µs budget). -/
def ppm (start data anc dec : Nat) : List SysCall :=
  [ { kind := SysCallKind.RequestFreshAncilla anc, begin_us := start,     end_us := start + 1 },
    { kind := SysCallKind.Gate2q data anc 0,     begin_us := start + 1, end_us := start + 2 },
    { kind := SysCallKind.Measure anc 0,         begin_us := start + 2, end_us := start + 3 },
    { kind := SysCallKind.DecodeSyndrome dec,    begin_us := start + 3, end_us := start + 4 } ]

/-! ## PASS ① — sequential PPM pair (time-disjoint, reuses one ancilla). -/

def passSequential : List SysCall := ppm 0 0 100 0 ++ ppm 10 50 100 1

theorem passSequential_ok : all_invariants_ok demoArch passSequential winUs maxPerWin noDist = true := by
  decide

/-! ## PASS ② — parallel PPM pair on DISTINCT ancillas (concurrent, disjoint atoms). -/

def passParallelDistinct : List SysCall := ppm 0 0 100 0 ++ ppm 0 1 101 1

theorem passParallelDistinct_ok :
    all_invariants_ok demoArch passParallelDistinct winUs maxPerWin noDist = true := by decide

/-- Pins the interval arithmetic only: `[1,2)` overlaps itself.  The statement does NOT
    reference the schedule — both PPMs' joint gates occupy `[1,2)` by construction of
    `passParallelDistinct` (`ppm start …` places the `Gate2q` in `[start+1, start+2)` and
    both PPMs start at 0), so this is the overlap fact that construction instantiates. -/
theorem passParallelDistinct_overlaps : intervals_overlap 1 2 1 2 = true := by decide

/-! ## FAIL ① — parallel PPM pair ALIASING one ancilla (violates I2 exclusivity). -/

def failAlias : List SysCall := ppm 0 0 100 0 ++ ppm 0 1 100 1

theorem failAlias_fails : all_invariants_ok demoArch failAlias winUs maxPerWin noDist = false := by
  decide
theorem failAlias_exclusivity_false : exclusivity_ok failAlias = false := by decide
theorem failAlias_capacity_true : capacity_in_arch_ok demoArch failAlias = true := by decide

/-! ## FAIL ② — two magic requests in one factory window (violates I4 throughput). -/

def failThroughput : List SysCall :=
  [ { kind := SysCallKind.RequestMagicState 200, begin_us := 0,   end_us := 12000 },
    { kind := SysCallKind.RequestMagicState 200, begin_us := 100, end_us := 12100 } ]

theorem failThroughput_fails :
    all_invariants_ok demoArch failThroughput winUs maxPerWin noDist = false := by decide
theorem failThroughput_window_false : window_throughput_ok failThroughput winUs maxPerWin = false := by
  decide
theorem failThroughput_others_true :
    (capacity_in_arch_ok demoArch failThroughput && exclusivity_ok failThroughput) = true := by
  decide

/-! ## FAIL ③ — a decode slower than the reaction budget (violates I3 decoder-reaction).

    `ZonedArch` carries `t_react_us` and `all_invariants_ok` folds in `decoder_react_ok`, so the
    HEADLINE bundle catches this directly. -/

def failDecodeSlow : List SysCall :=
  [ { kind := SysCallKind.Gate2q 0 100 0,   begin_us := 0, end_us := 1 },
    { kind := SysCallKind.Measure 100 0,    begin_us := 1, end_us := 2 },
    { kind := SysCallKind.DecodeSyndrome 0, begin_us := 2, end_us := 22 } ]   -- 20 µs > 10 µs budget

/-- The headline bundle REJECTS the too-slow decode (decoder reaction is enforced). -/
theorem failDecodeSlow_fails :
    all_invariants_ok demoArch failDecodeSlow winUs maxPerWin noDist = false := by decide
/-- The specific failing component is I3 decoder-reaction; I1/I2/I4 still hold. -/
theorem failDecodeSlow_decoder_react_false :
    decoder_react_ok demoArch.t_react_us failDecodeSlow = false := by decide
theorem failDecodeSlow_others_true :
    (capacity_in_arch_ok demoArch failDecodeSlow && exclusivity_ok failDecodeSlow
      && window_throughput_ok failDecodeSlow winUs maxPerWin) = true := by decide

end FormalRV.System.SystemInvariantExamples
