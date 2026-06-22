/-
  FormalRV.System.ScheduleAdvance — beating the naive baseline (an advanced scheduler), the WALL it
  hits, and applying the framework to OTHER papers.

  ## Advanced scheduler: parallel magic-state factories

  The naive baseline (`Audit/GidneyEkera2021/Verifier`, Part B: `naiveWallclockHours`) is fully
  serial — one factory, ~8782 hours.  The first
  real optimization is to run `F` factories IN PARALLEL (disjoint footprints): the magic supply
  drops to `⌈K/F⌉ · production_us` (`MagicScheduleComplete.magicSupplyTimeUs`).  We show:

    * a concrete 2-factory schedule is VALID and produces 2 magic states in ONE production window
      instead of two (real parallelism, proven conflict-free);
    * at `F = 1093` factories the magic supply is `≤ 8 hours` — MATCHING the paper, a ~1098×
      speedup over the naive 8782 hours.

  ## The WALL

  Parallelizing factories cannot go below the **spacetime floor** (`ScheduleLowerBound`,
  `Q·T ≥ K·fq·prod`): more factories cost more qubits, and the paper already sits ~7× above the
  floor.  Beyond matching the magic supply to the LOGICAL DEPTH, further speedup requires
  parallelizing the data-dependent logical operations themselves (the accumulator chain) — which
  needs the circuit's detailed dependency structure (the time-optimal scheme).  That is the wall:
  the magic-supply optimization is exhausted once `F` meets the depth; the rest is detailed circuit
  scheduling.

  ## Other papers

  The lower bound and baseline are PARAMETRIC, so they instantiate per paper.  We instantiate the
  floor for Babbush-2026 ECC-256 (`90 000 000` Toffolis) as a demonstration.
-/
import FormalRV.System.Magic.MagicStateReadiness
import FormalRV.System.Bounds.ScheduleLowerBound
import FormalRV.System.DeviceLane.DeviceSchedule
import FormalRV.System.Params.RSA2048

namespace FormalRV.System.ScheduleAdvance

open FormalRV.System.DeviceSchedule
open FormalRV.System.MagicStateReadiness
open FormalRV.System.Architecture

/-! ## §1. Advanced scheduler: parallel factories beat the serial baseline. -/

/-- **A 2-factory parallel schedule is valid and genuinely parallel.**  Two `prepMagic` ops run in
    the SAME window `[0,2)` on DISJOINT footprints (factories A=`{100,101}`, B=`{102,103}`), so the
    schedule is conflict-free — two magic states produced in ONE production window, not two. -/
def parallelTwoFactories : DSchedule :=
  [ { id := 1, kind := OpKind.prepMagic, footprint := [100, 101], begin_t := 0, dur_t := 2, deps := [] },
    { id := 2, kind := OpKind.prepMagic, footprint := [102, 103], begin_t := 0, dur_t := 2, deps := [] } ]

def parDev : Device :=
  { totalResources := 1000, nDecoders := 1, reactionTime := 2, codeCycleUs := 1, d := 27 }

theorem parallelTwoFactories_valid : scheduleValid parDev parallelTwoFactories = true := by native_decide

/-- Both factories overlap in time (genuine parallelism) yet do not conflict. -/
theorem parallelTwoFactories_parallel :
    opsTimeOverlap parallelTwoFactories[0]! parallelTwoFactories[1]! = true
    ∧ conflictFree parallelTwoFactories = true := by native_decide

/-- **★ Parallel factories hit the paper's runtime ★** — with `F = 1093` CCZ factories, the magic
    supply for the windowed RSA-2048 budget is `≤ 8 hours` (`28 795 884 000 µs`), versus the naive
    serial `8782` hours — a ~1098× speedup that MATCHES the paper. -/
theorem parallel_1093_within_8h :
    magicSupplyTimeUs 2622824448 1093 ccz_spec_qianxu ≤ 8 * 3600000000
    ∧ 7 * 3600000000 ≤ magicSupplyTimeUs 2622824448 1093 ccz_spec_qianxu := by
  refine ⟨by native_decide, by native_decide⟩

/-- Speedup over the naive serial baseline (F = 1): the 1093-factory supply is `> 1000×` faster. -/
theorem parallel_speedup :
    1000 * magicSupplyTimeUs 2622824448 1093 ccz_spec_qianxu
      ≤ magicSupplyTimeUs 2622824448 1 ccz_spec_qianxu := by native_decide

/-! ## §2. The WALL: cannot beat the spacetime floor. -/

/-- **The wall, checked at the 1093-factory point.**  This is ONE NUMERIC INSTANCE, not a
    universal statement: it verifies that the 1093-factory configuration's spacetime
    ((data + factory qubits) × supply time) stays at or above the RSA-2048 magic-state floor.
    The universal impossibility — NO schedule beats `Q·T ≥ K·fq·prod` — is
    `ScheduleLowerBound.magic_spacetime_floor`.  The paper already sits ~7× above that floor; the
    remaining speedup is not a magic-supply problem but a LOGICAL-DEPTH problem (parallelizing the
    data-dependent operations), which needs the circuit's detailed dependency structure. -/
theorem parallel_supply_above_floor :
    -- the 1093-factory magic supply, as qubit·µs over the data+factory device, is ≥ the floor
    ScheduleLowerBound.rsa2048_floor_qubit_us
      ≤ (9633792 + 1093 * 2565) * magicSupplyTimeUs 2622824448 1093 ccz_spec_qianxu := by
  native_decide

/-! ## §3. Other papers: the framework is parametric. -/

/-- **Babbush-2026 ECC-256 magic-state floor.**  The lower bound `magic_spacetime_floor` is
    parametric, so it instantiates per paper.  For Babbush ECC-256's `90 000 000` Toffolis (with a
    CCZ-style factory: `2565` qubits, `12000 µs`), the spacetime floor is `≈ 769 500` qubit-hours —
    a hard limit for that computation too.  (The concrete factory spec should be the paper's own;
    here we use the cited qianxu CCZ factory as a stand-in to show the framework generalizes.) -/
def babbush_ecc256_floor_qubit_hours : Nat :=
  (90000000 * (RSA2048.cczFactoryQubits * RSA2048.cczWindowUs)) / 3600000000

theorem babbush_ecc256_floor_value : babbush_ecc256_floor_qubit_hours = 769500 := by native_decide

/-- The naive serial baseline applies to ANY Toffoli count `K`: runtime `= K · 12054 µs`
    (12 000 µs CCZ window + 27 µs teleport + 27 µs decode at d=27; derived as
    `Audit/GidneyEkera2021/Verifier.perToffoliUs`).  For
    Babbush ECC-256 (`K = 90 000 000`) that is `≈ 301` hours serially — which the paper's parallel
    construction (500 000 qubits, ~20 min) beats by exploiting parallelism, exactly as for RSA. -/
def naiveSerialHours (K : Nat) : Nat := K * 12054 / 3600000000

theorem babbush_ecc256_naive_hours : naiveSerialHours 90000000 = 301 := by native_decide

end FormalRV.System.ScheduleAdvance
