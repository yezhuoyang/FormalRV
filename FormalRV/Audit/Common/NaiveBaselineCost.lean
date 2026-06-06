/-
  FormalRV.Audit.Common.NaiveBaselineCost — concrete running-time and qubit numbers for the verified
  NAIVE (fully-serial) RSA-2048 device schedule, and the gap to the Gidney–Ekerå paper.

  The naive schedule (`NaiveSchedule.rsa2048_naive_schedule_valid`, proven valid for all of it) does
  one operation at a time: per Toffoli, PRODUCE a magic state, TELEPORT it in, DECODE — with a
  SINGLE factory and NO parallelism.  So:

    * per-Toffoli wall-time = CCZ production (`ccz_spec_qianxu.production_us = 12000 µs`) + a
      teleport surgery (`d = 27` cycles ≈ 27 µs) + a decode (≈ `d` cycles ≈ 27 µs) = 12054 µs;
    * runtime  = (Toffoli count `2 622 824 448`) × 12054 µs ≈ 8782 hours ≈ 366 days;
    * qubits   = data (`9 633 792`) + ONE factory (`2565`) ≈ 9 636 357.

  Gap to the paper (`PaperClaims`: 20 000 000 qubits, 8 hours):
    * TIME   — ≈ 1098× SLOWER (≈ the 1093 magic-state factories the paper runs in parallel that the
               naive baseline forgoes; serial magic production is the whole gap);
    * QUBITS — ≈ 0.48× (the naive baseline uses LESS than half — no factory farm, minimal routing);
    * SPACETIME (qubit·hours) — ≈ 529× WORSE (the serial schedule's price for provable simplicity).

  This is the classic space-time trade-off: the naive baseline is the slow, small-footprint corner;
  the paper buys ~1100× speed with ~2× more qubits (mostly factories) — exactly the optimization
  (parallelism) that builds ON TOP of this provably-correct baseline.
-/
import FormalRV.System.NaiveSchedule
import FormalRV.System.Architecture
import FormalRV.Audit.Common.PaperClaims
import FormalRV.Audit.Common.WindowedShorPhysicalEstimate

namespace FormalRV.Audit.Common.NaiveBaselineCost

open FormalRV.Framework.Architecture
open FormalRV.PaperClaims

/-! ### Naive baseline concrete numbers. -/

/-- Verified Toffoli (= CCZ magic) count for windowed RSA-2048. -/
def toffoliCount : Nat := 2622824448

/-- Per-Toffoli serial wall-time (µs): CCZ production + teleport surgery (d=27 cycles) + decode. -/
def perToffoliUs : Nat := ccz_spec_qianxu.production_us + 27 + 27

theorem perToffoliUs_value : perToffoliUs = 12054 := by native_decide

/-- Naive serial runtime (µs), hours. -/
def naiveWallclockUs : Nat := toffoliCount * perToffoliUs
def naiveWallclockHours : Nat := naiveWallclockUs / 3600000000

theorem naiveWallclockHours_value : naiveWallclockHours = 8782 := by native_decide

/-- Naive qubits: the full data register plus ONE magic-state factory. -/
def naiveQubits : Nat :=
  FormalRV.Audit.Common.WindowedShorPhysicalEstimate.windowedPhysicalDataQubits_rsa2048
    + ccz_spec_qianxu.factory_qubits

theorem naiveQubits_value : naiveQubits = 9636357 := by native_decide

/-! ### Gap to the Gidney–Ekerå paper (20 000 000 qubits, 8 hours). -/

/-- **TIME GAP ≈ 1098×.**  The naive serial baseline takes `8782` hours; the paper reports `8`.
    The factor `1097–1098` is essentially the `1093` parallel CCZ factories the paper uses and the
    naive baseline does not — serial magic production is the entire gap. -/
theorem time_gap :
    1097 * gidney_ekera_2021_rsa2048_wallclock_hours ≤ naiveWallclockHours
    ∧ naiveWallclockHours ≤ 1098 * gidney_ekera_2021_rsa2048_wallclock_hours := by native_decide

/-- **QUBIT GAP ≈ 0.48×.**  The naive baseline uses FEWER than half the paper's qubits — it has no
    factory farm (one factory) and minimal routing; the data register dominates. -/
theorem qubit_gap :
    naiveQubits < gidney_ekera_2021_rsa2048_physical_qubits
    ∧ 2 * naiveQubits ≤ gidney_ekera_2021_rsa2048_physical_qubits := by native_decide

/-- **SPACETIME GAP ≈ 529×.**  In qubit·hours the naive baseline is ~529× worse than the paper —
    the price of a fully-serial, provably-correct schedule (all the loss is in time, from serial
    magic production). -/
theorem spacetime_gap :
    528 * (gidney_ekera_2021_rsa2048_physical_qubits * gidney_ekera_2021_rsa2048_wallclock_hours)
        ≤ naiveQubits * naiveWallclockHours
    ∧ naiveQubits * naiveWallclockHours
        ≤ 530 * (gidney_ekera_2021_rsa2048_physical_qubits * gidney_ekera_2021_rsa2048_wallclock_hours) := by
  native_decide

end FormalRV.Audit.Common.NaiveBaselineCost
