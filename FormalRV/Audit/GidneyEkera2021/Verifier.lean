/-
  Audit · gidney-ekera-2021 · VERIFIER — end-to-end obligation + anti-cheat gate
  ============================================================================
  END-TO-END (resource reproduction): GE2021's 20M qubits / 8 h is reproduced as
  a FEASIBLE CEILING — the reported footprint IS the verified surface-code area
  ceiling (19.44M ≤ 20M), and the 8 h sits 2–3× UNDER the verified
  naive-sequential time ceiling.  The capstone `gidney_ekera_2021_reproduced` is
  axiom-free (#verify_clean ACCEPTS it).  The 2–3× time gap = reaction-limited
  pipelining, claimed but not verified at full scale (GAP).

  Merged here (one flat namespace `FormalRV.Audit.GidneyEkera2021`):
    • the verified-formula resource reproduction + capstone
      (was GidneyEkera2021Reproduction);
    • the concrete naive (fully-serial) baseline numbers + the gap to the paper
      (was NaiveBaselineCost).

  ## What "reproduce" means here — and what it does NOT
  This is a RESOURCE reproduction: GE2021's OWN inputs (Toffoli count,
  logical-qubit count, the distance-27 surface tile, 1 µs cycle) plugged into the
  rfl-VERIFIED resource derivation (`estimateWith (surfaceModel …)`,
  `Framework/CostModel.lean`) and compared to the paper's headline.  The
  derivation FORMULA is verified; the gap is the part the paper achieves that the
  simple model does not capture.  It is NOT a claim of a closed whole-circuit
  semantic theorem — the delimited semantic chain is the one in the corpus.

  ## The finding
  • QUBITS: the verified surface area-ceiling = 6200 · (2·1568) = 19.44 M, within
    ~3 % of the reported 20 M (residual = the magic factory) — no unverified
    qubit-side optimization.
  • TIME: the verified naive-SEQUENTIAL ceiling = 2.7×10⁹ · 27 · 1 µs = 20.25 h;
    the reported 8 h sits 2–3× under it.  That ≈2.5× speed-up is reaction-limited
    PIPELINING of the Toffoli critical path — THE GAP, made explicit.

  No `sorry`, no new `axiom`.
-/

import FormalRV.System.Bounds.NaiveUpperBound
import FormalRV.System.Compile.SurfaceSystemCompile
import FormalRV.System.Bounds.NaiveSchedule
import FormalRV.System.Core.Architecture
import FormalRV.Framework.PaperClaims
import FormalRV.Audit.GidneyEkera2021.SystemZones
import FormalRV.Verifier

set_option maxRecDepth 8000

namespace FormalRV.Audit.GidneyEkera2021

open FormalRV.System.NaiveUpperBound
open FormalRV.System.SurfaceSystemCompile
open FormalRV.System.Architecture
open FormalRV.PaperClaims

/-============================================================================
  PART A — Verified-formula resource reproduction + capstone
           (was GidneyEkera2021Reproduction)
============================================================================-/

/-! ## The distance-27 code is a REAL verified construction, not a stub -/

/-- GE2021 runs at distance 27.  Our `surfaceCodeD 27` is an actual surface-code
    construction `[[1405, 1, 27]]` (unrotated HGP `surfaceHGP 27`); the paper's
    per-logical tile `2(d+1)² = 1568` is the ROTATED patch including routing. -/
theorem ge2021_distance_is_verified_code :
    (surfaceCodeD 27).d = 27 ∧ (surfaceCodeD 27).k = 1 ∧ (surfaceCodeD 27).n = 1405 := by
  decide

/-! ## QUBITS — reproduced within ~3 % (no unverified qubit-side optimization) -/

/-- The verified surface area-ceiling for GE2021: 6200 logical × (2·1568) = 19.44 M. -/
theorem ge2021_qubits_derived : ge2021_naive.qubits = 19_443_200 := by decide

/-- It sits below the reported 20 M and within ~600 k (≈3 %) — the residual is the
    magic factory the area model folds out.  So the reported qubit count IS the
    verified ceiling: no unverified qubit-side speed-up. -/
theorem ge2021_qubits_reproduce_reported :
    ge2021_naive.qubits ≤ ge2021_reported_qubits
    ∧ ge2021_reported_qubits - ge2021_naive.qubits ≤ 600_000 := by decide

/-! ## TIME — the reported 8 h is 2–3× under the verified sequential ceiling -/

/-- The verified naive-sequential time ceiling: 2.7×10⁹ Toffolis · 27 cycles · 1 µs
    = 729×10⁹ tenths-µs ≈ 20.25 h. -/
theorem ge2021_time_ceiling : ge2021_naive.time_us_tenths = 729_000_000_000 := by decide

/-- The reported 8 h (288×10⁹ tenths-µs) is 2–3× UNDER the verified sequential
    ceiling.  That factor (~2.5×) is the reaction-limited pipelining the paper
    achieves but we do not verify at full scale — THE GAP. -/
theorem ge2021_time_gap_2_to_3x :
    2 * ge2021_reported_time_us_tenths ≤ ge2021_naive.time_us_tenths
    ∧ ge2021_naive.time_us_tenths ≤ 3 * ge2021_reported_time_us_tenths := by decide

/-! ## The reproduction capstone -/

/-- **GIDNEY–EKERÅ 2021 REPRODUCED, gap pinned.**  From the verified surface-code
    resource derivation and the paper's own inputs:
    (i) QUBITS — derived 19.44 M ≤ reported 20 M, within ~3 % (factory residual):
        the reported footprint IS the verified area ceiling, no unverified gap;
    (ii) TIME — reported 8 h is 2–3× under the verified sequential ceiling of
        20.25 h: the ≈2.5× gap is pipelining, claimed but not verified at scale.
    This is a verified-formula reproduction; the end-to-end Hilbert-space semantic
    closure remains the delimited chain (see the file header). -/
theorem gidney_ekera_2021_reproduced :
    (ge2021_naive.qubits ≤ ge2021_reported_qubits
      ∧ ge2021_reported_qubits - ge2021_naive.qubits ≤ 600_000)
    ∧ (2 * ge2021_reported_time_us_tenths ≤ ge2021_naive.time_us_tenths
      ∧ ge2021_naive.time_us_tenths ≤ 3 * ge2021_reported_time_us_tenths) :=
  ⟨ge2021_qubits_reproduce_reported, ge2021_time_gap_2_to_3x⟩

/-============================================================================
  PART B — Concrete naive (fully-serial) baseline + gap to the paper
           (was NaiveBaselineCost)
============================================================================-/

/-! ### Naive baseline concrete numbers. -/

/-- Verified Toffoli (= CCZ magic) count for windowed RSA-2048. -/
def toffoliCount : Nat := 2622824448

/-- Per-Toffoli serial wall-time (µs): CCZ production + teleport surgery (d=27 cycles) + decode. -/
def perToffoliUs : Nat := ccz_spec_qianxu.production_us + 27 + 27

theorem perToffoliUs_value : perToffoliUs = 12054 := by decide

/-- Naive serial runtime (µs), hours. -/
def naiveWallclockUs : Nat := toffoliCount * perToffoliUs
def naiveWallclockHours : Nat := naiveWallclockUs / 3600000000

theorem naiveWallclockHours_value : naiveWallclockHours = 8782 := by decide

/-- Naive qubits: the full data register plus ONE magic-state factory. -/
def naiveQubits : Nat :=
  windowedPhysicalDataQubits_rsa2048 + ccz_spec_qianxu.factory_qubits

theorem naiveQubits_value : naiveQubits = 9636357 := by decide

/-! ### Gap to the Gidney–Ekerå paper (20 000 000 qubits, 8 hours). -/

/-- **TIME GAP ≈ 1098×.**  The naive serial baseline takes `8782` hours; the paper reports `8`.
    The factor `1097–1098` is essentially the `1093` parallel CCZ factories the paper uses and the
    naive baseline does not — serial magic production is the entire gap. -/
theorem time_gap :
    1097 * gidney_ekera_2021_rsa2048_wallclock_hours ≤ naiveWallclockHours
    ∧ naiveWallclockHours ≤ 1098 * gidney_ekera_2021_rsa2048_wallclock_hours := by decide

/-- **QUBIT GAP ≈ 0.48×.**  The naive baseline uses FEWER than half the paper's qubits — it has no
    factory farm (one factory) and minimal routing; the data register dominates. -/
theorem qubit_gap :
    naiveQubits < gidney_ekera_2021_rsa2048_physical_qubits
    ∧ 2 * naiveQubits ≤ gidney_ekera_2021_rsa2048_physical_qubits := by decide

/-- **SPACETIME GAP ≈ 529×.**  In qubit·hours the naive baseline is ~529× worse than the paper —
    the price of a fully-serial, provably-correct schedule (all the loss is in time, from serial
    magic production). -/
theorem spacetime_gap :
    528 * (gidney_ekera_2021_rsa2048_physical_qubits * gidney_ekera_2021_rsa2048_wallclock_hours)
        ≤ naiveQubits * naiveWallclockHours
    ∧ naiveQubits * naiveWallclockHours
        ≤ 530 * (gidney_ekera_2021_rsa2048_physical_qubits * gidney_ekera_2021_rsa2048_wallclock_hours) := by
  decide

end FormalRV.Audit.GidneyEkera2021

-- ✅ CAPSTONE: GE2021 reproduced via the verified surface-code area/time law (axiom-free):
#verify_clean FormalRV.Audit.GidneyEkera2021.gidney_ekera_2021_reproduced
-- the resource ceilings the capstone rests on (➗ arithmetic):
#check @FormalRV.Audit.GidneyEkera2021.ge2021_qubits_derived          -- 19,443,200
#check @FormalRV.Audit.GidneyEkera2021.ge2021_qubits_reproduce_reported-- ≤ 20M
#check @FormalRV.Audit.GidneyEkera2021.ge2021_time_ceiling            -- ~20.25 h
#check @FormalRV.Audit.GidneyEkera2021.ge2021_time_gap_2_to_3x        -- 8 h < ceiling
