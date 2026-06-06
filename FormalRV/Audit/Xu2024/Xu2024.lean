/-
  FormalRV.Audit.Xu2024.Xu2024 — Phase-C corpus paper #6.

  Xu et al. 2024, "Constant-overhead fault-tolerant quantum
  computation with reconfigurable atom arrays" (Nat. Phys. 20).
  HGP/LP qLDPC codes on the same neutral-atom architecture that
  qianxu (C.1) later extrapolates from.

  **Critical cross-paper datapoint.** Xu 2024 gives the
  paper-authors' own explicit cycle-time estimate for the LP/HGP
  syndrome-extraction round on this architecture:
       **24 ms per syndrome round** (notes/xu-2024.md line 115).
  This is **24,000× longer** than the 1 μs values used in
  GE2021 / Gidney2025 / Babbush / Webster / qianxu's later claim.
  Recording this in the framework makes the cross-paper hardware
  sensitivity range surfaced and verifiable.

  Parametric tuple bound here:
    L1 ShorAlgorithm     : q_A = 8 (algorithm-level, paper does not
                           override; matches Gidney 2025).
    L4 QECCode           : (n, k, d) = (544, 80, 12) — the
                           `[[544, 80, ≤12]]` LP code instance the
                           paper explicitly demonstrates (notes line
                           77). Multi-logical-qubit code (k=80!).
    HW QualtranPhysical  : physical_error = 1e-3,
                           cycle_time = **24 ms** = 24000 μs =
                           240000 tenths (notes line 115).
-/

import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Audit.Xu2024.Xu2024

open FormalRV.Framework FormalRV.Qualtran

/-- Xu 2024 Shor instance (q_A baseline matches other windowed Shor
papers; Xu is code-layer-focused). -/
def xu2024_shor : ShorAlgorithm :=
  { N := 0, q_A := 8 }

/-- Xu 2024 LP qLDPC instance: `[[544, 80, 12]]` lifted-product code,
80 logical qubits encoded in 544 physical at distance 12 (notes line
77). The same construction qianxu extrapolates to `[[2610, 744, 16]]`. -/
def xu2024_code : QECCode :=
  { n := 544, k := 80, d := 12, hx := [], hz := [] }

/-- Xu 2024 hardware: 1e-3 gate error, **24 ms cycle time**
(notes line 115).  This is the slow-cycle outlier in the corpus —
24000 μs = 240000 in 1/10 μs Nat units. The framework's hardware
parameter range explicitly spans 1 μs → 24 ms with this entry. -/
def xu2024_hw : QualtranPhysicalParameters :=
  { physical_error_thousandths := 1, cycle_time_us_tenths := 240000 }

/-- The full parametric tuple. -/
def xu2024_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (xu2024_shor, xu2024_code, xu2024_hw)

/-- Smoke: paper-stated parameters read back, including the slow
24 ms cycle time (240,000 tenths-of-μs). -/
example : xu2024_instance.1.q_A = 8 := by rfl
example : xu2024_instance.2.1.n = 544 ∧
          xu2024_instance.2.1.k = 80 ∧
          xu2024_instance.2.1.d = 12 := ⟨rfl, rfl, rfl⟩
example : xu2024_instance.2.2.cycle_time_us_tenths = 240000 := by rfl

/-- Cross-paper sensitivity check: Xu 2024 explicitly states 24 ms
per syndrome round; this is 24,000× the 1 μs cycle time used by GE2021
/ Gidney2025 / Babbush / Webster / qianxu. The 24000 multiplier is
visible in Lean. -/
example : xu2024_hw.cycle_time_us_tenths = 24000 * gidney_fowler_realistic.cycle_time_us_tenths := by
  show 240000 = 24000 * 10
  rfl

end FormalRV.Audit.Xu2024.Xu2024
