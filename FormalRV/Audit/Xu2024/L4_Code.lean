/-
  Audit · xu-2024 · LAYER 4 — THE QEC CODE
  ----------------------------------------------------------------------------
  ⬜ RECORDED — lifted-product (LP) qLDPC code `[[544, 80, 12]]`: 80 logical
  qubits encoded in 544 physical at distance 12 (notes line 77).  Multi-logical
  code (k = 80!).  The same construction qianxu (C.1) extrapolates to
  `[[2610, 744, 16]]`.  Parity matrices stubbed `[]` — recorded tuple.

  This file also holds the full Xu2024 parametric tuple `xu2024_instance`
  (Shor × QECCode × hardware), since it bundles the L1 algorithm, this L4 code,
  and the hardware parameters.
-/
import FormalRV.Framework.L4_QECCode
import FormalRV.Audit.Xu2024.Hardware
import FormalRV.Audit.Xu2024.L1_Algorithm

namespace FormalRV.Audit.Xu2024

open FormalRV.Framework FormalRV.Qualtran

/-- Xu 2024 LP qLDPC instance: `[[544, 80, 12]]` lifted-product code,
80 logical qubits encoded in 544 physical at distance 12 (notes line
77). The same construction qianxu extrapolates to `[[2610, 744, 16]]`. -/
def xu2024_code : QECCode :=
  { n := 544, k := 80, d := 12, hx := [], hz := [] }

/-- The full parametric tuple for the Xu 2024 instance. -/
def xu2024_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (xu2024_shor, xu2024_code, xu2024_hw)

/-- Smoke: paper-stated parameters read back, including the slow
24 ms cycle time (240,000 tenths-of-µs). -/
example : xu2024_instance.1.q_A = 8 := by rfl
example : xu2024_instance.2.1.n = 544 ∧
          xu2024_instance.2.1.k = 80 ∧
          xu2024_instance.2.1.d = 12 := ⟨rfl, rfl, rfl⟩
example : xu2024_instance.2.2.cycle_time_us_tenths = 240000 := by rfl

end FormalRV.Audit.Xu2024

#check @FormalRV.Audit.Xu2024.xu2024_code   -- QECCode [[544,80,12]] (LP code, recorded)
