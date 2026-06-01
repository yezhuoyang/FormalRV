/-
  FormalRV.Corpus.GidneyEkera2021 — Phase-C corpus paper #2.

  Gidney & Ekerå 2021, "How to factor 2048-bit RSA integers in 8 hours
  using 20 million noisy qubits."  Surface-code on superconducting
  qubits.

  Parametric tuple bound here:
    L1 ShorAlgorithm     : q_A = 3072  (≈ 3(n-1) = 3·1023 ≈ 3070
                           windowed runs for Ekerå–Håstad with n=2048;
                           paper §2.5)
    L4 QECCode           : (n, k, d) = (1568, 1, 27)
                           rotated surface-code patch at distance 27
                           (paper §2.13–2.14, n_physical = 2(d+1)²
                           = 2·28² = 1568 per logical qubit)
    HW QualtranPhysical  : physical_error = 1e-3,
                           cycle_time = 1 μs
                           (paper §2.13: "device 10⁻³ gate err,
                           1 μs cycle")  — matches Qualtran's
                           `gidney_fowler_realistic` factory.
-/

import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Corpus.GidneyEkera2021

open FormalRV.Framework FormalRV.Qualtran

/-- Gidney–Ekerå Shor instance: RSA-2048 with ≈ 3072 windowed runs
(paper §2.5; the Ekerå–Håstad window count `n_e ≈ 3(n-1)`). -/
def ge2021_shor : ShorAlgorithm :=
  { N := 0, q_A := 3072 }

/-- Gidney–Ekerå surface-code patch: distance-27 rotated surface code,
1568 physical qubits per logical (paper §2.14 + Fig. 8, formula
`n = 2(d+1)²`). Parity matrices stubbed `[]` — a later tick can
encode the d=27 stabilizer schedule. -/
def ge2021_code : QECCode :=
  { n := 1568, k := 1, d := 27, hx := [], hz := [] }

/-- Gidney–Ekerå hardware: matches Qualtran's canonical
`gidney_fowler_realistic` (1e-3 physical error, 1 μs cycle). -/
def ge2021_hw : QualtranPhysicalParameters :=
  gidney_fowler_realistic

/-- The full parametric tuple for the Gidney–Ekerå 2021 instance. -/
def ge2021_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (ge2021_shor, ge2021_code, ge2021_hw)

/-- Smoke: paper-stated parameters read back. q_A ≈ 3·n; d = 27;
hardware matches the Qualtran factory. -/
example : ge2021_instance.1.q_A = 3072 := by rfl
example : ge2021_instance.2.1.n = 1568 ∧
          ge2021_instance.2.1.k = 1 ∧
          ge2021_instance.2.1.d = 27 := ⟨rfl, rfl, rfl⟩
example : ge2021_instance.2.2 = gidney_fowler_realistic := rfl

end FormalRV.Corpus.GidneyEkera2021
