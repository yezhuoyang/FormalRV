/-
  FormalRV.Corpus.Webster2026 — Phase-C corpus paper #4.

  Webster et al. 2026 ("Pinnacle"), reconfigurable-atom-array Shor
  on **generalised-bicycle (GB) qLDPC codes**. Conceptually closest
  to Cain–Xu (C.1) at the hardware layer but uses a different qLDPC
  family at L4.

  Parametric tuple bound here:
    L1 ShorAlgorithm     : q_A = 3072 (same Ekerå–Håstad window count
                           shape as GE2021; the paper is code-layer-
                           focused and doesn't override)
    L4 QECCode           : (n, k, d) = (1620, 16, 24) — Webster Tab.
                           headline GB code instance, n_cb = 1620
                           physical qubits encoding 16 logical at
                           distance 24 (notes line 74, 195).
                           Parity matrices stubbed `[]` — explicit
                           GB matrix encoding is a later tick.
    HW QualtranPhysical  : physical_error = 1e-3, cycle_time = 1 μs
                           (paper §III.D primary baseline, notes
                           line 29).  Same numeric profile as
                           Qualtran's `default_params` and Cain–Xu.
-/

import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Corpus.Webster2026

open FormalRV.Framework FormalRV.Qualtran

/-- Webster Shor instance: RSA-2048 with the same nominal Ekerå–Håstad
window count as GE2021 (the paper is code-layer-focused; q_A is
algorithm-level and not overridden in Webster). -/
def webster_shor : ShorAlgorithm :=
  { N := 0, q_A := 3072 }

/-- Webster GB code: `[[1620, 16, 24]]` generalised-bicycle code
(paper Tab.; notes/webster-2026.md lines 74, 195: n_cb = 1620,
κ = 16 logical qubits, distance 24, syndrome rounds d_t = d+2 = 26).
Distance scaling is paper-flagged Type-B conjecture (notes line 143). -/
def webster_code : QECCode :=
  { n := 1620, k := 16, d := 24, hx := [], hz := [] }

/-- Webster hardware: 1e-3 gate error + 1 μs cycle time (paper §III.D
primary baseline, notes line 29). Numerically identical to Qualtran's
`default_params` and Cain–Xu's neutral-atom profile. -/
def webster_hw : QualtranPhysicalParameters :=
  { physical_error_thousandths := 1, cycle_time_us_tenths := 10 }

/-- The full parametric tuple. -/
def webster_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (webster_shor, webster_code, webster_hw)

/-- Smoke: paper-stated parameters read back. -/
example : webster_instance.1.q_A = 3072 := by rfl
example : webster_instance.2.1.n = 1620 ∧
          webster_instance.2.1.k = 16 ∧
          webster_instance.2.1.d = 24 := ⟨rfl, rfl, rfl⟩
example : webster_instance.2.2.physical_error_thousandths = 1 := by rfl

end FormalRV.Corpus.Webster2026
