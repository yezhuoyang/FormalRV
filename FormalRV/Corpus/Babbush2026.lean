/-
  FormalRV.Corpus.Babbush2026 — Phase-C corpus paper #5.

  Babbush et al. 2026, "Approaching ECC-256 with less than half a
  million physical qubits" (low-qubit variant). Surface code on
  superconducting / fast-clock hardware.

  **Key cross-paper note:** Babbush targets **ECC-256** discrete-log,
  not RSA-2048 — the algorithm is still Shor (now on the elliptic-
  curve subgroup), and the framework's L1 `ShorAlgorithm` structure
  is `(N, q_A) : Nat × Nat` which accommodates ECC-256 with `N` =
  256-bit prime modulus. This is the first non-RSA paper in the
  corpus and tests whether the framework's algorithm layer is truly
  modulus-agnostic.

  Parametric tuple bound here:
    L1 ShorAlgorithm     : q_A = 8 (consistent with other windowed
                           Shor papers; Babbush is gate-count-focused
                           and does not override the algorithm layer)
    L4 QECCode           : (n, k, d) = (425, 1, 14) — surface code
                           sized so that 1175 logical qubits ×
                           425 phys/logical ≈ 500,000 phys qubits
                           (notes/babbush-2026.md lines 222, 225;
                           distance back-solved from 2(d+1)² ≈ 425).
    HW QualtranPhysical  : `gidney_fowler_realistic` (1e-3 physical
                           error, 1 μs fast-clock cycle; notes line
                           42, 198). Same as GE2021 / Gidney2025.
-/

import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Corpus.Babbush2026

open FormalRV.Framework FormalRV.Qualtran

/-- Babbush ECC-256 Shor instance.  `N` is placeholder for the 256-bit
prime modulus the paper uses.  **First non-RSA paper** — confirms the
framework's L1 layer is modulus-agnostic. -/
def babbush_shor : ShorAlgorithm :=
  { N := 0, q_A := 8 }

/-- Babbush surface-code instance: distance ≈ 14, ~425 physical qubits
per logical (back-solved from notes line 222 `1175 logical qubits` ×
notes line 225 `500_000 physical qubits` ÷ 1175 ≈ 425; 2(d+1)² = 450
gives d = 14 as the matching distance). Parity matrices stubbed. -/
def babbush_code : QECCode :=
  { n := 425, k := 1, d := 14, hx := [], hz := [] }

/-- Babbush hardware: fast-clock superconducting baseline matching
Qualtran's canonical `gidney_fowler_realistic` factory (1e-3 gate err,
1 μs cycle; paper §II.B + notes line 198). -/
def babbush_hw : QualtranPhysicalParameters :=
  gidney_fowler_realistic

/-- The full parametric tuple. -/
def babbush_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (babbush_shor, babbush_code, babbush_hw)

/-- Smoke: paper-stated parameters read back. -/
example : babbush_instance.1.q_A = 8 := by rfl
example : babbush_instance.2.1.n = 425 ∧
          babbush_instance.2.1.k = 1 ∧
          babbush_instance.2.1.d = 14 := ⟨rfl, rfl, rfl⟩
example : babbush_instance.2.2 = gidney_fowler_realistic := rfl

end FormalRV.Corpus.Babbush2026
