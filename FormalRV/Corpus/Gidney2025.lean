/-
  FormalRV.Corpus.Gidney2025 — Phase-C corpus paper #3.

  Gidney 2025, "How to factor 2048-bit RSA integers with less than a
  million noisy qubits" (arXiv:2505.15917). Surface-code + yoked-
  surface-code cold storage + cultivation on superconducting qubits.

  Parametric tuple bound here:
    L1 ShorAlgorithm     : q_A = 8  (Ekerå–Håstad-style parameter `s`,
                           paper §3.1 / notes line 72-73; m=1280 input
                           qubits for n=2048)
    L4 QECCode           : (n, k, d) = (1352, 1, 25) — hot-region
                           rotated surface code at distance 25,
                           n_physical = 2(d+1)² = 2·26² = 1352
                           (paper §3.2, notes line 128).  Yoked cold-
                           storage region (d=8-10, 430 phys/logical) is
                           a separate region this tick does not model.
    HW QualtranPhysical  : `gidney_fowler_realistic` (1e-3 gate err,
                           1 μs cycle) — paper §3.2 explicit, notes
                           line 22-23.
-/

import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Corpus.Gidney2025

open FormalRV.Framework FormalRV.Qualtran

/-- Gidney 2025 Shor instance: RSA-2048 with Ekerå–Håstad `s = 8`
parameter (input qubits m = n/2 + ⌈n/(2s)⌉ = 1024 + 128 = 1152;
paper reports 1280 due to extra ancillas). -/
def gidney2025_shor : ShorAlgorithm :=
  { N := 0, q_A := 8 }

/-- Gidney 2025 hot-region surface-code patch: distance-25 rotated
surface code, 1352 physical qubits per logical (paper §3.2 / notes
line 128: `2(d+1)² = 2·26² = 1352`). -/
def gidney2025_code : QECCode :=
  { n := 1352, k := 1, d := 25, hx := [], hz := [] }

/-- Gidney 2025 hardware: same canonical `gidney_fowler_realistic`
profile as GE2021 — 1e-3 physical error, 1 μs cycle time, square
grid NN connectivity (paper §3.2). -/
def gidney2025_hw : QualtranPhysicalParameters :=
  gidney_fowler_realistic

/-- The full parametric tuple. -/
def gidney2025_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (gidney2025_shor, gidney2025_code, gidney2025_hw)

/-- Smoke: paper-stated parameters read back. -/
example : gidney2025_instance.1.q_A = 8 := by rfl
example : gidney2025_instance.2.1.n = 1352 ∧
          gidney2025_instance.2.1.k = 1 ∧
          gidney2025_instance.2.1.d = 25 := ⟨rfl, rfl, rfl⟩
example : gidney2025_instance.2.2 = gidney_fowler_realistic := rfl

end FormalRV.Corpus.Gidney2025
