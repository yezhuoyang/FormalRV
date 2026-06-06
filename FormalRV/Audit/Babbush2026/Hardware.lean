/-
  Audit · babbush-2026 (arXiv:2603.28846) · HARDWARE ASSUMPTIONS
  ----------------------------------------------------------------------------
  The paper's physical parameters — reader checks these match the paper.
    • gidney_fowler_realistic: physical two-qubit error 1e-3, fast-clock cycle
      1 µs (paper §II.B + notes line 198) — matches Qualtran's
      `gidney_fowler_realistic` factory.  Same as GE2021 / Gidney2025.
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Audit.Babbush2026

open FormalRV.Framework FormalRV.Qualtran

/-- Babbush hardware: fast-clock superconducting baseline matching
Qualtran's canonical `gidney_fowler_realistic` factory (1e-3 gate err,
1 μs cycle; paper §II.B + notes line 198). -/
def babbush_hw : QualtranPhysicalParameters :=
  gidney_fowler_realistic

end FormalRV.Audit.Babbush2026

#check @FormalRV.Audit.Babbush2026.babbush_hw   -- QualtranPhysicalParameters (1e-3, 1µs fast clock)
