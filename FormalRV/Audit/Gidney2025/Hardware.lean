/-
  Audit · gidney-2025 (arXiv:2505.15917) · HARDWARE ASSUMPTIONS
  ----------------------------------------------------------------------------
  The paper's physical parameters — reader checks these match the paper.
    • gidney2025_hw: physical two-qubit error 1e-3, error-correction cycle 1 µs
      (paper §3.2 explicit, notes line 22-23) — matches Qualtran's canonical
      `gidney_fowler_realistic` factory (same profile as GE2021), square grid
      NN connectivity.
    Hot surface code (n,k,d) = (1352,1,25) = 2·(d+1)² (recorded in L4_Code);
    yoked cold storage 430 phys/logical (recorded in SystemZones).
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Audit.Gidney2025

open FormalRV.Framework FormalRV.Qualtran

/-- Gidney 2025 hardware: same canonical `gidney_fowler_realistic` profile as
GE2021 — 1e-3 physical error, 1 μs cycle time, square grid NN connectivity
(paper §3.2). -/
def gidney2025_hw : QualtranPhysicalParameters :=
  gidney_fowler_realistic

end FormalRV.Audit.Gidney2025

#check @FormalRV.Audit.Gidney2025.gidney2025_hw   -- QualtranPhysicalParameters (1e-3, 1µs)
