/-
  Audit · gidney-ekera-2021 (arXiv:1905.09749) · HARDWARE ASSUMPTIONS
  ----------------------------------------------------------------------------
  The paper's physical parameters — reader checks these match the paper.
    • gidney_fowler_realistic: physical two-qubit error 1e-3, cycle time 1 µs
      (paper §2.13: "device 10⁻³ gate err, 1 µs cycle") — matches Qualtran's
      `gidney_fowler_realistic` factory.
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Audit.GidneyEkera2021

open FormalRV.Framework FormalRV.Qualtran

/-- Gidney–Ekerå hardware: matches Qualtran's canonical
`gidney_fowler_realistic` (1e-3 physical error, 1 μs cycle). -/
def ge2021_hw : QualtranPhysicalParameters :=
  gidney_fowler_realistic

end FormalRV.Audit.GidneyEkera2021

#check @FormalRV.Audit.GidneyEkera2021.ge2021_hw   -- QualtranPhysicalParameters (1e-3, 1µs)
