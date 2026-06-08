/-
  Audit · webster-2026 "Pinnacle" (arXiv:2602.11457) · HARDWARE ASSUMPTIONS
  ----------------------------------------------------------------------------
  The paper's physical parameters — reader checks these match the paper.
    • pinnacle_hw: physical two-qubit error 1e-3, error-correction cycle 1 µs,
      reaction time 10 µs (paper §III.D primary baseline, notes line 29).
      Same numeric profile as Qualtran's `default_params` and Cain–Xu's
      neutral-atom profile.
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Audit.Pinnacle

open FormalRV.Framework FormalRV.Qualtran

/-- Pinnacle hardware: 1e-3 gate error + 1 μs cycle time (paper §III.D
primary baseline, notes line 29). Numerically identical to Qualtran's
`default_params` and Cain–Xu's neutral-atom profile. -/
def pinnacle_hw : QualtranPhysicalParameters :=
  { physical_error_thousandths := 1, cycle_time_us_tenths := 10 }

end FormalRV.Audit.Pinnacle

#check @FormalRV.Audit.Pinnacle.pinnacle_hw   -- QualtranPhysicalParameters (1e-3, 1 µs)
