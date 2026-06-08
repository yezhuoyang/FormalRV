/-
  Audit · cain-xu-2026 (arXiv:2603.28627) · HARDWARE ASSUMPTIONS
  ----------------------------------------------------------------------------
  The physical parameters the paper's resource estimate assumes — reader checks
  these match the paper.
    • neutral-atom baseline: physical two-qubit error 1e-3, error-correction
      cycle 1 µs (Bluvstein 2024-style numbers, in our Nat units 1/1000 and
      1/10 µs).

  Holds the hardware component `cainxu_hw` of the recorded
  (algorithm, code, hardware) tuple `cainxu_instance` (the algorithm part lives
  in L1_Algorithm, the code part in L4_Code).  ONE flat namespace
  `FormalRV.Audit.CainXu2026`.
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Audit.CainXu2026

open FormalRV.Framework FormalRV.Qualtran

/-- The Cain–Xu neutral-atom hardware baseline: physical error 1e-3,
cycle time 1 μs (Bluvstein 2024-style numbers, encoded in our Nat
units as 1/1000 and 1/10 μs respectively). -/
def cainxu_hw : QualtranPhysicalParameters :=
  { physical_error_thousandths := 1, cycle_time_us_tenths := 10 }

end FormalRV.Audit.CainXu2026

#check @FormalRV.Audit.CainXu2026.cainxu_hw   -- QualtranPhysicalParameters (1e-3, 1µs)
