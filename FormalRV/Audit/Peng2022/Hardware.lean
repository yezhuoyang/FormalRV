/-
  Audit · peng-2022 (arXiv:2204.07112, SQIR/Coq) · HARDWARE ASSUMPTIONS
  ----------------------------------------------------------------------------
  Peng's result is ALGORITHM-LEVEL only (no QEC/hardware model); a neutral
  default placeholder is bound for interface uniformity.  ⬜ abstract.
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Audit.Peng2022

open FormalRV.Framework FormalRV.Qualtran

/-- Peng 2022 specifies no hardware — use Qualtran's `default_params`
(1e-3, 1 μs) as a neutral placeholder (Peng is algorithm-level and does
not specify hardware). -/
def peng_hw : QualtranPhysicalParameters :=
  default_params

end FormalRV.Audit.Peng2022

#check @FormalRV.Audit.Peng2022.peng_hw   -- default placeholder hardware (abstract)
