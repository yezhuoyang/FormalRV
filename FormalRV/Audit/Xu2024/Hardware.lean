/-
  Audit · xu-2024 (arXiv:2308.08648) · HARDWARE ASSUMPTIONS
  ----------------------------------------------------------------------------
  Xu et al. 2024, "Constant-overhead fault-tolerant quantum computation with
  reconfigurable atom arrays" (Nat. Phys. 20).  The paper's physical parameters
  — reader checks these match the paper.
    • physical error 1e-3.
    • the critical OUTLIER: error-correction cycle 24 ms (240000 tenths-of-µs)
      = 24,000× the 1 µs baseline of every other corpus paper
      (notes/xu-2024.md line 115).
  This file also holds the cross-paper cycle-time cross-check (it references
  `xu2024_hw.cycle_time_us_tenths`), kept next to the hardware definition.
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Audit.Xu2024

open FormalRV.Framework FormalRV.Qualtran

/-- Xu 2024 hardware: 1e-3 gate error, **24 ms cycle time**
(notes line 115).  This is the slow-cycle outlier in the corpus —
24000 µs = 240000 in 1/10 µs Nat units. The framework's hardware
parameter range explicitly spans 1 µs → 24 ms with this entry. -/
def xu2024_hw : QualtranPhysicalParameters :=
  { physical_error_thousandths := 1, cycle_time_us_tenths := 240000 }

/-- Cross-paper sensitivity check: Xu 2024 explicitly states 24 ms
per syndrome round; this is 24,000× the 1 µs cycle time used by GE2021
/ Gidney2025 / Babbush / Webster / qianxu. The 24000 multiplier is
visible in Lean. -/
example : xu2024_hw.cycle_time_us_tenths = 24000 * gidney_fowler_realistic.cycle_time_us_tenths := by
  show 240000 = 24000 * 10
  rfl

end FormalRV.Audit.Xu2024

#check @FormalRV.Audit.Xu2024.xu2024_hw   -- QualtranPhysicalParameters (cycle = 24 ms, 240000 tenths)
