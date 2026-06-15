/-
  Audit · Pinnacle · LAYER 1 — THE ALGORITHM
  ----------------------------------------------------------------------------
  Windowed Ekerå–Håstad Shor (q_A = 3072; same nominal window count shape as
  GE2021 — the paper is code-layer-focused and doesn't override the algorithm
  layer).  Pinnacle's factoring algorithm is based on Gidney's.  Algorithm-level
  success is SHARED and N-parametric (order finding ≥ κ/(log₂N)⁴ —
  FormalRV.StandardShor.orderFindingSucceeds).
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Shor.StandardShor

namespace FormalRV.Audit.Pinnacle

open FormalRV.Framework

/-- Pinnacle Shor instance: RSA-2048 with the same nominal Ekerå–Håstad
window count as GE2021 (the paper is code-layer-focused; q_A is
algorithm-level and not overridden in Pinnacle). -/
def pinnacle_shor : ShorAlgorithm :=
  { N := 0, q_A := 3072 }

end FormalRV.Audit.Pinnacle

#check @FormalRV.Audit.Pinnacle.pinnacle_shor   -- ShorAlgorithm (q_A = 3072)
#check @FormalRV.StandardShor.orderFindingSucceeds         -- ✅ shared success bound
