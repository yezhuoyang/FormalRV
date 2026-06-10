/-
  Audit · xu-2024 · LAYER 1 — THE ALGORITHM
  ----------------------------------------------------------------------------
  q_A = 8 (algorithm-level; the paper is code-layer-focused and does not
  override the windowed-Shor baseline — matches Gidney 2025).  Algorithm-level
  success is SHARED and N-parametric (order finding; FormalRV.StandardShor).
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Shor.StandardShor

namespace FormalRV.Audit.Xu2024

open FormalRV.Framework

/-- Xu 2024 Shor instance (q_A baseline matches other windowed Shor
papers; Xu is code-layer-focused). -/
def xu2024_shor : ShorAlgorithm :=
  { N := 0, q_A := 8 }

end FormalRV.Audit.Xu2024

#check @FormalRV.Audit.Xu2024.xu2024_shor              -- ShorAlgorithm (q_A = 8)
#check @FormalRV.StandardShor.orderFindingSucceeds     -- ✅ shared success bound
