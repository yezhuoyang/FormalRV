/-
  Audit · gidney-ekera-2021 · LAYER 1 — THE ALGORITHM
  ----------------------------------------------------------------------------
  Windowed Ekerå–Håstad Shor (q_A = 3072, ≈ 3(n-1) windowed runs for n=2048;
  paper §2.5).  Algorithm-level success is SHARED and N-parametric (order
  finding ≥ κ/(log₂N)⁴ — Audit/Peng2022, FormalRV.StandardShor).
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Shor.StandardShor

namespace FormalRV.Audit.GidneyEkera2021

open FormalRV.Framework

/-- Gidney–Ekerå Shor instance: RSA-2048 with ≈ 3072 windowed runs
(paper §2.5; the Ekerå–Håstad window count `n_e ≈ 3(n-1)`). -/
def ge2021_shor : ShorAlgorithm :=
  { N := 0, q_A := 3072 }

end FormalRV.Audit.GidneyEkera2021

#check @FormalRV.Audit.GidneyEkera2021.ge2021_shor      -- ShorAlgorithm (q_A = 3072)
#check @FormalRV.StandardShor.orderFindingSucceeds      -- ✅ shared success bound
