/-
  Audit · gidney-ekera-2021 · LAYER 1 — THE ALGORITHM
  Windowed Ekerå–Håstad Shor (q_A = 3072).  Algorithm-level success is SHARED and
  N-parametric (order finding ≥ κ/(log₂N)⁴ — Audit/Peng2022, FormalRV.StandardShor).
-/
import FormalRV.Audit.GidneyEkera2021.GidneyEkera2021
import FormalRV.StandardShor
#check @FormalRV.Audit.GidneyEkera2021.GidneyEkera2021.ge2021_shor      -- ShorAlgorithm (q_A = 3072)
#check @FormalRV.StandardShor.orderFindingSucceeds                     -- ✅ shared success bound
