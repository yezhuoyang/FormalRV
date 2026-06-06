/-
  Audit · gidney-2025 · LAYER 1 — THE ALGORITHM
  Windowed Ekerå–Håstad Shor (s = 8).  Algorithm-level success is SHARED, N-parametric
  (order finding ≥ κ/(log₂N)⁴ — Audit/Peng2022, FormalRV.StandardShor).
-/
import FormalRV.StandardShor
#check @FormalRV.StandardShor.orderFindingSucceeds      -- ✅ shared success bound
