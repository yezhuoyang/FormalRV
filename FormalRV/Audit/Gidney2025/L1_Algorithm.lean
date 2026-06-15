/-
  Audit · gidney-2025 · LAYER 1 — THE ALGORITHM
  ----------------------------------------------------------------------------
  Windowed Ekerå–Håstad Shor (s = 8; paper §3.1 / notes line 72-73, m = 1280
  input qubits for n = 2048).  Algorithm-level success is SHARED and
  N-parametric (order finding ≥ κ/(log₂N)⁴ — Audit/Peng2022,
  FormalRV.StandardShor).
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Shor.StandardShor

namespace FormalRV.Audit.Gidney2025

open FormalRV.Framework

/-- Gidney 2025 Shor instance: RSA-2048 with Ekerå–Håstad `s = 8` parameter
(input qubits m = ⌊n/2⌋ + ⌊n/s⌋ = 1024 + 256 = 1280 at n = 2048; paper
§3.1, main.tex:1030,1166). -/
def gidney2025_shor : ShorAlgorithm :=
  { N := 0, q_A := 8 }

end FormalRV.Audit.Gidney2025

#check @FormalRV.Audit.Gidney2025.gidney2025_shor       -- ShorAlgorithm (q_A = 8)
#check @FormalRV.StandardShor.orderFindingSucceeds      -- ✅ shared success bound
