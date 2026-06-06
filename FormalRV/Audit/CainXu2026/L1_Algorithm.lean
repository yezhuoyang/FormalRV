/-
  Audit · cain-xu-2026 · LAYER 1 — THE ALGORITHM
  ----------------------------------------------------------------------------
  cain-xu factors RSA-2048 with a windowed Ekerå–Håstad Shor (q_A = 33).  The
  ALGORITHM-LEVEL success guarantee is SHARED and N-parametric — the order-finding
  success bound ≥ κ/(log₂N)⁴ (see Audit/Peng2022 and FormalRV.StandardShor).
-/
import FormalRV.Audit.CainXu2026.CainXu
import FormalRV.StandardShor

#check @FormalRV.Audit.CainXu2026.CainXu.cainxu_instance              -- the recorded ShorAlgorithm (q_A = 33)
#check @FormalRV.StandardShor.orderFindingSucceeds                   -- ✅ shared success bound ≥ κ/(log₂N)⁴
