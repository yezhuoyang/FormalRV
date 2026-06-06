/-
  Audit · babbush-2026 · LAYER 1 — THE ALGORITHM (first NON-RSA paper: ECC-256 discrete log)
  Confirms the L1 interface is modulus-agnostic; algorithm success is the SHARED bound.
-/
import FormalRV.Audit.Babbush2026.Babbush2026
import FormalRV.StandardShor
#check @FormalRV.Audit.Babbush2026.Babbush2026.babbush_shor   -- ECC-256, q_A = 8
#check @FormalRV.StandardShor.orderFindingSucceeds            -- ✅ shared success bound (N-agnostic)
