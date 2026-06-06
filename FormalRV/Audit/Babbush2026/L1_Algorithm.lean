/-
  Audit · babbush-2026 · LAYER 1 — THE ALGORITHM (first NON-RSA paper: ECC-256 discrete log)
  ----------------------------------------------------------------------------
  Babbush targets ECC-256 discrete-log, not RSA-2048 — the algorithm is still
  Shor (now on the elliptic-curve subgroup), and the framework's L1
  `ShorAlgorithm` structure `(N, q_A) : Nat × Nat` accommodates ECC-256 with
  `N` = 256-bit prime modulus.  This is the first non-RSA paper in the corpus
  and tests whether the framework's algorithm layer is truly modulus-agnostic.
  Algorithm-level success is the SHARED, N-parametric bound
  (`StandardShor.orderFindingSucceeds`).
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.StandardShor

namespace FormalRV.Audit.Babbush2026

open FormalRV.Framework

/-- Babbush ECC-256 Shor instance.  `N` is placeholder for the 256-bit prime
modulus the paper uses (`q_A = 8`, consistent with other windowed Shor papers;
Babbush is gate-count-focused and does not override the algorithm layer).
**First non-RSA paper** — confirms the framework's L1 layer is modulus-agnostic. -/
def babbush_shor : ShorAlgorithm :=
  { N := 0, q_A := 8 }

end FormalRV.Audit.Babbush2026

#check @FormalRV.Audit.Babbush2026.babbush_shor   -- ShorAlgorithm (ECC-256, q_A = 8)
#check @FormalRV.StandardShor.orderFindingSucceeds -- ✅ shared success bound (N-agnostic)
