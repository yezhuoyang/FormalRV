/-
  Audit · webster-2026 "The Pinnacle Architecture" (arXiv:2602.11457) · LAYER 1 — THE ALGORITHM
  ----------------------------------------------------------------------------
  Pinnacle's factoring algorithm IS Gidney 2025: **Ekerå–Håstad short discrete log** (ekera_quantum
  2017) + **Chevignard residue-number-system** modular arithmetic — NOT vanilla order/period finding.
  So the success quantity is the EKERÅ–HÅSTAD single-run DLOG-RECOVERY bound (the `EkeraDLPSuccess`
  witness from the verified CFS engine), and the per-shot count `σ` (paper Eq. shots) is inherited from
  Gidney 2025.  (An EARLIER version of this layer #check'd the VANILLA `orderFindingSucceeds`
  ≥ κ/(log₂N)⁴ bound — that is the generic Shor-success TEMPLATE, but it is the WRONG algorithm for
  Pinnacle's EH-RNS route; corrected here.)

  The Pinnacle-specific algorithm success on the ACTUAL logical circuit (the CFS `residueFold`
  computing `g^e mod N`, threaded to dlog recovery and factor recovery) is proven in
  `EndToEndQPE.pinnacle_modexp_endToEnd` (conjuncts 1–4).  This file records the algorithm settings and
  the dlog-recovery success bound it rests on.
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Shor.StandardShor
import FormalRV.Shor.CFS.EkeraSuccess

namespace FormalRV.Audit.Pinnacle

open FormalRV.Framework
open FormalRV.CFS

/-- Pinnacle Shor instance settings (RSA-2048, q_A = 3072).  `N` is left `0` because the algorithm
    success is N-PARAMETRIC and EH-RNS (it does not period-find a fixed modulus in this record); the
    real modulus-bearing statement is the `residueFold` circuit in `EndToEndQPE`. -/
def pinnacle_shor : ShorAlgorithm :=
  { N := 0, q_A := 3072 }

/-- **Pinnacle's algorithm-level success bound (Ekerå–Håstad single-run dlog recovery).**  For any
    `EkeraDLPSuccess` witness `S` (carrying the Lemma-1 trigamma good-pair and Lemma-2 t-balanced
    lattice obligations, Ekerå 2023 Thm 1), one quantum run recovers the short discrete log with
    probability `≥ ekeraGoodFactor·ekeraBalancedFactor` — the success quantity Pinnacle's factoring
    actually uses (vs vanilla order-finding).  This is the bound threaded onto the real `residueFold`
    circuit in `pinnacle_modexp_endToEnd` (conjunct 3). -/
theorem pinnacle_dlog_recovery_succeeds (S : EkeraDLPSuccess) :
    ekeraGoodFactor S.τ * ekeraBalancedFactor S.Δ S.t S.τ ≤ S.successProb :=
  S.success_ge

end FormalRV.Audit.Pinnacle

#check @FormalRV.Audit.Pinnacle.pinnacle_shor   -- ShorAlgorithm (q_A = 3072)
-- ✅ Pinnacle's ACTUAL algorithm success route (EH-RNS dlog recovery), not vanilla order-finding:
#check @FormalRV.Audit.Pinnacle.pinnacle_dlog_recovery_succeeds
-- generic Shor-success TEMPLATE (for reference only; not Pinnacle's EH-RNS route):
#check @FormalRV.StandardShor.orderFindingSucceeds
