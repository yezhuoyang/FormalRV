/-
  Audit · peng-2022 · LAYER 1 — THE ALGORITHM  (this paper's whole point)
  ----------------------------------------------------------------------------
  THE cross-cutting verified result lives here: order finding succeeds with
  probability ≥ κ/(log₂N)⁴ (κ = 4·e⁻²/π²), N-parametric, ported from SQIR's Coq
  proof.  Every other paper's algorithm layer reuses it.  ✅ verify-clean.

  Peng 2022 is the only corpus paper with a *machine-checked* algorithm
  correctness theorem (SQIR/RCIR in Coq; see `SQIR/examples/shor/`).  Its L1 is
  therefore the genuine verified-Shor anchor of the whole corpus, while it has
  NO QEC stack (notes/peng-2022.md lines 54-55) — hence the honest ⬜ GAPs in
  SystemZones / L3 / L4.  The Shor INSTANCE bound here is the classical
  single-window phase-estimation (no Ekerå–Håstad multi-window optimisation).
-/
import FormalRV.Framework.L1_Algorithm
import FormalRV.Shor.OrderFinding.SuccessSensitivity
import FormalRV.Shor.PostQFT.PostQFTCompletion
import FormalRV.Verifier

namespace FormalRV.Audit.Peng2022

open FormalRV.Framework

/-- Peng / SQIR Shor instance: classical single-window phase estimation
(no Ekerå–Håstad multi-window optimisation).  This is the **machine-checked
algorithm anchor** of the corpus. -/
def peng_shor : ShorAlgorithm :=
  { N := 0, q_A := 1 }

end FormalRV.Audit.Peng2022

#check @FormalRV.Audit.Peng2022.peng_shor                           -- ShorAlgorithm (q_A = 1)
#check @FormalRV.SQIRPort.κ                                          -- κ = 4·e⁻²/π²
-- ✅ N-parametric order-finding success bound (the headline, oracle-generic):
#verify_clean FormalRV.SQIRPort.Shor_correct_var
-- ✅ the bound minus a tunable error budget (decoder cutoff + p_L), reusable by every paper:
#verify_clean FormalRV.Shor.SuccessSensitivity.master_success_bound
