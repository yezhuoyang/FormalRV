/-
  Audit · peng-2022 · LAYER 1 — THE ALGORITHM  (this paper's whole point)
  ----------------------------------------------------------------------------
  THE cross-cutting verified result lives here: order finding succeeds with
  probability ≥ κ/(log₂N)⁴ (κ = 4·e⁻²/π²), N-parametric, ported from SQIR's Coq proof.
  Every other paper's algorithm layer reuses it.  ✅ verify-clean.
-/
import FormalRV.Audit.Peng2022.Peng2022
import FormalRV.Shor.SuccessSensitivity
import FormalRV.Shor.PostQFT.PostQFTCompletion
import FormalRV.Verifier

#check @FormalRV.SQIRPort.κ                                          -- κ = 4·e⁻²/π²
-- ✅ N-parametric order-finding success bound (the headline, oracle-generic):
#verify_clean FormalRV.SQIRPort.Shor_correct_var
-- ✅ the bound minus a tunable error budget (decoder cutoff + p_L), reusable by every paper:
#verify_clean FormalRV.Shor.SuccessSensitivity.master_success_bound
