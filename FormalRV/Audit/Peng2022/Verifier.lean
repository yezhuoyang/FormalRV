/-
  Audit · peng-2022 · VERIFIER — end-to-end obligation + anti-cheat gate
  ----------------------------------------------------------------------------
  END-TO-END (algorithm): order finding / Shor succeeds with probability ≥ κ/(log₂N)⁴
  for ANY N and any correct modular-multiplier oracle — the SHARED guarantee every other
  paper's algorithm layer inherits.  #verify_clean ACCEPTS it (axioms ⊆ the allowed set).

  Honest scope: this is the ALGORITHM layer only.  Peng 2022 has no QEC/system/PPM layers
  (⬜ GAPs above) — and the ported QPE/continued-fractions semantics are the open frontier
  (see README STILL UNSOLVED).
-/
import FormalRV.Shor.PostQFT.PostQFTCompletion
import FormalRV.Shor.SuccessSensitivity
import FormalRV.Verifier
#verify_clean FormalRV.SQIRPort.Shor_correct_var
#verify_clean FormalRV.Shor.SuccessSensitivity.master_success_bound
