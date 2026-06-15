/-
  FormalRV.Arithmetic.Cuccaro.CuccaroUComBridge — Cuccaro-specific
  corollaries of the generic Gate→UCom bridge.

  These lemmas instantiate the certified-optimizer semantic
  preservation theorems (`FormalRV.Arithmetic.GateToUCom`) at the
  Cuccaro MAJ/UMA gate blocks. They live here (not in `GateToUCom`)
  so that the generic bridge — and everything importing it, including
  the `Adder` interface — does not transitively pull in the Cuccaro
  gate definitions.
-/
import FormalRV.Arithmetic.GateToUCom
import FormalRV.Arithmetic.Cuccaro.Cuccaro

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- Cuccaro MAJ: the certified optimizer preserves its semantics
    (which is non-trivially the majority function on bits). -/
theorem uc_eval_optimize_to_fixpoint_cuccaro_MAJ {dim : Nat}
    (a b c : Nat) (h_wt : Gate.WellTyped dim (cuccaro_MAJ a b c)) :
    uc_eval (Gate.toUCom dim (optimize_to_fixpoint (cuccaro_MAJ a b c)))
      = uc_eval (Gate.toUCom dim (cuccaro_MAJ a b c)) :=
  uc_eval_toUCom_optimize_to_fixpoint _ h_wt

/-- Cuccaro UMA analog. -/
theorem uc_eval_optimize_to_fixpoint_cuccaro_UMA {dim : Nat}
    (a b c : Nat) (h_wt : Gate.WellTyped dim (cuccaro_UMA a b c)) :
    uc_eval (Gate.toUCom dim (optimize_to_fixpoint (cuccaro_UMA a b c)))
      = uc_eval (Gate.toUCom dim (cuccaro_UMA a b c)) :=
  uc_eval_toUCom_optimize_to_fixpoint _ h_wt

/-- Documented limitation: on `seq MAJ UMA`, the natural CCX-CCX
    boundary between MAJ-end and UMA-start is NOT caught by the
    current optimizer because association blocks the pattern.
    `seq MAJ UMA` has shape `seq (seq ... (CCX a b c)) (seq (CCX a b c) ...)`
    where the two CCXs are at different nesting depths. T-count
    stays at 14 (= 7 + 7) without an associativity-normalizing
    preprocessor.
    Smoke test: optimizer leaves it at 14 T per
    `MAJ_UMA_pair_tcount`. -/
example (a b c : Nat) :
    tcount (cuccaro_MAJ a b c) + tcount (cuccaro_UMA a b c) = 14 := by
  simp [tcount, MAJ_meets_paper_claim, UMA_meets_paper_claim,
        paper_claim_MAJ_tcount, paper_claim_UMA_tcount]

end FormalRV.BQAlgo
