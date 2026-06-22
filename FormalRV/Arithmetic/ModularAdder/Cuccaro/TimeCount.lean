/-
  FormalRV.Arithmetic.ModularAdder.Cuccaro.TimeCount
  ──────────────────────────────────────────────────
  THE time-resource (T-count) theorems for the Cuccaro-style (SQIR-layout)
  modular adder — closing the audit gap "ModularAdder time counts missing".

  The gates here ARE the SQIR clean modular-add gates (`Def.lean` re-exports
  them from `Cuccaro/CuccaroSQIRDirtyFlag`), so the closed forms are proven
  once in `Cuccaro/CuccaroVariantsResource.lean` and re-surfaced here as the
  spine's TIME headlines:

    sqir_style_modAddConst_clean_gate bits N c            56·bits   (c ≠ 0)
    sqir_style_controlledModAddConst_gate bits …          56·bits   (c ≠ 0)

  ANCHORED: `Gate.tcount` (= `Resource.countT`) walking the same syntactic
  objects verified by `…clean_candidate_clean` / `…candidate_clean_qstart`.
  Cross-check: ModMult's proven `112·bits²` = `2 × bits × 56·bits`.
-/
import FormalRV.Arithmetic.ModularAdder.Cuccaro.Def
import FormalRV.Arithmetic.Cuccaro.CuccaroVariantsResource

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- **THE Cuccaro-style clean modular add-constant gate: T-count = 56·bits**
(0 in the dispatched `c = 0` identity case). -/
theorem tcount_cuccaro_style_modAddConst_clean_gate (bits N c : Nat) :
    tcount (sqir_style_modAddConst_clean_gate bits N c)
      = if c = 0 then 0 else 56 * bits :=
  tcount_sqir_style_modAddConst_clean_gate bits N c

/-- **The CONTROLLED Cuccaro-style modular add-constant gate: T-count =
56·bits** (0 for `c = 0`) — the per-bit primitive whose `bits`-fold forward +
uncompute composition is ModMult's proven `112·bits²`. -/
theorem tcount_cuccaro_style_controlledModAddConst_gate
    (bits q_start N c controlIdx flagPos : Nat) :
    tcount (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
      = if c = 0 then 0 else 56 * bits :=
  tcount_sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos

end FormalRV.BQAlgo
