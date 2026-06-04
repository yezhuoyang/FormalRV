/-
  FormalRV.QEC.LPInstancesValid — the PARAMETRIC `liftedProduct_well_shaped` instantiated at
  the ACTUAL paper codes lp16 / lp20 / lp24, NATIVE-FREE.

  `Instances.lean` flags `well_shaped`/`css_condition` for these codes as residues "infeasible
  to elaborate" at the ~2600/4350/5278-column scale (only the `n`-count is discharged there).
  But the well_shaped half is NOT scale-bound: `liftedProduct_well_shaped` (proved
  parametrically in `LPCssCondition.lean`) needs only the 3×7 SEED's shape, which is a tiny
  `decide`.  So `well_shaped` for the real codes follows with NO `decide`/`native_decide` on
  the big matrices — the parametric proof paying off on the paper instances.

  This closes the `well_shaped` half of `code.valid` (the verifier's `hCSS`) for lp16/lp20/lp24.
  (`css_condition` remains the in-progress half — see `LPCssCondition.lean` §9.)

  No `sorry`, no `axiom`, no `native_decide`.
-/

import FormalRV.QEC.LPCssCondition
import FormalRV.QEC.Instances

namespace FormalRV.QEC.LPInstancesValid

open FormalRV.QEC.Algebraic
open FormalRV.QEC.Instances
open FormalRV.QEC

/-- **`lp16` ([[2610,744,16]]) is well-shaped — native-free.**  From the parametric
    `liftedProduct_well_shaped`; the only `decide`s are on the 3×7 seed `A_lp16`'s shape
    (`length = 3`, rows `length = 7`), NOT the 2610-column check matrices. -/
theorem lp16_well_shaped : lp16.well_shaped = true :=
  liftedProduct_well_shaped 45 A_lp16 3 7 (by decide) (by decide)

/-- **`lp20` ([[4350,1224,20]]) is well-shaped — native-free.** -/
theorem lp20_well_shaped : lp20.well_shaped = true :=
  liftedProduct_well_shaped 75 A_lp20 3 7 (by decide) (by decide)

/-- **`lp24` ([[5278,1480,24]]) is well-shaped — native-free.** -/
theorem lp24_well_shaped : lp24.well_shaped = true :=
  liftedProduct_well_shaped 91 A_lp24 3 7 (by decide) (by decide)

/-- The well_shaped half of `code.valid` holds for all three real LP memory codes, with no
    `decide`/`native_decide` at the 2600–5300-column scale. -/
theorem lp_codes_well_shaped :
    lp16.well_shaped = true ∧ lp20.well_shaped = true ∧ lp24.well_shaped = true :=
  ⟨lp16_well_shaped, lp20_well_shaped, lp24_well_shaped⟩

end FormalRV.QEC.LPInstancesValid
