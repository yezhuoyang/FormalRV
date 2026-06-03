/-
  FormalRV.Corpus.CostModelWeightDemo — wiring the purpose-tagged ancilla budget
  to REAL code data.

  The qLDPC `CostModel` (`Framework/CostModel.lean`) tags ancilla by purpose.
  This file shows the two operator-dependent tags are computed from genuine repo
  objects, NOT magic constants:
    • SYNDROME ancilla = the code's actual parity-check count `|hx| + |hz|`
      (read from `code422`'s real check matrices).
    • SURGERY  ancilla = the measured logical operator's PHYSICAL WEIGHT,
      `rowWeight (L.selectZ S)` — the Hamming weight of the VERIFIED logical
      operator from `QEC/Logical.lean` + `QEC/Addressing.lean`
      (`code422Logical`, whose `valid = true`).

  Worked on the [[4,2,2]] code and its verified logical basis.  This closes the
  loop: the resource cost a verifier reads off is sourced from the same logical
  operators it already proved correct.

  No Mathlib.  `decide` only.
-/
import FormalRV.Framework.CostModel
import FormalRV.QEC.Instances
import FormalRV.QEC.Addressing
import FormalRV.Corpus.GateSyndromeWorkedExample

namespace FormalRV.Corpus.CostModelWeightDemo

open FormalRV.Framework.Resource FormalRV.QEC FormalRV.QEC.Instances
open FormalRV.Corpus.GateSyndrome   -- `rowWeight`

/-- The [[4,2,2]] code as a flat `QECCode` (k = 2, d = 2), carrying its real
    parity-check matrices `hx = [XXXX]`, `hz = [ZZZZ]`. -/
def code422Q : FormalRV.Framework.QECCode := code422.toQECCode 2 2

/-- Dummy workload (the operator-dependent ancilla tags ignore it). -/
def w0 : Workload := { n_toff := 0, n_logical := 2 }

/-! ### The SURGERY tag is the real logical-operator weight. -/

/-- The PHYSICAL WEIGHT of the logical operator Z̄₀ = Z₀Z₂ on [[4,2,2]], read off
    the verified logical basis: `rowWeight (selectZ [0]) = 2`. -/
example : rowWeight (code422Logical.selectZ [0]) = 2 := by decide

/-- Wiring: the qLDPC SURGERY ancilla for measuring Z̄₀ equals the operator's
    real weight (2), fed in as `op_weight = rowWeight (selectZ [0])` — not a
    magic constant. -/
example :
    ((qldpcModel 0).ancilla code422Q w0 (rowWeight (code422Logical.selectZ [0])) 1).surgery = 2 := by
  decide

/-- The weight-2 product Z̄₀Z̄₁ = `selectZ [0,1]` (= Z₁Z₂) is also weight 2 ⇒
    surgery ancilla 2.  A heavier product scales the surgery tag up linearly. -/
example : rowWeight (code422Logical.selectZ [0, 1]) = 2 := by decide

/-! ### The SYNDROME tag is the real parity-check count. -/

/-- Wiring: the qLDPC SYNDROME ancilla = the code's real parity-check count
    `|hx| + |hz| = 1 + 1 = 2` (the `op_weight` argument is irrelevant here). -/
example : ((qldpcModel 0).ancilla code422Q w0 7 1).syndrome = 2 := by decide

/-! ### The full purpose-tagged budget, every term from real code data. -/

/-- For measuring Z̄₀ on [[4,2,2]] under the qLDPC model:
    syndrome 2 (real checks) + surgery 2 (real weight) ⇒ total 4 (the flat count
    the purpose-agnostic `RequestFreshAncilla` syscall provisions). -/
example : ((qldpcModel 0).ancilla code422Q w0 (rowWeight (code422Logical.selectZ [0])) 1).syndrome = 2 := by
  decide
example : ((qldpcModel 0).ancilla code422Q w0 (rowWeight (code422Logical.selectZ [0])) 1).surgery = 2 := by
  decide
example : ((qldpcModel 0).ancilla code422Q w0 (rowWeight (code422Logical.selectZ [0])) 1).total = 4 := by
  decide

end FormalRV.Corpus.CostModelWeightDemo
