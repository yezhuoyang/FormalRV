/-
  FormalRV.Shor.MeasuredBabbushHonestTCount — the HONEST gadget-by-gadget T-count of the ACTUAL
  Babbush-measured mod-N lookup-add step (Concern-2, route (1): no uniform 4-T charge, each Toffoli
  at its REAL fault-tolerant T-cost, summed over the composed syntactic object).

  ## Why this exists

  `gidneyTCount = 4 · toffoli` charges EVERY Toffoli at the 4-T temporary-AND rate.  That is EXACT
  for the Babbush QROM lookups (merged-AND tree: each Toffoli writes a fresh `mz`-cleared ancilla, a
  genuine temporary AND — `GidneyTCount.gidneyTCount_unaryQROMAt`).  But the step's adder/reduction
  (`cuccaro_n_bit_adder_full` + `modNReduceFlag` + `regCompareXor`) is the TEXTBOOK reversible
  construction, whose carry Toffolis are NOT clean-target temporary ANDs — charging them 4 T UNDER-
  counts (a real Toffoli is 7 T here).  So the uniform `gidneyTCount` of the whole step is optimistic.

  This file gives the HONEST count — charging each gadget at its real cost, gadget by gadget over the
  actual composed step:

    * the two Babbush reads at the temporary-AND rate (`gidneyTCount`, 4 T per AND = `4·(2^w − 1)` each);
    * the Cuccaro adder, the mod-N reduce, and the register-compare at the textbook rate
      (`EGate.tcount`, 7 T per Toffoli) — because in THIS circuit those gadgets are reversible, not
      measured temporary ANDs.

  `honestBabbushStepTCount_eq`: the honest step T-count is exactly `8·(2^w − 1) + 56·bits`.
  `gidneyTCount_le_honest` / `honest_le_tcount`: it sits between the optimistic all-temporary-AND
  count (`8·(2^w − 1) + 32·bits`) and the pessimistic all-textbook count (`14·(2^w − 1) + 56·bits`) —
  the difference from `gidneyTCount` (`24·bits`) is exactly the under-charge the uniform model hides.
  (Route (2) — the all-MEASURED rebuild where the adder too is a temporary-AND gadget, so the honest
  count drops to the optimistic one and matches the paper — is the separate next step.)
-/
import FormalRV.Shor.MeasuredBabbushWindowedModN

namespace FormalRV.Shor.MeasuredBabbushWindowedModN

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.MeasUncomputeAt
open FormalRV.Shor.MeasuredBabbushRead

/-- **The HONEST gadget-by-gadget T-count of the Babbush-measured step.**  Each gadget at its REAL
    fault-tolerant T-cost: the two Babbush reads as temporary ANDs (`gidneyTCount`, 4 T/AND); the
    Cuccaro adder, mod-N reduce, and register-compare at the textbook 7-T rate (`EGate.tcount`),
    since in this circuit they are reversible (not measured temporary ANDs).  No uniform charge. -/
def honestBabbushStepTCount (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat) : Nat :=
  FormalRV.Shor.GidneyTCount.gidneyTCount (babbushReadInPlace w (addendIdx q_start) bits T)
  + EGate.tcount (EGate.base (cuccaro_n_bit_adder_full bits q_start))
  + EGate.tcount (EGate.base (modNReduceFlag bits q_start N flagPos))
  + FormalRV.Shor.GidneyTCount.gidneyTCount (babbushReadInPlace w (addendIdx q_start) bits T)
  + EGate.tcount (EGate.base (regCompareXor bits q_start flagPos))

/-- **The honest step T-count is exactly `8·(2^w − 1) + 56·bits`.**  Two temporary-AND reads
    (`2·4·(2^w − 1)`) + textbook adder (`14·bits`) + reduce (`28·bits`) + compare (`14·bits`). -/
theorem honestBabbushStepTCount_eq (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat) :
    honestBabbushStepTCount w bits N T q_start flagPos = 8 * (2 ^ w - 1) + 56 * bits := by
  unfold honestBabbushStepTCount FormalRV.Shor.GidneyTCount.gidneyTCount
    FormalRV.PaperClaims.gidney_2018_logical_AND_compute_tcount
  simp only [EGate.tcount, toffoli_babbushReadInPlace, tcount_cuccaro_n_bit_adder_full,
    tcount_modNReduceFlag, tcount_regCompareXor]
  omega

/-- **The uniform `gidneyTCount` UNDER-counts the honest cost** by `24·bits` (the textbook adder's
    `3 T` per Toffoli the all-temporary-AND model omits): `gidneyTCount(step) = 8·(2^w − 1) + 32·bits
    ≤ honest`. -/
theorem gidneyTCount_le_honest (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat) :
    FormalRV.Shor.GidneyTCount.gidneyTCount (babbushMeasModNLookupAddStep w bits N T q_start flagPos)
      ≤ honestBabbushStepTCount w bits N T q_start flagPos := by
  rw [honestBabbushStepTCount_eq, gidneyTCount_babbushMeasModNLookupAddStep]
  omega

/-- **The honest cost never exceeds the all-textbook `EGate.tcount`** (`14·(2^w − 1) + 56·bits`): the
    Babbush reads are genuinely temporary ANDs, so charging them 4 T (not 7) is sound. -/
theorem honest_le_tcount (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat) :
    honestBabbushStepTCount w bits N T q_start flagPos
      ≤ EGate.tcount (babbushMeasModNLookupAddStep w bits N T q_start flagPos) := by
  rw [honestBabbushStepTCount_eq, tcount_babbushMeasModNLookupAddStep]
  have h : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  omega

end FormalRV.Shor.MeasuredBabbushWindowedModN
