/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayResource — the RESOURCE face of the
  oblivious-carry-runway adder, bundled with its semantic correctness.

  `runwayAddK gSep k` (RunwayAdderFunctional) is the `k`-segment oblivious-carry-runway
  adder `Gate` whose value-correctness is `runwayAddK_exact` (it computes the segmented
  sum `kAugend + kAddend`, via `Gate.applyNat`).  This file adds the matching closed-form
  Toffoli count on the SAME `Gate` — `k` segment adds, each a `(gSep+1)`-bit Cuccaro adder
  (`14·(gSep+1)` T = `2·(gSep+1)` Toffoli) — and the combined capstone
  `runwayAddK_verified`: ONE concrete circuit carrying BOTH semantic correctness and a
  resource count.  No `native_decide`; the count walks the actual `Gate` (`tcount`).
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
import FormalRV.Arithmetic.Windowed.WindowedCircuit

namespace FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit

/-- One segment add is a `(gSep+1)`-bit Cuccaro full adder: `14·(gSep+1)` T-gates,
    independent of the segment index. -/
theorem tcount_segAdd (gSep j : Nat) :
    tcount (segAdd gSep j) = 14 * (gSep + 1) := by
  show tcount (cuccaro_n_bit_adder_full (gSep + 1) (segBase gSep j)) = 14 * (gSep + 1)
  rw [tcount_cuccaro_n_bit_adder_full]

/-- **T-count of the k-segment runway adder**: `k · 14·(gSep+1)` — `k` segment adds
    in sequence, by induction on the `Gate.seq` chain. -/
theorem tcount_runwayAddK (gSep : Nat) :
    ∀ k, tcount (runwayAddK gSep k) = k * (14 * (gSep + 1)) := by
  intro k
  induction k with
  | zero => simp [runwayAddK, tcount]
  | succ m ih =>
      show tcount (runwayAddK gSep m) + tcount (segAdd gSep m) = (m + 1) * (14 * (gSep + 1))
      rw [ih, tcount_segAdd]
      ring

/-- **Closed-form Toffoli count of the oblivious-carry-runway adder `Gate`**:
    `2·k·(gSep+1)` — `k` segments, each a `(gSep+1)`-bit Cuccaro adder
    (`2·(gSep+1)` Toffoli). -/
theorem toffoli_runwayAddK (gSep k : Nat) :
    toffoliCount (runwayAddK gSep k) = 2 * k * (gSep + 1) := by
  rw [toffoliCount, tcount_runwayAddK,
      show k * (14 * (gSep + 1)) = 2 * k * (gSep + 1) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **THE COMBINED RUNWAY CAPSTONE — one syntactic circuit, both faces.**
    The single oblivious-carry-runway adder `Gate` `runwayAddK gSep k` SIMULTANEOUSLY
    (a) computes the correct segmented sum `kAugend + kAddend` under `Gate.applyNat`
    (SEMANTIC CORRECTNESS on the actual syntactic structure, from a clean state) and
    (b) has the closed-form Toffoli count `2·k·(gSep+1)` (RESOURCE), for the SAME
    circuit.  Kernel-clean. -/
theorem runwayAddK_verified (gSep k : Nat) (f : Nat → Bool) (hclean : kClean gSep k f) :
    kDecode gSep k (Gate.applyNat (runwayAddK gSep k) f)
        = kAugend gSep k f + kAddend gSep k f
    ∧ toffoliCount (runwayAddK gSep k) = 2 * k * (gSep + 1) :=
  ⟨runwayAddK_exact gSep k f hclean, toffoli_runwayAddK gSep k⟩

end FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
