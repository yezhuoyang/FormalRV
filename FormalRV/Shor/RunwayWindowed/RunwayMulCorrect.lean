/-
  FormalRV.Shor.RunwayWindowed.RunwayMulCorrect — M3 core: the runway add at base.
  ════════════════════════════════════════════════════════════════════════════

  The single-add correctness of the re-based runway adder, pulled through the
  `runwayAddKAt_downshift` bridge from the base-0 `runwayAddK_contiguous`.  A
  single runway add needs only input-cleanliness (`kClean`) — the 1-bit runway
  absorbs the single carry, and the contiguous reading folds it by place value —
  so NO no-overflow hypothesis is needed here (that enters only for the windowed
  FOLD, where the accumulator grows; M4).

  REUSE: `runwayAddKAt_downshift` (RunwayShift), `runwayAddK_contiguous` +
  `contiguousDecode`/`contiguousAugend`/`contiguousAddend`/`kClean` (the verified
  base-0 runway adder).  NEW: only the one-line transport.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.RunwayWindowed.RunwayShift
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderContiguous

namespace FormalRV.Shor.RunwayWindowed.RunwayMulCorrect

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.RunwayWindowed.RunwayLayout (runwayAddKAt)
open FormalRV.Shor.RunwayWindowed.RunwayShift (runwayAddKAt_downshift)
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional (runwayAddK kClean)
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderContiguous
  (contiguousDecode contiguousAugend contiguousAddend runwayAddK_contiguous)

/-- **The runway add at base.**  Reading the re-based runway adder's output via
    the base-shifted contiguous decode (= the base-0 contiguous decode of the
    down-shifted state) yields `augend + addend`, exactly the base-0
    `runwayAddK_contiguous` — transported through `runwayAddKAt_downshift`.  Only
    `kClean` (down-shifted) is required; a single add never overflows the runway. -/
theorem runwayAddKAt_contiguous_at_base (gSep base k : Nat) (f : Nat → Bool)
    (hclean : kClean gSep k (fun q => f (q + base))) :
    contiguousDecode gSep k
        (fun q => Gate.applyNat (runwayAddKAt gSep base k) f (q + base))
      = contiguousAugend gSep k (fun q => f (q + base))
        + contiguousAddend gSep k (fun q => f (q + base)) := by
  rw [runwayAddKAt_downshift]
  exact runwayAddK_contiguous gSep k (fun q => f (q + base)) hclean

end FormalRV.Shor.RunwayWindowed.RunwayMulCorrect
