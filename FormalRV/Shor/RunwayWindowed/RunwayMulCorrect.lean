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
open FormalRV.Shor.RunwayWindowed.RunwayLayout (runwayAddKAt runwayAddendIdx)
open FormalRV.Shor.RunwayWindowed.RunwayShift (runwayAddKAt_downshift)
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
  (runwayAddK kClean segStride segBase)
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderContiguous
  (contiguousDecode contiguousAugend contiguousAddend runwayAddK_contiguous)
open FormalRV.Shor.WindowedCircuit
  (copyWindow lookupReadAt copyWindow_loads_window copyWindow_frame
   lookupReadAt_selects_word lookupReadAt_frame)

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

/-! ## M3 window-step prerequisites — the segment-major addend index facts. -/

/-- The segment-major addend positions sit strictly above the lookup zone
    (`> 2w`), as `lookupReadAt_selects_word`/`_frame` require. -/
theorem runwayAddendIdx_gt_two_w (gSep w i : Nat) :
    2 * w < runwayAddendIdx gSep (1 + 2 * w) i := by
  unfold runwayAddendIdx
  show 2 * w < 1 + 2 * w + segBase gSep (i / gSep) + 2 * (i % gSep) + 2
  omega

/-- The segment-major addend index is injective: it determines the segment
    `i / gSep` and the within-segment offset `i % gSep`, hence `i`. -/
theorem runwayAddendIdx_inj (gSep base : Nat) (hgSep : 0 < gSep) (i i' : Nat)
    (h : runwayAddendIdx gSep base i = runwayAddendIdx gSep base i') : i = i' := by
  have hr : i % gSep < gSep := Nat.mod_lt _ hgSep
  have hr' : i' % gSep < gSep := Nat.mod_lt _ hgSep
  have hE : (i / gSep) * (2 * gSep + 3) + 2 * (i % gSep)
      = (i' / gSep) * (2 * gSep + 3) + 2 * (i' % gSep) := by
    have h' : 1 + 2 * base + (i / gSep) * (2 * gSep + 3) + 2 * (i % gSep) + 2
        = 1 + 2 * base + (i' / gSep) * (2 * gSep + 3) + 2 * (i' % gSep) + 2 := by
      have : base + (i / gSep) * (2 * gSep + 3) + 2 * (i % gSep) + 2
          = base + (i' / gSep) * (2 * gSep + 3) + 2 * (i' % gSep) + 2 := h
      omega
    omega
  -- The quotient `i/gSep` is determined (the `2·(i%gSep)` term is `< 2gSep+3`).
  have hq : i / gSep = i' / gSep := by
    have h1 : (i / gSep) * (2 * gSep + 3) < (i' / gSep + 1) * (2 * gSep + 3) := by
      calc (i / gSep) * (2 * gSep + 3)
          ≤ (i / gSep) * (2 * gSep + 3) + 2 * (i % gSep) := Nat.le_add_right _ _
        _ = (i' / gSep) * (2 * gSep + 3) + 2 * (i' % gSep) := hE
        _ < (i' / gSep) * (2 * gSep + 3) + (2 * gSep + 3) := by omega
        _ = (i' / gSep + 1) * (2 * gSep + 3) := by ring
    have h2 : (i' / gSep) * (2 * gSep + 3) < (i / gSep + 1) * (2 * gSep + 3) := by
      calc (i' / gSep) * (2 * gSep + 3)
          ≤ (i' / gSep) * (2 * gSep + 3) + 2 * (i' % gSep) := Nat.le_add_right _ _
        _ = (i / gSep) * (2 * gSep + 3) + 2 * (i % gSep) := hE.symm
        _ < (i / gSep) * (2 * gSep + 3) + (2 * gSep + 3) := by omega
        _ = (i / gSep + 1) * (2 * gSep + 3) := by ring
    have hlt1 : i / gSep < i' / gSep + 1 :=
      Nat.lt_of_mul_lt_mul_right h1
    have hlt2 : i' / gSep < i / gSep + 1 :=
      Nat.lt_of_mul_lt_mul_right h2
    omega
  have hrmod : i % gSep = i' % gSep := by rw [hq] at hE; omega
  calc i = gSep * (i / gSep) + i % gSep := (Nat.div_add_mod i gSep).symm
    _ = gSep * (i' / gSep) + i' % gSep := by rw [hq, hrmod]
    _ = i' := Nat.div_add_mod i' gSep

end FormalRV.Shor.RunwayWindowed.RunwayMulCorrect
