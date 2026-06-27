/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd.Headline
  ────────────────────────────────────────────────
  Submodule of `RunwayAdderMultiAdd` (split out for per-file compile memory).
  Contains §9–§10: the HEADLINE contiguous multi-add exact under no-overflow
  (`runwayAddK_iter_contiguous`) and the standard `a + t·b` corollary under full
  input cleanliness (`IterReady_of_kClean` … `runwayAddK_iter_contiguous_clean`).

  Re-exported VERBATIM from the original `RunwayAdderMultiAdd.lean`; the
  declarations, statements, names, namespace and `open`s are unchanged.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd.MultiAddStep

namespace FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderContiguous

/-! ## §9. Deliverable #6 — HEADLINE: contiguous multi-add, exact under no-overflow.

The augend term reads each segment's FULL `(gSep+1)`-bit register `segReg_m` at
contiguous spacing — i.e. it is literally `contiguousDecode gSep k f`, the contiguous
decode of the INPUT.  (When the input runways are clean, `segReg_m = a_m`, so this
coincides with `contiguousAugend gSep k f`; in general it is the input's contiguous
reading.)  The addend term is `contiguousAddend gSep k f = Σ b_m · 2^(m·gSep)`. -/

/-- **Deliverable #6 — HEADLINE, contiguous multi-add (EXACT under per-segment
    no-overflow).**  Iterating the runway adder `t` times accumulates, in the
    CONTIGUOUS reading,

        contiguousDecode gSep k (applyNat (iterGate (runwayAddK gSep k) t) f)
          = contiguousDecode gSep k f + t · contiguousAddend gSep k f,

    EXACT, provided each segment's `(gSep+1)`-bit register never overflows over the
    whole run: `segReg_m f + t·b_m f < 2^(gSep+1)` for `m < k`.  The augend term is
    the contiguous decode of the INPUT (each segment read at its full register, so
    `a + t·b` in the contiguous place-value reading).  Proved by induction on a
    prefix `j ≤ k`, folding the MAIN per-segment multi-add (#5, mod dropped by
    no-overflow) into the `contiguousDecode`/`contiguousAddend` place-value
    recursion; `ring`.  Wired to `Gate.applyNat (iterGate (runwayAddK gSep k) t) f`
    with a concrete `contiguousDecode f + t·contiguousAddend f` RHS. -/
theorem runwayAddK_iter_contiguous (gSep k t : Nat) (f : Nat → Bool)
    (hready : IterReady gSep k f)
    (hno : ∀ m, m < k →
      segReg gSep m f
        + t * decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f
        < 2 ^ (gSep + 1)) :
    contiguousDecode gSep k (Gate.applyNat (iterGate (runwayAddK gSep k) t) f)
      = contiguousDecode gSep k f + t * contiguousAddend gSep k f := by
  set out := Gate.applyNat (iterGate (runwayAddK gSep k) t) f with hout
  -- Induct on a prefix `j ≤ k`; the per-segment multi-add applies for each m < k.
  suffices h : ∀ (j : Nat), j ≤ k →
      contiguousDecode gSep j out
        = contiguousDecode gSep j f + t * contiguousAddend gSep j f by
    exact h k (le_refl _)
  intro j
  induction j with
  | zero => intro _; simp [contiguousDecode, contiguousAddend]
  | succ n ih =>
      intro hjk
      -- unfold the (n+1) layer of contiguousDecode (out / f) and contiguousAddend f.
      show contiguousDecode gSep n out + segReg gSep n out * 2 ^ (n * gSep)
        = (contiguousDecode gSep n f + segReg gSep n f * 2 ^ (n * gSep))
          + t * (contiguousAddend gSep n f
              + decodeReg (cuccaroAdder.addendIdx (segBase gSep n)) gSep f
                  * 2 ^ (n * gSep))
      -- ① the top segment's register: MAIN multi-add (#5) at m = n, mod dropped.
      have hstep : segReg gSep n out
          = segReg gSep n f
            + t * decodeReg (cuccaroAdder.addendIdx (segBase gSep n)) gSep f := by
        rw [hout, runwayAddK_iter_segReg gSep k t f hready n (by omega)]
        exact Nat.mod_eq_of_lt (hno n (by omega))
      -- ② the lower-n contiguous decode reduces to the IH.
      have hlow : contiguousDecode gSep n out
          = contiguousDecode gSep n f + t * contiguousAddend gSep n f :=
        ih (by omega)
      rw [hstep, hlow]
      ring

/-! ## §10. Corollary — standard `a + t·b` form when the INPUT runways are clean.

`kClean` (the standard input precondition: carry-in, runway, AND addend-top all
clear per segment) is stronger than `IterReady` (carry-in + addend-top only).  Under
`kClean` the input runways are 0, so each `segReg_m f = a_m` and the augend term
becomes the standard contiguous augend `contiguousAugend gSep k f`. -/

/-- `kClean` implies `IterReady` (it additionally clears the runways). -/
theorem IterReady_of_kClean (gSep k : Nat) (f : Nat → Bool)
    (h : kClean gSep k f) : IterReady gSep k f :=
  fun m hm => ⟨(h m hm).1, (h m hm).2.2⟩

/-- With the input runways clean, the contiguous decode of the input equals the
    standard contiguous augend (`segReg_m f = a_m`, top runway bit dropped). -/
theorem contiguousDecode_eq_augend_of_kClean (gSep : Nat) :
    ∀ (k : Nat) (f : Nat → Bool), kClean gSep k f →
      contiguousDecode gSep k f = contiguousAugend gSep k f := by
  intro k
  induction k with
  | zero => intro f _; rfl
  | succ n ih =>
      intro f hclean
      show contiguousDecode gSep n f + segReg gSep n f * 2 ^ (n * gSep)
        = contiguousAugend gSep n f
          + decodeReg (cuccaroAdder.augendIdx (segBase gSep n)) gSep f * 2 ^ (n * gSep)
      have hlow : contiguousDecode gSep n f = contiguousAugend gSep n f :=
        ih f (fun j hj => hclean j (by omega))
      have hseg : segReg gSep n f
          = decodeReg (cuccaroAdder.augendIdx (segBase gSep n)) gSep f := by
        unfold segReg
        exact decodeReg_succ_of_top_false _ gSep f (hclean n (by omega)).2.1
      rw [hlow, hseg]

/-- **Corollary — standard contiguous multi-add `a + t·b`.**  Under the full input
    cleanliness `kClean` (runways included), iterating the runway adder `t` times
    accumulates EXACTLY `contiguousAugend + t·contiguousAddend` in the contiguous
    reading, under per-segment no-overflow.  This is the headline in the standard
    `a + t·b` shape. -/
theorem runwayAddK_iter_contiguous_clean (gSep k t : Nat) (f : Nat → Bool)
    (hclean : kClean gSep k f)
    (hno : ∀ m, m < k →
      decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep f
        + t * decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f
        < 2 ^ (gSep + 1)) :
    contiguousDecode gSep k (Gate.applyNat (iterGate (runwayAddK gSep k) t) f)
      = contiguousAugend gSep k f + t * contiguousAddend gSep k f := by
  -- Rewrite the no-overflow hypothesis in terms of `segReg_m f = a_m`.
  have hno' : ∀ m, m < k →
      segReg gSep m f
        + t * decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f
        < 2 ^ (gSep + 1) := by
    intro m hm
    have hseg : segReg gSep m f
        = decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep f := by
      unfold segReg
      exact decodeReg_succ_of_top_false _ gSep f (hclean m hm).2.1
    rw [hseg]; exact hno m hm
  rw [runwayAddK_iter_contiguous gSep k t f (IterReady_of_kClean gSep k f hclean) hno',
      contiguousDecode_eq_augend_of_kClean gSep k f hclean]

end FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd
