/-
  FormalRV.Shor.GidneyInPlace.ProductAddWrapper
  ────────────────────────────────────────────────
  The two-register product-add WRAPPER (layout/wiring + well-typedness ONLY — NO
  arithmetic correctness, by directive).

  `gidneyProductAddTOf` is ONE Gidney product-add (`b += a·k`): windowed accumulation
  of `Σⱼ Tⱼ[window j of the multiplicand]` into the accumulator at `accBase`, reading
  the multiplicand at `yBase` (via `copyWindow`), through the addend-temp at `tempBase`
  with carry at `tempBase+bits`, using the RELOCATED contiguous two-base adder
  (`relocatedContiguousAdder` / `relocatedAdderCircuit`).  The full in-place multiply
  is two of these plus a LOGICAL relabel `(a,b):=(b,a)` (NOT built here).

  Faithful `cosetDim = 2+2w+3·bits` wiring (see `ProductAddLayout`):
    pass 1 (`b += a·k`):    accBase = bReg = 1+2w+bits,  yBase = aReg = 1+2w
    pass 2 (`a -= b·kInv`):  accBase = aReg = 1+2w,        yBase = bReg = 1+2w+bits
  both with tempBase = 1+2w+2bits, carry = tempBase+bits = 1+2w+3bits.

  Key preservation facts (proved in `RelocatedTransport`, consumed by the eventual
  arithmetic proof): the adder leg leaves the MULTIPLICAND block untouched —
  `relocated_pass1_multiplicand_preserved` (`a` is below the accumulator) and
  `relocated_pass2_multiplicand_preserved` (`b` is in the adder's GAP, via the
  load-bearing `relocated_gap_frame`).  And the wiring validity for both passes is
  `relocated_pass1_valid` / `relocated_pass2_valid`.
-/
import FormalRV.Arithmetic.Adder.RelocatedTransport
import FormalRV.Shor.WindowedModNShor

namespace FormalRV.Shor.GidneyInPlace.ProductAddWrapper

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit (copyWindow lookupReadAt)
open FormalRV.BQAlgo.WindowedModNShor (copyWindow_wellTyped lookupReadAt_wellTyped wellTyped_foldl_seq_range)

/-! ## §1. The gate. -/

/-- One lookup-ADD via the relocated two-base adder: read table `T` into the
    addend-temp `[tempBase, tempBase+bits)`, add into the accumulator
    `[accBase, accBase+bits)`, unread.  (Carry at `tempBase+bits`.) -/
def relocatedLookupAdd (w bits : Nat) (T : Nat → Nat) (accBase tempBase : Nat) : Gate :=
  Gate.seq (Gate.seq (lookupReadAt w (fun k => tempBase + k) bits T)
                     (relocatedAdderCircuit accBase tempBase bits))
           (lookupReadAt w (fun k => tempBase + k) bits T)

/-- One window step: copy window `j` of the multiplicand `@yBase` into the address,
    lookup-add, uncopy. -/
def relocatedProductAddStep (w bits : Nat) (T : Nat → Nat)
    (accBase tempBase yBase j : Nat) : Gate :=
  Gate.seq (Gate.seq (copyWindow w yBase j) (relocatedLookupAdd w bits T accBase tempBase))
           (copyWindow w yBase j)

/-- **The two-register product-add gate** (`b += a·k`), a fold of window steps using
    the relocated contiguous adder; accumulator `@accBase`, multiplicand `@yBase`,
    addend-temp `@tempBase`, carry `tempBase+bits`. -/
def gidneyProductAddTOf (w bits : Nat) (Tfam : Nat → Nat → Nat)
    (accBase tempBase yBase numWin : Nat) : Gate :=
  (List.range numWin).foldl
    (fun g j => Gate.seq g (relocatedProductAddStep w bits (Tfam j) accBase tempBase yBase j)) Gate.I

/-! ## §2. Well-typedness (layout/wiring only). -/

/-- One window step is well-typed, given the wiring bounds:
    multiplicand block `@yBase` above the address zone and inside `dim`; addend-temp
    `@tempBase` above the AND-ancillas; the adder block (up to carry `tempBase+bits`)
    inside `dim`; and `accBase + bits ≤ tempBase` (the relocated adder's `valid`). -/
theorem relocatedProductAddStep_wellTyped (w bits : Nat) (T : Nat → Nat)
    (accBase tempBase yBase j numWin dim : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin)
    (hv : accBase + bits ≤ tempBase)
    (hyBase : 2 * w < yBase) (hyfit : yBase + bits ≤ dim)
    (htemp : 2 * w < tempBase) (htfit : tempBase + bits + 1 ≤ dim) :
    Gate.WellTyped dim (relocatedProductAddStep w bits T accBase tempBase yBase j) := by
  have hjwi : ∀ i, i < w → j * w + i < bits := by
    intro i hi
    calc j * w + i < j * w + w := by omega
      _ = (j + 1) * w := by ring
      _ ≤ numWin * w := Nat.mul_le_mul_right w hj
      _ = bits := hbits
  have hcw : Gate.WellTyped dim (copyWindow w yBase j) :=
    copyWindow_wellTyped w yBase j dim (by omega)
      (fun i hi => by have := hjwi i hi; omega) (fun i hi => by omega)
  have hlook : Gate.WellTyped dim (lookupReadAt w (fun k => tempBase + k) bits T) :=
    lookupReadAt_wellTyped w bits (fun k => tempBase + k) T dim hw (by omega)
      (fun k hk => ⟨by show tempBase + k < dim; omega,
                    by show ulookup_and_idx (w - 1) ≠ tempBase + k; unfold ulookup_and_idx; omega⟩)
  have hadd : Gate.WellTyped dim (relocatedAdderCircuit accBase tempBase bits) :=
    relocated_wellTyped bits accBase tempBase dim hv (by omega)
  unfold relocatedProductAddStep relocatedLookupAdd
  exact ⟨⟨hcw, ⟨⟨hlook, hadd⟩, hlook⟩⟩, hcw⟩

/-- The full product-add gate is well-typed (fold of well-typed steps). -/
theorem gidneyProductAddTOf_wellTyped (w bits : Nat) (Tfam : Nat → Nat → Nat)
    (accBase tempBase yBase numWin dim : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hv : accBase + bits ≤ tempBase)
    (hyBase : 2 * w < yBase) (hyfit : yBase + bits ≤ dim)
    (htemp : 2 * w < tempBase) (htfit : tempBase + bits + 1 ≤ dim) :
    Gate.WellTyped dim (gidneyProductAddTOf w bits Tfam accBase tempBase yBase numWin) := by
  unfold gidneyProductAddTOf
  refine wellTyped_foldl_seq_range _ numWin dim (by omega) (fun j hj => ?_)
  exact relocatedProductAddStep_wellTyped w bits (Tfam j) accBase tempBase yBase j numWin dim
    hw hbits hj hv hyBase hyfit htemp htfit

/-! ## §3. Faithful-layout wiring: both passes well-typed at `cosetDim = 2+2w+3·bits`. -/

/-- Pass 1 (`b += a·k`): accumulator `b @ 1+2w+bits`, multiplicand `a @ 1+2w`,
    temp `@ 1+2w+2bits` — well-typed at `cosetDim`. -/
theorem gidneyProductAdd_pass1_wellTyped (w bits : Nat) (Tfam : Nat → Nat → Nat) (numWin : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) :
    Gate.WellTyped (2 + 2 * w + 3 * bits)
      (gidneyProductAddTOf w bits Tfam (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin) :=
  gidneyProductAddTOf_wellTyped w bits Tfam (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w)
    numWin (2 + 2 * w + 3 * bits) hw hbits (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Pass 2 (`a -= b·kInv`): accumulator `a @ 1+2w`, multiplicand `b @ 1+2w+bits`,
    temp `@ 1+2w+2bits` (the spread case the packed adder could not host) —
    well-typed at `cosetDim`. -/
theorem gidneyProductAdd_pass2_wellTyped (w bits : Nat) (Tfam : Nat → Nat → Nat) (numWin : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) :
    Gate.WellTyped (2 + 2 * w + 3 * bits)
      (gidneyProductAddTOf w bits Tfam (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin) :=
  gidneyProductAddTOf_wellTyped w bits Tfam (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits)
    numWin (2 + 2 * w + 3 * bits) hw hbits (by omega) (by omega) (by omega) (by omega) (by omega)

end FormalRV.Shor.GidneyInPlace.ProductAddWrapper
