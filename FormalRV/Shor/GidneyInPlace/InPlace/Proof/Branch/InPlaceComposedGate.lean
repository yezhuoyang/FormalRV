/-
  FormalRV.Shor.GidneyInPlace.InPlaceComposedGate
  ─────────────────────────────────────────────────
  PACKAGING checkpoint 2a: the composed in-place gate `multiply ; swap`.

      gidneyInPlaceWithSwap := Gate.seq gidneyTwoRegInPlaceCosetMul swapAB

  `Gate.seq g₁ g₂` runs `g₁` FIRST, then `g₂` (`Gate.applyNat_seq` /
  `gateToPerm_seq` both compose as `g₂ ∘ g₁`), so this is exactly "multiply, then
  swap".  The faithful two-register multiplier leaves the product in the b-block (a
  cleared); the final `swapAB` moves the product back onto the a-block, so the
  single-register contract can read input AND output from the SAME physical a-block,
  with the b-block as the cleared internal ancilla.

  This file states ONLY the gate, its `rfl` unfold guard (so the `seq` order can never
  be confused), and its well-typedness — the structured agree-off is the next brick.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Def.InPlaceSwapBlocks

namespace FormalRV.Shor.GidneyInPlace.InPlaceComposedGate

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.GidneyTwoRegInPlace
  (gidneyTwoRegInPlaceCosetMul gidneyTwoRegInPlaceCosetMul_wellTyped)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceSwapBlocks (swapAB swapAB_wellTyped)

/-- **The in-place coset multiplier WITH the final a↔b block swap.**  Run the faithful
    two-register multiplier (`b ← k·a`, then the reverse leg clears `a`), THEN swap the
    blocks so the product lands back in the a-block (the contract's input block) and the
    b-block becomes the cleared ancilla.  `Gate.seq g₁ g₂` runs `g₁` first then `g₂`, so
    this is "multiply, then swap". -/
def gidneyInPlaceWithSwap (w bits : Nat) (TfamK TfamKinv : Nat → Nat → Nat) (numWin : Nat) : Gate :=
  Gate.seq (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) (swapAB w bits)

/-- **`rfl` unfold guard** — pins the `Gate.seq` order (multiply FIRST, then swap) so it
    can never be silently reversed. -/
@[simp] theorem gidneyInPlaceWithSwap_unfold (w bits : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (numWin : Nat) :
    gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin
      = Gate.seq (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) (swapAB w bits) := rfl

/-- The composed gate is well-typed at `cosetDim w bits` (both legs are: the multiplier
    via `gidneyTwoRegInPlaceCosetMul_wellTyped`, the swap via `swapAB_wellTyped`). -/
theorem gidneyInPlaceWithSwap_wellTyped (w bits : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (numWin : Nat) (hw : 0 < w) (hbits : numWin * w = bits) :
    Gate.WellTyped (cosetDim w bits) (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin) :=
  ⟨gidneyTwoRegInPlaceCosetMul_wellTyped w bits TfamK TfamKinv numWin hw hbits,
   swapAB_wellTyped w bits⟩

end FormalRV.Shor.GidneyInPlace.InPlaceComposedGate
