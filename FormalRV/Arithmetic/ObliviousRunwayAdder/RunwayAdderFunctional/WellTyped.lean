/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional.WellTyped
  ──────────────────────────────────────────────────
  Submodule of `RunwayAdderFunctional` (split out for per-file compile memory).
  Contains §15: k-segment well-typedness — `wellTyped_mono`, the k-segment width,
  and `runwayAddK_wellTyped`.

  Re-exported VERBATIM from the original `RunwayAdderFunctional.lean`; the
  declarations, statements, names, namespace and `open`s are unchanged.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional.KSegment

namespace FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §15. k-segment well-typedness. -/

/-- **WellTyped monotonicity** (local; enlarging the dimension preserves it).
    A self-contained copy so this file needs only the Cuccaro import. -/
theorem wellTyped_mono {dim dim' : Nat} {g : Gate}
    (h : Gate.WellTyped dim g) (hle : dim ≤ dim') : Gate.WellTyped dim' g := by
  induction g with
  | I => show 0 < dim'; have : 0 < dim := h; omega
  | X q => show q < dim'; have : q < dim := h; omega
  | CX a b => obtain ⟨_, _, hab⟩ := h; exact ⟨by omega, by omega, hab⟩
  | CCX a b c =>
      obtain ⟨_, _, _, hab, hac, hbc⟩ := h
      exact ⟨by omega, by omega, by omega, hab, hac, hbc⟩
  | seq g₁ g₂ ih₁ ih₂ => obtain ⟨h₁, h₂⟩ := h; exact ⟨ih₁ h₁, ih₂ h₂⟩

/-- Total qubit width of the k-segment runway adder. -/
def runwayWidthK (gSep k : Nat) : Nat := k * segStride gSep

/-- **`runwayAddK gSep k` is well-typed** at `runwayWidthK gSep k`.  Each segment
    `j < k` fits in `[segBase j, (j+1)·stride) ⊆ [0, k·stride)`. -/
theorem runwayAddK_wellTyped (gSep : Nat) :
    ∀ (k : Nat), 0 < k → Gate.WellTyped (runwayWidthK gSep k) (runwayAddK gSep k) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ m ih =>
      intro _
      refine ⟨?_, ?_⟩
      · -- prefix `runwayAddK gSep m`: WellTyped at `m·stride ≤ (m+1)·stride`.
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm
          show Gate.WellTyped (runwayWidthK gSep 1) Gate.I
          show 0 < runwayWidthK gSep 1
          unfold runwayWidthK segStride; omega
        · have hwm := ih hm
          refine wellTyped_mono hwm ?_
          unfold runwayWidthK
          exact Nat.mul_le_mul_right _ (by omega)
      · -- segment m: width-`(gSep+1)` Cuccaro at base `segBase m`, fits in `(m+1)·stride`.
        show Gate.WellTyped (runwayWidthK gSep (m + 1))
          (cuccaro_n_bit_adder_full (gSep + 1) (segBase gSep m))
        apply cuccaro_n_bit_adder_full_wellTyped (gSep + 1) (segBase gSep m)
        show segBase gSep m + 2 * (gSep + 1) + 1 ≤ runwayWidthK gSep (m + 1)
        unfold runwayWidthK segBase segStride
        have : m * (2 * gSep + 3) + (2 * gSep + 3) = (m + 1) * (2 * gSep + 3) := by ring
        omega

end FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
