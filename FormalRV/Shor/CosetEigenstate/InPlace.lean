/-
  FormalRV.Shor.CosetEigenstate.InPlace — in-place from out-of-place (the swap +
  uncompute trick), generically.
  ════════════════════════════════════════════════════════════════════════════

  The Shor oracle must be IN-PLACE: `|x⟩ → |a·x⟩` on one register, so the iterates
  compose.  The standard construction from an OUT-OF-PLACE multiplier
  (`|x⟩|0⟩ → |x⟩|a·x⟩`) is

      inPlaceMul = mulFwd ; swap ; reverse mulInv

  where `mulFwd` multiplies by `a` into a scratch register, `swap` exchanges data
  and scratch, and `reverse mulInv` un-computes the old value using the out-of-place
  multiplier for `a⁻¹` (since `a⁻¹·(a·x) = x`):

      |x⟩|0⟩  --mulFwd-->  |x⟩|a·x⟩  --swap-->  |a·x⟩|x⟩  --rev mulInv-->  |a·x⟩|0⟩.

  **This file proves the trick GENERICALLY and REUSABLY**: the un-compute leg is
  discharged by pure REVERSIBILITY (`applyNat_reverse_cancel`) — NO arithmetic — so
  the whole arithmetic content is isolated in a single `hchain` hypothesis (the
  round-trip of `mulFwd`/`swap`/`mulInv`), to be discharged per multiplier (Cuccaro,
  runway-coset, …).  Works for ANY out-of-place multiplier pair.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.GateReversible

namespace FormalRV.Shor.CosetEigenstate.InPlace

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.CosetEigenstate.GateReversible (applyNat_reverse_cancel)

/-- The in-place multiplier built from out-of-place pieces: `mulFwd ; swap ;
    reverse mulInv`.  Generic in the three gates. -/
def inPlaceMul (mulFwd swap mulInv : Gate) : Gate :=
  Gate.seq mulFwd (Gate.seq swap (GateReversible.Gate.reverse mulInv))

/-- **The in-place trick (generic, reusable) — correctness from one round-trip.**
    If `mulFwd` then `swap` carries the input state `s0` to exactly the state that
    `mulInv` produces from the desired output `sFinal`, then `inPlaceMul` carries
    `s0` to `sFinal`.  The un-compute leg is PURE reversibility; all arithmetic is
    in `hchain`. -/
theorem inPlaceMul_correct (mulFwd swap mulInv : Gate) (dim : Nat)
    (hwt : Gate.WellTyped dim mulInv) (s0 sFinal : Nat → Bool)
    (hchain : Gate.applyNat swap (Gate.applyNat mulFwd s0) = Gate.applyNat mulInv sFinal) :
    Gate.applyNat (inPlaceMul mulFwd swap mulInv) s0 = sFinal := by
  show Gate.applyNat (GateReversible.Gate.reverse mulInv)
    (Gate.applyNat swap (Gate.applyNat mulFwd s0)) = sFinal
  rw [hchain]
  exact applyNat_reverse_cancel mulInv dim hwt sFinal

/-! ## §2. The register swap (the `swap` leg). -/

/-- Swap two qubits `a`, `b` with the standard 3-CNOT gadget. -/
def swapPair (a b : Nat) : Gate :=
  Gate.seq (Gate.CX a b) (Gate.seq (Gate.CX b a) (Gate.CX a b))

/-- **`swapPair a b` exchanges qubits `a` and `b`** (and fixes the rest). -/
theorem applyNat_swapPair (a b : Nat) (h : a ≠ b) (f : Nat → Bool) (p : Nat) :
    Gate.applyNat (swapPair a b) f p =
      if p = a then f b else if p = b then f a else f p := by
  show Gate.applyNat (Gate.CX a b)
    (Gate.applyNat (Gate.CX b a) (Gate.applyNat (Gate.CX a b) f)) p = _
  simp only [Gate.applyNat, update]
  by_cases hpa : p = a
  · by_cases hpb : p = b
    · simp_all
    · cases hfa : f a <;> cases hfb : f b <;> simp_all
  · by_cases hpb : p = b
    · cases hfa : f a <;> cases hfb : f b <;> simp_all
    · simp_all

end FormalRV.Shor.CosetEigenstate.InPlace
