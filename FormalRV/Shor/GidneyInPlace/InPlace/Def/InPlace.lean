/-
  FormalRV.Shor.GidneyInPlace.InPlace — in-place from out-of-place (the swap +
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
import FormalRV.Shor.GidneyInPlace.Gate.Def.GateReversible

namespace FormalRV.Shor.GidneyInPlace.InPlace

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.GateReversible (applyNat_reverse_cancel)

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

/-- **The register swap**: swap registers `idxA` and `idxB` qubit-by-qubit over the
    first `n` indices.  (The two registers must be disjoint and each index-injective;
    these are passed as hypotheses to the correctness lemmas.) -/
def swapReg (idxA idxB : Nat → Nat) : Nat → Gate
  | 0 => Gate.I
  | n + 1 => Gate.seq (swapReg idxA idxB n) (swapPair (idxA n) (idxB n))

/-- `swapReg` fixes every position outside the swapped index set. -/
theorem swapReg_frame (idxA idxB : Nat → Nat) (hAB : ∀ i i', idxA i ≠ idxB i') :
    ∀ (n : Nat) (f : Nat → Bool) (p : Nat),
      (∀ i, i < n → p ≠ idxA i ∧ p ≠ idxB i) →
      Gate.applyNat (swapReg idxA idxB n) f p = f p := by
  intro n
  induction n with
  | zero => intro f p _; rfl
  | succ m ih =>
      intro f p hp
      show Gate.applyNat (swapPair (idxA m) (idxB m))
        (Gate.applyNat (swapReg idxA idxB m) f) p = f p
      rw [applyNat_swapPair (idxA m) (idxB m) (hAB m m) _ p]
      obtain ⟨hpa, hpb⟩ := hp m (Nat.lt_succ_self m)
      rw [if_neg hpa, if_neg hpb]
      exact ih f p (fun i hi => hp i (Nat.lt_succ_of_lt hi))

/-- **`swapReg` carries `idxA j` to the old `idxB j` value.** -/
theorem swapReg_idxA (idxA idxB : Nat → Nat) (hAB : ∀ i i', idxA i ≠ idxB i')
    (hAinj : ∀ i i', idxA i = idxA i' → i = i') (hBinj : ∀ i i', idxB i = idxB i' → i = i') :
    ∀ (n : Nat) (f : Nat → Bool) (j : Nat), j < n →
      Gate.applyNat (swapReg idxA idxB n) f (idxA j) = f (idxB j) := by
  intro n
  induction n with
  | zero => intro f j hj; omega
  | succ m ih =>
      intro f j hj
      show Gate.applyNat (swapPair (idxA m) (idxB m))
        (Gate.applyNat (swapReg idxA idxB m) f) (idxA j) = f (idxB j)
      rw [applyNat_swapPair (idxA m) (idxB m) (hAB m m) _ (idxA j)]
      by_cases hjm : j = m
      · rw [hjm, if_pos rfl]
        exact swapReg_frame idxA idxB hAB m f (idxB m)
          (fun i hi => ⟨(hAB i m).symm, fun he => absurd (hBinj i m he.symm) (by omega)⟩)
      · rw [if_neg (fun he => hjm (hAinj j m he)), if_neg (hAB j m)]
        exact ih f j (by omega)

/-- **`swapReg` carries `idxB j` to the old `idxA j` value.** -/
theorem swapReg_idxB (idxA idxB : Nat → Nat) (hAB : ∀ i i', idxA i ≠ idxB i')
    (hAinj : ∀ i i', idxA i = idxA i' → i = i') (hBinj : ∀ i i', idxB i = idxB i' → i = i') :
    ∀ (n : Nat) (f : Nat → Bool) (j : Nat), j < n →
      Gate.applyNat (swapReg idxA idxB n) f (idxB j) = f (idxA j) := by
  intro n
  induction n with
  | zero => intro f j hj; omega
  | succ m ih =>
      intro f j hj
      show Gate.applyNat (swapPair (idxA m) (idxB m))
        (Gate.applyNat (swapReg idxA idxB m) f) (idxB j) = f (idxA j)
      rw [applyNat_swapPair (idxA m) (idxB m) (hAB m m) _ (idxB j)]
      by_cases hjm : j = m
      · rw [hjm, if_neg (fun he => (hAB m m) he.symm), if_pos rfl]
        exact swapReg_frame idxA idxB hAB m f (idxA m)
          (fun i hi => ⟨fun he => absurd (hAinj i m he.symm) (by omega), hAB m i⟩)
      · rw [if_neg (fun he => (hAB m j) he.symm), if_neg (fun he => hjm (hBinj j m he))]
        exact ih f j (by omega)

end FormalRV.Shor.GidneyInPlace.InPlace
