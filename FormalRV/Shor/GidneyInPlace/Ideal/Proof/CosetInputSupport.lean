/-
  FormalRV.Shor.GidneyInPlace.CosetInputSupport — P1.0 of the hybrid route:
  the raw-index SUPPORT / AMPLITUDE characterization of `cosetInputVec z 0`.
  ════════════════════════════════════════════════════════════════════════════

  The clean ideal shift P1.1 (`idealFi · cosetInputVec z 0 = cosetInputVec ((mult·z)%N) 0`)
  is proved by tracking, basis-index by basis-index, which raw indices carry nonzero amplitude
  in `cosetInputVec` and what that amplitude is.  This file packages exactly that — purely an
  input-state fact, NO gate dynamics, NO bad sets, NO physical gate.

  `cosetInputVec w bits N cm xa xb = cosetInputTwoReg …` (InPlaceNormBound.lean:55) is, at a raw
  basis index `idx`, the scratch-clean-gated PRODUCT of the two block coset-window indicators:
  the a-block decode in `cosetWindow xa` and the b-block decode in `cosetWindow xb`, each with
  amplitude `1/√2^cm`.  We expose:

    • `inSupport`                         — the support predicate (scratch clean ∧ a-decode ∈
                                            window xa ∧ b-decode ∈ window xb);
    • `cosetInputVec_amp`                 — the FULL characterization: amplitude is
                                            `(1/√2^cm)·(1/√2^cm)` on `inSupport`, else `0`;
    • `cosetInputVec_ne_zero_iff`         — nonzero ⟺ `inSupport`;
    • `cosetInputVec_eq_zero_of_not_inSupport` — off support ⇒ `0`.

  These repackage the existing `InPlaceLeg1.cosetInputTwoReg_support_nonzero` (forward support)
  and `InPlaceComposedAgree.cosetInputVec_nonzero_eq` (on-support amplitude) into the single
  characterization P1.1 consumes.  Stated in the native `Fin (2^cosetDim w bits)` convention;
  the cast bridge to the `E2shorZ`/workDim register (`Fin.cast (E2shor_dim_eq …)`) is applied at
  the embedding layer (P1.2 / H3.2), not here.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceComposedAgree

namespace FormalRV.Shor.GidneyInPlace.CosetInputSupport

open FormalRV.Framework (nat_to_funbool)
open FormalRV.BQAlgo (decodeReg)
open FormalRV.Shor.WindowedCircuit (decodeReg_lt_two_pow)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg (aBase bBase scratchClean cosetInputTwoReg)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree (cosetInputVec_nonzero_eq)
open FormalRV.Shor.GidneyInPlace.InPlaceLeg1 (cosetInputTwoReg_support_nonzero)
open scoped Classical

/-- **The `cosetInputVec` support predicate at a raw basis index.**  `idx` carries amplitude in
    `cosetInputVec xa xb` exactly when its bit-function is scratch-clean and BOTH block decodes
    lie in their coset windows (a-block ∈ `cosetWindow xa`, b-block ∈ `cosetWindow xb`). -/
def inSupport (w bits N cm xa xb : Nat) (idx : Fin (2 ^ cosetDim w bits)) : Prop :=
  scratchClean w bits (nat_to_funbool (cosetDim w bits) idx.val)
  ∧ (⟨decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val),
      decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xa
  ∧ (⟨decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val),
      decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xb

/-- **The full amplitude characterization.**  At every raw basis index, `cosetInputVec xa xb` is
    `(1/√2^cm)·(1/√2^cm)` on `inSupport` and `0` off it — the scratch-clean-gated product of the
    two block window indicators, restated as a single `if inSupport`. -/
theorem cosetInputVec_amp (w bits N cm xa xb : Nat) (idx : Fin (2 ^ cosetDim w bits)) :
    cosetInputVec w bits N cm xa xb idx 0
      = if inSupport w bits N cm xa xb idx then
          ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) * ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ)
        else 0 := by
  classical
  show cosetInputTwoReg w bits N cm xa xb idx 0 = _
  have hV : cosetInputTwoReg w bits N cm xa xb idx 0
      = (if scratchClean w bits (nat_to_funbool (cosetDim w bits) idx.val) then
          (if (⟨decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val),
              decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xa
            then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
          * (if (⟨decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val),
              decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xb
            then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
        else 0) := rfl
  rw [hV]
  unfold inSupport
  by_cases hsc : scratchClean w bits (nat_to_funbool (cosetDim w bits) idx.val)
  · by_cases hA : (⟨decodeReg (fun i => aBase w + i) bits (nat_to_funbool (cosetDim w bits) idx.val),
        decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xa
    · by_cases hB : (⟨decodeReg (fun i => bBase w bits + i) bits (nat_to_funbool (cosetDim w bits) idx.val),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xb
      · rw [if_pos hsc, if_pos hA, if_pos hB, if_pos ⟨hsc, hA, hB⟩]
      · rw [if_pos hsc, if_pos hA, if_neg hB, mul_zero, if_neg (fun h => hB h.2.2)]
    · rw [if_pos hsc, if_neg hA, zero_mul, if_neg (fun h => hA h.2.1)]
  · rw [if_neg hsc, if_neg (fun h => hsc h.1)]

/-- The on-support amplitude `1/√2^cm` is nonzero (`2^cm > 0`). -/
theorem cosetAmp_ne_zero (cm : Nat) :
    ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) * ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) ≠ 0 := by
  have hpos : (0 : ℝ) < 1 / Real.sqrt (2 ^ cm) := by
    apply div_pos one_pos
    exact Real.sqrt_pos.mpr (by positivity)
  have : ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  exact mul_ne_zero this this

/-- **Nonzero ⟺ in support.** -/
theorem cosetInputVec_ne_zero_iff (w bits N cm xa xb : Nat) (idx : Fin (2 ^ cosetDim w bits)) :
    cosetInputVec w bits N cm xa xb idx 0 ≠ 0 ↔ inSupport w bits N cm xa xb idx := by
  rw [cosetInputVec_amp]
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    exact h rfl
  · intro h
    rw [if_pos h]
    exact cosetAmp_ne_zero cm

/-- **Off support ⇒ amplitude 0.** -/
theorem cosetInputVec_eq_zero_of_not_inSupport (w bits N cm xa xb : Nat)
    (idx : Fin (2 ^ cosetDim w bits)) (h : ¬ inSupport w bits N cm xa xb idx) :
    cosetInputVec w bits N cm xa xb idx 0 = 0 := by
  rw [cosetInputVec_amp, if_neg h]

/-- **On support ⇒ the exact amplitude `(1/√2^cm)²`.**  (The backward direction, the form P1.1
    uses to evaluate the shifted target column.) -/
theorem cosetInputVec_eq_of_inSupport (w bits N cm xa xb : Nat)
    (idx : Fin (2 ^ cosetDim w bits)) (h : inSupport w bits N cm xa xb idx) :
    cosetInputVec w bits N cm xa xb idx 0
      = ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) * ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) := by
  rw [cosetInputVec_amp, if_pos h]

end FormalRV.Shor.GidneyInPlace.CosetInputSupport
