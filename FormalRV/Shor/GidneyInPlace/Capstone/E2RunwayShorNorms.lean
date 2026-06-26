/-
  FormalRV.Shor.GidneyInPlace.E2RunwayShorNorms — Route B′ step 2d: the coset-machine final state is a
  sub-unit vector, discharging the capstone's `hnormP`/`hnormI`.
  ════════════════════════════════════════════════════════════════════════════

  `pmNorm (Shor_final_state_E2coset … f) ≤ 1` for ANY well-typed oracle family `f`: the final state is
  `orbitState (qpeStageMap … f) (E2runwayInit …) (m+1)`, every QPE stage is a `pmDist`-isometry fixing
  the zero state (so it preserves `pmNorm`), and `E2runwayInit` is unit-norm (`E2runwayInit_normalized`).
  Instantiating `f := physRunwayOracle …` (well-typed via `physRunwayOracle_wellTyped`) discharges
  `hnormP`; `f := f_runwayIdeal` (via `hwtI`) discharges `hnormI`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorClosure

namespace FormalRV.Shor.GidneyInPlace.E2RunwayShorNorms

open FormalRV.SQIRPort
open FormalRV.Shor.Approx (pmNorm pmDist)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp (qpeStageMap)
open FormalRV.Shor.GidneyInPlace.OrbitState (orbitState)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess
    (E2runwayInit Shor_final_state_E2coset
     Shor_final_state_E2coset_def E2runwayInit_normalized)
open FormalRV.Shor.GidneyInPlace.QpeStageWellTyped (qpeStage_physical_isom)

/-- `QState.cast` maps the all-zeros state to the all-zeros state. -/
private lemma QState.cast_zero_fn {a b : Nat} (h : a = b) :
    QState.cast h (fun _ _ => (0 : ℂ)) = (fun _ _ => 0) := by
  funext i j
  simp [QState.cast]

/-- The QPE stage map sends the zero state to the zero state (it is `uc_eval`-linear). -/
private lemma qpeStageMap_zero_fn (m n anc : Nat)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc)) (k : Nat) :
    qpeStageMap m n anc f k (fun _ _ => 0) = (fun _ _ => 0) := by
  unfold qpeStageMap
  rw [QState.cast_zero_fn]
  funext i j
  simp only [QState.cast, FormalRV.SQIRPort.uc_eval, Matrix.mul_apply, mul_zero,
             Finset.sum_const_zero]

/-- Distance to the zero state is the norm. -/
private lemma pmDist_zero_eq_pmNorm {d : Nat} (phi : QState d) :
    pmDist phi (fun _ _ => 0) = pmNorm phi := by
  simp [pmDist, pmNorm, sub_zero]

/-- Each QPE stage preserves `pmNorm` (it is a `pmDist`-isometry fixing `0`). -/
private lemma qpeStageMap_pmNorm_eq (m n anc : Nat) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (hwt : ∀ j, FormalRV.Framework.UCom.WellTyped (n + anc) (f j))
    (k : Nat) (s : QState (2 ^ m * 2 ^ n * 2 ^ anc)) :
    pmNorm (qpeStageMap m n anc f k s) = pmNorm s := by
  rw [← pmDist_zero_eq_pmNorm (qpeStageMap m n anc f k s),
      ← qpeStageMap_zero_fn m n anc f k,
      qpeStage_physical_isom m n anc hm f hwt k s (fun _ _ => 0)]
  exact pmDist_zero_eq_pmNorm s

/-- The orbit (fold of QPE stages) preserves `pmNorm`. -/
private lemma orbitState_pmNorm_eq (m n anc : Nat) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (hwt : ∀ j, FormalRV.Framework.UCom.WellTyped (n + anc) (f j))
    (init : QState (2 ^ m * 2 ^ n * 2 ^ anc)) (numIter : Nat) :
    pmNorm (orbitState (qpeStageMap m n anc f) init numIter) = pmNorm init := by
  induction numIter with
  | zero => simp [orbitState]
  | succ k ih =>
    simp only [orbitState]
    rw [qpeStageMap_pmNorm_eq m n anc hm f hwt k]
    exact ih

/-- The `E2runwayInit` normalization side-condition `hfit`, from `hMN` (`2^cm·N ≤ 2^bits`) and `N ≥ 2`. -/
private lemma hfit_of_hMN (cm N bits : Nat) (hN1 : 1 < N) (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (hN2 : 2 * N ≤ 2 ^ bits) :
    1 + (2 ^ cm - 1) * N < 2 ^ bits := by
  have hge1 : 1 ≤ 2 ^ cm := Nat.one_le_two_pow
  have hNge2 : 2 ≤ N := hN1
  have hexp : (2 ^ cm - 1) * N = 2 ^ cm * N - N := by
    rw [Nat.sub_mul, Nat.one_mul]
  rw [hexp]
  omega

/-- **Step 2d — the coset machine's final state is sub-unit.**  `pmNorm (Shor_final_state_E2coset … f) ≤ 1`
    for any well-typed oracle `f`; instantiated at `physRunwayOracle`/`f_runwayIdeal` it discharges the
    capstone's `hnormP`/`hnormI`. -/
theorem coset_final_pmNorm_le (m w bits N cm numWin : Nat)
    (hm : 0 < m) (hw : 0 < w) (hbits : numWin * w = bits) (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (f : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f j)) :
    pmNorm (Shor_final_state_E2coset m w bits N cm f) ≤ 1 := by
  rw [Shor_final_state_E2coset_def]
  rw [orbitState_pmNorm_eq m bits (cosetAnc w bits) hm f hwt (E2runwayInit m w bits N cm) (m + 1)]
  have hN_pos : 0 < N := by omega
  rw [E2runwayInit_normalized m w bits numWin N cm hw hbits hN_pos
      (hfit_of_hMN cm N bits hN1 hMN hN2)]

end FormalRV.Shor.GidneyInPlace.E2RunwayShorNorms
