/-
  FormalRV.Shor.GidneyInPlace.E2HisomDischarged — final glue G0:
  H4/H5 with the `hisom` hypothesis ELIMINATED (supplied by the verified `qpeStage_physical_isom`).
  ════════════════════════════════════════════════════════════════════════════

  H4 (`orbit_E2_pmDist_deviation`) and H5 (`coset_route2_success_hybrid_norm_E2`) each carried an
  explicit `hisom` hypothesis (every physical QPE stage is a `pmDist` isometry).  hU closed that
  obligation as the theorem `QpeStageWellTyped.qpeStage_physical_isom` (from `0 < m` plus the
  oracle-family well-typedness `hwtP`, both already present in the bounds).  This file instantiates
  it, removing `hisom` from the public statements while leaving EVERY other realization/support/norm
  hypothesis (`hf_physical`, `hf_runway`, `hf_residue`, `hsupp_res`, `hnormP`/`hnormI`, `hwtP`/…)
  UNCHANGED and the constant `2·m·√(8·numWin/2^cm)` and the actual-side object
  `probability_of_success_E2coset` UNCHANGED.

  The originals are left intact (they keep `hisom`); these `_no_hisom` variants are the
  hisom-free public faces.  Kernel-clean: axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import FormalRV.Shor.GidneyInPlace.Deviation.Proof.E2SuccessDeviation
import FormalRV.Shor.GidneyInPlace.QPE.Spec.QpeStageWellTyped

namespace FormalRV.Shor.GidneyInPlace.E2HisomDischarged

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Shor.Approx (pmDist pmNorm)
open FormalRV.SQIRPort.ApproxTransfer (jointIdx)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate (gidneyInPlaceWithSwap)
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp (qpeStageMap)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq)
open FormalRV.Shor.GidneyInPlace.ControlOracleLift (workMat)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess
  (Shor_final_state_E2coset probability_of_success_E2coset)
open FormalRV.Shor.GidneyInPlace.E2OrbitDeviation (orbit_E2_pmDist_deviation)
open FormalRV.Shor.GidneyInPlace.E2SuccessDeviation (coset_route2_success_hybrid_norm_E2)
open FormalRV.Shor.GidneyInPlace.QpeStageWellTyped (qpeStage_physical_isom)

/-! ## H4 without `hisom`. -/

/-- **H4, `hisom`-free.**  Identical to `orbit_E2_pmDist_deviation` but the per-stage isometry is
    supplied by `qpeStage_physical_isom` (needs only `0 < m` and `hwtP`); all other hypotheses and
    the constant are unchanged. -/
theorem orbit_E2_pmDist_deviation_no_hisom
    (m w bits numWin N cm : Nat) (hm : 0 < m)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat) (mult kInv : Nat → Nat)
    (f_runwayPhysical f_runwayIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwtP : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayPhysical j))
    (hwtI : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hTfamK : ∀ k j addr, TfamK k j addr = tableValue (mult k) N w j addr)
    (hTfamKinv : ∀ k j addr, TfamKinv k j addr = tableValue (kInv k) N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hN1 : 1 < N)
    (hkkinv : ∀ k, (kInv k * mult k) % N = 1 % N)
    (hfit : ∀ (k z : Nat), z < N → (mult k * z) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (hxfit : ∀ (z : Nat), z < N → z + (2 ^ cm - 1) * N < 2 ^ bits)
    (hf_physical : ∀ (k : Nat), k < m → ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayPhysical (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = (FormalRV.Framework.uc_eval (Gate.toUCom (cosetDim w bits)
                (gidneyInPlaceWithSwap w bits (TfamK k) (TfamKinv k) numWin))
              * cosetInputVec w bits N cm z 0) (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_runway : ∀ (k : Nat) (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = cosetInputVec w bits N cm ((mult k * z) % N) 0
              (Fin.cast (E2shor_dim_eq m w bits) y) 0) :
    pmDist (Shor_final_state_E2coset m w bits N cm f_runwayPhysical)
        (Shor_final_state_E2coset m w bits N cm f_runwayIdeal)
      ≤ (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) :=
  orbit_E2_pmDist_deviation m w bits numWin N cm TfamK TfamKinv mult kInv
    f_runwayPhysical f_runwayIdeal hwtP hwtI hTfamK hTfamKinv hw hbits hN hN1 hkkinv hfit hxfit
    (qpeStage_physical_isom m bits (cosetAnc w bits) hm f_runwayPhysical hwtP)
    hf_physical hf_runway

/-! ## H5 without `hisom`. -/

/-- **H5, `hisom`-free.**  The conditional success capstone with the per-stage isometry supplied by
    `qpeStage_physical_isom` (`hm`/`hwtP` already in the bounds).  Every other realization/support/
    norm hypothesis, the constant `2·m·√(8·numWin/2^cm)`, and the actual-side object
    `probability_of_success_E2coset` are unchanged. -/
theorem coset_route2_success_hybrid_norm_E2_no_hisom
    (a r N m w bits numWin cm : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat) (mult kInv : Nat → Nat)
    (f_runwayPhysical f_runwayIdeal f_residueIdeal :
      Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hm : 0 < m) (hbitsPos : 0 < bits)
    (hwtP : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayPhysical j))
    (hwtI : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hwtRes : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_residueIdeal j))
    (hTfamK : ∀ k j addr, TfamK k j addr = tableValue (mult k) N w j addr)
    (hTfamKinv : ∀ k j addr, TfamKinv k j addr = tableValue (kInv k) N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hN1 : 1 < N)
    (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (hkkinv : ∀ k, (kInv k * mult k) % N = 1 % N)
    (hf_physical : ∀ (k : Nat), k < m → ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayPhysical (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = (FormalRV.Framework.uc_eval (Gate.toUCom (cosetDim w bits)
                (gidneyInPlaceWithSwap w bits (TfamK k) (TfamKinv k) numWin))
              * cosetInputVec w bits N cm z 0) (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_runway : ∀ (k : Nat) (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = cosetInputVec w bits N cm ((mult k * z) % N) 0
              (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_residue : ∀ (kstep : Nat), kstep < m →
        ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b
          = if a.val = (if b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N
                then ((mult kstep * (b.val / 2 ^ (cosetAnc w bits))) % N) * 2 ^ (cosetAnc w bits)
                else b.val)
              then 1 else 0)
    (hsupp_res : ∀ (x : Fin (2 ^ m))
        (b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        ¬ (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        Shor_final_state m bits (cosetAnc w bits) f_residueIdeal
            (jointIdx (shorDvd m bits (cosetAnc w bits)) x b) 0 = 0)
    (hnormP : pmNorm (Shor_final_state_E2coset m w bits N cm f_runwayPhysical) ≤ 1)
    (hnormI : pmNorm (Shor_final_state_E2coset m w bits N cm f_runwayIdeal) ≤ 1) :
    probability_of_success_E2coset a r N m w bits cm f_runwayPhysical
      ≥ probability_of_success a r N m bits (cosetAnc w bits) f_residueIdeal
          - 2 * (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) :=
  coset_route2_success_hybrid_norm_E2 a r N m w bits numWin cm TfamK TfamKinv mult kInv
    f_runwayPhysical f_runwayIdeal f_residueIdeal hm hbitsPos hwtP hwtI hwtRes hTfamK hTfamKinv
    hw hbits hN hN1 hMN hkkinv
    (qpeStage_physical_isom m bits (cosetAnc w bits) hm f_runwayPhysical hwtP)
    hf_physical hf_runway hf_residue hsupp_res hnormP hnormI

end FormalRV.Shor.GidneyInPlace.E2HisomDischarged
