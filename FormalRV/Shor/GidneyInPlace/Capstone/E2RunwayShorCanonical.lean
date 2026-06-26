/-
  FormalRV.Shor.GidneyInPlace.E2RunwayShorCanonical — the coset/runway Shor bound with `hf_residue`
  WEAKENED to canonical-only data (Route B′), and the fully-UNCONDITIONAL κ-floor consequence.
  ════════════════════════════════════════════════════════════════════════════

  Mirrors the capstone chain (`E2SuccessDeviation` H5 + `E2HisomDischarged` G0 +
  `E2RunwayShorCapstone`), but threads the WEAKENED residue-oracle hypotheses
  (`hf_res_can` + `hf_res_pres`, from `E2ResidueEmbedCanonical`) instead of the full-matrix
  `hf_residue` (off-canonical identity).  The deviation half (`E2coset_prob_success_diff_le`) is
  reused verbatim; only the P1.3 success bridge is swapped for its canonical variant.

  The point: these weakened hypotheses ARE satisfied by a genuine `ModMulImpl` multiplier
  (`IdealResidueOracle.idealResidueFamily`), unlike the off-canonical-identity form — so this is the
  capstone shape that an actually-constructible ideal residue oracle can discharge.

  `gidney_inplace_coset_shor_succeeds_unconditional_canonical` chains the canonical capstone with
  `Shor_correct_var` (turning `prob(f_residueIdeal)` into the explicit Shor floor `κ/(log₂N)⁴`, given
  `BasicSetting` + `ModMulImpl`), yielding the coset machine's bound `≥ κ/(log₂N)⁴ − 2m√(8numWin/2^cm)`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.E2ResidueEmbedCanonical
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorUnconditional
import FormalRV.Shor.GidneyInPlace.Deviation.Proof.E2SuccessDeviation

namespace FormalRV.Shor.GidneyInPlace.E2RunwayShorCanonical

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.Shor.Approx (pmNorm)
open FormalRV.SQIRPort.ApproxTransfer (jointIdx)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq)
open FormalRV.Shor.GidneyInPlace.ControlOracleLift (workMat)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess (Shor_final_state_E2coset probability_of_success_E2coset)
open FormalRV.Shor.GidneyInPlace.E2PhysicalRealization (physRunwayOracle hf_physical_runway)
open FormalRV.Shor.GidneyInPlace.E2SuccessDeviation (E2coset_prob_success_diff_le)
open FormalRV.Shor.GidneyInPlace.QpeStageWellTyped (qpeStage_physical_isom)
open FormalRV.Shor.GidneyInPlace.E2ResidueEmbedCanonical (probability_of_success_E2coset_eq_canonical)
open FormalRV.Shor.GidneyInPlace.E2RunwayShorCapstone (physRunwayOracle_wellTyped)

/-- **The coset/runway Shor bound (canonical-only residue hypotheses).**  Identical conclusion to
    `gidney_inplace_coset_shor_succeeds_hybrid`, but `hf_residue` is replaced by the WEAKENED
    `hf_res_can` (canonical multiply) + `hf_res_pres` (canonical preservation) — the form a real
    `ModMulImpl` multiplier satisfies.  The physical-oracle well-typedness `hwtP` is discharged
    internally (`physRunwayOracle_wellTyped`); the per-stage isometry by `qpeStage_physical_isom`. -/
theorem gidney_inplace_coset_shor_succeeds_canonical
    (a r N m w bits numWin cm : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat) (mult kInv : Nat → Nat)
    (f_runwayIdeal f_residueIdeal :
      Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hm : 0 < m) (hbitsPos : 0 < bits)
    (hwtI : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hwtRes : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_residueIdeal j))
    (hTfamK : ∀ k j addr, TfamK k j addr = tableValue (mult k) N w j addr)
    (hTfamKinv : ∀ k j addr, TfamKinv k j addr = tableValue (kInv k) N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hN1 : 1 < N)
    (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (hkkinv : ∀ k, (kInv k * mult k) % N = 1 % N)
    (hf_runway : ∀ (k : Nat) (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = cosetInputVec w bits N cm ((mult k * z) % N) 0
              (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_res_can : ∀ (kstep : Nat), kstep < m →
        ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b
          = if a.val = ((mult kstep * (b.val / 2 ^ (cosetAnc w bits))) % N) * 2 ^ (cosetAnc w bits)
              then 1 else 0)
    (hf_res_pres : ∀ (kstep : Nat), kstep < m →
        ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        (a.val % 2 ^ (cosetAnc w bits) = 0 ∧ a.val / 2 ^ (cosetAnc w bits) < N) →
        ¬ (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b = 0)
    (hsupp_res : ∀ (x : Fin (2 ^ m))
        (b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        ¬ (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        Shor_final_state m bits (cosetAnc w bits) f_residueIdeal
            (jointIdx (shorDvd m bits (cosetAnc w bits)) x b) 0 = 0)
    (hnormP : pmNorm (Shor_final_state_E2coset m w bits N cm
        (physRunwayOracle m w bits numWin TfamK TfamKinv)) ≤ 1)
    (hnormI : pmNorm (Shor_final_state_E2coset m w bits N cm f_runwayIdeal) ≤ 1) :
    probability_of_success_E2coset a r N m w bits cm
        (physRunwayOracle m w bits numWin TfamK TfamKinv)
      ≥ probability_of_success a r N m bits (cosetAnc w bits) f_residueIdeal
          - 2 * (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) := by
  have hbridge := probability_of_success_E2coset_eq_canonical a r N m w bits cm hm hbitsPos mult hN hN1
    numWin hw hbits hMN f_runwayIdeal f_residueIdeal hwtI hwtRes
    (fun kstep _ z hz y => hf_runway kstep z hz y) hf_res_can hf_res_pres hsupp_res
  have hdiff := E2coset_prob_success_diff_le a r N m w bits numWin cm TfamK TfamKinv mult kInv
    (physRunwayOracle m w bits numWin TfamK TfamKinv) f_runwayIdeal
    (fun j => physRunwayOracle_wellTyped m w bits numWin TfamK TfamKinv hw hbits j) hwtI
    hTfamK hTfamKinv hw hbits hN hN1 hMN hkkinv
    (qpeStage_physical_isom m bits (cosetAnc w bits) hm
      (physRunwayOracle m w bits numWin TfamK TfamKinv)
      (fun j => physRunwayOracle_wellTyped m w bits numWin TfamK TfamKinv hw hbits j))
    (hf_physical_runway m w bits numWin N cm TfamK TfamKinv)
    hf_runway hnormP hnormI
  rw [hbridge] at hdiff
  linarith [(abs_le.mp hdiff).1]

/-- **★ THE COSET/RUNWAY SHOR BOUND AGAINST THE EXPLICIT Shor FLOOR `κ/(log₂N)⁴`, FROM CANONICAL-ONLY
    RESIDUE DATA (Route B′). ★**  The canonical capstone with `prob(f_residueIdeal)` discharged to the
    Shor floor via `Shor_correct_var` (given `BasicSetting` + `ModMulImpl`).  Crucially, the residue
    hypotheses are the WEAKENED canonical form (`hf_res_can`/`hf_res_pres`), which the constructible
    exact multiplier `IdealResidueOracle.idealResidueFamily` satisfies (a genuine `ModMulImpl` at the
    coset dimension).  Remaining inputs are the runway-ideal realization + norms + the standard
    `BasicSetting`. -/
theorem gidney_inplace_coset_shor_succeeds_unconditional_canonical
    (a r N m w bits numWin cm : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat) (mult kInv : Nat → Nat)
    (f_runwayIdeal f_residueIdeal :
      Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hm : 0 < m) (hbitsPos : 0 < bits)
    (hwtI : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hwtRes : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_residueIdeal j))
    (hTfamK : ∀ k j addr, TfamK k j addr = tableValue (mult k) N w j addr)
    (hTfamKinv : ∀ k j addr, TfamKinv k j addr = tableValue (kInv k) N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hN1 : 1 < N)
    (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (hkkinv : ∀ k, (kInv k * mult k) % N = 1 % N)
    (hf_runway : ∀ (k : Nat) (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = cosetInputVec w bits N cm ((mult k * z) % N) 0
              (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_res_can : ∀ (kstep : Nat), kstep < m →
        ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b
          = if a.val = ((mult kstep * (b.val / 2 ^ (cosetAnc w bits))) % N) * 2 ^ (cosetAnc w bits)
              then 1 else 0)
    (hf_res_pres : ∀ (kstep : Nat), kstep < m →
        ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        (a.val % 2 ^ (cosetAnc w bits) = 0 ∧ a.val / 2 ^ (cosetAnc w bits) < N) →
        ¬ (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b = 0)
    (hsupp_res : ∀ (x : Fin (2 ^ m))
        (b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        ¬ (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        Shor_final_state m bits (cosetAnc w bits) f_residueIdeal
            (jointIdx (shorDvd m bits (cosetAnc w bits)) x b) 0 = 0)
    (hnormP : pmNorm (Shor_final_state_E2coset m w bits N cm
        (physRunwayOracle m w bits numWin TfamK TfamKinv)) ≤ 1)
    (hnormI : pmNorm (Shor_final_state_E2coset m w bits N cm f_runwayIdeal) ≤ 1)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m bits)
    (h_mmi : FormalRV.SQIRPort.ModMulImpl a N bits (cosetAnc w bits) f_residueIdeal) :
    probability_of_success_E2coset a r N m w bits cm
        (physRunwayOracle m w bits numWin TfamK TfamKinv)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
          - 2 * (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) := by
  have hcap := gidney_inplace_coset_shor_succeeds_canonical a r N m w bits numWin cm
    TfamK TfamKinv mult kInv f_runwayIdeal f_residueIdeal hm hbitsPos hwtI hwtRes hTfamK hTfamKinv
    hw hbits hN hN1 hMN hkkinv hf_runway hf_res_can hf_res_pres hsupp_res hnormP hnormI
  have hideal : probability_of_success a r N m bits (cosetAnc w bits) f_residueIdeal
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4 :=
    FormalRV.SQIRPort.Shor_correct_var a r N m bits (cosetAnc w bits) f_residueIdeal
      h_basic h_mmi (fun i _ => hwtRes i)
  linarith

end FormalRV.Shor.GidneyInPlace.E2RunwayShorCanonical
