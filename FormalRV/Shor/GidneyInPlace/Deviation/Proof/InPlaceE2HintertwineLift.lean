/-
  FormalRV.Shor.GidneyInPlace.InPlaceE2HintertwineLift — F2 brick 2: the E₂
  controlled-oracle intertwining lift.
  ════════════════════════════════════════════════════════════════════════════

  Generalizes `ControlOracleLift.controlled_shifted_oracle_hintertwine` over an ABSTRACT embedding
  `(Ephys, Emat)` with its acts-via-matrix law `hEacts`, then instantiates it for the
  canonical-zeroed E₂ embedding (`E2shorZ`, `E2matZ`) fed by `E2_hwork_int` (brick 1).  The proof is
  the original verbatim with `cosetEmbedMat → Emat`, `E_phys → Ephys`, `E_phys_acts → hEacts` — pure
  structural lifting (controlled index + `workMat` intertwining), NO re-proof of the matrix identity.

  `hc_local` needs NO E₂ version: `ControlOracleLift.controlled_shifted_oracle_hc_local` is
  embedding-free (purely `workMat` good-set preservation), so it is reused as-is.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Deviation.Proof.InPlaceE2HworkInt

namespace FormalRV.Shor.GidneyInPlace.InPlaceE2HintertwineLift

open FormalRV.Framework FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer (jointIdx)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp (qpeStageMap)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (qpeStage_oracle_jointIdx workDim_eq)
open FormalRV.Shor.GidneyInPlace.ControlOracleLift (workMat)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceE2HworkInt (E2matZ)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedCanon (E2shorZ E2shorZ_acts)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)

/-- **Generic controlled-oracle intertwining lift.**  Over any embedding `Ephys` with matrix `Emat`
    (`hEacts`: `Ephys psi (jointIdx x yy) = ∑ yp, Emat yy yp · psi (jointIdx x yp)`), the off-`bad_step`
    work-matrix identity `hwork_int` lifts to the controlled-oracle intertwining
    `O_c ∘ Ephys = Ephys ∘ O_i` off `bad_step`.  Original `controlled_shifted_oracle_hintertwine` is
    the `cosetEmbedMat`/`E_phys` instance; here it is the parameter. -/
theorem controlled_oracle_hintertwine_generic (m n anc k : Nat) (hk : k < m)
    (f_coset f_ideal : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (hwt_c : ∀ j, UCom.WellTyped (n + anc) (f_coset j))
    (hwt_i : ∀ j, UCom.WellTyped (n + anc) (f_ideal j))
    (Ephys : QState (2 ^ m * 2 ^ n * 2 ^ anc) → QState (2 ^ m * 2 ^ n * 2 ^ anc))
    (Emat : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) → Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) → ℂ)
    (hEacts : ∀ (psi : QState (2 ^ m * 2 ^ n * 2 ^ anc)) (x : Fin (2 ^ m))
        (yy : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)),
        Ephys psi (jointIdx (shorDvd m n anc) x yy) 0
          = ∑ yp, Emat yy yp * psi (jointIdx (shorDvd m n anc) x yp) 0)
    (bad_step : Finset (Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)))
    (hwork_int : ∀ y, y ∉ bad_step → ∀ y2 : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m),
        (∑ yp, workMat m n anc k f_coset y yp * Emat yp y2)
          = (∑ yp, Emat y yp * workMat m n anc k f_ideal yp y2)) :
    ∀ (phi : QState (2 ^ m * 2 ^ n * 2 ^ anc)) (x : Fin (2 ^ m))
      (y : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)), y ∉ bad_step →
      (qpeStageMap m n anc f_coset k (Ephys phi)) (jointIdx (shorDvd m n anc) x y) 0
        = (Ephys (qpeStageMap m n anc f_ideal k phi)) (jointIdx (shorDvd m n anc) x y) 0 := by
  classical
  intro phi x y hy
  rw [qpeStage_oracle_jointIdx m n anc k hk f_coset hwt_c (Ephys phi) x y]
  rw [hEacts (qpeStageMap m n anc f_ideal k phi) x y]
  by_cases hcb : controlBit m k hk x
  · rw [if_pos hcb]
    rw [Finset.sum_congr rfl (fun yp _ =>
      by rw [hEacts phi x yp] :
      ∀ yp ∈ Finset.univ,
        Framework.uc_eval (f_coset (revIndex m k))
            (Fin.cast (workDim_eq m n anc) y) (Fin.cast (workDim_eq m n anc) yp)
          * Ephys phi (jointIdx (shorDvd m n anc) x yp) 0
        = Framework.uc_eval (f_coset (revIndex m k))
            (Fin.cast (workDim_eq m n anc) y) (Fin.cast (workDim_eq m n anc) yp)
          * ∑ y2, Emat yp y2 * phi (jointIdx (shorDvd m n anc) x y2) 0)]
    rw [Finset.sum_congr rfl (fun yp _ =>
      by rw [qpeStage_oracle_jointIdx m n anc k hk f_ideal hwt_i phi x yp, if_pos hcb] :
      ∀ yp ∈ Finset.univ,
        Emat y yp * qpeStageMap m n anc f_ideal k phi (jointIdx (shorDvd m n anc) x yp) 0
        = Emat y yp * ∑ y2, Framework.uc_eval (f_ideal (revIndex m k))
              (Fin.cast (workDim_eq m n anc) yp) (Fin.cast (workDim_eq m n anc) y2)
              * phi (jointIdx (shorDvd m n anc) x y2) 0)]
    have hL : (∑ yp, workMat m n anc k f_coset y yp
                * ∑ y2, Emat yp y2 * phi (jointIdx (shorDvd m n anc) x y2) 0)
        = ∑ y2, (∑ yp, workMat m n anc k f_coset y yp * Emat yp y2)
                * phi (jointIdx (shorDvd m n anc) x y2) 0 := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y2 _ => Finset.sum_congr rfl (fun yp _ => by ring))
    have hR : (∑ yp, Emat y yp * ∑ y2, workMat m n anc k f_ideal yp y2
                    * phi (jointIdx (shorDvd m n anc) x y2) 0)
        = ∑ y2, (∑ yp, Emat y yp * workMat m n anc k f_ideal yp y2)
                * phi (jointIdx (shorDvd m n anc) x y2) 0 := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y2 _ => Finset.sum_congr rfl (fun yp _ => by ring))
    show (∑ yp, Framework.uc_eval (f_coset (revIndex m k))
            (Fin.cast (workDim_eq m n anc) y) (Fin.cast (workDim_eq m n anc) yp)
            * ∑ y2, Emat yp y2 * phi (jointIdx (shorDvd m n anc) x y2) 0)
        = ∑ yp, Emat y yp
            * ∑ y2, Framework.uc_eval (f_ideal (revIndex m k))
                (Fin.cast (workDim_eq m n anc) yp) (Fin.cast (workDim_eq m n anc) y2)
                * phi (jointIdx (shorDvd m n anc) x y2) 0
    rw [show (∑ yp, Framework.uc_eval (f_coset (revIndex m k))
            (Fin.cast (workDim_eq m n anc) y) (Fin.cast (workDim_eq m n anc) yp)
            * ∑ y2, Emat yp y2 * phi (jointIdx (shorDvd m n anc) x y2) 0)
          = (∑ yp, workMat m n anc k f_coset y yp
                * ∑ y2, Emat yp y2 * phi (jointIdx (shorDvd m n anc) x y2) 0) from rfl]
    rw [show (∑ yp, Emat y yp
            * ∑ y2, Framework.uc_eval (f_ideal (revIndex m k))
                (Fin.cast (workDim_eq m n anc) yp) (Fin.cast (workDim_eq m n anc) y2)
                * phi (jointIdx (shorDvd m n anc) x y2) 0)
          = (∑ yp, Emat y yp
                * ∑ y2, workMat m n anc k f_ideal yp y2
                    * phi (jointIdx (shorDvd m n anc) x y2) 0) from rfl]
    rw [hL, hR]
    refine Finset.sum_congr rfl (fun y2 _ => ?_)
    rw [hwork_int y hy y2]
  · rw [if_neg hcb]
    rw [hEacts phi x y]
    refine Finset.sum_congr rfl (fun yp _ => ?_)
    rw [qpeStage_oracle_jointIdx m n anc k hk f_ideal hwt_i phi x yp, if_neg hcb]

/-- `E2shorZ` acts on the data factor through its matrix `E2matZ` (the form the generic lift wants). -/
theorem E2shorZ_acts_mat (m w bits N cm : Nat)
    (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    E2shorZ m w bits N cm phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
      = ∑ yp, E2matZ m w bits N cm y yp
          * phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x yp) 0 := by
  rw [E2shorZ_acts m w bits N cm phi x y]
  rfl

/-- **F2 brick 2 — the E₂ controlled-oracle intertwining.**  Instantiates the generic lift with the
    canonical-zeroed E₂ embedding (`E2shorZ`, `E2matZ`, `E2shorZ_acts_mat`) and the brick-1
    `hwork_int` (`E2_hwork_int` supplied at the call site as `hwork_int`).  No re-proof of the matrix
    identity. -/
theorem controlled_shifted_oracle_hintertwine_E2 (m w bits N cm kstep : Nat) (hk : kstep < m)
    (f_coset f_ideal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt_c : ∀ j, UCom.WellTyped (bits + cosetAnc w bits) (f_coset j))
    (hwt_i : ∀ j, UCom.WellTyped (bits + cosetAnc w bits) (f_ideal j))
    (bad_step : Finset (Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)))
    (hwork_int : ∀ y, y ∉ bad_step → ∀ y2 : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        (∑ yp, workMat m bits (cosetAnc w bits) kstep f_coset y yp * E2matZ m w bits N cm yp y2)
          = (∑ yp, E2matZ m w bits N cm y yp
                * workMat m bits (cosetAnc w bits) kstep f_ideal yp y2)) :
    ∀ (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits))) (x : Fin (2 ^ m))
      (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)), y ∉ bad_step →
      (qpeStageMap m bits (cosetAnc w bits) f_coset kstep (E2shorZ m w bits N cm phi))
          (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
        = (E2shorZ m w bits N cm (qpeStageMap m bits (cosetAnc w bits) f_ideal kstep phi))
            (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0 :=
  controlled_oracle_hintertwine_generic m bits (cosetAnc w bits) kstep hk f_coset f_ideal hwt_c hwt_i
    (E2shorZ m w bits N cm) (E2matZ m w bits N cm) (E2shorZ_acts_mat m w bits N cm) bad_step hwork_int

end FormalRV.Shor.GidneyInPlace.InPlaceE2HintertwineLift
