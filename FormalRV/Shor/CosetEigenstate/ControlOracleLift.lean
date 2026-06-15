/-
  FormalRV.Shor.CosetEigenstate.ControlOracleLift — lemmas 2 + 3 - the live engine's `hc_local` and `hintertwine` for the
  CONTROLLED shifted oracle (`qpeStageMap`), via the proven layout bridge
  (`qpeStage_oracle_jointIdx`) as the single coordinate translator.

  Work oracle ABSTRACT: hypotheses talk only about
  `uc_eval (f_coset (revIndex m k))` / `uc_eval (f_ideal (revIndex m k))` and
  `cosetEmbedMat`/`badY`.  PHASE-INDEPENDENT bad set: a SINGLE `Finset` of work
  indices, never a function of the phase value `x`.
-/
import FormalRV.Shor.CosetEigenstate.ControlStageBridge
import FormalRV.Shor.CosetEigenstate.CosetEphys
import FormalRV.Shor.CosetEigenstate.EmbedOrbitCompose

namespace FormalRV.Shor.CosetEigenstate.ControlOracleLift

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer (jointIdx)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.CosetEigenstate.QPEStageDecomp (qpeStageMap)
open FormalRV.Shor.CosetEigenstate.ControlStageBridge
  (qpeStage_oracle_jointIdx workDim_eq)
open FormalRV.Shor.CosetEigenstate.CosetEphys (E_phys E_phys_acts cosetEmbedMat)

/-- The work matrix on the DATA factor `Fin ((2^m*2^n*2^anc)/2^m)`, obtained by
    casting both indices to the native work register `Fin (2^(n+anc))` (`toWork`)
    and reading `uc_eval` of the (abstract) work oracle there. -/
noncomputable def workMat (m n anc k : Nat) (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (y yp : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)) : ℂ :=
  FormalRV.Framework.uc_eval (f (revIndex m k))
    (Fin.cast (workDim_eq m n anc) y) (Fin.cast (workDim_eq m n anc) yp)

/-! ## LEMMA 2 — `hc_local` for the controlled shifted oracle. -/

/-- **Lemma 2 (`hc_local`).**  The controlled coset oracle preserves off-`badY`
    agreement.  The single WORK-LEVEL hypothesis `hwork` is GOOD-SET PRESERVATION:
    off `badY`, the work-matrix row is supported on the good set — exactly what the
    bit-true sum needs. -/
theorem controlled_shifted_oracle_hc_local (m n anc k : Nat) (hk : k < m)
    (f_coset : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (hwt : ∀ j, FormalRV.Framework.UCom.WellTyped (n + anc) (f_coset j))
    (badY : Finset (Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)))
    (hwork : ∀ y, y ∉ badY →
      ∀ yp, workMat m n anc k f_coset y yp ≠ 0 → yp ∉ badY) :
    ∀ (a₁ a₂ : QState (2 ^ m * 2 ^ n * 2 ^ anc)),
      (∀ x y, y ∉ badY →
        a₁ (jointIdx (shorDvd m n anc) x y) 0 = a₂ (jointIdx (shorDvd m n anc) x y) 0) →
      ∀ x y, y ∉ badY →
        (qpeStageMap m n anc f_coset k a₁) (jointIdx (shorDvd m n anc) x y) 0
          = (qpeStageMap m n anc f_coset k a₂) (jointIdx (shorDvd m n anc) x y) 0 := by
  classical
  intro a₁ a₂ hagree x y hy
  rw [qpeStage_oracle_jointIdx m n anc k hk f_coset hwt a₁ x y,
      qpeStage_oracle_jointIdx m n anc k hk f_coset hwt a₂ x y]
  by_cases hcb : controlBit m k hk x
  · -- bit TRUE: both sides are work-matrix sums; agree term-by-term off the good set.
    rw [if_pos hcb, if_pos hcb]
    refine Finset.sum_congr rfl (fun yp _ => ?_)
    by_cases hM : FormalRV.Framework.uc_eval (f_coset (revIndex m k))
        (Fin.cast (workDim_eq m n anc) y) (Fin.cast (workDim_eq m n anc) yp) = 0
    · rw [hM, zero_mul, zero_mul]
    · have hyp : yp ∉ badY := hwork y hy yp hM
      rw [hagree x yp hyp]
  · -- bit FALSE: identity branch; close by `hagree`.
    rw [if_neg hcb, if_neg hcb]
    exact hagree x y hy

/-! ## LEMMA 3 — `hintertwine` for the controlled shifted oracle. -/

/-- **Lemma 3 (`hintertwine`).**  Off `bad_step`, the controlled coset oracle after the
    embedding equals the embedding after the controlled ideal oracle.  The single
    WORK-LEVEL hypothesis `hwork_int` is the off-`bad_step` matrix-row intertwining
    `(M_c ∘ E_data) = (E_data ∘ M_i)` between the abstract coset/ideal work oracles and
    `cosetEmbedMat` (PHASE-INDEPENDENT). -/
theorem controlled_shifted_oracle_hintertwine (m n anc k N cm : Nat) (hk : k < m)
    (f_coset f_ideal : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (hwt_c : ∀ j, FormalRV.Framework.UCom.WellTyped (n + anc) (f_coset j))
    (hwt_i : ∀ j, FormalRV.Framework.UCom.WellTyped (n + anc) (f_ideal j))
    (bad_step : Finset (Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)))
    (hwork_int : ∀ y, y ∉ bad_step →
      ∀ y2 : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m),
        (∑ yp : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m),
            workMat m n anc k f_coset y yp
              * cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm yp y2)
          = (∑ yp : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m),
              cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm y yp
                * workMat m n anc k f_ideal yp y2)) :
    ∀ (phi : QState (2 ^ m * 2 ^ n * 2 ^ anc)) (x : Fin (2 ^ m))
      (y : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)), y ∉ bad_step →
      (qpeStageMap m n anc f_coset k (E_phys m n anc N cm phi))
          (jointIdx (shorDvd m n anc) x y) 0
        = (E_phys m n anc N cm (qpeStageMap m n anc f_ideal k phi))
            (jointIdx (shorDvd m n anc) x y) 0 := by
  classical
  intro phi x y hy
  -- LHS: bridge through f_coset on (E_phys phi).
  rw [qpeStage_oracle_jointIdx m n anc k hk f_coset hwt_c (E_phys m n anc N cm phi) x y]
  -- RHS: E_phys acts on the data factor of (qpeStageMap f_ideal k phi).
  rw [E_phys_acts m n anc N cm (qpeStageMap m n anc f_ideal k phi) x y]
  by_cases hcb : controlBit m k hk x
  · -- bit TRUE.
    rw [if_pos hcb]
    -- LHS = ∑ yp, M_c y yp * (E_phys phi)(jointIdx x yp)
    --     = ∑ yp, M_c y yp * (∑ y2, cosetEmbedMat yp y2 * phi(jointIdx x y2))
    rw [Finset.sum_congr rfl (fun yp _ =>
      by rw [E_phys_acts m n anc N cm phi x yp] :
      ∀ yp ∈ Finset.univ,
        FormalRV.Framework.uc_eval (f_coset (revIndex m k))
            (Fin.cast (workDim_eq m n anc) y) (Fin.cast (workDim_eq m n anc) yp)
          * E_phys m n anc N cm phi (jointIdx (shorDvd m n anc) x yp) 0
        = FormalRV.Framework.uc_eval (f_coset (revIndex m k))
            (Fin.cast (workDim_eq m n anc) y) (Fin.cast (workDim_eq m n anc) yp)
          * ∑ y2, cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm yp y2
              * phi (jointIdx (shorDvd m n anc) x y2) 0)]
    -- RHS = ∑ yp, cosetEmbedMat y yp * (qpeStageMap f_ideal k phi)(jointIdx x yp)
    --     = ∑ yp, cosetEmbedMat y yp * (∑ y2, M_i yp y2 * phi(jointIdx x y2))   [bridge, bit true]
    rw [Finset.sum_congr rfl (fun yp _ =>
      by rw [qpeStage_oracle_jointIdx m n anc k hk f_ideal hwt_i phi x yp, if_pos hcb] :
      ∀ yp ∈ Finset.univ,
        cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm y yp
          * qpeStageMap m n anc f_ideal k phi (jointIdx (shorDvd m n anc) x yp) 0
        = cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm y yp
          * ∑ y2, FormalRV.Framework.uc_eval (f_ideal (revIndex m k))
              (Fin.cast (workDim_eq m n anc) yp) (Fin.cast (workDim_eq m n anc) y2)
              * phi (jointIdx (shorDvd m n anc) x y2) 0)]
    -- Pull each outer factor inside, swap the order of summation on both sides, and
    -- reduce to the work-level matrix identity at each fixed y2.
    have hL : (∑ yp, workMat m n anc k f_coset y yp
                * ∑ y2, cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm yp y2
                    * phi (jointIdx (shorDvd m n anc) x y2) 0)
        = ∑ y2, (∑ yp, workMat m n anc k f_coset y yp
                  * cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm yp y2)
                * phi (jointIdx (shorDvd m n anc) x y2) 0 := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y2 _ => Finset.sum_congr rfl (fun yp _ => by ring))
    have hR : (∑ yp, cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm y yp
                * ∑ y2, workMat m n anc k f_ideal yp y2
                    * phi (jointIdx (shorDvd m n anc) x y2) 0)
        = ∑ y2, (∑ yp, cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm y yp
                  * workMat m n anc k f_ideal yp y2)
                * phi (jointIdx (shorDvd m n anc) x y2) 0 := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y2 _ => Finset.sum_congr rfl (fun yp _ => by ring))
    -- The two work-matrix factorizations: workMat is exactly the bridge's matrix entry.
    show (∑ yp, FormalRV.Framework.uc_eval (f_coset (revIndex m k))
            (Fin.cast (workDim_eq m n anc) y) (Fin.cast (workDim_eq m n anc) yp)
            * ∑ y2, cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm yp y2
                * phi (jointIdx (shorDvd m n anc) x y2) 0)
        = ∑ yp, cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm y yp
            * ∑ y2, FormalRV.Framework.uc_eval (f_ideal (revIndex m k))
                (Fin.cast (workDim_eq m n anc) yp) (Fin.cast (workDim_eq m n anc) y2)
                * phi (jointIdx (shorDvd m n anc) x y2) 0
    rw [show (∑ yp, FormalRV.Framework.uc_eval (f_coset (revIndex m k))
            (Fin.cast (workDim_eq m n anc) y) (Fin.cast (workDim_eq m n anc) yp)
            * ∑ y2, cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm yp y2
                * phi (jointIdx (shorDvd m n anc) x y2) 0)
          = (∑ yp, workMat m n anc k f_coset y yp
                * ∑ y2, cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm yp y2
                    * phi (jointIdx (shorDvd m n anc) x y2) 0) from rfl]
    rw [show (∑ yp, cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm y yp
            * ∑ y2, FormalRV.Framework.uc_eval (f_ideal (revIndex m k))
                (Fin.cast (workDim_eq m n anc) yp) (Fin.cast (workDim_eq m n anc) y2)
                * phi (jointIdx (shorDvd m n anc) x y2) 0)
          = (∑ yp, cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm y yp
                * ∑ y2, workMat m n anc k f_ideal yp y2
                    * phi (jointIdx (shorDvd m n anc) x y2) 0) from rfl]
    rw [hL, hR]
    refine Finset.sum_congr rfl (fun y2 _ => ?_)
    rw [hwork_int y hy y2]
  · -- bit FALSE: both sides reduce to (E_phys phi)(jointIdx x y).
    rw [if_neg hcb]
    -- LHS = (E_phys phi)(jointIdx x y) = ∑ yp, cosetEmbedMat y yp * phi(jointIdx x yp).
    rw [E_phys_acts m n anc N cm phi x y]
    -- RHS: each (qpeStageMap f_ideal k phi)(jointIdx x yp) = phi(jointIdx x yp) [bit false, same x].
    refine Finset.sum_congr rfl (fun yp _ => ?_)
    rw [qpeStage_oracle_jointIdx m n anc k hk f_ideal hwt_i phi x yp, if_neg hcb]

end FormalRV.Shor.CosetEigenstate.ControlOracleLift
