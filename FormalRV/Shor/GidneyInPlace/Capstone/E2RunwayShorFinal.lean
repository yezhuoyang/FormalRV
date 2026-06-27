/-
  FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorFinal —
  THE FULLY-UNCONDITIONAL coset/runway Shor bound (no abstract oracle).
  ════════════════════════════════════════════════════════════════════════════

  Assembly of the capstone `gidney_inplace_coset_shor_succeeds_unconditional_canonical`
  with EVERY abstract-oracle hypothesis discharged by the concrete verified gates:
   • the ideal runway oracle  = the verified perm-synthesis gate `runwayGate`
     (generic synthesis of `resShiftPerm`), packaged via `runwayIdealFam`;
   • the ideal residue oracle  = the verified exact multiplier `idealResidueFamily`;
   • the runway column identity = `runwayGate_column_identity`;
   • the residue canonical/preservation/support facts = the `E2RunwayShorClosure` lemmas;
   • the sub-unit norms = `E2RunwayShorNorms.coset_final_pmNorm_le`.

  The result `gidney_inplace_coset_shor_succeeds_fully_unconditional` has NO abstract oracle
  hypothesis and NO `cm ≤ 2w−3` constraint — only the standard parameters (w ≥ 2, etc.) and a
  modular-inverse witness `a·ainv0 ≡ 1`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorCanonical
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorClosure
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorNorms
import FormalRV.Shor.GidneyInPlace.Capstone.IdealResidueOracle
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayReduction
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthRunwayGate

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorFinal

open FormalRV.SQIRPort (revIndex BasicSetting κ)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess (probability_of_success_E2coset)
open FormalRV.Shor.GidneyInPlace.E2PhysicalRealization (physRunwayOracle)
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthRunwayGate
  (runwayGate runwayGate_wellTyped runwayGate_column_identity)
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayReduction
  (runwayIdealFam runwayIdealFam_wellTyped hf_runway_of_column_identity)
open FormalRV.Shor.GidneyInPlace.IdealResidueOracle (idealResidueFamily)

/-- **★ THE FULLY-UNCONDITIONAL COSET/RUNWAY SHOR BOUND. ★**

    The coset machine's success probability against the EXPLICIT physical oracle
    `physRunwayOracle` exceeds the Shor floor `κ/(log₂N)⁴` minus the runway deviation
    `2·m·√(8·numWin/2^cm)`, with NO abstract-oracle hypotheses:
     • the ideal runway oracle is the verified perm-synthesis gate `runwayGate`
       (generic synthesis of the guarded residue shift `resShiftPerm`);
     • the ideal residue oracle is the verified exact multiplier `idealResidueFamily`.
    Standard parameters only (`w ≥ 2`, full-blocks budget `2^cm·N ≤ 2^bits`, `2·N ≤ 2^bits`),
    plus a modular-inverse witness `a·ainv0 ≡ 1 (mod N)` and `BasicSetting`.  No `cm ≤ 2w−3`. -/
theorem gidney_inplace_coset_shor_succeeds_fully_unconditional
    (a r N m w bits numWin cm ainv0 : Nat)
    (hm : 0 < m) (hw2 : 2 ≤ w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m bits) :
    probability_of_success_E2coset a r N m w bits cm
        (physRunwayOracle m w bits numWin
          (fun k => tableValue (a ^ (2 ^ (revIndex m k)) % N) N w)
          (fun k => tableValue (ainv0 ^ (2 ^ (revIndex m k)) % N) N w))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
          - 2 * (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) := by
  -- Standard derived parameters.
  have hw : 0 < w := by omega
  have hN : 0 < N := by omega
  have hbitsPos : 0 < bits := hb1
  have hnumWin : 1 ≤ numWin := by
    rcases Nat.eq_zero_or_pos numWin with h0 | h; · subst h0; simp at hbits; omega
    exact h
  -- The squared-power multiplier table and its inverse.
  set mult : Nat → Nat := fun k => a ^ (2 ^ (revIndex m k)) % N with hmult
  set kInv : Nat → Nat := fun k => ainv0 ^ (2 ^ (revIndex m k)) % N with hkinv
  -- The per-stage forward/backward inverse laws (mult·kInv ≡ kInv·mult ≡ 1).
  have hfwd : ∀ k, (mult k * kInv k) % N = 1 := by
    intro k
    exact FormalRV.BQAlgo.mul_pow_mod_one a ainv0 N (2 ^ (revIndex m k)) hN1 h_inv0
  have hbwd : ∀ k, (kInv k * mult k) % N = 1 := by
    intro k
    exact FormalRV.BQAlgo.mul_pow_mod_one ainv0 a N (2 ^ (revIndex m k)) hN1
      (by rw [Nat.mul_comm]; exact h_inv0)
  have hkkinv : ∀ k, (kInv k * mult k) % N = 1 % N := by
    intro k; rw [hbwd k, Nat.mod_eq_of_lt hN1]
  -- The verified runway-gate family.
  set gFam : Nat → FormalRV.Framework.Gate :=
    fun k => runwayGate w bits N cm (mult k) (kInv k) hN1 (hfwd k) (hbwd k) with hgFam
  -- The ideal runway oracle family (verified perm synthesis).
  set f_runwayIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits) :=
    runwayIdealFam m w bits gFam with hfrun
  -- The ideal residue oracle family (verified exact multiplier).
  set RF := idealResidueFamily w bits N a ainv0 hw2 hb1 hN1 hN2 h_inv0 with hRF
  set f_residueIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits) :=
    RF.family with hfres
  -- The physical-oracle table families.
  set TfamK : Nat → Nat → Nat → Nat := fun k => tableValue (mult k) N w with hTK
  set TfamKinv : Nat → Nat → Nat → Nat := fun k => tableValue (kInv k) N w with hTKinv
  -- Well-typedness of the runway-ideal family.
  have hwtI : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j) :=
    runwayIdealFam_wellTyped m w bits gFam
      (fun j => runwayGate_wellTyped w bits N cm (mult j) (kInv j) hN1 (hfwd j) (hbwd j))
  -- Well-typedness of the residue family.
  have hwtRes : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits)
      (f_residueIdeal j) := fun j => RF.wellTyped j
  -- The runway oracle's `hf_runway` (∑-form), valid for ALL `k` (the capstone's hypothesis is
  -- stated `∀ k`).  For each `k`, the family iterate `f_runwayIdeal (revIndex m k)` is, by
  -- definition of `runwayIdealFam`, the gate `gFam (revIndex m (revIndex m k))`, whose column
  -- identity realises the multiplier `mult (revIndex m (revIndex m k)) = mult k` (the `revIndex`
  -- triple-collapse, valid for all `k` since `m > 0`).  This is exactly the per-stage column
  -- identity `hf_runway_of_column_identity` packages — applied via the general helper below.
  have hrevcollapse : ∀ k, revIndex m (revIndex m (revIndex m k)) = revIndex m k := by
    intro k; unfold FormalRV.SQIRPort.revIndex; omega
  have hmultcollapse : ∀ k, mult (revIndex m (revIndex m k)) = mult k := by
    intro k
    simp only [hmult]
    rw [hrevcollapse k]
  have hcol : ∀ (k : Nat), ∀ (z : Nat), z < N →
      FormalRV.Framework.uc_eval
          (FormalRV.BQAlgo.Gate.toUCom
            (FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate.cosetDim w bits)
            (gFam (revIndex m (revIndex m k))))
          * FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w bits N cm z 0
        = FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w bits N cm ((mult k * z) % N) 0 := by
    intro k z hz
    have h := runwayGate_column_identity w bits N cm
      (mult (revIndex m (revIndex m k))) (kInv (revIndex m (revIndex m k))) z hN1
      (hfwd (revIndex m (revIndex m k))) (hbwd (revIndex m (revIndex m k))) hMN hz
    rw [← hmultcollapse k]
    exact h
  -- General ∑-form `hf_runway` (∀ k), proved inline by unfolding `runwayIdealFam` and recognising
  -- the supplied column identity via `Matrix.mul_apply` (clone of `hf_runway_of_column_identity`,
  -- but routed through `gFam (revIndex m (revIndex m k))` so no `k < m` is needed).
  have hf_runway : ∀ (k : Nat) (z : Nat), z < N →
      ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
      (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
          FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
              (Fin.cast (FormalRV.Shor.GidneyInPlace.ControlStageBridge.workDim_eq
                m bits (cosetAnc w bits)) y)
              (Fin.cast (FormalRV.Shor.GidneyInPlace.ControlStageBridge.workDim_eq
                m bits (cosetAnc w bits)) yp)
            * FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w bits N cm z 0
                (Fin.cast (FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg.E2shor_dim_eq
                  m w bits) yp) 0)
        = FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w bits N cm ((mult k * z) % N) 0
            (Fin.cast (FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg.E2shor_dim_eq
              m w bits) y) 0 := by
    intro k z hz y
    -- unfold the family iterate to the underlying gate at `revIndex m (revIndex m k)`.
    show (∑ yp,
        FormalRV.Framework.uc_eval
            (FormalRV.BQAlgo.Gate.toUCom (bits + cosetAnc w bits)
              (gFam (revIndex m (revIndex m k))))
            (Fin.cast (FormalRV.Shor.GidneyInPlace.ControlStageBridge.workDim_eq
              m bits (cosetAnc w bits)) y)
            (Fin.cast (FormalRV.Shor.GidneyInPlace.ControlStageBridge.workDim_eq
              m bits (cosetAnc w bits)) yp)
          * FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w bits N cm z 0
              (Fin.cast (FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg.E2shor_dim_eq
                m w bits) yp) 0)
      = FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w bits N cm ((mult k * z) % N) 0
          (Fin.cast (FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg.E2shor_dim_eq m w bits) y) 0
    rw [← hcol k z hz]
    show (∑ yp,
        FormalRV.Framework.uc_eval
            (FormalRV.BQAlgo.Gate.toUCom (bits + cosetAnc w bits)
              (gFam (revIndex m (revIndex m k))))
            (Fin.cast (FormalRV.Shor.GidneyInPlace.ControlStageBridge.workDim_eq
              m bits (cosetAnc w bits)) y)
            (Fin.cast (FormalRV.Shor.GidneyInPlace.ControlStageBridge.workDim_eq
              m bits (cosetAnc w bits)) yp)
          * FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w bits N cm z 0
              (Fin.cast (FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg.E2shor_dim_eq
                m w bits) yp) 0)
      = (FormalRV.Framework.uc_eval
            (FormalRV.BQAlgo.Gate.toUCom
              (FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate.cosetDim w bits)
              (gFam (revIndex m (revIndex m k))))
          * FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w bits N cm z 0)
          (Fin.cast (FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg.E2shor_dim_eq m w bits) y) 0
    rw [Finset.sum_congr rfl (fun yp _ => by
      rw [FormalRV.Shor.GidneyInPlace.E2PhysicalRealization.uc_eval_toUCom_dimcast
            (FormalRV.Shor.GidneyInPlace.InPlaceCosetGate.cosetWork_dim_eq w bits)
            (gFam (revIndex m (revIndex m k)))
            (Fin.cast (FormalRV.Shor.GidneyInPlace.ControlStageBridge.workDim_eq
              m bits (cosetAnc w bits)) y)
            (Fin.cast (FormalRV.Shor.GidneyInPlace.ControlStageBridge.workDim_eq
              m bits (cosetAnc w bits)) yp)])]
    rw [Matrix.mul_apply]
    exact (Fintype.sum_equiv
      (finCongr (FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg.E2shor_dim_eq m w bits))
      (fun yp => FormalRV.Framework.uc_eval
          (FormalRV.BQAlgo.Gate.toUCom
            (FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate.cosetDim w bits)
            (gFam (revIndex m (revIndex m k))))
          (Fin.cast (FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg.E2shor_dim_eq m w bits) y)
          (Fin.cast (FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg.E2shor_dim_eq m w bits) yp)
        * FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w bits N cm z 0
            (Fin.cast (FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg.E2shor_dim_eq m w bits) yp) 0)
      (fun i => FormalRV.Framework.uc_eval
          (FormalRV.BQAlgo.Gate.toUCom
            (FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate.cosetDim w bits)
            (gFam (revIndex m (revIndex m k))))
          (Fin.cast (FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg.E2shor_dim_eq m w bits) y) i
        * FormalRV.Shor.GidneyInPlace.InPlaceNormBound.cosetInputVec w bits N cm z 0 i 0)
      (fun yp => rfl))
  -- The residue oracle's `hf_res_can`.
  have hf_res_can : ∀ (kstep : Nat), kstep < m →
      ∀ p q : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
      (q.val % 2 ^ (cosetAnc w bits) = 0 ∧ q.val / 2 ^ (cosetAnc w bits) < N) →
      FormalRV.Shor.GidneyInPlace.ControlOracleLift.workMat m bits (cosetAnc w bits) kstep
          f_residueIdeal p q
        = if p.val = ((mult kstep * (q.val / 2 ^ (cosetAnc w bits))) % N) * 2 ^ (cosetAnc w bits)
            then 1 else 0 := by
    intro kstep _ p q hq
    rw [hmult]
    exact FormalRV.Shor.GidneyInPlace.E2RunwayShorClosure.idealResidue_hf_res_can
      w bits N a ainv0 hw2 hb1 hN1 hN2 h_inv0 m kstep p q hq
  -- The residue oracle's `hf_res_pres`.
  have hf_res_pres : ∀ (kstep : Nat), kstep < m →
      ∀ p q : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
      (p.val % 2 ^ (cosetAnc w bits) = 0 ∧ p.val / 2 ^ (cosetAnc w bits) < N) →
      ¬ (q.val % 2 ^ (cosetAnc w bits) = 0 ∧ q.val / 2 ^ (cosetAnc w bits) < N) →
      FormalRV.Shor.GidneyInPlace.ControlOracleLift.workMat m bits (cosetAnc w bits) kstep
          f_residueIdeal p q = 0 := by
    intro kstep _ p q hp hq
    exact FormalRV.Shor.GidneyInPlace.E2RunwayShorClosure.idealResidue_hf_res_pres
      w bits N a ainv0 hw2 hb1 hN1 hN2 h_inv0 m kstep p q hp hq
  -- The residue oracle's `hsupp_res`.
  have hsupp_res : ∀ (x : Fin (2 ^ m))
      (b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
      ¬ (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
      FormalRV.SQIRPort.Shor_final_state m bits (cosetAnc w bits) f_residueIdeal
          (FormalRV.SQIRPort.ApproxTransfer.jointIdx
            (FormalRV.Shor.CosetMarginalShorBound.shorDvd m bits (cosetAnc w bits)) x b) 0 = 0 := by
    intro x b hb
    exact FormalRV.Shor.GidneyInPlace.E2RunwayShorClosure.idealResidue_hsupp_res
      w bits N a ainv0 r m hw2 hb1 hN1 hN2 h_inv0 h_basic x b hb
  -- Norms: both final states are sub-unit.
  have hnormP : FormalRV.Shor.Approx.pmNorm
      (FormalRV.Shor.GidneyInPlace.E2CosetSuccess.Shor_final_state_E2coset m w bits N cm
        (physRunwayOracle m w bits numWin TfamK TfamKinv)) ≤ 1 :=
    FormalRV.Shor.GidneyInPlace.E2RunwayShorNorms.coset_final_pmNorm_le
      m w bits N cm numWin hm hw hbits hN1 hN2 hMN
      (physRunwayOracle m w bits numWin TfamK TfamKinv)
      (fun j => FormalRV.Shor.GidneyInPlace.E2RunwayShorCapstone.physRunwayOracle_wellTyped
        m w bits numWin TfamK TfamKinv hw hbits j)
  have hnormI : FormalRV.Shor.Approx.pmNorm
      (FormalRV.Shor.GidneyInPlace.E2CosetSuccess.Shor_final_state_E2coset m w bits N cm
        f_runwayIdeal) ≤ 1 :=
    FormalRV.Shor.GidneyInPlace.E2RunwayShorNorms.coset_final_pmNorm_le
      m w bits N cm numWin hm hw hbits hN1 hN2 hMN f_runwayIdeal hwtI
  -- The ModMulImpl contract for the residue family.
  have h_mmi : FormalRV.SQIRPort.ModMulImpl a N bits (cosetAnc w bits) f_residueIdeal := RF.mmi
  -- Invoke the canonical unconditional capstone with everything discharged.
  exact FormalRV.Shor.GidneyInPlace.E2RunwayShorCanonical.gidney_inplace_coset_shor_succeeds_unconditional_canonical
    a r N m w bits numWin cm TfamK TfamKinv mult kInv f_runwayIdeal f_residueIdeal
    hm hbitsPos hwtI hwtRes (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    hw hbits hN hN1 hMN hkkinv hf_runway hf_res_can hf_res_pres hsupp_res hnormP hnormI
    h_basic h_mmi

end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorFinal
