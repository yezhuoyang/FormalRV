/-
  FormalRV.Shor.GidneyInPlace.E2ResidueEmbedCanonical — the E2 residue↔runway intertwining LEAF with
  `hf_residue` WEAKENED to the canonical subspace (Route B′).
  ════════════════════════════════════════════════════════════════════════════

  The capstone's intertwining (`E2ResidueEmbed.E2residue_hwork_int`) carried the FULL-matrix
  `hf_residue`: `uc_eval(f_residueIdeal)` is the residue layout permutation, INCLUDING identity off the
  canonical subspace.  That off-canonical identity is strictly stronger than `ModMulImpl` and is NOT
  satisfied by a straight-line modular multiplier (which scrambles off-canonical inputs).

  HERE we re-prove the same intertwining from only what a real multiplier provides:
    * `hf_res_can`  — the multiply on CANONICAL columns (= `ModMulImpl`'s content as a matrix entry);
    * `hf_res_pres` — CANONICAL PRESERVATION: a non-canonical column has zero weight on canonical
      rows (equivalently: the oracle maps canonical states to canonical states, so — being a
      permutation — it maps non-canonical to non-canonical).

  The original proof used the off-canonical identity ONLY in the non-canonical branch, to collapse
  `∑ yp E2residueMat y yp · workMat(f_res) yp y2` to the `yp = y2` term.  That branch is actually 0 for
  a SHARPER reason: `E2residueMat y yp = 0` unless `yp` is canonical, and for canonical `yp` with
  non-canonical `y2`, `hf_res_pres` gives `workMat(f_res) yp y2 = 0`.  Both `hf_res_can`/`hf_res_pres`
  hold for `IdealResidueOracle.idealResidueFamily` (the exact `ModMulImpl` multiplier at `cosetAnc`).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Deviation.Proof.E2ResidueEmbed

namespace FormalRV.Shor.GidneyInPlace.E2ResidueEmbedCanonical

open scoped BigOperators
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq)
open FormalRV.Shor.GidneyInPlace.ControlOracleLift (workMat)
open FormalRV.Shor.GidneyInPlace.E2ResidueEmbed (E2residueMat E2residueEmbedZ E2residueEmbedZ_acts_mat
  E2residueEmbedZ_qpeInit E2residueEmbedZ_qftinv_comm E2residueEmbedZ_hmarg qstate_ext_jointIdx
  qpeStageMap_qftinv_indep)
open FormalRV.Shor.GidneyInPlace.InPlaceE2HintertwineLift (controlled_oracle_hintertwine_generic)
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp (qpeInit qpeStageMap shor_final_eq_orbitState)
open FormalRV.Shor.GidneyInPlace.OrbitState (orbitState)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess
  (E2runwayInit Shor_final_state_E2coset probability_of_success_E2coset)
open FormalRV.SQIRPort
  (probability_of_success r_found basis_vector prob_partial_meas Shor_final_state QState)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.SQIRPort.ApproxTransfer (jointIdx)

/-- **The residue↔runway intertwining, from canonical-only data (Route B′).**  Identical conclusion to
    `E2ResidueEmbed.E2residue_hwork_int`, but `hf_residue` is split into its canonical-subspace part
    (`hf_res_can`) and a canonical-preservation part (`hf_res_pres`) — both of which a genuine
    `ModMulImpl` multiplier satisfies, unlike the full-matrix off-canonical-identity form. -/
theorem E2residue_hwork_int_canonical
    (m w bits N cm kstep : Nat) (mult : Nat → Nat)
    (hN : 0 < N) (hNbits : N ≤ 2 ^ bits)
    (f_runwayIdeal f_residueIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hf_runway : ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult kstep * z) % N) 0
                (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_res_can : ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b
          = if a.val = ((mult kstep * (b.val / 2 ^ (cosetAnc w bits))) % N) * 2 ^ (cosetAnc w bits)
              then 1 else 0)
    (hf_res_pres : ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        (a.val % 2 ^ (cosetAnc w bits) = 0 ∧ a.val / 2 ^ (cosetAnc w bits) < N) →
        ¬ (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b = 0)
    (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m))
    (y2 : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    (∑ yp, workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
        * E2residueMat m w bits N cm yp y2)
      = (∑ yp, E2residueMat m w bits N cm y yp
          * workMat m bits (cosetAnc w bits) kstep f_residueIdeal yp y2) := by
  classical
  have hdimEq : (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m
      = 2 ^ bits * 2 ^ (cosetAnc w bits) := by
    rw [workDim_eq m bits (cosetAnc w bits), pow_add]
  by_cases hy2 : y2.val % 2 ^ (cosetAnc w bits) = 0 ∧ y2.val / 2 ^ (cosetAnc w bits) < N
  · -- canonical residue-layout column
    set z2 := y2.val / 2 ^ (cosetAnc w bits) with hz2
    have hz2N : z2 < N := hy2.2
    have hmodN : (mult kstep * z2) % N < N := Nat.mod_lt _ hN
    have hres_bits : (mult kstep * z2) % N < 2 ^ bits := lt_of_lt_of_le hmodN hNbits
    have ht_lt : (mult kstep * z2) % N * 2 ^ (cosetAnc w bits)
        < (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m := by
      rw [hdimEq]
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hres_bits
    set t : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m) :=
      ⟨(mult kstep * z2) % N * 2 ^ (cosetAnc w bits), ht_lt⟩ with ht
    have htmod : t.val % 2 ^ (cosetAnc w bits) = 0 := by
      show ((mult kstep * z2) % N * 2 ^ (cosetAnc w bits)) % 2 ^ (cosetAnc w bits) = 0
      exact Nat.mul_mod_left _ _
    have htdiv : t.val / 2 ^ (cosetAnc w bits) = (mult kstep * z2) % N := by
      show ((mult kstep * z2) % N * 2 ^ (cosetAnc w bits)) / 2 ^ (cosetAnc w bits) = _
      exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)
    have hLHS : (∑ yp, workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
            * E2residueMat m w bits N cm yp y2)
        = cosetInputVec w bits N cm ((mult kstep * z2) % N) 0
            (Fin.cast (E2shor_dim_eq m w bits) y) 0 := by
      rw [← hf_runway z2 hz2N y]
      refine Finset.sum_congr rfl (fun yp _ => ?_)
      rw [E2residueMat, if_pos hy2]
    have hRHS : (∑ yp, E2residueMat m w bits N cm y yp
            * workMat m bits (cosetAnc w bits) kstep f_residueIdeal yp y2)
        = cosetInputVec w bits N cm ((mult kstep * z2) % N) 0
            (Fin.cast (E2shor_dim_eq m w bits) y) 0 := by
      rw [Finset.sum_eq_single t]
      · rw [hf_res_can t y2 hy2, if_pos rfl, mul_one, E2residueMat,
            if_pos ⟨htmod, by rw [htdiv]; exact hmodN⟩, htdiv]
      · intro yp _ hypne
        rw [hf_res_can yp y2 hy2, if_neg (fun h => hypne (Fin.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hLHS, hRHS]
  · -- non-canonical column: both sides 0
    have hLHS0 : (∑ yp, workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
            * E2residueMat m w bits N cm yp y2) = 0 := by
      refine Finset.sum_eq_zero (fun yp _ => ?_)
      rw [E2residueMat, if_neg hy2, mul_zero]
    have hRHS0 : (∑ yp, E2residueMat m w bits N cm y yp
            * workMat m bits (cosetAnc w bits) kstep f_residueIdeal yp y2) = 0 := by
      refine Finset.sum_eq_zero (fun yp _ => ?_)
      by_cases hyp : yp.val % 2 ^ (cosetAnc w bits) = 0 ∧ yp.val / 2 ^ (cosetAnc w bits) < N
      · -- canonical yp, non-canonical y2 ⇒ workMat(f_res) yp y2 = 0 (canonical preservation)
        rw [hf_res_pres yp y2 hyp hy2, mul_zero]
      · -- non-canonical yp ⇒ E2residueMat y yp = 0
        rw [E2residueMat, if_neg hyp, zero_mul]
    rw [hLHS0, hRHS0]

/-- **Per-stage intertwining (canonical hyps).**  Mirror of `E2ResidueEmbed.E2residueEmbedZ_intertwine`,
    fed by the canonical leaf. -/
theorem E2residueEmbedZ_intertwine_canonical
    (m w bits N cm kstep : Nat) (hk : kstep < m) (mult : Nat → Nat)
    (hN : 0 < N) (hNbits : N ≤ 2 ^ bits)
    (f_runwayIdeal f_residueIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt_c : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hwt_i : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_residueIdeal j))
    (hf_runway : ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult kstep * z) % N) 0
                (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_res_can : ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b
          = if a.val = ((mult kstep * (b.val / 2 ^ (cosetAnc w bits))) % N) * 2 ^ (cosetAnc w bits)
              then 1 else 0)
    (hf_res_pres : ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        (a.val % 2 ^ (cosetAnc w bits) = 0 ∧ a.val / 2 ^ (cosetAnc w bits) < N) →
        ¬ (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b = 0)
    (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal kstep (E2residueEmbedZ m w bits N cm phi))
        (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
      = (E2residueEmbedZ m w bits N cm
          (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal kstep phi))
          (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0 :=
  controlled_oracle_hintertwine_generic m bits (cosetAnc w bits) kstep hk
    f_runwayIdeal f_residueIdeal hwt_c hwt_i
    (E2residueEmbedZ m w bits N cm) (E2residueMat m w bits N cm)
    (E2residueEmbedZ_acts_mat m w bits N cm)
    (∅ : Finset (Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)))
    (fun y _ y2 => E2residue_hwork_int_canonical m w bits N cm kstep mult hN hNbits
      f_runwayIdeal f_residueIdeal hf_runway hf_res_can hf_res_pres y y2)
    phi x y (Finset.notMem_empty y)

/-- **Oracle-stage orbit bridge (canonical hyps).**  Mirror of `E2ResidueEmbed.orbit_oracle_bridge`. -/
theorem orbit_oracle_bridge_canonical (m w bits N cm : Nat) (hm : 0 < m) (hbits : 0 < bits)
    (mult : Nat → Nat) (hN : 0 < N) (hN1 : 1 < N) (hNbits : N ≤ 2 ^ bits)
    (f_runwayIdeal f_residueIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt_c : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hwt_i : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_residueIdeal j))
    (hf_runway : ∀ (kstep : Nat), kstep < m → ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult kstep * z) % N) 0
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
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b = 0) :
    ∀ numIter, numIter ≤ m →
      orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
          (E2runwayInit m w bits N cm) numIter
        = E2residueEmbedZ m w bits N cm
            (orbitState (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal)
              (qpeInit m bits (cosetAnc w bits)) numIter) := by
  intro numIter
  induction numIter with
  | zero =>
      intro _
      show E2runwayInit m w bits N cm
          = E2residueEmbedZ m w bits N cm (qpeInit m bits (cosetAnc w bits))
      exact (E2residueEmbedZ_qpeInit m w bits N cm hm hbits hN1).symm
  | succ p ih =>
      intro hp
      have hpm : p < m := hp
      show qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal p
            (orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
              (E2runwayInit m w bits N cm) p)
          = E2residueEmbedZ m w bits N cm
              (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal p
                (orbitState (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal)
                  (qpeInit m bits (cosetAnc w bits)) p))
      rw [ih (Nat.le_of_lt hpm)]
      apply qstate_ext_jointIdx m bits (cosetAnc w bits)
      intro x y
      exact E2residueEmbedZ_intertwine_canonical m w bits N cm p hpm mult hN hNbits
        f_runwayIdeal f_residueIdeal hwt_c hwt_i
        (hf_runway p hpm) (hf_res_can p hpm) (hf_res_pres p hpm)
        (orbitState (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal)
          (qpeInit m bits (cosetAnc w bits)) p) x y

/-- **The orbit bridge (canonical hyps).**  Mirror of `E2ResidueEmbed.Shor_final_state_E2coset_eq_embed`. -/
theorem Shor_final_state_E2coset_eq_embed_canonical (m w bits N cm : Nat)
    (hm : 0 < m) (hbits : 0 < bits)
    (mult : Nat → Nat) (hN : 0 < N) (hN1 : 1 < N) (hNbits : N ≤ 2 ^ bits)
    (f_runwayIdeal f_residueIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt_c : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hwt_i : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_residueIdeal j))
    (hf_runway : ∀ (kstep : Nat), kstep < m → ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult kstep * z) % N) 0
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
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b = 0) :
    Shor_final_state_E2coset m w bits N cm f_runwayIdeal
      = E2residueEmbedZ m w bits N cm
          (Shor_final_state m bits (cosetAnc w bits) f_residueIdeal) := by
  have hdim_pos : 0 < m + (bits + cosetAnc w bits) := by omega
  rw [show Shor_final_state_E2coset m w bits N cm f_runwayIdeal
        = orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
            (E2runwayInit m w bits N cm) (m + 1) from rfl,
      shor_final_eq_orbitState m bits (cosetAnc w bits) f_residueIdeal hdim_pos]
  show qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal m
        (orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
          (E2runwayInit m w bits N cm) m)
      = E2residueEmbedZ m w bits N cm
          (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal m
            (orbitState (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal)
              (qpeInit m bits (cosetAnc w bits)) m))
  rw [orbit_oracle_bridge_canonical m w bits N cm hm hbits mult hN hN1 hNbits
        f_runwayIdeal f_residueIdeal hwt_c hwt_i hf_runway hf_res_can hf_res_pres m (Nat.le_refl m)]
  rw [show qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal m
        = qpeStageMap m bits (cosetAnc w bits) f_residueIdeal m from
      qpeStageMap_qftinv_indep m bits (cosetAnc w bits) f_runwayIdeal f_residueIdeal]
  apply qstate_ext_jointIdx m bits (cosetAnc w bits)
  intro x y
  exact E2residueEmbedZ_qftinv_comm m w bits N cm hm f_residueIdeal
    (orbitState (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal)
      (qpeInit m bits (cosetAnc w bits)) m) x y

/-- **The success bridge (canonical hyps).**  Mirror of `E2ResidueEmbed.probability_of_success_E2coset_eq`:
    the runway machine's Shor success EQUALS the residue Shor success, now from canonical-only data. -/
theorem probability_of_success_E2coset_eq_canonical (a r N m w bits cm : Nat)
    (hm : 0 < m) (hbits : 0 < bits)
    (mult : Nat → Nat) (hN : 0 < N) (hN1 : 1 < N)
    (numWin : Nat) (hw : 0 < w) (hbitsWin : numWin * w = bits) (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (f_runwayIdeal f_residueIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt_c : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hwt_i : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_residueIdeal j))
    (hf_runway : ∀ (kstep : Nat), kstep < m → ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult kstep * z) % N) 0
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
            (jointIdx (shorDvd m bits (cosetAnc w bits)) x b) 0 = 0) :
    probability_of_success_E2coset a r N m w bits cm f_runwayIdeal
      = probability_of_success a r N m bits (cosetAnc w bits) f_residueIdeal := by
  show (∑ x ∈ Finset.range (2 ^ m),
          r_found x m r a N
            * prob_partial_meas (basis_vector (2 ^ m) x)
                (Shor_final_state_E2coset m w bits N cm f_runwayIdeal))
      = ∑ x ∈ Finset.range (2 ^ m),
          r_found x m r a N
            * prob_partial_meas (basis_vector (2 ^ m) x)
                (Shor_final_state m bits (cosetAnc w bits) f_residueIdeal)
  rw [Shor_final_state_E2coset_eq_embed_canonical m w bits N cm hm hbits mult hN hN1
        (le_trans (Nat.le_mul_of_pos_left N (Nat.two_pow_pos cm)) hMN)
        f_runwayIdeal f_residueIdeal hwt_c hwt_i hf_runway hf_res_can hf_res_pres]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.mem_range] at hx
  congr 1
  have hxeq : x = (⟨x, hx⟩ : Fin (2 ^ m)).val := rfl
  rw [hxeq]
  exact E2residueEmbedZ_hmarg m w bits numWin N cm hw hbitsWin hN hMN
    (Shor_final_state m bits (cosetAnc w bits) f_residueIdeal) hsupp_res ⟨x, hx⟩

end FormalRV.Shor.GidneyInPlace.E2ResidueEmbedCanonical
