/-
  FormalRV.Shor.GidneyInPlace.E2LocalDeviation — H3.2b of the coset-Shor hybrid route:
  the ACTUAL-side controlled local `pmDist` lift (the `hlocal` for the telescope).
  ════════════════════════════════════════════════════════════════════════════

  `PmDistTelescope.pmDist_orbit_telescope` (H1) consumes a per-step local deviation `δ k` in the
  ℓ² distance `pmDist`, between the ACTUAL physical stage `Fa k := qpeStageMap … f_runwayPhysical k`
  and the IDEAL trajectory point `Φ_k` (in `IdealCosetForm`).  This file builds that per-step
  bound at one oracle stage `k < m`:

    `qpeStage_E2_local_pmDist_deviation :
        pmDist (qpeStageMap m bits (cosetAnc w bits) f_runwayPhysical k Φ)
               (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal     k Φ)
          ≤ Real.sqrt (8 * numWin / 2^cm)`.

  ROUTE (dimension-clean aggregation — NO 2^m blowup).
    `pmDist²(Fa Φ, Fi Φ) = ∑_i normSq(…)`  (`pmDist_sq`)
      `= ∑_x ∑_y normSq(…)`                 (`sum_jointIdx_eq`, the bijection split)
    For each phase branch `x`:
      • INACTIVE (`controlBit … x = false`):  both stages are the identity on that branch
        (`qpeStage_oracle_jointIdx`'s `if_neg`), so every term is `normSq(Φ − Φ) = 0`.
      • ACTIVE   (`controlBit … x = true`):   `Φ`'s work slice is the FIXED scalar `1/√2^m`
        times one canonical coset column `cosetInputVec z 0` (`IdealCosetForm`, scalar PINNED).
        Factor the scalar; the actual work action realizes the gidney gate (`hf_physical`) and
        the ideal work action the clean shift (`hf_runway`), so the `y`-sum reduces, after
        reindexing the work dim to `2^(cosetDim w bits)` via `E2shor_dim_eq`, to H3.1's
        `pmDist²(gidney · cosetInputVec z 0, cosetInputVec ((mult k · z)%N) 0) ≤ 8·numWin/2^cm`.
        Each active branch contributes `|1/√2^m|² · (≤ 8·numWin/2^cm) = (1/2^m) · L`.
      Summing over `x`: `∑_x (1/2^m) · L = L` (the `2^m` phase branches × `1/2^m`).  `√` ⇒ `√L`.

  THE NORMALIZATION (the H3.2a decision point).  `IdealCosetForm`'s scalar is PINNED to `1/√2^m`
  (refined from the prior existential in `InPlaceE2IdealTrajectory.lean`; `IdealCosetForm` has no
  external consumers, so the refinement is local).  Pinning is what makes `∑_x |scalar_x|² = 1`
  provable — the existential scalar could not be summed.  Hence this `hlocal` theorem is
  UNCONDITIONAL in the scalar (NO carried `pmNorm Φ ≤ 1` side hypothesis).

  The two realization hypotheses are carried EXPLICITLY and are DISTINCT (`f_runwayPhysical ≠
  f_runwayIdeal`):
    • `hf_physical` — the physical oracle's active work action equals the gidney gate at the
      `workDim_eq`/`E2shor_dim_eq` casts (the cast chain audited in H3.2a);
    • `hf_runway`   — the ideal oracle's active work action is the clean coset shift (the
      matrix-vector form of `IdealPermLift.idealShift_cosetInputVec`, IDENTICAL to the one
      `InPlaceE2IdealTrajectory.idealCosetForm_step` already uses).

  NO bad sets, NO `hwork`/forward-closure/`EmbedAgreeOff`, NO `normSqDist` (lives only inside
  H3.1), NO H4 accumulation.

  Kernel-clean target: no `sorry`, no `native_decide`, no axioms beyond the prelude
  `{propext, Classical.choice, Quot.sound}`.
-/
import FormalRV.Shor.GidneyInPlace.Deviation.Engine.PmDistLocalDeviation
import FormalRV.Shor.GidneyInPlace.Ideal.Proof.InPlaceE2IdealTrajectory
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Input.InPlaceCosetInputNorm

namespace FormalRV.Shor.GidneyInPlace.E2LocalDeviation

open scoped Classical BigOperators
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.SQIRPort.ApproxTransfer (jointIdx sum_jointIdx_eq)
open FormalRV.Shor.Approx (pmDist pmDist_sq pmDist_nonneg)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate (gidneyInPlaceWithSwap)
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp (qpeStageMap)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq qpeStage_oracle_jointIdx)
open FormalRV.Shor.GidneyInPlace.InPlaceE2IdealTrajectory (IdealCosetForm)
open FormalRV.Shor.GidneyInPlace.PmDistLocalDeviation (gidneyInPlaceWithSwap_coset_pmDist_deviation)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputNorm (cosetInputVec_normalized)

/-! ## §1. Reindexing the per-branch work-dim sum to the coset dimension. -/

/-- **Work-dim → coset-dim reindex of an ℓ²-difference sum.**  For two coset columns
    `g h : Matrix (Fin (2^(cosetDim w bits))) (Fin 1) ℂ`, summing `normSq(g − h)` over the work
    register `Fin ((2^m·2^bits·2^(cosetAnc w bits))/2^m)` read at the `E2shor_dim_eq` cast equals
    `pmDist² g h` (the cast `E2shor_dim_eq` is a `Fin`-reindex bijection). -/
theorem sum_workDim_normSq_sub_eq_pmDist_sq (m w bits : Nat)
    (g h : Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ) :
    (∑ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        Complex.normSq (g (Fin.cast (E2shor_dim_eq m w bits) y) 0
                        - h (Fin.cast (E2shor_dim_eq m w bits) y) 0))
      = (pmDist g h) ^ 2 := by
  rw [pmDist_sq]
  exact Fintype.sum_equiv (finCongr (E2shor_dim_eq m w bits))
    (fun y => Complex.normSq (g (Fin.cast (E2shor_dim_eq m w bits) y) 0
                              - h (Fin.cast (E2shor_dim_eq m w bits) y) 0))
    (fun i => Complex.normSq (g i 0 - h i 0))
    (fun y => rfl)

/-! ## §2. The per-active-branch local bound. -/

/-- **The local `pmDist²` budget `8·numWin/2^cm`.** -/
private noncomputable def Lbudget (numWin cm : Nat) : ℝ := 8 * (numWin : ℝ) / 2 ^ cm

private theorem Lbudget_nonneg (numWin cm : Nat) : 0 ≤ Lbudget numWin cm := by
  unfold Lbudget; positivity

/-- **Per-active-branch local bound.**  For an ACTIVE phase branch `x` whose `Φ`-work slice is the
    fixed scalar `1/√2^m` times the canonical column `cosetInputVec z 0` (`z < N`), the `y`-sum of
    the squared stagewise amplitude differences is at most `(1/2^m) · (8·numWin/2^cm)`.

    Substitute the two stage values via `qpeStage_oracle_jointIdx` (`if_pos`), factor the fixed
    scalar through `hf_physical`/`hf_runway`, reindex the work register to `2^(cosetDim w bits)`,
    and bound by H3.1's `pmDist²(gidney · cosetInputVec z 0, cosetInputVec ((mult k · z)%N) 0)`. -/
private theorem active_branch_local_le
    (m w bits numWin N cm k kInv : Nat) (hk : k < m)
    (TfamK TfamKinv : Nat → Nat → Nat)
    (f_runwayPhysical f_runwayIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwtP : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayPhysical j))
    (hwtI : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (mult : Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue (mult k) N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hkkinv : (kInv * mult k) % N = 1 % N)
    (Φ : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (x : Fin (2 ^ m)) (z : Nat) (hz : z < N)
    (hfit : (mult k * z) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (hxfit : z + (2 ^ cm - 1) * N < 2 ^ bits)
    (hcb : controlBit m k hk x)
    (hslice : ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
      Φ (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
        = ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
            * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_physical : ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayPhysical (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = (FormalRV.Framework.uc_eval (Gate.toUCom (cosetDim w bits)
                (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin))
              * cosetInputVec w bits N cm z 0) (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_runway : ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = cosetInputVec w bits N cm ((mult k * z) % N) 0
              (Fin.cast (E2shor_dim_eq m w bits) y) 0) :
    (∑ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        Complex.normSq
          (qpeStageMap m bits (cosetAnc w bits) f_runwayPhysical k Φ
              (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
            - qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal k Φ
              (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0))
      ≤ (1 / 2 ^ m) * Lbudget numWin cm := by
  -- The two post-swap target columns of H3.1: the gidney gate output `g` and the clean shift `h`.
  set g : Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ :=
    FormalRV.Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin))
      * cosetInputVec w bits N cm z 0 with hg
  set h : Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ :=
    cosetInputVec w bits N cm ((mult k * z) % N) 0 with hh
  -- Per-`y`: the stagewise difference is the fixed scalar times the H3.1 column difference.
  have hdiff : ∀ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
      qpeStageMap m bits (cosetAnc w bits) f_runwayPhysical k Φ
          (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
        - qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal k Φ
          (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
      = ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
          * (g (Fin.cast (E2shor_dim_eq m w bits) y) 0
              - h (Fin.cast (E2shor_dim_eq m w bits) y) 0) := by
    -- Generic per-leg reduction: an active oracle leg with realization `hf` equals the fixed
    -- scalar times the target column (at the cast index `y`).
    have hleg : ∀ (fam : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
        (hwtf : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (fam j))
        (target : Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ)
        (hf : ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
            (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
                FormalRV.Framework.uc_eval (fam (revIndex m k))
                    (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                    (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
                  * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
              = target (Fin.cast (E2shor_dim_eq m w bits) y) 0)
        (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        qpeStageMap m bits (cosetAnc w bits) fam k Φ
            (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
          = ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ)) * target (Fin.cast (E2shor_dim_eq m w bits) y) 0 := by
      intro fam hwtf target hf y
      rw [qpeStage_oracle_jointIdx m bits (cosetAnc w bits) k hk fam hwtf Φ x y, if_pos hcb]
      rw [Finset.sum_congr rfl (fun yp _ => by rw [hslice yp])]
      rw [show (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              FormalRV.Framework.uc_eval (fam (revIndex m k))
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
                * (((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
                    * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0))
            = ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
                * (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
                    FormalRV.Framework.uc_eval (fam (revIndex m k))
                        (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                        (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
                      * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          from by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun yp _ => by ring)]
      rw [hf y]
    intro y
    rw [hleg f_runwayPhysical hwtP g hf_physical y, hleg f_runwayIdeal hwtI h hf_runway y]
    ring
  -- rewrite the whole sum via `hdiff`, factor `|1/√2^m|²`, reindex, and bound by H3.1.
  rw [Finset.sum_congr rfl (fun y _ => by rw [hdiff y, Complex.normSq_mul])]
  rw [← Finset.mul_sum]
  rw [sum_workDim_normSq_sub_eq_pmDist_sq m w bits g h]
  -- |1/√2^m|² = 1/2^m
  have hscalar : Complex.normSq ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ)) = 1 / 2 ^ m := by
    rw [show ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ)) = ((1 / Real.sqrt (2 ^ m : ℝ) : ℝ) : ℂ) from by
          push_cast; ring]
    rw [Complex.normSq_ofReal, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by positivity)]
  rw [hscalar]
  -- (pmDist g h)² ≤ Lbudget  via H3.1 (square the √-bound).
  have hH31 : pmDist g h ≤ Real.sqrt (Lbudget numWin cm) := by
    rw [hg, hh]
    exact gidneyInPlaceWithSwap_coset_pmDist_deviation w bits numWin N cm (mult k) kInv z
      TfamK TfamKinv hTfamK hTfamKinv hw hbits hN hz hkkinv hfit hxfit
  have hsq : (pmDist g h) ^ 2 ≤ Lbudget numWin cm := by
    have := mul_self_le_mul_self (pmDist_nonneg g h) hH31
    rw [Real.mul_self_sqrt (Lbudget_nonneg numWin cm)] at this
    nlinarith [this]
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-! ## §3. H3.2b — the actual-side controlled local `pmDist` deviation (the telescope `hlocal`). -/

/-- **H3.2b — the actual-side controlled local `pmDist` deviation.**  At one oracle stage `k < m`,
    on any state `Φ` in `IdealCosetForm`, the physical QPE stage `qpeStageMap … f_runwayPhysical k`
    deviates from the ideal stage `qpeStageMap … f_runwayIdeal k` by at most `√(8·numWin/2^cm)` in
    the ℓ² distance `pmDist`.  This is exactly the per-step local deviation
    `PmDistTelescope.pmDist_orbit_telescope`'s `hlocal` consumes (with `Φ := orbitState Fi init k`,
    the ideal trajectory point, which is in `IdealCosetForm` by P1.2's
    `idealCosetForm_orbit_runway_direct`).

    ROUTE: `pmDist_sq` → `sum_jointIdx_eq` (the bijection split, NO `2^m` blowup) → per phase
    branch `x`, INACTIVE ⇒ the per-branch sum is `0` (`qpeStage_oracle_jointIdx`'s `if_neg`),
    ACTIVE ⇒ `active_branch_local_le` bounds it by `(1/2^m)·(8·numWin/2^cm)` (H3.1 after the
    `E2shor_dim_eq` work→coset reindex) → `∑_x ≤ 2^m · (1/2^m)·L = L` → `√`.

    The realization hypotheses `hf_physical` (the physical gate realizes the gidney coset
    multiplier) and `hf_runway` (the ideal gate realizes the clean coset shift) are DISTINCT and
    carried explicitly; the budget/coprime/fit hypotheses feed H3.1; the scalar is PINNED in
    `IdealCosetForm` (so NO `pmNorm Φ ≤ 1` side hypothesis is needed). -/
theorem qpeStage_E2_local_pmDist_deviation
    (m w bits numWin N cm k kInv : Nat) (hk : k < m)
    (TfamK TfamKinv : Nat → Nat → Nat)
    (f_runwayPhysical f_runwayIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwtP : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayPhysical j))
    (hwtI : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (mult : Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue (mult k) N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hkkinv : (kInv * mult k) % N = 1 % N)
    (hfit : ∀ z : Nat, z < N → (mult k * z) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (hxfit : ∀ z : Nat, z < N → z + (2 ^ cm - 1) * N < 2 ^ bits)
    (Φ : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (hΦ : IdealCosetForm m w bits N cm Φ)
    (hf_physical : ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayPhysical (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = (FormalRV.Framework.uc_eval (Gate.toUCom (cosetDim w bits)
                (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin))
              * cosetInputVec w bits N cm z 0) (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_runway : ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = cosetInputVec w bits N cm ((mult k * z) % N) 0
              (Fin.cast (E2shor_dim_eq m w bits) y) 0) :
    pmDist (qpeStageMap m bits (cosetAnc w bits) f_runwayPhysical k Φ)
        (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal k Φ)
      ≤ Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) := by
  -- The dvd witness for the joint-index split.
  have hdvd : (2 ^ m) ∣ (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) :=
    ⟨2 ^ bits * 2 ^ (cosetAnc w bits), by rw [mul_assoc]⟩
  set Fa := qpeStageMap m bits (cosetAnc w bits) f_runwayPhysical k Φ with hFa
  set Fi := qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal k Φ with hFi
  -- pmDist² ≤ Lbudget.
  have hsq : (pmDist Fa Fi) ^ 2 ≤ Lbudget numWin cm := by
    rw [pmDist_sq]
    -- split the full-register sum into ∑_x ∑_y via the joint-index bijection
    rw [← sum_jointIdx_eq hdvd (fun i => Complex.normSq (Fa i 0 - Fi i 0))]
    -- each phase branch's inner sum is ≤ (1/2^m)·Lbudget
    have hbranch : ∀ x : Fin (2 ^ m),
        (∑ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            Complex.normSq (Fa (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
                            - Fi (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0))
          ≤ (1 / 2 ^ m) * Lbudget numWin cm := by
      intro x
      obtain ⟨z, hz, hslice⟩ := hΦ x
      by_cases hcb : controlBit m k hk x
      · -- ACTIVE: the H3.1 local bound.
        exact active_branch_local_le m w bits numWin N cm k kInv hk TfamK TfamKinv
          f_runwayPhysical f_runwayIdeal hwtP hwtI mult hTfamK hTfamKinv hw hbits hN hkkinv
          Φ x z hz (hfit z hz) (hxfit z hz) hcb hslice (hf_physical z hz) (hf_runway z hz)
      · -- INACTIVE: every term vanishes (both stages are the identity on this branch).
        have hzero : ∀ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            Complex.normSq (Fa (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
                            - Fi (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0) = 0 := by
          intro y
          rw [hFa, hFi,
              qpeStage_oracle_jointIdx m bits (cosetAnc w bits) k hk f_runwayPhysical hwtP Φ x y,
              qpeStage_oracle_jointIdx m bits (cosetAnc w bits) k hk f_runwayIdeal hwtI Φ x y,
              if_neg hcb, if_neg hcb, sub_self, Complex.normSq_zero]
        rw [Finset.sum_congr rfl (fun y _ => hzero y), Finset.sum_const_zero]
        exact mul_nonneg (by positivity) (Lbudget_nonneg numWin cm)
    -- aggregate: ∑_x (inner) ≤ ∑_x (1/2^m)·L = 2^m·(1/2^m)·L = L.
    calc ∑ x : Fin (2 ^ m),
            ∑ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              Complex.normSq (Fa (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
                              - Fi (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0)
        ≤ ∑ _x : Fin (2 ^ m), (1 / 2 ^ m) * Lbudget numWin cm :=
          Finset.sum_le_sum (fun x _ => hbranch x)
      _ = Lbudget numWin cm := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [show ((2 ^ m : Nat) : ℝ) * (1 / 2 ^ m * Lbudget numWin cm)
                = ((2 ^ m : Nat) : ℝ) * (1 / 2 ^ m) * Lbudget numWin cm from by ring]
          rw [show ((2 ^ m : Nat) : ℝ) = (2 : ℝ) ^ m from by push_cast; ring]
          rw [mul_one_div, div_self (by positivity : (2 : ℝ) ^ m ≠ 0), one_mul]
  -- √ both sides.
  have h := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (pmDist_nonneg Fa Fi)] at h
  rwa [show Lbudget numWin cm = 8 * (numWin : ℝ) / 2 ^ cm from rfl] at h

end FormalRV.Shor.GidneyInPlace.E2LocalDeviation
