/-
  FormalRV.Shor.GidneyInPlace.InPlaceE2HworkInt — F2 brick 1: the E₂ `hwork_int`
  matrix/intertwining identity (cast-heavy bridge).
  ════════════════════════════════════════════════════════════════════════════

  The exact `hwork_int` slot of `ControlOracleLift.controlled_shifted_oracle_hintertwine`, but with
  the embedding matrix `cosetEmbedMat` replaced by the CANONICAL-ZEROED E₂ matrix `E2matZ` (the data
  matrix of `E2shorZ`).  Discharged from T2 (`inplace_agree_off_union`) + the explicit realization
  hypotheses (casts exposed):

    • `hf_coset` : `workMat … f_coset = uc_eval(gidneyInPlaceWithSwap)` at the `E2shor_dim_eq` cast;
    • `hf_ideal` : `workMat … f_ideal a b = [a.val = idealPerm b]`, where the IDEAL permutation
      FIXES non-canonical indices: `idealPerm b = if b.val < N then (k·b.val)%N else b.val`.
      (Per the refined spec — without this, the zero-column embedding is NOT an intertwiner.)

  Proof by cases on the work column `y2`:
    • `y2.val < N` (canonical): LHS = `(uc_eval(gate)·cosetInputVec y2 0)(cast y)` (matrix-vector
      product via `hf_coset` + `finCongr` reindex); RHS = `cosetInputVec ((k·y2)%N) 0 (cast y)` (the
      single `f_ideal`-permuted column); equal off `inplaceUnionBad` by `inplace_agree_off_union`.
    • `y2.val ≥ N` (non-canonical): LHS = 0 (`E2matZ` zero column) and RHS = 0 (`f_ideal` fixes `y2`,
      `E2matZ` zero at that column).

  Casts kept explicit: `E2shor_dim_eq` (data factor = `2^cosetDim`), `Fin.cast`/`finCongr`; the bad
  set is `inplaceUnionBad` transported by the `E2shor_dim_eq` cast via the `hbad` hypothesis.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Embedding.Def.InPlaceUnionAgree
import FormalRV.Shor.GidneyInPlace.Embedding.Def.InPlaceTwoRegEmbedCanon
import FormalRV.Shor.GidneyInPlace.QPE.Proof.ControlOracleLift

namespace FormalRV.Shor.GidneyInPlace.InPlaceE2HworkInt

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate (gidneyInPlaceWithSwap)
open FormalRV.Shor.GidneyInPlace.ControlOracleLift (workMat)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.GidneyInPlace.InPlaceUnionAgree (inplaceUnionBad inplace_agree_off_union)

/-- **The canonical-zeroed E₂ data matrix** (entry `(a, b)` = row `a`, column `b`): the column `b`
    is `cosetInputVec b.val 0` (read at the `E2shor_dim_eq`-cast row) when `b.val < N`, else `0`.
    This is the data matrix of `E2shorZ`. -/
noncomputable def E2matZ (m w bits N cm : Nat)
    (a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) : ℂ :=
  if b.val < N then
    cosetInputVec w bits N cm b.val 0 (Fin.cast (E2shor_dim_eq m w bits) a) 0
  else 0

/-- **F2 brick 1 — the E₂ `hwork_int` matrix identity.**  Off `bad_step` (the `E2shor_dim_eq`
    transport of `inplaceUnionBad`), the work-level intertwining `workMat(f_coset)·E2matZ =
    E2matZ·workMat(f_ideal)` holds for EVERY column `y2`.  Canonical columns via
    `inplace_agree_off_union`; non-canonical via the zeroed column + the non-canonical-fixing
    `f_ideal`. -/
theorem E2_hwork_int
    (m w bits numWin N cm k kInv kstep : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfitAll : ∀ z, z < N → (k * z) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (hNdata : N ≤ (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)
    (f_coset f_ideal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hf_coset : ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        workMat m bits (cosetAnc w bits) kstep f_coset a b
          = Framework.uc_eval (Gate.toUCom (cosetDim w bits)
              (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin))
              (Fin.cast (E2shor_dim_eq m w bits) a) (Fin.cast (E2shor_dim_eq m w bits) b))
    (hf_ideal : ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        workMat m bits (cosetAnc w bits) kstep f_ideal a b
          = if a.val = (if b.val < N then (k * b.val) % N else b.val) then 1 else 0)
    (bad_step : Finset (Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)))
    (hbad : ∀ y, y ∉ bad_step →
        Fin.cast (E2shor_dim_eq m w bits) y ∉ inplaceUnionBad w bits numWin N cm k TfamK TfamKinv hw hbits)
    (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) (hy : y ∉ bad_step)
    (y2 : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    (∑ yp, workMat m bits (cosetAnc w bits) kstep f_coset y yp * E2matZ m w bits N cm yp y2)
      = (∑ yp, E2matZ m w bits N cm y yp * workMat m bits (cosetAnc w bits) kstep f_ideal yp y2) := by
  classical
  by_cases hy2 : y2.val < N
  · -- canonical column
    have hpermN : (k * y2.val) % N < N := Nat.mod_lt _ hN
    have hpermD : (k * y2.val) % N < (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m :=
      lt_of_lt_of_le hpermN hNdata
    -- LHS = (uc_eval(gate) * cosetInputVec y2.val 0) (cast y)
    have hLHS : (∑ yp, workMat m bits (cosetAnc w bits) kstep f_coset y yp * E2matZ m w bits N cm yp y2)
        = (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
              (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin))
            * cosetInputVec w bits N cm y2.val 0) (Fin.cast (E2shor_dim_eq m w bits) y) 0 := by
      rw [Matrix.mul_apply,
          ← Equiv.sum_comp (finCongr (E2shor_dim_eq m w bits))
            (fun j => Framework.uc_eval (Gate.toUCom (cosetDim w bits)
                (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin))
                (Fin.cast (E2shor_dim_eq m w bits) y) j
              * cosetInputVec w bits N cm y2.val 0 j 0)]
      refine Finset.sum_congr rfl (fun yp _ => ?_)
      rw [hf_coset y yp, E2matZ, if_pos hy2]
      rfl
    -- RHS = cosetInputVec ((k*y2.val)%N) 0 (cast y)
    have hRHS : (∑ yp, E2matZ m w bits N cm y yp * workMat m bits (cosetAnc w bits) kstep f_ideal yp y2)
        = cosetInputVec w bits N cm ((k * y2.val) % N) 0 (Fin.cast (E2shor_dim_eq m w bits) y) 0 := by
      rw [Finset.sum_eq_single (⟨(k * y2.val) % N, hpermD⟩ :
            Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m))]
      · rw [hf_ideal _ y2, if_pos hy2, if_pos rfl, mul_one, E2matZ, if_pos hpermN]
      · intro yp _ hypne
        rw [hf_ideal yp y2, if_pos hy2,
            if_neg (fun h => hypne (Fin.ext (by rw [h]))), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hLHS, hRHS]
    exact inplace_agree_off_union w bits numWin N cm k kInv TfamK TfamKinv hTfamK hTfamKinv
      hw hbits hN hkkinv hfitAll (Fin.cast (E2shor_dim_eq m w bits) y) (hbad y hy) y2.val hy2
  · -- non-canonical column: both sides are 0
    have hLHS0 : (∑ yp, workMat m bits (cosetAnc w bits) kstep f_coset y yp * E2matZ m w bits N cm yp y2)
        = 0 := by
      refine Finset.sum_eq_zero (fun yp _ => ?_)
      rw [E2matZ, if_neg hy2, mul_zero]
    have hRHS0 : (∑ yp, E2matZ m w bits N cm y yp * workMat m bits (cosetAnc w bits) kstep f_ideal yp y2)
        = 0 := by
      rw [Finset.sum_eq_single y2]
      · rw [hf_ideal y2 y2, if_neg hy2, if_pos rfl, mul_one, E2matZ, if_neg hy2]
      · intro yp _ hypne
        rw [hf_ideal yp y2, if_neg hy2,
            if_neg (fun h => hypne (Fin.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hLHS0, hRHS0]

end FormalRV.Shor.GidneyInPlace.InPlaceE2HworkInt
