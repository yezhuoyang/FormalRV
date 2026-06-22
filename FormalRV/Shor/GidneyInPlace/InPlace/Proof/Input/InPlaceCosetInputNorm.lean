/-
  FormalRV.Shor.GidneyInPlace.InPlaceCosetInputNorm — T1: the UNCONDITIONAL
  normalization of the two-register coset input.
  ════════════════════════════════════════════════════════════════════════════

  Discharges the `hnorm` frontier of `InPlaceTargetMassLeg`: the two-register coset input
  `cosetInputVec x 0` is a UNIT-norm state (total Born mass = 1), for every residue `x`.

  ROUTE (the `eGid` product factorization).  Reindex the total-mass sum over
  `Fin (2^cosetDim)` through the BRICK-1 product equiv `eGid` (data factor = the b-block):
    bornWeightOn (cosetInputVec x 0) univ
      = ∑_ctrl ∑_z ‖cosetInputVec x 0 (eGid (ctrl,z))‖²            (sum_prodEquiv_eq)
      = ∑_ctrl ∑_z ‖betaB ctrl‖² · ‖cosetState 0 z‖²               (branchOfE_…_passB, normSq_mul)
      = (∑_ctrl ‖betaB ctrl‖²) · (∑_z ‖cosetState 0 z‖²)           (factor)
      = 1 · 1 = 1
  The b-factor is exactly `cosetState_normalized`; the a-factor `∑‖betaB‖² = 1`
  (`betaB_normSq_total`) is the EXACT version of `leg1_hweight` (which only gave `≤ 1`),
  via `betaB_xCtrlGid` + `clean_ctrl_eq_xCtrlGid` + `cosetWindow_card`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceComposedAgree

namespace FormalRV.Shor.GidneyInPlace.InPlaceCosetInputNorm

open FormalRV.Framework FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedCircuit (decodeReg_lt_two_pow)
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.ApproxOp (cosetState cosetState_normalized)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow cosetWindow_card)
open FormalRV.Shor.GidneyInPlace.BranchFactor (branchOfE sum_prodEquiv_eq)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate (eGid pass1_accfit)
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput (xCtrlGid)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg
  (aBase bBase betaB ctrlFunB branchOfE_cosetInputTwoReg_passB)
open FormalRV.Shor.GidneyInPlace.InPlaceLeg1 (clean_ctrl_eq_xCtrlGid leg1_xval_roundtrip)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree (betaB_xCtrlGid)

/-- The single Born value `‖(1/√2^cm : ℝ) : ℂ‖² = 1/2^cm`. -/
private theorem normSq_coeff (cm : Nat) :
    Complex.normSq ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) = 1 / 2 ^ cm := by
  rw [Complex.normSq_ofReal, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by positivity)]

/-! ## §1. The EXACT betaB total `∑ ‖betaB‖² = 1`. -/

/-- **Exact β-weight total.**  Summed over ALL control branches, `‖betaB‖²` is exactly `1`
    (the EXACT version of `leg1_hweight`'s `≤ 1`).  Off the active image
    `{xCtrlGid ja : ja ∈ window x}` the weight is `0`; on it (injectively indexed by the
    `2^cm`-element window) each `‖betaB‖² = 1/2^cm`. -/
theorem betaB_normSq_total (w bits numWin N cm x : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hN : 0 < N) (hfit_x : x + (2 ^ cm - 1) * N < 2 ^ bits) :
    ∑ ctrl : Fin (2 ^ (cosetDim w bits - bits)),
        Complex.normSq (betaB w bits N cm x ctrl.val) = 1 := by
  classical
  set W : Finset (Fin (2 ^ bits)) := cosetWindow (2 ^ bits) N cm x with hWdef
  set img : Finset (Fin (2 ^ (cosetDim w bits - bits))) :=
    W.image (fun ja : Fin (2 ^ bits) => xCtrlGid w bits numWin (bBase w bits) (aBase w) ja.val)
    with himg
  -- off the active image, betaB = 0
  have hoff : ∀ ctrl ∈ (Finset.univ : Finset (Fin (2 ^ (cosetDim w bits - bits)))),
      ctrl ∉ img → Complex.normSq (betaB w bits N cm x ctrl.val) = 0 := by
    intro ctrl _ hni
    by_contra hne
    have hbne : betaB w bits N cm x ctrl.val ≠ 0 := fun h => hne (by rw [h, Complex.normSq_zero])
    unfold betaB at hbne
    split_ifs at hbne with hclean hawin
    · exact hni (by
        rw [himg, Finset.mem_image]
        exact ⟨⟨decodeReg (fun i => aBase w + i) bits (ctrlFunB w bits ctrl.val),
            decodeReg_lt_two_pow _ _ _⟩, hawin,
          (clean_ctrl_eq_xCtrlGid w bits numWin _ hw hbits ctrl hclean rfl).symm⟩)
    · exact hbne rfl
    · exact hbne rfl
  rw [← Finset.sum_subset (Finset.subset_univ img) hoff]
  -- reindex over the injective image of the window
  rw [himg, Finset.sum_image (by
    intro a _ b _ hab
    apply Fin.ext
    calc a.val
        = decodeReg (fun i => aBase w + i) bits
            (ctrlFunB w bits (xCtrlGid w bits numWin (bBase w bits) (aBase w) a.val).val) :=
          (leg1_xval_roundtrip w bits numWin a.val hw hbits a.isLt).symm
      _ = decodeReg (fun i => aBase w + i) bits
            (ctrlFunB w bits (xCtrlGid w bits numWin (bBase w bits) (aBase w) b.val).val) := by
          rw [congrArg Fin.val hab]
      _ = b.val := leg1_xval_roundtrip w bits numWin b.val hw hbits b.isLt)]
  -- each window term is exactly 1/2^cm; sum = card·(1/2^cm) = 1
  rw [Finset.sum_congr rfl (fun ja hja => by
    rw [betaB_xCtrlGid w bits numWin N cm x ja.val hw hbits ja.isLt,
      if_pos (show (⟨ja.val, ja.isLt⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm x from
        by rw [hWdef] at hja; exact hja), normSq_coeff]
    : ∀ ja ∈ W, Complex.normSq (betaB w bits N cm x
        (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja.val).val) = 1 / 2 ^ cm)]
  rw [Finset.sum_const, hWdef, cosetWindow_card (2 ^ bits) N cm x hN hfit_x, nsmul_eq_mul,
    mul_one_div]
  push_cast
  exact div_self (by positivity)

/-! ## §2. The two-register coset input is normalized. -/

/-- **T1 — two-register coset-input normalization.**  `bornWeightOn (cosetInputVec x 0) univ = 1`
    for every `x` with the standard fit.  Discharges `InPlaceTargetMassLeg`'s `hnorm`. -/
theorem cosetInputVec_normalized (w bits numWin N cm x : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hN : 0 < N) (hfit_x : x + (2 ^ cm - 1) * N < 2 ^ bits) :
    bornWeightOn (cosetInputVec w bits N cm x 0) Finset.univ = 1 := by
  classical
  have hfit0 : (0 : Nat) + (2 ^ cm - 1) * N < 2 ^ bits := by omega
  -- the b-factor total = 1
  have hz1 : (∑ z : Fin (2 ^ bits), Complex.normSq (cosetState (2 ^ bits) N cm 0 z 0)) = 1 := by
    have h := cosetState_normalized (2 ^ bits) N cm 0 hN hfit0
    unfold bornWeightOn at h
    exact h
  -- bornWeightOn = ∑ normSq, then reindex via eGid
  have hb : bornWeightOn (cosetInputVec w bits N cm x 0) Finset.univ
      = ∑ i : Fin (2 ^ cosetDim w bits), Complex.normSq (cosetInputVec w bits N cm x 0 i 0) := rfl
  rw [hb, ← sum_prodEquiv_eq (eGid w bits (bBase w bits) (pass1_accfit w bits))
        (fun i => Complex.normSq (cosetInputVec w bits N cm x 0 i 0))]
  -- factor each branch via passB
  have hbranch : ∀ (ctrl : Fin (2 ^ (cosetDim w bits - bits))) (z : Fin (2 ^ bits)),
      Complex.normSq (cosetInputVec w bits N cm x 0
          (eGid w bits (bBase w bits) (pass1_accfit w bits) (ctrl, z)) 0)
        = Complex.normSq (betaB w bits N cm x ctrl.val)
          * Complex.normSq (cosetState (2 ^ bits) N cm 0 z 0) := by
    intro ctrl z
    have hval := congrFun (congrFun (branchOfE_cosetInputTwoReg_passB w bits N cm x 0 ctrl) z) 0
    show Complex.normSq (cosetInputVec w bits N cm x 0 _ 0) = _
    rw [show cosetInputVec w bits N cm x 0
          (eGid w bits (bBase w bits) (pass1_accfit w bits) (ctrl, z)) 0
        = betaB w bits N cm x ctrl.val * cosetState (2 ^ bits) N cm 0 z 0 from hval,
      Complex.normSq_mul]
  simp_rw [hbranch]
  -- factor the product sum
  rw [Finset.sum_congr rfl (fun ctrl _ => by
    rw [← Finset.mul_sum, hz1, mul_one]
    : ∀ ctrl ∈ (Finset.univ : Finset (Fin (2 ^ (cosetDim w bits - bits)))),
        (∑ z : Fin (2 ^ bits), Complex.normSq (betaB w bits N cm x ctrl.val)
            * Complex.normSq (cosetState (2 ^ bits) N cm 0 z 0))
          = Complex.normSq (betaB w bits N cm x ctrl.val))]
  exact betaB_normSq_total w bits numWin N cm x hw hbits hN hfit_x

end FormalRV.Shor.GidneyInPlace.InPlaceCosetInputNorm
