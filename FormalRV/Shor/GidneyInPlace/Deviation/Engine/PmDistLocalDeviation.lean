/-
  FormalRV.Shor.GidneyInPlace.PmDistLocalDeviation — H3.1 of the hybrid/telescoping route:
  the LOCAL controlled-step deviation expressed in the ℓ² distance `pmDist`.
  ════════════════════════════════════════════════════════════════════════════

  H1 (`PmDistTelescope.pmDist_orbit_telescope`) needs a per-step local deviation `δ k` in the
  ℓ² distance `pmDist` (NOT the L1-Born `normSqDist`, which cannot telescope through the
  inverse QFT).  This file provides:

    • `pmDist_le_of_agree_off` — the generic ℓ² analogue of
      `CosetBornWeight.normSqDist_le_of_agree_off`: if `s₁ s₂` agree (amplitude-level) off a
      finite set `B` and each carries Born mass `≤ W` on `B`, then `pmDist s₁ s₂ ≤ √(4·W)`.
      (Proof = `pmDist_sq` → off-`B` collapse → pointwise `‖a−b‖² ≤ 2(‖a‖²+‖b‖²)` → the two
      Born masses → one `Real.sqrt` step.  The square root is the genuine, unitary-invariant
      currency the inverse-QFT stage demands; it is what makes the orbit error term `∑ δ`
      square-root rather than the unachievable linear bad-mass term.)

    • `gidneyInPlaceWithSwap_coset_pmDist_deviation` — the coset-register instantiation: the
      swap-form in-place coset multiplier deviates from its post-swap target by at most
      `√(8·numWin/2^cm)` in `pmDist`.  Built from the IDENTICAL three inputs that feed the L1
      capstone `InPlaceCosetDeviation.gidneyInPlaceWithSwap_coset_deviation`:
        – T2 `gidneyInPlaceWithSwap_agree_off_explicit`  (amplitude agreement off `inplaceBadSetB`);
        – D5 `inplaceBadSetB_evolved_bornWeight_le`       (evolved-state mass `≤ 2·numWin/2^cm`);
        – T3 `inplaceBadSetB_target_bornWeight_le_closed` (target-state mass `≤ 2·numWin/2^cm`),
      at `W = 2·numWin/2^cm`, giving `√(4·W) = √(8·numWin/2^cm)`.

  NOTE (the remaining H3 work, NOT done here): lifting this coset-register bound through
  `control k (qpeOracle …)` / `jointIdx` to the joint QPE dimension at the ideal trajectory
  point — that is the per-step `δ k` H1 actually consumes, and the one piece structurally
  related to the (dead) EmbedAgreeOff per-step lemma; it is audited separately before building.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.  The generic
  `pmDist_le_of_agree_off` proof was de-risked via `lean_run_code` before landing.
-/
import FormalRV.Shor.Approx.GracefulDegradation
import FormalRV.Shor.GidneyInPlace.InPlace.Spec.InPlaceCosetDeviation

namespace FormalRV.Shor.GidneyInPlace.PmDistLocalDeviation

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.Approx (pmDist pmDist_sq pmDist_nonneg)
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate (gidneyInPlaceWithSwap)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree (inplaceBadSetB)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedMassBound (inplaceBadSetB_evolved_bornWeight_le)
open FormalRV.Shor.GidneyInPlace.InPlaceTargetMassLegClosed (inplaceBadSetB_target_bornWeight_le_closed)
open FormalRV.Shor.GidneyInPlace.InPlaceAgreeOffExplicit (gidneyInPlaceWithSwap_agree_off_explicit)

/-! ## §1. The generic ℓ² agree-off bound (mirror of `normSqDist_le_of_agree_off`). -/

/-- **The ℓ² analytic core.**  If `s₁ s₂` agree (amplitude-level) off the finite set `B`, and
    each carries Born mass `≤ W` on `B`, then `pmDist s₁ s₂ ≤ √(4·W)`.  Off `B` the difference
    vanishes; on `B` the pointwise bound `‖a−b‖² ≤ 2(‖a‖²+‖b‖²)` turns the two Born masses into
    `pmDist² ≤ 4·W`. -/
theorem pmDist_le_of_agree_off {dim : Nat} (s₁ s₂ : QState dim)
    (B : Finset (Fin dim)) (W : ℝ)
    (hagree : ∀ i, i ∉ B → s₁ i 0 = s₂ i 0)
    (hw₁ : bornWeightOn s₁ B ≤ W) (hw₂ : bornWeightOn s₂ B ≤ W) :
    pmDist s₁ s₂ ≤ Real.sqrt (4 * W) := by
  have hsq : (pmDist s₁ s₂) ^ 2 ≤ 4 * W := by
    rw [pmDist_sq]
    have hcollapse : (∑ i, Complex.normSq (s₁ i 0 - s₂ i 0))
        = ∑ i ∈ B, Complex.normSq (s₁ i 0 - s₂ i 0) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ B)
      intro i _ hiB
      rw [hagree i hiB, sub_self, Complex.normSq_zero]
    rw [hcollapse]
    calc ∑ i ∈ B, Complex.normSq (s₁ i 0 - s₂ i 0)
        ≤ ∑ i ∈ B, 2 * (Complex.normSq (s₁ i 0) + Complex.normSq (s₂ i 0)) := by
          apply Finset.sum_le_sum
          intro i _
          nlinarith [Complex.normSq_nonneg (s₁ i 0 + s₂ i 0),
                     Complex.normSq_add (s₁ i 0) (s₂ i 0),
                     Complex.normSq_sub (s₁ i 0) (s₂ i 0)]
      _ = 2 * (bornWeightOn s₁ B + bornWeightOn s₂ B) := by
          unfold bornWeightOn
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 2 * (W + W) := mul_le_mul_of_nonneg_left (add_le_add hw₁ hw₂) (by norm_num)
      _ = 4 * W := by ring
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (pmDist_nonneg s₁ s₂)] at h

/-! ## §2. The coset-register local `pmDist` deviation (H3.1 deliverable). -/

/-- **H3.1 — the coset-register local controlled-step deviation in `pmDist`.**  The swap-form
    in-place coset multiplier `gidneyInPlaceWithSwap`, applied to the clean two-register coset
    input `cosetInputVec x 0`, deviates from the post-swap target `cosetInputVec ((k·x)%N) 0` by
    at most `√(8·numWin/2^cm)` in the ℓ² distance.  Built from the IDENTICAL three inputs as the
    L1 capstone (T2 agreement + D5 evolved mass + T3 target mass) via `pmDist_le_of_agree_off` at
    `W = 2·numWin/2^cm`.  This is the local oracle deviation H1 telescopes (one per oracle stage). -/
theorem gidneyInPlaceWithSwap_coset_pmDist_deviation
    (w bits numWin N cm k kInv x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfit : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (hxfit : x + (2 ^ cm - 1) * N < 2 ^ bits) :
    pmDist
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin))
          * cosetInputVec w bits N cm x 0)
        (cosetInputVec w bits N cm ((k * x) % N) 0)
      ≤ Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) := by
  have h := pmDist_le_of_agree_off
    (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin))
      * cosetInputVec w bits N cm x 0)
    (cosetInputVec w bits N cm ((k * x) % N) 0)
    (inplaceBadSetB w bits numWin N cm k x TfamK TfamKinv hw hbits)
    (2 * (numWin : ℝ) / 2 ^ cm)
    (fun i hiB => gidneyInPlaceWithSwap_agree_off_explicit w bits numWin N cm k kInv x
      TfamK TfamKinv hTfamK hTfamKinv hw hbits hN hxN hkkinv hfit i hiB)
    (inplaceBadSetB_evolved_bornWeight_le w bits numWin N cm k kInv x TfamK TfamKinv
      hTfamK hTfamKinv hw hbits hN hxN hkkinv hfit hxfit)
    (inplaceBadSetB_target_bornWeight_le_closed w bits numWin N cm k kInv x TfamK TfamKinv
      hTfamK hTfamKinv hw hbits hN hxN hkkinv hfit hxfit)
  calc pmDist _ _ ≤ Real.sqrt (4 * (2 * (numWin : ℝ) / 2 ^ cm)) := h
    _ = Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) := by congr 1; ring

end FormalRV.Shor.GidneyInPlace.PmDistLocalDeviation
