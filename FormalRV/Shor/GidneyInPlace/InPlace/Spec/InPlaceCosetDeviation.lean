/-
  FormalRV.Shor.GidneyInPlace.InPlaceCosetDeviation — G3: the SEALED two-register
  Architecture-B deviation capstone for the swap-form in-place coset multiplier.
  ════════════════════════════════════════════════════════════════════════════

  The single contract-level object the downstream (marginal) route consumes — built from the
  off-bad-exact agreement plus BOTH bad-set masses (NOT from the old frozen Arch-A norm bound):

    normSqDist (uc_eval(gidneyInPlaceWithSwap) · cosetInputVec x 0) (cosetInputVec ((k·x)%N) 0)
      ≤ 4·numWin / 2^cm

  Assembled by `normSqDist_le_of_agree_off` at `W = 2·numWin/2^cm` from:
    • T2 `gidneyInPlaceWithSwap_agree_off_explicit` — `hagree`, off the EXACT `inplaceBadSetB`;
    • D5 `inplaceBadSetB_evolved_bornWeight_le`      — `hw₁` (evolved-state mass);
    • T3 `inplaceBadSetB_target_bornWeight_le_closed`— `hw₂` (target-state mass, unconditional).
  Both masses are `2·numWin/2^cm` ⇒ `2·W = 4·numWin/2^cm`; `numWin` stays physical.

  Distinct from the Arch-A `gidneyTwoRegInPlace_coset_norm_bound` (which is the NO-swap gate
  `pass1;reverse pass2`, output in the b-block, proven via the triangle/leg backbone).  This is
  the SWAP form `…;swapAB` (output back in the a-block) and is proven by the off-bad/bad-mass
  route — the form the single-register/marginal packaging needs.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Mass.InPlaceTargetMassLegClosed

namespace FormalRV.Shor.GidneyInPlace.InPlaceCosetDeviation

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer (normSqDist)
open FormalRV.Shor.CosetBornWeight (normSqDist_le_of_agree_off)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate (gidneyInPlaceWithSwap)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree (inplaceBadSetB)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedMassBound (inplaceBadSetB_evolved_bornWeight_le)
open FormalRV.Shor.GidneyInPlace.InPlaceTargetMassLegClosed (inplaceBadSetB_target_bornWeight_le_closed)
open FormalRV.Shor.GidneyInPlace.InPlaceAgreeOffExplicit (gidneyInPlaceWithSwap_agree_off_explicit)

/-- **G3 — two-register Architecture-B deviation capstone.**  The swap-form in-place coset
    multiplier `gidneyInPlaceWithSwap`, applied to the clean two-register coset input
    `cosetInputVec x 0`, deviates from the post-swap target `cosetInputVec ((k·x)%N) 0` by at most
    `4·numWin/2^cm` in Born-L¹ (`normSqDist`).  Built unconditionally from the off-`inplaceBadSetB`
    agreement (T2) and BOTH `inplaceBadSetB` masses (D5 evolved + T3 target), via
    `normSqDist_le_of_agree_off` at `W = 2·numWin/2^cm`. -/
theorem gidneyInPlaceWithSwap_coset_deviation
    (w bits numWin N cm k kInv x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfit : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (hxfit : x + (2 ^ cm - 1) * N < 2 ^ bits) :
    normSqDist
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin))
          * cosetInputVec w bits N cm x 0)
        (cosetInputVec w bits N cm ((k * x) % N) 0)
      ≤ 4 * (numWin : ℝ) / 2 ^ cm := by
  have h := normSqDist_le_of_agree_off
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
  calc normSqDist _ _ ≤ 2 * (2 * (numWin : ℝ) / 2 ^ cm) := h
    _ = 4 * (numWin : ℝ) / 2 ^ cm := by ring

end FormalRV.Shor.GidneyInPlace.InPlaceCosetDeviation
