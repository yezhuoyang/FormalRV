/-
  FormalRV.Shor.GidneyInPlace.InPlaceComposedMassBound
  ──────────────────────────────────────────────────────
  PACKAGING checkpoint D5 (the bad-set Born-mass CAPSTONE of Architecture B):
  the EVOLVED two-register state's Born mass on the FULL agree-off bad set
  `inplaceBadSetB` is `≤ 2·numWin/2^cm`.

  This assembles, with NO new arithmetic, three already-verified pieces:
    • `inplace_hred`                     — the `σ.symm`-preimage of `B`, restricted to the
      input support, lands in `inplaceBadIn` (covers the FULL symmetric-difference `B`,
      i.e. BOTH the `σ(badIn)\targetSupp` leg and the `targetSupp\σ(goodIn)` leg — the
      latter has empty nonzero-input preimage, so no separate "target leg" mass count is
      needed once the transport is taken on the EVOLVED state);
    • `bornWeightOn_evolved_le_badInput` — generic permutation-pushforward mass transport;
    • `inplaceBadIn_bornWeight_le`       — D4: the input bad set's mass `≤ 2·numWin/2^cm`,
  and rewrites the evolved state into `permState σ.symm` via `uc_eval_eq_permState`.

  Physical reading: the genuine composite gate `gidneyInPlaceWithSwap`
  (`(b += k·a) ; reverse(a += b·kInv) ; swapAB`), applied to the clean two-register coset
  input `|coset_x⟩_a ⊗ |coset_0⟩_b`, lands `≤ 2·numWin/2^cm` of its Born mass on the
  symmetric-difference bad set `B` where the off-`B` exact coset shift
  (`gidneyInPlaceWithSwap_agree_off`) can fail.  Together with that agree-off this is the
  Architecture-B (off-bad-exact + bad-mass-bounded) counterpart to the Architecture-A
  `normSqDist ≤ 4·numWin/2^cm` deviation bound — the direct input the deviation/transfer
  framework consumes.  STILL on the TWO-register `cosetInputVec`; the single-register
  packaging (register-iso lift + logical output convention + D6 factor-2 roll-up) is the
  remaining structural lift toward `inplaceReducedLookupCosetMul_shift`.

  ⚠ SCOPE (E0 audit, 2026-06-18).  This theorem is the EVOLVED-state half ONLY.  The deviation
  consumer `CosetBornWeight.normSqDist_le_of_agree_off` requires the bad mass on BOTH states —
  the evolved state (this theorem, `hw₁`) AND the TARGET state (`hw₂`).  The target half is
  `InPlaceTargetMassLeg.inplaceBadSetB_target_bornWeight_le`.  Do NOT feed the deviation lemma
  with this theorem alone.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceReverseCount

namespace FormalRV.Shor.GidneyInPlace.InPlaceComposedMassBound

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.GidneyInPlace.ApproxOp (permState)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_eq_permState)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate
  (gidneyInPlaceWithSwap gidneyInPlaceWithSwap_wellTyped)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedMass (bornWeightOn_evolved_le_badInput)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree
  (inplaceSigma inplaceBadSetB inplaceBadIn inplace_hred)
open FormalRV.Shor.GidneyInPlace.InPlaceReverseCount (inplaceBadIn_bornWeight_le)

/-- **Bad-set Born-mass capstone (D5).**  The EVOLVED two-register state
    `uc_eval(gidneyInPlaceWithSwap) · cosetInputVec x 0` carries Born mass `≤ 2·numWin/2^cm`
    on the FULL agree-off bad set `inplaceBadSetB`.

    Proof = pure packaging: rewrite the evolved state as `permState σ.symm` (with
    `σ = inplaceSigma = gateToPerm gidneyInPlaceWithSwap`), then transport its mass on `B`
    to the input's mass on `inplaceBadIn` (`bornWeightOn_evolved_le_badInput`, fed by
    `inplace_hred`), which D4 (`inplaceBadIn_bornWeight_le`) bounds by `2·numWin/2^cm`. -/
theorem inplaceBadSetB_evolved_bornWeight_le
    (w bits numWin N cm k kInv x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfit : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (hxfit : x + (2 ^ cm - 1) * N < 2 ^ bits) :
    bornWeightOn
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin))
          * cosetInputVec w bits N cm x 0)
        (inplaceBadSetB w bits numWin N cm k x TfamK TfamKinv hw hbits)
      ≤ 2 * (numWin : ℝ) / 2 ^ cm := by
  rw [uc_eval_eq_permState (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin) (cosetDim w bits)
        (gidneyInPlaceWithSwap_wellTyped w bits TfamK TfamKinv numWin hw hbits)]
  refine le_trans (bornWeightOn_evolved_le_badInput
      (inplaceSigma w bits numWin TfamK TfamKinv hw hbits)
      (cosetInputVec w bits N cm x 0)
      (inplaceBadSetB w bits numWin N cm k x TfamK TfamKinv hw hbits)
      (inplaceBadIn w bits numWin N cm k x TfamK TfamKinv)
      (fun j hj hjne => inplace_hred w bits numWin N cm k x TfamK TfamKinv hw hbits j hj hjne))
    (inplaceBadIn_bornWeight_le w bits numWin N cm k kInv x TfamK TfamKinv hTfamK hTfamKinv
      hw hbits hN hxN hkkinv hfit hxfit)

end FormalRV.Shor.GidneyInPlace.InPlaceComposedMassBound
