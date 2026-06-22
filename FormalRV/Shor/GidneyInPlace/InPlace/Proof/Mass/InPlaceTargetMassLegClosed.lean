/-
  FormalRV.Shor.GidneyInPlace.InPlaceTargetMassLegClosed — T3: the target-mass
  leg, UNCONDITIONAL.
  ════════════════════════════════════════════════════════════════════════════

  Discharges the two hypotheses (`hagreeB`, `hnorm`) of the conditional
  `InPlaceTargetMassLeg.inplaceBadSetB_target_bornWeight_le` and closes the target leg:

    bornWeightOn (cosetInputVec ((k·x)%N) 0) inplaceBadSetB  ≤  2·numWin / 2^cm

  with NO extra hypotheses.  Inputs:
    • `hagreeB` ← T2 `InPlaceAgreeOffExplicit.gidneyInPlaceWithSwap_agree_off_explicit`
      (off the EXACT `inplaceBadSetB`, no existential sibling);
    • `hnorm`   ← T1 `InPlaceCosetInputNorm.cosetInputVec_normalized`, applied at residues
      `x` and `(k·x)%N` (both unit-norm ⇒ equal totals).

  Constant: `W = 2·numWin/2^cm` (unchanged); fed to `normSqDist_le_of_agree_off` (alongside D5)
  this gives `normSqDist ≤ 2·W = 4·numWin/2^cm` — `numWin` stays physical.

  This is the SECOND of the two masses the deviation consumer requires; together with D5
  (`InPlaceComposedMassBound.inplaceBadSetB_evolved_bornWeight_le`) the Architecture-B
  deviation is now fully fed, on the two-register object.  (No Route B / `normSqDist`
  packaging here — that is the next phase.)

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Mass.InPlaceTargetMassLeg
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Input.InPlaceCosetInputNorm
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceAgreeOffExplicit

namespace FormalRV.Shor.GidneyInPlace.InPlaceTargetMassLegClosed

open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree (inplaceBadSetB)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputNorm (cosetInputVec_normalized)
open FormalRV.Shor.GidneyInPlace.InPlaceAgreeOffExplicit (gidneyInPlaceWithSwap_agree_off_explicit)
open FormalRV.Shor.GidneyInPlace.InPlaceTargetMassLeg (inplaceBadSetB_target_bornWeight_le)

/-- **T3 — UNCONDITIONAL target-mass leg.**  The TARGET state `cosetInputVec ((k·x)%N) 0` carries
    Born mass `≤ 2·numWin/2^cm` on the bad set `inplaceBadSetB`, with no auxiliary hypotheses.
    Closes `InPlaceTargetMassLeg.inplaceBadSetB_target_bornWeight_le` by supplying its `hagreeB`
    (T2, explicit-B agree-off) and `hnorm` (T1, normalization at both residues). -/
theorem inplaceBadSetB_target_bornWeight_le_closed
    (w bits numWin N cm k kInv x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfit : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (hxfit : x + (2 ^ cm - 1) * N < 2 ^ bits) :
    bornWeightOn (cosetInputVec w bits N cm ((k * x) % N) 0)
        (inplaceBadSetB w bits numWin N cm k x TfamK TfamKinv hw hbits)
      ≤ 2 * (numWin : ℝ) / 2 ^ cm := by
  have hn1 := cosetInputVec_normalized w bits numWin N cm x hw hbits hN hxfit
  have hn2 := cosetInputVec_normalized w bits numWin N cm ((k * x) % N) hw hbits hN hfit
  exact inplaceBadSetB_target_bornWeight_le w bits numWin N cm k kInv x TfamK TfamKinv
    hTfamK hTfamKinv hw hbits hN hxN hkkinv hfit hxfit
    (fun i hiB => gidneyInPlaceWithSwap_agree_off_explicit w bits numWin N cm k kInv x
      TfamK TfamKinv hTfamK hTfamKinv hw hbits hN hxN hkkinv hfit i hiB)
    (by rw [hn1, hn2])

end FormalRV.Shor.GidneyInPlace.InPlaceTargetMassLegClosed
