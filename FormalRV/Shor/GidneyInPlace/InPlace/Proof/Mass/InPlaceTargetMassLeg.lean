/-
  FormalRV.Shor.GidneyInPlace.InPlaceTargetMassLeg
  ──────────────────────────────────────────────────
  The TARGET-mass leg of the Architecture-B deviation (consumer audit E0).

  E0 FINDING (by signature, not prose).  The deviation consumer is
  `CosetBornWeight.normSqDist_le_of_agree_off`:

      (hagree : ∀ i ∉ B, s₁ i 0 = s₂ i 0)
      (hw₁ : bornWeightOn s₁ B ≤ W)        -- the EVOLVED state (D5)
      (hw₂ : bornWeightOn s₂ B ≤ W)        -- the TARGET state  ← REQUIRED separately
      ⊢ normSqDist s₁ s₂ ≤ 2 * W

  So `inplaceBadSetB_evolved_bornWeight_le` (D5) is only `hw₁`.  The consumer ALSO needs
  `hw₂`, the TARGET state's mass on the SAME bad set `B`.  (The proven out-of-place template
  `ReducedLookupCosetShift.reducedLookupWindowedMul_embedAgreeOff_local` likewise returns BOTH
  masses, and `CosetAgreesOffWrap` bundles `coset_born_le` AND `ideal_born_le`.)  The earlier
  "target leg not separately needed" claim was WRONG for the deviation consumer; this file
  supplies the target leg.

  THE ARGUMENT (mass conservation — the `p₁ = p₂` identity).  The evolved state and the target
  agree off `B`, so their Born masses agree off `B`; if their TOTAL masses are equal then their
  on-`B` masses are equal too.  Hence the target's bad mass EQUALS the evolved's bad mass, which
  D5 already bounds by `2·numWin/2^cm` — SAME constant `W = 2·numWin/2^cm` (no `numWin` doubling;
  the scalar `normSqDist` bound stays `2·W = 4·numWin/2^cm`).

  This file proves the GENERIC, reusable mass-conservation lemmas unconditionally, and assembles
  the target leg modulo exactly TWO named, true, separately-dischargeable facts:
    • `hagreeB`  — the off-`inplaceBadSetB` agreement, EXPLICIT in `inplaceBadSetB` (the §6
      `gidneyInPlaceWithSwap_agree_off` proves precisely this, but wraps it in `∃ B`; exposing
      the explicit-`B` form is a mechanical refactor of that proof);
    • `hnorm`    — equal total Born mass of `cosetInputVec x 0` and `cosetInputVec ((k·x)%N) 0`
      (both unit-norm two-register coset inputs; the normalization is the one remaining build).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Mass.InPlaceComposedMassBound

namespace FormalRV.Shor.GidneyInPlace.InPlaceTargetMassLeg

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
open FormalRV.Shor.GidneyInPlace.InPlaceComposedMass (bornWeightOn_permState_symm)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree (inplaceBadSetB)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedMassBound (inplaceBadSetB_evolved_bornWeight_le)

/-! ## §1. Generic mass-conservation lemmas (reusable, unconditional). -/

/-- **Total Born mass is permutation-invariant.**  Reindexing a state by `σ.symm` leaves its
    total (`Finset.univ`) Born mass unchanged — the special case of `bornWeightOn_permState_symm`
    at `B = univ` (`univ.image σ.symm = univ`). -/
theorem bornWeightOn_permState_symm_univ {dim : Nat} (σ : Equiv.Perm (Fin dim)) (s : QState dim) :
    bornWeightOn (permState σ.symm s) Finset.univ = bornWeightOn s Finset.univ := by
  rw [bornWeightOn_permState_symm σ s Finset.univ]
  congr 1
  apply Finset.eq_univ_of_forall
  intro i
  rw [Finset.mem_image]
  exact ⟨σ i, Finset.mem_univ _, σ.symm_apply_apply i⟩

/-- **Mass conservation (`p₁ = p₂`).**  If two states agree (entrywise) off a bad set `B` and
    carry equal TOTAL Born mass, then their Born masses on `B` are EQUAL.  (Off `B` the masses
    agree pointwise; equal totals force the on-`B` remainders to agree.)  This is the identity
    that lets D5's evolved-state bad mass stand in for the target's bad mass. -/
theorem bornWeightOn_eq_of_agree_off_of_total_eq {dim : Nat} (s₁ s₂ : QState dim)
    (B : Finset (Fin dim))
    (hagree : ∀ i, i ∉ B → s₁ i 0 = s₂ i 0)
    (htot : bornWeightOn s₁ Finset.univ = bornWeightOn s₂ Finset.univ) :
    bornWeightOn s₁ B = bornWeightOn s₂ B := by
  have hcompl : bornWeightOn s₁ Bᶜ = bornWeightOn s₂ Bᶜ := by
    unfold bornWeightOn
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hagree i (Finset.mem_compl.mp hi)]
  have h1 : bornWeightOn s₁ B + bornWeightOn s₁ Bᶜ = bornWeightOn s₁ Finset.univ := by
    unfold bornWeightOn; exact Finset.sum_add_sum_compl B _
  have h2 : bornWeightOn s₂ B + bornWeightOn s₂ Bᶜ = bornWeightOn s₂ Finset.univ := by
    unfold bornWeightOn; exact Finset.sum_add_sum_compl B _
  linarith

/-! ## §2. The target-mass leg (assembled; modulo the two named true facts). -/

/-- **Target-mass leg.**  The TARGET state `cosetInputVec ((k·x)%N) 0` carries Born mass
    `≤ 2·numWin/2^cm` on the bad set `inplaceBadSetB` — the second hypothesis the deviation
    consumer `normSqDist_le_of_agree_off` requires (alongside D5's evolved-state mass).

    Proof = mass conservation: the evolved state `uc_eval(gidneyInPlaceWithSwap)·cosetInputVec x 0`
    agrees with the target off `inplaceBadSetB` (`hagreeB`) and (being a unitary image of
    `cosetInputVec x 0`) has the same total mass as the target (`hnorm`), so their bad masses are
    equal; D5 (`inplaceBadSetB_evolved_bornWeight_le`) bounds the evolved one.  The two
    hypotheses are TRUE and separately dischargeable (see the file header). -/
theorem inplaceBadSetB_target_bornWeight_le
    (w bits numWin N cm k kInv x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfit : (k * x) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (hxfit : x + (2 ^ cm - 1) * N < 2 ^ bits)
    (hagreeB : ∀ i : Fin (2 ^ cosetDim w bits),
        i ∉ inplaceBadSetB w bits numWin N cm k x TfamK TfamKinv hw hbits →
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin))
          * cosetInputVec w bits N cm x 0) i 0
          = cosetInputVec w bits N cm ((k * x) % N) 0 i 0)
    (hnorm : bornWeightOn (cosetInputVec w bits N cm x 0) Finset.univ
           = bornWeightOn (cosetInputVec w bits N cm ((k * x) % N) 0) Finset.univ) :
    bornWeightOn (cosetInputVec w bits N cm ((k * x) % N) 0)
        (inplaceBadSetB w bits numWin N cm k x TfamK TfamKinv hw hbits)
      ≤ 2 * (numWin : ℝ) / 2 ^ cm := by
  set ev := Framework.uc_eval (Gate.toUCom (cosetDim w bits)
      (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin)) * cosetInputVec w bits N cm x 0 with hev
  -- total mass of the evolved state = total mass of the input = total mass of the target
  have htot_ev : bornWeightOn ev Finset.univ
      = bornWeightOn (cosetInputVec w bits N cm ((k * x) % N) 0) Finset.univ := by
    rw [hev, uc_eval_eq_permState (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin)
        (cosetDim w bits) (gidneyInPlaceWithSwap_wellTyped w bits TfamK TfamKinv numWin hw hbits),
      bornWeightOn_permState_symm_univ]
    exact hnorm
  -- mass conservation ⇒ target bad mass = evolved bad mass
  have heq := bornWeightOn_eq_of_agree_off_of_total_eq ev
    (cosetInputVec w bits N cm ((k * x) % N) 0)
    (inplaceBadSetB w bits numWin N cm k x TfamK TfamKinv hw hbits) hagreeB htot_ev
  rw [← heq]
  -- D5 bounds the evolved bad mass
  exact inplaceBadSetB_evolved_bornWeight_le w bits numWin N cm k kInv x TfamK TfamKinv
    hTfamK hTfamKinv hw hbits hN hxN hkkinv hfit hxfit

end FormalRV.Shor.GidneyInPlace.InPlaceTargetMassLeg
