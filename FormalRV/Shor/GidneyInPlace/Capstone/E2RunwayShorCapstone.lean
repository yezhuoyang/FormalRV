/-
  FormalRV.Shor.GidneyInPlace.E2RunwayShorCapstone — final glue G1+G3:
  the exported coset-Shor success theorem for the CONCRETE physical runway machine.
  ════════════════════════════════════════════════════════════════════════════

  The capstone instantiates the hisom-free H5 (`coset_route2_success_hybrid_norm_E2_no_hisom`,
  G0) with the CONCRETE physical oracle `physRunwayOracle` (G2b) and the now-PROVEN realization
  `hf_physical_runway` (G2b).  So both load-bearing layout obligations — `hisom` (eliminated in G0)
  and `hf_physical` (proven in G2b) — are discharged inside the statement.

  THE ACTUAL SIDE IS THE E2 RUNWAY/COSET MACHINE, not plain-init Shor:
    `probability_of_success_E2coset … (physRunwayOracle …)`
      ≥ `probability_of_success … f_residueIdeal` − `2·m·√(8·numWin/2^cm)`.
  The ideal side `probability_of_success … f_residueIdeal` IS the ordinary plain Shor machine (the
  honest reference); the `√`-error term is unchanged.

  What REMAINS as explicit external assumptions (all genuine, none load-bearing for the layout):
    • parameter sizing/coprimality: `hm`, `hbitsPos`, `hw`, `hbits`, `hN`, `hN1`, `hMN`, `hkkinv`;
    • concrete table existence: `hTfamK`, `hTfamKinv`;
    • the IDEAL/residue plain-Shor oracle's defining realizations & well-typedness: `f_runwayIdeal`,
      `f_residueIdeal`, `hf_runway`, `hf_residue`, `hsupp_res`, `hwtI`, `hwtRes`;
    • unit-norm of the two final states: `hwtP`, `hnormP`, `hnormI` (dischargeable from
      `E2runwayInit_normalized` + the hU stage isometry; carried here, reduced in a refinement).

  No `E_phys`/`cosetEmbedded` object, no EmbedAgreeOff route, no bad-set accumulation, no
  `normSqDist` route.  Kernel-clean: axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.Proof.E2HisomDischarged
import FormalRV.Shor.GidneyInPlace.Capstone.Proof.E2PhysicalRealization

namespace FormalRV.Shor.GidneyInPlace.E2RunwayShorCapstone

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Shor.Approx (pmNorm)
open FormalRV.SQIRPort.ApproxTransfer (jointIdx)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate (gidneyInPlaceWithSwap)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq)
open FormalRV.Shor.GidneyInPlace.ControlOracleLift (workMat)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess
  (Shor_final_state_E2coset probability_of_success_E2coset)
open FormalRV.Shor.GidneyInPlace.E2HisomDischarged (coset_route2_success_hybrid_norm_E2_no_hisom)
open FormalRV.Shor.GidneyInPlace.E2PhysicalRealization (physRunwayOracle hf_physical_runway)

/-- **HEADLINE — the in-place coset Gidney runway Shor success bound (E2 machine).**

    The CONCRETE physical runway/coset machine `physRunwayOracle` (the gidney in-place multiplier
    lifted to the QPE oracle register) succeeds at order-finding at least as well as the ORDINARY
    plain Shor machine `f_residueIdeal`, up to the square-root deviation `2·m·√(8·numWin/2^cm)`:

      `probability_of_success_E2coset … (physRunwayOracle …)
         ≥ probability_of_success … f_residueIdeal − 2·m·√(8·numWin/2^cm)`.

    Both layout-critical obligations are DISCHARGED in the statement: `hisom` (every physical stage
    is a `pmDist` isometry — G0 via hU) and `hf_physical` (the physical oracle realizes the gidney
    gate — G2b, `hf_physical_runway`).  The actual side is the E2 runway/coset object, NOT plain
    Shor.  Remaining hypotheses are the genuine external assumptions documented in the file header. -/
theorem gidney_inplace_coset_shor_succeeds_hybrid
    (a r N m w bits numWin cm : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat) (mult kInv : Nat → Nat)
    (f_runwayIdeal f_residueIdeal :
      Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hm : 0 < m) (hbitsPos : 0 < bits)
    (hwtP : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits)
        (physRunwayOracle m w bits numWin TfamK TfamKinv j))
    (hwtI : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hwtRes : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_residueIdeal j))
    (hTfamK : ∀ k j addr, TfamK k j addr = tableValue (mult k) N w j addr)
    (hTfamKinv : ∀ k j addr, TfamKinv k j addr = tableValue (kInv k) N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hN1 : 1 < N)
    (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (hkkinv : ∀ k, (kInv k * mult k) % N = 1 % N)
    (hf_runway : ∀ (k : Nat) (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = cosetInputVec w bits N cm ((mult k * z) % N) 0
              (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_residue : ∀ (kstep : Nat), kstep < m →
        ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b
          = if a.val = (if b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N
                then ((mult kstep * (b.val / 2 ^ (cosetAnc w bits))) % N) * 2 ^ (cosetAnc w bits)
                else b.val)
              then 1 else 0)
    (hsupp_res : ∀ (x : Fin (2 ^ m))
        (b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        ¬ (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        Shor_final_state m bits (cosetAnc w bits) f_residueIdeal
            (jointIdx (shorDvd m bits (cosetAnc w bits)) x b) 0 = 0)
    (hnormP : pmNorm (Shor_final_state_E2coset m w bits N cm
        (physRunwayOracle m w bits numWin TfamK TfamKinv)) ≤ 1)
    (hnormI : pmNorm (Shor_final_state_E2coset m w bits N cm f_runwayIdeal) ≤ 1) :
    probability_of_success_E2coset a r N m w bits cm
        (physRunwayOracle m w bits numWin TfamK TfamKinv)
      ≥ probability_of_success a r N m bits (cosetAnc w bits) f_residueIdeal
          - 2 * (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) :=
  coset_route2_success_hybrid_norm_E2_no_hisom a r N m w bits numWin cm TfamK TfamKinv mult kInv
    (physRunwayOracle m w bits numWin TfamK TfamKinv) f_runwayIdeal f_residueIdeal
    hm hbitsPos hwtP hwtI hwtRes hTfamK hTfamKinv hw hbits hN hN1 hMN hkkinv
    (hf_physical_runway m w bits numWin N cm TfamK TfamKinv)
    hf_runway hf_residue hsupp_res hnormP hnormI

end FormalRV.Shor.GidneyInPlace.E2RunwayShorCapstone
