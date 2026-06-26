/-
  FormalRV.Shor.GidneyInPlace.E2RunwayShorUnconditional — the coset/runway success bound with the
  RHS made the EXPLICIT Shor success value `κ/(log₂N)⁴`.
  ════════════════════════════════════════════════════════════════════════════

  The hybrid capstone `gidney_inplace_coset_shor_succeeds_hybrid` (G1+G3) bounds the CONCRETE physical
  runway/coset machine below the IDEAL residue Shor machine:

    `probability_of_success_E2coset … (physRunwayOracle …)
       ≥ probability_of_success a r N m bits (cosetAnc w bits) f_residueIdeal − 2·m·√(8·numWin/2^cm)`.

  Here we DISCHARGE the opaque ideal-side term into the canonical Shor success value: when the ideal
  residue oracle `f_residueIdeal` is a genuine `ModMulImpl` (the per-iterate "multiply by `a^(2^i) mod N`"
  basis-action spec) over the standard `BasicSetting`, the proven, axiom-clean
  `SQIRPort.Shor_correct_var` gives `probability_of_success … f_residueIdeal ≥ κ/(log₂N)⁴`.  Chaining
  the two yields the coset machine's bound against the EXPLICIT Shor floor:

    `probability_of_success_E2coset … (physRunwayOracle …) ≥ κ/(log₂N)⁴ − 2·m·√(8·numWin/2^cm)`.

  WHAT THIS DOES AND DOES NOT CLOSE.  This makes the RIGHT-HAND SIDE the actual Shor success bound
  (no longer a reference to an opaque `probability_of_success` of an abstract oracle); the deviation
  term is unchanged.  The remaining inputs are exactly the (genuine) properties of the IDEAL residue
  reference oracle at the coset dimension `bits + cosetAnc w bits`: `ModMulImpl` + the layout/support
  realizations (`hf_residue`, `hsupp_res`) + the runway realization (`hf_runway`) + the unit-norm
  bookkeeping.  Constructing a CONCRETE `BaseUCom` family realizing that ideal residue oracle at the
  tight `cosetAnc = 2+2w+2bits` ancilla budget — one qubit below the windowed multiplier, GE2021's
  saving, so no existing verified family reuses — is the single remaining frontier (a dedicated
  modular-arithmetic circuit construction), kept honestly as a hypothesis here.

  Kernel-clean: axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorCapstone

namespace FormalRV.Shor.GidneyInPlace.E2RunwayShorCapstone

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.Shor.Approx (pmNorm)
open FormalRV.SQIRPort.ApproxTransfer (jointIdx)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq)
open FormalRV.Shor.GidneyInPlace.ControlOracleLift (workMat)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess
  (Shor_final_state_E2coset probability_of_success_E2coset)
open FormalRV.Shor.GidneyInPlace.E2PhysicalRealization (physRunwayOracle)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetWork_dim_eq)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate (gidneyInPlaceWithSwap gidneyInPlaceWithSwap_wellTyped)

/-- **The concrete physical runway oracle is well-typed** at the oracle-native dim
    `bits + cosetAnc w bits`.  Discharges the capstone's `hwtP` for the concrete machine:
    `physRunwayOracle = Gate.toUCom (gidneyInPlaceWithSwap …)`, and the gidney gate is well-typed
    at `cosetDim w bits = bits + cosetAnc w bits` (`gidneyInPlaceWithSwap_wellTyped`,
    `cosetWork_dim_eq`), lifted through `Gate.toUCom` by `uc_well_typed_toUCom_of_Gate_WellTyped`. -/
theorem physRunwayOracle_wellTyped (m w bits numWin : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat) (hw : 0 < w) (hbits : numWin * w = bits) (j : Nat) :
    FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits)
      (physRunwayOracle m w bits numWin TfamK TfamKinv j) :=
  FormalRV.BQAlgo.uc_well_typed_toUCom_of_Gate_WellTyped (bits + cosetAnc w bits)
    (gidneyInPlaceWithSwap w bits (TfamK (revIndex m j)) (TfamKinv (revIndex m j)) numWin)
    ((cosetWork_dim_eq w bits) ▸
      gidneyInPlaceWithSwap_wellTyped w bits (TfamK (revIndex m j)) (TfamKinv (revIndex m j))
        numWin hw hbits)

/-- **THE COSET/RUNWAY SHOR BOUND AGAINST THE EXPLICIT SHOR FLOOR `κ/(log₂N)⁴`.**

    Identical to `gidney_inplace_coset_shor_succeeds_hybrid`, but the ideal-side term is discharged to
    the canonical Shor success value via `Shor_correct_var`: given that the ideal residue reference
    oracle `f_residueIdeal` (at the coset dimension `bits + cosetAnc w bits`) is a genuine `ModMulImpl`
    over the standard `BasicSetting`, the concrete physical runway/coset machine `physRunwayOracle`
    succeeds at order-finding with probability

      `≥ κ/(log₂N)⁴ − 2·m·√(8·numWin/2^cm)`.

    The actual object is the composed SYNTACTIC gate `physRunwayOracle = Gate.toUCom (gidneyInPlaceWithSwap …)`.
    The remaining hypotheses are the genuine realizations of the ideal residue reference oracle; the one
    open frontier is constructing such an oracle concretely at the tight `cosetAnc` budget. -/
theorem gidney_inplace_coset_shor_succeeds_unconditional
    (a r N m w bits numWin cm : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat) (mult kInv : Nat → Nat)
    (f_runwayIdeal f_residueIdeal :
      Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hm : 0 < m) (hbitsPos : 0 < bits)
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
    (hnormI : pmNorm (Shor_final_state_E2coset m w bits N cm f_runwayIdeal) ≤ 1)
    -- the ideal residue reference oracle is a genuine Shor modexp oracle:
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m bits)
    (h_mmi : FormalRV.SQIRPort.ModMulImpl a N bits (cosetAnc w bits) f_residueIdeal) :
    probability_of_success_E2coset a r N m w bits cm
        (physRunwayOracle m w bits numWin TfamK TfamKinv)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
          - 2 * (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) := by
  have hcap := gidney_inplace_coset_shor_succeeds_hybrid a r N m w bits numWin cm
    TfamK TfamKinv mult kInv f_runwayIdeal f_residueIdeal hm hbitsPos
    (fun j => physRunwayOracle_wellTyped m w bits numWin TfamK TfamKinv hw hbits j)
    hwtI hwtRes
    hTfamK hTfamKinv hw hbits hN hN1 hMN hkkinv hf_runway hf_residue hsupp_res hnormP hnormI
  have hideal : probability_of_success a r N m bits (cosetAnc w bits) f_residueIdeal
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4 :=
    FormalRV.SQIRPort.Shor_correct_var a r N m bits (cosetAnc w bits) f_residueIdeal
      h_basic h_mmi (fun i _ => hwtRes i)
  linarith

end FormalRV.Shor.GidneyInPlace.E2RunwayShorCapstone
