/-
  FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayReduction — the IDEAL RUNWAY ORACLE
  reduced to one concrete-gate obligation, with the clean-ancilla route proven insufficient.
  ════════════════════════════════════════════════════════════════════════════

  CONSOLIDATED STATUS of the Route-B′ ideal-runway-oracle effort (all kernel-clean,
  axioms ⊆ {propext, Classical.choice, Quot.sound}):
   • The CONDITIONAL coset/runway Shor bound (all parameters) is `E2RunwayShorCanonical.
     gidney_inplace_coset_shor_succeeds_unconditional_canonical` — it holds for any well-typed
     `f_runwayIdeal` satisfying `hf_runway`; everything around it (residue oracle, norms,
     deviation) is discharged.
   • The UNCONDITIONAL bound is now REDUCED, kernel-clean, to a SINGLE obligation: a concrete
     well-typed gate `g` at `cosetDim` with `gateToPerm g = idealPerm` (see §1 + §2 below) — then
     `hf_runway`/`hwtI` follow mechanically and the canonical capstone closes.
   • HONEST CORRECTION (was: "clean-ancilla proven insufficient / dirty-ancilla gate is open"):
     that framing is MISLEADING and the marker theorems are removed (see §0).  It described a limit of
     THIS file's two-coset-register `cosetInputVec` interface (which forces an unused-but-preserved
     b-block), NOT a limit of Gidney's algorithm.  Gidney's windowed coset multiplier is implementable
     (working Q# code + counts); the deviation term is the INTRINSIC coset approximation, not a missing
     gate.  The faithful, modular coset/runway multiplier lives in `FormalRV/Shor/RunwayWindowed/`.

  GOAL (M3 + M4).  Build a concrete `placedGate c cinv : Gate` at `cosetDim w bits`
  whose `uc_eval` realizes the coset-shift column identity
      uc_eval (toUCom (cosetDim) (placedGate c cinv)) · cosetInputVec z 0
        = cosetInputVec ((c·z)%N) 0                                   (z < N)
  reusing the verified compressed guarded-shift gate `cgsGate` (E2RunwayGuardedShift), then
  package it into the `hf_runway` ∑-form (clone `hf_physical_concrete`).

  STATUS (this file).  Three kernel-clean results:
   • §0  HONEST NOTE — the misleading `placement_impossible` markers were REMOVED (they described a
         limitation of this file's two-coset-register interface, not of Gidney's implementable gate).
   • §1  `column_identity_of_gateToPerm_eq_idealPerm` — M3 REDUCED to a single concrete-realization
         obligation: the coset-shift COLUMN IDENTITY holds for any WellTyped `g` at `cosetDim` with
         `gateToPerm g = idealPerm` (the already-verified abstract guarded-shift permutation).  So
         the entire remaining M3 content is "build such a `g`" (necessarily a DIRTY-ancilla circuit
         that reuses the b-block, which `cgsGate` is not).
   • §2  `hf_runway_of_column_identity` + `runwayIdealFam_wellTyped` — M4 DONE: a complete, reusable
         packaging that turns ANY per-stage column identity into the capstone's exact `hf_runway`
         ∑-form + `hwtI`, independent of how the column identity is obtained.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayGuardedShift
import FormalRV.Shor.GidneyInPlace.Ideal.Def.IdealPermLift
import FormalRV.Shor.GidneyInPlace.InPlace.Def.InPlaceSwapBlocks
import FormalRV.Shor.GidneyInPlace.Capstone.Proof.E2PhysicalRealization
import FormalRV.Arithmetic.GateShift

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayReduction

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Arithmetic (shiftGate applyNat_shiftGate applyNat_shiftGate_at shiftGate_frame)
open FormalRV.BQAlgo.WindowedModNShor (swapCascade swapCascade_apply swapCascade_wellTyped)
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayGuardedShift
  (cgsGate cgsGate_decode cgsGate_wellTyped cgsDim cgsDim_le_cosetDim)
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider
  (encDiv encDiv_data encDiv_cin encDiv_read encDiv_flag encDiv_qbit)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg (aBase bBase)

open FormalRV.SQIRPort
open FormalRV.Shor.GidneyInPlace.GatePerm (gateToPerm extendBool funboolNat applyFin funboolEquiv)
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_eq_permState)
open FormalRV.Shor.GidneyInPlace.ApproxOp (permState)
open FormalRV.Shor.GidneyInPlace.RunwayShiftPerm (guardedShift resShiftPerm)
open FormalRV.Shor.GidneyInPlace.IdealPermLift (idealPerm idealShift_cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc cosetWork_dim_eq)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq)
open FormalRV.Shor.GidneyInPlace.E2PhysicalRealization (uc_eval_toUCom_dimcast)

/-! ## §0. HONEST NOTE — the misleading "placement impossibility" was REMOVED.

  Earlier revisions carried `placement_impossible`/`placement_impossible_capstone` claiming a
  clean-ancilla arithmetic gate (`cgsGate`) "cannot be placed in `cosetDim`".  Those marker theorems
  are DELETED: their framing was MISLEADING.  They were a fact about THIS file's particular INTERFACE
  — a two-coset-register `cosetInputVec` whose b-block `Coset_m(0)=Σ_j|jN⟩` is required to survive,
  leaving too few clean-scratch wires — NOT a fact about Gidney's algorithm.  Gidney's windowed coset
  multiplier IS implementable: he ships working Q# (`Library/1905.07682/.../MulAdd_Window.qs`) with
  concrete gate/qubit counts, and FormalRV itself realises a faithful, counted, bound-riding windowed
  multiply in `ModExpAtSameObjectWeld.ge2021_oracle_correct_AND_counted_AND_bound`
  (on `measWindowedModNEncodeGate`).  The deviation term `2·m·√(8·numWin/2^cm)` is the INTRINSIC
  coset-approximation error (Zalka 2006 / Gidney 1905.08488 `2^{-m}`), NOT a penalty for a missing
  gate.  The faithful coset/runway multiplier is built modularly on the verified oblivious-carry adder
  in `FormalRV/Shor/RunwayWindowed/` (`runwayWindowedMul` + `runwayWindowedMul_residue`). -/

/-! ## §1. The column identity reduces to "realize `idealPerm` as a concrete `cosetDim` Gate".

  Because the IDEAL coset-shift column identity is ALREADY proven for the abstract permutation
  `idealPerm` (`IdealPermLift.idealShift_cosetInputVec`: `permState idealPerm.symm · cosetInputVec
  z 0 = cosetInputVec ((mult·z)%N) 0`), and the literal SQIR gate action is
  `uc_eval (toUCom g) = permState (gateToPerm g).symm` (`UCEvalBridge.uc_eval_eq_permState`), the
  M3 COLUMN IDENTITY for a concrete gate `g` follows IMMEDIATELY once `gateToPerm g = idealPerm`.

  This isolates the *entire* remaining content as one concrete-realization obligation. -/

/-- **M3 COLUMN IDENTITY (reduction form).**  For ANY `WellTyped` gate `g` at `cosetDim w bits`
    whose basis permutation IS the ideal guarded-shift permutation `idealPerm`, the coset-shift
    column identity holds EXACTLY:
        uc_eval (toUCom (cosetDim) g) · cosetInputVec z 0 = cosetInputVec ((mult·z)%N) 0
    (for `z < N`, full-blocks budget `2^cm·N ≤ 2^bits`, coprimality data).  Kernel-clean;
    the only remaining obligation is to BUILD such a `g`. -/
theorem column_identity_of_gateToPerm_eq_idealPerm
    (w bits N cm mult kInv z : Nat) (hN : 1 < N)
    (hfwd : (mult * kInv) % N = 1) (hbwd : (kInv * mult) % N = 1)
    (hfull : 2 ^ cm * N ≤ 2 ^ bits) (hz : z < N)
    (g : Gate) (hwt : Gate.WellTyped (cosetDim w bits) g)
    (hperm : gateToPerm g (cosetDim w bits) hwt
              = idealPerm w bits N cm mult kInv hN hfwd hbwd) :
    Framework.uc_eval (Gate.toUCom (cosetDim w bits) g) * cosetInputVec w bits N cm z 0
      = cosetInputVec w bits N cm ((mult * z) % N) 0 := by
  rw [uc_eval_eq_permState g (cosetDim w bits) hwt, hperm]
  exact idealShift_cosetInputVec w bits N cm mult kInv z hN hfwd hbwd hfull hz

/-! ## §2. M4 — packaging a column identity into the capstone's `hf_runway` ∑-form.

  This is the MECHANICAL half (cloned from `E2PhysicalRealization.hf_physical_concrete`): it takes
  ANY concrete gate `g` together with its coset-shift COLUMN IDENTITY (at `cosetDim`) and produces
  the exact `hf_runway` slot the capstone `gidney_inplace_coset_shor_succeeds_canonical` consumes,
  for `f_runwayIdeal := fun _ => Gate.toUCom (bits + cosetAnc w bits) g`.  It is INDEPENDENT of how
  the column identity is obtained, so it is a complete, reusable M4 even while the concrete M3 gate
  is structurally blocked (see §0). -/

/-- The `f_runwayIdeal` family realized by a STAGE-INDEXED concrete gate family `gFam`
    (oracle-native dim `bits + cosetAnc w bits`), with the table evaluated at `revIndex m j`
    exactly like `physRunwayOracle`, so the QPE call `f (revIndex m k)` lands on stage `k`'s gate. -/
noncomputable def runwayIdealFam (m w bits : Nat) (gFam : Nat → Gate) :
    Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits) :=
  fun j => Gate.toUCom (bits + cosetAnc w bits) (gFam (revIndex m j))

/-- **Stage-index alignment** (clone of `physRunwayOracle_align`): `runwayIdealFam (revIndex m k)`
    is the stage-`k` gate `gFam k`, by the `revIndex` involution. -/
theorem runwayIdealFam_align (m w bits : Nat) (gFam : Nat → Gate) (k : Nat) (hk : k < m) :
    runwayIdealFam m w bits gFam (revIndex m k)
      = Gate.toUCom (bits + cosetAnc w bits) (gFam k) := by
  unfold runwayIdealFam
  have hinv : revIndex m (revIndex m k) = k := by unfold revIndex; omega
  rw [hinv]

/-- Cast composition (reproved locally; the E2 version is `private`): the work index reindexed by
    `workDim_eq` then by the `cosetWork_dim_eq` power-cast equals the `E2shor_dim_eq` reindex. -/
private theorem cast_wd_cw (m w bits : Nat)
    (a : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    Fin.cast (congrArg (fun x => 2 ^ x) (cosetWork_dim_eq w bits))
        (Fin.cast (workDim_eq m bits (cosetAnc w bits)) a)
      = Fin.cast (E2shor_dim_eq m w bits) a := by
  apply Fin.ext; rfl

/-- **M4 — `hf_runway` from a per-stage column identity.**  Given, for every stage `k < m`, the
    coset-shift COLUMN IDENTITY for stage `k`'s concrete gate `gFam k` (at `cosetDim`, every `z < N`,
    multiplier `mult k`), the family `runwayIdealFam m w bits gFam` satisfies the capstone's
    `hf_runway` hypothesis EXACTLY.  Proof clones `hf_physical_concrete`: stage-index alignment
    (`runwayIdealFam_align`), the per-entry dimension-cast bridge (`uc_eval_toUCom_dimcast` at
    `cosetWork_dim_eq`), reindex the work sum to `Fin (2^cosetDim)`, then the supplied column
    identity recognised via `Matrix.mul_apply`. -/
theorem hf_runway_of_column_identity
    (m w bits N cm : Nat) (gFam : Nat → Gate) (mult : Nat → Nat)
    (hcol : ∀ (k : Nat), k < m → ∀ (z : Nat), z < N →
        Framework.uc_eval (Gate.toUCom (cosetDim w bits) (gFam k)) * cosetInputVec w bits N cm z 0
          = cosetInputVec w bits N cm ((mult k * z) % N) 0) :
    ∀ (k : Nat), k < m → ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            Framework.uc_eval (runwayIdealFam m w bits gFam (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = cosetInputVec w bits N cm ((mult k * z) % N) 0
              (Fin.cast (E2shor_dim_eq m w bits) y) 0 := by
  intro k hk z hz y
  -- align the family to stage `k`'s gate.
  rw [runwayIdealFam_align m w bits gFam k hk]
  -- rewrite the target column via the supplied (stage-`k`) column identity (at cosetDim).
  rw [← hcol k hk z hz]
  show (∑ yp,
      Framework.uc_eval (Gate.toUCom (bits + cosetAnc w bits) (gFam k))
          (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
          (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
        * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
    = (Framework.uc_eval (Gate.toUCom (cosetDim w bits) (gFam k))
        * cosetInputVec w bits N cm z 0) (Fin.cast (E2shor_dim_eq m w bits) y) 0
  -- push the dimension cast through every entry.
  rw [Finset.sum_congr rfl (fun yp _ => by
    rw [uc_eval_toUCom_dimcast (cosetWork_dim_eq w bits) (gFam k)
          (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
          (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp),
        cast_wd_cw m w bits y, cast_wd_cw m w bits yp])]
  -- the work sum is now entirely in the coset dim; reindex to `Fin (2^cosetDim)`.
  rw [Matrix.mul_apply]
  exact (Fintype.sum_equiv (finCongr (E2shor_dim_eq m w bits))
    (fun yp => Framework.uc_eval (Gate.toUCom (cosetDim w bits) (gFam k))
        (Fin.cast (E2shor_dim_eq m w bits) y) (Fin.cast (E2shor_dim_eq m w bits) yp)
      * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
    (fun i => Framework.uc_eval (Gate.toUCom (cosetDim w bits) (gFam k))
        (Fin.cast (E2shor_dim_eq m w bits) y) i
      * cosetInputVec w bits N cm z 0 i 0)
    (fun yp => rfl))

/-- The `hwtI` slot: `runwayIdealFam m w bits gFam` is `UCom.WellTyped` at every stage, from each
    stage gate's `Gate.WellTyped` at `cosetDim = bits + cosetAnc`. -/
theorem runwayIdealFam_wellTyped (m w bits : Nat) (gFam : Nat → Gate)
    (hwt : ∀ j, Gate.WellTyped (cosetDim w bits) (gFam j)) :
    ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits)
          (runwayIdealFam m w bits gFam j) := by
  intro j
  have hwt' : Gate.WellTyped (bits + cosetAnc w bits) (gFam (revIndex m j)) := by
    rw [cosetWork_dim_eq w bits]; exact hwt (revIndex m j)
  exact FormalRV.BQAlgo.uc_well_typed_toUCom_of_Gate_WellTyped (bits + cosetAnc w bits)
    (gFam (revIndex m j)) hwt'

end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayReduction
