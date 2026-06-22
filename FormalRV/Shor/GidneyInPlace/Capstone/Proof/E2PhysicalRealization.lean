/-
  FormalRV.Shor.GidneyInPlace.E2PhysicalRealization — G2b: discharge `hf_physical`.
  ════════════════════════════════════════════════════════════════════════════

  `hf_physical` (carried by the coset-Shor H4/H5 bounds) asserts the ABSTRACT physical oracle
  `f_runwayPhysical (revIndex m k)` realizes the CONCRETE in-place multiplier
  `gidneyInPlaceWithSwap … (TfamK k) (TfamKinv k) …` on coset columns.  The audit (G2a) found
  this is the SAME physical object in two cast conventions — the oracle-native dim
  `bits + cosetAnc w bits` vs the gate-native dim `cosetDim w bits`, equal by `cosetWork_dim_eq`.

  We discharge it by:
    • `uc_eval_toUCom_dimcast` — the generic `uc_eval`/`Gate.toUCom` DIMENSION-CAST bridge: for any
      `h : A = B`, the gate's matrix at dim `A` equals its matrix at dim `B` reindexed by the cast
      (proved by `subst h`, after which the `Fin.cast` is the identity — NO `gateToPerm`/funbool);
    • `physRunwayOracle` — the CONCRETE physical oracle family `j ↦ Gate.toUCom (bits+cosetAnc w
      bits) (gidneyInPlaceWithSwap … (TfamK (revIndex m j)) …)`, with the stage-index alignment
      `physRunwayOracle (revIndex m k) = gate(TfamK k)` pinned via the `revIndex` involution;
    • `hf_physical_concrete` — `hf_physical` for `f_runwayPhysical := physRunwayOracle` (cast bridge
      + `Matrix.mul_apply` + the work-register reindex).

  No bad sets, no EmbedAgreeOff, no normSqDist, no pmDist.  Kernel-clean: axioms ⊆ {propext,
  Classical.choice, Quot.sound}.
-/
import FormalRV.Shor.GidneyInPlace.Deviation.Proof.E2OrbitDeviation

namespace FormalRV.Shor.GidneyInPlace.E2PhysicalRealization

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc cosetWork_dim_eq)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate (gidneyInPlaceWithSwap)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq)

/-! ## §1. The generic `uc_eval` / `Gate.toUCom` dimension-cast bridge. -/

/-- **`uc_eval` of `Gate.toUCom` is dimension-cast covariant.**  For `h : A = B`, the gate `g`'s
    matrix at dim `A` equals its matrix at dim `B`, reindexed by the `Fin (2^A) ≃ Fin (2^B)` cast.
    `Gate.toUCom` is dim-parametric (the gate indices don't depend on the ambient dim), so once
    `A = B` is substituted the cast is the identity — no per-gate induction or `gateToPerm`. -/
theorem uc_eval_toUCom_dimcast {A B : Nat} (h : A = B) (g : FormalRV.Framework.Gate)
    (i j : Fin (2 ^ A)) :
    FormalRV.Framework.uc_eval (FormalRV.BQAlgo.Gate.toUCom A g) i j
      = FormalRV.Framework.uc_eval (FormalRV.BQAlgo.Gate.toUCom B g)
          (Fin.cast (congrArg (fun x => 2 ^ x) h) i) (Fin.cast (congrArg (fun x => 2 ^ x) h) j) := by
  subst h
  rfl

/-! ## §2. The concrete physical oracle family + stage-index alignment. -/

/-- **The concrete physical runway oracle.**  Stage-`j` oracle = the gidney in-place multiplier
    realized as a `Gate.toUCom` at the oracle-native dim `bits + cosetAnc w bits`, with the table
    families evaluated at `revIndex m j` so that the QPE call `f (revIndex m k)` (stage `k`) lands
    on the stage-`k` tables `TfamK k`/`TfamKinv k`. -/
noncomputable def physRunwayOracle (m w bits numWin : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat) (j : Nat) :
    FormalRV.Framework.BaseUCom (bits + cosetAnc w bits) :=
  Gate.toUCom (bits + cosetAnc w bits)
    (gidneyInPlaceWithSwap w bits (TfamK (revIndex m j)) (TfamKinv (revIndex m j)) numWin)

/-- **Stage-index alignment.**  `physRunwayOracle (revIndex m k)` is the gate with the stage-`k`
    tables `TfamK k`/`TfamKinv k` (NOT `TfamK (revIndex m k)`), because `revIndex m` is an
    involution on `[0, m)`. -/
theorem physRunwayOracle_align (m w bits numWin : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat) (k : Nat) (hk : k < m) :
    physRunwayOracle m w bits numWin TfamK TfamKinv (revIndex m k)
      = Gate.toUCom (bits + cosetAnc w bits)
          (gidneyInPlaceWithSwap w bits (TfamK k) (TfamKinv k) numWin) := by
  unfold physRunwayOracle
  have hinv : revIndex m (revIndex m k) = k := by unfold revIndex; omega
  rw [hinv]

/-! ## §3. `hf_physical` for the concrete physical oracle. -/

/-- Cast composition: the work index reindexed by `workDim_eq` then by the `cosetWork_dim_eq`
    power-cast is exactly the `E2shor_dim_eq` reindex (all preserve `.val`). -/
private theorem cast_workDim_cosetWork (m w bits : Nat)
    (a : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    Fin.cast (congrArg (fun x => 2 ^ x) (cosetWork_dim_eq w bits))
        (Fin.cast (workDim_eq m bits (cosetAnc w bits)) a)
      = Fin.cast (E2shor_dim_eq m w bits) a := by
  apply Fin.ext; rfl

/-- **G2b — `hf_physical` for the concrete physical oracle.**  The abstract `f_runwayPhysical`
    instantiated by `physRunwayOracle` satisfies the `hf_physical` hypothesis of the coset-Shor
    H4/H5 bounds EXACTLY: the oracle's work-register action on the coset column `cosetInputVec z 0`
    equals the gidney gate's action, after the `cosetWork_dim_eq` dimension cast between the
    oracle-native (`bits + cosetAnc`) and gate-native (`cosetDim`) conventions.

    Proof: stage-index alignment (`physRunwayOracle_align`), the per-entry dimension-cast bridge
    (`uc_eval_toUCom_dimcast` at `cosetWork_dim_eq` + `cast_workDim_cosetWork`), then reindex the
    work sum to `Fin (2^cosetDim)` (`finCongr (E2shor_dim_eq)`) and recognise `Matrix.mul_apply`. -/
theorem hf_physical_concrete (m w bits numWin N cm : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat)
    (k : Nat) (hk : k < m) (z : Nat) (_hz : z < N)
    (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        FormalRV.Framework.uc_eval (physRunwayOracle m w bits numWin TfamK TfamKinv (revIndex m k))
            (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
            (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
          * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
      = (FormalRV.Framework.uc_eval (FormalRV.BQAlgo.Gate.toUCom (cosetDim w bits)
            (gidneyInPlaceWithSwap w bits (TfamK k) (TfamKinv k) numWin))
          * cosetInputVec w bits N cm z 0) (Fin.cast (E2shor_dim_eq m w bits) y) 0 := by
  -- align the oracle to the stage-`k` gate, then push the dimension cast through every entry.
  rw [physRunwayOracle_align m w bits numWin TfamK TfamKinv k hk]
  rw [Finset.sum_congr rfl (fun yp _ => by
    rw [uc_eval_toUCom_dimcast (cosetWork_dim_eq w bits)
          (gidneyInPlaceWithSwap w bits (TfamK k) (TfamKinv k) numWin)
          (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
          (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp),
        cast_workDim_cosetWork m w bits y, cast_workDim_cosetWork m w bits yp])]
  -- the work sum, now entirely in the coset dim, reindexes to `Fin (2^cosetDim)`.
  rw [Matrix.mul_apply]
  exact (Fintype.sum_equiv (finCongr (E2shor_dim_eq m w bits))
    (fun yp => FormalRV.Framework.uc_eval (FormalRV.BQAlgo.Gate.toUCom (cosetDim w bits)
          (gidneyInPlaceWithSwap w bits (TfamK k) (TfamKinv k) numWin))
        (Fin.cast (E2shor_dim_eq m w bits) y) (Fin.cast (E2shor_dim_eq m w bits) yp)
      * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
    (fun i => FormalRV.Framework.uc_eval (FormalRV.BQAlgo.Gate.toUCom (cosetDim w bits)
          (gidneyInPlaceWithSwap w bits (TfamK k) (TfamKinv k) numWin))
        (Fin.cast (E2shor_dim_eq m w bits) y) i
      * cosetInputVec w bits N cm z 0 i 0)
    (fun yp => rfl))

/-- **The `hf_physical` hypothesis, fully discharged.**  The `∀`-form matching EXACTLY the
    `hf_physical` slot of `orbit_E2_pmDist_deviation` / `coset_route2_success_hybrid_norm_E2` with
    `f_runwayPhysical := physRunwayOracle m w bits numWin TfamK TfamKinv`.  This is what the final
    glue passes for `hf_physical`. -/
theorem hf_physical_runway (m w bits numWin N cm : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat) :
    ∀ (k : Nat), k < m → ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval
                (physRunwayOracle m w bits numWin TfamK TfamKinv (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = (FormalRV.Framework.uc_eval (Gate.toUCom (cosetDim w bits)
                (gidneyInPlaceWithSwap w bits (TfamK k) (TfamKinv k) numWin))
              * cosetInputVec w bits N cm z 0) (Fin.cast (E2shor_dim_eq m w bits) y) 0 :=
  fun k hk z hz y => hf_physical_concrete m w bits numWin N cm TfamK TfamKinv k hk z hz y

end FormalRV.Shor.GidneyInPlace.E2PhysicalRealization
