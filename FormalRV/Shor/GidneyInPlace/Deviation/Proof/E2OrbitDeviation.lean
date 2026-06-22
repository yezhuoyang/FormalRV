/-
  FormalRV.Shor.GidneyInPlace.E2OrbitDeviation — H4 of the coset-Shor hybrid route:
  the ORBIT-LEVEL ℓ² deviation bound (telescope accumulation of the per-step H3.2 lift).
  ════════════════════════════════════════════════════════════════════════════

  H1 (`PmDistTelescope.pmDist_orbit_telescope`) accumulates a per-step local deviation `δ k`
  into a final-state bound `∑ δ k`.  H3.2 (`E2LocalDeviation.qpeStage_E2_local_pmDist_deviation`)
  supplies that per-step deviation at each ORACLE stage `k < m`:  `√(8·numWin/2^cm)`.  This file
  runs the telescope over the full `m + 1` QPE stages and lands the orbit bound

    `pmDist (Shor_final_state_E2coset f_runwayPhysical)
            (Shor_final_state_E2coset f_runwayIdeal)
      ≤ m · √(8·numWin/2^cm)`.

  THE CONSTANT IS EXACTLY `m`, NOT `m + 1`.  The QPE stage circuit
  (`QPEStageDecomp.qpeStageUCom`) references the oracle family `f` ONLY in the `k < m` branch;
  for EVERY `k ≥ m` the stage is the f-independent `QFTinv m`.  So the physical and ideal stages
  COINCIDE on the QFTinv stage (`k = m`, the last one) — its local deviation is `δ m = 0`.  The
  telescope sum over `Finset.range (m + 1)` is therefore `m · √(…) + 0 = m · √(…)`.

  ROUTE.
    • `qpeStageMap_eq_of_ge` — the general f-independence `qpeStageMap f k = qpeStageMap g k`
      for `m ≤ k` (the existing `E2ResidueEmbed.qpeStageMap_qftinv_indep` is the `k = m` case
      only; the telescope's `∀ k` `hlocal` needs it for ALL `k ≥ m`).
    • `pmDist_orbit_telescope_qftinv` — the ABSTRACT core: given isometric actual steps
      (`hisom`), a per-step oracle bound `≤ L` (`hstep`, for `k < m`), and f-independence of the
      tail stages (`hqftinv`, for `m ≤ k`), the `m + 1`-stage orbit deviates by `≤ m · L`.
    • `orbit_E2_pmDist_deviation` — the concrete H4: wires H3.2 (per oracle stage, on the ideal
      trajectory point `orbitState … k`, which is in `IdealCosetForm` by P1.2's
      `idealCosetForm_orbit_runway_direct`) into the core.

  HYPOTHESES (all carried EXPLICITLY, dischargeable later; NO bad sets, NO EmbedAgreeOff, NO
  `normSqDist` except through the H3.1/H3.2 dependency chain):
    • `hisom` — each physical stage is a `pmDist` isometry (this is what `hU` will discharge; we
      do NOT prove `hU` here);
    • `hf_physical` — the physical oracle's active work action realizes the gidney gate (per
      stage `k < m`, with the per-stage table family `TfamK k`/`TfamKinv k = tableValue (mult k)/
      (kInv k)`);  `hf_runway` — the ideal oracle's active work action is the clean coset shift;
    • the per-stage coprimality/fit data feeding H3.1.
  The two oracle families `f_runwayPhysical ≠ f_runwayIdeal` are DISTINCT.

  Kernel-clean target: no `sorry`, no `native_decide`, no axioms beyond `{propext,
  Classical.choice, Quot.sound}`.
-/
import FormalRV.Shor.GidneyInPlace.Deviation.Engine.PmDistTelescope
import FormalRV.Shor.GidneyInPlace.Deviation.Proof.E2LocalDeviation
import FormalRV.Shor.GidneyInPlace.Ideal.Def.E2CosetSuccess

namespace FormalRV.Shor.GidneyInPlace.E2OrbitDeviation

open scoped Classical BigOperators
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate (gidneyInPlaceWithSwap)
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp (qpeStageMap qpeStageUCom)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq)
open FormalRV.Shor.GidneyInPlace.InPlaceE2IdealTrajectory
  (IdealCosetForm idealCosetForm_orbit_runway_direct)
open FormalRV.Shor.GidneyInPlace.E2LocalDeviation (qpeStage_E2_local_pmDist_deviation)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess
  (E2runwayInit Shor_final_state_E2coset Shor_final_state_E2coset_def)
open FormalRV.Shor.Approx (pmDist pmDist_eq_dist pmDist_orbit_telescope)
open FormalRV.Shor.GidneyInPlace.OrbitState (orbitState)

/-! ## §1. General f-independence of the tail (QFTinv) stages. -/

/-- **The QPE stage map is INDEPENDENT of the oracle family `f` for every `k ≥ m`.**  The stage
    circuit `qpeStageUCom m n anc f k` reduces to the f-independent `QFTinv m` whenever
    `¬ (k < m)`, so the cast-conjugated stage maps coincide.  (Generalizes
    `E2ResidueEmbed.qpeStageMap_qftinv_indep`, which is only the `k = m` case; the telescope's
    `∀ k` `hlocal` needs all tail stages.) -/
theorem qpeStageMap_eq_of_ge (m n anc : Nat)
    (f g : Nat → FormalRV.Framework.BaseUCom (n + anc)) (k : Nat) (hk : m ≤ k) :
    qpeStageMap m n anc f k = qpeStageMap m n anc g k := by
  funext psi
  show QState.cast (dim_assoc_eq m n anc)
        (uc_eval (qpeStageUCom m n anc f k) (QState.cast (dim_assoc_eq m n anc).symm psi))
      = QState.cast (dim_assoc_eq m n anc)
        (uc_eval (qpeStageUCom m n anc g k) (QState.cast (dim_assoc_eq m n anc).symm psi))
  have hfg : qpeStageUCom m n anc f k = qpeStageUCom m n anc g k := by
    unfold qpeStageUCom
    rw [if_neg (Nat.not_lt.mpr hk), if_neg (Nat.not_lt.mpr hk)]
  rw [hfg]

/-! ## §2. The abstract telescope core: `m` oracle stages at `≤ L`, then an f-independent tail. -/

/-- **H4 core — telescope an `m`-stage-then-QFTinv orbit.**  Abstract over the actual/ideal step
    families `Fa`/`Fi`.  Given:
      • `hisom` — each actual step is a `pmDist` isometry;
      • `hstep` — for each ORACLE stage `k < m`, the actual step deviates from the ideal
        trajectory by `≤ L`;
      • `hqftinv` — for every TAIL stage `m ≤ k`, the actual and ideal steps COINCIDE
        (`Fa k = Fi k`), so the tail contributes ZERO deviation;
    the `m + 1`-stage orbits deviate by `≤ m · L`.

    The telescope (`pmDist_orbit_telescope`) is applied with the per-step budget
    `δ k = if k < m then L else 0`; the tail term `δ m = 0` is exactly why the constant is `m`
    and not `m + 1`. -/
theorem pmDist_orbit_telescope_qftinv {full_dim : Nat} (m : Nat)
    (Fa Fi : Nat → QState full_dim → QState full_dim)
    (init : QState full_dim) (L : ℝ)
    (hisom : ∀ (k : Nat) (a b : QState full_dim), pmDist (Fa k a) (Fa k b) = pmDist a b)
    (hstep : ∀ (k : Nat), k < m →
        pmDist (Fa k (orbitState Fi init k)) (orbitState Fi init (k + 1)) ≤ L)
    (hqftinv : ∀ (k : Nat), m ≤ k → Fa k = Fi k) :
    pmDist (orbitState Fa init (m + 1)) (orbitState Fi init (m + 1)) ≤ (m : ℝ) * L := by
  -- the per-step budget: L on oracle stages, 0 on the f-independent tail.
  have hlocal : ∀ (k : Nat),
      pmDist (Fa k (orbitState Fi init k)) (orbitState Fi init (k + 1))
        ≤ (if k < m then L else 0) := by
    intro k
    by_cases hk : k < m
    · rw [if_pos hk]; exact hstep k hk
    · -- tail stage: Fa k = Fi k, and `orbitState Fi init (k+1) = Fi k (orbitState Fi init k)`.
      have hge : m ≤ k := Nat.not_lt.mp hk
      rw [if_neg hk, hqftinv k hge]
      exact le_of_eq (by rw [pmDist_eq_dist]; exact dist_self _)
  have hbound := pmDist_orbit_telescope Fa Fi init (fun k => if k < m then L else 0)
    hisom hlocal (m + 1)
  -- ∑_{k ∈ range (m+1)} (if k < m then L else 0) = m · L.
  have hsum : (∑ k ∈ Finset.range (m + 1), (if k < m then L else 0)) = (m : ℝ) * L := by
    rw [Finset.sum_range_succ, if_neg (Nat.lt_irrefl m), add_zero]
    rw [show (∑ k ∈ Finset.range m, (if k < m then L else 0)) = ∑ _k ∈ Finset.range m, L from
      Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc pmDist (orbitState Fa init (m + 1)) (orbitState Fi init (m + 1))
      ≤ ∑ k ∈ Finset.range (m + 1), (if k < m then L else 0) := hbound
    _ = (m : ℝ) * L := hsum

/-! ## §3. H4 — the concrete coset-Shor orbit deviation bound. -/

/-- **H4 — the orbit-level coset-Shor ℓ² deviation bound.**  The ACTUAL runway/coset machine
    (`Shor_final_state_E2coset f_runwayPhysical`, the physical in-place gate orbit over
    `E2runwayInit`) deviates from the IDEAL runway machine (`f_runwayIdeal`, the clean coset
    shift) by at most `m · √(8·numWin/2^cm)` in the ℓ² distance `pmDist`.

    Telescope accumulation of H3.2 over the `m` oracle stages; the trailing QFTinv stage is
    f-independent (`qpeStageMap_eq_of_ge`) so contributes `0` — the constant is exactly `m`.
    Each oracle stage's ideal trajectory point `orbitState … k` is in `IdealCosetForm` by P1.2.

    The per-stage table families are k-indexed (`TfamK k = tableValue (mult k)` etc.), faithful
    to Shor's stagewise multiplier `mult k`.  `hisom` is carried as an explicit hypothesis (to be
    discharged later by per-stage matrix unitarity `hU`); the realization hypotheses
    `hf_physical`/`hf_runway` are DISTINCT and carried explicitly. -/
theorem orbit_E2_pmDist_deviation
    (m w bits numWin N cm : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat) (mult kInv : Nat → Nat)
    (f_runwayPhysical f_runwayIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwtP : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayPhysical j))
    (hwtI : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hTfamK : ∀ k j addr, TfamK k j addr = tableValue (mult k) N w j addr)
    (hTfamKinv : ∀ k j addr, TfamKinv k j addr = tableValue (kInv k) N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hN1 : 1 < N)
    (hkkinv : ∀ k, (kInv k * mult k) % N = 1 % N)
    (hfit : ∀ (k z : Nat), z < N → (mult k * z) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (hxfit : ∀ (z : Nat), z < N → z + (2 ^ cm - 1) * N < 2 ^ bits)
    (hisom : ∀ (k : Nat) (a b : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits))),
        pmDist (qpeStageMap m bits (cosetAnc w bits) f_runwayPhysical k a)
               (qpeStageMap m bits (cosetAnc w bits) f_runwayPhysical k b) = pmDist a b)
    (hf_physical : ∀ (k : Nat), k < m → ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayPhysical (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = (FormalRV.Framework.uc_eval (Gate.toUCom (cosetDim w bits)
                (gidneyInPlaceWithSwap w bits (TfamK k) (TfamKinv k) numWin))
              * cosetInputVec w bits N cm z 0) (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_runway : ∀ (k : Nat) (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
              * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
          = cosetInputVec w bits N cm ((mult k * z) % N) 0
              (Fin.cast (E2shor_dim_eq m w bits) y) 0) :
    pmDist (Shor_final_state_E2coset m w bits N cm f_runwayPhysical)
        (Shor_final_state_E2coset m w bits N cm f_runwayIdeal)
      ≤ (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) := by
  rw [Shor_final_state_E2coset_def, Shor_final_state_E2coset_def]
  -- per-oracle-stage local bound (H3.2 on the ideal trajectory point, which is in IdealCosetForm).
  have hstep : ∀ (k : Nat), k < m →
      pmDist (qpeStageMap m bits (cosetAnc w bits) f_runwayPhysical k
                (orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
                  (E2runwayInit m w bits N cm) k))
             (orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
                (E2runwayInit m w bits N cm) (k + 1))
        ≤ Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) := by
    intro k hk
    have hΦ : IdealCosetForm m w bits N cm
        (orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
          (E2runwayInit m w bits N cm) k) :=
      idealCosetForm_orbit_runway_direct m w bits N cm hN hN1 f_runwayIdeal hwtI mult hf_runway
        k (Nat.le_of_lt hk)
    exact qpeStage_E2_local_pmDist_deviation m w bits numWin N cm k (kInv k) hk
      (TfamK k) (TfamKinv k) f_runwayPhysical f_runwayIdeal hwtP hwtI mult
      (hTfamK k) (hTfamKinv k) hw hbits hN (hkkinv k) (hfit k) hxfit
      (orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
        (E2runwayInit m w bits N cm) k) hΦ
      (fun z hz y => hf_physical k hk z hz y) (fun z hz y => hf_runway k z hz y)
  exact pmDist_orbit_telescope_qftinv m
    (qpeStageMap m bits (cosetAnc w bits) f_runwayPhysical)
    (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
    (E2runwayInit m w bits N cm) (Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm))
    hisom hstep
    (fun k hge => qpeStageMap_eq_of_ge m bits (cosetAnc w bits)
      f_runwayPhysical f_runwayIdeal k hge)

end FormalRV.Shor.GidneyInPlace.E2OrbitDeviation
