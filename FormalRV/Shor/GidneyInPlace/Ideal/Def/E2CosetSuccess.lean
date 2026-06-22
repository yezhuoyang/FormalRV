/-
  FormalRV.Shor.GidneyInPlace.E2CosetSuccess — A1′ of the Option-A contract restatement:
  the CORRECTED public actual-side objects for the hybrid/telescoping route, over the
  TWO-REGISTER `E2shorZ` embedding (`cosetInputVec` columns).
  ════════════════════════════════════════════════════════════════════════════

  WHY A1 (`CosetEmbeddedSuccess.probability_of_success_cosetEmbedded`) WAS WRONG FOR THIS ROUTE.
  That object is built over `Shor_final_state_cosetEmbedded = orbitState (qpeStageMap f)
  (E_phys (qpeInit)) …`, where `E_phys`'s column is a SINGLE-register `cosetState` (the runway on
  the whole work-register value, `cosetEmbedMat_eq_cosetState`).  But the faithful physical gate
  `gidneyInPlaceWithSwap` is a TWO-register multiplier, and H3.1
  (`PmDistLocalDeviation.gidneyInPlaceWithSwap_coset_pmDist_deviation`) bounds its action on
  `cosetInputVec z 0 = cosetInputTwoReg …` — the a-block `cosetState z` ⊗ b-block `cosetState 0`
  product.  These two embeddings are DIFFERENT states, so the hybrid route's actual side must be
  the `E2shorZ` (two-register) trajectory, NOT the `E_phys` one.  `E_phys`/`cosetEmbeddedInit`/
  `Shor_final_state_cosetEmbedded` belong to the (dead) EmbedAgreeOff route only.

  THESE are the hybrid route's public actual-side objects:
    • `E2cosetInit`              = `E2shorZ (qpeInit)` (the runway-product init the telescope shares);
    • `Shor_final_state_E2coset` = the QPE stages run on it;
    • `probability_of_success_E2coset` = its outcome-weighted phase marginal.

  THE TARGET CAPSTONE (H5):
    `probability_of_success_E2coset a r N m w bits cm f_coset
        ≥ probability_of_success a r N m bits (cosetAnc w bits) f_ideal
            − 2·m·√(8·numWin/2^cm)`
  i.e. the ACTUAL runway/coset (two-register) machine succeeds almost as well as the ORDINARY
  ideal Shor machine — the ideal side stays plain, transported via the embedding's marginal
  preservation (`E2shor_hmarg`).

  Option B (plain-init success via an approximate init bridge with its own `ε_init`) remains
  explicit future work, NOT claimed here.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Embedding.Def.InPlaceTwoRegEmbedCanon
import FormalRV.Shor.GidneyInPlace.Primitives.Def.OrbitState
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Input.InPlaceCosetInputNorm
import FormalRV.Shor.Approx.GracefulDegradation
import FormalRV.Shor.MainAlgorithm.QuantumAndContinuedFractions.ShorStatesAndHeadlineStatements

namespace FormalRV.Shor.GidneyInPlace.E2CosetSuccess

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer (jointIdx sum_jointIdx_eq)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputNorm (cosetInputVec_normalized)
open FormalRV.Shor.GidneyInPlace.BranchFactor (jointEquiv jointEquiv_apply)
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp (qpeInit qpeStageMap)
open FormalRV.Shor.GidneyInPlace.OrbitState (orbitState)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedCanon (E2shorZ)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.Approx (pmNorm)
open FormalRV.Shor.CosetBornWeight (bornWeightOn)

/-- **⚠ SUPERSEDED / INCORRECT for the hybrid route** — `E2shorZ` of the H-prepared ideal init
    `qpeInit`.  This is DEGENERATE: `qpeInit`'s per-phase work register is the canonical basis
    vector at work value `2^(cosetAnc w bits)` (the value of `|1⟩_bits ⊗ |0⟩_anc` under the
    standard kron ordering), which for real parameters satisfies `2^(cosetAnc w bits) ≥ N`, so
    `E2shorZ` (which ZEROES all columns `yp.val ≥ N`) maps it to the ZERO state.  Kept ONLY as a
    dead artifact; it no longer feeds `Shor_final_state_E2coset`.  The corrected init is the
    DIRECT runway-product state `E2runwayInit` below (phase-uniform ⊗ `cosetInputVec 1 0`), the
    genuine residue-1 two-register runway state — NOT obtained by applying `E2shorZ` to `qpeInit`. -/
noncomputable def E2cosetInit (m w bits N cm : Nat) :
    QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) :=
  E2shorZ m w bits N cm (qpeInit m bits (cosetAnc w bits))

/-- **The corrected direct runway-product (two-register) telescope init** `E2runwayInit`.
    Defined DIRECTLY (mirroring `E2shorZ`'s `jointEquiv.symm` structure, but WITHOUT applying
    `E2shorZ` to anything): per phase branch, the work register is the faithful two-register
    coset state `cosetInputVec 1 0` (residue `z = 1`), uniformly weighted across phases by
    `1/√2^m`.  This is the genuine residue-1 runway state the physical gate acts on — in contrast
    to the degenerate `E2cosetInit = E2shorZ (qpeInit)`, which is the zero state for real
    parameters (its `qpeInit` accumulator-`|1⟩` sits at work value `2^(cosetAnc w bits) ≥ N`,
    zeroed by `E2shorZ`).  This is the shared init of the hybrid telescope. -/
noncomputable def E2runwayInit (m w bits N cm : Nat) :
    QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) :=
  fun i _ =>
    let p := (jointEquiv (shorDvd m bits (cosetAnc w bits))).symm i
    ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
      * cosetInputVec w bits N cm 1 0 (Fin.cast (E2shor_dim_eq m w bits) p.2) 0

/-- **`E2runwayInit` touches only the data factor** (the `E2shorZ_acts` analogue).  Reading it at
    `jointIdx x y` gives `(1/√2^m) · cosetInputVec 1 0` at the cast work index `y`. -/
theorem E2runwayInit_acts (m w bits N cm : Nat)
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    E2runwayInit m w bits N cm (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
      = ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
          * cosetInputVec w bits N cm 1 0 (Fin.cast (E2shor_dim_eq m w bits) y) 0 := by
  unfold E2runwayInit
  simp only
  rw [show jointIdx (shorDvd m bits (cosetAnc w bits)) x y
        = jointEquiv (shorDvd m bits (cosetAnc w bits)) (x, y) from
      (jointEquiv_apply (shorDvd m bits (cosetAnc w bits)) x y).symm,
    Equiv.symm_apply_apply]

/-- **The hybrid actual-side coset Shor final state** — the QPE stages run on the corrected
    DIRECT two-register runway init `E2runwayInit`.  This is the object the pmDist telescope (H1)
    bounds against the ideal trajectory; its success marginal is the Option-A exported quantity. -/
noncomputable def Shor_final_state_E2coset (m w bits N cm : Nat)
    (f : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits)) :
    QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) :=
  orbitState (qpeStageMap m bits (cosetAnc w bits) f) (E2runwayInit m w bits N cm) (m + 1)

/-- **The hybrid (two-register `E2coset`) Shor success probability** — the Option-A public
    actual-side object.  Verbatim analogue of `probability_of_success`
    (ShorStatesAndHeadlineStatements.lean:81), but the final state is the two-register
    `Shor_final_state_E2coset` (physical gate on the runway-product init), so the bound this
    object carries is over the machine Gidney's two-register construction actually realizes. -/
noncomputable def probability_of_success_E2coset
    (a r N m w bits cm : Nat)
    (f : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits)) : ℝ :=
  ∑ x ∈ Finset.range (2 ^ m),
    r_found x m r a N *
      prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state_E2coset m w bits N cm f)

/-- `Shor_final_state_E2coset` is the orbit of the stage map over the corrected direct
    `E2runwayInit` — by definition (the `hdecomp_a` of the hybrid route, free). -/
theorem Shor_final_state_E2coset_def (m w bits N cm : Nat)
    (f : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits)) :
    Shor_final_state_E2coset m w bits N cm f
      = orbitState (qpeStageMap m bits (cosetAnc w bits) f) (E2runwayInit m w bits N cm) (m + 1) :=
  rfl

/-- Unfolding lemma for the hybrid success object (kept for downstream rewrites). -/
theorem probability_of_success_E2coset_def
    (a r N m w bits cm : Nat)
    (f : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits)) :
    probability_of_success_E2coset a r N m w bits cm f
      = ∑ x ∈ Finset.range (2 ^ m),
          r_found x m r a N *
            prob_partial_meas (basis_vector (2 ^ m) x)
              (Shor_final_state_E2coset m w bits N cm f) :=
  rfl

/-! ## Normalization and nonvanishing of the corrected direct runway init. -/

/-- **`E2runwayInit` is a unit vector.**  `pmNorm (E2runwayInit) = 1`.  The total Born mass
    splits (via `sum_jointIdx_eq`) into the phase sum of `1/2^m` times the per-phase data-factor
    mass, each of which is `1` by `cosetInputVec_normalized` (T1) modulo the `E2shor_dim_eq`
    reindex; the phase sum of `2^m` copies of `1/2^m` is `1`, so `pmNorm = √1 = 1`. -/
theorem E2runwayInit_normalized (m w bits numWin N cm : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hfit : 1 + (2 ^ cm - 1) * N < 2 ^ bits) :
    pmNorm (E2runwayInit m w bits N cm) = 1 := by
  classical
  -- the total Born mass equals 1
  have hmass : (∑ i, Complex.normSq (E2runwayInit m w bits N cm i 0)) = 1 := by
    -- split the full-register sum into the phase × work sum
    rw [← sum_jointIdx_eq (shorDvd m bits (cosetAnc w bits))
          (fun i => Complex.normSq (E2runwayInit m w bits N cm i 0))]
    -- read each term via E2runwayInit_acts and factor the scalar
    have hterm : ∀ (x : Fin (2 ^ m)),
        (∑ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            Complex.normSq (E2runwayInit m w bits N cm
              (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0))
          = ((1 : ℝ) / (2 ^ m : ℝ)) := by
      intro x
      -- substitute E2runwayInit_acts and split normSq of the product
      rw [Finset.sum_congr rfl (fun y _ => by
            rw [E2runwayInit_acts m w bits N cm x y, Complex.normSq_mul])]
      -- pull the constant normSq(1/√2^m) out
      rw [← Finset.mul_sum]
      -- the data-factor sum, reindexed by the E2shor_dim_eq cast, is 1
      have hdata : (∑ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
            Complex.normSq (cosetInputVec w bits N cm 1 0
              (Fin.cast (E2shor_dim_eq m w bits) y) 0))
          = 1 := by
        have hbw : bornWeightOn (cosetInputVec w bits N cm 1 0) Finset.univ = 1 :=
          cosetInputVec_normalized w bits numWin N cm 1 hw hbits hN (by omega)
        unfold bornWeightOn at hbw
        rw [← hbw]
        exact Fintype.sum_equiv (finCongr (E2shor_dim_eq m w bits)) _ _ (fun y => by rfl)
      rw [hdata, mul_one]
      -- normSq((1:ℂ)/√2^m) = 1/2^m
      rw [show ((1 : ℂ) / (Real.sqrt (2 ^ m : ℝ) : ℂ))
            = ((1 / Real.sqrt (2 ^ m : ℝ) : ℝ) : ℂ) by push_cast; ring,
          Complex.normSq_ofReal]
      rw [div_mul_div_comm, one_mul,
          Real.mul_self_sqrt (by positivity)]
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [show ((2 ^ m : ℕ) : ℝ) = (2 ^ m : ℝ) by push_cast; ring]
    field_simp
  unfold pmNorm
  rw [hmass, Real.sqrt_one]

/-- **`E2runwayInit` is nonzero** (for `1 < N`, the relevant nonemptiness).  Immediate from
    `E2runwayInit_normalized` (a unit vector cannot be the zero state) — its total Born mass is
    `1 ≠ 0`. -/
theorem E2runwayInit_ne_zero (m w bits numWin N cm : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hfit : 1 + (2 ^ cm - 1) * N < 2 ^ bits) :
    E2runwayInit m w bits N cm ≠ (fun _ _ => 0) := by
  intro hzero
  have hmass : pmNorm (E2runwayInit m w bits N cm) = 0 := by
    unfold pmNorm
    rw [hzero]
    simp
  rw [E2runwayInit_normalized m w bits numWin N cm hw hbits hN hfit] at hmass
  exact one_ne_zero hmass

end FormalRV.Shor.GidneyInPlace.E2CosetSuccess
