/-
  FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg — F1 WRAPPER: the full
  Shor-register embedding E₂_shor and the EXACT `hmarg` field of `ApproxCosetOrbitShift`.
  ════════════════════════════════════════════════════════════════════════════

  Defines `E2shor = I_phase ⊗ E2data` on the Shor register `2^m·2^bits·2^(cosetAnc w bits)` (so
  `n=bits`, `anc=cosetAnc w bits`; the data factor `(2^m·2^bits·2^cosetAnc)/2^m` equals
  `2^cosetDim` via `E2shor_dim_eq = workDim_eq ▸ cosetWork_dim_eq`), and proves the EXACT marginal
  field the Route-2 engine consumes:

      prob_partial_meas (basis_vector (2^m) x.val) (E2shor φ)
        = prob_partial_meas (basis_vector (2^m) x.val) φ      (for canonically-supported φ).

  This is `ApproxCosetOrbitShift.hmarg` verbatim (with `E_phys := E2shor`).  Proven by mirroring
  `E_phys`/`E_phys_acts`/`E_phys_marginal`, reducing through `prob_partial_meas_basis_eq` to the
  data-factor isometry `E2data_marginal` (F1 core), threading the `E2shor_dim_eq` cast.  NO
  `cosetEmbedMat`, NO `prepB`, NO σ-relabel, no ε / probability-loss claims.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Embedding.Def.InPlaceTwoRegEmbedMarginal
import FormalRV.Shor.GidneyInPlace.InPlace.Def.InPlaceCosetGate
import FormalRV.Shor.GidneyInPlace.QPE.Proof.ControlStageBridge
import FormalRV.Shor.CosetMarginalShorBound

namespace FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc cosetWork_dim_eq)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq)
open FormalRV.Shor.GidneyInPlace.BranchFactor (jointEquiv jointEquiv_apply)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedMarginal (E2data E2data_marginal)

/-- The data-factor dimension of the Shor register (with `n=bits`, `anc=cosetAnc w bits`) is
    `2^cosetDim` — `workDim_eq` composed with `cosetWork_dim_eq`. -/
theorem E2shor_dim_eq (m w bits : Nat) :
    (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m = 2 ^ (cosetDim w bits) :=
  (workDim_eq m bits (cosetAnc w bits)).trans (congrArg (2 ^ ·) (cosetWork_dim_eq w bits))

/-- **The full Shor-register two-register embedding** `E2shor = I_phase ⊗ E2data`.  Mirrors
    `CosetEphys.E_phys`, with the data-factor matrix entry `cosetEmbedMat … p.2 yp` replaced by
    the faithful column `cosetInputVec yp.val 0` read at the cast row `Fin.cast E2shor_dim_eq p.2`. -/
noncomputable def E2shor (m w bits N cm : Nat)
    (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits))) :
    QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) :=
  fun i _ =>
    let p := (jointEquiv (shorDvd m bits (cosetAnc w bits))).symm i
    ∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
      cosetInputVec w bits N cm yp.val 0 (Fin.cast (E2shor_dim_eq m w bits) p.2) 0
        * phi (jointIdx (shorDvd m bits (cosetAnc w bits)) p.1 yp) 0

/-- **`E2shor` touches only the data factor** (the `E_phys_acts` analogue). -/
theorem E2shor_acts (m w bits N cm : Nat) (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    E2shor m w bits N cm phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
      = ∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
          cosetInputVec w bits N cm yp.val 0 (Fin.cast (E2shor_dim_eq m w bits) y) 0
            * phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x yp) 0 := by
  unfold E2shor
  simp only
  rw [show jointIdx (shorDvd m bits (cosetAnc w bits)) x y
        = jointEquiv (shorDvd m bits (cosetAnc w bits)) (x, y) from
      (jointEquiv_apply (shorDvd m bits (cosetAnc w bits)) x y).symm,
    Equiv.symm_apply_apply]

/-- **F1 WRAPPER — the exact `hmarg` field.**  For a state `phi` supported on canonical residues
    (`yp.val < N`), the two-register embedding `E2shor` preserves the per-outcome Born marginal.
    Reduces through `prob_partial_meas_basis_eq` + the `E2shor_dim_eq` cast to the data-factor
    isometry `E2data_marginal`. -/
theorem E2shor_hmarg (m w bits numWin N cm : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hN : 0 < N) (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (hsupp : ∀ (x : Fin (2 ^ m)) (yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        N ≤ yp.val → phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x yp) 0 = 0)
    (x : Fin (2 ^ m)) :
    prob_partial_meas (basis_vector (2 ^ m) x.val) (E2shor m w bits N cm phi)
      = prob_partial_meas (basis_vector (2 ^ m) x.val) phi := by
  classical
  rw [prob_partial_meas_basis_eq (E2shor m w bits N cm phi) x (shorDvd m bits (cosetAnc w bits)),
      prob_partial_meas_basis_eq phi x (shorDvd m bits (cosetAnc w bits))]
  set e := finCongr (E2shor_dim_eq m w bits) with he
  set ψ : Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ :=
    fun z' _ => phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x (e.symm z')) 0 with hψ
  have hval : ∀ z' : Fin (2 ^ cosetDim w bits), (e.symm z').val = z'.val := by
    intro z'; rw [he]; rfl
  have hey : ∀ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
      e y = Fin.cast (E2shor_dim_eq m w bits) y := by
    intro y; rw [he]; rfl
  have hψsupp : ∀ z' : Fin (2 ^ cosetDim w bits), N ≤ z'.val → ψ z' 0 = 0 := by
    intro z' hz'
    show phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x (e.symm z')) 0 = 0
    exact hsupp x (e.symm z') (by rw [hval]; exact hz')
  -- per-`y` collapse to E2data at the cast index
  have hpoint : ∀ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
      Complex.normSq (E2shor m w bits N cm phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0)
        = Complex.normSq (E2data w bits N cm ψ (e y) 0) := by
    intro y
    congr 1
    rw [E2shor_acts m w bits N cm phi x y,
        show E2data w bits N cm ψ (e y) 0
          = ∑ z' : Fin (2 ^ cosetDim w bits),
              cosetInputVec w bits N cm z'.val 0 (e y) 0 * ψ z' 0 from rfl,
        hey y,
        ← Equiv.sum_comp e.symm
          (fun yp => cosetInputVec w bits N cm yp.val 0 (Fin.cast (E2shor_dim_eq m w bits) y) 0
            * phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x yp) 0)]
    refine Finset.sum_congr rfl (fun z' _ => ?_)
    simp only [hψ, hval]
  -- assemble both sides through the cast equiv `e`
  rw [Finset.sum_congr rfl (fun y _ => hpoint y),
      Equiv.sum_comp e (fun y' => Complex.normSq (E2data w bits N cm ψ y' 0)),
      E2data_marginal w bits numWin N cm hw hbits hN hMN ψ hψsupp,
      ← Equiv.sum_comp e.symm
        (fun y => Complex.normSq (phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0))]

end FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg
