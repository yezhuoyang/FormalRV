/-
  FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedCanon — F2 brick-1 prerequisite:
  the CANONICAL-ZEROED two-register embedding E2shorZ.
  ════════════════════════════════════════════════════════════════════════════

  The controlled-oracle `hwork_int` quantifies over ALL columns `y2` — including non-canonical
  `y2.val ≥ N`, where T2 (`gidneyInPlaceWithSwap_agree_off_explicit`, needs `x < N`) gives nothing.
  Per the design decision, E₂'s embedding zeroes its non-canonical columns:

      E2shorZ column yp = (if yp.val < N then cosetInputVec yp.val 0 else 0).

  Then `hwork_int` at a non-canonical column is trivially `0 = 0`, and the canonical columns are
  handled by `inplace_agree_off_union` (T2 off the union).

  CRUCIALLY this changes the embedding ONLY on non-canonical columns, so on canonical-supported `φ`
  (the only case F1's `hmarg` cares about) E2shorZ AGREES with E2shor pointwise — hence F1's
  `E2shor_hmarg` is REUSED verbatim (no re-proof) via the bridge `E2shorZ_eq_canon`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Embedding.Def.InPlaceTwoRegEmbedHmarg

namespace FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedCanon

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.BranchFactor (jointEquiv jointEquiv_apply)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor E2shor_acts E2shor_hmarg E2shor_dim_eq)

/-- **The canonical-zeroed Shor-register embedding** `E2shorZ`.  Identical to `E2shor` except its
    non-canonical columns (`yp.val ≥ N`) are zeroed — so `hwork_int`'s `∀ y2` includes the
    non-canonical columns trivially. -/
noncomputable def E2shorZ (m w bits N cm : Nat)
    (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits))) :
    QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) :=
  fun i _ =>
    let p := (jointEquiv (shorDvd m bits (cosetAnc w bits))).symm i
    ∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
      (if yp.val < N then
          cosetInputVec w bits N cm yp.val 0 (Fin.cast (E2shor_dim_eq m w bits) p.2) 0
        else 0)
        * phi (jointIdx (shorDvd m bits (cosetAnc w bits)) p.1 yp) 0

/-- `E2shorZ` touches only the data factor (the `E2shor_acts` analogue). -/
theorem E2shorZ_acts (m w bits N cm : Nat) (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    E2shorZ m w bits N cm phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
      = ∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
          (if yp.val < N then
              cosetInputVec w bits N cm yp.val 0 (Fin.cast (E2shor_dim_eq m w bits) y) 0
            else 0)
            * phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x yp) 0 := by
  unfold E2shorZ
  simp only
  rw [show jointIdx (shorDvd m bits (cosetAnc w bits)) x y
        = jointEquiv (shorDvd m bits (cosetAnc w bits)) (x, y) from
      (jointEquiv_apply (shorDvd m bits (cosetAnc w bits)) x y).symm,
    Equiv.symm_apply_apply]

/-- **The canonical-agreement bridge.**  On canonical-supported `phi`, `E2shorZ` agrees with
    `E2shor` pointwise at every `jointIdx x y` — the zeroed non-canonical columns coincide with
    `E2shor`'s (which are killed by `phi = 0` there). -/
theorem E2shorZ_eq_canon (m w bits N cm : Nat)
    (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (hsupp : ∀ (x : Fin (2 ^ m)) (yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        N ≤ yp.val → phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x yp) 0 = 0)
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    E2shorZ m w bits N cm phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
      = E2shor m w bits N cm phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0 := by
  rw [E2shorZ_acts m w bits N cm phi x y, E2shor_acts m w bits N cm phi x y]
  refine Finset.sum_congr rfl (fun yp _ => ?_)
  by_cases hyp : yp.val < N
  · rw [if_pos hyp]
  · rw [if_neg hyp, zero_mul, hsupp x yp (Nat.le_of_not_lt hyp), mul_zero]

/-- **`hmarg` for the canonical-zeroed embedding** — reused from F1's `E2shor_hmarg` verbatim via
    the bridge (no re-proof).  This is the exact `ApproxCosetOrbitShift.hmarg` field with
    `E_phys := E2shorZ`. -/
theorem E2shorZ_hmarg (m w bits numWin N cm : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hN : 0 < N) (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (hsupp : ∀ (x : Fin (2 ^ m)) (yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        N ≤ yp.val → phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x yp) 0 = 0)
    (x : Fin (2 ^ m)) :
    prob_partial_meas (basis_vector (2 ^ m) x.val) (E2shorZ m w bits N cm phi)
      = prob_partial_meas (basis_vector (2 ^ m) x.val) phi := by
  rw [prob_partial_meas_basis_eq (E2shorZ m w bits N cm phi) x (shorDvd m bits (cosetAnc w bits)),
      Finset.sum_congr rfl (fun y _ => by rw [E2shorZ_eq_canon m w bits N cm phi hsupp x y]),
      ← prob_partial_meas_basis_eq (E2shor m w bits N cm phi) x (shorDvd m bits (cosetAnc w bits))]
  exact E2shor_hmarg m w bits numWin N cm hw hbits hN hMN phi hsupp x

end FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedCanon
