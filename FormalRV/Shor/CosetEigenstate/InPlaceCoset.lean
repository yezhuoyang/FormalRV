/-
  FormalRV.Shor.CosetEigenstate.InPlaceCoset — in-place coset multiplier deviation:
  the three-leg composition `mulFwd ; swap ; reverse mulInv` at the Born-L1 level.
  ════════════════════════════════════════════════════════════════════════════

  The in-place trick maps the two-register coset state
  `(cosetState x, cosetState 0)` to `(cosetState (a·x mod N), cosetState 0)` via

      forward multiply (δ_f)  ;  swap (exact permutation, 0)  ;  reverse uncompute (δ_i).

  `inPlaceMul_deviation_compose` proves the deviation accumulates as `δ_f + δ_i`,
  with the **swap contributing ZERO by permutation invariance** (it is an explicit
  coordinate permutation `permState σ`, so `normSqDist_perm_invariant` removes it).
  Specializing both legs to the windowed coset bound `numAdds·(2/2^m)` gives the
  total `2·numAdds·(2/2^m)` (`inPlaceMul_coset_deviation`).

  Discharge of the two leg hypotheses:
    * forward `δ_f = numAdds·(2/2^m)` — by `CosetMul.cosetMul_superposition_deviation`
      (the controlled-add fold over the data control register; the real wrapping gate
      via `cosetMulOutOfPlace_deviation_wrap` under the running-sum fit);
    * reverse `δ_i = numAdds·(2/2^m)` — symmetrically, the uncompute multiply by `a⁻¹`
      (`a⁻¹` from `CosetModArith.cosetModInv_exists`; the residue returns to `0` —
      i.e. `cosetState N m 0`, NOT exact zero — by `CosetModArith.modInv_mul_cancel`);
    * `U_rev` an isometry — it is a reversible-gate (wrapping) fold, a basis permutation.

  HONEST FENCES (flagged, not buried — see the audit synthesis):
    (1) The two leg deviations and the `U_rev` isometry are taken as HYPOTHESES here;
        their discharge for a CONCRETE multiplier needs the two-register tensor
        factorization (`hfac_*` of `cosetMul_superposition_deviation`), which is
        multiplier-specific and not yet done for any literal `mulFwd`.
    (2) The data register is taken as `cosetState N m x` (a coset superposition), not
        an exact basis `|x⟩`; the basis→coset initialization is a separate obligation.
    (3) Forward and inverse legs are assumed to share `numAdds`; if the `a⁻¹` circuit
        differs, replace `2·numAdds` by `numAddsFwd + numAddsInv` (the general
        `inPlaceMul_deviation_compose` already supports distinct `δ_f, δ_i`).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.CosetMul
import FormalRV.Shor.CosetEigenstate.CosetModArith

namespace FormalRV.Shor.CosetEigenstate.InPlaceCoset

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetEigenstate.ApproxOp (permState normSqDist_triangle normSqDist_perm_invariant)

/-- **THE IN-PLACE DEVIATION COMPOSITION (the three legs).**  Forward operator
    `U_fwd` (deviation `≤ δf` from the ideal `I_fwd`), then the swap as an explicit
    coordinate permutation `permState σ_swap`, then the reverse uncompute `U_rev` (an
    isometry, deviation `≤ δi` from the final `s_out`).  The total Born-L1 deviation
    is `≤ δf + δi`: the **swap drops out entirely** (permutation invariance) and the
    two legs add.  No assumption couples the two leg sizes. -/
theorem inPlaceMul_deviation_compose {dim : Nat}
    (U_fwd U_rev : QState dim → QState dim) (σ_swap : Equiv.Perm (Fin dim))
    (s_in I_fwd s_out : QState dim) (δf δi : ℝ)
    (hrev_isom : ∀ a b, normSqDist (U_rev a) (U_rev b) = normSqDist a b)
    (hfwd : normSqDist (U_fwd s_in) I_fwd ≤ δf)
    (hrev : normSqDist (U_rev (permState σ_swap I_fwd)) s_out ≤ δi) :
    normSqDist (U_rev (permState σ_swap (U_fwd s_in))) s_out ≤ δf + δi := by
  calc normSqDist (U_rev (permState σ_swap (U_fwd s_in))) s_out
      ≤ normSqDist (U_rev (permState σ_swap (U_fwd s_in))) (U_rev (permState σ_swap I_fwd))
          + normSqDist (U_rev (permState σ_swap I_fwd)) s_out := normSqDist_triangle _ _ _
    _ = normSqDist (permState σ_swap (U_fwd s_in)) (permState σ_swap I_fwd)
          + normSqDist (U_rev (permState σ_swap I_fwd)) s_out := by rw [hrev_isom]
    _ = normSqDist (U_fwd s_in) I_fwd
          + normSqDist (U_rev (permState σ_swap I_fwd)) s_out := by rw [normSqDist_perm_invariant]
    _ ≤ δf + δi := by linarith

/-- **IN-PLACE COSET MULTIPLIER DEVIATION — `2·numAdds·(2/2^m)`.**  Specialization of
    `inPlaceMul_deviation_compose` with both legs at the windowed coset bound
    `numAdds·(2/2^m)`: the in-place multiplier carries the input to within
    `2·numAdds·(2/2^m)` (Born-L1) of the ideal final state `s_out` (whose scratch is
    `cosetState N m 0`).  Forward leg + uncompute leg each contribute
    `numAdds·(2/2^m)`; the swap contributes `0`. -/
theorem inPlaceMul_coset_deviation {dim : Nat}
    (U_fwd U_rev : QState dim → QState dim) (σ_swap : Equiv.Perm (Fin dim))
    (s_in I_fwd s_out : QState dim) (numAdds m : Nat)
    (hrev_isom : ∀ a b, normSqDist (U_rev a) (U_rev b) = normSqDist a b)
    (hfwd : normSqDist (U_fwd s_in) I_fwd ≤ (numAdds : ℝ) * (2 / 2 ^ m))
    (hrev : normSqDist (U_rev (permState σ_swap I_fwd)) s_out ≤ (numAdds : ℝ) * (2 / 2 ^ m)) :
    normSqDist (U_rev (permState σ_swap (U_fwd s_in))) s_out
      ≤ 2 * (numAdds : ℝ) * (2 / 2 ^ m) := by
  have heq : 2 * (numAdds : ℝ) * (2 / 2 ^ m)
      = (numAdds : ℝ) * (2 / 2 ^ m) + (numAdds : ℝ) * (2 / 2 ^ m) := by ring
  rw [heq]
  exact inPlaceMul_deviation_compose U_fwd U_rev σ_swap s_in I_fwd s_out _ _ hrev_isom hfwd hrev

end FormalRV.Shor.CosetEigenstate.InPlaceCoset
