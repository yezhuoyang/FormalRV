/-
  FormalRV.Shor.GidneyInPlace.InPlaceCoset — in-place coset multiplier deviation:
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
import FormalRV.Shor.GidneyInPlace.OutOfPlaceCoset.Spec.CosetMul
import FormalRV.Shor.GidneyInPlace.Primitives.Def.CosetModArith
import FormalRV.Shor.GidneyInPlace.Gate.Def.GatePerm
import FormalRV.Shor.GidneyInPlace.Gate.Spec.UCEvalBridge

namespace FormalRV.Shor.GidneyInPlace.InPlaceCoset

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.ApproxOp (permState normSqDist_triangle normSqDist_perm_invariant)
open FormalRV.Shor.GidneyInPlace.GateReversible (Gate.reverse)
open FormalRV.Shor.GidneyInPlace.GatePerm (gateToPerm gate_normSqDist_perm reverse_wellTyped)
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_eq_permState gate_uc_eval_normSqDist_perm)

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

/-- **DISCHARGED FOR THE CONCRETE CIRCUITS.**  Instantiating `inPlaceMul_coset_deviation`
    with the ACTUAL classical reversible gates on the physical register `Fin (2^bits)`:
    the swap leg is the basis permutation `gateToPerm swapG` and the uncompute leg is
    the basis permutation `gateToPerm (reverse mulInv)` — both `X/CX/CCX/seq` circuits,
    so the **`U_rev` isometry and swap-`=0` hypotheses are discharged automatically by
    `gate_normSqDist_perm`** (the classical Gate IR denotes basis permutations).  The
    total deviation is `2·numAdds·(2/2^m)` given the two per-leg coset bounds.

    DIMENSION: stated on `Fin (2^bits)` — the physical register — so `wrapShiftState`
    mod `dim = 2^bits` matches the real adder.  Remaining flagged bridge: identifying
    `permState (gateToPerm g)` with the literal `uc_eval (toUCom g)` matrix action
    (the funbool coordinatization), and the forward-leg deviation `hfwd` via the
    two-register factorization. -/
theorem inPlaceMul_coset_deviation_gates {bits : Nat}
    (U_fwd : QState (2 ^ bits) → QState (2 ^ bits)) (mulInv swapG : Gate)
    (hwt_inv : Gate.WellTyped bits mulInv) (hwt_swap : Gate.WellTyped bits swapG)
    (s_in I_fwd s_out : QState (2 ^ bits)) (numAdds m : Nat)
    (hfwd : normSqDist (U_fwd s_in) I_fwd ≤ (numAdds : ℝ) * (2 / 2 ^ m))
    (hrev : normSqDist
        (permState (gateToPerm (Gate.reverse mulInv) bits
            (reverse_wellTyped mulInv bits hwt_inv))
          (permState (gateToPerm swapG bits hwt_swap) I_fwd)) s_out
        ≤ (numAdds : ℝ) * (2 / 2 ^ m)) :
    normSqDist
        (permState (gateToPerm (Gate.reverse mulInv) bits
            (reverse_wellTyped mulInv bits hwt_inv))
          (permState (gateToPerm swapG bits hwt_swap) (U_fwd s_in))) s_out
      ≤ 2 * (numAdds : ℝ) * (2 / 2 ^ m) :=
  inPlaceMul_coset_deviation U_fwd
    (permState (gateToPerm (Gate.reverse mulInv) bits
      (reverse_wellTyped mulInv bits hwt_inv)))
    (gateToPerm swapG bits hwt_swap) s_in I_fwd s_out numAdds m
    (gate_normSqDist_perm (Gate.reverse mulInv) bits
      (reverse_wellTyped mulInv bits hwt_inv))
    hfwd hrev

/-- **DISCHARGED FOR THE LITERAL SQIR SEMANTICS.**  The strongest form: the swap and
    uncompute legs are the genuine SQIR unitary actions `uc_eval (toUCom ·) * ·` (not
    abstract permutations).  `UCEvalBridge.uc_eval_eq_permState` rewrites the swap leg
    to `permState (gateToPerm swapG).symm`, and `gate_uc_eval_normSqDist_perm`
    discharges the uncompute leg's isometry — so the bound `2·numAdds·(2/2^m)` holds
    for the actual `uc_eval` matrix semantics of the classical reversible circuits. -/
theorem inPlaceMul_coset_deviation_sqir {bits : Nat}
    (U_fwd : Matrix (Fin (2 ^ bits)) (Fin 1) ℂ → Matrix (Fin (2 ^ bits)) (Fin 1) ℂ)
    (mulInv swapG : Gate)
    (hwt_inv : Gate.WellTyped bits mulInv) (hwt_swap : Gate.WellTyped bits swapG)
    (s_in I_fwd s_out : Matrix (Fin (2 ^ bits)) (Fin 1) ℂ) (numAdds m : Nat)
    (hfwd : normSqDist (U_fwd s_in) I_fwd ≤ (numAdds : ℝ) * (2 / 2 ^ m))
    (hrev : normSqDist
        (Framework.uc_eval (Gate.toUCom bits (Gate.reverse mulInv)) *
          (Framework.uc_eval (Gate.toUCom bits swapG) * I_fwd)) s_out
        ≤ (numAdds : ℝ) * (2 / 2 ^ m)) :
    normSqDist
        (Framework.uc_eval (Gate.toUCom bits (Gate.reverse mulInv)) *
          (Framework.uc_eval (Gate.toUCom bits swapG) * (U_fwd s_in))) s_out
      ≤ 2 * (numAdds : ℝ) * (2 / 2 ^ m) := by
  rw [uc_eval_eq_permState swapG bits hwt_swap (U_fwd s_in)]
  rw [uc_eval_eq_permState swapG bits hwt_swap I_fwd] at hrev
  exact inPlaceMul_coset_deviation U_fwd
    (fun s : Matrix (Fin (2 ^ bits)) (Fin 1) ℂ =>
      Framework.uc_eval (Gate.toUCom bits (Gate.reverse mulInv)) * s)
    (gateToPerm swapG bits hwt_swap).symm s_in I_fwd s_out numAdds m
    (fun a b => gate_uc_eval_normSqDist_perm (Gate.reverse mulInv) bits
      (reverse_wellTyped mulInv bits hwt_inv) a b)
    hfwd hrev

end FormalRV.Shor.GidneyInPlace.InPlaceCoset
