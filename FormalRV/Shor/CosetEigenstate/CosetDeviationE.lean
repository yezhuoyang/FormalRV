/-
  FormalRV.Shor.CosetEigenstate.CosetDeviationE — the coset out-of-place deviation
  engine over an ARBITRARY product factorization (the `branchOfE` versions).
  ════════════════════════════════════════════════════════════════════════════

  `CosetMul.cosetMul_superposition_deviation` and `CosetTableSum.cosetOutOfPlace_hfwd`
  bound the windowed coset multiplier's Born-L1 deviation, but state the per-branch
  contract via `branchOf`/`jointIdx` (the contiguous control-high/data-low layout).
  A real circuit's accumulator sits at scattered qubit positions, so its natural
  factorization is an arbitrary product equiv `e : Fin m × Fin d ≃ Fin full`, NOT
  `jointIdx`.  These `…_E` versions restate the SAME bounds via `BranchFactor.branchOfE e`,
  so a concrete gate feeds them directly (the `jointIdx` versions are the
  `e := jointEquiv h` instance, via `branchOf_eq_branchOfE`).

  The proofs are byte-for-byte the originals with `branchOf h` → `branchOfE e`, the data
  dim `full/m` → the explicit `d`, and the sub-normalized lift swapped to its `branchOfE`
  counterpart — the deviation core `cosetMulOutOfPlace_deviation` is dim-generic and reused
  verbatim.

  This is what discharges `hfac_act` for the reduced-lookup coset gate (`cosetModMulCircuitOf`):
  feed `cosetOutOfPlace_hfwd_E` with the gate's qubit-block equiv and the per-branch QState
  coset-fold action, getting `cosetState(k) → cosetState((a·k) mod N)` off `numWin/2^m`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.BranchFactor
import FormalRV.Shor.CosetEigenstate.CosetTableSum

namespace FormalRV.Shor.CosetEigenstate.CosetDeviationE

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetEigenstate.ApproxOp (cosetState)
open FormalRV.Shor.CosetEigenstate.BranchFactor
  (branchOfE normSqDist_branchOfE_controlled_lift_subnormalized)
open FormalRV.Shor.CosetEigenstate.CosetMul (actualAcc idealAcc cosetMulOutOfPlace_deviation)
open FormalRV.Shor.CosetEigenstate.CosetTableSum
  (cosetWindowConst cosetWindowConst_lt idealAcc_cosetWindowConst)

/-- **Superposition deviation over an arbitrary product factorization.**  The
    `branchOfE e` version of `cosetMul_superposition_deviation`: in each control branch
    `x` the data substate (under `e`) runs the coset fold with addend sequence `cs x`;
    the sub-normalized controlled lift keeps the whole-register Born-L1 deviation at
    `≤ numAdds·(2/2^cm)`. -/
theorem cosetMul_superposition_deviation_E
    {m d full : Nat} (e : Fin m × Fin d ≃ Fin full)
    (s_act s_idl : QState full) (active : Finset (Fin m)) (β : Fin m → ℂ)
    (N cm k₀ numAdds : Nat) (cs : Fin m → Nat → Nat)
    (hN : 0 < N) (hk₀ : k₀ < N) (hcs : ∀ x t, cs x t < N)
    (hfit : N + 2 ^ cm * N ≤ d)
    (hzero : ∀ x, x ∉ active → branchOfE e s_act x = branchOfE e s_idl x)
    (hfac_act : ∀ x, x ∈ active →
        branchOfE e s_act x = fun i z => β x * actualAcc d N cm k₀ (cs x) numAdds i z)
    (hfac_idl : ∀ x, x ∈ active →
        branchOfE e s_idl x = fun i z => β x * cosetState d N cm (idealAcc N k₀ (cs x) numAdds) i z)
    (hweight : ∑ x ∈ active, Complex.normSq (β x) ≤ 1) :
    normSqDist s_act s_idl ≤ (numAdds : ℝ) * (2 / 2 ^ cm) := by
  refine normSqDist_branchOfE_controlled_lift_subnormalized e s_act s_idl active β
    ((numAdds : ℝ) * (2 / 2 ^ cm)) (by positivity)
    (fun x => actualAcc d N cm k₀ (cs x) numAdds)
    (fun x => cosetState d N cm (idealAcc N k₀ (cs x) numAdds))
    hzero hfac_act hfac_idl (fun x _ => ?_) hweight
  exact cosetMulOutOfPlace_deviation d N cm k₀ (cs x) hN hk₀ (hcs x) hfit numAdds

/-- **The `hfwd` deviation over an arbitrary product factorization.**  The `branchOfE e`
    version of `cosetOutOfPlace_hfwd`: if in each active control branch the gate's data
    substate (under `e`) is `β b ·` the coset fold of the reduced window constants
    `cosetWindowConst a N w (xval b)` (the `hfac_act` contract), and the ideal is
    `β b · cosetState ((a·xval b) mod N)`, then the Born-L1 deviation is `≤ numWin·(2/2^cm)`.
    The ideal residue is `(a·x) mod N` by the abstract table-sum `idealAcc_cosetWindowConst`. -/
theorem cosetOutOfPlace_hfwd_E {m d full : Nat} (e : Fin m × Fin d ≃ Fin full)
    (s_act s_idl : QState full) (active : Finset (Fin m)) (β : Fin m → ℂ)
    (a N cm w numWin : Nat) (xval : Fin m → Nat)
    (hN : 0 < N) (hxval : ∀ b, b ∈ active → xval b < (2 ^ w) ^ numWin)
    (hfit : N + 2 ^ cm * N ≤ d)
    (hzero : ∀ b, b ∉ active → branchOfE e s_act b = branchOfE e s_idl b)
    (hfac_act : ∀ b, b ∈ active → branchOfE e s_act b
        = fun i z => β b * actualAcc d N cm 0 (cosetWindowConst a N w (xval b)) numWin i z)
    (hfac_idl : ∀ b, b ∈ active → branchOfE e s_idl b
        = fun i z => β b * cosetState d N cm ((a * xval b) % N) i z)
    (hweight : ∑ b ∈ active, Complex.normSq (β b) ≤ 1) :
    normSqDist s_act s_idl ≤ (numWin : ℝ) * (2 / 2 ^ cm) := by
  refine cosetMul_superposition_deviation_E e s_act s_idl active β N cm 0 numWin
    (fun b => cosetWindowConst a N w (xval b)) hN hN
    (fun b t => cosetWindowConst_lt a N w (xval b) hN t) hfit hzero hfac_act ?_ hweight
  intro b hb
  rw [hfac_idl b hb]
  funext i z
  rw [idealAcc_cosetWindowConst a N w numWin (xval b) hN (hxval b hb)]

end FormalRV.Shor.CosetEigenstate.CosetDeviationE
