/-
  FormalRV.Shor.CosetEigenstate.ReducedLookupCosetValue — VALUE-correctness of the
  reduced-lookup coset multiplier gate `cosetModMulCircuitOf`.
  ════════════════════════════════════════════════════════════════════════════

  The concrete reduced-lookup coset gate (`ReducedLookupCosetGate.cosetModMulCircuitOf`,
  windowed multiply-accumulate with the mod-N-REDUCED table `tableValue a N w`) computes,
  on the clean encoded input, the **windowed reduced fold** — and that fold is `≡ a·y mod N`,
  with the input runway forgotten (`r·N ≡ 0`).  This is the Boolean-level half of the
  runway-preserving coset oracle's correctness.

  Because the windowed value proof is now TABLE-GENERIC (`WindowedCircuitCorrect.stepInv_foldT`)
  and `cosetModMulCircuitOf` is DEFINITIONALLY the `Tfam := tableValue a N w` instance of
  `windowedMulTOf`, Theorem 1 is a one-line `stepInv_foldT` application.  The residue
  (Theorem 2) reduces the plain fold mod `N` to `idealAcc` (the mod-N running sum) via the
  general bridge `idealAcc_eq_sum_mod`, then invokes the already-proven abstract table-sum
  `CosetTableSum.idealAcc_cosetWindowConst = (a·y) mod N`.

    * `reducedCosetMul_decodeAcc_cuccaro` — `decodeAcc = (∑ₖ tableValue a N w k (windowₖ y)) mod 2^bits`.
    * `idealAcc_eq_sum_mod` — `idealAcc N 0 cs t = (∑_{k<t} cs k) mod N` (general).
    * `reducedCosetMul_residue` — `(∑ₖ tableValue a N w k (windowₖ y)) mod N = (a·y) mod N`.
    * `reducedCosetMul_decodeAcc_residue_cuccaro` — combined, under the runway-fit `fold < 2^bits`:
      `decodeAcc mod N = (a·y) mod N` (no `2^bits` wrap).

  WHAT REMAINS (the coset-state lift, next phase).  This is the BOOLEAN (register-value)
  correctness.  Lifting it to the QState coset-state shift `cosetState(k) → cosetState((a·k) mod N)`
  off the `numWin/2^m` boundary — i.e. discharging `CosetTableSum.cosetOutOfPlace_hfwd`'s
  per-branch `hfac_act` contract (`branchOf = actualAcc` coset fold) for this concrete gate —
  is the follow-up.  The runway-fit `hfit` here is the Boolean shadow of that bounded growth.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
  De-risked via 3 parallel verified attempts.
-/
import FormalRV.Shor.CosetEigenstate.ReducedLookupCosetGate
import FormalRV.Shor.CosetEigenstate.CosetTableSum

open scoped BigOperators

namespace FormalRV.Shor.CosetEigenstate.ReducedLookupCosetValue

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
  (decodeAccOf mulInputOf mulInputOf_low stepInv_foldT windowedMulTOf)
open FormalRV.Shor.WindowedArith (tableValue window)
open FormalRV.Shor.CosetEigenstate.ReducedLookupCosetGate
  (cosetModMulCircuitOf reducedWindowedMulOf)
open FormalRV.Shor.CosetEigenstate.CosetTableSum
  (cosetWindowConst idealAcc_cosetWindowConst)
open FormalRV.Shor.CosetEigenstate.CosetMul (idealAcc)

/-! ## Theorem 1 — the reduced coset gate computes the windowed reduced fold.

`cosetModMulCircuitOf cuccaroAdder w bits N a numWin` is DEFINITIONALLY
`windowedMulTOf cuccaroAdder w bits (tableValue a N w) bits (1+2w) (1+2w+span) numWin`
(via `reducedWindowedMulOf = foldl = windowedMulTOf` and `reducedWindowStepOf = windowStepTOf`
at the reduced table), and `decodeAccOf` is defeq `decodeReg (·.augendIdx …)`.  So the (V)
conjunct of `stepInv_foldT` at `Tfam := tableValue a N w` closes the goal by `exact`. -/
theorem reducedCosetMul_decodeAcc_cuccaro (w bits N a numWin y : Nat) (hw : 0 < w) :
    decodeAccOf cuccaroAdder
        (Gate.applyNat (cosetModMulCircuitOf cuccaroAdder w bits N a numWin)
          (mulInputOf cuccaroAdder w bits numWin y)) (1 + 2 * w) bits
      = (∑ k ∈ Finset.range numWin, tableValue a N w k (WindowedArith.window w y k)) % 2 ^ bits := by
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  have hclean : cuccaroAdder.ancClean (mulInputOf cuccaroAdder w bits numWin y) bits (1 + 2 * w) := by
    show mulInputOf cuccaroAdder w bits numWin y (1 + 2 * w) = false
    exact mulInputOf_low cuccaroAdder w bits numWin y _ (by unfold ulookup_ctrl_idx; omega)
      (by rw [hspan]; omega)
  have hfold := (stepInv_foldT cuccaroAdder w bits (tableValue a N w)
    numWin y hw hclean numWin (le_refl numWin)).2.2.2
  exact hfold

/-! ## Bridge: the mod-N running accumulator equals the plain sum reduced mod N. -/

/-- **`idealAcc` is the plain sum reduced mod `N`.**  The mod-N running accumulator
    `idealAcc N 0 cs t` (each step `(acc + cs k) % N`) equals `(∑_{k<t} cs k) % N`.
    General over `cs`; the inductive step is `Nat.add_mod` collapsing the inner `% N`. -/
theorem idealAcc_eq_sum_mod (N : Nat) (cs : Nat → Nat) :
    ∀ t, idealAcc N 0 cs t = (∑ k ∈ Finset.range t, cs k) % N := by
  intro t
  induction t with
  | zero => simp [idealAcc, Nat.zero_mod]
  | succ n ih =>
      show (idealAcc N 0 cs n + cs n) % N = (∑ k ∈ Finset.range (n + 1), cs k) % N
      rw [ih, Finset.sum_range_succ, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-! ## Theorem 2 — the windowed reduced fold is `≡ a·y mod N` (input runway forgotten). -/

/-- **Residue correctness.**  The windowed reduced-lookup fold reduces mod `N` to `(a·y) mod N`:
    `(∑ₖ tableValue a N w k (windowₖ y)) mod N = (a·y) mod N`.  The per-window addends are the
    reduced `cosetWindowConst`; their mod-N sum is the abstract `idealAcc`, which
    `idealAcc_cosetWindowConst` evaluates to `(a·y) mod N`. -/
theorem reducedCosetMul_residue (w N a numWin y : Nat) (hN : 0 < N) (hy : y < (2 ^ w) ^ numWin) :
    (∑ k ∈ Finset.range numWin, tableValue a N w k (WindowedArith.window w y k)) % N = (a * y) % N := by
  have hcs : (∑ k ∈ Finset.range numWin, tableValue a N w k (WindowedArith.window w y k))
      = ∑ k ∈ Finset.range numWin, cosetWindowConst a N w y k := by
    apply Finset.sum_congr rfl
    intro k _
    rfl
  rw [hcs, ← idealAcc_eq_sum_mod N (cosetWindowConst a N w y) numWin,
      idealAcc_cosetWindowConst a N w numWin y hN hy]

/-! ## Theorem 3 — combined residue-value form (no `2^bits` wrap). -/

/-- **Residue value of the gate, under the runway-fit.**  When the fold fits the register
    (`fold < 2^bits`, i.e. the runway has not overflowed), the accumulator's residue is
    exactly `(a·y) mod N`.  Chains Theorem 1, `Nat.mod_eq_of_lt`, Theorem 2. -/
theorem reducedCosetMul_decodeAcc_residue_cuccaro
    (w bits N a numWin y : Nat) (hw : 0 < w) (hN : 0 < N) (hy : y < (2 ^ w) ^ numWin)
    (hfit : (∑ k ∈ Finset.range numWin, tableValue a N w k (WindowedArith.window w y k)) < 2 ^ bits) :
    decodeAccOf cuccaroAdder
        (Gate.applyNat (cosetModMulCircuitOf cuccaroAdder w bits N a numWin)
          (mulInputOf cuccaroAdder w bits numWin y)) (1 + 2 * w) bits % N
      = (a * y) % N := by
  rw [reducedCosetMul_decodeAcc_cuccaro w bits N a numWin y hw, Nat.mod_eq_of_lt hfit,
      reducedCosetMul_residue w N a numWin y hN hy]

end FormalRV.Shor.CosetEigenstate.ReducedLookupCosetValue
