/-
  FormalRV.Shor.CosetEigenstate.InPlaceCosetClearing — CHECKPOINT 3 of the in-place phase:
  the swap + second-forward-pass two-register transform (the clearing).
  ════════════════════════════════════════════════════════════════════════════

  Clones the PROVEN `windowedModNMulInPlace_correct` (WindowedModNInPlace.lean:224) at the
  COSET (runway, no-flag) level.  The in-place gate is

      inplaceCosetGate = mulFwd(a) ; accYSwap ; mulFwd(N − aInv)

  and checkpoint 3 proves the accumulator CLEARS to the coset of `0` while the y-register
  holds the coset of `(a·y) mod N`, off the phase-independent wrap bad set.

  KEY ENABLER (this file's brick 1): `cosetModMulCircuitOf cuccaroAdder w bits N c numWin`
  is DEFEQ to the table-generic `windowedMulTOf cuccaroAdder w bits (tableValue c N w) …`
  (`reducedWindowStepOf` and `windowStepTOf` have byte-identical bodies), so the VERIFIED
  accumulator-agnostic basis fold `stepInv_foldT_acc` applies to BOTH forward passes with
  ZERO new fold induction.  It tracks the UNREDUCED runway sum `acc₀ + ∑ tableValue`
  (no modular flag) — exactly the coset behavior.

  THE CLEARING (for every runway term, confirmed):  a `StepInv` term at `acc₀ = j·N`
  advances under pass 1 to `j·N + Sa` (`Sa = ∑ tableValue a`, `≡ a·y mod N`); the swap puts
  this in the y-register and `y` in the accumulator; pass 2 adds `Sb = ∑ tableValue (N−aInv)`
  reading the swapped multiplicand `V ≡ a·y (mod N)`, giving accumulator `y + Sb ≡
  y − aInv·(a·y) − aInv·(j·N) ≡ 0 (mod N)` — since `acc₀ = j·N ≡ 0 (mod N)`, EVERY runway
  term clears to a coset-0 point.  Honest deviation: forward-wrap ∪ reverse-wrap,
  `≤ 2·numWin/2^cm` (the swap contributes 0 by `normSqDist_perm_invariant`).

  STATUS: brick 1 (this file) — the reusable coset basis fold.  Remaining bricks (next):
  per-runway-term basis in-place action (clone of the template via `stepInv_init_acc` +
  brick 1 + `accYSwap_apply` + `stepInv_determines_mulInputAccOf` + the windowed value
  identity for the clearing); then the `cosetState`/`cosetInput` superposition lift
  (`uc_eval_eq_permState` + branch classification) + the bad-set transport through
  `accYSwap` (OBLIGATION (b), phase-independent).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.InPlaceCosetGate
import FormalRV.Shor.CosetEigenstate.InPlaceCosetForward

namespace FormalRV.Shor.CosetEigenstate.InPlaceCosetClearing

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit (StepInv stepInv_foldT_acc)
open FormalRV.Shor.WindowedArith (tableValue window)
open FormalRV.Shor.CosetEigenstate.ReducedLookupCosetGate (cosetModMulCircuitOf)

/-- **CHECKPOINT 3, brick 1 — the coset multiplier's basis fold (reusable, BOTH passes).**
    A `StepInv` state at partial sum `acc₀` advances under the whole forward coset
    multiplier `cosetModMulCircuitOf … c` to `StepInv` at `acc₀ + ∑ tableValue c` — the
    UNREDUCED runway sum.  Direct application of the verified accumulator-agnostic
    `stepInv_foldT_acc` through the `cosetModMulCircuitOf = windowedMulTOf (tableValue c N w)`
    defeq.  This is the per-pass engine of the clearing (pass 1 at constant `a`, pass 2 at
    `N − aInv`). -/
theorem cosetMul_stepInv_fold (w bits N c numWin y acc₀ : Nat) (hw : 0 < w)
    (f : Nat → Bool) (hf : StepInv cuccaroAdder w bits numWin y acc₀ f) :
    StepInv cuccaroAdder w bits numWin y
        (acc₀ + ∑ k ∈ Finset.range numWin, tableValue c N w k (window w y k))
        (Gate.applyNat (cosetModMulCircuitOf cuccaroAdder w bits N c numWin) f) :=
  stepInv_foldT_acc cuccaroAdder w bits (tableValue c N w) numWin y acc₀ hw f hf
    numWin (le_refl numWin)

end FormalRV.Shor.CosetEigenstate.InPlaceCosetClearing
