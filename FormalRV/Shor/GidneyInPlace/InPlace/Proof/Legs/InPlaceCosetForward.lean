/-
  FormalRV.Shor.GidneyInPlace.InPlaceCosetForward — CHECKPOINT 2 of the in-place phase:
  the FORWARD leg only (transport/reuse from the verified out-of-place multiplier).
  ════════════════════════════════════════════════════════════════════════════

  Strictly scoped to the FORWARD leg of `inplaceCosetGate`.  By `inplaceCosetGate_unfold`,

      inplaceCosetGate w bits N a aInv numWin
        = Gate.seq (cosetModMulCircuitOf cuccaroAdder w bits N a numWin)   -- ← THIS leg
            (Gate.seq (accYSwap cuccaroAdder w bits)
              (Gate.reverse (cosetModMulCircuitOf cuccaroAdder w bits N aInv numWin)))

  so the first thing the in-place gate applies is exactly the VERIFIED out-of-place
  reduced-lookup multiplier `cosetModMulCircuitOf … a`.  This file transports the
  already-proven out-of-place theorems to characterise the state ENTERING the swap.

  WHAT IS PROVEN HERE (pure reuse — no new arithmetic):
    * `inplaceCosetGate_forward_state` — EXACT: on the coset-zero-accumulator input
      `cosetInput … 0 y`, the forward leg produces `cosetInput … (runningSum …) y`
      (accumulator advanced to the running sum of the reduced table = the coset of `a·y`).
      This is the state that enters `accYSwap`.  (= `reducedWindowedMul_cosetInput`.)
    * `inplaceCosetGate_forward_deviation` — its distance to the IDEAL canonical-`mod N`
      target `cosetInput … ((a*y)%N) y` is `≤ numWin·(2/2^cm)` (the runway-wrap gap).
      (= `reducedLookupWindowedMul_cosetState_shift`, the form named in review.)

  WHAT IS **NOT** PROVEN HERE (deliberately — these are checkpoint 3):
    * that the second (accumulator) register CLEARS after `accYSwap ; reverse(mulFwd aInv)`
      — that is the hard `inplaceCosetGate_hchain` un-compute (checkpoint 3);
    * the swap action, the `a⁻¹` reverse leg, the in-place row form, or anything lemma-5.

  No NEW bad set is introduced: the `runningSum`-vs-`(a·y)%N` gap quantified by
  `inplaceCosetGate_forward_deviation` IS the same forward-leg runway-wrap boundary of the
  out-of-place result; checkpoint 3 must carry exactly THIS set through `accYSwap`
  (phase-independently), not invent a new one.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Def.InPlaceCosetGate
import FormalRV.Shor.GidneyInPlace.ReducedLookup.Spec.ReducedLookupCosetShift

namespace FormalRV.Shor.GidneyInPlace.InPlaceCosetForward

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer (normSqDist)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetModMulCircuitOf cosetDim)
open FormalRV.Shor.GidneyInPlace.ReducedLookupEgate (cosetInput)
open FormalRV.Shor.GidneyInPlace.CosetMul (runningSum)
open FormalRV.Shor.GidneyInPlace.CosetTableSum (cosetWindowConst)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetShift
  (reducedWindowedMul_cosetInput reducedLookupWindowedMul_cosetState_shift)

/-- **CHECKPOINT 2 — the forward leg, EXACT (transport).**  The forward leg of
    `inplaceCosetGate` (= `cosetModMulCircuitOf cuccaroAdder w bits N a numWin`, the first
    `Gate.seq` component by `InPlaceCosetGate.inplaceCosetGate_unfold`) carries the
    coset-zero-accumulator input `cosetInput … 0 y` to the two-register coset state with
    the accumulator advanced to `runningSum (cosetWindowConst a N w y) numWin` (the coset
    of `a·y`).  This is the state entering `accYSwap`.  Direct reuse of the verified
    out-of-place `reducedWindowedMul_cosetInput`: layout (`q_start = 1+2w`,
    `yBase = 1+2w+span bits`), accumulator-zero input, constants, and dimension
    `cosetDim w bits` all match by definition. -/
theorem inplaceCosetGate_forward_state (w bits N a numWin y cm : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hfitAll : runningSum (cosetWindowConst a N w y) numWin + (2 ^ cm - 1) * N < 2 ^ bits) :
    (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (cosetModMulCircuitOf cuccaroAdder w bits N a numWin))
      * (id (cosetInput w bits numWin N cm 0 y) :
          Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ))
      = cosetInput w bits numWin N cm (runningSum (cosetWindowConst a N w y) numWin) y :=
  reducedWindowedMul_cosetInput w bits N a numWin y cm hw hbits hN hfitAll

/-- **CHECKPOINT 2 — the forward leg, deviation to the canonical `mod N` target
    (transport).**  The exact forward-leg state `cosetInput … (runningSum …) y` differs
    from the IDEAL canonical target `cosetInput … ((a*y)%N) y` by `normSqDist ≤
    numWin·(2/2^cm)` — the runway-wrap boundary.  This is the SAME forward-leg bad set
    checkpoint 3 must carry through the swap; no new set is introduced here.  Direct reuse
    of `reducedLookupWindowedMul_cosetState_shift`. -/
theorem inplaceCosetGate_forward_deviation (w bits N a numWin y cm : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hy : y < (2 ^ w) ^ numWin) (hfit_engine : N + 2 ^ cm * N ≤ 2 ^ bits)
    (hfitAll : runningSum (cosetWindowConst a N w y) numWin + (2 ^ cm - 1) * N < 2 ^ bits) :
    normSqDist
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (cosetModMulCircuitOf cuccaroAdder w bits N a numWin))
          * (id (cosetInput w bits numWin N cm 0 y) :
              Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ))
        (cosetInput w bits numWin N cm ((a * y) % N) y)
      ≤ (numWin : ℝ) * (2 / 2 ^ cm) :=
  reducedLookupWindowedMul_cosetState_shift w bits N a numWin y cm hw hbits hN hy hfit_engine
    hfitAll

end FormalRV.Shor.GidneyInPlace.InPlaceCosetForward
