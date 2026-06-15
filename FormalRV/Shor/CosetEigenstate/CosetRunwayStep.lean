/-
  FormalRV.Shor.CosetEigenstate.CosetRunwayStep — the concrete NON-MODULAR runway
  add-constant step: wrapping = ordinary addition on the reachable coset support.
  ════════════════════════════════════════════════════════════════════════════

  The concrete coset multiplier's per-window operation is an ORDINARY (non-modular)
  add-constant on the scratch register, realized by the Cuccaro wrapping
  add-constant gate `cuccaro_addConstGate` whose decoded target satisfies
  `cuccaro_target_val (…) = (x + c) % 2^bits` (`cuccaro_addConstGate_target_decode`,
  proven).  This file proves the GATE-LEVEL analogue of
  `ApproxOp.shiftState_eq_wrapState_on_coset`: under the running-fit / no-wrap
  condition `x + c < 2^bits`, the wrapping add computes the ORDINARY sum `x + c` —
  the wrap never fires on the reachable coset support, so the runway add behaves as
  exact addition.

  This is the atomic step of the windowed coset fold (`Part 2` of the runway
  multiplier construction): each controlled `tableValue`-add advances the scratch by
  one ordinary addition while the running fit holds, and the deviation is paid only
  when the fit is violated (the wrap set of the sound marginal route).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroAddConst

namespace FormalRV.Shor.CosetEigenstate.CosetRunwayStep

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-- **Wrapping = ordinary addition on the reachable coset support (single step).**
    The non-modular (wrapping mod `2^bits`) Cuccaro add-constant gate computes the
    ORDINARY sum `x + c` whenever the result does not overflow the register
    (`x + c < 2^bits` — the running-fit / no-wrap condition).  Concrete gate-level
    analogue of `ApproxOp.shiftState_eq_wrapState_on_coset`: under the fit, the wrap
    never fires, so the runway add is exact addition. -/
theorem cuccaro_addConst_noWrap (bits q_start c x : Nat) (hc : c < 2 ^ bits)
    (hfit : x + c < 2 ^ bits) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (cuccaro_addConstGate bits q_start c)
          (cuccaro_input_F q_start false 0 x))
      = x + c := by
  rw [cuccaro_addConstGate_target_decode bits q_start c x hc, Nat.mod_eq_of_lt hfit]

end FormalRV.Shor.CosetEigenstate.CosetRunwayStep
