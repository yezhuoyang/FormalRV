/-
  FormalRV.Framework.Contracts — inter-layer contract theorems.

  Phase A.5 of the paper plan (`PAPER_PLAN.md`). The four-layer
  software stack is glued together by three contracts (paper §2):

      L4 → L3 : cycle_logical_error_rate ≤ f_code (p_g) d
      L3 → L2 : per_op_error ≤ c · cycle_logical_error_rate
      L2 → L1 : gadget-by-gadget semantic correctness + T-count

  This tick states ONLY the first contract as a sorry-stubbed
  theorem and defines its left-hand-side stub. The remaining two
  contracts are future ticks. The proof body is `sorry` because
  the actual error-rate model (surface-code analytic ansatz vs.
  qLDPC numerical fit) will be supplied per-code by Phase-C corpus
  files; the contract statement freezes the L4→L3 interface so
  every L4 code instance in `Phase B/C` ships with a proof
  obligation of this exact shape.

  Hardware-parameters bundle lives in `HardwareParams.lean`
  (separate tick); this file imports it.
-/

import FormalRV.Framework.L4_QECCode
import FormalRV.Framework.L3_PPM

namespace FormalRV.Framework

/-- Placeholder hardware-parameter bundle used by the L4→L3 contract
until `HardwareParams.lean` lands in a later tick. -/
structure HardwareParamsStub where
  /-- Two-qubit physical gate-error probability in 1/1000 units. -/
  p_g_thousandths : Nat
  deriving Inhabited

/-- The cycle-level logical-error rate of a QEC code on given hardware.
Placeholder: returns `hw.p_g_thousandths` directly (a trivial upper
bound, true for `d = 1`).  A later tick refines per-code using the
analytic surface-code ansatz or qLDPC numerical fit. -/
def cycle_logical_error_rate (qec : QECCode) (hw : HardwareParamsStub) : Nat :=
  let _ := qec
  hw.p_g_thousandths

/-- L4 → L3 contract: the per-cycle logical error rate of any QEC code on
any hardware is bounded by the code's subthreshold ansatz `f_code`
evaluated at the hardware's physical gate-error rate and the code's
distance.

Trivially holds for the current stub definitions (both sides reduce
to `hw.p_g_thousandths`).  This proof will need to be re-derived when
`cycle_logical_error_rate` becomes a real per-code model and `f_code`
becomes the genuine `a · (p_g / p_star)^{(d+1)/2}` ansatz. -/
theorem L4_to_L3_contract (qec : QECCode) (hw : HardwareParamsStub) :
    cycle_logical_error_rate qec hw ≤ f_code hw.p_g_thousandths qec.d := by
  unfold cycle_logical_error_rate f_code
  exact Nat.le_refl _

end FormalRV.Framework
