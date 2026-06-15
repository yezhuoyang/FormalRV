/-
  FormalRV.Arithmetic.MeasuredAdder.MeasuredAdderResource
  ────────────────────────────────────────────────────────
  COUNT theorems for the measured Gidney adder family: the uncontrolled adder is
  `n` Toffoli (HALF the reversible adder) and the controlled adder is `2n` Toffoli
  (DOUBLE the uncontrolled).  Imports only the shared base `MeasuredAdderDef`;
  every proof here is byte-for-byte the one that used to live in
  `GidneyMeasured.lean` / `GidneyMeasuredControlled.lean`.

  The measurement-uncompute trick makes the reverse sweep Toffoli-free
  (`tcount_gidneyMeasFullReverse = 0`), so the uncontrolled adder's cost collapses
  to the forward sweep's `n` (`toffoli_gidneyAdderMeasured`), realising Cain–Xu's
  `n`-Toffoli-per-add adder and closing the factor-2 of the reversible version
  (`gidneyAdderMeasured_halves`).  A *controlled* add cannot measure away its addend
  gating, so the controlled core (`ctrlMaskRead`, `n` CCX) adds a genuine `n`
  Toffoli on top, giving `2n` (`toffoli_gidneyAdderMeasuredControlled`,
  `gidneyAdderMeasuredControlled_doubles`) — Cain–Xu's E3 → E4 jump.

  Refs: Gidney arXiv:1709.06648 (temporary AND); Cain–Xu 2026 (E3 n / E4 2n).
-/
import FormalRV.Arithmetic.MeasuredAdder.MeasuredAdderDef

namespace FormalRV.Arithmetic.MeasuredAdder

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute

/-! ## §1. Count (uncontrolled): `n` Toffoli — final-CX and the measured reverse are Toffoli-free. -/

/-- **Toffoli count of the measured adder is exactly the forward sweep's `n`** (here
`n+2` at width `n+2`): the final-CX cascade and the measured reverse cascade
contribute `0`.  Derived from `tcount_gidney_adder_forward_faithful_full`
(`7·(n+2)` T = `(n+2)` Toffolis), `tcount_gidney_final_cx_cascade = 0`, and
`tcount_gidneyMeasFullReverse = 0`. -/
theorem toffoli_gidneyAdderMeasured (n q_start : Nat) :
    EGate.toffoli (gidneyAdderMeasured (n + 2) q_start) = n + 2 := by
  unfold EGate.toffoli gidneyAdderMeasured
  simp only [EGate.tcount, Gate.tcount, tcount_gidneyMeasFullReverse, Nat.add_zero,
             tcount_gidney_adder_forward_faithful_full, tcount_gidney_final_cx_cascade]
  rw [Nat.mul_div_cancel_left _ (by norm_num)]

/-- **★ HEADLINE — the measurement-uncompute HALVES the adder Toffoli count.**  The
measured Gidney adder costs exactly HALF the Toffolis of the reversible faithful
`gidney_adder_full_faithful_no_measurement` (`n+2` vs `2·(n+2)`) — the verified
statement that Gidney's measurement-based carry-uncompute realises Cain–Xu's
`n`-Toffoli-per-add adder, closing the factor-2 of the reversible version, while
STILL computing the FAITHFUL sum `(a+b) % 2^bits` (`gidneyAdderMeasured_correct`). -/
theorem gidneyAdderMeasured_halves (n q_start : Nat) :
    EGate.toffoli (gidneyAdderMeasured (n + 2) q_start)
      = tcount (gidney_adder_full_faithful_no_measurement (n + 2)) / 7 / 2 := by
  rw [toffoli_gidneyAdderMeasured, tcount_gidney_adder_full_faithful_no_measurement,
      show 14 * (n + 2) = (n + 2) * 2 * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num), Nat.mul_div_cancel _ (by norm_num)]

/-! ## §2. Count (controlled): `2·(n+2)` Toffoli — controlled core `n` + measured add `n`. -/

/-- **Toffoli count of the controlled measured adder is exactly `2·(n+2)`** at
width `n+2`: the controlled mask contributes `n+2` (one CCX per addend bit) and
the reused measured adder contributes `n+2`; their sum is `2·(n+2)`.  This is the
verified `E3 (n) → E4 (2n)` jump: the control DOUBLES the adder Toffoli cost vs the
uncontrolled measured adder `gidneyAdderMeasured` (`toffoli_gidneyAdderMeasured`). -/
theorem toffoli_gidneyAdderMeasuredControlled (n q_start ctrl : Nat) :
    EGate.toffoli (gidneyAdderMeasuredControlled (n + 2) q_start ctrl) = 2 * (n + 2) := by
  have hadd : EGate.tcount (gidneyAdderMeasured (n + 2) q_start) = 7 * (n + 2) := by
    show EGate.tcount
      (EGate.seq
        (EGate.base (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                              (gidney_final_cx_cascade (n + 2))))
        (gidneyMeasFullReverse (n + 2))) = 7 * (n + 2)
    simp only [EGate.tcount, Gate.tcount, tcount_gidneyMeasFullReverse, Nat.add_zero,
               tcount_gidney_adder_forward_faithful_full, tcount_gidney_final_cx_cascade]
  unfold EGate.toffoli gidneyAdderMeasuredControlled
  simp only [EGate.tcount, tcount_ctrlMaskRead, hadd]
  rw [show 7 * (n + 2) + 7 * (n + 2) = 2 * (n + 2) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **★ The control DOUBLES the measured-adder Toffoli count (E3 → E4).**  The
controlled measured adder costs exactly TWICE the uncontrolled measured Gidney
adder `gidneyAdderMeasured` — Cain–Xu's `30 q_A = 2·q_A` (E4) vs `25 q_A = q_A`
(E3) controlled-adder factor-2, on verified objects. -/
theorem gidneyAdderMeasuredControlled_doubles (n q_start ctrl : Nat) :
    EGate.toffoli (gidneyAdderMeasuredControlled (n + 2) q_start ctrl)
      = 2 * EGate.toffoli (gidneyAdderMeasured (n + 2) q_start) := by
  rw [toffoli_gidneyAdderMeasuredControlled, toffoli_gidneyAdderMeasured]

end FormalRV.Arithmetic.MeasuredAdder
