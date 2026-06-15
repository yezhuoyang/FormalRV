/-
  FormalRV.Arithmetic.MeasuredAdder.Example
  ──────────────────────────────────────────
  Concrete demonstration of the measured Gidney adder on a small case (width
  `n+2 = 4`).  We `#eval` the Toffoli counts (the HALF / DOUBLE headlines) and run
  the Boolean `EGate.applyNat` semantics on real inputs, decoding the target with
  `gidney_target_val` to see the faithful sum `(a + b) % 16` (uncontrolled) and the
  controlled sum `ctrl ? (a+b) : b`.  Everything here is `#eval` of verified,
  kernel-clean objects (no axioms, no `native_decide`).
-/
import FormalRV.Arithmetic.MeasuredAdder

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Arithmetic.MeasuredAdder

/-! ## §1. Toffoli counts — the HALF (E3) and DOUBLE (E4) headlines.

At width `n+2 = 4` (so `n = 2`):
  • uncontrolled measured adder = `4` Toffoli  (= width; the reversible adder is `8`),
  • controlled measured adder   = `8` Toffoli  (= `2·4`). -/
#eval IO.println s!"uncontrolled gidneyAdderMeasured 4 : toffoli = {EGate.toffoli (gidneyAdderMeasured 4 0)} (reversible would be 8; HALF)"
#eval IO.println s!"controlled   gidneyAdderMeasuredControlled 4 ctrl=14 : toffoli = {EGate.toffoli (gidneyAdderMeasuredControlled 4 0 14)} (= 2·4; DOUBLE)"

/-! ## §2. The uncontrolled adder computes the faithful sum `(a + b) % 16`.

Run `EGate.applyNat (gidneyAdderMeasured 4 0)` on the clean two-operand input
`adder_input_F 4 a b` and decode the target register with `gidney_target_val 4`. -/
private def runMeas (a b : Nat) : Nat :=
  gidney_target_val 4 (EGate.applyNat (gidneyAdderMeasured 4 0) (adder_input_F 4 a b))

/-- Carry register after the measured adder (should be all-zero = released). -/
private def carryAfter (a b : Nat) : Nat :=
  gidney_carry_val 4 (EGate.applyNat (gidneyAdderMeasured 4 0) (adder_input_F 4 a b))

#eval IO.println s!"a=3 b=5 : target decodes to {runMeas 3 5}  (expected (3+5)%16 = {(3+5) % 16}), carries released = {carryAfter 3 5}"
#eval IO.println s!"a=7 b=6 : target decodes to {runMeas 7 6}  (expected (7+6)%16 = {(7+6) % 16}), carries released = {carryAfter 7 6}"
#eval IO.println s!"a=9 b=9 : target decodes to {runMeas 9 9}  (expected (9+9)%16 = {(9+9) % 16} — wraps), carries released = {carryAfter 9 9}"

/-- Machine-checked: the measured adder really computes `(a+b) % 16` on this case
(the same fact as `gidneyAdderMeasured_target_val`, here `decide`d numerically). -/
example : runMeas 3 5 = 8 := by decide
example : runMeas 9 9 = 2 := by decide   -- 18 % 16 = 2
example : carryAfter 7 6 = 0 := by decide

/-! ## §3. The controlled adder gates the addend: `ctrl ? (a+b) : b`.

The control qubit sits at index `ctrl = adder_n_qubits 4 = 14`, the addend `a`
lives in the source register `srcA_idx 14 i = 15 + i`, and the accumulator `b`
sits in the adder block's target.  The classical control bit is `cval`. -/
private def runCtrl (a b ctrl cval : Nat) : Nat :=
  gidney_target_val 4
    (EGate.applyNat (gidneyAdderMeasuredControlled 4 0 ctrl) (ctrlAdder_input_F 4 a b ctrl cval))

#eval IO.println s!"controlled, cval=1 : a=3 b=5 → target {runCtrl 3 5 14 1} (expected a+b = {(3+5) % 16})"
#eval IO.println s!"controlled, cval=0 : a=3 b=5 → target {runCtrl 3 5 14 0} (expected b   = {5 % 16}, addend gated off)"

/-- Machine-checked controlled cases: `cval=1` adds, `cval=0` is the identity on `b`. -/
example : runCtrl 3 5 14 1 = 8 := by decide
example : runCtrl 3 5 14 0 = 5 := by decide
