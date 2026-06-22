/-
  FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderCostSkeleton
  ─────────────────────────────────────────────────────────────────
  ⚠️ A deliberately-WRONG "cost-only skeleton" Gidney adder family.
  **Definitions only — no proofs.**

  This family has the right Toffoli / T-count but the WRONG logical action:
  for `i > 0` the per-bit step omits the carry-propagation CXs, so it does not
  compute Gidney's carry. It is kept ONLY for T-count accounting — its cost
  provably equals the correct faithful adder's (`gidney_cost_skeleton_eq_faithful`
  in `RippleCarryAdderForwardAndCost.lean`), and the factor-of-2 no-measurement
  vs. measurement gap is stated against it (`gidney_no_measurement_vs_measurement_gap`).

  For the semantically-correct adder use `gidney_adder` /
  `gidney_adder_full_faithful_no_measurement` in `RippleCarryAdderDef.lean`.
  Do NOT build on anything in this file.
-/
import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Framework.PaperClaims
import FormalRV.PPM.Magic.GidneyAND
import Mathlib.Tactic.IntervalCases
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderDef

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-- ⚠️ COST-ONLY SKELETON per-bit step: right Toffoli count, wrong carry (omits
the propagation CXs). Correct version: `gidney_adder_bit_step_faithful_*`. -/
def gidney_adder_bit_step (i : Nat) : Gate :=
  if i = 0 then
    Gate.CCX (read_idx 0) (target_idx 0) (carry_idx 0)
  else
    Gate.seq
      (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))
      (Gate.CX (carry_idx (i - 1)) (carry_idx i))

/-- ⚠️ COST-ONLY SKELETON gate-reverse of `gidney_adder_bit_step` (`CX; CCX`
at `i > 0`); the per-bit inverse used by the proper-reverse cascade. -/
def gidney_adder_bit_step_reverse (i : Nat) : Gate :=
  if i = 0 then
    Gate.CCX (read_idx 0) (target_idx 0) (carry_idx 0)
  else
    Gate.seq
      (Gate.CX (carry_idx (i - 1)) (carry_idx i))
      (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))

/-- ⚠️ COST-ONLY SKELETON forward pass. Use `gidney_adder_forward_faithful_full`. -/
def gidney_adder_forward : Nat → Gate
  | 0       => Gate.I
  | n + 1   => Gate.seq (gidney_adder_forward n) (gidney_adder_bit_step n)

/-- ⚠️ COST-ONLY SKELETON reverse pass: forward bit-steps in reverse bit order
(right `7n` Toffoli count, but not a true gate-level inverse of the forward). -/
def gidney_adder_uncompute : Nat → Gate
  | 0       => Gate.I
  | n + 1   => Gate.seq (gidney_adder_bit_step n) (gidney_adder_uncompute n)

/-- ⚠️ COST-ONLY SKELETON proper reverse cascade: the true gate-by-gate inverse
of `gidney_adder_forward`, built from `gidney_adder_bit_step_reverse`. -/
def gidney_adder_uncompute_proper : Nat → Gate
  | 0       => Gate.I
  | n + 1   => Gate.seq (gidney_adder_bit_step_reverse n)
                        (gidney_adder_uncompute_proper n)

/-- ⚠️ COST-ONLY SKELETON full adder (forward + reverse + final CX). Its T-count
`14n` is valid (and is what the measurement-gap theorem uses); it is NOT
semantically correct. -/
def gidney_adder_full (n : Nat) : Gate :=
  Gate.seq (Gate.seq (gidney_adder_forward n) (gidney_adder_uncompute n))
           (gidney_final_cx_cascade n)

/-- Per-bit Gidney adder T-count WITH measurement-based uncomputation = 7. -/
def gidney_adder_bit_with_measurement_uncompute_tcount : Nat := 7

/-- n-bit Gidney adder T-count with measurement-based uncomputation: `7n` (one
Gidney-AND cycle per bit; matches qianxu Eq. E3). -/
def gidney_adder_full_with_measurement_uncompute_tcount (n : Nat) : Nat :=
  gidney_adder_bit_with_measurement_uncompute_tcount * n

end FormalRV.BQAlgo
