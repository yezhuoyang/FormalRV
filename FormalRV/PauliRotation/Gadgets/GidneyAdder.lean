/-
  FormalRV.PauliRotation.Gadgets.GidneyAdder
  ──────────────────────────────────────────
  THE (PATCHED) GIDNEY RIPPLE-CARRY ADDER, compiled to Pauli rotations
  (`GateBridge.lean`): the canonical faithful no-measurement adder
  (`gidney_adder`, T-count `14·(n+2)`), the carry-clean PATCHED variant the
  modular-adder layer builds on, and the forward-faithful reverse-patched
  composition (`7·(n+2)`).

  HONESTY: the COST-ONLY skeleton gates of `RippleCarryAdderCostSkeleton.lean`
  are deliberately NOT compiled here — they have the right T-count but the
  wrong carry logic (their own header says so); only the faithful gadgets
  get rotation programs.  Correctness = the optimizer leg (see
  `PauliRotation/README.md`).
-/
import FormalRV.PauliRotation.Compiler.GateBridge
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderResource
import FormalRV.Arithmetic.ModularAdder.Gidney.TimeCount

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource
open FormalRV.BQAlgo

/-! ## §1. The canonical faithful adder. -/

/-- The faithful no-measurement Gidney adder as a rotation program. -/
def gidneyRot (n : Nat) : RotProg := gateRotSchedule (gidney_adder n)

/-- **Rotation T-count = `14·(n+2)`** (the family's `n ≥ 2` shape). -/
theorem gidneyRot_countPi8 (n : Nat) :
    countPi8 (gidneyRot (n + 2)) = 14 * (n + 2) := by
  rw [gidneyRot, gateRotSchedule_countPi8, gidney_adder_tcount]

/-- Correctness instance (the 2-bit faithful adder). -/
theorem gidneyRot_denote_2 :
    RotProg.denote (width (gidney_adder 2)) (gidneyRot 2)
      = seqDenote _ (gateRots (gidney_adder 2)) :=
  gateRotSchedule_denote _ _ (by decide) (Nat.le_refl _)

/-! ## §2. The carry-clean PATCHED adder (what `ModularAdder/Gidney` uses). -/

/-- The patched (carry-clearing) adder as a rotation program. -/
def gidneyPatchedRot (n : Nat) : RotProg :=
  gateRotSchedule (gidney_adder_full_faithful_no_measurement_patched n)

theorem gidneyPatchedRot_countPi8 (n : Nat) :
    countPi8 (gidneyPatchedRot (n + 2)) = 14 * (n + 2) := by
  rw [gidneyPatchedRot, gateRotSchedule_countPi8,
      tcount_gidney_adder_full_faithful_no_measurement_patched]

theorem gidneyPatchedRot_denote_2 :
    RotProg.denote (width (gidney_adder_full_faithful_no_measurement_patched 2))
        (gidneyPatchedRot 2)
      = seqDenote _ (gateRots (gidney_adder_full_faithful_no_measurement_patched 2)) :=
  gateRotSchedule_denote _ _ (by decide) (Nat.le_refl _)

/-! ## §3. The forward-faithful reverse-patched composition. -/

/-- The forward + patched-reverse composition as a rotation program. -/
def gidneyForwardRevRot (n : Nat) : RotProg :=
  gateRotSchedule (gidney_adder_forward_faithful_full_reverse_patched n)

theorem gidneyForwardRevRot_countPi8 (n : Nat) :
    countPi8 (gidneyForwardRevRot (n + 2)) = 7 * (n + 2) := by
  rw [gidneyForwardRevRot, gateRotSchedule_countPi8,
      tcount_gidney_adder_forward_faithful_full_reverse_patched]

end FormalRV.PauliRotation
