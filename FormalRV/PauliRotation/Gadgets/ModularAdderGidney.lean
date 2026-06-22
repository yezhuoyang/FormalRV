/-
  FormalRV.PauliRotation.Gadgets.ModularAdderGidney
  ─────────────────────────────────────────────────
  THE GIDNEY-PIPELINE MODULAR ADDER family — `(x + c) mod N` built on the
  patched Gidney adder (verified but STANDALONE; the live Shor path uses the
  Cuccaro pipeline, `ModularAdderCuccaro.lean`) — compiled to Pauli
  rotations (`GateBridge.lean`): the constant add/sub primitives, the
  flag-conditional add, and the full clean + controlled modular adders.

  Count shapes follow the family's `bits = n + 2` / `n + 1` statements.
-/
import FormalRV.PauliRotation.Compiler.GateBridge
import FormalRV.Arithmetic.ModularAdder.Gidney.TimeCount

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource
open FormalRV.BQAlgo

/-! ## §1. Constant add / subtract on the patched adder. -/

/-- `target += c` as a rotation program. -/
def gidneyAddConstRot (bits c : Nat) : RotProg :=
  gateRotSchedule (addConstGate bits c)

theorem gidneyAddConstRot_countPi8 (n c : Nat) :
    countPi8 (gidneyAddConstRot (n + 2) c) = 14 * (n + 2) := by
  rw [gidneyAddConstRot, gateRotSchedule_countPi8, tcount_addConstGate]

theorem gidneyAddConstRot_denote_2 :
    RotProg.denote (width (addConstGate 2 1)) (gidneyAddConstRot 2 1)
      = seqDenote _ (gateRots (addConstGate 2 1)) :=
  gateRotSchedule_denote _ _ (by decide) (Nat.le_refl _)

/-- `target -= N` (two's complement) as a rotation program. -/
def gidneySubConstRot (bits N : Nat) : RotProg :=
  gateRotSchedule (subConstGate bits N)

theorem gidneySubConstRot_countPi8 (n N : Nat) :
    countPi8 (gidneySubConstRot (n + 2) N) = 14 * (n + 2) := by
  rw [gidneySubConstRot, gateRotSchedule_countPi8, tcount_subConstGate]

/-- The flag-conditional constant add as a rotation program. -/
def gidneyCondAddRot (bits N flagIdx : Nat) : RotProg :=
  gateRotSchedule (conditionalAddConstGate bits N flagIdx)

theorem gidneyCondAddRot_countPi8 (n N flagIdx : Nat) :
    countPi8 (gidneyCondAddRot (n + 2) N flagIdx) = 14 * (n + 2) := by
  rw [gidneyCondAddRot, gateRotSchedule_countPi8, tcount_conditionalAddConstGate]

/-! ## §2. The full modular adder and its controlled form. -/

/-- The clean `(x + c) mod N` as a rotation program. -/
def gidneyModAddRot (bits N c : Nat) : RotProg :=
  gateRotSchedule (modAddConstGate bits N c)

/-- **Rotation T-count = `70·(n+2)`** for `bits = n + 1` (the family's
five-adder pipeline shape). -/
theorem gidneyModAddRot_countPi8 (n N c : Nat) :
    countPi8 (gidneyModAddRot (n + 1) N c) = 70 * (n + 2) := by
  rw [gidneyModAddRot, gateRotSchedule_countPi8, tcount_modAddConstGate]

/-- The controlled `(x + c) mod N` as a rotation program. -/
def gidneyCtrlModAddRot (bits N c controlIdx flagIdx : Nat) : RotProg :=
  gateRotSchedule (controlledModAddConstGate bits N c controlIdx flagIdx)

/-- **Rotation T-count = `70·(n+2) + 14`** for `bits = n + 1`. -/
theorem gidneyCtrlModAddRot_countPi8 (n N c controlIdx flagIdx : Nat) :
    countPi8 (gidneyCtrlModAddRot (n + 1) N c controlIdx flagIdx)
      = 70 * (n + 2) + 14 := by
  rw [gidneyCtrlModAddRot, gateRotSchedule_countPi8,
      tcount_controlledModAddConstGate]

end FormalRV.PauliRotation
