/-
  FormalRV.PauliRotation.Gadgets.ModularAdderCuccaro
  ──────────────────────────────────────────────────
  THE LIVE MODULAR ADDER — the Cuccaro/SQIR-style `(x + c) mod N` and its
  controlled form (`sqir_style_controlledModAddConst_gate` is the per-bit
  primitive the verified multiplier and Shor actually stack) — compiled to
  Pauli rotations (`GateBridge.lean`).

  T-counts carry the family's honest `if c = 0` dispatch (the `c = 0` case
  is the identity, zero rotations).
-/
import FormalRV.PauliRotation.Compiler.GateBridge
import FormalRV.Arithmetic.ModularAdder.Cuccaro.TimeCount

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource
open FormalRV.BQAlgo

/-! ## §1. The clean modular add-constant `(x + c) mod N`. -/

/-- The clean Cuccaro-style modular adder as a rotation program. -/
def cuccaroModAddRot (bits N c : Nat) : RotProg :=
  gateRotSchedule (sqir_style_modAddConst_clean_gate bits N c)

/-- **Rotation T-count = `56·bits`** (`0` when `c = 0`), all sizes. -/
theorem cuccaroModAddRot_countPi8 (bits N c : Nat) :
    countPi8 (cuccaroModAddRot bits N c)
      = if c = 0 then 0 else 56 * bits := by
  rw [cuccaroModAddRot, gateRotSchedule_countPi8,
      tcount_cuccaro_style_modAddConst_clean_gate]

/-- Correctness instance (3 bits, `(x + 2) mod 5`). -/
theorem cuccaroModAddRot_denote_3 :
    RotProg.denote (width (sqir_style_modAddConst_clean_gate 3 5 2))
        (cuccaroModAddRot 3 5 2)
      = seqDenote _ (gateRots (sqir_style_modAddConst_clean_gate 3 5 2)) :=
  gateRotSchedule_denote _ _ (by decide) (Nat.le_refl _)

/-! ## §2. The CONTROLLED modular add-constant (ModMult's per-bit primitive). -/

/-- The controlled Cuccaro-style modular adder as a rotation program. -/
def cuccaroCtrlModAddRot (bits q_start N c controlIdx flagPos : Nat) : RotProg :=
  gateRotSchedule
    (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)

/-- **Rotation T-count = `56·bits`** (`0` when `c = 0`) — the per-bit cost
whose `bits`-fold forward+uncompute stack is ModMult's `112·bits²`. -/
theorem cuccaroCtrlModAddRot_countPi8
    (bits q_start N c controlIdx flagPos : Nat) :
    countPi8 (cuccaroCtrlModAddRot bits q_start N c controlIdx flagPos)
      = if c = 0 then 0 else 56 * bits := by
  rw [cuccaroCtrlModAddRot, gateRotSchedule_countPi8,
      tcount_cuccaro_style_controlledModAddConst_gate]

end FormalRV.PauliRotation
