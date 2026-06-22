/-
  FormalRV.PauliRotation.Gadgets.Windowed
  ───────────────────────────────────────
  THE WINDOWED ARITHMETIC (Gidney–Ekerå windows), compiled to Pauli
  rotations (`GateBridge.lean`):

    • `windowedMulCircuit`        — the (Cuccaro-instance) windowed
      multiplier: `numWin·(28·w·2^w + 14·bits)` T;
    • `windowedModNMulCircuit`    — the per-window mod-N multiplier:
      `numWin·(56·w·2^w + 56·bits)` T;
    • `windowedModNMulGate`       — the IN-PLACE mod-N Shor-weld entry:
      `2·numWin·(56·w·2^w + 56·bits)` T;
    • `grayWindowedMulCircuitOf cuccaroAdder` — the Gray-code windowed
      multiplier: `numWin·(28·(2^w − 1) + 14·bits)` T (the `w` factor gone).

  All compile exactly.  This file only IMPORTS the windowed modules (the
  folder belongs to another work lane) and the rotation T-counts compose
  with their existing anchored `tcount_*` theorems symbolically.
-/
import FormalRV.PauliRotation.Compiler.GateBridge
import FormalRV.Arithmetic.Windowed.WindowedCircuit
import FormalRV.Arithmetic.Windowed.WindowedModN
import FormalRV.Arithmetic.Windowed.WindowedModNInPlace
import FormalRV.Arithmetic.Windowed.WindowedGrayLookup

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource
open FormalRV.Shor.WindowedCircuit
open FormalRV.BQAlgo

/-! ## §1. The windowed multiplier (mod `2^bits` accumulator). -/

/-- The windowed multiplier as a rotation program. -/
def windowedMulRot (w bits a numWin : Nat) : RotProg :=
  gateRotSchedule (windowedMulCircuit w bits a numWin)

/-- **Rotation T-count = `numWin·(28·w·2^w + 14·bits)`**, all parameters. -/
theorem windowedMulRot_countPi8 (w bits a numWin : Nat) :
    countPi8 (windowedMulRot w bits a numWin)
      = numWin * (28 * w * 2 ^ w + 14 * bits) := by
  rw [windowedMulRot, gateRotSchedule_countPi8, tcount_windowedMulCircuit]

/-! ## §2. The per-window mod-N multiplier. -/

/-- The exactly-modular per-window multiplier as a rotation program. -/
def windowedModNMulRot (w bits a N numWin : Nat) : RotProg :=
  gateRotSchedule (windowedModNMulCircuit w bits a N numWin)

/-- **Rotation T-count = `numWin·(56·w·2^w + 56·bits)`**, all parameters. -/
theorem windowedModNMulRot_countPi8 (w bits a N numWin : Nat) :
    countPi8 (windowedModNMulRot w bits a N numWin)
      = numWin * (56 * w * 2 ^ w + 56 * bits) := by
  rw [windowedModNMulRot, gateRotSchedule_countPi8,
      tcount_windowedModNMulCircuit]

/-! ## §3. The IN-PLACE mod-N multiplier (the Shor-weld entry point). -/

/-- The in-place mod-N windowed multiplier (Shor-weld wrapper) as a
rotation program. -/
def windowedModNInPlaceRot (w bits N numWin c cinv : Nat) : RotProg :=
  gateRotSchedule (windowedModNMulGate w bits N numWin c cinv)

/-- **Rotation T-count = `2·numWin·(56·w·2^w + 56·bits)`** (the in-place
forward + inverse-uncompute factor), all parameters. -/
theorem windowedModNInPlaceRot_countPi8 (w bits N numWin c cinv : Nat) :
    countPi8 (windowedModNInPlaceRot w bits N numWin c cinv)
      = 2 * numWin * (56 * w * 2 ^ w + 56 * bits) := by
  rw [windowedModNInPlaceRot, gateRotSchedule_countPi8,
      tcount_windowedModNMulGate]
  ring

/-! ## §4. The Gray-code windowed multiplier (Cuccaro instance). -/

/-- The Gray-code windowed multiplier (over the Cuccaro `Adder` instance)
as a rotation program. -/
def grayWindowedMulRot (w bits a numWin : Nat) : RotProg :=
  gateRotSchedule (grayWindowedMulCircuitOf cuccaroAdder w bits a numWin)

/-- **Rotation T-count = `numWin·(28·(2^w − 1) + 14·bits)`** — the Gray-code
window cost with the `w` factor gone, all parameters. -/
theorem grayWindowedMulRot_countPi8 (w bits a numWin : Nat) :
    countPi8 (grayWindowedMulRot w bits a numWin)
      = numWin * (28 * (2 ^ w - 1) + 14 * bits) := by
  rw [grayWindowedMulRot, gateRotSchedule_countPi8,
      tcount_grayWindowedMulCircuit_cuccaro]

/-! ## §5. A correctness instance (small windowed multiplier). -/

/-- Correctness instance (`w = 2`, `bits = 4`, `a = 3`, two windows). -/
theorem windowedMulRot_denote_2_4_3_2 :
    RotProg.denote (Resource.width (windowedMulCircuit 2 4 3 2))
        (windowedMulRot 2 4 3 2)
      = seqDenote _ (gateRots (windowedMulCircuit 2 4 3 2)) :=
  gateRotSchedule_denote _ _ (by decide) (Nat.le_refl _)

end FormalRV.PauliRotation
