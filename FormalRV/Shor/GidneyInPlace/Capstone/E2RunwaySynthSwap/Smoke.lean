/- E2RunwaySynthSwap — Â§7 definitional smoke checks.  Part of the `E2RunwaySynthSwap` re-export shim (same namespace). -/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.WellTyped

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthMCX
open FormalRV.Shor.WindowedCircuit (writeReg writeReg_at writeReg_frame
  decodeReg_testBit decodeReg_lt_two_pow decodeReg_succ_eq)


/-! ## §7. Smoke checks (definitional). -/

-- `x = y` ⇒ the gate is the identity.
example (reg anc : List Nat) (x : Nat) : swapGate reg x x anc = Gate.I := by
  unfold swapGate; rw [if_pos rfl]

-- The lowest set bit of `1` is `0`; of `2` is `1`; of `6 = 0b110` is `1`.
example : lowestBit 1 = 0 := by
  unfold lowestBit; rw [dif_pos ⟨0, by decide⟩]; exact Nat.find_eq_zero _ |>.mpr (by decide)


end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap
