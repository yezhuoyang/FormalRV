/-
  FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap —
  SYNTH-2 (attempt A): a TRANSPOSITION gate on a register, with proven
  CLEAN-ancilla action.
  ════════════════════════════════════════════════════════════════════════════

  Goal: `swapGate reg x y anc : Gate` realizing the transposition of the two
  register-VALUES `x` and `y` (x, y < 2^k, k = reg.length): it swaps the basis
  state whose reg-decode is `x` with the one whose reg-decode is `y`, leaving
  every other state fixed, using `anc` as CLEAN scratch (restored).

  regVal = `decodeReg (reg.getD · 0) reg.length` from the repo (Adder.lean).

  CONSTRUCTION (conjugation; reuse `mcxClean` from E2RunwaySynthMCX):
    swapGate reg x y anc := Xmask ; reduceCNOT ; antiCtrlX ; reduceCNOT ; Xmask
  with z := x XOR y, p := lowest set bit of z:
   • Xmask   : X reg[i] for each i with x.testBit i — maps reg-value v ↦ v XOR x.
   • reduceCNOT : CX reg[p] reg[i] for each i≠p with z.testBit i — maps 0↦0, z↦2^p.
   • antiCtrlX : (X reg[i] for i≠p) ; mcxClean (reg i≠p) reg[p] anc ; (X reg[i] for i≠p)
       — flips reg[p] iff all other reg wires are 0 ⇔ reg-value ∈ {0, 2^p}.
  For x = y (z = 0) the construction reduces to identity on reg-values.

  Kernel-clean target: no `sorry`, no `native_decide`.
-/

-- Re-export shim: split into E2RunwaySynthSwap/ submodules (same namespace); importers unchanged.
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.Indices
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.RegAct
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.Stages
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.Values
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.Compose
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.WellTyped
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.Smoke
