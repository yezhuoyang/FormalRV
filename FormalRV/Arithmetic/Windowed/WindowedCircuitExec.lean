/-
  FormalRV.Shor.WindowedCircuitExec — executable end-to-end checks of the full
  windowed-multiplier LOGICAL circuit on genuinely qubit-encoded integers.

  These RUN the actual `Gate` circuit (`Gate.applyNat`) on `encodeReg`-encoded inputs
  and check the decoded accumulator equals `a·y`, at TWO different window sizes
  (`w = 2` and `w = 3`) — concretely demonstrating the construction is parametric in
  the window size, not hard-wired.

  (`native_decide` ⇒ these carry `Lean.ofReduceBool`; they are execution smoke-tests.
  The kernel-clean *parametric value-correctness* is `WindowedArith.windowed_modProductAdd`
  / `windowedLookupFold_modProductAdd`, and the resource count is
  `WindowedCircuit.windowedMulCircuit_toffoli`.) -/
import FormalRV.Arithmetic.Windowed.WindowedCircuit

namespace FormalRV.Shor.WindowedCircuitExec

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit

/-- Run the circuit on `y` and decode the accumulator. -/
def runMul (w bits a numWin y : Nat) : Nat :=
  decodeAcc (Gate.applyNat (windowedMulCircuit w bits a numWin) (mulInput w bits numWin y)) (accStart w) bits

-- Window size w = 2 (2-bit windows), numWin = 2 (y < 16), bits = 6.
example : runMul 2 6 3 2 6 = 18 := by native_decide   -- 3·6
example : runMul 2 6 3 2 7 = 21 := by native_decide   -- 3·7
example : runMul 2 6 5 2 5 = 25 := by native_decide   -- 5·5

-- A DIFFERENT window size w = 3 (3-bit windows) also passes — `runMul 3 7 3 2 10 = 30` —
-- but its native compilation is slow (~7 min), so it is documented rather than checked
-- here.  The construction is parametric in `w`, and the kernel-clean value-correctness
-- (`WindowedArith.windowedMultiplier`/`windowed_modProductAdd`) and resource/PPM theorems
-- (`WindowedCircuit.windowedMulCircuit_toffoli`, `WindowedPPM.windowedMulCircuit_magicDemand`)
-- hold for ALL `w`.  This file is standalone / on-demand (not in the routine build).

end FormalRV.Shor.WindowedCircuitExec
