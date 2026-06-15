/-
  FormalRV.Shor.WindowedPPM — the hand-off from the windowed logical circuit to the
  PPM (Pauli-product-measurement / magic-state-factory) compiler.

  The PPM layer (`FormalRV.PPM`) compiles any `Gate` to a magic-PPM program and PROVES
  (`shorMagicDemand_eq_ccxCount`) that the magic-state demand equals the circuit's
  Toffoli (`CCX`) count — one teleported-CCX request per `Gate.CCX`.

  This file closes the interface loop: it relates the resource counter used in
  `WindowedCircuit` (`toffoliCount = tcount/7`) to the PPM counter (`gateCCXCount`),
  and concludes that the PPM compiler, applied to the full windowed multiplier,
  demands EXACTLY the verified Toffoli count of magic states:

      shorMagicDemand (windowedMulCircuit w bits a numWin) = numWin · (4·w·2^w + 2·bits).

  So the logical circuit plugs straight into the lower (magic-factory / lattice-surgery)
  layer with a proven, closed-form magic budget — the same `Gate`-IR interface the rest
  of the framework consumes.
-/
import FormalRV.Arithmetic.Windowed.WindowedCircuit
import FormalRV.PPM.CircuitToPPMFactoryProvision

namespace FormalRV.Shor.WindowedPPM

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.Framework.CircuitToPPMFactoryProvision
open FormalRV.Shor.WindowedCircuit

/-- The T-count is exactly `7 ×` the `CCX` count (only `CCX` carries T-cost). -/
theorem tcount_eq_seven_mul_ccxCount (g : Gate) : tcount g = 7 * gateCCXCount g := by
  induction g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ ih₁ ih₂ => simp only [tcount, gateCCXCount, ih₁, ih₂]; ring

/-- The `WindowedCircuit` Toffoli counter agrees with the PPM `gateCCXCount`. -/
theorem toffoliCount_eq_gateCCXCount (g : Gate) : toffoliCount g = gateCCXCount g := by
  rw [toffoliCount, tcount_eq_seven_mul_ccxCount, Nat.mul_div_cancel_left _ (by norm_num)]

/-- **PPM hand-off (the lower-level interface).**  Compiling the full windowed
    multiplier through the PPM magic-state compiler demands exactly the verified
    Toffoli count of magic states — `numWin · (4·w·2^w + 2·bits)`.  This is the
    plug-in point: the logical `Gate` circuit descends to the magic-factory layer
    with a proven, closed-form resource budget. -/
theorem windowedMulCircuit_magicDemand (w bits a numWin : Nat) :
    shorMagicDemand (windowedMulCircuit w bits a numWin)
      = numWin * (4 * w * 2 ^ w + 2 * bits) := by
  rw [shorMagicDemand_eq_ccxCount, ← toffoliCount_eq_gateCCXCount, windowedMulCircuit_toffoli]

end FormalRV.Shor.WindowedPPM
