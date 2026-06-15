/-
  FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.Example
  ────────────────────────────────────────────────────────────
  Worked example for the faithful Gidney-2025 subtract-fixup modular adder.
  Contains `#eval` / `#check` demos, so it is OFF the default build path. Build:
    lake build FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.Example
-/
import FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup
import FormalRV.Codegen.EGateQasm

namespace FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup

open FormalRV.Framework
open FormalRV.Shor.MeasUncompute
open FormalRV.Codegen

-- The verified instance behind the README: `(x + 1) mod 3` at `bits = 2`
-- (so `p = 3 ≤ 2^2 = 4`, `x = 1 < 3`, `c = 1 < 3`), running over `W = 3` register
-- bits + flag. Decodes the low `2` target bits to `(1 + 1) mod 3 = 2`, releases Q
-- and the flag to `0`.
#check (gidneyModAddFixup_correct 2 3 1 1
          (by decide) (by decide) (by decide) (by decide) (by decide))

-- Its exact Toffoli cost: `2·(bits+1) = 2·3 = 6` Toffoli (two `n`-Toffoli measured
-- adds), at `bits = 2` (= `n + 1` with `n = 1`).
example : EGate.toffoli (gidneyModAddFixup 2 3 1) = 6 := by
  rw [show (2 : Nat) = 1 + 1 from rfl, toffoli_gidneyModAddFixup]

-- Head-to-head with the paper's `2.5n` half-Toffoli charge at `bits = 4` (n = 3):
-- twice the verified count (`= 2·2·(3+2) = 20`) is `≤` `g2025 4 = 5·4 = 20`.
example : 2 * EGate.toffoli (gidneyModAddFixup 4 0 0)
    ≤ FormalRV.Audit.Gidney2025.g2025_modadd_toffoli_halves 4 :=
  gidneyModAddFixup_meets_g2025_modadd 3 (by decide)

/-! ## Emit native-basis OpenQASM to file (input to `scripts/draw_qasm.py` → PNG). -/

#eval (do
  IO.FS.createDirAll "FormalRV/Arithmetic/ModularAdder/GidneySubtractFixup/diagrams"
  IO.FS.writeFile "FormalRV/Arithmetic/ModularAdder/GidneySubtractFixup/diagrams/gidney_subtractfixup_modadd_2_3_1.qasm"
    (toQasmE (gidneyModAddFixup 2 3 1))
  IO.println "wrote diagrams/gidney_subtractfixup_modadd_2_3_1.qasm" : IO Unit)

end FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup
