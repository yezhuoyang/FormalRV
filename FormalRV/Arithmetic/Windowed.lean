import FormalRV.Arithmetic.Windowed.WindowedArith
import FormalRV.Arithmetic.Windowed.WindowedCostModel
import FormalRV.Arithmetic.Windowed.WindowedLookupAdd
import FormalRV.Arithmetic.Windowed.WindowedCircuit
import FormalRV.Arithmetic.Windowed.WindowedLookupSelect
import FormalRV.Arithmetic.Windowed.WindowedCopySemantics
import FormalRV.Arithmetic.Windowed.WindowedCircuitCorrect
import FormalRV.Arithmetic.Windowed.WindowedWidth
import FormalRV.Arithmetic.Windowed.WindowedExpStep
import FormalRV.Arithmetic.Windowed.WindowedGrayLookup
-- NOTE: `WindowedCircuitExec` (executable `native_decide` smoke tests) is a
-- standalone test file and is intentionally NOT imported here — it is slow to
-- compile and is kept off the default build path. Build it on demand with
-- `lake build FormalRV.Arithmetic.Windowed.WindowedCircuitExec`.

/-!
# FormalRV.Arithmetic.Windowed

Windowed (Gidney-style) modular-multiplication arithmetic: base-2^w digit
expansion, the windowed multiplier circuit, lookup-addition, ℚ-valued
resource/cost models, and qubit-width counts.

Relocated from `FormalRV/Shor/` (2026-06-09). These are pure L2 arithmetic
gadgets — no order-finding / QPE / eigenstate / success-probability content —
so they live under `Arithmetic/` with the other logical gadgets.
-/
